-- Prove2me | Definitions.Def_StatefulPricing_Chase
-- name    : StatefulPricing_Chase
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T08:25:21.625698+00:00
-- url     : https://prove2.me/theorems/b51f4020-3626-4804-a761-7d29ffb7c42f
-- title:
--   The randomized chasing oracle of Theorem 3.4 run on fixed coins: Good, Bad, Missing and the potential $\phi$
-- statement:
--   Fix a DRACC instance, a tie-breaking rank, a target policy $\gamma$, a start round $t_{\mathrm{init}}$ and an initial inventory vector $\hat\lambda_{t_{\mathrm{init}}}$. In each round $t\ge t_{\mathrm{init}}$ the chasing oracle of Theorem 3.4 posts either the all-$1$ price vector (with probability $\varepsilon$) or
--   $$
--   \hat p_t(i)=\begin{cases}p^\gamma_t(i), & i\in\mathrm{Good}_t,\\ 1, & i\in\mathrm{Bad}_t,\end{cases}
--   $$
--   where $\lambda^\gamma_t$ is the inventory of $\gamma$ run from round $1$, $\hat\lambda_t$ is the oracle's own inventory, $\mathrm{Good}_t=\{i\in A_t:\lambda^\gamma_t(i)\le\hat\lambda_t(i)\}$ and $\mathrm{Bad}_t=A_t\setminus\mathrm{Good}_t$. Round $t$ is **Missing** if $\gamma$ sells a unit of some resource of $\mathrm{Bad}_t$, and **Following** otherwise. The potential is
--   $$
--   \phi(t)=\sum_{i\in\mathrm{Bad}_t}\big(\lambda^\gamma_t(i)-\hat\lambda_t(i)\big).
--   $$
--   The module fixes the outcome of the coins as a sequence (true = post the all-$1$ vector at that round) and defines, as deterministic functions of it, the oracle's prices and inventory, $\mathrm{Good}_t$, $\mathrm{Bad}_t$, Missing rounds, $\phi$ and the number of Missing rounds in $[t_{\mathrm{init}},t_{\mathrm{final}}]$.
--
--   These are the objects of the potential argument behind Theorem 3.6.
--
--   **Formalization Note** The law of the coins (i.i.d. Bernoulli$(\varepsilon)$) enters only the statement that takes an expectation. The initial inventory vector is arbitrary; only its values on $A_{t_{\mathrm{init}}}$ matter. $\phi$ is computed in $\mathbb Z$.
-- source:
--   Emek, Lavi, Niazadeh, Shi, Stateful Posted Pricing with Vanishing Regret via Dynamic Deterministic Markov Decision Processes, arXiv:2005.01869v2, proof of Theorem 3.4, p.9; proof of Theorem 3.6, p.10

import Mathlib
import Definitions.Def_StatefulPricing_Instance

set_option autoImplicit false

namespace StatefulPricing

/-- **The randomized chasing oracle of Theorem 3.4, with fixed coins** (proof of Theorem 3.4,
arXiv:2005.01869v2, p.9; reused by the proof of Theorem 3.6, p.10): "Given an initial round tinit
and an initial inventory vector λ̂tinit, we construct a randomized chasing oracle OChasing … In
each round tinit ≤ t ≤ tfinal, the chasing oracle posts the (|At|-dimensional) all-1 price vector
with probability ε … and it posts the price vector p̂t = p^γ_t(i) if i ∈ Goodt; 1 if i ∈ Badt
with probability 1 − ε".

The data of one run: a DRACC instance `I`, the tie-breaking rank, the target policy `γ`, the start
round `tinit`, the initial inventory vector `init` (= `λ̂_{tinit}`), and the outcome of the coins:
`coin t = true` means that the all-1 vector is posted at round `t`.

**Formalization Note.** The coins are an explicit sequence, so the objects below are
deterministic functions of it; their law (i.i.d. Bernoulli(ε)) enters only the statement that
takes an expectation. `init` is an arbitrary inventory vector (only its values on `A_{tinit}`
matter). -/
structure Chase (T C W : ℕ) where
  /-- The DRACC instance. -/
  I : Instance T C W
  /-- The tie-breaking rank. -/
  rank : Finset ℕ → ℕ
  /-- The target policy. -/
  γ : Policy
  /-- The round at which the oracle is invoked. -/
  tinit : ℕ
  /-- The initial inventory vector `λ̂_{tinit}`. -/
  init : ℕ → ℕ
  /-- `coin t = true`: the oracle posts the all-1 price vector at round `t`. -/
  coin : ℕ → Bool

namespace Chase

variable {T C W : ℕ}

/-- `λ^γ_t`, the inventory vector at time `t` obtained by running `γ` from round `1` to `t`. -/
noncomputable def polInv (c : Chase T C W) (t : ℕ) : ℕ → ℕ :=
  c.I.policyInv c.rank c.γ t

/-- `p^γ_t`, the price vector posted by `γ` at round `t`. -/
noncomputable def polPrice (c : Chase T C W) (t : ℕ) : ℕ → ℝ :=
  c.I.policyPrice c.rank c.γ t

/-- The price vector `p̂_t` for the oracle's inventory `inv` at round `t`: `p^γ_t(i)` on
`Good_t = {i ∈ A_t | λ^γ_t(i) ≤ inv(i)}`, and `1` on `Bad_t` and off `A_t`. -/
noncomputable def hatPrice (c : Chase T C W) (t : ℕ) (inv : ℕ → ℕ) : ℕ → ℝ := by
  classical
  exact fun i => if i ∈ c.I.active t ∧ c.polInv t i ≤ inv i then c.polPrice t i else 1

/-- The price vector actually posted at round `t`: the all-1 vector if `coin t`, else `p̂_t`. -/
noncomputable def price (c : Chase T C W) (t : ℕ) (inv : ℕ → ℕ) : ℕ → ℝ :=
  if c.coin t then fun _ => 1 else c.hatPrice t inv

/-- The oracle's inventory `λ̂_{tinit + k}` (Eq. (5)): `λ̂_{tinit} = init`, then the DRACC update
with the oracle's own sales. -/
noncomputable def invOff (c : Chase T C W) : ℕ → (ℕ → ℕ)
  | 0 => c.init
  | k + 1 => c.I.step (c.tinit + k) (invOff c k)
      (c.I.demand c.rank (c.tinit + k) (c.price (c.tinit + k) (invOff c k)))

/-- `λ̂_t`, the oracle's inventory vector at round `t ≥ tinit`. -/
noncomputable def inv (c : Chase T C W) (t : ℕ) : ℕ → ℕ :=
  c.invOff (t - c.tinit)

/-- The price vector `p̂_t` at the oracle's inventory `λ̂_t`. -/
noncomputable def hatPriceAt (c : Chase T C W) (t : ℕ) : ℕ → ℝ :=
  c.hatPrice t (c.inv t)

/-- The price vector posted by the oracle at round `t`. -/
noncomputable def priceAt (c : Chase T C W) (t : ℕ) : ℕ → ℝ :=
  c.price t (c.inv t)

/-- `Good_t = {i ∈ A_t | λ^γ_t(i) ≤ λ̂_t(i)}` (p.9). -/
noncomputable def good (c : Chase T C W) (t : ℕ) : Finset ℕ := by
  classical
  exact (c.I.active t).filter (fun i => c.polInv t i ≤ c.inv t i)

/-- `Bad_t = A_t \ Good_t` (p.9). -/
noncomputable def bad (c : Chase T C W) (t : ℕ) : Finset ℕ := by
  classical
  exact (c.I.active t).filter (fun i => c.inv t i < c.polInv t i)

/-- Round `t` is `Missing` if at least one unit of a resource in `Bad_t` is sold by `γ` in this
round; otherwise it is `Following` (p.9). -/
def Missing (c : Chase T C W) (t : ℕ) : Prop :=
  ∃ i ∈ c.bad t, i ∈ c.I.demand c.rank t (c.polPrice t)

/-- The potential `φ(t) = Σ_{i∈Badt} λ^γ_t(i) − λ̂_t(i)` (p.9), computed in `ℤ`. -/
noncomputable def phi (c : Chase T C W) (t : ℕ) : ℤ :=
  ∑ i ∈ c.bad t, ((c.polInv t i : ℤ) - (c.inv t i : ℤ))

/-- The number `#M` of `Missing` rounds in `[tinit, tfinal]`. -/
noncomputable def numMissing (c : Chase T C W) (tfinal : ℕ) : ℕ := by
  classical
  exact ((Finset.Icc c.tinit tfinal).filter (fun t => c.Missing t)).card

end Chase

end StatefulPricing


