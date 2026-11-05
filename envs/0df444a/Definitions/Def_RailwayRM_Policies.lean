-- Prove2me | Definitions.Def_RailwayRM_Policies
-- name    : RailwayRM_Policies
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T05:35:25.413773+00:00
-- url     : https://prove2.me/theorems/9fbcea94-7740-434e-9dfb-2441ad0d62c8
-- title:
--   The static-price flexible-capacity policy $\pi_1$, the relaxed policy $\tilde\pi_1$ and the hitting times $\tau_{\ell,m}$
-- statement:
--   Let $(\vec x,\vec y,\vec b)$ be a solution of $P_D$, with $v=(\vec x,\vec y)$.
--
--   **Pricing of $\pi_1$.** In period $1$ every itinerary sells at its rate $v_n$. In a period $t>1$, itinerary $n$ sells at the rate $0$ (the null price) if
--   $$\bar X_{\ell,m}[1,t-1]=k(\bar b_m-\lfloor b_m\rfloor)\quad\text{for some }\ell\in\bar S_n\text{ and some train }m,$$
--   and at $v_n$ otherwise.
--
--   **Capacity of $\pi_1$.** At the end of the horizon train $m$ uses $b_{r,m}=\lceil\max_\ell\bar X_{\ell,m}[1,T]/k\rceil$ reserved coaches. A vector $\vec\beta$ minimizes
--   $$\sum_m c_o\beta_m+\sum_m\sum_\ell c_s\,\mathbb E\big[(\bar Y_{\ell,m}[1,T]-\beta_mk)^+\,\big|\,\text{observed path}\big]$$
--   over the real box $\prod_m[\underline b_m,\bar b_m-b_{r,m}]$, and train $m$ uses $\lfloor\beta_m\rfloor$ unreserved coaches. A *selection* chooses such a minimizer at every observed path of positive probability.
--
--   **The relaxed policy $\tilde\pi_1$.** It sells at the rates $v$ in every period, with no stopping, uses $\lfloor b_m\rfloor$ unreserved coaches, and has no coach limits. Its expected cost is $C^{\tilde\pi_1}_U$ of (9).
--
--   **Hitting times.** $\tau_{\ell,m}$ is the earliest period $t\in\{1,\dots,T\}$ in which $\bar X_{\ell,m}[1,t]=(\bar b_m-\lfloor b_m\rfloor)k$, and $T$ if there is none, and $\tau=\min_{\ell,m}\tau_{\ell,m}$.
--
--   In the $\kappa$-scaled system these definitions are applied to the scaled instance and the solution $(\vec x,\vec y,\kappa\vec b)$, so the threshold is $k(\kappa\bar b_m-\lfloor\kappa b_m\rfloor)$.
--
--   **Formalization Note.** The expectation in the capacity problem is conditional on the observed path, as a quotient of finite sums; a selection is constrained only on observed paths of positive probability, since the box can be empty on an unreachable path. The threshold is an integer, so no natural-number subtraction truncates it.
-- source:
--   Manchiraju et al., SSRN 4112672 (2023-08-22), §3.1, p. 16 (algorithm, (Q^{π1})); App. p. 2 (policy π̃1); App. p. 3 ((6), (9))

import Mathlib
import Definitions.Def_RailwayRM_Model

open Finset

namespace RailwayRM

/-!
The static-price flexible-capacity policy `π₁` (SSRN 4112672, 2023-08-22, §3.1, p. 16), the relaxed
static policy `π̃₁` (App. p. 2), and the hitting times of (6) (App. p. 3).
-/

namespace Instance

variable {L M N : ℕ} (I : Instance L M N)

/-- The probability of an observed path under rate decisions `ρ`. -/
noncomputable def obsProb (ρ : I.RatePolicy) (o : I.ObsPath) : ℝ :=
  ∑ ω ∈ univ.filter (fun ω : I.FullPath => I.observe ω = o), I.pathProb ρ ω

/-- The conditional expectation of a function of the full path given the observed path `o`, for `o`
of positive probability: the expectation over the train choices of the unreserved buyers. -/
noncomputable def condExpect (ρ : I.RatePolicy) (o : I.ObsPath) (f : I.FullPath → ℝ) : ℝ :=
  (∑ ω ∈ univ.filter (fun ω : I.FullPath => I.observe ω = o), I.pathProb ρ ω * f ω) /
    I.obsProb ρ o

/-- The reserved-sales limit `k (b̄_m - ⌊b_m⌋)` of step 2 of `π₁` (SSRN 4112672, 2023-08-22, p. 16),
for coaches `b` of a solution of (P_D). It is an integer, so nothing is truncated. -/
noncomputable def threshold (b : Fin M → ℝ) (m : Fin M) : ℤ :=
  (I.k : ℤ) * ((I.bMax m : ℤ) - ⌊b m⌋)

open Classical in
/-- The pricing decisions of `π₁` from a solution `(v, b)` of (P_D), steps 1–2 of the algorithm
(SSRN 4112672, 2023-08-22, p. 16). In period 1 every itinerary sells at `v n`. In period `t > 1`
itinerary `n` sells at the rate `0` (the null price) if `X̄_{ℓ,m}[1,t-1] = k (b̄_m - ⌊b_m⌋)` for some
`ℓ ∈ S̄_n` and some train `m`, and at `v n` otherwise.

**Formalization Note.** The index `t : Fin T` is the paper's period `t + 1`, so `t.val ≠ 0` is
"`t > 1`" and `resCount o ℓ m t.val` is `X̄_{ℓ,m}[1, t-1]`. The rule runs over every train and nulls
the whole itinerary. -/
noncomputable def pi1Rates (v : Rates M N) (b : Fin M → ℝ) : I.RatePolicy := fun t o n =>
  if t.val ≠ 0 ∧ ∃ ℓ ∈ I.legs n, ∃ m, (I.resCount o ℓ m t.val : ℤ) = I.threshold b m then 0 else v n

/-- The box `B^{π₁} = B^{π₁}_1 × ⋯ × B^{π₁}_M`, `B^{π₁}_m = [b̲_m, b̄_m - b^{π₁}_{r,m}]` of step 4
(SSRN 4112672, 2023-08-22, p. 16), a box of real vectors. -/
noncomputable def capacityBox [NeZero L] (o : I.ObsPath) : Set (Fin M → ℝ) :=
  Set.univ.pi fun m => Set.Icc (I.bMin m : ℝ) ((I.bMax m : ℝ) - (I.reservedCoaches o m : ℝ))

/-- The objective of `Q^{π₁}` (SSRN 4112672, 2023-08-22, p. 16) at the end of the sales horizon:
`∑_m c_o β_m + ∑_m ∑_ℓ c_s E[(Ȳ_{ℓ,m}[1,T] - β_m k)⁺ | o]`.

**Formalization Note.** `E` is read as conditional on the observed sales history `o`, the information
available when the coaches are chosen. `B^{π₁}` is random, so an unconditional `E` would not define
a decision per path. -/
noncomputable def capacityObjective [NeZero L] (ρ : I.RatePolicy) (o : I.ObsPath)
    (β : Fin M → ℝ) : ℝ :=
  ∑ m, I.co * β m +
    ∑ m, ∑ ℓ : Fin L, I.cs *
      I.condExpect ρ o fun ω => max ((I.unresCount ω ℓ m : ℝ) - β m * (I.k : ℝ)) 0

/-- `sel` selects a minimizer of `Q^{π₁}` over `B^{π₁}` (step 4, p. 16) at every observed path of
positive probability. Statements hold for every such selection, so nothing depends on a tie-break. -/
def IsCapacitySelection [NeZero L] (v : Rates M N) (b : Fin M → ℝ)
    (sel : I.ObsPath → Fin M → ℝ) : Prop :=
  ∀ o, 0 < I.obsProb (I.pi1Rates v b) o →
    sel o ∈ I.capacityBox o ∧
      ∀ β ∈ I.capacityBox o,
        I.capacityObjective (I.pi1Rates v b) o (sel o) ≤ I.capacityObjective (I.pi1Rates v b) o β

/-- The static-price flexible-capacity policy `π₁` (SSRN 4112672, 2023-08-22, p. 16): the rates
`pi1Rates` and `⌊b^{π₁}_{u,m}⌋` unreserved coaches on train `m`, where `b^{π₁}_u` is a selection. -/
noncomputable def pi1 (v : Rates M N) (b : Fin M → ℝ) (sel : I.ObsPath → Fin M → ℝ) : I.Policy where
  rate := I.pi1Rates v b
  coaches := fun o m => ⌊sel o m⌋₊

/-- The rate decisions of the relaxed static policy `π̃₁` (App. p. 2): the rates `v` in every period,
with no stopping. -/
def staticRates (v : Rates M N) : I.RatePolicy := fun _ _ => v

/-- The relaxed static policy `π̃₁` (App. p. 2): the rates `v` throughout and `⌊b_m⌋` unreserved
coaches on train `m`. Its reserved coaches are those the demand requires, which is how `cost`
charges them, and `cost` of this policy is `C^{π̃₁}_U` of (9), App. p. 3. Problem `P_U` has no coach
limits, so no feasibility is attached. -/
noncomputable def relaxedPolicy (v : Rates M N) (b : Fin M → ℝ) : I.Policy where
  rate := I.staticRates v
  coaches := fun _ m => ⌊b m⌋₊

/-- `τ_{ℓ,m}` (App. p. 3): the earliest period `t ∈ {1, …, T}` in which `X̄_{ℓ,m}[1,t]` equals
`(b̄_m - ⌊b_m⌋) k`, and `T` if there is none. -/
noncomputable def hitTime (b : Fin M → ℝ) (ℓ : Fin L) (m : Fin M) (o : I.ObsPath) : ℕ :=
  if h : ((Icc 1 I.T).filter fun t => (I.resCount o ℓ m t : ℤ) = I.threshold b m).Nonempty then
    ((Icc 1 I.T).filter fun t => (I.resCount o ℓ m t : ℤ) = I.threshold b m).min' h
  else I.T

/-- `τ = min {τ_{ℓ,m} : 1 ≤ ℓ ≤ L, 1 ≤ m ≤ M}`, (6), App. p. 3. -/
noncomputable def firstHitTime [NeZero L] [NeZero M] (b : Fin M → ℝ) (o : I.ObsPath) : ℕ :=
  univ.inf' univ_nonempty fun p : Fin L × Fin M => I.hitTime b p.1 p.2 o

end Instance

end RailwayRM


