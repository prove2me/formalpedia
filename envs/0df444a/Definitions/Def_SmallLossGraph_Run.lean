-- Prove2me | Definitions.Def_SmallLossGraph_Run
-- name    : SmallLossGraph_Run
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T07:54:07.360988+00:00
-- url     : https://prove2.me/theorems/79ee1182-3850-48f5-a276-9ef0b45a7ac3
-- title:
--   Algorithm 1 run on a full-information learner: path probabilities, events and approximate regret
-- statement:
--   1. **Full-information algorithm.** A deterministic map $A$ from the list of past loss vectors $(\ell^0,\dots,\ell^{t-1})$ to a probability vector $p^t$ on the $d$ arms ($A$ applied to the empty list is its initialization).
--   2. **Approximate-regret guarantee.** For parameters $\varepsilon'>0$, $L$, horizon $T$ and a real $\mathcal A$ (the paper's $A(d,T)$), $A$ has the guarantee if for every loss sequence with entries in $[0,L]$ and every arm $f$,
--   $$
--   (1-\varepsilon')\sum_{t}\sum_i p^t_i\ell^t_i-\sum_t\ell^t_f\le\frac{L\,\mathcal A}{\varepsilon'} .
--   $$
--   With $\varepsilon'=\varepsilon/5$ the right side is the paper's $5L\cdot A(d,T)/\varepsilon$.
--   3. **The run.** Along an arm path $I(0),\dots,I(T-1)$: $p^t=A(\tilde\ell^0,\dots,\tilde\ell^{t-1})$ (the *estimated* losses), $(G^t,\ell^t)$ is the adversary's response to $I(0),\dots,I(t-1)$, the frozen set, $w^t$ and $\tilde\ell^t$ are those of one round of Algorithm 1 with parameters $\varepsilon',\alpha$, and $\tilde\ell^t$ uses the drawn arm $I(t)$.
--   4. **Path probability and events.** The probability of the path is $\prod_t w^t_{I(t)}$, and an event $E$ on arm paths has probability $\Pr[E]=\sum_{I\in E}\prod_t w^t_{I(t)}$.
--   5. **Approximate regret** against arm $f$:
--   $$
--   \mathrm{ApxReg}(f,\varepsilon)=(1-\varepsilon)\sum_t\ell^t_{I(t)}-\sum_t\ell^t_f .
--   $$
--
--   **Formalization Note** Rounds are $0$-based and paths are functions `Fin T → Fin d`. A full-information algorithm outputs probability vectors, so it exists only for $d\ge1$. The guarantee is a property of $A$ at the given $\varepsilon'$, $L$ and $T$ (the loss range is known to $A$, as for Multiplicative Weights in Corollary 3.5).
-- source:
--   Lykouris–Sridharan–Tardos, Small-loss bounds for online learning with partial information, arXiv:1711.03639v5, Algorithm 1, lines 1, 6, 8, p.8; §2.2, p.6 (approximate regret); Theorem 3.6, p.12 (guarantee of A)

import Mathlib
import Definitions.Def_SmallLossGraph_Protocol
import Definitions.Def_SmallLossGraph_Freezing

open scoped BigOperators

namespace SmallLossGraph

/-- **Full-information learning algorithm `A`.**
arXiv:1711.03639v5, §3, Algorithm 1, lines 1 and 8, p.8: `A` supplies the probability vector
`p^t` of each round and is updated with the (estimated) loss vector of every round.

`A.dist h` is the probability vector `p^t` after the loss vectors `h = [ℓ^0, …, ℓ^{t−1}]`
(oldest first); `A.dist []` is `A`'s initialization `p^1` (line 1).

**Formalization Note** `A` is deterministic; its outputs are probability vectors (nonnegative,
summing to `1`), which is part of being a learner, not an added condition. Since `Fin 0` carries
no probability vector, an algorithm exists only for `d ≥ 1`. -/
structure FullInfoAlg (d : ℕ) where
  /-- The probability vector `p^t` after the loss history (oldest first). -/
  dist : List (Fin d → ℝ) → Fin d → ℝ
  /-- Probabilities are nonnegative. -/
  dist_nonneg : ∀ h i, 0 ≤ dist h i
  /-- Probabilities sum to one. -/
  dist_sum : ∀ h, ∑ i, dist h i = 1

/-- **`A`'s approximate-regret guarantee** (arXiv:1711.03639v5, Theorem 3.6, p.12: "`A` … with an
expected approximate regret guarantee of `E[ApxReg(f, ε/5)] ≤ 5L·A(d,T)/ε` against any arm `f`,
when run on losses in `[0, L]`").

`HasApxRegretBound A T ε' L Abound`: for every loss sequence `ℓ^0, …, ℓ^{T−1}` with entries in
`[0, L]` and every arm `f`,
`(1 − ε′) ∑_t ∑_i p^t_i ℓ^t_i − ∑_t ℓ^t_f ≤ L · Abound / ε′`,
where `p^t = A(ℓ^0, …, ℓ^{t−1})`. With `ε′ = ε/5` the right side is the paper's `5L·A(d,T)/ε`.

**Formalization Note** `A` is deterministic, so its expected loss in round `t` is
`∑_i p^t_i ℓ^t_i` and its expected approximate regret is the left side above. The loss range
`L`, the parameter `ε′` and the horizon `T` are arguments: `A` may be instantiated knowing them
(as Multiplicative Weights is in Corollary 3.5). -/
def HasApxRegretBound {d : ℕ} (A : FullInfoAlg d) (T : ℕ) (ε' L Abound : ℝ) : Prop :=
  ∀ ℓ : Fin T → Fin d → ℝ, (∀ t i, ℓ t i ∈ Set.Icc (0 : ℝ) L) → ∀ f : Fin d,
    (1 - ε') * ∑ t : Fin T, ∑ i, A.dist ((List.ofFn ℓ).take t) i * ℓ t i - ∑ t : Fin T, ℓ t f
      ≤ L * Abound / ε'

/-- The estimated-loss history of Algorithm 1 after the arms `r`, listed **newest first**; the
result is in chronological order (auxiliary to `estHist`). -/
noncomputable def estHistRev {d : ℕ} (A : FullInfoAlg d) (adv : Adversary d) (ε' : ℝ) (α : ℕ) :
    List (Fin d) → List (Fin d → ℝ)
  | [] => []
  | a :: r =>
      estHistRev A adv ε' α r ++
        [estLoss (adv.graph r.reverse) (adv.loss r.reverse) (A.dist (estHistRev A adv ε' α r))
          (gamma ε' α) (gammaPrime ε' α) a]

/-- **The estimated losses fed to `A`** (arXiv:1711.03639v5, Algorithm 1, lines 7–8, p.8).
`estHist A adv ε' α [I(1), …, I(t)]` is `[ℓ̃^1, …, ℓ̃^t]`: in round `s`, `A`'s vector
`p^s = A(ℓ̃^1, …, ℓ̃^{s−1})`, the adversary's `G^s, ℓ^s` (functions of `I(1), …, I(s−1)`), the
frozen set and `W^s` of Algorithm 1 with `γ = ε′/(4α)`, `γ′ = γ/3`, and the drawn arm `I(s)`
determine `ℓ̃^s`. -/
noncomputable def estHist {d : ℕ} (A : FullInfoAlg d) (adv : Adversary d) (ε' : ℝ) (α : ℕ)
    (arms : List (Fin d)) : List (Fin d → ℝ) :=
  estHistRev A adv ε' α arms.reverse

/-- **`A`'s vector `p^t` along an arm path** (arXiv:1711.03639v5, Algorithm 1, lines 1, 8):
`s : Fin T → Fin d` is the arm path (`s t` is the arm of round `t`, 0-based), and `p^t` is `A`
applied to the estimated losses of rounds `0, …, t−1`. -/
noncomputable def runP {d T : ℕ} (A : FullInfoAlg d) (adv : Adversary d) (ε' : ℝ) (α : ℕ)
    (s : Fin T → Fin d) (t : Fin T) : Fin d → ℝ :=
  A.dist (estHist A adv ε' α ((List.ofFn s).take t))

/-- **The feedback graph `G^t` along an arm path**: the adversary's graph after the arms of
rounds `0, …, t−1`. -/
def runGraph {d T : ℕ} (adv : Adversary d) (s : Fin T → Fin d) (t : Fin T) : SimpleGraph (Fin d) :=
  adv.graph ((List.ofFn s).take t)

/-- **The loss vector `ℓ^t` along an arm path**: the adversary's losses after the arms of rounds
`0, …, t−1`. -/
def runLoss {d T : ℕ} (adv : Adversary d) (s : Fin T → Fin d) (t : Fin T) : Fin d → ℝ :=
  adv.loss ((List.ofFn s).take t)

/-- **The sampling vector `w^t` of Algorithm 1 along an arm path** (arXiv:1711.03639v5,
Algorithm 1, lines 3–5, p.8), with `γ = ε′/(4α)` and `γ′ = γ/3`. -/
noncomputable def runW {d T : ℕ} (A : FullInfoAlg d) (adv : Adversary d) (ε' : ℝ) (α : ℕ)
    (s : Fin T → Fin d) (t : Fin T) : Fin d → ℝ :=
  sampling (runGraph adv s t) (runP A adv ε' α s t) (gamma ε' α) (gammaPrime ε' α)

/-- **Path probability** of Algorithm 1 (arXiv:1711.03639v5, Algorithm 1, line 6, `I(t) ∼ w^t`):
the probability that the arms drawn in rounds `0, …, T−1` are `s 0, …, s (T−1)`,
`∏_t w^t_{s t}`. -/
noncomputable def pathProb {d T : ℕ} (A : FullInfoAlg d) (adv : Adversary d) (ε' : ℝ) (α : ℕ)
    (s : Fin T → Fin d) : ℝ :=
  ∏ t : Fin T, runW A adv ε' α s t (s t)

open Classical in
/-- **Probability of an event** on arm paths when Algorithm 1 runs `A` with parameters `ε′`, `α`
against `adv` for `T` rounds: `Pr[E] = ∑_{s ∈ E} ∏_t w^t_{s t}`. -/
noncomputable def probEvent {d : ℕ} (T : ℕ) (A : FullInfoAlg d) (adv : Adversary d) (ε' : ℝ)
    (α : ℕ) (E : (Fin T → Fin d) → Prop) : ℝ :=
  ∑ s : Fin T → Fin d, if E s then pathProb A adv ε' α s else 0

/-- **ε-approximate regret** against arm `f` along an arm path (arXiv:1711.03639v5, §2.2, p.6):
`ApxReg(f, ε) = (1 − ε) ∑_t ℓ^t_{I(t)} − ∑_t ℓ^t_f`, with the losses the adversary produces
along the path. -/
def apxReg {d T : ℕ} (adv : Adversary d) (s : Fin T → Fin d) (f : Fin d) (ε : ℝ) : ℝ :=
  (1 - ε) * ∑ t : Fin T, runLoss adv s t (s t) - ∑ t : Fin T, runLoss adv s t f

end SmallLossGraph


