-- Prove2me | Definitions.Def_ModelRiskOT_PrimalOpt_GrowthAssumptions
-- name    : ModelRiskOT_PrimalOpt_GrowthAssumptions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T01:40:04.869877+00:00
-- url     : https://prove2.me/theorems/bfd8db55-f1d1-45d1-9e52-814cf30ec27b
-- title:
--   Assumptions (A3) and (A4): growth conditions on c and f in a normed space (p. 27)
-- statement:
--   Let $E$ be a normed space with norm $\|\cdot\|$, $c:E\times E\to\mathbb R$ a cost and $f:E\to\mathbb R$.
--
--   1. **Assumption (A3)**: there are a nondecreasing $g:[0,\infty)\to[0,\infty)$ with $g(t)\uparrow\infty$ as $t\to\infty$ and a constant $C>0$ such that
--   $$c(x,y)\ge g(\|x-y\|)\quad\text{whenever }\|x-y\|>C.$$
--   2. **Assumption (A4)**: there are an increasing $h:[0,\infty)\to[0,\infty)$ with $h(t)\uparrow\infty$ as $t\to\infty$ and a constant $K>0$ such that
--   $$\sup_{x,y\in E}\frac{f(y)-f(x)}{1+h(\|x-y\|)}\le K;$$
--   and for every $\varepsilon>0$ there is $C_\varepsilon>0$ with $f(y)-f(x)\le\varepsilon\,(1+c(x,y))$ for all $x,y$ with $\|x-y\|>C_\varepsilon$.
--
--   (A3) says the cost grows without bound with the distance moved; (A4) says $f$ grows at most like $h$ and, at long range, more slowly than the cost. They are the sufficient conditions of Corollary 1.
--
--   **Formalization Note** $g$ and $h$ are functions $\mathbb R\to\mathbb R$ constrained on $[0,\infty)$: $g$ monotone and $h$ strictly monotone there, both nonnegative there, both tending to $+\infty$. "Increasing" for $h$ is read as strictly increasing; the proof only uses that $h$ is nondecreasing. The supremum bound is stated pointwise, which is equivalent; the denominator is at least $1$.
-- source:
--   Blanchet & Murthy, Quantifying Distributional Model Risk via Optimal Transport, arXiv:1604.01446v2, p. 27, Assumption 3 (A3) and Assumption 4 (A4)

import Mathlib

namespace ModelRiskOT.PrimalOpt

open Filter

/-- **Assumption 3 (A3)** (p. 27), on a normed space `E`: there are a nondecreasing
`g : ℝ₊ → ℝ₊` with `g(t) ↑ ∞` as `t → ∞` and a constant `C > 0` such that
`c(x, y) ≥ g(‖x − y‖)` whenever `‖x − y‖ > C`. -/
def AssumptionA3 {E : Type*} [NormedAddCommGroup E] (c : E → E → ℝ) : Prop :=
  ∃ g : ℝ → ℝ, MonotoneOn g (Set.Ici 0) ∧ (∀ t, 0 ≤ t → 0 ≤ g t) ∧ Tendsto g atTop atTop ∧
    ∃ C : ℝ, 0 < C ∧ ∀ x y : E, C < ‖x - y‖ → g ‖x - y‖ ≤ c x y

/-- **Assumption 4 (A4)** (p. 27), on a normed space `E`: there are an increasing
`h : ℝ₊ → ℝ₊` with `h(t) ↑ ∞` as `t → ∞` and a constant `K > 0` such that
`sup_{x,y} (f(y) − f(x)) / (1 + h(‖x − y‖)) ≤ K`; and for every `ε > 0` there is `C_ε > 0` with
`f(y) − f(x) ≤ ε (1 + c(x, y))` whenever `‖x − y‖ > C_ε`. -/
def AssumptionA4 {E : Type*} [NormedAddCommGroup E] (c : E → E → ℝ) (f : E → ℝ) : Prop :=
  (∃ h : ℝ → ℝ, StrictMonoOn h (Set.Ici 0) ∧ (∀ t, 0 ≤ t → 0 ≤ h t) ∧ Tendsto h atTop atTop ∧
    ∃ K : ℝ, 0 < K ∧ ∀ x y : E, (f y - f x) / (1 + h ‖x - y‖) ≤ K) ∧
  ∀ ε : ℝ, 0 < ε → ∃ Cε : ℝ, 0 < Cε ∧
    ∀ x y : E, Cε < ‖x - y‖ → f y - f x ≤ ε * (1 + c x y)

end ModelRiskOT.PrimalOpt


