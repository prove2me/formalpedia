-- Prove2me | Definitions.Def_RiskDistMDP_DPP_G
-- name    : RiskDistMDP_DPP_G
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:55:29.375464+00:00
-- url     : https://prove2.me/theorems/9a2d9a70-21fa-4521-8f4f-38cd00acf307
-- title:
--   Operator $G^\lambda_t v(x)=\sigma_{t,x}(\widetilde P^v_{t,x,\lambda})$ (3.2)–(3.3)
-- statement:
--   For $t\in\mathbb N$, $\lambda\in\Lambda$ and $v\in\ell^\infty(\mathbb X,\mathcal B(\mathbb X))$, let $\widetilde P^v_{t,x,\lambda}$ be the law of $C_t(x,A,Y)+\gamma v(Y)$ where $(A,Y)$ has joint law $\lambda(da)P(t,x,a,dy)$:
--   $$\widetilde P^v_{t,x,\lambda}(B)=\int_{\mathbb A}\int_{\mathbb X}\mathbb 1_B\big(C_t(x,a,y)+\gamma v(y)\big)\,P(t,x,a,dy)\,\lambda(da),\qquad B\in\mathcal B(\mathbb R).$$
--   The one-step risk operator is
--   $$G^\lambda_t v(x):=\sigma_{t,x}\big(\widetilde P^v_{t,x,\lambda}\big).$$
--   It evaluates the risk of the immediate cost plus the discounted continuation value when the randomized action $\lambda$ is used at state $x$.
--
--   **Formalization Note** The law is the Giry bind of $\lambda$ with $a\mapsto P(t,x,a,\cdot)\circ(C_t(x,a,\cdot)+\gamma v)^{-1}$, which is (3.3) for measurable data. $\lambda$ is written `l`. The value is in `EReal`; it is finite under Assumption 2.13 (iv) (Lemma 3.1).
-- source:
--   Cheng & Jaimungal, Risk-Averse Markov Decision Processes through a Distributional Lens, arXiv:2203.09612v4, (3.2)–(3.3), pp. 14–15

import Mathlib
import Definitions.Def_RiskDistMDP_DPP_RiskMDP

set_option autoImplicit false

open MeasureTheory

namespace RiskDistMDP.DPP

/-- The law `P̃^v_{t,x,λ}` of arXiv:2203.09612v4, (3.3), p.15: the distribution of
`C_t(x, A, Y) + γ v(Y)` where `(A, Y)` has joint law `λ(da) P(t, x, a, dy)`,
`P̃^v_{t,x,λ}(B) = ∫_𝔸 ∫_𝕏 𝟙_B(C_t(x,a,y) + γ v(y)) P(t,x,a,dy) λ(da)`.

**Formalization Note** Written as the Giry bind of `λ` with `a ↦ (P t x a).map (C_t(x,a,·) + γ v)`;
for measurable `v` (and `C_t`, `P` measurable, as in `BorelMDP.Standing`) this is the measure (3.3).
`λ` is written `l`. -/
noncomputable def lawG {𝕏 𝔸 : Type*} [MeasurableSpace 𝕏] [MeasurableSpace 𝔸] (R : RiskMDP 𝕏 𝔸)
    (t : ℕ) (x : 𝕏) (l : ProbabilityMeasure 𝔸) (v : 𝕏 → ℝ) : Measure ℝ :=
  (l : Measure 𝔸).bind fun a => (R.P t x a : Measure 𝕏).map fun y => R.C t x a y + R.γ * v y

/-- The operator `G^λ_t v(x) := σ_{t,x}(P̃^v_{t,x,λ})` of arXiv:2203.09612v4, (3.2), p.14, for
`t ∈ ℕ`, `λ ∈ Λ` and `v ∈ ℓ^∞(𝕏, ℬ(𝕏))`.

**Formalization Note** Values in `EReal`; Lemma 3.1 (`lemma_3_1`) states that they are finite
under Assumption 2.13 (iv). -/
noncomputable def G {𝕏 𝔸 : Type*} [MeasurableSpace 𝕏] [MeasurableSpace 𝔸] (R : RiskMDP 𝕏 𝔸)
    (t : ℕ) (l : ProbabilityMeasure 𝔸) (v : 𝕏 → ℝ) (x : 𝕏) : EReal :=
  R.σ t x (lawG R t x l v)

end RiskDistMDP.DPP


