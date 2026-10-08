-- Prove2me | Definitions.Def_ModelRiskOT_Duality_primalValue
-- name    : ModelRiskOT_Duality_primalValue
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T17:15:37.966089+00:00
-- url     : https://prove2.me/theorems/c921e8c7-9da2-4e2d-813b-e328f9711041
-- title:
--   Primal objective $I(\pi)=\int f(y)\,d\pi(x,y)$ and value $I=\sup\{I(\pi):\pi\in\Phi_{\mu,\delta}\}$ (3)
-- statement:
--   Let $f:S\to\mathbb R$ and let $\pi$ be a measure on $S\times S$. The **primal objective** is
--
--   $$I(\pi)=\int f(y)\,d\pi(x,y)\in[-\infty,\infty],$$
--
--   computed as $\int f^+(y)\,d\pi-\int f^-(y)\,d\pi$ with $\infty-\infty=-\infty$. The **primal value** is the worst-case expectation of $f$ over the optimal-transport ball of radius $\delta$ around $\mu$,
--
--   $$I=\sup\{I(\pi):\pi\in\Phi_{\mu,\delta}\}\in[-\infty,\infty].$$
--
--   This is equation (3) of the paper: the quantity of interest $\sup\{\int f\,d\nu : d_c(\mu,\nu)\le\delta\}$ rewritten over transport plans.
--
--   **Formalization Note** Couplings with $\int f^-\,d\pi=\infty$ contribute $-\infty$ and so never raise the supremum; this is the paper's interpretation $\sup\{\int f d\nu : d_c(\mu,\nu)\le\delta,\ \int f^-d\nu<\infty\}$ of footnote 2, which the paper shows does not change the supremum.
-- source:
--   Blanchet & Murthy, Quantifying Distributional Model Risk via Optimal Transport, arXiv:1604.01446v2, p. 6, Eq. (3) and the definition of I(π); p. 5, footnote 2

import Mathlib
import Definitions.Def_ModelRiskOT_Duality_extIntegral
import Definitions.Def_ModelRiskOT_Duality_primalFeasible

namespace ModelRiskOT.Duality

open MeasureTheory

/-- The primal objective `I(π) = ∫ f(y) dπ(x, y)` (Blanchet & Murthy, arXiv:1604.01446v2, p. 6),
in `EReal`: `∫ f⁺(y) dπ − ∫ f⁻(y) dπ`, with `∞ − ∞ = ⊥` (see `extIntegral`). -/
noncomputable def primalObj {S : Type*} [MeasurableSpace S] (f : S → ℝ) (π : Measure (S × S)) :
    EReal :=
  extIntegral π (fun p => (f p.2 : EReal))

/-- The primal value **(3)**, `I = sup {I(π) : π ∈ Φ_{μ,δ}}` (arXiv:1604.01446v2, p. 6), a
supremum in `EReal`. Couplings with `∫ f⁻ dπ = ∞` contribute `⊥`, which is the paper's reading
`sup{∫ f dν : d_c(μ, ν) ≤ δ, ∫ f⁻ dν < ∞}` of footnote 2 (p. 5). -/
noncomputable def primalValue {S : Type*} [MeasurableSpace S] (c : S → S → ℝ) (f : S → ℝ)
    (μ : Measure S) (δ : ℝ) : EReal :=
  ⨆ π ∈ primalFeasible c μ δ, primalObj f π

end ModelRiskOT.Duality


