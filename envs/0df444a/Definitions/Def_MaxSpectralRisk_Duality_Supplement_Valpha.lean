-- Prove2me | Definitions.Def_MaxSpectralRisk_Duality_Supplement_Valpha
-- name    : MaxSpectralRisk_Duality_Supplement_Valpha
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T10:06:36.261764+00:00
-- url     : https://prove2.me/theorems/71fc6f9c-9c0f-4cf9-b8c2-fcd8a45c9c68
-- title:
--   (11)–(12) — MES value and the feasible-pair correspondence
-- statement:
--   Let $\mu,\nu$ be probability measures and $L:\mathcal X\times\mathcal Y\to\mathbb R$ a loss. With $\Pi(\mu,\nu)$ the published set of all couplings and $g_\alpha$ the published Rockafellar–Uryasev objective, define
--   $$
--   V_\alpha(\mu,\nu)=\sup_{\pi\in\Pi(\mu,\nu)}\inf_{b\in\mathbb R}g_\alpha(b,\pi),\qquad
--   F_\alpha(\mu,\nu)=\{(\pi,\Theta):\pi\in\Pi(\mu,\nu),\ \Theta\in G_\alpha(\pi)\}.
--   $$
--   The value is defined by the primal risk problem (11). The dual vertex representation (16) remains a theorem, so it is not assumed in this definition.
--
--   **Formalization Note** Supremum and infimum are in $\overline{\mathbb R}$. In the finite-space uses of this supplement, the loss is automatically bounded and integrable for every coupling, the inner infimum is attained, and (16) explicitly asserts a finite attained value. No claim about nonintegrable losses on infinite spaces is made. The alternative representation (12) is a consequence, rather than a second definition.
-- source:
--   Ghossoub, Hall, Saunders, Maximum Spectral Measures of Risk with given Risk Factor Marginal Distributions, arXiv:2010.14673v1, p. 14, (11) and definition after (12)

import Mathlib
import Definitions.Def_MaxSpectralRisk_Duality_Supplement_Envelope
import Definitions.Def_MaxSpectralRisk_Duality_Setting

namespace MaxSpectralRisk.Duality.Supplement

open MeasureTheory

/-- (11), p. 14: the MES value uses the published g and the published set of all
couplings. The extended-real sup and inf have no default at empty/unbounded sets.
In this supplement it is used only on finite spaces with probability marginals,
where the value is finite and the inner minimum is attained. -/
noncomputable def Valpha {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (α : ℝ) (L : X × Y → ℝ) (μ : Measure X) (ν : Measure Y) : EReal :=
  ⨆ π ∈ MongeKantorovichYao.transferencePlans μ ν,
    ⨅ b : ℝ, (MaxSpectralRisk.Duality.g α b π L : EReal)

/-- The feasible-pair correspondence following (12), p. 14. -/
def Falpha {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (α : ℝ) (μ : Measure X) (ν : Measure Y) :
    Set (ProbabilityMeasure (X × Y) × ProbabilityMeasure (X × Y)) :=
  {r | (r.1 : Measure (X × Y)) ∈ MongeKantorovichYao.transferencePlans μ ν ∧
    r.2 ∈ Galpha α r.1}

end MaxSpectralRisk.Duality.Supplement


