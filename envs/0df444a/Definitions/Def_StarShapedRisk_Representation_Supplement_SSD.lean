-- Prove2me | Definitions.Def_StarShapedRisk_Representation_Supplement_SSD
-- name    : StarShapedRisk_Representation_Supplement_SSD
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T06:44:57.2117+00:00
-- url     : https://prove2.me/theorems/30c2ec1e-7fc6-46b8-814e-84b3fe6fc2bd
-- title:
--   Second-order stochastic dominance and SSD-consistency
-- statement:
--   For bounded measurable losses $X,Y$ under $P$, define $X\succeq_{\rm SSD}Y$ by
--   $$E_P[u(-X)]\ge E_P[u(-Y)]$$
--   for every increasing concave $u:\mathbb R\to\mathbb R$ for which both expectations exist. A functional $\rho$ is SSD-consistent when
--   $$X\succeq_{\rm SSD}Y\ \Longrightarrow\ \rho(X)\le\rho(Y).$$
--   The minus signs convert losses into gains before utility is evaluated. These notions distinguish Theorem 4 from the law-invariant characterization. Integrability records existence of expectations rather than using the default value of a nonintegrable Bochner integral; for globally concave real utilities on bounded positions under a probability it holds automatically.
-- source:
--   Castagnoli, Cattelan, Maccheroni, Tebaldi, Wang, Star-Shaped Risk Measures, Operations Research 70(5) (2022), DOI 10.1287/opre.2022.2303, p. 2646, def-ssd

import Mathlib
import Definitions.Def_StarShapedRisk_LawInvariant_Model

namespace StarShapedRisk.Representation.Supplement

/-- Second-order stochastic dominance, comparing utilities of gains, with existence of expectations. -/
def SSD {Ω : Type*} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
    (X Y : StarShapedRisk.LawInvariant.Positions Ω) : Prop :=
  ∀ u : ℝ → ℝ, Monotone u → ConcaveOn ℝ Set.univ u →
    MeasureTheory.Integrable (fun ω => u (-X.1 ω)) P →
    MeasureTheory.Integrable (fun ω => u (-Y.1 ω)) P →
    (∫ ω, u (-Y.1 ω) ∂P) ≤ ∫ ω, u (-X.1 ω) ∂P

/-- SSD-consistency in the loss convention. -/
def IsSSDConsistent {Ω : Type*} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
    (ρ : StarShapedRisk.LawInvariant.Positions Ω → ℝ) : Prop :=
  ∀ X Y, SSD P X Y → ρ X ≤ ρ Y

end StarShapedRisk.Representation.Supplement


