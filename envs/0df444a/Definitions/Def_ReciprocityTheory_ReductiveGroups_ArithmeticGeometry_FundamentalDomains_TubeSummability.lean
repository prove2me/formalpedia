-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_TubeSummability
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_TubeSummability
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:31:26.637408+00:00
-- url     : https://prove2.me/theorems/fb06a7a4-de8d-46c8-8990-08590d2235d7
-- title:
--   Tube Summability
-- statement:
--   Definitions and structural lemmas for Tube Summability, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/TubeSummability.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowMeanContinuity
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FourIndep
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FourBasic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.FD.TubeSummability
open NumberField Complex MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs
  ReciprocityTheory.ChartRestriction.G.FD.AdmissibleHermitianColumns ReciprocityTheory.ChartRestriction.G.FD.TransvectionPeriodicity ReciprocityTheory.ChartRestriction.G.FD.RealEmbeddingCharacters
  ReciprocityTheory.ChartRestriction.G.FD.FlowMeanContinuity ReciprocityTheory.L2DbarEstimates.Y
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
section line
variable (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (ξ : Fin r → E) (x : Frame X.Ψ r)
  {n : ℕ} (ω : Fin n → X.Ψ → ℝ)
def Lc (t : Fin n → ℂ) : X.Ψ → ℂ := fun τ => ∑ j, t j * (ω j τ : ℂ)
noncomputable def hline (t : Fin n → ℂ) : ℂ := P (X.flow ξ (Lc X ω t) x)
def Om : Set (Fin n → ℝ) := (Fintype.linearCombination ℝ ω) ⁻¹' admissibleImaginary X ξ x
variable {X ξ x}
variable (X ξ x)
end line
end ReciprocityTheory.ChartRestriction.G.FD.TubeSummability


