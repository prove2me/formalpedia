-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowMeanContinuity
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowMeanContinuity
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:28:34.848804+00:00
-- url     : https://prove2.me/theorems/ad30ec02-920f-4db4-a5f2-e51b0867670d
-- title:
--   Flow Mean Continuity
-- statement:
--   Definitions and structural lemmas for Flow Mean Continuity, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FlowMeanContinuity.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_RealEmbeddingCharacters
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FourSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.FD.FlowMeanContinuity
open NumberField Complex MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs
  ReciprocityTheory.ChartRestriction.G.FD.AdmissibleHermitianColumns ReciprocityTheory.ChartRestriction.G.FD.TransvectionPeriodicity ReciprocityTheory.ChartRestriction.G.FD.RealEmbeddingCharacters
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
variable (X : Data E r) (la : Wt X.Ψ r)
noncomputable def fjI (ξ : Fin r → E) (ν : X.Ψ → ℝ) (P : Frame X.Ψ r → ℂ) (x : Frame X.Ψ r)
    (s : X.Ψ → ℝ) : ℂ :=
  P (X.flow ξ (fun τ => (s τ : ℂ)) x) * cexp (-(4 * Real.pi * I) * ∑ τ, (ν τ : ℂ) * s τ)
end ReciprocityTheory.ChartRestriction.G.FD.FlowMeanContinuity


