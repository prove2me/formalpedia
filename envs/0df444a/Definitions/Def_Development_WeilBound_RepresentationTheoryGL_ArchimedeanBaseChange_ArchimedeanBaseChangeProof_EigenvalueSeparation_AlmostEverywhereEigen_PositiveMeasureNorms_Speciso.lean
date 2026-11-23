-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_EigenvalueSeparation_AlmostEverywhereEigen_PositiveMeasureNorms_Speciso
-- name    : Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_EigenvalueSeparation_AlmostEverywhereEigen_PositiveMeasureNorms_Speciso
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:05:24.187679+00:00
-- url     : https://prove2.me/theorems/f8caf5e6-3e0c-4454-8b76-05a17c51e6d7
-- title:
--   Speciso
-- statement:
--   Definitions and structural lemmas for Speciso, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ArchimedeanBaseChange/ArchimedeanBaseChangeProof/EigenvalueSeparation/AlmostEverywhereEigen/PositiveMeasureNorms/Speciso.lean

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_EigenvalueSeparation_AlmostEverywhereEigen_OneStepOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.Rg.BcB.E1 PositivityTheory.Rg.BcB.E2
noncomputable section
open MeasureTheory
open scoped ENNReal ComplexConjugate
namespace PositivityTheory.Rg.BcB.E2.P
namespace Speciso
variable {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] {S : Type}
  [TopologicalSpace S] [CompactSpace S] [T2Space S] [MeasurableSpace S] [BorelSpace S]
def Lmap (π : C(S, ℂ) →⋆ₐ[ℂ] (K →L[ℂ] K)) (v : K) : C(S, ℂ) →ₗ[ℂ] K where
  toFun f := π f v
  map_add' f g := by simp
  map_smul' c f := by simp
end Speciso
end PositivityTheory.Rg.BcB.E2.P


