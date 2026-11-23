-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WeilRepEvalZeroMemInduced
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WeilRepEvalZeroMemInduced
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:01:23.893798+00:00
-- url     : https://prove2.me/theorems/9fe46aae-7cf0-4cc3-90a5-f06f4f50c345
-- title:
--   Weil Rep Eval Zero Mem Induced
-- statement:
--   Definitions and structural lemmas for Weil Rep Eval Zero Mem Induced, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/WeilRepEvalZeroMemInduced.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ContinuousEtaleHermitianPairNormAndMapZeroStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaleHermitianPairEventuallyIsUnitContinuousAtInStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
namespace GlobalTheory.WeilSmooth
def lS {k : Type} [CommRing k] (u : k) : SpecialLinearGroup (Fin 2) k :=
  ⟨!![1, 0; u, 1], by simp [Matrix.det_fin_two]⟩
end GlobalTheory.WeilSmooth
noncomputable section
namespace GlobalTheory.WeilSmooth
open GlobalTheory.JR
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
end GlobalTheory.WeilSmooth


