-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CommutingIntegralMatrixDecompose
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CommutingIntegralMatrixDecompose
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:37:27.702648+00:00
-- url     : https://prove2.me/theorems/bfa91bc7-7611-4fe3-969a-f6b6d7649918
-- title:
--   Commuting Integral Matrix Decompose
-- statement:
--   Definitions and structural lemmas for Commuting Integral Matrix Decompose, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CommutingIntegralMatrixDecompose.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CommOfBezout
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CommutingIntegralMatrixTopnilStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitDiscAlg
namespace GlobalTheory.UnitDiscAlg.Red
variable {E : Type} [NontriviallyNormedField E] [IsUltrametricDist E] {n : ℕ}
def Sm (s : Matrix (Fin n) (Fin n) E) : Prop := ∀ i j, ‖s i j‖ < 1
end GlobalTheory.UnitDiscAlg.Red
namespace GlobalTheory.UnitDiscAlg.Red
variable {E : Type} [NontriviallyNormedField E] [IsUltrametricDist E] {n : ℕ}
end GlobalTheory.UnitDiscAlg.Red
namespace GlobalTheory.UnitDiscAlg.Red
end GlobalTheory.UnitDiscAlg.Red


