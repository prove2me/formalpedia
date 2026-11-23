-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DvdAllPowOfFrobeniusEqKilledByPerfectPoints
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DvdAllPowOfFrobeniusEqKilledByPerfectPoints
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:35:58.67281+00:00
-- url     : https://prove2.me/theorems/b433124f-d1ba-4f63-a56f-41a9a305e9aa
-- title:
--   Dvd All Pow Of Frobenius Eq Killed By Perfect Points
-- statement:
--   Definitions and structural lemmas for Dvd All Pow Of Frobenius Eq Killed By Perfect Points, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/DvdAllPowOfFrobeniusEqKilledByPerfectPoints.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FrobeniusPowEquationDvdAllPowStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PowDvdOfVanishingAtPerfectValuationPointsStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped NNReal
namespace GlobalTheory.PointsKey
def oneSubMul {R : Type} [CommRing R] (u : R) : Submonoid R where
  carrier := {x | ∃ r, x = 1 - u * r}
  mul_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a + b - u * a * b, by ring⟩
  one_mem' := ⟨0, by simp⟩
end GlobalTheory.PointsKey


