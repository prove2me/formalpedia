-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsIsUnitDetKrylovMatrixOfSeparable
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsIsUnitDetKrylovMatrixOfSeparable
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T22:00:46.618746+00:00
-- url     : https://prove2.me/theorems/030bf816-dddd-42d8-89b8-2543a4490afb
-- title:
--   Exists Is Unit Det Krylov Matrix Of Separable
-- statement:
--   Definitions and structural lemmas for Exists Is Unit Det Krylov Matrix Of Separable, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsIsUnitDetKrylovMatrixOfSeparable.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KrylovApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LeftMulMatrixTransfer
import Theorems.Thm_GlobalTheory_ClassParam_exists_cyclic_field

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Polynomial
namespace GlobalTheory.LeviDesc.Krylov
theorem exists_isUnit_det_krylov_of_separable {F : Type} [Field F] {r : ℕ}
    (y : Matrix (Fin r) (Fin r) F) (hs : y.charpoly.Separable) :
    ∃ e : Fin r → F, IsUnit (GlobalTheory.LeviDesc.Krylov.krylov y e).det := by
  obtain ⟨v, hv⟩ := GlobalTheory.ClassParam.exists_cyclic_field y hs
  exact ⟨v, isUnit_iff_ne_zero.2 hv⟩
example : ∀ {F : Type} [Field F] {r : ℕ} (y : Matrix (Fin r) (Fin r) F), y.charpoly.Separable → ∃ e : Fin r → F, IsUnit (GlobalTheory.LeviDesc.Krylov.krylov y e).det :=
  @exists_isUnit_det_krylov_of_separable
end GlobalTheory.LeviDesc.Krylov


