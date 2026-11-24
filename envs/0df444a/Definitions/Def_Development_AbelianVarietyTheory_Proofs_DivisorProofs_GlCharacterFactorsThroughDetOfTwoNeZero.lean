-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GlCharacterFactorsThroughDetOfTwoNeZero
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_GlCharacterFactorsThroughDetOfTwoNeZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:00:34.623315+00:00
-- url     : https://prove2.me/theorems/707e6171-d415-4e55-b77f-2f0f29a22b11
-- title:
--   Gl Character Factors Through Det Of Two Ne Zero
-- statement:
--   Definitions and structural lemmas for Gl Character Factors Through Det Of Two Ne Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GlCharacterFactorsThroughDetOfTwoNeZero.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
namespace GlobalTheory.DetFactor
variable {k : Type} [Field k] {m : ℕ}
noncomputable def diagGL (n : ℕ) : (Fin n → kˣ) →* GL (Fin n) k :=
  (Units.map (diagonalRingHom (Fin n) k).toMonoidHom).comp MulEquiv.piUnits.symm.toMonoidHom
noncomputable def toGL {n : ℕ} (M : Matrix (Fin n) (Fin n) k) (h : M.det ≠ 0) : GL (Fin n) k :=
  nonsingInvUnit M (isUnit_iff_ne_zero.mpr h)
theorem det_transvection_ne {n : ℕ} {i j : Fin n} (hij : i ≠ j) (t : k) :
    (transvection i j t).det ≠ 0 := by
  rw [det_transvection_of_ne _ _ hij]; exact one_ne_zero
end GlobalTheory.DetFactor


