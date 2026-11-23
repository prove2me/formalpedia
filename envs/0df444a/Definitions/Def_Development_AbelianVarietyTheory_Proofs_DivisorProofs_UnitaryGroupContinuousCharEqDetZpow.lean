-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryGroupContinuousCharEqDetZpow
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryGroupContinuousCharEqDetZpow
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:03:06.608325+00:00
-- url     : https://prove2.me/theorems/91be5dd0-5cb2-44d8-810c-8a9985fddb06
-- title:
--   Unitary Group Continuous Char Eq Det Zpow
-- statement:
--   Definitions and structural lemmas for Unitary Group Continuous Char Eq Det Zpow, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitaryGroupContinuousCharEqDetZpow.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_CircleHomEqZpow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
namespace GlobalTheory.UnitaryChar
variable {n : ℕ}
noncomputable def diagHom (n : ℕ) : (Fin n → Circle) →* Matrix.unitaryGroup (Fin n) ℂ where
  toFun t := ⟨diagonal fun i => (t i : ℂ), by
    rw [Matrix.mem_unitaryGroup_iff, star_eq_conjTranspose, diagonal_conjTranspose,
      diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    ext i
    simp [Complex.mul_conj]⟩
  map_one' := by ext i j; simp
  map_mul' s t := by
    apply Subtype.ext
    simp [diagonal_mul_diagonal]
end GlobalTheory.UnitaryChar


