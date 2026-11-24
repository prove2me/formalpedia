-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ColRepSemisimple
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ColRepSemisimple
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T18:34:12.330796+00:00
-- url     : https://prove2.me/theorems/224689d9-7666-4cd3-8dd6-6068d4690b6e
-- title:
--   Col Rep Semisimple
-- statement:
--   Definitions and structural lemmas for Col Rep Semisimple, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ColRepSemisimple.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataN
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NonemptyLinearEquivOfCharpolyEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.TraceConj
variable {Γ k : Type} [Group Γ] [Field k] {a : ℕ}
def colRep (ρ : Γ →* GL (Fin a) k) : Representation k Γ (Fin a → k) where
  toFun g := Matrix.toLin' ((ρ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k)
  map_one' := by
    rw [map_one, Units.val_one, Matrix.toLin'_one]
    rfl
  map_mul' g h := by
    rw [map_mul, Units.val_mul, Matrix.toLin'_mul]
    rfl
end GlobalTheory.TraceConj
end


