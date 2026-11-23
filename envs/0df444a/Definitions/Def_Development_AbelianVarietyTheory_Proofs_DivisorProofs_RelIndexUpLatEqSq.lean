-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RelIndexUpLatEqSq
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_RelIndexUpLatEqSq
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:45:54.1058+00:00
-- url     : https://prove2.me/theorems/f32f6119-ff0c-48a4-84c9-4d76c01711e3
-- title:
--   Rel Index Up Lat Eq Sq
-- statement:
--   Definitions and structural lemmas for Rel Index Up Lat Eq Sq, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RelIndexUpLatEqSq.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LineOppositeParabolicUnitaryLeviSectionEq
import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemGUIffAdjJ
import Theorems.Thm_GlobalTheory_LGrp_checkFun_apply
import Theorems.Thm_GlobalTheory_LGrp_checkFun_checkFun
import Theorems.Thm_GlobalTheory_LGrp_lFactor_singleton
import Theorems.Thm_GlobalTheory_LGrp_lFactor_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.LGrp.checkFun_apply
attribute [local simp] GlobalTheory.LGrp.checkFun_checkFun
attribute [local simp] GlobalTheory.LGrp.lFactor_singleton
attribute [local simp] GlobalTheory.LGrp.lFactor_zero


set_option autoImplicit false
open GlobalTheory.LGrp GlobalTheory.BorelUMod Formalism.UG
noncomputable section
namespace GlobalTheory.BorelUMod
variable {L : Type} [Field L] {n : ℕ}
def skewPair (σ : L →+* L) (θ d : L) :
    Matrix (Fin n) (Fin n) L →+ Matrix (Fin n) (Fin n) L × Matrix (Fin n) (Fin n) L :=
  AddMonoidHom.mk' (fun X => (X - θ • (X + adjJ σ X), d • (X + adjJ σ X))) (fun X Y => by
    ext i j <;> simp [adjJ] <;> ring)
variable [Valued L (WithZero (Multiplicative ℤ))]
end GlobalTheory.BorelUMod


