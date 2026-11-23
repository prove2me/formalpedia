-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsIdealWeight
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsIdealWeight
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:52:53.390796+00:00
-- url     : https://prove2.me/theorems/10f92290-68d2-4e87-a47f-c1bb2f16a580
-- title:
--   Exists Ideal Weight
-- statement:
--   Definitions and structural lemmas for Exists Ideal Weight, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsIdealWeight.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LineOppositeParabolicUnitaryLeviSectionEq
import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_RelIndexMulMeasure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemGUIffAdjJ
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RelIndexEqOfSurj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RelIndexUpLatEqSq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RelIndexUpLatEqProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnipLatIsOpenIsCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ImportsTerTail
import Theorems.Thm_GlobalTheory_LGrp_checkFun_apply
import Theorems.Thm_GlobalTheory_LGrp_checkFun_checkFun
import Theorems.Thm_GlobalTheory_LGrp_lFactor_singleton
import Theorems.Thm_GlobalTheory_LGrp_lFactor_zero
import Theorems.Thm_GlobalTheory_LGrp_ordL_eq
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
open MeasureTheory GlobalTheory.PRep GlobalTheory.LGrp Formalism.UG
open scoped NNReal
noncomputable section
namespace GlobalTheory.BorelUMod
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ}
abbrev upPairs (n : ℕ) : Finset (Fin n × Fin n) := Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2
theorem ord_rev {σ : L →+* L} (hσ : ∀ x, Valued.v (σ x) = Valued.v x) (t : torusU σ n) (i : Fin n) :
    ordL (t.1 i.rev : L) = -ordL (t.1 i : L) := by
  have h := (mem_GU_iff σ n _).1 t.2 i i
  rw [← map_inv, diagHom_val, diagHom_val, Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq] at h
  have := congrArg Valued.v h
  rw [hσ] at this
  simp [ordL_eq, ← this]
theorem isWeight_ord {σ : L →+* L} (hσ : ∀ x, Valued.v (σ x) = Valued.v x) (t : torusU σ n) :
    IsWeight fun i j : Fin n => ordL (t.1 i : L) - ordL (t.1 j : L) :=
  ⟨fun i j => by simp only [ord_rev hσ]; ring, fun i j k _ _ => by simp⟩
end GlobalTheory.BorelUMod


