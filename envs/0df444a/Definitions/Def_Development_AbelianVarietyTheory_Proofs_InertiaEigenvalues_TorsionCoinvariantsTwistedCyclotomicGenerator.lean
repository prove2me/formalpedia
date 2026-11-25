-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TorsionCoinvariantsTwistedCyclotomicGenerator
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TorsionCoinvariantsTwistedCyclotomicGenerator
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T15:46:43.06395+00:00
-- url     : https://prove2.me/theorems/ee2eefc9-0cb5-47f4-b557-01d6168beadc
-- title:
--   Torsion Coinvariants Twisted Cyclotomic Generator
-- statement:
--   Definitions and structural lemmas for Torsion Coinvariants Twisted Cyclotomic Generator, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TorsionCoinvariantsTwistedCyclotomicGenerator.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormPrimitiveRootPrimePowSubOnePadicComplex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PadicNormZpowSubOnePadicValInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TateDecompositionCompletedCyclotomicIntegersStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormZpowSubOneLeTer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AevalProdEqZeroHodgeTateCyclotomicFrameStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc Polynomial
namespace GlobalTheory.CycCoinv
variable {l : ℕ} [hl : Fact l.Prime]
noncomputable def fld (F : IntermediateField ℚ_[l] (Om l)) : Subfield (PadicComplex l) :=
  F.toSubfield.map (algebraMap (Om l) (PadicComplex l))
theorem mem_fld (F : IntermediateField ℚ_[l] (Om l)) (y : PadicComplex l) :
    y ∈ fld F ↔ y ∈ inC F := by
  simp [fld, inC, PadicComplex.coe_eq]
noncomputable def intR (F : IntermediateField ℚ_[l] (Om l)) : Subring (PadicComplex l) where
  carrier := intC F
  mul_mem' := fun {a b} ha hb => ⟨(mem_fld F _).1 (mul_mem ((mem_fld F _).2 ha.1) ((mem_fld F _).2 hb.1)),
    by rw [norm_mul]; exact mul_le_one₀ ha.2 (norm_nonneg _) hb.2⟩
  one_mem' := ⟨(mem_fld F _).1 (one_mem _), by simp⟩
  add_mem' := fun {a b} ha hb => ⟨(mem_fld F _).1 (add_mem ((mem_fld F _).2 ha.1) ((mem_fld F _).2 hb.1)),
    (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha.2 hb.2)⟩
  zero_mem' := ⟨(mem_fld F _).1 (zero_mem _), by simp⟩
  neg_mem' := fun {a} ha => ⟨(mem_fld F _).1 (neg_mem ((mem_fld F _).2 ha.1)), by simpa using ha.2⟩
end GlobalTheory.CycCoinv


