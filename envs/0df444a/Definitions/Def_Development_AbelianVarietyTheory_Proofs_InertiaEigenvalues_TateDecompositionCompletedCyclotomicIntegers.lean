-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TateDecompositionCompletedCyclotomicIntegers
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TateDecompositionCompletedCyclotomicIntegers
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T03:09:46.144066+00:00
-- url     : https://prove2.me/theorems/b0f7c64a-76e2-408c-9a88-73d158a479e9
-- title:
--   Tate Decomposition Completed Cyclotomic Integers
-- statement:
--   Definitions and structural lemmas for Tate Decomposition Completed Cyclotomic Integers, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TateDecompositionCompletedCyclotomicIntegers.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntegersEqSumZetaPowStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
open scoped Pointwise
noncomputable section
namespace GlobalTheory.TateDecomp
variable {l : ℕ} [Fact l.Prime]
abbrev io (l : ℕ) [Fact l.Prime] : Om l →+* PadicComplex l := algebraMap (Om l) (PadicComplex l)
def subC (F : IntermediateField ℚ_[l] (Om l)) : Subfield (PadicComplex l) := F.toSubfield.map (io l)
theorem intC_iff {F : IntermediateField ℚ_[l] (Om l)} {y : PadicComplex l} :
    y ∈ intC F ↔ y ∈ subC F ∧ ‖y‖ ≤ 1 := Iff.rfl
def intA (F : IntermediateField ℚ_[l] (Om l)) : AddSubgroup (PadicComplex l) where
  carrier := intC F
  zero_mem' := ⟨zero_mem (subC F), by simp⟩
  add_mem' := fun {a b} ha hb => ⟨add_mem (intC_iff.1 ha).1 (intC_iff.1 hb).1,
    (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha.2 hb.2)⟩
  neg_mem' := fun {a} ha => ⟨neg_mem (intC_iff.1 ha).1, by rw [norm_neg]; exact ha.2⟩
def Xsum (K : FinExt l) (j : ℕ) : AddSubgroup (PadicComplex l) := ⨆ (i : ℕ) (_ : j < i), Xlev K i
def Xfin (K : FinExt l) (j : ℕ) (n : ℕ) : AddSubgroup (PadicComplex l) :=
  Nat.rec ⊥ (fun m G => G ⊔ Xlev K (j + (m + 1))) n
end GlobalTheory.TateDecomp


