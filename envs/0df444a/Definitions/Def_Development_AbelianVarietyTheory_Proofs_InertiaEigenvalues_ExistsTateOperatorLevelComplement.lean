-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsTateOperatorLevelComplement
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsTateOperatorLevelComplement
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T06:01:10.376161+00:00
-- url     : https://prove2.me/theorems/4db68a93-293a-47e2-9924-5b0e071bf0e2
-- title:
--   Exists Tate Operator Level Complement
-- statement:
--   Definitions and structural lemmas for Exists Tate Operator Level Complement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsTateOperatorLevelComplement.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormPrimitiveRootPrimePowSubOnePadicComplex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntegersEqSumZetaPowStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsCyclotomicTowerLevelGeneratorPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TateDecompositionCompletedCyclotomicIntegersStatement
import Theorems.Thm_GlobalTheory_TateDecomp_Ks_mono

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
noncomputable section
namespace GlobalTheory.Cyc.TateS
variable {l : ℕ} [Fact l.Prime]
theorem Ks_mono (K : FinExt l) {m n : ℕ} (h : m ≤ n) : Ks K m ≤ Ks K n := by
  refine sup_le_sup_left (IntermediateField.adjoin.mono _ _ _ ?_) _
  intro x hx
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le h
  simp only [Set.mem_setOf_eq] at hx ⊢
  rw [pow_add, pow_mul, hx, one_pow]
theorem mem_inC {F : IntermediateField ℚ_[l] (Om l)} {y : PadicComplex l} :
    y ∈ inC F ↔ ∃ x ∈ F, algebraMap (Om l) (PadicComplex l) x = y := Iff.rfl
def algC (K : FinExt l) : Subring (PadicComplex l) where
  carrier := {y | ∃ m, y ∈ inC (Ks K m)}
  zero_mem' := ⟨0, mem_inC.2 ⟨0, zero_mem _, map_zero _⟩⟩
  one_mem' := ⟨0, mem_inC.2 ⟨1, one_mem _, map_one _⟩⟩
  add_mem' := by
    rintro _ _ ⟨m, hm⟩ ⟨n, hn⟩
    obtain ⟨a, ha, rfl⟩ := mem_inC.1 hm
    obtain ⟨b, hb, rfl⟩ := mem_inC.1 hn
    exact ⟨max m n, mem_inC.2 ⟨a + b, add_mem (Ks_mono K (le_max_left _ _) ha)
      (Ks_mono K (le_max_right _ _) hb), map_add _ _ _⟩⟩
  mul_mem' := by
    rintro _ _ ⟨m, hm⟩ ⟨n, hn⟩
    obtain ⟨a, ha, rfl⟩ := mem_inC.1 hm
    obtain ⟨b, hb, rfl⟩ := mem_inC.1 hn
    exact ⟨max m n, mem_inC.2 ⟨a * b, mul_mem (Ks_mono K (le_max_left _ _) ha)
      (Ks_mono K (le_max_right _ _) hb), map_mul _ _ _⟩⟩
  neg_mem' := by
    rintro _ ⟨m, hm⟩
    obtain ⟨a, ha, rfl⟩ := mem_inC.1 hm
    exact ⟨m, mem_inC.2 ⟨-a, neg_mem ha, map_neg _ _⟩⟩
def Xalg (K : FinExt l) (j : ℕ) : AddSubgroup (PadicComplex l) := ⨆ (i : ℕ) (_ : j < i), Xlev K i
variable {act : GQ l →* (PadicComplex l ≃+* PadicComplex l)} {χ : GQ l →* ℚ_[l]ˣ}
end GlobalTheory.Cyc.TateS
namespace GlobalTheory.Cyc
open TateS
end GlobalTheory.Cyc


