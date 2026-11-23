-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PolarizationModuleUnitDual
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_PolarizationModuleUnitDual
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:06:46.119042+00:00
-- url     : https://prove2.me/theorems/9c9a4c60-2ca7-4cc8-9be6-31c139502b7e
-- title:
--   Polarization Module Unit Dual
-- statement:
--   Definitions and structural lemmas for Polarization Module Unit Dual, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PolarizationModuleUnitDual.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_PolarisationModuleIndex
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub


set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex
namespace GlobalTheory.PolModLattice
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
def altForm (x y : E) : E := x * bar y - bar x * y
def formSpan (L : Submodule (OF E) E) : Submodule (OF E) E :=
  Submodule.span (OF E) {w | ∃ x ∈ L, ∃ y ∈ L, w = altForm x y}
variable (E) in

def invDiff : Submodule (OF E) E where
  carrier := {v | ∃ w : maximalRealSubfield E, (w : E) = v ∧
    ∀ a : OF E, ∃ n : ℤ, Algebra.trace ℚ (maximalRealSubfield E) (w * (a : maximalRealSubfield E)) = n}
  zero_mem' := ⟨0, by simp, fun a => ⟨0, by simp⟩⟩
  add_mem' := by
    rintro _ _ ⟨w, rfl, hw⟩ ⟨w', rfl, hw'⟩
    refine ⟨w + w', by simp, fun a => ?_⟩
    obtain ⟨m, hm⟩ := hw a
    obtain ⟨n, hn⟩ := hw' a
    exact ⟨m + n, by rw [add_mul, map_add, hm, hn]; push_cast; rfl⟩
  smul_mem' := by
    rintro c _ ⟨w, rfl, hw⟩
    refine ⟨(c : maximalRealSubfield E) * w, ?_, fun a => ?_⟩
    · rw [Algebra.smul_def]; rfl
    · obtain ⟨n, hn⟩ := hw (c * a)
      exact ⟨n, by rw [← hn]; congr 1; push_cast; ring⟩
theorem coe_OF (a : OF E) : (((a : maximalRealSubfield E)) : E) = algebraMap (OF E) E a := rfl
theorem bar_real (w : maximalRealSubfield E) : bar (w : E) = w := IsCMField.complexConj_apply_eq_self E w
theorem bar_smul (a : OF E) (x : E) : bar (a • x) = a • bar x := by
  rw [Algebra.smul_def, Algebra.smul_def, bar, map_mul, ← bar, ← bar, ← coe_OF, bar_real]
def imagPart (E : Type) [Field E] [NumberField E] [IsCMField E] : Submodule (OF E) E where
  carrier := {j | bar j = -j}
  zero_mem' := by simp [bar]
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, bar, map_add] at ha hb ⊢
    rw [ha, hb]; ring
  smul_mem' := by
    intro c a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    rw [bar_smul, ha, smul_neg]
end GlobalTheory.PolModLattice


