-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_HermitianLattices_ExistsZsmulMemOfIsLattice
-- name    : Development_AbelianVarietyTheory_Definitions_HermitianLattices_ExistsZsmulMemOfIsLattice
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-24T18:38:04.270802+00:00
-- url     : https://prove2.me/theorems/184e3079-ca07-43fd-9d3e-8603b9df19e6
-- title:
--   Exists Zsmul Mem Of Is Lattice
-- statement:
--   Definitions and structural lemmas for Exists Zsmul Mem Of Is Lattice, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/HermitianLattices/ExistsZsmulMemOfIsLattice.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorsionNonvanishStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_Imports
import Theorems.Thm_GlobalTheory_IntSmulIntegral_exists_int_smul_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory
open NumberField Matrix
open ReciprocityTheory.MultiplicativeHeights (IsLattice)
open scoped TensorProduct nonZeroDivisors
variable {r : ℕ}
section Lattice
variable {K : Type} [Field K] [NumberField K]
variable {M M' : Type} [AddCommGroup M] [Module (𝓞 K) M] [AddCommGroup M'] [Module (𝓞 K) M']
theorem exists_zsmul_mem_of_isLattice {Λ : Submodule (𝓞 K) (Fin r → K)} (hΛ : IsLattice Λ)
    (v : Fin r → K) : ∃ n : ℤ, n ≠ 0 ∧ n • v ∈ Λ := by
  first
  | exact @_root_.GlobalTheory.IntSmulIntegral.exists_int_smul_mem
  | exact _root_.GlobalTheory.IntSmulIntegral.exists_int_smul_mem
  | (apply _root_.GlobalTheory.IntSmulIntegral.exists_int_smul_mem <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntSmulIntegral.exists_int_smul_mem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntSmulIntegral.exists_int_smul_mem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntSmulIntegral.exists_int_smul_mem ..)
def IsLatticeEmb (φ : M →ₗ[𝓞 K] (Fin r → K)) : Prop :=
  Function.Injective φ ∧ IsLattice (LinearMap.range φ)
theorem isLatticeEmb_of_span [Module.Finite (𝓞 K) M] {φ : M →ₗ[𝓞 K] (Fin r → K)}
    (hi : Function.Injective φ) (hs : Submodule.span K (Set.range φ) = ⊤) : IsLatticeEmb φ :=
  ⟨hi, by rw [LinearMap.range_eq_map]; exact Module.Finite.fg_top.map _, hs⟩
namespace IsLatticeEmb
variable {φ : M →ₗ[𝓞 K] (Fin r → K)}
theorem exists_zsmul (h : IsLatticeEmb φ) (v : Fin r → K) :
    ∃ n : ℤ, n ≠ 0 ∧ ∃ x, φ x = n • v :=
  exists_zsmul_mem_of_isLattice h.2 v
theorem isLocalizedModule_int (h : IsLatticeEmb φ) :
    IsLocalizedModule ℤ⁰ (φ.restrictScalars ℤ) where
  map_units s := by
    have hs : ((s : ℤ) : ℚ) ≠ 0 := by exact_mod_cast nonZeroDivisors.coe_ne_zero s
    rw [Module.End.isUnit_iff]
    have : ⇑(algebraMap ℤ (Module.End ℤ (Fin r → K)) s) = fun v => ((s : ℤ) : ℚ) • v := by
      funext v; rw [Module.algebraMap_end_apply, Int.cast_smul_eq_zsmul]
    rw [this]
    exact MulAction.bijective (Units.mk0 _ hs)
  surj v := by
    obtain ⟨n, hn, x, hx⟩ := h.exists_zsmul v
    exact ⟨(x, ⟨n, mem_nonZeroDivisors_of_ne_zero hn⟩), hx.symm⟩
  exists_of_eq hxy := ⟨1, by rw [h.1 hxy]⟩
theorem isBaseChange_rat (h : IsLatticeEmb φ) : IsBaseChange ℚ (φ.restrictScalars ℤ) :=
  (isLocalizedModule_iff_isBaseChange ℤ⁰ ℚ _).mp h.isLocalizedModule_int
def extend (h : IsLatticeEmb φ) (β : LinearMap.BilinForm ℤ M) :
    LinearMap.BilinForm ℚ (Fin r → K) :=
  LinearMap.BilinForm.congr h.isBaseChange_rat.equiv (β.baseChange ℚ)
end IsLatticeEmb
end Lattice
example {K : Type} [Field K] [NumberField K] :
    IsLatticeEmb ((Algebra.linearMap (𝓞 K) K).compLeft (Fin r)) := by
  refine isLatticeEmb_of_span (fun x y h => funext fun i => RingOfIntegers.ext (congrFun h i)) ?_
  rw [eq_top_iff, ← (Pi.basisFun K (Fin r)).span_eq]
  refine Submodule.span_mono ?_
  rintro _ ⟨i, rfl⟩
  refine ⟨Pi.single i 1, funext fun j => ?_⟩
  by_cases h : j = i
  · subst h; simp
  · simp [h]
end GlobalTheory


