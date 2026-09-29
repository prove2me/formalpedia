-- Prove2me | solution 1 for AutomorphicForm.setIntegral_mul_pseudoEisenstein_eq_integral_rationalTorusUnipotentQuotient_constantTerm_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/e285cd93-8f69-552f-893b-deda3b8716af

import Definitions.Def_AutomorphicForm_SlabProfile
import Definitions.Def_AutomorphicForm_RationalTorusUnipotentQuotient
import Definitions.Def_AutomorphicForm_BorelSubgroup
import Definitions.Def_Mathlib_LinearAlgebra_Countable
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine
import Theorems.Thm_AutomorphicForm_integrableOn_tsum_and_setIntegral_tsum_comp_globalPoints_inv_mul_eq_integral_haarQuotient_setIntegral
import Theorems.Thm_AutomorphicForm_isFundamentalDomain_boxSheet_rationalTorusUnipotent
import Theorems.Thm_AutomorphicForm_isClosed_rationalTorusUnipotent
import Theorems.Thm_AutomorphicForm_isHaarMeasure_rationalTorusUnipotentHaar_and_isMulRightInvariant
import Theorems.Thm_AutomorphicForm_constantTerm_adelicBox_globalPoints_mul_of_mem_borelSubgroup
import Theorems.Thm_AutomorphicForm_constantTerm_adelicBox_unipotentGL2_mul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_setIntegral_mul_pseudoEisenstein_eq_integral_rationalTorusUnipotentQuotient_constantTerm_mul
p2m_attr_erase "instance" "RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicBox NumberField.AdelicLevel AutomorphicForm
open scoped Pointwise

noncomputable section

namespace R4RSUnfold

section Bruhat

open scoped OnePoint

variable {F : Type} [Field F]

def rep : OnePoint F → GL (Fin 2) F
  | ∞ => 1
  | (ξ : F) => gl2Weyl * unipotentGL2 ξ

@[scoped simp] theorem rep_infty : rep (∞ : OnePoint F) = 1 := rfl
@[scoped simp] theorem rep_coe (ξ : F) : rep (ξ : OnePoint F) = gl2Weyl * unipotentGL2 ξ := rfl

def swapAdj (γ : GL (Fin 2) F) : GL (Fin 2) F :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![γ 1 1, γ 0 1; γ 1 0, γ 0 0] (by
    rw [Matrix.det_fin_two_of]
    intro h'
    apply γ.det_ne_zero
    rw [Matrix.det_fin_two]
    linear_combination h')

@[scoped simp] theorem swapAdj_apply_00 (γ : GL (Fin 2) F) : swapAdj γ 0 0 = γ 1 1 := rfl
@[scoped simp] theorem swapAdj_apply_01 (γ : GL (Fin 2) F) : swapAdj γ 0 1 = γ 0 1 := rfl
@[scoped simp] theorem swapAdj_apply_10 (γ : GL (Fin 2) F) : swapAdj γ 1 0 = γ 1 0 := rfl
@[scoped simp] theorem swapAdj_apply_11 (γ : GL (Fin 2) F) : swapAdj γ 1 1 = γ 0 0 := rfl

omit [Field F] in
theorem coe_unipotentGL2_inv {R : Type*} [CommRing R] (x : R) :
    (((unipotentGL2 x)⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) = !![1, -x; 0, 1] := rfl

theorem mul_unipotent_mul_weyl_apply_one_zero (A : Matrix (Fin 2) (Fin 2) F) (x : F) :
    (A * ((unipotentGL2 x : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
      * ((gl2Weyl : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) 1 0 = A 1 0 * x + A 1 1 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  simp [unipotentGL2_coe, gl2Weyl_val]

theorem weyl_mul_unipotent_mul_apply_one_zero (A : Matrix (Fin 2) (Fin 2) F) (ξ : F) :
    (((gl2Weyl : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
      * ((unipotentGL2 ξ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * A) 1 0 = A 0 0 + ξ * A 1 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  simp [unipotentGL2_coe, gl2Weyl_val]

theorem weyl_mul_unipotent_mul_apply_one (A : Matrix (Fin 2) (Fin 2) F) (ξ : F) (j : Fin 2) :
    (((gl2Weyl : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
      * ((unipotentGL2 ξ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * A) 1 j = A 0 j + ξ * A 1 j := by
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases j <;> simp [unipotentGL2_coe, gl2Weyl_val]

theorem rep_mem_borel_iff (Q : OnePoint F) : rep Q ∈ borelSubgroup F ↔ Q = ∞ := by
  induction Q using OnePoint.rec with
  | infty => simp only [rep_infty, Subgroup.one_mem]
  | coe ξ =>
    simp only [mem_borelSubgroup_iff, rep_coe, Units.val_mul]
    have h := weyl_mul_unipotent_mul_apply_one_zero (1 : Matrix (Fin 2) (Fin 2) F) ξ
    rw [mul_one] at h
    rw [h]
    simp

variable [DecidableEq F]

theorem rep_mul_mul_inv_mem_borel (γ : GL (Fin 2) F) (P : OnePoint F) :
    rep P * γ * (rep (swapAdj γ • P))⁻¹ ∈ borelSubgroup F := by
  show ((rep P * γ * (rep (swapAdj γ • P))⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 0 = 0
  induction P using OnePoint.rec with
  | infty =>
    rw [OnePoint.smul_infty_eq_ite]
    by_cases hc : swapAdj γ 1 0 = 0
    · rw [if_pos hc]
      simp only [rep_infty, one_mul, inv_one, mul_one]
      exact hc
    · rw [if_neg hc]
      have hc' : (γ : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0 := hc
      simp only [rep_infty, one_mul, rep_coe, mul_inv_rev, gl2Weyl_inv, swapAdj_apply_00, swapAdj_apply_10]
      rw [← mul_assoc, Units.val_mul, Units.val_mul, coe_unipotentGL2_inv,
        show (!![1, -(γ 1 1 / γ 1 0); 0, 1] : Matrix (Fin 2) (Fin 2) F)
          = ((unipotentGL2 (-(γ 1 1 / γ 1 0)) : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) from rfl,
        mul_unipotent_mul_weyl_apply_one_zero]
      change (γ : Matrix (Fin 2) (Fin 2) F) 1 0 * -((γ : Matrix (Fin 2) (Fin 2) F) 1 1
        / (γ : Matrix (Fin 2) (Fin 2) F) 1 0) + (γ : Matrix (Fin 2) (Fin 2) F) 1 1 = 0
      field_simp
      ring
  | coe ξ =>
    rw [OnePoint.smul_some_eq_ite]
    by_cases h0 : swapAdj γ 1 0 * ξ + swapAdj γ 1 1 = 0
    · rw [if_pos h0]
      have h0' : (γ : Matrix (Fin 2) (Fin 2) F) 1 0 * ξ + (γ : Matrix (Fin 2) (Fin 2) F) 0 0 = 0 := h0
      simp only [rep_infty, inv_one, mul_one, rep_coe]
      rw [Units.val_mul, Units.val_mul, weyl_mul_unipotent_mul_apply_one_zero]
      linear_combination h0'
    · rw [if_neg h0]
      have h0' : (γ : Matrix (Fin 2) (Fin 2) F) 1 0 * ξ + (γ : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0 := h0
      simp only [rep_coe, mul_inv_rev, gl2Weyl_inv, swapAdj_apply_00, swapAdj_apply_01, swapAdj_apply_10,
        swapAdj_apply_11]
      set t : F := (γ 1 1 * ξ + γ 0 1) / (γ 1 0 * ξ + γ 0 0) with ht
      rw [← mul_assoc, Units.val_mul, Units.val_mul, coe_unipotentGL2_inv,
        show (!![1, -t; 0, 1] : Matrix (Fin 2) (Fin 2) F)
          = (((unipotentGL2 (-t)) : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) from rfl,
        mul_unipotent_mul_weyl_apply_one_zero, Units.val_mul, Units.val_mul,
        weyl_mul_unipotent_mul_apply_one, weyl_mul_unipotent_mul_apply_one]
      rw [ht]
      change ((γ : Matrix (Fin 2) (Fin 2) F) 0 0 + ξ * (γ : Matrix (Fin 2) (Fin 2) F) 1 0)
          * -(((γ : Matrix (Fin 2) (Fin 2) F) 1 1 * ξ + (γ : Matrix (Fin 2) (Fin 2) F) 0 1)
            / ((γ : Matrix (Fin 2) (Fin 2) F) 1 0 * ξ + (γ : Matrix (Fin 2) (Fin 2) F) 0 0))
        + ((γ : Matrix (Fin 2) (Fin 2) F) 0 1 + ξ * (γ : Matrix (Fin 2) (Fin 2) F) 1 1) = 0
      have hX : (γ : Matrix (Fin 2) (Fin 2) F) 0 0 + ξ * (γ : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0 := by
        rw [add_comm, mul_comm]; exact h0'
      rw [show (γ : Matrix (Fin 2) (Fin 2) F) 1 0 * ξ + (γ : Matrix (Fin 2) (Fin 2) F) 0 0
          = (γ : Matrix (Fin 2) (Fin 2) F) 0 0 + ξ * (γ : Matrix (Fin 2) (Fin 2) F) 1 0 by ring,
        mul_neg, ← mul_div_assoc, mul_div_cancel_left₀ _ hX]
      ring

theorem existsUnique_rep_mul_mem_borel (γ : GL (Fin 2) F) : ∃! P : OnePoint F, rep P * γ ∈ borelSubgroup F := by
  refine ⟨(swapAdj γ)⁻¹ • ∞, ?_, ?_⟩
  · have h := rep_mul_mul_inv_mem_borel γ ((swapAdj γ)⁻¹ • ∞)
    rwa [smul_inv_smul, rep_infty, inv_one, mul_one] at h
  · intro P hP
    have h := rep_mul_mul_inv_mem_borel γ P
    have h' : (rep (swapAdj γ • P))⁻¹ ∈ borelSubgroup F := by
      have := (borelSubgroup F).mul_mem ((borelSubgroup F).inv_mem hP) h
      rwa [inv_mul_cancel_left] at this
    have h'' : swapAdj γ • P = ∞ := (rep_mem_borel_iff _).mp (by simpa using (borelSubgroup F).inv_mem h')
    rw [eq_inv_smul_iff, h'']

end Bruhat

section Sums

open scoped OnePoint

theorem tsum_onePoint {X : Type} {M : Type*} [AddCommMonoid M] [TopologicalSpace M] [ContinuousAdd M] [T2Space M]
    (h : OnePoint X → M) (hs : Summable fun ξ : X => h ξ) :
    ∑' P : OnePoint X, h P = h ∞ + ∑' ξ : X, h ξ := by
  let e : X ⊕ PUnit.{1} ≃ OnePoint X := (Equiv.optionEquivSumPUnit.{0, 0} X).symm
  have h1 : Summable ((h ∘ e) ∘ Sum.inl) := by
    have : (h ∘ e) ∘ Sum.inl = fun ξ : X => h ξ := by
      funext ξ; simp [e]; rfl
    rw [this]; exact hs
  have h2 : Summable ((h ∘ e) ∘ Sum.inr) := Summable.of_finite
  rw [← Equiv.tsum_eq e h]
  have hsplit : ∑' c : X ⊕ PUnit.{1}, (h ∘ e) c = (∑' a : X, (h ∘ e) (Sum.inl a))
      + ∑' b : PUnit.{1}, (h ∘ e) (Sum.inr b) := Summable.tsum_sum h1 h2
  simp only [Function.comp] at hsplit
  rw [hsplit, add_comm]
  congr 1
  rw [tsum_fintype]
  simp [e]
  rfl

theorem summable_onePoint {X : Type} {M : Type*} [AddCommMonoid M] [TopologicalSpace M] [ContinuousAdd M]
    (h : OnePoint X → M) (hs : Summable fun ξ : X => h ξ) : Summable h := by
  let e : X ⊕ PUnit.{1} ≃ OnePoint X := (Equiv.optionEquivSumPUnit.{0, 0} X).symm
  have h1 : Summable ((h ∘ e) ∘ Sum.inl) := by
    have : (h ∘ e) ∘ Sum.inl = fun ξ : X => h ξ := by
      funext ξ; simp [e]; rfl
    rw [this]; exact hs
  have h2 : Summable ((h ∘ e) ∘ Sum.inr) := Summable.of_finite
  exact (Equiv.summable_iff e).mp (h1.hasSum.sum h2.hasSum).summable

variable {F : Type} [Field F] [NumberField F]

def fam (ψ : AdelicGL2 (𝓞 F) F → ℂ) (x : AdelicGL2 (𝓞 F) F) : OnePoint F → ℂ :=
  fun P => ψ (globalPoints (𝓞 F) F (rep P) * x)

theorem globalPoints_unipotentGL2 (ξ : F) :
    globalPoints (𝓞 F) F (unipotentGL2 ξ) = unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) := by
  ext i j
  rw [globalPoints_apply]
  fin_cases i <;> fin_cases j <;> simp

theorem fam_infty (ψ : AdelicGL2 (𝓞 F) F → ℂ) (x : AdelicGL2 (𝓞 F) F) : fam ψ x ∞ = ψ x := by
  simp [fam]

theorem fam_coe (ψ : AdelicGL2 (𝓞 F) F → ℂ) (x : AdelicGL2 (𝓞 F) F) (ξ : F) :
    fam ψ x ξ = ψ (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * x) := by
  simp only [fam, rep_coe, map_mul, globalPoints_unipotentGL2]
  rfl

theorem pseudoEisenstein_eq_tsum_fam (ψ : AdelicGL2 (𝓞 F) F → ℂ) (x : AdelicGL2 (𝓞 F) F)
    (hs : Summable fun ξ : F => fam ψ x ξ) :
    pseudoEisenstein F ψ x = ∑' P : OnePoint F, fam ψ x P := by
  rw [tsum_onePoint _ hs, fam_infty, pseudoEisenstein_apply]
  simp only [fam_coe]

end Sums

section Main

open scoped ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

variable (F : Type) [Field F] [NumberField F]

theorem continuous_unipotentGL2_adele :
    Continuous fun u : AdeleRing (𝓞 F) F => (unipotentGL2 u : AdelicGL2 (𝓞 F) F) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [unipotentGL2] <;> first | exact continuous_const | exact continuous_id
  · have h : ∀ u : AdeleRing (𝓞 F) F,
        (((unipotentGL2 u)⁻¹ : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) = !![1, -u; 0, 1] :=
      fun u => rfl
    simp_rw [h]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp <;> first | exact continuous_const | exact continuous_id | exact continuous_neg

def sheet (u : AdeleRing (𝓞 F) F) : rationalTorusUnipotent F :=
  Subgroup.inclusion le_sup_right (toAdelicUnipotent F u)

theorem sheet_coe (u : AdeleRing (𝓞 F) F) :
    ((sheet F u : rationalTorusUnipotent F) : AdelicGL2 (𝓞 F) F) = unipotentGL2 u := rfl

theorem measurable_sheet : Measurable (sheet F) := by
  have h : Measurable fun u : AdeleRing (𝓞 F) F => (unipotentGL2 u : AdelicGL2 (𝓞 F) F) :=
    (continuous_unipotentGL2_adele F).measurable
  exact h.subtype_mk

omit [NumberField F] in

theorem scalar_mem_borelSubgroup (z : Fˣ) :
    Units.map (Matrix.scalar (Fin 2) : F →+* Matrix (Fin 2) (Fin 2) F).toMonoidHom z ∈ borelSubgroup F := by
  rw [mem_borelSubgroup_iff]
  show (Matrix.scalar (Fin 2) (z : F)) 1 0 = 0
  simp

omit [NumberField F] in

theorem diagOne_mem_borelSubgroup (a : Fˣ) : diagOne a ∈ borelSubgroup F := by
  rw [mem_borelSubgroup_iff, diagOne_coe_apply]
  simp

theorem indicator_constantTerm_mul_left_invariant
    (S : Set (AdelicGL2 (𝓞 F) F))
    (hS : ∀ (γ : GL (Fin 2) F) (x : AdelicGL2 (𝓞 F) F), globalPoints (𝓞 F) F γ * x ∈ S ↔ x ∈ S)
    (hSN : ∀ (u : AdeleRing (𝓞 F) F) (x : AdelicGL2 (𝓞 F) F), unipotentGL2 u * x ∈ S ↔ x ∈ S)
    (f ψ : AdelicGL2 (𝓞 F) F → ℂ)
    (hfG : ∀ (γ : GL (Fin 2) F) (x : AdelicGL2 (𝓞 F) F), f (globalPoints (𝓞 F) F γ * x) = f x)
    (hψB : ∀ γ ∈ borelSubgroup F, ∀ x : AdelicGL2 (𝓞 F) F, ψ (globalPoints (𝓞 F) F γ * x) = ψ x)
    (hψN : ∀ (u : AdeleRing (𝓞 F) F) (x : AdelicGL2 (𝓞 F) F), ψ (unipotentGL2 u * x) = ψ x) :
    ∀ h ∈ rationalTorusUnipotent F, ∀ y : AdelicGL2 (𝓞 F) F,
      S.indicator (fun y => constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F))
          (fun t => unipotentGL2 t) f y * ψ y) (h * y) =
        S.indicator (fun y => constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F))
          (fun t => unipotentGL2 t) f y * ψ y) y := by
  set Rfun : AdelicGL2 (𝓞 F) F → ℂ := S.indicator (fun y =>
      constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F))
        (fun t => unipotentGL2 t) f y * ψ y) with hRfun

  let Stab : Subgroup (AdelicGL2 (𝓞 F) F) :=
    { carrier := {h | ∀ y, Rfun (h * y) = Rfun y}
      mul_mem' := fun {a b} ha hb y => by rw [mul_assoc, ha, hb]
      one_mem' := fun y => by rw [one_mul]
      inv_mem' := fun {a} ha y => by rw [← ha (a⁻¹ * y), mul_inv_cancel_left] }
  suffices hle : rationalTorusUnipotent F ≤ Stab from fun h hh y => hle hh y

  have hB : ∀ γ ∈ borelSubgroup F, globalPoints (𝓞 F) F γ ∈ Stab := by
    intro γ hγ y
    show Rfun _ = Rfun _
    by_cases hy : y ∈ S
    · rw [hRfun, Set.indicator_of_mem ((hS γ y).mpr hy), Set.indicator_of_mem hy, hψB γ hγ y,
        AutomorphicForm.constantTerm_adelicBox_globalPoints_mul_of_mem_borelSubgroup F (fun γ' _ h => hfG γ' h) hγ y]
    · rw [hRfun, Set.indicator_of_notMem (fun h => hy ((hS γ y).mp h)), Set.indicator_of_notMem hy]

  have hN : ∀ u : AdeleRing (𝓞 F) F, unipotentGL2 u ∈ Stab := by
    intro u y
    show Rfun _ = Rfun _
    by_cases hy : y ∈ S
    · rw [hRfun, Set.indicator_of_mem ((hSN u y).mpr hy), Set.indicator_of_mem hy, hψN u y,
        AutomorphicForm.constantTerm_adelicBox_unipotentGL2_mul F (φ := f) (fun k h => hfG _ h) u y]
    · rw [hRfun, Set.indicator_of_notMem (fun h => hy ((hSN u y).mp h)), Set.indicator_of_notMem hy]
  refine sup_le (sup_le ?_ ?_) ?_
  · rintro _ ⟨z, rfl⟩
    exact hB _ (scalar_mem_borelSubgroup F z)
  · rintro _ ⟨a, rfl⟩
    exact hB _ (diagOne_mem_borelSubgroup F a)
  · rintro _ ⟨t, rfl⟩
    exact hN t.toAdd

theorem main
    (S : Set (AdelicGL2 (𝓞 F) F)) (hSm : MeasurableSet S)
    (hS : ∀ (γ : GL (Fin 2) F) (x : AdelicGL2 (𝓞 F) F), globalPoints (𝓞 F) F γ * x ∈ S ↔ x ∈ S)
    (hSN : ∀ (u : AdeleRing (𝓞 F) F) (x : AdelicGL2 (𝓞 F) F), unipotentGL2 u * x ∈ S ↔ x ∈ S)
    (Φ₀ : Set (AdelicGL2 (𝓞 F) F)) (hΦ₀S : Φ₀ ⊆ S)
    (hΦ₀ : IsFundamentalDomain (globalPoints (𝓞 F) F).range Φ₀ ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict S))
    (f ψ : AdelicGL2 (𝓞 F) F → ℂ) (hf : Measurable f) (hψ : Measurable ψ)
    (hfG : ∀ (γ : GL (Fin 2) F) (x : AdelicGL2 (𝓞 F) F), f (globalPoints (𝓞 F) F γ * x) = f x)
    (hψB : ∀ γ ∈ borelSubgroup F, ∀ x : AdelicGL2 (𝓞 F) F, ψ (globalPoints (𝓞 F) F γ * x) = ψ x)
    (hψN : ∀ (u : AdeleRing (𝓞 F) F) (x : AdelicGL2 (𝓞 F) F), ψ (unipotentGL2 u * x) = ψ x)
    (hfin : ∫⁻ x in Φ₀, ‖f x‖ₑ * (‖ψ x‖ₑ + ∑' ξ : F,
        ‖ψ (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * x)‖ₑ)
      ∂(adelicGLHaar (Fin 2) (𝓞 F) F) < ∞) :
    IntegrableOn (fun x => f x * pseudoEisenstein F ψ x) Φ₀ (adelicGLHaar (Fin 2) (𝓞 F) F) ∧
    (∀ h ∈ rationalTorusUnipotent F, ∀ y : AdelicGL2 (𝓞 F) F,
      S.indicator (fun y => constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F))
          (fun t => unipotentGL2 t) f y * ψ y) (h * y) =
        S.indicator (fun y => constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F))
          (fun t => unipotentGL2 t) f y * ψ y) y) ∧
    Integrable (fun q : RationalTorusUnipotentQuotient F =>
        S.indicator (fun y => constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F))
          (fun t => unipotentGL2 t) f y * ψ y) q.out)
      (rationalTorusUnipotentQuotientMeasure F) ∧
    ∫ x in Φ₀, f x * pseudoEisenstein F ψ x ∂(adelicGLHaar (Fin 2) (𝓞 F) F) =
      ∫ q, S.indicator (fun y => constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F))
          (fun t => unipotentGL2 t) f y * ψ y) q.out ∂(rationalTorusUnipotentQuotientMeasure F) := by
  classical

  haveI : Countable (OnePoint F) := inferInstanceAs (Countable (Option F))
  set μ := adelicGLHaar (Fin 2) (𝓞 F) F with hμ
  set G' : AdelicGL2 (𝓞 F) F → ℂ := fun y => f y * ψ y with hG'
  set Rfun : AdelicGL2 (𝓞 F) F → ℂ := S.indicator (fun y =>
      constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F))
        (fun t => unipotentGL2 t) f y * ψ y) with hRfun
  haveI := (isHaarMeasure_rationalTorusUnipotentHaar_and_isMulRightInvariant F).1
  haveI := (isHaarMeasure_rationalTorusUnipotentHaar_and_isMulRightInvariant F).2
  obtain ⟨hBle, -, -, hΩfd, hΩint⟩ := isFundamentalDomain_boxSheet_rationalTorusUnipotent F

  set r : OnePoint F → GL (Fin 2) F := fun P => (rep P)⁻¹ with hr_def
  have hr : ∀ γ : GL (Fin 2) F, ∃! P : OnePoint F, (r P)⁻¹ * γ ∈ borelSubgroup F := by
    intro γ; simpa only [hr_def, inv_inv] using existsUnique_rep_mul_mem_borel γ
  have hrP : ∀ (P : OnePoint F) (x : AdelicGL2 (𝓞 F) F),
      (globalPoints (𝓞 F) F (r P))⁻¹ * x = globalPoints (𝓞 F) F (rep P) * x := by
    intro P x; simp [hr_def, map_inv]

  have hG'm : Measurable G' := hf.mul hψ
  have hG'B : ∀ γ ∈ borelSubgroup F, ∀ x, G' (globalPoints (𝓞 F) F γ * x) = G' x := by
    intro γ hγ x; simp only [hG', hfG, hψB γ hγ]
  have hgP : ∀ (P : OnePoint F) (x : AdelicGL2 (𝓞 F) F),
      G' ((globalPoints (𝓞 F) F (r P))⁻¹ * x) = f x * fam ψ x P := by
    intro P x; rw [hrP]; simp only [hG', hfG, fam]

  have hfin' : ∫⁻ x in Φ₀, ∑' P : OnePoint F, ‖G' ((globalPoints (𝓞 F) F (r P))⁻¹ * x)‖ₑ ∂μ < ∞ := by
    have hkey : ∀ x, (∑' P : OnePoint F, ‖G' ((globalPoints (𝓞 F) F (r P))⁻¹ * x)‖ₑ) =
        ‖f x‖ₑ * (‖ψ x‖ₑ + ∑' ξ : F,
          ‖ψ (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * x)‖ₑ) := by
      intro x
      simp_rw [hgP, enorm_mul]
      rw [ENNReal.tsum_mul_left, tsum_onePoint (fun P => ‖fam ψ x P‖ₑ) ENNReal.summable, fam_infty]
      simp only [fam_coe]
    simp_rw [hkey]
    exact hfin

  obtain ⟨h1, h2, -, h4, h5⟩ :=
    AutomorphicForm.integrableOn_tsum_and_setIntegral_tsum_comp_globalPoints_inv_mul_eq_integral_haarQuotient_setIntegral
      F S hSm hS Φ₀ hΦ₀S hΦ₀ (borelSubgroup F) r hr (rationalTorusUnipotent F) (isClosed_rationalTorusUnipotent F)
      hBle (rationalTorusUnipotentHaar F) _ hΩfd G' hG'm hG'B hfin'

  have hpt : ∀ x, (Summable fun P : OnePoint F => ‖G' ((globalPoints (𝓞 F) F (r P))⁻¹ * x)‖) →
      (∑' P : OnePoint F, G' ((globalPoints (𝓞 F) F (r P))⁻¹ * x)) = f x * pseudoEisenstein F ψ x := by
    intro x hsum
    simp_rw [hgP] at hsum ⊢
    rw [tsum_mul_left]
    by_cases hfx : f x = 0
    · simp [hfx]
    · congr 1
      simp_rw [norm_mul] at hsum
      have hs : Summable (fam ψ x) := ((summable_mul_left_iff (norm_ne_zero_iff.mpr hfx)).mp hsum).of_norm
      have hs' : Summable fun ξ : F => fam ψ x ξ := hs.comp_injective OnePoint.coe_injective
      exact (pseudoEisenstein_eq_tsum_fam ψ x hs').symm
  have hae : (fun x => ∑' P : OnePoint F, G' ((globalPoints (𝓞 F) F (r P))⁻¹ * x)) =ᵐ[μ.restrict Φ₀]
      fun x => f x * pseudoEisenstein F ψ x := h2.mono fun x hx => hpt x hx

  set ν' : Measure (AdeleRing (𝓞 F) F) := ((adelicAddHaar (𝓞 F) F) (adelicBox F))⁻¹ • adelicAddHaar (𝓞 F) F
    with hν'
  set Ω : Set (rationalTorusUnipotent F) := (fun u : AdeleRing (𝓞 F) F =>
      Subgroup.inclusion le_sup_right (toAdelicUnipotent F u)) '' adelicBox F with hΩ_def
  have hΩmap : (rationalTorusUnipotentHaar F).restrict Ω = Measure.map (sheet F) (ν'.restrict (adelicBox F)) := by
    refine (Measure.ext_iff_lintegral _).mpr fun Fn hFn => ?_
    rw [lintegral_map hFn (measurable_sheet F)]
    exact hΩint Fn hFn
  have hfibre : ∀ y : AdelicGL2 (𝓞 F) F,
      (∫ h in Ω, S.indicator G' ((h : AdelicGL2 (𝓞 F) F) * y) ∂(rationalTorusUnipotentHaar F)) = Rfun y := by
    intro y
    have hmeasG : Measurable fun h : rationalTorusUnipotent F => S.indicator G' ((h : AdelicGL2 (𝓞 F) F) * y) :=
      (hG'm.indicator hSm).comp (measurable_subtype_coe.mul_const y)
    have step1 : (∫ h in Ω, S.indicator G' ((h : AdelicGL2 (𝓞 F) F) * y) ∂(rationalTorusUnipotentHaar F)) =
        ∫ u in adelicBox F, S.indicator G' (unipotentGL2 u * y) ∂ν' := by
      show (∫ h, S.indicator G' ((h : AdelicGL2 (𝓞 F) F) * y) ∂((rationalTorusUnipotentHaar F).restrict Ω)) = _
      rw [hΩmap, integral_map (measurable_sheet F).aemeasurable hmeasG.aestronglyMeasurable]
      rfl
    rw [step1]
    by_cases hy : y ∈ S
    · have hpt' : ∀ u, S.indicator G' (unipotentGL2 u * y) = f (unipotentGL2 u * y) * ψ y := by
        intro u
        rw [Set.indicator_of_mem ((hSN u y).mpr hy)]
        show f _ * ψ _ = _
        rw [hψN]
      simp_rw [hpt']
      rw [integral_mul_const, hRfun, Set.indicator_of_mem hy]
      congr 1
      show _ = ∫ q, f (unipotentGL2 q * y) ∂(ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F))
      rw [ProbabilityTheory.cond, hν', Measure.restrict_smul]
    · have hpt' : ∀ u, S.indicator G' (unipotentGL2 u * y) = 0 := by
        intro u
        exact Set.indicator_of_notMem (fun h => hy ((hSN u y).mp h)) _
      simp_rw [hpt']
      rw [integral_zero, hRfun, Set.indicator_of_notMem hy]
  have hfibre_fun : (fun q : RationalTorusUnipotentQuotient F =>
      ∫ h in Ω, S.indicator G' ((h : AdelicGL2 (𝓞 F) F) * q.out) ∂(rationalTorusUnipotentHaar F)) =
      fun q => Rfun q.out := funext fun q => hfibre q.out

  refine ⟨h1.congr hae, indicator_constantTerm_mul_left_invariant F S hS hSN f ψ hfG hψB hψN, ?_, ?_⟩
  · have h4' := h4
    rw [hfibre_fun] at h4'
    exact h4'
  · calc ∫ x in Φ₀, f x * pseudoEisenstein F ψ x ∂μ
        = ∫ x in Φ₀, ∑' P : OnePoint F, G' ((globalPoints (𝓞 F) F (r P))⁻¹ * x) ∂μ :=
          (integral_congr_ae hae).symm
      _ = ∫ q, (∫ h in Ω, S.indicator G' ((h : AdelicGL2 (𝓞 F) F) * q.out) ∂(rationalTorusUnipotentHaar F))
            ∂(HaarQuotient.measure μ (rationalTorusUnipotent F) (rationalTorusUnipotentHaar F)) := h5
      _ = ∫ q, Rfun q.out ∂(rationalTorusUnipotentQuotientMeasure F) := by
          rw [hfibre_fun]; rfl

end Main

end R4RSUnfold
p2m_reactivate "P2MW.S_AutomorphicForm_setIntegral_mul_pseudoEisenstein_eq_integral_rationalTorusUnipotentQuotient_constantTerm_mul.R4RSUnfold"

end
p2m_reactivate "P2MW.S_AutomorphicForm_setIntegral_mul_pseudoEisenstein_eq_integral_rationalTorusUnipotentQuotient_constantTerm_mul.R4RSUnfold"

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

open scoped ENNReal in
theorem solution
    (F : Type) [Field F] [NumberField F]
    (S : Set (AdelicGL2 (𝓞 F) F)) (hSm : MeasurableSet S)
    (hS : ∀ (γ : GL (Fin 2) F) (x : AdelicGL2 (𝓞 F) F), globalPoints (𝓞 F) F γ * x ∈ S ↔ x ∈ S)
    (hSN : ∀ (u : AdeleRing (𝓞 F) F) (x : AdelicGL2 (𝓞 F) F), unipotentGL2 u * x ∈ S ↔ x ∈ S)
    (Φ₀ : Set (AdelicGL2 (𝓞 F) F)) (hΦ₀S : Φ₀ ⊆ S)
    (hΦ₀ : IsFundamentalDomain (globalPoints (𝓞 F) F).range Φ₀ ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict S))
    (f ψ : AdelicGL2 (𝓞 F) F → ℂ) (hf : Measurable f) (hψ : Measurable ψ)
    (hfG : ∀ (γ : GL (Fin 2) F) (x : AdelicGL2 (𝓞 F) F), f (globalPoints (𝓞 F) F γ * x) = f x)
    (hψB : ∀ γ ∈ borelSubgroup F, ∀ x : AdelicGL2 (𝓞 F) F, ψ (globalPoints (𝓞 F) F γ * x) = ψ x)
    (hψN : ∀ (u : AdeleRing (𝓞 F) F) (x : AdelicGL2 (𝓞 F) F), ψ (unipotentGL2 u * x) = ψ x)
    (hfin : ∫⁻ x in Φ₀, ‖f x‖ₑ * (‖ψ x‖ₑ + ∑' ξ : F,
        ‖ψ (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * x)‖ₑ)
      ∂(adelicGLHaar (Fin 2) (𝓞 F) F) < ∞) :
    IntegrableOn (fun x => f x * pseudoEisenstein F ψ x) Φ₀ (adelicGLHaar (Fin 2) (𝓞 F) F) ∧
    (∀ h ∈ rationalTorusUnipotent F, ∀ y : AdelicGL2 (𝓞 F) F,
      S.indicator (fun y => constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F))
          (fun t => unipotentGL2 t) f y * ψ y) (h * y) =
        S.indicator (fun y => constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F))
          (fun t => unipotentGL2 t) f y * ψ y) y) ∧
    Integrable (fun q : RationalTorusUnipotentQuotient F =>
        S.indicator (fun y => constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F))
          (fun t => unipotentGL2 t) f y * ψ y) q.out)
      (rationalTorusUnipotentQuotientMeasure F) ∧
    ∫ x in Φ₀, f x * pseudoEisenstein F ψ x ∂(adelicGLHaar (Fin 2) (𝓞 F) F) =
      ∫ q, S.indicator (fun y => constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F))
          (fun t => unipotentGL2 t) f y * ψ y) q.out ∂(rationalTorusUnipotentQuotientMeasure F) :=
  R4RSUnfold.main F S hSm hS hSN Φ₀ hΦ₀S hΦ₀ f ψ hf hψ hfG hψB hψN hfin

end S_AutomorphicForm_setIntegral_mul_pseudoEisenstein_eq_integral_rationalTorusUnipotentQuotient_constantTerm_mul
end P2MW
export P2MW.S_AutomorphicForm_setIntegral_mul_pseudoEisenstein_eq_integral_rationalTorusUnipotentQuotient_constantTerm_mul (solution)
