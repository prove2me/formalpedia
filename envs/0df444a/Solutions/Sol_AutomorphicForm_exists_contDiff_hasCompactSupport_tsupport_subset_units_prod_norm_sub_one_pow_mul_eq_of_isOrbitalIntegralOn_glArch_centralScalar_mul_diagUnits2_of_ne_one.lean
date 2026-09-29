-- Prove2me | solution 1 for AutomorphicForm.exists_contDiff_hasCompactSupport_tsupport_subset_units_prod_norm_sub_one_pow_mul_eq_of_isOrbitalIntegralOn_glArch_centralScalar_mul_diagUnits2_of_ne_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/6537af47-485e-5b62-b6e2-fc7b5b5756a6

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Theorems.Thm_AutomorphicForm_exists_contDiff_hasCompactSupport_tsupport_subset_units_prod_norm_sub_one_pow_mul_eq_of_isOrbitalIntegralOn_scalar_mul_diagUnits2
import Theorems.Thm_AutomorphicForm_centralizer_secondCountableTopology_locallyCompactSpace_and_exists_glArch_finComponent_localIntegralSet_isOpen_surjective_isCompact_restrictedProduct
import Theorems.Thm_AutomorphicForm_glArch_centralScalar_mul_diagUnits2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_contDiff_hasCompactSupport_tsupport_subset_units_prod_norm_sub_one_pow_mul_eq_of_isOrbitalIntegralOn_glArch_centralScalar_mul_diagUnits2_of_ne_one
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply"
p2m_attr_erase "simp" "Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicHaar IsDedekindDomain
open scoped NNReal ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel

open LanglandsTunnell.CubicInduction (diagUnits2)

namespace PccTorus

open LanglandsTunnell.CubicInduction (diagUnits2)

variable {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

theorem diagUnits2_mul (a b c d : Aˣ) : diagUnits2 (a * c) (b * d) = diagUnits2 a b * diagUnits2 c d := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem offdiag_eq_zero (γ t : GL (Fin 2) A)
    (h10 : (γ : Matrix (Fin 2) (Fin 2) A) 1 0 = 0) (h01 : (γ : Matrix (Fin 2) (Fin 2) A) 0 1 = 0)
    (hreg : IsUnit ((γ : Matrix (Fin 2) (Fin 2) A) 0 0 - (γ : Matrix (Fin 2) (Fin 2) A) 1 1))
    (ht : t ∈ Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) :
    (t : Matrix (Fin 2) (Fin 2) A) 0 1 = 0 ∧ (t : Matrix (Fin 2) (Fin 2) A) 1 0 = 0 := by
  have hc : γ * t = t * γ := (Subgroup.mem_centralizer_iff.mp ht) γ (Set.mem_singleton γ)
  have hv : (γ : Matrix (Fin 2) (Fin 2) A) * (t : Matrix (Fin 2) (Fin 2) A) =
      (t : Matrix (Fin 2) (Fin 2) A) * (γ : Matrix (Fin 2) (Fin 2) A) := by
    rw [← Units.val_mul, hc, Units.val_mul]
  have e01 := congrFun (congrFun hv 0) 1
  have e10 := congrFun (congrFun hv 1) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_two, h10, h01, zero_mul, mul_zero, add_zero, zero_add] at e01 e10
  obtain ⟨d, hd⟩ := hreg
  constructor
  · have : (d : A) * (t : Matrix (Fin 2) (Fin 2) A) 0 1 = 0 := by
      rw [hd, sub_mul, e01, mul_comm, sub_self]
    simpa using congrArg (fun x => ((d⁻¹ : Aˣ) : A) * x) this
  · have : (d : A) * (t : Matrix (Fin 2) (Fin 2) A) 1 0 = 0 := by
      rw [hd, sub_mul, mul_comm ((γ : Matrix (Fin 2) (Fin 2) A) 0 0), ← e10, mul_comm, sub_self]
    simpa using congrArg (fun x => ((d⁻¹ : Aˣ) : A) * x) this

def unit00 (t : GL (Fin 2) A) (h01 : (t : Matrix (Fin 2) (Fin 2) A) 0 1 = 0)
    (h10 : (t : Matrix (Fin 2) (Fin 2) A) 1 0 = 0) : Aˣ where
  val := (t : Matrix (Fin 2) (Fin 2) A) 0 0
  inv := ((t⁻¹ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 0 0
  val_inv := by
    have h := congrFun (congrFun (Units.mul_inv t) 0) 0
    rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_eq, h01, zero_mul, add_zero] at h
    exact h
  inv_val := by
    have h := congrFun (congrFun (Units.inv_mul t) 0) 0
    rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_eq, h10, mul_zero, add_zero] at h
    exact h

def unit11 (t : GL (Fin 2) A) (h01 : (t : Matrix (Fin 2) (Fin 2) A) 0 1 = 0)
    (h10 : (t : Matrix (Fin 2) (Fin 2) A) 1 0 = 0) : Aˣ where
  val := (t : Matrix (Fin 2) (Fin 2) A) 1 1
  inv := ((t⁻¹ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 1 1
  val_inv := by
    have h := congrFun (congrFun (Units.mul_inv t) 1) 1
    rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_eq, h10, zero_mul, zero_add] at h
    exact h
  inv_val := by
    have h := congrFun (congrFun (Units.inv_mul t) 1) 1
    rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_eq, h01, mul_zero, zero_add] at h
    exact h

theorem diagUnits2_unit00_unit11 (t : GL (Fin 2) A) (h01 : (t : Matrix (Fin 2) (Fin 2) A) 0 1 = 0)
    (h10 : (t : Matrix (Fin 2) (Fin 2) A) 1 0 = 0) : diagUnits2 (unit00 t h01 h10) (unit11 t h01 h10) = t := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [unit00, unit11, h01, h10]

theorem diagUnits2_mem_centralizer (γ : GL (Fin 2) A)
    (h10 : (γ : Matrix (Fin 2) (Fin 2) A) 1 0 = 0) (h01 : (γ : Matrix (Fin 2) (Fin 2) A) 0 1 = 0) (a b : Aˣ) :
    diagUnits2 a b ∈ Subgroup.centralizer ({γ} : Set (GL (Fin 2) A)) := by
  rw [Subgroup.mem_centralizer_iff]
  intro g hg
  rw [Set.mem_singleton_iff] at hg
  rw [hg]
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, h10, h01, mul_comm]

theorem continuous_diagUnits2 : Continuous fun p : Aˣ × Aˣ => diagUnits2 p.1 p.2 := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j
    · first
        | simpa using Units.continuous_val.comp continuous_fst
        | (have h' := Units.continuous_val.comp continuous_fst; simp at h' ⊢; exact h')
        | (have h' := Units.continuous_val.comp continuous_fst; simp at h'; exact h')
        | exact Units.continuous_val.comp continuous_fst
        | (simpa [Function.comp_def] using Units.continuous_val.comp continuous_fst)
    · simpa using continuous_const
    · simpa using continuous_const
    · first
        | simpa using Units.continuous_val.comp continuous_snd
        | (have h' := Units.continuous_val.comp continuous_snd; simp at h' ⊢; exact h')
        | (have h' := Units.continuous_val.comp continuous_snd; simp at h'; exact h')
        | exact Units.continuous_val.comp continuous_snd
        | (simpa [Function.comp_def] using Units.continuous_val.comp continuous_snd)
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j
    · first
        | simpa [diagUnits2] using Units.continuous_coe_inv.comp continuous_fst
        | (have h' := Units.continuous_coe_inv.comp continuous_fst; simp [diagUnits2] at h' ⊢; exact h')
        | (have h' := Units.continuous_coe_inv.comp continuous_fst; simp [diagUnits2] at h'; exact h')
        | exact Units.continuous_coe_inv.comp continuous_fst
        | (simpa [diagUnits2, Function.comp_def] using Units.continuous_coe_inv.comp continuous_fst)
    · simpa [diagUnits2] using continuous_const
    · simpa [diagUnits2] using continuous_const
    · first
        | simpa [diagUnits2] using Units.continuous_coe_inv.comp continuous_snd
        | (have h' := Units.continuous_coe_inv.comp continuous_snd; simp [diagUnits2] at h' ⊢; exact h')
        | (have h' := Units.continuous_coe_inv.comp continuous_snd; simp [diagUnits2] at h'; exact h')
        | exact Units.continuous_coe_inv.comp continuous_snd
        | (simpa [diagUnits2, Function.comp_def] using Units.continuous_coe_inv.comp continuous_snd)

noncomputable def torusEquiv (γ : GL (Fin 2) A)
    (h10 : (γ : Matrix (Fin 2) (Fin 2) A) 1 0 = 0) (h01 : (γ : Matrix (Fin 2) (Fin 2) A) 0 1 = 0)
    (hreg : IsUnit ((γ : Matrix (Fin 2) (Fin 2) A) 0 0 - (γ : Matrix (Fin 2) (Fin 2) A) 1 1)) :
    (Aˣ × Aˣ) ≃ₜ* Subgroup.centralizer ({γ} : Set (GL (Fin 2) A)) where
  toFun p := ⟨diagUnits2 p.1 p.2, diagUnits2_mem_centralizer γ h10 h01 p.1 p.2⟩
  invFun t := (unit00 (t : GL (Fin 2) A) (offdiag_eq_zero γ t h10 h01 hreg t.2).1 (offdiag_eq_zero γ t h10 h01 hreg t.2).2,
    unit11 (t : GL (Fin 2) A) (offdiag_eq_zero γ t h10 h01 hreg t.2).1 (offdiag_eq_zero γ t h10 h01 hreg t.2).2)
  left_inv p := by
    ext <;> simp [unit00, unit11]
  right_inv t := Subtype.ext (diagUnits2_unit00_unit11 (t : GL (Fin 2) A)
    (offdiag_eq_zero γ _ h10 h01 hreg t.2).1 (offdiag_eq_zero γ _ h10 h01 hreg t.2).2)
  map_mul' p q := Subtype.ext (by simpa using diagUnits2_mul p.1 p.2 q.1 q.2)
  continuous_toFun := (continuous_diagUnits2.subtype_mk _)
  continuous_invFun := by
    have hc : Continuous fun t : Subgroup.centralizer ({γ} : Set (GL (Fin 2) A)) => ((t : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) :=
      Units.continuous_val.comp continuous_subtype_val
    have hci : Continuous fun t : Subgroup.centralizer ({γ} : Set (GL (Fin 2) A)) =>
        (((t : GL (Fin 2) A)⁻¹ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) :=
      Units.continuous_val.comp (continuous_inv.comp continuous_subtype_val)
    refine Continuous.prodMk ?_ ?_
    · exact Units.continuous_iff.mpr ⟨hc.matrix_elem 0 0, hci.matrix_elem 0 0⟩
    · exact Units.continuous_iff.mpr ⟨hc.matrix_elem 1 1, hci.matrix_elem 1 1⟩

theorem torusEquiv_apply (γ : GL (Fin 2) A)
    (h10 : (γ : Matrix (Fin 2) (Fin 2) A) 1 0 = 0) (h01 : (γ : Matrix (Fin 2) (Fin 2) A) 0 1 = 0)
    (hreg : IsUnit ((γ : Matrix (Fin 2) (Fin 2) A) 0 0 - (γ : Matrix (Fin 2) (Fin 2) A) 1 1)) (p : Aˣ × Aˣ) :
    ((torusEquiv γ h10 h01 hreg p : Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) : GL (Fin 2) A) =
      diagUnits2 p.1 p.2 := by
  simp [torusEquiv]

end PccTorus

namespace PccArch

open LanglandsTunnell.CubicInduction (diagUnits2)

variable (K : Type) [Field K] [NumberField K]

theorem glArch_apply (g : GL (Fin 2) (AdeleRing (𝓞 K) K)) (i j : Fin 2) :
    ((AdelicLevel.glArch (𝓞 K) K g : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) i j =
      AdelicLevel.adeleArch (𝓞 K) K (((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))) i j) := rfl

theorem val_centralScalar_mul_diagUnits2 (z a b : (AdeleRing (𝓞 K) K)ˣ) :
    ((AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 a b : GL (Fin 2) (AdeleRing (𝓞 K) K)) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) =
      !![(z : AdeleRing (𝓞 K) K) * a, 0; 0, (z : AdeleRing (𝓞 K) K) * b] := by
  rw [Units.val_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [AutomorphicForm.centralScalar, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply]

theorem gamma_entries (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ) :
    ((AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1) : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 1 0 = 0 ∧
    ((AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1) : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 0 1 = 0 ∧
    ((AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1) : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 0 0 -
      ((AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1) : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 1 1 =
      AdelicLevel.adeleArch (𝓞 K) K (z : AdeleRing (𝓞 K) K) *
        AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) (u : K) - 1) := by
  refine ⟨?_, ?_, ?_⟩ <;> simp only [glArch_apply, val_centralScalar_mul_diagUnits2, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, map_zero]
  rw [← map_mul, ← map_sub, mul_sub, mul_one, Units.val_one, mul_one, Units.coe_map, MonoidHom.coe_coe]

theorem isUnit_gamma_sub (u : Kˣ) (hu1 : (u : K) ≠ 1) (z : (AdeleRing (𝓞 K) K)ˣ) :
    IsUnit (((AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1) : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 0 0 -
      ((AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1) : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 1 1) := by
  rw [(gamma_entries K u z).2.2]
  refine (z.isUnit.map _).mul ?_
  rw [← map_one (algebraMap K (AdeleRing (𝓞 K) K)), ← map_sub]
  exact ((isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr hu1)).map _).map _

end PccArch

namespace AWin

open LanglandsTunnell.CubicInduction (diagUnits2)

section Generic

variable {A : Type} [CommRing A] [TopologicalSpace A]

theorem isOrbitalIntegralOn_of_eq_smul
    (μ : @Measure (GL (Fin 2) A) (AutomorphicForm.glBorelOf A)) (γ : GL (Fin 2) A)
    (τ τ' : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) (AutomorphicForm.centralizerBorel A γ))
    (c : ℝ≥0) (h : τ = c • τ') (f : GL (Fin 2) A → ℂ) (I : ℂ)
    (hI : AutomorphicForm.IsOrbitalIntegralOn A μ γ τ f I) :
    AutomorphicForm.IsOrbitalIntegralOn A μ γ τ' f (((c : ℝ) : ℂ) * I) := by
  letI := AutomorphicForm.glBorelOf A
  obtain ⟨w, ⟨hw0, hwm, hwc, hws⟩, hIw⟩ := hI
  refine ⟨fun x => (c : ℝ) * w x, ⟨fun x => mul_nonneg c.coe_nonneg (hw0 x), hwm.const_mul _, hwc.mul_left,
    fun x hx => ?_⟩, ?_⟩
  · have h1 := hws x hx
    rw [h, integral_smul_nnreal_measure] at h1
    rw [integral_const_mul]
    simpa [NNReal.smul_def, smul_eq_mul] using h1
  · rw [hIw, ← integral_const_mul]
    congr 1
    funext x
    push_cast
    ring

theorem transport
    (μ : @Measure (GL (Fin 2) A) (AutomorphicForm.glBorelOf A)) {γ γ' : GL (Fin 2) A} (h : γ = γ')
    (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) (AutomorphicForm.centralizerBorel A γ))
    (R : (GL (Fin 2) A → ℂ) → ℂ)
    (hc : ∀ g : GL (Fin 2) A → ℂ, ∫ t, g (t : GL (Fin 2) A) ∂τ = R g)
    (f : GL (Fin 2) A → ℂ) (I : ℂ) (hI : AutomorphicForm.IsOrbitalIntegralOn A μ γ τ f I) :
    ∃ τ' : @Measure (Subgroup.centralizer ({γ'} : Set (GL (Fin 2) A))) (AutomorphicForm.centralizerBorel A γ'),
      (∀ g : GL (Fin 2) A → ℂ, ∫ t, g (t : GL (Fin 2) A) ∂τ' = R g) ∧
        AutomorphicForm.IsOrbitalIntegralOn A μ γ' τ' f I := by
  subst h
  exact ⟨τ, hc, hI⟩

omit [TopologicalSpace A] in
theorem diagUnits2_injective : Function.Injective (fun p : Aˣ × Aˣ => diagUnits2 p.1 p.2) := by
  intro p q h
  have h00 := congrArg (fun g : GL (Fin 2) A => (g : Matrix (Fin 2) (Fin 2) A) 0 0) h
  have h11 := congrArg (fun g : GL (Fin 2) A => (g : Matrix (Fin 2) (Fin 2) A) 1 1) h
  simp only [LanglandsTunnell.CubicInduction.coe_diagUnits2, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one] at h00 h11
  exact Prod.ext (Units.ext h00) (Units.ext h11)

end Generic

section Arch

variable (K : Type) [Field K] [NumberField K]

omit [NumberField K] in
theorem secondCountableTopology_completion (v : InfinitePlace K) : SecondCountableTopology v.Completion :=
  (InfinitePlace.Completion.isometry_extensionEmbedding v).isEmbedding.secondCountableTopology

theorem secondCountableTopology_infiniteAdeleRing : SecondCountableTopology (InfiniteAdeleRing K) := by
  haveI := secondCountableTopology_completion K
  exact inferInstanceAs (SecondCountableTopology ((v : InfinitePlace K) → v.Completion))

theorem secondCountableTopology_units : SecondCountableTopology (InfiniteAdeleRing K)ˣ := by
  haveI := secondCountableTopology_infiniteAdeleRing K
  haveI : SecondCountableTopology (InfiniteAdeleRing K)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isInducing.secondCountableTopology
  exact Units.isInducing_embedProduct.secondCountableTopology

theorem locallyCompactSpace_units : LocallyCompactSpace (InfiniteAdeleRing K)ˣ := by
  haveI : LocallyCompactSpace (InfiniteAdeleRing K)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  exact Units.isClosedEmbedding_embedProduct.locallyCompactSpace

@[reducible] noncomputable def unitsBorel : MeasurableSpace (InfiniteAdeleRing K)ˣ := borel _

theorem borelSpace_unitsBorel : @BorelSpace (InfiniteAdeleRing K)ˣ _ (unitsBorel K) :=
  @BorelSpace.mk _ _ (unitsBorel K) rfl

attribute [local instance] unitsBorel

theorem exists_eq_smul_map (γ : GL (Fin 2) (InfiniteAdeleRing K))
    (h10 : (γ : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 1 0 = 0)
    (h01 : (γ : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 0 1 = 0)
    (hreg : IsUnit ((γ : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 0 0 -
      (γ : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 1 1))
    [SecondCountableTopology (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (InfiniteAdeleRing K))))]
    [LocallyCompactSpace (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (InfiniteAdeleRing K))))]
    (τ : Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (InfiniteAdeleRing K)))))
    [τ.IsHaarMeasure]
    (ρ : Measure (InfiniteAdeleRing K)ˣ) [ρ.IsHaarMeasure] :
    ∃ c : ℝ≥0, 0 < c ∧ τ = c • (ρ.prod ρ).map (PccTorus.torusEquiv γ h10 h01 hreg) := by
  haveI : BorelSpace (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (InfiniteAdeleRing K)))) := ⟨rfl⟩
  haveI := borelSpace_unitsBorel K
  haveI := secondCountableTopology_units K
  haveI := locallyCompactSpace_units K
  haveI : BorelSpace ((InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ) := Prod.borelSpace
  haveI : SigmaCompactSpace (InfiniteAdeleRing K)ˣ := sigmaCompactSpace_of_locallyCompact_secondCountable
  haveI : SigmaFinite ρ := Measure.IsHaarMeasure.sigmaFinite ρ
  haveI : SFinite ρ := inferInstance
  haveI : (ρ.prod ρ).IsHaarMeasure := inferInstance
  haveI : ((ρ.prod ρ).map (PccTorus.torusEquiv γ h10 h01 hreg)).IsHaarMeasure :=
    (PccTorus.torusEquiv γ h10 h01 hreg).isHaarMeasure_map _
  exact ⟨Measure.haarScalarFactor τ ((ρ.prod ρ).map (PccTorus.torusEquiv γ h10 h01 hreg)),
    Measure.haarScalarFactor_pos_of_isHaarMeasure _ _, Measure.isMulLeftInvariant_eq_smul τ _⟩

theorem integral_map_torusEquiv (γ : GL (Fin 2) (InfiniteAdeleRing K))
    (h10 : (γ : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 1 0 = 0)
    (h01 : (γ : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 0 1 = 0)
    (hreg : IsUnit ((γ : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 0 0 -
      (γ : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 1 1))
    (μ2 : Measure ((InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ))
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : GL (Fin 2) (InfiniteAdeleRing K) → E) :
    ∫ t, g (t : GL (Fin 2) (InfiniteAdeleRing K)) ∂(μ2.map (PccTorus.torusEquiv γ h10 h01 hreg)) =
      ∫ p, g (diagUnits2 p.1 p.2) ∂μ2 := by
  haveI : BorelSpace (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (InfiniteAdeleRing K)))) := ⟨rfl⟩
  haveI := borelSpace_unitsBorel K
  haveI := secondCountableTopology_units K
  haveI : BorelSpace ((InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ) := Prod.borelSpace
  rw [show ⇑(PccTorus.torusEquiv γ h10 h01 hreg) =
      ⇑((PccTorus.torusEquiv γ h10 h01 hreg).toHomeomorph.toMeasurableEquiv) from rfl,
    MeasureTheory.integral_map_equiv]
  rfl

theorem adeleArch_algebraMap_apply_ne_one (u : Kˣ) (hu1 : (u : K) ≠ 1) (w : InfinitePlace K) :
    AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) (u : K)) w ≠ 1 := by
  rw [AdelicLevel.adeleArch_apply]
  change algebraMap K w.Completion (u : K) ≠ 1
  intro h
  exact hu1 ((algebraMap K w.Completion).injective (by rw [h, map_one]))

end Arch

end AWin

open scoped Classical in
theorem solution
    (K : Type) [Field K] [NumberField K]
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (νZK : Measure (AdeleRing (𝓞 K) K)ˣ) [νZK.IsHaarMeasure]
    (fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ) (hfa : AutomorphicForm.IsArchTestFactor K fa)
    (cτK : ℝ) (hcτK : 0 < cτK)
    (νA : @Measure (GL (Fin 2) (InfiniteAdeleRing K)) (AutomorphicForm.glBorelOf (InfiniteAdeleRing K)))
    (hνA : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.glBorelOf (InfiniteAdeleRing K)) νA)
    (τG : ∀ (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ),
      Measure (Subgroup.centralizer ({(AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K)))))
    (hτG : ∀ u z, ((u : Kˣ) : K) ≠ 1 → (τG u z).IsHaarMeasure)
    (hτGc : ∀ u z, ((u : Kˣ) : K) ≠ 1 → ∀ g : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ,
      ∫ t : Subgroup.centralizer ({(AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))),
          g (t : GL (Fin 2) (AdeleRing (𝓞 K) K)) ∂(τG u z) =
        cτK * ∫ p : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ, g (diagUnits2 p.1 p.2) ∂(νZK.prod νZK))
    (τA : ∀ (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ),
      @Measure (Subgroup.centralizer
          ({AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)} : Set (GL (Fin 2) (InfiniteAdeleRing K))))
        (AutomorphicForm.centralizerBorel (InfiniteAdeleRing K) (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))))
    (hτA : ∀ u z, ((u : Kˣ) : K) ≠ 1 → @Measure.IsHaarMeasure _ _ _
      (AutomorphicForm.centralizerBorel (InfiniteAdeleRing K) (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) (τA u z))
    (τF : ∀ (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ) (v : HeightOneSpectrum (𝓞 K)),
      @Measure (AutomorphicForm.localCentralizer K v
          (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))))
        (AutomorphicForm.localCentralizerBorel K v
          (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)))))
    (hτF : ∀ u z v, ((u : Kˣ) : K) ≠ 1 → @Measure.IsHaarMeasure _ _ _
      (AutomorphicForm.localCentralizerBorel K v
        (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)))) (τF u z v))
    (hτF1 : ∀ u z v, ((u : Kˣ) : K) ≠ 1 → τF u z v (Subtype.val ⁻¹' AutomorphicForm.localIntegralSet K v) = 1)
    (cT : ℝ) (hcT : 0 < cT)
    (hT : ∀ (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ), (u : K) ≠ 1 → ∀ (S : Finset (HeightOneSpectrum (𝓞 K)))
        (W : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) (Wa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)
        (WS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ),
        AEStronglyMeasurable[AutomorphicForm.centralizerBorel (InfiniteAdeleRing K)
          (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))] (fun t => Wa t) (τA u z) →
        (∀ v ∈ S, AEStronglyMeasurable[AutomorphicForm.localCentralizerBorel K v
          (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)))]
            (fun t => WS v t) (τF u z v)) →
        (∀ t : Subgroup.centralizer ({(AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))),
          (∀ v ∉ S, AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K t) ∈
              AutomorphicForm.localIntegralSet K v) →
            W t = Wa (AdelicLevel.glArch (𝓞 K) K t) *
              ∏ v ∈ S, WS v (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K t))) →
        (∀ t : Subgroup.centralizer ({(AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))),
          (∃ v ∉ S, AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K t) ∉
              AutomorphicForm.localIntegralSet K v) → W t = 0) →
          ∫ t, W t ∂(τG u z) = cT * (∫ t, Wa t ∂(τA u z)) * ∏ v ∈ S, ∫ t, WS v t ∂(τF u z v))
    :
    ∃ Φ : (Fin 2 → mixedEmbedding.mixedSpace K) → ℂ,
      ContDiff ℝ (⊤ : ℕ∞) Φ ∧ HasCompactSupport Φ ∧
      (∀ p : Fin 2 → mixedEmbedding.mixedSpace K, Φ p ≠ 0 →
        IsUnit ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (p 0)) ∧
          IsUnit ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (p 1))) ∧
      (∃ Ca : Set ((InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ), IsCompact Ca ∧
        ∀ p ∈ tsupport Φ, ∃ q ∈ Ca,
          p = ![InfiniteAdeleRing.ringEquiv_mixedSpace K ((q.1 : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K),
                InfiniteAdeleRing.ringEquiv_mixedSpace K ((q.2 : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K)]) ∧
      ∀ (u : Kˣ), (u : K) ≠ 1 → ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (I : ℂ),
        AutomorphicForm.IsOrbitalIntegralOn (InfiniteAdeleRing K) νA
            (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)) (τA u z) fa I →
          ((∏ w : InfinitePlace K,
              ‖AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) (u : K)) w - 1‖ ^ w.mult : ℝ) : ℂ) * I =
            Φ ![InfiniteAdeleRing.ringEquiv_mixedSpace K
                  (AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) (u : K))),
                InfiniteAdeleRing.ringEquiv_mixedSpace K
                  (AdelicLevel.adeleArch (𝓞 K) K ((z : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K))] := by
  classical

  letI mGL : MeasurableSpace (GL (Fin 2) (InfiniteAdeleRing K)) := AutomorphicForm.glBorelOf (InfiniteAdeleRing K)
  haveI : BorelSpace (GL (Fin 2) (InfiniteAdeleRing K)) := AutomorphicForm.borelSpace_glBorelOf (InfiniteAdeleRing K)
  letI mU : MeasurableSpace (InfiniteAdeleRing K)ˣ := AWin.unitsBorel K
  haveI : BorelSpace (InfiniteAdeleRing K)ˣ := AWin.borelSpace_unitsBorel K
  haveI := AWin.secondCountableTopology_units K
  haveI := AWin.locallyCompactSpace_units K
  haveI : BorelSpace ((InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ) := Prod.borelSpace

  set γ : Kˣ → (AdeleRing (𝓞 K) K)ˣ → GL (Fin 2) (InfiniteAdeleRing K) :=
    fun u z => AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1) with hγ
  have h10 : ∀ (u : Kˣ) z, ((γ u z : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 1 0 = 0 :=
    fun u z => (PccArch.gamma_entries K u z).1
  have h01 : ∀ (u : Kˣ) z, ((γ u z : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 0 1 = 0 :=
    fun u z => (PccArch.gamma_entries K u z).2.1
  have hreg : ∀ (u : Kˣ) (hu : (u : K) ≠ 1) z, IsUnit (((γ u z : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 0 0 -
      ((γ u z : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 1 1) :=
    fun u hu z => PccArch.isUnit_gamma_sub K u hu z
  have hSC : ∀ (u : Kˣ) z, SecondCountableTopology (Subgroup.centralizer ({γ u z} : Set (GL (Fin 2) (InfiniteAdeleRing K)))) :=
    fun u z => (AutomorphicForm.centralizer_secondCountableTopology_locallyCompactSpace_and_exists_glArch_finComponent_localIntegralSet_isOpen_surjective_isCompact_restrictedProduct
      K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)).2.2.1
  have hLC : ∀ (u : Kˣ) z, LocallyCompactSpace (Subgroup.centralizer ({γ u z} : Set (GL (Fin 2) (InfiniteAdeleRing K)))) :=
    fun u z => (AutomorphicForm.centralizer_secondCountableTopology_locallyCompactSpace_and_exists_glArch_finComponent_localIntegralSet_isOpen_surjective_isCompact_restrictedProduct
      K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)).2.2.2.1

  set ρ : Measure (InfiniteAdeleRing K)ˣ := Measure.haar with hρ
  set e : ∀ (u : Kˣ) (hu : (u : K) ≠ 1) z, ((InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ) ≃ₜ*
      Subgroup.centralizer ({γ u z} : Set (GL (Fin 2) (InfiniteAdeleRing K))) :=
    fun u hu z => PccTorus.torusEquiv (γ u z) (h10 u z) (h01 u z) (hreg u hu z) with he

  have hcls : ∀ (u : Kˣ) (hu : (u : K) ≠ 1) z, ∃ c : ℝ≥0, 0 < c ∧ τA u z = c • (ρ.prod ρ).map (e u hu z) := by
    intro u hu z
    haveI := hSC u z; haveI := hLC u z; haveI := hτA u z hu
    exact AWin.exists_eq_smul_map K (γ u z) (h10 u z) (h01 u z) (hreg u hu z) (τA u z) ρ
  choose c hcpos hcτ using hcls
  have hcoup : ∀ (u : Kˣ) (hu : (u : K) ≠ 1) z (g : GL (Fin 2) (InfiniteAdeleRing K) → ℂ),
      ∫ t, g (t : GL (Fin 2) (InfiniteAdeleRing K)) ∂((ρ.prod ρ).map (e u hu z)) =
        ∫ p : (InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ, g (diagUnits2 p.1 p.2) ∂(ρ.prod ρ) :=
    fun u hu z g => AWin.integral_map_torusEquiv K (γ u z) (h10 u z) (h01 u z) (hreg u hu z) (ρ.prod ρ) g

  have hn1 : (((-1 : Kˣ)) : K) ≠ 1 := by
    rw [Units.val_neg, Units.val_one]
    intro h
    exact two_ne_zero (α := K) (by linear_combination (-1 : K) * h)

  have hconst : ∀ (u : Kˣ) (hu : (u : K) ≠ 1) z, c u hu z = c (-1) hn1 1 := by

    obtain ⟨C, hCc, hC1⟩ := exists_compact_mem_nhds (1 : (InfiniteAdeleRing K)ˣ)
    have hρC0 : ρ C ≠ 0 := (Measure.measure_pos_of_mem_nhds ρ hC1).ne'
    have hρCt : ρ C ≠ ⊤ := hCc.measure_lt_top.ne
    have hCCm : MeasurableSet (C ×ˢ C) := (hCc.prod hCc).isClosed.measurableSet
    obtain ⟨S, hS⟩ : ∃ S : Set (GL (Fin 2) (InfiniteAdeleRing K)),
        S = (fun p : (InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ => diagUnits2 p.1 p.2) '' (C ×ˢ C) := ⟨_, rfl⟩
    have hSc : IsClosed S := hS ▸ ((hCc.prod hCc).image PccTorus.continuous_diagUnits2).isClosed
    obtain ⟨Wa, hWa⟩ : ∃ Wa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ, Wa = S.indicator (fun _ => (1 : ℂ)) := ⟨_, rfl⟩
    have hWam : Measurable Wa := hWa ▸ (measurable_const.indicator hSc.measurableSet)
    obtain ⟨Wf, hWf⟩ : ∃ Wf : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ, Wf = fun g =>
        if ∀ v : HeightOneSpectrum (𝓞 K),
            AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K g) ∈ AutomorphicForm.localIntegralSet K v
        then Wa (AdelicLevel.glArch (𝓞 K) K g) else 0 := ⟨_, rfl⟩

    have hWa_diag : ∀ p : (InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ,
        Wa (diagUnits2 p.1 p.2) = (C ×ˢ C).indicator (fun _ => (1 : ℂ)) p := by
      intro p
      rw [hWa]
      by_cases hp : p ∈ C ×ˢ C
      · rw [Set.indicator_of_mem hp, Set.indicator_of_mem]
        exact hS ▸ ⟨p, hp, rfl⟩
      · rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem]
        rw [hS]
        rintro ⟨q, hq, hqp⟩
        exact hp (AWin.diagUnits2_injective hqp ▸ hq)
    have hJ : ∫ p : (InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ, Wa (diagUnits2 p.1 p.2) ∂(ρ.prod ρ) =
        (((ρ C).toReal : ℝ) : ℂ) * (((ρ C).toReal : ℝ) : ℂ) := by
      simp_rw [hWa_diag]
      rw [integral_indicator_const _ hCCm, measureReal_def, Measure.prod_prod, ENNReal.toReal_mul, Complex.real_smul,
        mul_one, Complex.ofReal_mul]
    have hJne : (∫ p : (InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ, Wa (diagUnits2 p.1 p.2) ∂(ρ.prod ρ)) ≠ 0 := by
      rw [hJ]
      have h : (((ρ C).toReal : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (ENNReal.toReal_ne_zero.2 ⟨hρC0, hρCt⟩)
      exact mul_ne_zero h h

    have hz : ∀ (u : Kˣ) (hu : (u : K) ≠ 1) z, (cT : ℂ) * ((((c u hu z : ℝ≥0) : ℝ) : ℂ) *
        ∫ p : (InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ, Wa (diagUnits2 p.1 p.2) ∂(ρ.prod ρ)) =
        cτK * ∫ p : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ, Wf (diagUnits2 p.1 p.2) ∂(νZK.prod νZK) := by
      intro u hu z
      haveI : BorelSpace (Subgroup.centralizer ({γ u z} : Set (GL (Fin 2) (InfiniteAdeleRing K)))) := ⟨rfl⟩
      have hmeas : AEStronglyMeasurable
          (fun t : Subgroup.centralizer ({γ u z} : Set (GL (Fin 2) (InfiniteAdeleRing K))) =>
            Wa (t : GL (Fin 2) (InfiniteAdeleRing K))) (τA u z) :=
        (hWam.comp continuous_subtype_val.measurable).aestronglyMeasurable
      have h1 := hT u z hu ∅ Wf Wa (fun _ _ => 0) hmeas (by simp) ?_ ?_
      rotate_left
      · intro t ht
        rw [Finset.prod_empty, mul_one, hWf]
        exact if_pos (fun v => ht v (by simp))
      · rintro t ⟨v, -, hv⟩
        rw [hWf]
        exact if_neg (fun h => hv (h v))
      rw [Finset.prod_empty, mul_one] at h1
      have h3 : ∫ t, Wa t ∂(τA u z) = (((c u hu z : ℝ≥0) : ℝ) : ℂ) *
          ∫ p : (InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ, Wa (diagUnits2 p.1 p.2) ∂(ρ.prod ρ) := by
        rw [hcτ u hu z, integral_smul_nnreal_measure, hcoup u hu z Wa, NNReal.smul_def, Complex.real_smul]
      rw [h3] at h1
      rw [← h1, hτGc u z hu Wf]
    intro u hu z
    have h := (hz u hu z).trans (hz (-1) hn1 1).symm
    have hcT' : (cT : ℂ) ≠ 0 := by exact_mod_cast hcT.ne'
    have h' := mul_right_cancel₀ hJne (mul_left_cancel₀ hcT' h)
    exact_mod_cast h'

  obtain ⟨Φ, hΦs, hΦc, hΦu, ⟨Ca, hCa, hCamem⟩, hwin⟩ :=
    AutomorphicForm.exists_contDiff_hasCompactSupport_tsupport_subset_units_prod_norm_sub_one_pow_mul_eq_of_isOrbitalIntegralOn_scalar_mul_diagUnits2
      K fa hfa νA hνA ρ
  have hc1 : (((c (-1) hn1 1 : ℝ≥0) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (hcpos (-1) hn1 1).ne'
  refine ⟨fun p => (((c (-1) hn1 1 : ℝ≥0) : ℝ) : ℂ)⁻¹ * Φ p, contDiff_const.mul hΦs, hΦc.mul_left, fun p hp => hΦu p ?_,
    ⟨Ca, hCa, fun p hp => hCamem p (tsupport_mul_subset_right hp)⟩, ?_⟩
  · intro h
    apply hp
    show (((c (-1) hn1 1 : ℝ≥0) : ℝ) : ℂ)⁻¹ * Φ p = 0
    rw [h, mul_zero]
  intro u hu z I hI

  have hI' : AutomorphicForm.IsOrbitalIntegralOn (InfiniteAdeleRing K) νA (γ u z) ((ρ.prod ρ).map (e u hu z)) fa
      ((((c (-1) hn1 1 : ℝ≥0) : ℝ) : ℂ) * I) := by
    have h := AWin.isOrbitalIntegralOn_of_eq_smul νA (γ u z) (τA u z) ((ρ.prod ρ).map (e u hu z)) (c u hu z) (hcτ u hu z) fa I hI
    rwa [hconst u hu z] at h

  set zI : (InfiniteAdeleRing K)ˣ := Units.map (AdelicLevel.adeleArch (𝓞 K) K : AdeleRing (𝓞 K) K →* InfiniteAdeleRing K) z with hzI
  set uI : (InfiniteAdeleRing K)ˣ := Units.map (AdelicLevel.adeleArch (𝓞 K) K : AdeleRing (𝓞 K) K →* InfiniteAdeleRing K) (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) with huI
  have hγ' : γ u z = Matrix.GeneralLinearGroup.scalar (Fin 2) zI * diagUnits2 uI 1 := by
    have h := AutomorphicForm.glArch_centralScalar_mul_diagUnits2 K z (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1
    rwa [map_one] at h
  obtain ⟨τ', hτ'c, hI''⟩ := AWin.transport νA hγ' ((ρ.prod ρ).map (e u hu z))
    (fun g => ∫ p : (InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ, g (diagUnits2 p.1 p.2) ∂(ρ.prod ρ))
    (hcoup u hu z) fa _ hI'
  have huI1 : ∀ w : InfinitePlace K, (uI : InfiniteAdeleRing K) w ≠ 1 :=
    AWin.adeleArch_algebraMap_apply_ne_one K u hu
  have key := hwin uI zI huI1 τ' hτ'c _ hI''

  have key' : ((∏ w : InfinitePlace K,
        ‖AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) (u : K)) w - 1‖ ^ w.mult : ℝ) : ℂ) *
        ((((c (-1) hn1 1 : ℝ≥0) : ℝ) : ℂ) * I) =
      Φ ![InfiniteAdeleRing.ringEquiv_mixedSpace K
            (AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) (u : K))),
          InfiniteAdeleRing.ringEquiv_mixedSpace K
            (AdelicLevel.adeleArch (𝓞 K) K ((z : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K))] := key
  show _ = (((c (-1) hn1 1 : ℝ≥0) : ℝ) : ℂ)⁻¹ * Φ _
  rw [← key']
  field_simp

end S_AutomorphicForm_exists_contDiff_hasCompactSupport_tsupport_subset_units_prod_norm_sub_one_pow_mul_eq_of_isOrbitalIntegralOn_glArch_centralScalar_mul_diagUnits2_of_ne_one
end P2MW
export P2MW.S_AutomorphicForm_exists_contDiff_hasCompactSupport_tsupport_subset_units_prod_norm_sub_one_pow_mul_eq_of_isOrbitalIntegralOn_glArch_centralScalar_mul_diagUnits2_of_ne_one (solution)
