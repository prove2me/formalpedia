-- Prove2me | solution 1 for AutomorphicForm.integrable_and_integral_finsum_borel_div_mem_inv_unipotentGL2_mul_eq_integral_finsum_of_norm_ne_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/2cd1112b-42aa-5ae2-8dfc-5c69734a53b1

import Mathlib
import Definitions.Def_AutomorphicForm_SigmaAdelicAction
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_AdelicHaar
import Theorems.Thm_NumberField_AdeleRing_finite_setOf_algebraMap_mem_of_isCompact
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Theorems.Thm_M4aHerbrand_IdeleGaloisDescent_exists_continuousAddEquiv_measurePreserving_act_sub_algebraMap_mul_of_norm_ne_one
import Theorems.Thm_M4aHerbrand_IdeleGaloisDescent_bijective_act_sub_algebraMap_mul_of_norm_ne_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_integrable_and_integral_finsum_borel_div_mem_inv_unipotentGL2_mul_eq_integral_finsum_of_norm_ne_one
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

noncomputable section

namespace R4UnipSubst

set_option maxHeartbeats 1600000

open MeasureTheory MeasureTheory.Measure NumberField Filter Function Set AutomorphicForm
open scoped ENNReal NNReal Topology Pointwise

section Lattice

variable {G : Type*} [AddGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]

theorem measurePreserving_of_forall_apply_mem_iff
    (μ : Measure G) [μ.IsAddHaarMeasure] [μ.Regular]
    (Γ : AddSubgroup G) [Countable Γ] (F : Set G) (hF : IsAddFundamentalDomain Γ F μ)
    (hFtop : μ F ≠ ⊤) (φ : G ≃ₜ+ G) (hφ : ∀ x : G, φ x ∈ Γ ↔ x ∈ Γ) :
    MeasurePreserving φ μ μ := by
  classical
  have hφm : Measurable (φ : G → G) := φ.continuous.measurable
  set e : G ≃ᵐ G := φ.toHomeomorph.toMeasurableEquiv with he
  have hecoe : (e : G → G) = φ := rfl
  set c : ℝ≥0 := addEquivAddHaarChar φ with hc
  have hcμ : c • μ.map φ = μ := addEquivAddHaarChar_smul_map μ φ
  have hmp : MeasurePreserving (φ : G → G) μ (μ.map φ) := ⟨hφm, rfl⟩
  have hmp' : MeasurePreserving (e : G → G) μ (μ.map φ) := by rw [hecoe]; exact hmp
  have hsymm : MeasurePreserving (e.symm : G → G) (μ.map φ) μ := hmp'.symm e
  have hφs : ∀ x : G, φ.symm x ∈ Γ ↔ x ∈ Γ := fun x => by
    rw [← hφ (φ.symm x), ContinuousAddEquiv.apply_symm_apply]
  set ε : Γ ≃ Γ :=
    { toFun := fun γ => ⟨φ.symm γ, (hφs γ).mpr γ.2⟩
      invFun := fun γ => ⟨φ γ, (hφ γ).mpr γ.2⟩
      left_inv := fun γ => Subtype.ext (by simp)
      right_inv := fun γ => Subtype.ext (by simp) } with hε
  have hF' : IsAddFundamentalDomain Γ ((φ.toEquiv : G ≃ G) '' F) (μ.map φ) := by
    refine hF.image_of_equiv (φ.toEquiv : G ≃ G) ?_ ε ?_
    · have : ((φ.toEquiv : G ≃ G).symm : G → G) = (e.symm : G → G) := rfl
      rw [this]
      exact hsymm.quasiMeasurePreserving
    · intro γ x
      show φ ((φ.symm (γ : G)) + x) = (γ : G) + φ x
      rw [map_add, ContinuousAddEquiv.apply_symm_apply]
  have himg : ((φ.toEquiv : G ≃ G) '' F) = φ '' F := rfl
  rw [himg] at hF'
  have hac0 : (c • μ.map φ) ≪ μ.map φ := smul_absolutelyContinuous
  have hac : μ ≪ μ.map φ := fun s hs => by
    have h := hac0 hs
    rwa [hcμ] at h
  have hF'' : IsAddFundamentalDomain Γ (φ '' F) μ := hF'.mono hac
  have h1 : μ (φ '' F) = μ F := hF''.measure_eq hF
  have h2 : μ.map φ (φ '' F) = μ F := by
    rw [map_apply₀ hφm.aemeasurable hF'.nullMeasurableSet, Set.preimage_image_eq _ φ.injective]
  have h3 : μ (φ '' F) = (c : ℝ≥0∞) * μ.map φ (φ '' F) := by
    conv_lhs => rw [← hcμ]
    rfl
  rw [h1, h2] at h3
  have hμ0 : μ ≠ 0 := NeZero.ne μ
  have hF0 : μ F ≠ 0 := hF.measure_ne_zero hμ0
  have hc1 : (c : ℝ≥0∞) = 1 := (ENNReal.mul_eq_right hF0 hFtop).mp h3.symm
  have hc1' : c = 1 := by exact_mod_cast hc1
  have hmap : μ.map φ = μ := by
    have := hcμ
    rw [hc1', one_smul] at this
    exact this
  exact ⟨hφm, hmap⟩

end Lattice

section GL2

variable {R : Type*} [CommRing R]

def diag2 (p q : Rˣ) : GL (Fin 2) R where
  val := !![(p : R), 0; 0, (q : R)]
  inv := !![((p⁻¹ : Rˣ) : R), 0; 0, ((q⁻¹ : Rˣ) : R)]
  val_inv := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

@[scoped simp] theorem diag2_val (p q : Rˣ) :
    ((diag2 p q : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) = !![(p : R), 0; 0, (q : R)] := rfl

theorem unipotentGL2_neg (t : R) : unipotentGL2 (-t) = (unipotentGL2 t)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← unipotentGL2_add, neg_add_cancel, unipotentGL2_zero]

theorem unipotent_mul_diag2 (p q : Rˣ) (u : R) :
    unipotentGL2 u * diag2 p q = diag2 p q * unipotentGL2 (((p⁻¹ : Rˣ) : R) * (q : R) * u) := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, diag2_val, unipotentGL2_coe, unipotentGL2_coe]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  rw [← mul_assoc, ← mul_assoc, Units.mul_inv, one_mul, mul_comm]

theorem val_diag2_mul_unipotent (p q : Rˣ) (s : R) :
    ((diag2 p q * unipotentGL2 s : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) =
      !![(p : R), (p : R) * s; 0, (q : R)] := by
  rw [Units.val_mul, diag2_val, unipotentGL2_coe]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

variable [TopologicalSpace R]

omit [CommRing R] in
theorem continuous_matrix_two {X : Type*} [TopologicalSpace X] {f : X → Matrix (Fin 2) (Fin 2) R}
    (h00 : Continuous fun x => f x 0 0) (h01 : Continuous fun x => f x 0 1)
    (h10 : Continuous fun x => f x 1 0) (h11 : Continuous fun x => f x 1 1) : Continuous f := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  fin_cases i <;> fin_cases j
  exacts [h00, h01, h10, h11]

theorem continuous_unipotentGL2' [IsTopologicalRing R] : Continuous fun v : R => (unipotentGL2 v : GL (Fin 2) R) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · show Continuous fun v : R => !![(1 : R), v; 0, 1]
    exact continuous_matrix_two (by simpa using continuous_const) (by simp; exact continuous_id)
      (by simpa using continuous_const) (by simpa using continuous_const)
  · show Continuous fun v : R => !![(1 : R), -v; 0, 1]
    exact continuous_matrix_two (by simpa using continuous_const) (by simpa using continuous_neg)
      (by simpa using continuous_const) (by simpa using continuous_const)

end GL2

section FieldGL2

variable {L : Type} [Field L]

theorem det_ne_zero_entries (d : GL (Fin 2) L) (h10 : (d : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) :
    (d : Matrix (Fin 2) (Fin 2) L) 0 0 ≠ 0 ∧ (d : Matrix (Fin 2) (Fin 2) L) 1 1 ≠ 0 := by
  have hdet : (d : Matrix (Fin 2) (Fin 2) L).det ≠ 0 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply]
    exact (Matrix.GeneralLinearGroup.det d).ne_zero
  rw [Matrix.det_fin_two, h10, mul_zero, sub_zero] at hdet
  exact ⟨left_ne_zero_of_mul hdet, right_ne_zero_of_mul hdet⟩

def e0 (d : GL (Fin 2) L) (h10 : (d : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) : Lˣ :=
  Units.mk0 _ (det_ne_zero_entries d h10).1

def e1 (d : GL (Fin 2) L) (h10 : (d : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) : Lˣ :=
  Units.mk0 _ (det_ne_zero_entries d h10).2

@[scoped simp] theorem coe_e0 (d : GL (Fin 2) L) (h10 : (d : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) :
    ((e0 d h10 : Lˣ) : L) = (d : Matrix (Fin 2) (Fin 2) L) 0 0 := rfl

@[scoped simp] theorem coe_e1 (d : GL (Fin 2) L) (h10 : (d : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) :
    ((e1 d h10 : Lˣ) : L) = (d : Matrix (Fin 2) (Fin 2) L) 1 1 := rfl

theorem eq_diag2_mul_unipotent_of_upper (b : GL (Fin 2) L) (h10 : (b : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) :
    b = diag2 (e0 b h10) (e1 b h10) * unipotentGL2 ((b : Matrix (Fin 2) (Fin 2) L) 0 1 / (b : Matrix (Fin 2) (Fin 2) L) 0 0) := by
  have h0 := (det_ne_zero_entries b h10).1
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [val_diag2_mul_unipotent]
  fin_cases i <;> fin_cases j
  · simp
  · simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.empty_val', coe_e0]
    rw [mul_div_cancel₀ _ h0]
  · simp [h10]
  · simp

end FieldGL2

section Param

variable {L : Type} [Field L] (A : Set L)

def BA : Set (GL (Fin 2) L) :=
  {γ : GL (Fin 2) L | (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
    (γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1 ∈ A}

def dom : Set ((Lˣ × Lˣ) × L) := {c | ((c.1.1 : Lˣ) : L) / ((c.1.2 : Lˣ) : L) ∈ A}

def param (c : (Lˣ × Lˣ) × L) : GL (Fin 2) L := diag2 c.1.1 c.1.2 * unipotentGL2 c.2

theorem param_injective : Function.Injective (param (L := L)) := by
  rintro ⟨⟨p, q⟩, s⟩ ⟨⟨p', q'⟩, s'⟩ h
  have hv := congrArg (fun γ : GL (Fin 2) L => (γ : Matrix (Fin 2) (Fin 2) L)) h
  simp only [param, val_diag2_mul_unipotent] at hv
  have h00 := congrFun (congrFun hv 0) 0
  have h01 := congrFun (congrFun hv 0) 1
  have h11 := congrFun (congrFun hv 1) 1
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Matrix.empty_val'] at h00 h01 h11
  have hp : p = p' := Units.ext h00
  have hq : q = q' := Units.ext h11
  subst hp; subst hq
  have hs : s = s' := mul_left_cancel₀ p.ne_zero h01
  subst hs
  rfl

theorem param_bijOn : Set.BijOn (param (L := L)) (dom A) (BA A) := by
  refine ⟨?_, param_injective.injOn, ?_⟩
  · rintro ⟨⟨p, q⟩, s⟩ hc
    refine ⟨?_, ?_⟩
    · show ((param ((p, q), s) : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 0 = 0
      simp [param]
    · show ((param ((p, q), s) : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 0 0 /
          ((param ((p, q), s) : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 1 ∈ A
      simp [param, val_diag2_mul_unipotent] at hc ⊢
      exact hc
  · rintro γ ⟨h10, hA⟩
    refine ⟨((e0 γ h10, e1 γ h10), (γ : Matrix (Fin 2) (Fin 2) L) 0 1 / (γ : Matrix (Fin 2) (Fin 2) L) 0 0), ?_, ?_⟩
    · show ((e0 γ h10 : Lˣ) : L) / ((e1 γ h10 : Lˣ) : L) ∈ A
      simpa using hA
    · exact (eq_diag2_mul_unipotent_of_upper γ h10).symm

end Param

section Adelic

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
variable (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)

abbrev princ : Lˣ →* (AdeleRing (𝓞 L) L)ˣ :=
  Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)

abbrev ιA : L →+* AdeleRing (𝓞 L) L := algebraMap L (AdeleRing (𝓞 L) L)

abbrev θ : AdeleRing (𝓞 L) L ≃+* AdeleRing (𝓞 L) L := (D.act σ : RingAut (AdeleRing (𝓞 L) L))

theorem sigmaAdelicAct_apply (g : AdelicGL2 (𝓞 L) L) (i j : Fin 2) :
    ((sigmaAdelicAct K L D σ g : AdelicGL2 (𝓞 L) L) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i j =
      θ K L D σ ((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i j) := rfl

theorem sigmaAdelicAct_unipotent (t : AdeleRing (𝓞 L) L) :
    sigmaAdelicAct K L D σ (unipotentGL2 t) = unipotentGL2 (θ K L D σ t) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [sigmaAdelicAct_apply, unipotentGL2_coe, unipotentGL2_coe]
  fin_cases i <;> fin_cases j <;> simp

theorem globalPoints_apply (g : GL (Fin 2) L) (i j : Fin 2) :
    ((globalPoints (𝓞 L) L g : AdelicGL2 (𝓞 L) L) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i j =
      ιA L ((g : Matrix (Fin 2) (Fin 2) L) i j) := rfl

theorem globalPoints_diag2 (p q : Lˣ) : globalPoints (𝓞 L) L (diag2 p q) = diag2 (princ L p) (princ L q) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [globalPoints_apply, diag2_val, diag2_val]
  fin_cases i <;> fin_cases j <;> simp

theorem globalPoints_unipotent (s : L) : globalPoints (𝓞 L) L (unipotentGL2 s) = unipotentGL2 (ιA L s) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [globalPoints_apply, unipotentGL2_coe, unipotentGL2_coe]
  fin_cases i <;> fin_cases j <;> simp

theorem θ_ιA (s : L) : θ K L D σ (ιA L s) = ιA L (σ s) := D.compat σ s

theorem θ_symm_ιA (s : L) : (θ K L D σ).symm (ιA L s) = ιA L (σ.symm s) := by
  apply (θ K L D σ).injective
  rw [RingEquiv.apply_symm_apply, θ_ιA, AlgEquiv.apply_symm_apply]

theorem unipotent_mul_globalPoints_diag2 (p q : Lˣ) (u : AdeleRing (𝓞 L) L) :
    unipotentGL2 u * globalPoints (𝓞 L) L (diag2 p q) =
      globalPoints (𝓞 L) L (diag2 p q) * unipotentGL2 (ιA L ((p⁻¹ * q : Lˣ) : L) * u) := by
  rw [globalPoints_diag2, unipotent_mul_diag2]
  congr 3
  rw [Units.val_mul, map_mul]
  rfl

def Psi (φ : AdelicGL2 (𝓞 L) L → ℂ) (x g : AdelicGL2 (𝓞 L) L) (pq : Lˣ × Lˣ) (v : AdeleRing (𝓞 L) L) : ℂ :=
  φ (x⁻¹ * globalPoints (𝓞 L) L (diag2 pq.1 pq.2) * unipotentGL2 v * sigmaAdelicAct K L D σ g)

theorem arg_eq_right (x g : AdelicGL2 (𝓞 L) L) (p q : Lˣ) (s : L) (t : AdeleRing (𝓞 L) L) :
    x⁻¹ * globalPoints (𝓞 L) L (diag2 p q * unipotentGL2 s) * sigmaAdelicAct K L D σ (unipotentGL2 t * g) =
      x⁻¹ * globalPoints (𝓞 L) L (diag2 p q) * unipotentGL2 (ιA L s + θ K L D σ t) *
        sigmaAdelicAct K L D σ g := by
  rw [map_mul (globalPoints (𝓞 L) L), globalPoints_unipotent, map_mul (sigmaAdelicAct K L D σ),
    sigmaAdelicAct_unipotent, unipotentGL2_add]
  simp only [mul_assoc]

theorem arg_eq_left (x g : AdelicGL2 (𝓞 L) L) (p q : Lˣ) (s : L) (t : AdeleRing (𝓞 L) L) :
    (unipotentGL2 t * x)⁻¹ * globalPoints (𝓞 L) L (diag2 p q * unipotentGL2 s) *
        sigmaAdelicAct K L D σ (unipotentGL2 t * g) =
      x⁻¹ * globalPoints (𝓞 L) L (diag2 p q) *
        unipotentGL2 (ιA L s + (θ K L D σ t - ιA L ((p⁻¹ * q : Lˣ) : L) * t)) *
          sigmaAdelicAct K L D σ g := by
  rw [mul_inv_rev, ← unipotentGL2_neg, map_mul (globalPoints (𝓞 L) L), globalPoints_unipotent,
    map_mul (sigmaAdelicAct K L D σ), sigmaAdelicAct_unipotent]
  have h1 : x⁻¹ * unipotentGL2 (-t) * (globalPoints (𝓞 L) L (diag2 p q) * unipotentGL2 (ιA L s)) *
      (unipotentGL2 (θ K L D σ t) * sigmaAdelicAct K L D σ g) =
      x⁻¹ * (unipotentGL2 (-t) * globalPoints (𝓞 L) L (diag2 p q)) * unipotentGL2 (ιA L s) *
        unipotentGL2 (θ K L D σ t) * sigmaAdelicAct K L D σ g := by
    simp only [mul_assoc]
  rw [h1, unipotent_mul_globalPoints_diag2]
  have h2 : x⁻¹ * (globalPoints (𝓞 L) L (diag2 p q) * unipotentGL2 (ιA L ((p⁻¹ * q : Lˣ) : L) * -t)) *
      unipotentGL2 (ιA L s) * unipotentGL2 (θ K L D σ t) * sigmaAdelicAct K L D σ g =
      x⁻¹ * globalPoints (𝓞 L) L (diag2 p q) *
        (unipotentGL2 (ιA L ((p⁻¹ * q : Lˣ) : L) * -t) * unipotentGL2 (ιA L s) * unipotentGL2 (θ K L D σ t)) *
          sigmaAdelicAct K L D σ g := by
    simp only [mul_assoc]
  rw [h2, ← unipotentGL2_add, ← unipotentGL2_add]
  congr 3
  rw [mul_neg]
  abel

end Adelic

section Periodic

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
variable (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
  (φ : AdelicGL2 (𝓞 L) L → ℂ) (x g : AdelicGL2 (𝓞 L) L)

theorem finite_setOf_ιA_mem {C : Set (AdeleRing (𝓞 L) L)} (hC : IsCompact C) : {s : L | ιA L s ∈ C}.Finite :=
  NumberField.AdeleRing.finite_setOf_algebraMap_mem_of_isCompact L hC

theorem finite_setOf_princ_mem {C : Set (AdeleRing (𝓞 L) L)} (hC : IsCompact C) :
    {u : Lˣ | ιA L (u : L) ∈ C}.Finite :=
  (finite_setOf_ιA_mem L hC).preimage (f := fun u : Lˣ => (u : L)) Units.val_injective.injOn

def Cx : Set (AdelicGL2 (𝓞 L) L) := (fun m => x * m * (sigmaAdelicAct K L D σ g)⁻¹) '' tsupport φ

theorem isCompact_Cx (hφs : HasCompactSupport φ) : IsCompact (Cx K L D σ φ x g) :=
  hφs.isCompact.image ((continuous_const.mul continuous_id).mul continuous_const)

theorem mem_Cx_of_Psi_ne_zero {pq : Lˣ × Lˣ} {v : AdeleRing (𝓞 L) L}
    (h : Psi K L D σ φ x g pq v ≠ 0) :
    globalPoints (𝓞 L) L (diag2 pq.1 pq.2) * unipotentGL2 v ∈ Cx K L D σ φ x g := by
  refine ⟨_, subset_tsupport φ (Function.mem_support.mpr h), ?_⟩
  simp only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one]

def contrib : Set (Lˣ × Lˣ) := {pq | ∃ v, Psi K L D σ φ x g pq v ≠ 0}

theorem finite_contrib (hφs : HasCompactSupport φ) : (contrib K L D σ φ x g).Finite := by
  have hC := isCompact_Cx K L D σ φ x g hφs
  have h0 : {p : Lˣ | ιA L (p : L) ∈
      (fun m : AdelicGL2 (𝓞 L) L => (m : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 0) '' Cx K L D σ φ x g}.Finite :=
    finite_setOf_princ_mem L (hC.image (Units.continuous_val.matrix_elem 0 0))
  have h1 : {q : Lˣ | ιA L (q : L) ∈
      (fun m : AdelicGL2 (𝓞 L) L => (m : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 1 1) '' Cx K L D σ φ x g}.Finite :=
    finite_setOf_princ_mem L (hC.image (Units.continuous_val.matrix_elem 1 1))
  refine ((h0.prod h1).subset ?_)
  rintro ⟨p, q⟩ ⟨v, hv⟩
  have hm := mem_Cx_of_Psi_ne_zero K L D σ φ x g hv
  have hval : ((globalPoints (𝓞 L) L (diag2 p q) * unipotentGL2 v : AdelicGL2 (𝓞 L) L) :
      Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) = !![ιA L (p : L), ιA L (p : L) * v; 0, ιA L (q : L)] := by
    rw [globalPoints_diag2, val_diag2_mul_unipotent]
    rfl
  refine ⟨⟨_, hm, ?_⟩, ⟨_, hm, ?_⟩⟩
  · show ((globalPoints (𝓞 L) L (diag2 p q) * unipotentGL2 v : AdelicGL2 (𝓞 L) L) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 0 = ιA L (p : L)
    rw [hval]; simp
  · show ((globalPoints (𝓞 L) L (diag2 p q) * unipotentGL2 v : AdelicGL2 (𝓞 L) L) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 1 1 = ιA L (q : L)
    rw [hval]; simp

theorem Psi_eq_zero_of_not_mem_contrib {pq : Lˣ × Lˣ} (h : pq ∉ contrib K L D σ φ x g) (v : AdeleRing (𝓞 L) L) :
    Psi K L D σ φ x g pq v = 0 := by
  by_contra hv
  exact h ⟨v, hv⟩

theorem exists_isCompact_support_Psi (hφs : HasCompactSupport φ) (pq : Lˣ × Lˣ) :
    ∃ Cv : Set (AdeleRing (𝓞 L) L), IsCompact Cv ∧ ∀ v, Psi K L D σ φ x g pq v ≠ 0 → v ∈ Cv := by
  have hC := isCompact_Cx K L D σ φ x g hφs
  refine ⟨(fun m : AdelicGL2 (𝓞 L) L => (ιA L ((pq.1⁻¹ : Lˣ) : L)) *
      (m : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 1) '' Cx K L D σ φ x g,
    hC.image (continuous_const.mul (Units.continuous_val.matrix_elem 0 1)), ?_⟩
  intro v hv
  refine ⟨_, mem_Cx_of_Psi_ne_zero K L D σ φ x g hv, ?_⟩
  show ιA L ((pq.1⁻¹ : Lˣ) : L) * ((globalPoints (𝓞 L) L (diag2 pq.1 pq.2) * unipotentGL2 v : AdelicGL2 (𝓞 L) L) :
      Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 1 = v
  rw [globalPoints_diag2, val_diag2_mul_unipotent]
  simp only [Units.coe_map, MonoidHom.coe_coe, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Matrix.cons_val_zero]
  rw [← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]

theorem continuous_Psi (hφc : Continuous φ) (pq : Lˣ × Lˣ) : Continuous (Psi K L D σ φ x g pq) := by
  unfold Psi
  exact hφc.comp ((continuous_const.mul continuous_unipotentGL2').mul continuous_const)

def Pd (pq : Lˣ × Lˣ) (u : AdeleRing (𝓞 L) L) : ℂ := ∑ᶠ s : L, Psi K L D σ φ x g pq (ιA L s + u)

theorem finite_setOf_ιA_add_mem_support (hφs : HasCompactSupport φ) (pq : Lˣ × Lˣ)
    {N : Set (AdeleRing (𝓞 L) L)} (hN : IsCompact N) :
    {s : L | ∃ u ∈ N, Psi K L D σ φ x g pq (ιA L s + u) ≠ 0}.Finite := by
  obtain ⟨Cv, hCv, hsub⟩ := exists_isCompact_support_Psi K L D σ φ x g hφs pq
  have hC : IsCompact ((fun p : AdeleRing (𝓞 L) L × AdeleRing (𝓞 L) L => p.1 - p.2) '' (Cv ×ˢ N)) :=
    (hCv.prod hN).image (continuous_fst.sub continuous_snd)
  refine (finite_setOf_ιA_mem L hC).subset ?_
  rintro s ⟨u, hu, hs⟩
  exact ⟨(ιA L s + u, u), Set.mk_mem_prod (hsub _ hs) hu, by simp only [add_sub_cancel_right]⟩

theorem continuous_Pd (hφc : Continuous φ) (hφs : HasCompactSupport φ) (pq : Lˣ × Lˣ) :
    Continuous (Pd K L D σ φ x g pq) := by
  refine continuous_finsum (fun s => (continuous_Psi K L D σ φ x g hφc pq).comp (continuous_const.add continuous_id)) ?_
  intro u
  obtain ⟨N, hNc, hNu⟩ := exists_compact_mem_nhds u
  refine ⟨N, hNu, ?_⟩
  refine (finite_setOf_ιA_add_mem_support K L D σ φ x g hφs pq hNc).subset ?_
  rintro s ⟨u', hu'1, hu'2⟩
  exact ⟨u', hu'2, hu'1⟩

theorem Pd_periodic (pq : Lˣ × Lˣ) (k : L) (u : AdeleRing (𝓞 L) L) :
    Pd K L D σ φ x g pq (ιA L k + u) = Pd K L D σ φ x g pq u := by
  unfold Pd
  rw [← finsum_comp_equiv (Equiv.subRight k)]
  refine finsum_congr fun s => ?_
  simp only [Equiv.subRight_apply, map_sub]
  congr 1
  abel

end Periodic

section Box

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
variable (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)

abbrev μA : Measure (AdeleRing (𝓞 L) L) := NumberField.AdelicHaar.adelicAddHaar (𝓞 L) L

abbrev μB : Measure (AdeleRing (𝓞 L) L) := ProbabilityTheory.cond (μA L) (NumberField.AdelicBox.adelicBox L)

abbrev Λ : AddSubgroup (AdeleRing (𝓞 L) L) := AdeleRing.principalSubgroup (𝓞 L) L

theorem countable_L : Countable L :=
  (Module.Free.chooseBasis ℚ L).equivFun.toEquiv.countable_iff.2 inferInstance

scoped instance countable_Λ : Countable (Λ L) := by
  have : (Λ L : Set (AdeleRing (𝓞 L) L)).Countable := by
    have hr : (Λ L : Set (AdeleRing (𝓞 L) L)) = Set.range (ιA L) := by
      ext v; exact ⟨fun ⟨y, hy⟩ => ⟨y, hy⟩, fun ⟨y, hy⟩ => ⟨y, hy⟩⟩
    rw [hr]
    haveI := countable_L L
    exact Set.countable_range _
  exact this.to_subtype

theorem integrable_μB_of_continuous {P : AdeleRing (𝓞 L) L → ℂ} (hP : Continuous P) : Integrable P (μB L) := by
  obtain ⟨C, hC, hBC⟩ := NumberField.AdelicBox.exists_isCompact_adelicBox_subset L
  have h1 : IntegrableOn P (NumberField.AdelicBox.adelicBox L) (μA L) :=
    (hP.continuousOn.integrableOn_compact hC).mono_set hBC
  exact h1.smul_measure (ENNReal.inv_ne_top.mpr (NumberField.AdelicBox.adelicAddHaar_adelicBox_pos L).ne')

theorem integral_μB_comp_eq (T : AdeleRing (𝓞 L) L ≃ₜ+ AdeleRing (𝓞 L) L)
    (hT : MeasurePreserving T (μA L) (μA L)) (hTΛ : ∀ v, T v ∈ Λ L ↔ v ∈ Λ L)
    (P : AdeleRing (𝓞 L) L → ℂ) (hP : ∀ (k : L) (u : AdeleRing (𝓞 L) L), P (ιA L k + u) = P u) :
    ∫ t, P (T t) ∂(μB L) = ∫ t, P t ∂(μB L) := by
  rw [show μB L = ((μA L) (NumberField.AdelicBox.adelicBox L))⁻¹ • (μA L).restrict (NumberField.AdelicBox.adelicBox L)
    from rfl, integral_smul_measure, integral_smul_measure]
  congr 1

  have hemb : MeasurableEmbedding T := T.toHomeomorph.measurableEmbedding
  rw [← hT.setIntegral_image_emb hemb P (NumberField.AdelicBox.adelicBox L)]

  have hB : IsAddFundamentalDomain (Λ L) (NumberField.AdelicBox.adelicBox L) (μA L) :=
    NumberField.AdelicBox.isAddFundamentalDomain_adelicBox L _
  have hTs : ∀ v, T.symm v ∈ Λ L ↔ v ∈ Λ L := fun v => by
    rw [← hTΛ (T.symm v), ContinuousAddEquiv.apply_symm_apply]
  set ε : Λ L ≃ Λ L :=
    { toFun := fun γ => ⟨T.symm γ, (hTs γ).mpr γ.2⟩
      invFun := fun γ => ⟨T γ, (hTΛ γ).mpr γ.2⟩
      left_inv := fun γ => Subtype.ext (by simp)
      right_inv := fun γ => Subtype.ext (by simp) } with hε
  have hsymm : MeasurePreserving (T.symm : AdeleRing (𝓞 L) L → AdeleRing (𝓞 L) L) (μA L) (μA L) :=
    hT.symm T.toHomeomorph.toMeasurableEquiv
  have hTB : IsAddFundamentalDomain (Λ L) ((T.toEquiv : AdeleRing (𝓞 L) L ≃ AdeleRing (𝓞 L) L) ''
      NumberField.AdelicBox.adelicBox L) (μA L) := by
    refine hB.image_of_equiv (T.toEquiv : AdeleRing (𝓞 L) L ≃ AdeleRing (𝓞 L) L) ?_ ε ?_
    · exact hsymm.quasiMeasurePreserving
    · intro γ v
      show T ((T.symm (γ : AdeleRing (𝓞 L) L)) + v) = (γ : AdeleRing (𝓞 L) L) + T v
      rw [map_add, ContinuousAddEquiv.apply_symm_apply]
  have himg : ((T.toEquiv : AdeleRing (𝓞 L) L ≃ AdeleRing (𝓞 L) L) '' NumberField.AdelicBox.adelicBox L) =
      T '' NumberField.AdelicBox.adelicBox L := rfl
  rw [himg] at hTB
  refine hTB.setIntegral_eq hB fun γ v => ?_
  obtain ⟨_, k, rfl⟩ := γ
  exact hP k v

def thetaEquiv : AdeleRing (𝓞 L) L ≃ₜ+ AdeleRing (𝓞 L) L :=
  { (θ K L D σ).toAddEquiv with
    continuous_toFun := D.continuous_act σ
    continuous_invFun := by
      have h : Continuous (D.act σ⁻¹ : RingAut (AdeleRing (𝓞 L) L)) := D.continuous_act σ⁻¹
      have heq : ∀ v, (θ K L D σ).toAddEquiv.symm v = (D.act σ⁻¹ : RingAut (AdeleRing (𝓞 L) L)) v := by
        intro v
        rw [map_inv]
        rfl
      show Continuous fun v => (θ K L D σ).toAddEquiv.symm v
      simp_rw [heq]
      exact h }

theorem thetaEquiv_apply (v : AdeleRing (𝓞 L) L) : thetaEquiv K L D σ v = θ K L D σ v := rfl

theorem thetaEquiv_mem_iff (v : AdeleRing (𝓞 L) L) : thetaEquiv K L D σ v ∈ Λ L ↔ v ∈ Λ L := by
  rw [thetaEquiv_apply]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨σ.symm k, ?_⟩
    apply (θ K L D σ).injective
    rw [show (algebraMap L (AdeleRing (𝓞 L) L)) (σ.symm k) = ιA L (σ.symm k) from rfl, θ_ιA,
      AlgEquiv.apply_symm_apply]
    exact hk
  · rintro ⟨k, rfl⟩
    exact ⟨σ k, (θ_ιA K L D σ k).symm⟩

theorem measurePreserving_thetaEquiv : MeasurePreserving (thetaEquiv K L D σ) (μA L) (μA L) := by
  haveI : SecondCountableTopology (AdeleRing (𝓞 L) L) := NumberField.AdeleRing.secondCountableTopology L
  haveI : (μA L).Regular := by
    obtain ⟨Kc, hKc, h0Kc⟩ := exists_compact_mem_nhds (0 : AdeleRing (𝓞 L) L)
    exact Measure.regular_of_isAddLeftInvariant hKc ⟨0, mem_interior_iff_mem_nhds.mpr h0Kc⟩
      hKc.measure_lt_top.ne
  exact measurePreserving_of_forall_apply_mem_iff (μA L) (Λ L) (NumberField.AdelicBox.adelicBox L)
    (NumberField.AdelicBox.isAddFundamentalDomain_adelicBox L _)
    (NumberField.AdelicBox.measure_adelicBox_lt_top L _).ne (thetaEquiv K L D σ) (thetaEquiv_mem_iff K L D σ)

theorem sub_mem_iff [FiniteDimensional K L] [IsGalois K L]
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) (c : L) (hc : Algebra.norm K c ≠ 1)
    (v : AdeleRing (𝓞 L) L) :
    θ K L D σ v - ιA L c * v ∈ Λ L ↔ v ∈ Λ L := by
  set TL : L →ₗ[K] L := (σ : L ≃ₐ[K] L).toLinearMap - c • LinearMap.id with hTL
  have hTL_apply : ∀ y : L, TL y = σ y - c * y := fun y => by
    simp [hTL, smul_eq_mul]
  have hcompat : ∀ y : L, θ K L D σ (ιA L y) - ιA L c * ιA L y = ιA L (TL y) := fun y => by
    rw [hTL_apply, map_sub, map_mul, θ_ιA]
  have hbij := M4aHerbrand.IdeleGaloisDescent.bijective_act_sub_algebraMap_mul_of_norm_ne_one D hgen c hc
  have hTinj : Function.Injective TL := by
    intro y y' hyy
    have h := congrArg (ιA L) hyy
    rw [← hcompat, ← hcompat] at h
    exact NumberField.AdeleRing.algebraMap_injective (R := 𝓞 L) (K := L) (hbij.1 h)
  have hTsurj : Function.Surjective TL := LinearMap.surjective_of_injective hTinj
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨y', rfl⟩ := hTsurj y
    have h : θ K L D σ v - ιA L c * v = θ K L D σ (ιA L y') - ιA L c * ιA L y' := by
      rw [hcompat]; exact hy.symm
    have hv : v = ιA L y' := hbij.1 h
    exact ⟨y', hv.symm⟩
  · rintro ⟨y, rfl⟩
    exact ⟨TL y, (hcompat y).symm⟩

end Box

section Main

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
variable (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
  (A : Set L) (φ : AdelicGL2 (𝓞 L) L → ℂ) (x g : AdelicGL2 (𝓞 L) L)

theorem finite_setOf_globalPoints_mem {C : Set (AdelicGL2 (𝓞 L) L)} (hC : IsCompact C) :
    {γ : GL (Fin 2) L | globalPoints (𝓞 L) L γ ∈ C}.Finite := by
  have hent : ∀ i j : Fin 2, {t : L | ιA L t ∈
      (fun m : AdelicGL2 (𝓞 L) L => (m : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i j) '' C}.Finite :=
    fun i j => finite_setOf_ιA_mem L (hC.image (Units.continuous_val.matrix_elem i j))
  have hpi : (Set.univ.pi fun p : Fin 2 × Fin 2 => {t : L | ιA L t ∈
      (fun m : AdelicGL2 (𝓞 L) L => (m : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) p.1 p.2) '' C}).Finite :=
    Set.Finite.pi fun p => hent p.1 p.2
  refine (hpi.preimage (f := fun γ : GL (Fin 2) L => fun p : Fin 2 × Fin 2 =>
    (γ : Matrix (Fin 2) (Fin 2) L) p.1 p.2) ?_).subset ?_
  · intro γ _ γ' _ h
    refine Matrix.GeneralLinearGroup.ext fun i j => ?_
    exact congrFun h (i, j)
  · intro γ hγ
    refine Set.mem_preimage.mpr (Set.mem_univ_pi.mpr fun p => ?_)
    exact ⟨globalPoints (𝓞 L) L γ, hγ, rfl⟩

theorem finsum_BA_eq
    (τ : Lˣ × Lˣ → AdeleRing (𝓞 L) L → AdeleRing (𝓞 L) L)
    (F : GL (Fin 2) L → ℂ) (t : AdeleRing (𝓞 L) L)
    (hF : ∀ (p q : Lˣ) (s : L), F (diag2 p q * unipotentGL2 s) = Psi K L D σ φ x g (p, q) (ιA L s + τ (p, q) t))
    (hFfin : (Function.support F).Finite)
    (T : Finset (Lˣ × Lˣ)) (hT : ∀ pq, pq ∈ contrib K L D σ φ x g → ((pq.1 : Lˣ) : L) / ((pq.2 : Lˣ) : L) ∈ A → pq ∈ T)
    (hT' : ∀ pq ∈ T, ((pq.1 : Lˣ) : L) / ((pq.2 : Lˣ) : L) ∈ A) :
    ∑ᶠ γ ∈ BA A, F γ = ∑ pq ∈ T, Pd K L D σ φ x g pq (τ pq t) := by
  classical

  have h1' : ∑ᶠ γ ∈ BA A, F γ = ∑ᶠ c ∈ dom A, (F ∘ param (L := L)) c :=
    (finsum_mem_eq_of_bijOn param (param_bijOn A) fun c _ => rfl).symm
  have h1 : ∑ᶠ γ ∈ BA A, F γ = ∑ᶠ c, (dom A).indicator (F ∘ param (L := L)) c := by
    rw [h1', finsum_mem_def]

  have hsupp : (Function.support ((dom A).indicator (F ∘ param (L := L)))).Finite := by
    refine (hFfin.preimage (param_injective (L := L)).injOn).subset ?_
    intro c hc
    rw [Set.mem_preimage, Function.mem_support]
    rw [Function.mem_support] at hc
    intro h0
    exact hc (Set.indicator_apply_eq_zero.mpr fun _ => h0)

  have h2 : ∑ᶠ c, (dom A).indicator (F ∘ param (L := L)) c =
      ∑ᶠ (pq : Lˣ × Lˣ) (s : L), (dom A).indicator (F ∘ param) (pq, s) := finsum_curry _ hsupp

  have h3 : ∀ (pq : Lˣ × Lˣ) (s : L), (dom A).indicator (F ∘ param (L := L)) (pq, s) =
      if ((pq.1 : Lˣ) : L) / ((pq.2 : Lˣ) : L) ∈ A then Psi K L D σ φ x g pq (ιA L s + τ pq t) else 0 := by
    rintro ⟨p, q⟩ s
    by_cases hA : ((p : Lˣ) : L) / ((q : Lˣ) : L) ∈ A
    · rw [Set.indicator_of_mem (show ((p, q), s) ∈ dom A from hA), if_pos hA]
      exact hF p q s
    · rw [Set.indicator_of_notMem (show ((p, q), s) ∉ dom A from hA), if_neg hA]

  have h4 : (Function.support fun pq : Lˣ × Lˣ => ∑ᶠ s : L, (dom A).indicator (F ∘ param (L := L)) (pq, s)) ⊆ ↑T := by
    intro pq hpq
    by_contra hpqT
    refine hpq (finsum_eq_zero_of_forall_eq_zero fun s => ?_)
    rw [h3]
    by_cases hA : ((pq.1 : Lˣ) : L) / ((pq.2 : Lˣ) : L) ∈ A
    · rw [if_pos hA]
      by_cases hc : pq ∈ contrib K L D σ φ x g
      · exact absurd (hT pq hc hA) hpqT
      · exact Psi_eq_zero_of_not_mem_contrib K L D σ φ x g hc _
    · rw [if_neg hA]
  rw [h1, h2, finsum_eq_sum_of_support_subset _ h4]
  refine Finset.sum_congr rfl fun pq hpq => ?_
  unfold Pd
  refine finsum_congr fun s => ?_
  rw [h3, if_pos (hT' pq hpq)]

theorem continuous_τL (c : L) : Continuous fun v : AdeleRing (𝓞 L) L => θ K L D σ v - ιA L c * v :=
  (D.continuous_act σ).sub (continuous_const.mul continuous_id)

theorem main [FiniteDimensional K L] [IsGalois K L]
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (hA : ∀ ρ ∈ A, Algebra.norm K ρ ≠ 1)
    (hφc : Continuous φ) (hφs : HasCompactSupport φ) :
    Integrable (fun t : AdeleRing (𝓞 L) L => ∑ᶠ γ ∈ BA A,
        φ ((unipotentGL2 t * x)⁻¹ * globalPoints (𝓞 L) L γ * sigmaAdelicAct K L D σ (unipotentGL2 t * g))) (μB L) ∧
    Integrable (fun t : AdeleRing (𝓞 L) L => ∑ᶠ γ ∈ BA A,
        φ (x⁻¹ * globalPoints (𝓞 L) L γ * sigmaAdelicAct K L D σ (unipotentGL2 t * g))) (μB L) ∧
    ∫ t, ∑ᶠ γ ∈ BA A, φ ((unipotentGL2 t * x)⁻¹ * globalPoints (𝓞 L) L γ *
        sigmaAdelicAct K L D σ (unipotentGL2 t * g)) ∂(μB L) =
      ∫ t, ∑ᶠ γ ∈ BA A, φ (x⁻¹ * globalPoints (𝓞 L) L γ *
        sigmaAdelicAct K L D σ (unipotentGL2 t * g)) ∂(μB L) := by
  classical

  have hfin := finite_contrib K L D σ φ x g hφs
  set T : Finset (Lˣ × Lˣ) := (hfin.toFinset).filter fun pq => ((pq.1 : Lˣ) : L) / ((pq.2 : Lˣ) : L) ∈ A
    with hTdef
  have hT : ∀ pq, pq ∈ contrib K L D σ φ x g → ((pq.1 : Lˣ) : L) / ((pq.2 : Lˣ) : L) ∈ A → pq ∈ T := by
    intro pq h1 h2
    rw [hTdef, Finset.mem_filter, Set.Finite.mem_toFinset]
    exact ⟨h1, h2⟩
  have hT' : ∀ pq ∈ T, ((pq.1 : Lˣ) : L) / ((pq.2 : Lˣ) : L) ∈ A := by
    intro pq hpq
    rw [hTdef, Finset.mem_filter] at hpq
    exact hpq.2

  have hne : ∀ pq ∈ T, Algebra.norm K (((pq.1⁻¹ * pq.2 : Lˣ) : L)) ≠ 1 := by
    rintro ⟨p, q⟩ hpq h1
    apply hA _ (hT' _ hpq)
    have hprod : ((p : L) / (q : L)) * (((p⁻¹ * q : Lˣ) : L)) = 1 := by
      rw [Units.val_mul, Units.val_inv_eq_inv_val]
      field_simp
    have h2 := congrArg (Algebra.norm K) hprod
    rw [map_mul, map_one, h1, mul_one] at h2
    exact h2

  set τL : Lˣ × Lˣ → AdeleRing (𝓞 L) L → AdeleRing (𝓞 L) L :=
    fun pq v => θ K L D σ v - ιA L ((pq.1⁻¹ * pq.2 : Lˣ) : L) * v with hτL
  set τR : Lˣ × Lˣ → AdeleRing (𝓞 L) L → AdeleRing (𝓞 L) L := fun _ v => θ K L D σ v with hτR

  have hFfin : ∀ (y h : AdelicGL2 (𝓞 L) L),
      (Function.support fun γ : GL (Fin 2) L => φ (y⁻¹ * globalPoints (𝓞 L) L γ * h)).Finite := by
    intro y h
    have hC : IsCompact ((fun m => y * m * h⁻¹) '' tsupport φ) :=
      hφs.isCompact.image ((continuous_const.mul continuous_id).mul continuous_const)
    refine (finite_setOf_globalPoints_mem L hC).subset ?_
    intro γ hγ
    refine ⟨_, subset_tsupport φ hγ, ?_⟩
    simp only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one]

  have hfunL : (fun t : AdeleRing (𝓞 L) L => ∑ᶠ γ ∈ BA A,
      φ ((unipotentGL2 t * x)⁻¹ * globalPoints (𝓞 L) L γ * sigmaAdelicAct K L D σ (unipotentGL2 t * g))) =
      fun t => ∑ pq ∈ T, Pd K L D σ φ x g pq (τL pq t) := by
    funext t
    refine finsum_BA_eq K L D σ A φ x g τL _ t ?_ (hFfin _ _) T hT hT'
    intro p q s
    show φ _ = φ _
    rw [arg_eq_left]
  have hfunR : (fun t : AdeleRing (𝓞 L) L => ∑ᶠ γ ∈ BA A,
      φ (x⁻¹ * globalPoints (𝓞 L) L γ * sigmaAdelicAct K L D σ (unipotentGL2 t * g))) =
      fun t => ∑ pq ∈ T, Pd K L D σ φ x g pq (τR pq t) := by
    funext t
    refine finsum_BA_eq K L D σ A φ x g τR _ t ?_ (hFfin _ _) T hT hT'
    intro p q s
    show φ _ = φ _
    rw [arg_eq_right]

  have hcL : ∀ pq, Continuous fun t => Pd K L D σ φ x g pq (τL pq t) := fun pq =>
    (continuous_Pd K L D σ φ x g hφc hφs pq).comp (continuous_τL K L D σ _)
  have hcR : ∀ pq, Continuous fun t => Pd K L D σ φ x g pq (τR pq t) := fun pq =>
    (continuous_Pd K L D σ φ x g hφc hφs pq).comp (D.continuous_act σ)
  have hiL : ∀ pq, Integrable (fun t => Pd K L D σ φ x g pq (τL pq t)) (μB L) := fun pq =>
    integrable_μB_of_continuous L (hcL pq)
  have hiR : ∀ pq, Integrable (fun t => Pd K L D σ φ x g pq (τR pq t)) (μB L) := fun pq =>
    integrable_μB_of_continuous L (hcR pq)
  refine ⟨?_, ?_, ?_⟩
  · rw [hfunL]; exact integrable_finsetSum _ fun pq _ => hiL pq
  · rw [hfunR]; exact integrable_finsetSum _ fun pq _ => hiR pq
  rw [hfunL, hfunR, integral_finsetSum _ fun pq _ => hiL pq, integral_finsetSum _ fun pq _ => hiR pq]
  refine Finset.sum_congr rfl fun pq hpq => ?_

  have hper : ∀ (k : L) (u : AdeleRing (𝓞 L) L), Pd K L D σ φ x g pq (ιA L k + u) = Pd K L D σ φ x g pq u :=
    Pd_periodic K L D σ φ x g pq
  have hR : ∫ t, Pd K L D σ φ x g pq (τR pq t) ∂(μB L) = ∫ t, Pd K L D σ φ x g pq t ∂(μB L) :=
    integral_μB_comp_eq L (thetaEquiv K L D σ) (measurePreserving_thetaEquiv K L D σ)
      (thetaEquiv_mem_iff K L D σ) _ hper
  obtain ⟨eq, heq, -, hmp⟩ :=
    M4aHerbrand.IdeleGaloisDescent.exists_continuousAddEquiv_measurePreserving_act_sub_algebraMap_mul_of_norm_ne_one
      D hgen (((pq.1⁻¹ * pq.2 : Lˣ) : L)) (hne pq hpq) (μA L)
  have hτe : (fun t => Pd K L D σ φ x g pq (τL pq t)) = fun t => Pd K L D σ φ x g pq (eq t) := by
    funext t
    rw [heq t]
  have hL : ∫ t, Pd K L D σ φ x g pq (τL pq t) ∂(μB L) = ∫ t, Pd K L D σ φ x g pq t ∂(μB L) := by
    rw [hτe]
    exact integral_μB_comp_eq L eq hmp
      (fun v => by rw [heq v]; exact sub_mem_iff K L D σ hgen _ (hne pq hpq) v) _ hper
  rw [hL, hR]

end Main

end R4UnipSubst
p2m_reactivate "P2MW.S_AutomorphicForm_integrable_and_integral_finsum_borel_div_mem_inv_unipotentGL2_mul_eq_integral_finsum_of_norm_ne_one.R4UnipSubst"

end
p2m_reactivate "P2MW.S_AutomorphicForm_integrable_and_integral_finsum_borel_div_mem_inv_unipotentGL2_mul_eq_integral_finsum_of_norm_ne_one.R4UnipSubst"

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicBox in
theorem solution
    (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (A : Set L) (hA : ∀ ρ ∈ A, Algebra.norm K ρ ≠ 1)
    (φ : AutomorphicForm.AdelicGL2 (𝓞 L) L → ℂ) (hφc : Continuous φ) (hφs : HasCompactSupport φ)
    (x g : AutomorphicForm.AdelicGL2 (𝓞 L) L) :
    Integrable (fun t : AdeleRing (𝓞 L) L =>
        ∑ᶠ γ ∈ {γ : Matrix.GeneralLinearGroup (Fin 2) L |
            (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
              (γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1 ∈ A},
          φ ((AutomorphicForm.unipotentGL2 t * x)⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L γ *
            AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.unipotentGL2 t * g)))
      (@ProbabilityTheory.cond _ (adeleBorel (𝓞 L) L) (adelicAddHaar (𝓞 L) L) (adelicBox L)) ∧
    Integrable (fun t : AdeleRing (𝓞 L) L =>
        ∑ᶠ γ ∈ {γ : Matrix.GeneralLinearGroup (Fin 2) L |
            (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
              (γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1 ∈ A},
          φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L γ *
            AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.unipotentGL2 t * g)))
      (@ProbabilityTheory.cond _ (adeleBorel (𝓞 L) L) (adelicAddHaar (𝓞 L) L) (adelicBox L)) ∧
    ∫ t, ∑ᶠ γ ∈ {γ : Matrix.GeneralLinearGroup (Fin 2) L |
            (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
              (γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1 ∈ A},
          φ ((AutomorphicForm.unipotentGL2 t * x)⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L γ *
            AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.unipotentGL2 t * g))
        ∂(@ProbabilityTheory.cond _ (adeleBorel (𝓞 L) L) (adelicAddHaar (𝓞 L) L) (adelicBox L)) =
      ∫ t, ∑ᶠ γ ∈ {γ : Matrix.GeneralLinearGroup (Fin 2) L |
            (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
              (γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1 ∈ A},
          φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L γ *
            AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.unipotentGL2 t * g))
        ∂(@ProbabilityTheory.cond _ (adeleBorel (𝓞 L) L) (adelicAddHaar (𝓞 L) L) (adelicBox L)) :=
  R4UnipSubst.main K L D σ A φ x g hgen hA hφc hφs

end S_AutomorphicForm_integrable_and_integral_finsum_borel_div_mem_inv_unipotentGL2_mul_eq_integral_finsum_of_norm_ne_one
end P2MW
export P2MW.S_AutomorphicForm_integrable_and_integral_finsum_borel_div_mem_inv_unipotentGL2_mul_eq_integral_finsum_of_norm_ne_one (solution)
