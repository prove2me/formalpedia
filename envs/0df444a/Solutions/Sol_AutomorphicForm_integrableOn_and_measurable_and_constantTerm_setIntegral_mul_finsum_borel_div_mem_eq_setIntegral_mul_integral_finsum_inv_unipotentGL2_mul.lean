-- Prove2me | solution 1 for AutomorphicForm.integrableOn_and_measurable_and_constantTerm_setIntegral_mul_finsum_borel_div_mem_eq_setIntegral_mul_integral_finsum_inv_unipotentGL2_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/536b92c8-0d43-5ae6-9cd4-3e86ace32858

import Mathlib
import Definitions.Def_AutomorphicForm_SigmaAdelicAction
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_AdelicHaar
import Theorems.Thm_NumberField_AdeleRing_finite_setOf_algebraMap_mem_of_isCompact
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology_generalLinearGroup_finTwo
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_integrableOn_and_measurable_and_constantTerm_setIntegral_mul_finsum_borel_div_mem_eq_setIntegral_mul_integral_finsum_inv_unipotentGL2_mul
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

noncomputable section

namespace R4FoldCT

set_option maxHeartbeats 1600000

open MeasureTheory MeasureTheory.Measure NumberField Filter Function Set AutomorphicForm
open scoped ENNReal NNReal Topology Pointwise

section Instances

variable (L : Type) [Field L] [NumberField L]

theorem countable_L : Countable L :=
  (Module.Free.chooseBasis ℚ L).equivFun.toEquiv.countable_iff.2 inferInstance

theorem countable_units : Countable Lˣ := by
  haveI : Countable L := countable_L L
  exact Function.Injective.countable (f := (Units.val : Lˣ → L)) Units.val_injective

theorem locallyCompactSpace_ideles : LocallyCompactSpace (AdeleRing (𝓞 L) L)ˣ := by
  haveI : LocallyCompactSpace (AdeleRing (𝓞 L) L)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  exact Units.isClosedEmbedding_embedProduct.locallyCompactSpace

theorem secondCountableTopology_ideles : SecondCountableTopology (AdeleRing (𝓞 L) L)ˣ := by
  haveI : SecondCountableTopology (AdeleRing (𝓞 L) L) := NumberField.AdeleRing.secondCountableTopology L
  haveI : SecondCountableTopology (AdeleRing (𝓞 L) L)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isClosedEmbedding.isEmbedding.secondCountableTopology
  exact Units.isClosedEmbedding_embedProduct.isEmbedding.secondCountableTopology

end Instances

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

theorem diag2_inv (p q : Rˣ) : (diag2 p q)⁻¹ = diag2 p⁻¹ q⁻¹ := by
  refine inv_eq_of_mul_eq_one_right ?_
  apply Units.ext
  rw [Units.val_mul, diag2_val, diag2_val, Units.val_one]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem diag2_mul_diag2 (p q p' q' : Rˣ) : diag2 p q * diag2 p' q' = diag2 (p * p') (q * q') := by
  apply Units.ext
  rw [Units.val_mul, diag2_val, diag2_val, diag2_val]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem scalar_eq_diag2 (z : Rˣ) : Matrix.GeneralLinearGroup.scalar (Fin 2) z = diag2 z z := by
  apply Units.ext
  rw [diag2_val]
  ext i j; fin_cases i <;> fin_cases j <;> simp

theorem unipotentGL2_neg (t : R) : unipotentGL2 (-t) = (unipotentGL2 t)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← unipotentGL2_add, neg_add_cancel, unipotentGL2_zero]

theorem val_unipotent_mul_diag2 (a b : Rˣ) (t : R) :
    ((unipotentGL2 t * diag2 a b : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) = !![(a : R), t * b; 0, (b : R)] := by
  rw [Units.val_mul, diag2_val, unipotentGL2_coe]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem inv_unipotent_mul_diag2_apply_one_one (a b : Rˣ) (t : R) :
    (((unipotentGL2 t * diag2 a b)⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) 1 1 = ((b⁻¹ : Rˣ) : R) := by
  rw [mul_inv_rev, diag2_inv, ← unipotentGL2_neg, Units.val_mul, diag2_val, unipotentGL2_coe]
  simp [Matrix.mul_apply, Fin.sum_univ_two]

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

theorem continuous_diag2_self : Continuous fun z : Rˣ => (diag2 z z : GL (Fin 2) R) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · show Continuous fun c : Rˣ => !![(c : R), 0; 0, (c : R)]
    exact continuous_matrix_two (by simpa using Units.continuous_val) (by simpa using continuous_const)
      (by simpa using continuous_const) (by simpa using Units.continuous_val)
  · show Continuous fun c : Rˣ => !![((c⁻¹ : Rˣ) : R), 0; 0, ((c⁻¹ : Rˣ) : R)]
    exact continuous_matrix_two (by simpa using Units.continuous_coe_inv) (by simpa using continuous_const)
      (by simpa using continuous_const) (by simpa using Units.continuous_coe_inv)

theorem continuous_val_apply (i j : Fin 2) :
    Continuous fun g : GL (Fin 2) R => (g : Matrix (Fin 2) (Fin 2) R) i j :=
  Units.continuous_val.matrix_elem i j

theorem continuous_val_inv_apply (i j : Fin 2) :
    Continuous fun g : GL (Fin 2) R => ((g⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) i j :=
  Units.continuous_coe_inv.matrix_elem i j

end GL2

section FieldGL2

variable {L : Type} [Field L] (A : Set L)

theorem det_ne_zero_entries (d : GL (Fin 2) L) (h10 : (d : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) :
    (d : Matrix (Fin 2) (Fin 2) L) 0 0 ≠ 0 ∧ (d : Matrix (Fin 2) (Fin 2) L) 1 1 ≠ 0 := by
  have hdet : (d : Matrix (Fin 2) (Fin 2) L).det ≠ 0 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply]
    exact (Matrix.GeneralLinearGroup.det d).ne_zero
  rw [Matrix.det_fin_two, h10, mul_zero, sub_zero] at hdet
  exact ⟨left_ne_zero_of_mul hdet, right_ne_zero_of_mul hdet⟩

def BA : Set (GL (Fin 2) L) :=
  {γ : GL (Fin 2) L | (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
    (γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1 ∈ A}

def dom : Set ((Lˣ × L) × Lˣ) := {c | ((c.1.1 : Lˣ) : L) ∈ A}

def E (c : (Lˣ × L) × Lˣ) : GL (Fin 2) L := unipotentGL2 c.1.2 * diag2 (c.1.1 * c.2) c.2

theorem val_E (ρ q : Lˣ) (s : L) :
    ((E ((ρ, s), q) : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) = !![(ρ : L) * q, s * q; 0, (q : L)] := by
  show ((unipotentGL2 s * diag2 (ρ * q) q : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) = _
  rw [val_unipotent_mul_diag2, Units.val_mul]

theorem E_injective : Function.Injective (E (L := L)) := by
  rintro ⟨⟨ρ, s⟩, q⟩ ⟨⟨ρ', s'⟩, q'⟩ h
  have hv := congrArg (fun γ : GL (Fin 2) L => (γ : Matrix (Fin 2) (Fin 2) L)) h
  simp only [val_E] at hv
  have h00 := congrFun (congrFun hv 0) 0
  have h01 := congrFun (congrFun hv 0) 1
  have h11 := congrFun (congrFun hv 1) 1
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Matrix.empty_val'] at h00 h01 h11
  have hq : q = q' := Units.ext h11
  subst hq
  have hρ : ρ = ρ' := Units.ext (mul_right_cancel₀ q.ne_zero h00)
  have hs : s = s' := mul_right_cancel₀ q.ne_zero h01
  subst hρ; subst hs
  rfl

theorem E_bijOn : Set.BijOn (E (L := L)) (dom A) (BA A) := by
  refine ⟨?_, E_injective.injOn, ?_⟩
  · rintro ⟨⟨ρ, s⟩, q⟩ hc
    refine ⟨?_, ?_⟩
    · show ((E ((ρ, s), q) : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 0 = 0
      rw [val_E]; simp
    · show ((E ((ρ, s), q) : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 0 0 /
          ((E ((ρ, s), q) : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 1 ∈ A
      rw [val_E]
      simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one, Matrix.empty_val']
      rw [mul_div_cancel_right₀ _ q.ne_zero]
      exact hc
  · rintro γ ⟨h10, hA⟩
    obtain ⟨h0, h1⟩ := det_ne_zero_entries γ h10
    refine ⟨((Units.mk0 _ h0 * (Units.mk0 _ h1)⁻¹, (γ : Matrix (Fin 2) (Fin 2) L) 0 1 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1),
      Units.mk0 _ h1), ?_, ?_⟩
    · show ((Units.mk0 _ h0 * (Units.mk0 _ h1)⁻¹ : Lˣ) : L) ∈ A
      rw [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0, Units.val_mk0, ← div_eq_mul_inv]
      exact hA
    · refine Matrix.GeneralLinearGroup.ext fun i j => ?_
      rw [val_E]
      fin_cases i <;> fin_cases j
      · simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0, Fin.zero_eta, Fin.isValue,
          Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one]
        rw [inv_mul_cancel_right₀ h1]
      · simp only [Units.val_mk0, Fin.zero_eta, Fin.isValue, Fin.mk_one, Matrix.of_apply, Matrix.cons_val',
          Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_zero]
        rw [div_mul_cancel₀ _ h1]
      · simp [h10]
      · simp

end FieldGL2

section Adelic

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
variable (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)

abbrev princ : Lˣ →* (AdeleRing (𝓞 L) L)ˣ :=
  Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)

abbrev ιA : L →+* AdeleRing (𝓞 L) L := algebraMap L (AdeleRing (𝓞 L) L)

abbrev θ : AdeleRing (𝓞 L) L ≃+* AdeleRing (𝓞 L) L := (D.act σ : RingAut (AdeleRing (𝓞 L) L))

abbrev actU : (AdeleRing (𝓞 L) L)ˣ →* (AdeleRing (𝓞 L) L)ˣ :=
  Units.map ((D.act σ : RingAut (AdeleRing (𝓞 L) L)).toRingHom : AdeleRing (𝓞 L) L →* _)

theorem centralScalar_comm (z : (AdeleRing (𝓞 L) L)ˣ) (g : AdelicGL2 (𝓞 L) L) :
    centralScalar (𝓞 L) L z * g = g * centralScalar (𝓞 L) L z := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul]
  exact (Matrix.scalar_commute (n := Fin 2) (z : AdeleRing (𝓞 L) L) (fun r' => Commute.all _ r') _).eq

theorem centralScalar_eq_diag2 (z : (AdeleRing (𝓞 L) L)ˣ) : centralScalar (𝓞 L) L z = diag2 z z :=
  scalar_eq_diag2 z

theorem continuous_centralScalar :
    Continuous (centralScalar (𝓞 L) L : (AdeleRing (𝓞 L) L)ˣ → AdelicGL2 (𝓞 L) L) := by
  have : (centralScalar (𝓞 L) L : (AdeleRing (𝓞 L) L)ˣ → AdelicGL2 (𝓞 L) L) = fun z => diag2 z z :=
    funext fun z => centralScalar_eq_diag2 L z
  rw [this]
  exact continuous_diag2_self

theorem sigmaAdelicAct_apply (g : AdelicGL2 (𝓞 L) L) (i j : Fin 2) :
    ((sigmaAdelicAct K L D σ g : AdelicGL2 (𝓞 L) L) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i j =
      θ K L D σ ((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i j) := rfl

theorem sigmaAdelicAct_diag2 (P Q : (AdeleRing (𝓞 L) L)ˣ) :
    sigmaAdelicAct K L D σ (diag2 P Q) = diag2 (actU K L D σ P) (actU K L D σ Q) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [sigmaAdelicAct_apply, diag2_val, diag2_val]
  fin_cases i <;> fin_cases j <;> simp

theorem sigmaAdelicAct_centralScalar (z : (AdeleRing (𝓞 L) L)ˣ) :
    sigmaAdelicAct K L D σ (centralScalar (𝓞 L) L z) = centralScalar (𝓞 L) L (actU K L D σ z) := by
  rw [centralScalar_eq_diag2, centralScalar_eq_diag2, sigmaAdelicAct_diag2]

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

theorem actU_princ (v : Lˣ) : actU K L D σ (princ L v) = princ L (Units.map (σ : L →* L) v) := by
  refine Units.ext ?_
  exact D.compat σ (v : L)

theorem princ_mul_actU (q : Lˣ) (z : (AdeleRing (𝓞 L) L)ˣ) :
    princ L q * actU K L D σ z = actU K L D σ (princ L (Units.map (σ.symm : L →* L) q) * z) := by
  rw [map_mul, actU_princ]
  congr 2
  refine Units.ext ?_
  show (q : L) = σ (σ.symm (q : L))
  rw [AlgEquiv.apply_symm_apply]

theorem continuous_actU (τ : L ≃ₐ[K] L) : Continuous (actU K L D τ) :=
  Continuous.units_map _ (D.continuous_act τ)

theorem actU_inv_apply (w : (AdeleRing (𝓞 L) L)ˣ) : actU K L D σ⁻¹ (actU K L D σ w) = w := by
  refine Units.ext ?_
  show (D.act σ⁻¹ : RingAut (AdeleRing (𝓞 L) L)) ((D.act σ : RingAut (AdeleRing (𝓞 L) L)) (w : AdeleRing (𝓞 L) L)) = w
  rw [map_inv]
  exact RingEquiv.symm_apply_apply _ _

def redArg (r : Lˣ × L) (w : (AdeleRing (𝓞 L) L)ˣ) : AdelicGL2 (𝓞 L) L :=
  unipotentGL2 (ιA L r.2) * diag2 (princ L r.1 * w) w

theorem globalPoints_E_mul (ρ q : Lˣ) (s : L) (z : (AdeleRing (𝓞 L) L)ˣ) (y : AdelicGL2 (𝓞 L) L) :
    globalPoints (𝓞 L) L (E ((ρ, s), q)) * sigmaAdelicAct K L D σ (centralScalar (𝓞 L) L z * y) =
      redArg L (ρ, s) (princ L q * actU K L D σ z) * sigmaAdelicAct K L D σ y := by
  show globalPoints (𝓞 L) L (unipotentGL2 s * diag2 (ρ * q) q) * _ = unipotentGL2 (ιA L s) * _ * _
  rw [map_mul (globalPoints (𝓞 L) L), globalPoints_unipotent, globalPoints_diag2, map_mul (sigmaAdelicAct K L D σ),
    sigmaAdelicAct_centralScalar, centralScalar_eq_diag2, map_mul (princ L)]
  simp only [mul_assoc]
  rw [← mul_assoc (diag2 _ _) (diag2 _ _), diag2_mul_diag2, mul_assoc (princ L ρ)]

end Adelic

section Support

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
variable (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
  (φ : AdelicGL2 (𝓞 L) L → ℂ)

theorem finite_setOf_ιA_mem {C : Set (AdeleRing (𝓞 L) L)} (hC : IsCompact C) : {s : L | ιA L s ∈ C}.Finite :=
  NumberField.AdeleRing.finite_setOf_algebraMap_mem_of_isCompact L hC

theorem finite_setOf_ιA_units_mem {C : Set (AdeleRing (𝓞 L) L)} (hC : IsCompact C) :
    {u : Lˣ | ιA L (u : L) ∈ C}.Finite :=
  (finite_setOf_ιA_mem L hC).preimage (f := fun u : Lˣ => (u : L)) Units.val_injective.injOn

theorem finite_setOf_princ_mem {C : Set (AdeleRing (𝓞 L) L)ˣ} (hC : IsCompact C) :
    {u : Lˣ | princ L u ∈ C}.Finite := by
  have h := NumberField.AdeleRing.finite_setOf_algebraMap_mem_of_isCompact L (hC.image Units.continuous_val)
  refine (h.preimage (f := fun u : Lˣ => (u : L)) (Units.val_injective.injOn)).subset ?_
  intro u hu
  exact ⟨princ L u, hu, rfl⟩

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

def F (x y : AdelicGL2 (𝓞 L) L) (r : Lˣ × L) (w : (AdeleRing (𝓞 L) L)ˣ) : ℂ :=
  φ (x⁻¹ * redArg L r w * sigmaAdelicAct K L D σ y)

def CP (P : Set (AdelicGL2 (𝓞 L) L × AdelicGL2 (𝓞 L) L)) : Set (AdelicGL2 (𝓞 L) L) :=
  (fun p : (AdelicGL2 (𝓞 L) L × AdelicGL2 (𝓞 L) L) × AdelicGL2 (𝓞 L) L =>
    p.1.1 * p.2 * (sigmaAdelicAct K L D σ p.1.2)⁻¹) '' (P ×ˢ tsupport φ)

theorem isCompact_CP (hφs : HasCompactSupport φ) {P : Set (AdelicGL2 (𝓞 L) L × AdelicGL2 (𝓞 L) L)}
    (hP : IsCompact P) : IsCompact (CP K L D σ φ P) :=
  (hP.prod hφs.isCompact).image ((continuous_fst.fst.mul continuous_snd).mul
    ((continuous_sigmaAdelicAct K L D σ).comp continuous_fst.snd).inv)

theorem redArg_mem_CP {P : Set (AdelicGL2 (𝓞 L) L × AdelicGL2 (𝓞 L) L)} {x y : AdelicGL2 (𝓞 L) L}
    (hxy : (x, y) ∈ P) {r : Lˣ × L} {w : (AdeleRing (𝓞 L) L)ˣ} (h : F K L D σ φ x y r w ≠ 0) :
    redArg L r w ∈ CP K L D σ φ P := by
  refine ⟨((x, y), x⁻¹ * redArg L r w * sigmaAdelicAct K L D σ y),
    Set.mk_mem_prod hxy (subset_tsupport φ (Function.mem_support.mpr h)), ?_⟩
  simp only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one]

def read00 (u : AdelicGL2 (𝓞 L) L) : AdeleRing (𝓞 L) L :=
  (u : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 0 *
    ((u⁻¹ : AdelicGL2 (𝓞 L) L) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 1 1

def read01 (u : AdelicGL2 (𝓞 L) L) : AdeleRing (𝓞 L) L :=
  (u : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 1 *
    ((u⁻¹ : AdelicGL2 (𝓞 L) L) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 1 1

def readW (u : AdelicGL2 (𝓞 L) L) : AdeleRing (𝓞 L) L × (AdeleRing (𝓞 L) L)ᵐᵒᵖ :=
  ((u : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 1 1,
    MulOpposite.op (((u⁻¹ : AdelicGL2 (𝓞 L) L) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 1 1))

theorem continuous_read00 : Continuous (read00 L) := (continuous_val_apply 0 0).mul (continuous_val_inv_apply 1 1)

theorem continuous_read01 : Continuous (read01 L) := (continuous_val_apply 0 1).mul (continuous_val_inv_apply 1 1)

theorem continuous_readW : Continuous (readW L) :=
  (continuous_val_apply 1 1).prodMk (MulOpposite.continuous_op.comp (continuous_val_inv_apply 1 1))

theorem read00_redArg (r : Lˣ × L) (w : (AdeleRing (𝓞 L) L)ˣ) : read00 L (redArg L r w) = ιA L (r.1 : L) := by
  unfold read00 redArg
  rw [val_unipotent_mul_diag2, inv_unipotent_mul_diag2_apply_one_one]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, Units.val_mul,
    Units.coe_map, MonoidHom.coe_coe]
  rw [mul_assoc, Units.mul_inv, mul_one]

theorem read01_redArg (r : Lˣ × L) (w : (AdeleRing (𝓞 L) L)ˣ) : read01 L (redArg L r w) = ιA L r.2 := by
  unfold read01 redArg
  rw [val_unipotent_mul_diag2, inv_unipotent_mul_diag2_apply_one_one]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_zero]
  rw [mul_assoc, Units.mul_inv, mul_one]

theorem readW_redArg (r : Lˣ × L) (w : (AdeleRing (𝓞 L) L)ˣ) : readW L (redArg L r w) = Units.embedProduct _ w := by
  unfold readW redArg
  rw [val_unipotent_mul_diag2, inv_unipotent_mul_diag2_apply_one_one]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one, Matrix.cons_val_fin_one, Units.embedProduct_apply]

def RP (P : Set (AdelicGL2 (𝓞 L) L × AdelicGL2 (𝓞 L) L)) : Set (Lˣ × L) :=
  {r | ∃ x y, (x, y) ∈ P ∧ ∃ w, F K L D σ φ x y r w ≠ 0}

theorem finite_RP (hφs : HasCompactSupport φ) {P : Set (AdelicGL2 (𝓞 L) L × AdelicGL2 (𝓞 L) L)}
    (hP : IsCompact P) : (RP K L D σ φ P).Finite := by
  have hC := isCompact_CP K L D σ φ hφs hP
  have h0 : {ρ : Lˣ | ιA L (ρ : L) ∈ read00 L '' CP K L D σ φ P}.Finite :=
    finite_setOf_ιA_units_mem L (hC.image (continuous_read00 L))
  have h1 : {s : L | ιA L s ∈ read01 L '' CP K L D σ φ P}.Finite :=
    finite_setOf_ιA_mem L (hC.image (continuous_read01 L))
  refine (h0.prod h1).subset ?_
  rintro ⟨ρ, s⟩ ⟨x, y, hxy, w, hw⟩
  have hm := redArg_mem_CP K L D σ φ hxy hw
  exact ⟨⟨_, hm, read00_redArg L _ _⟩, ⟨_, hm, read01_redArg L _ _⟩⟩

theorem F_eq_zero_of_not_mem_RP {P : Set (AdelicGL2 (𝓞 L) L × AdelicGL2 (𝓞 L) L)} {x y : AdelicGL2 (𝓞 L) L}
    (hxy : (x, y) ∈ P) {r : Lˣ × L} (hr : r ∉ RP K L D σ φ P) (w : (AdeleRing (𝓞 L) L)ˣ) :
    F K L D σ φ x y r w = 0 := by
  by_contra h
  exact hr ⟨x, y, hxy, w, h⟩

def WP (P : Set (AdelicGL2 (𝓞 L) L × AdelicGL2 (𝓞 L) L)) : Set (AdeleRing (𝓞 L) L)ˣ :=
  Units.embedProduct _ ⁻¹' (readW L '' CP K L D σ φ P)

theorem isCompact_WP (hφs : HasCompactSupport φ) {P : Set (AdelicGL2 (𝓞 L) L × AdelicGL2 (𝓞 L) L)}
    (hP : IsCompact P) : IsCompact (WP K L D σ φ P) :=
  Units.isClosedEmbedding_embedProduct.isCompact_preimage ((isCompact_CP K L D σ φ hφs hP).image (continuous_readW L))

theorem mem_WP_of_F_ne_zero {P : Set (AdelicGL2 (𝓞 L) L × AdelicGL2 (𝓞 L) L)} {x y : AdelicGL2 (𝓞 L) L}
    (hxy : (x, y) ∈ P) {r : Lˣ × L} {w : (AdeleRing (𝓞 L) L)ˣ} (h : F K L D σ φ x y r w ≠ 0) :
    w ∈ WP K L D σ φ P :=
  ⟨_, redArg_mem_CP K L D σ φ hxy h, readW_redArg L r w⟩

def F' (x y : AdelicGL2 (𝓞 L) L) (r : Lˣ × L) (w : (AdeleRing (𝓞 L) L)ˣ) : ℂ :=
  F K L D σ φ x y r (actU K L D σ w)

def WP' (P : Set (AdelicGL2 (𝓞 L) L × AdelicGL2 (𝓞 L) L)) : Set (AdeleRing (𝓞 L) L)ˣ :=
  actU K L D σ⁻¹ '' WP K L D σ φ P

theorem isCompact_WP' (hφs : HasCompactSupport φ) {P : Set (AdelicGL2 (𝓞 L) L × AdelicGL2 (𝓞 L) L)}
    (hP : IsCompact P) : IsCompact (WP' K L D σ φ P) :=
  (isCompact_WP K L D σ φ hφs hP).image (continuous_actU K L D σ⁻¹)

theorem mem_WP'_of_F'_ne_zero {P : Set (AdelicGL2 (𝓞 L) L × AdelicGL2 (𝓞 L) L)} {x y : AdelicGL2 (𝓞 L) L}
    (hxy : (x, y) ∈ P) {r : Lˣ × L} {w : (AdeleRing (𝓞 L) L)ˣ} (h : F' K L D σ φ x y r w ≠ 0) :
    w ∈ WP' K L D σ φ P :=
  ⟨actU K L D σ w, mem_WP_of_F_ne_zero K L D σ φ hxy h, actU_inv_apply K L D σ w⟩

theorem F'_eq_zero_of_not_mem_RP {P : Set (AdelicGL2 (𝓞 L) L × AdelicGL2 (𝓞 L) L)} {x y : AdelicGL2 (𝓞 L) L}
    (hxy : (x, y) ∈ P) {r : Lˣ × L} (hr : r ∉ RP K L D σ φ P) (w : (AdeleRing (𝓞 L) L)ˣ) :
    F' K L D σ φ x y r w = 0 :=
  F_eq_zero_of_not_mem_RP K L D σ φ hxy hr _

theorem finite_setOf_princ_mul_mem {W : Set (AdeleRing (𝓞 L) L)ˣ} (hW : IsCompact W)
    {N : Set (AdeleRing (𝓞 L) L)ˣ} (hN : IsCompact N) : {u : Lˣ | ∃ z ∈ N, princ L u * z ∈ W}.Finite := by
  have hC : IsCompact ((fun p : (AdeleRing (𝓞 L) L)ˣ × (AdeleRing (𝓞 L) L)ˣ => p.1 * p.2⁻¹) '' (W ×ˢ N)) :=
    (hW.prod hN).image (continuous_fst.mul continuous_snd.inv)
  refine (finite_setOf_princ_mem L hC).subset ?_
  rintro u ⟨z, hz, hu⟩
  exact ⟨(princ L u * z, z), Set.mk_mem_prod hu hz, by simp only [mul_inv_cancel_right]⟩

end Support

section Decompose

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
variable (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
  (A : Set L) (φ : AdelicGL2 (𝓞 L) L → ℂ)

def unitsPerm : Lˣ ≃ Lˣ where
  toFun := Units.map (σ.symm : L →* L)
  invFun := Units.map (σ : L →* L)
  left_inv u := Units.ext (σ.apply_symm_apply (u : L))
  right_inv u := Units.ext (σ.symm_apply_apply (u : L))

theorem finsum_BA_eq (hφs : HasCompactSupport φ)
    {P : Set (AdelicGL2 (𝓞 L) L × AdelicGL2 (𝓞 L) L)} {x y : AdelicGL2 (𝓞 L) L} (hxy : (x, y) ∈ P)
    (T : Finset (Lˣ × L)) (hT : ∀ r, r ∈ RP K L D σ φ P → ((r.1 : Lˣ) : L) ∈ A → r ∈ T)
    (hT' : ∀ r ∈ T, ((r.1 : Lˣ) : L) ∈ A) (z : (AdeleRing (𝓞 L) L)ˣ) :
    ∑ᶠ γ ∈ BA A, φ (x⁻¹ * globalPoints (𝓞 L) L γ * sigmaAdelicAct K L D σ (centralScalar (𝓞 L) L z * y)) =
      ∑ r ∈ T, ∑ᶠ q : Lˣ, F' K L D σ φ x y r (princ L q * z) := by
  classical
  set G : GL (Fin 2) L → ℂ := fun γ =>
    φ (x⁻¹ * globalPoints (𝓞 L) L γ * sigmaAdelicAct K L D σ (centralScalar (𝓞 L) L z * y)) with hG

  have hGE : ∀ (ρ : Lˣ) (s : L) (q : Lˣ), G (E ((ρ, s), q)) = F K L D σ φ x y (ρ, s) (princ L q * actU K L D σ z) := by
    intro ρ s q
    show φ _ = φ _
    rw [mul_assoc, globalPoints_E_mul, ← mul_assoc]

  have h1 : ∑ᶠ γ ∈ BA A, G γ = ∑ᶠ c, (dom A).indicator (G ∘ E (L := L)) c := by
    rw [← finsum_mem_def]
    exact (finsum_mem_eq_of_bijOn E (E_bijOn A) fun c _ => rfl).symm

  have hGfin : (Function.support G).Finite := by
    have hC : IsCompact ((fun m => x * m * (sigmaAdelicAct K L D σ (centralScalar (𝓞 L) L z * y))⁻¹) '' tsupport φ) :=
      hφs.isCompact.image ((continuous_const.mul continuous_id).mul continuous_const)
    refine (finite_setOf_globalPoints_mem L hC).subset ?_
    intro γ hγ
    refine ⟨_, subset_tsupport φ hγ, ?_⟩
    simp only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one]
  have hsupp : (Function.support ((dom A).indicator (G ∘ E (L := L)))).Finite := by
    refine (hGfin.preimage (E_injective (L := L)).injOn).subset ?_
    intro c hc
    rw [Set.mem_preimage, Function.mem_support]
    rw [Function.mem_support] at hc
    intro h0
    exact hc (Set.indicator_apply_eq_zero.mpr fun _ => h0)

  have h2 : ∑ᶠ c, (dom A).indicator (G ∘ E (L := L)) c =
      ∑ᶠ (r : Lˣ × L) (q : Lˣ), (dom A).indicator (G ∘ E) (r, q) := finsum_curry _ hsupp

  have h3 : ∀ (r : Lˣ × L) (q : Lˣ), (dom A).indicator (G ∘ E (L := L)) (r, q) =
      if ((r.1 : Lˣ) : L) ∈ A then F K L D σ φ x y r (princ L q * actU K L D σ z) else 0 := by
    rintro ⟨ρ, s⟩ q
    by_cases hA : ((ρ : Lˣ) : L) ∈ A
    · rw [Set.indicator_of_mem (show ((ρ, s), q) ∈ dom A from hA), if_pos hA]
      exact hGE ρ s q
    · rw [Set.indicator_of_notMem (show ((ρ, s), q) ∉ dom A from hA), if_neg hA]

  have h4 : (Function.support fun r : Lˣ × L => ∑ᶠ q : Lˣ, (dom A).indicator (G ∘ E (L := L)) (r, q)) ⊆ ↑T := by
    intro r hr
    by_contra hrT
    refine hr (finsum_eq_zero_of_forall_eq_zero fun q => ?_)
    rw [h3]
    by_cases hA : ((r.1 : Lˣ) : L) ∈ A
    · rw [if_pos hA]
      by_cases hc : r ∈ RP K L D σ φ P
      · exact absurd (hT r hc hA) hrT
      · exact F_eq_zero_of_not_mem_RP K L D σ φ hxy hc _
    · rw [if_neg hA]
  rw [h1, h2, finsum_eq_sum_of_support_subset _ h4]
  refine Finset.sum_congr rfl fun r hr => ?_

  rw [← finsum_comp_equiv (unitsPerm K L σ) (f := fun q => F' K L D σ φ x y r (princ L q * z))]
  refine finsum_congr fun q => ?_
  rw [h3, if_pos (hT' r hr)]
  unfold F'
  rw [princ_mul_actU]
  rfl

end Decompose

section Continuity

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
variable (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
  (A : Set L) (φ : AdelicGL2 (𝓞 L) L → ℂ)

def kfun (p : (AdelicGL2 (𝓞 L) L × AdelicGL2 (𝓞 L) L) × (AdeleRing (𝓞 L) L)ˣ) : ℂ :=
  ∑ᶠ γ ∈ BA A, φ (p.1.1⁻¹ * globalPoints (𝓞 L) L γ * sigmaAdelicAct K L D σ (centralScalar (𝓞 L) L p.2 * p.1.2))

theorem continuous_term (hφc : Continuous φ) (γ : GL (Fin 2) L) :
    Continuous fun p : (AdelicGL2 (𝓞 L) L × AdelicGL2 (𝓞 L) L) × (AdeleRing (𝓞 L) L)ˣ =>
      φ (p.1.1⁻¹ * globalPoints (𝓞 L) L γ * sigmaAdelicAct K L D σ (centralScalar (𝓞 L) L p.2 * p.1.2)) :=
  hφc.comp ((continuous_fst.fst.inv.mul continuous_const).mul ((continuous_sigmaAdelicAct K L D σ).comp
    (((continuous_centralScalar L).comp continuous_snd).mul continuous_fst.snd)))

theorem continuous_kfun (hφc : Continuous φ) (hφs : HasCompactSupport φ) : Continuous (kfun K L D σ A φ) := by
  haveI := locallyCompactSpace_ideles L
  have hfun : kfun K L D σ A φ = fun p => ∑ᶠ γ, (BA A).indicator (fun γ =>
      φ (p.1.1⁻¹ * globalPoints (𝓞 L) L γ * sigmaAdelicAct K L D σ (centralScalar (𝓞 L) L p.2 * p.1.2))) γ := by
    funext p
    show (∑ᶠ γ ∈ BA A, _) = _
    rw [finsum_mem_def]
  rw [hfun]
  refine continuous_finsum (fun γ => ?_) ?_
  · by_cases hγ : γ ∈ BA A
    · simp only [Set.indicator_of_mem hγ]
      exact continuous_term K L D σ φ hφc γ
    · simp only [Set.indicator_of_notMem hγ]
      exact continuous_const
  · intro p
    obtain ⟨N, hNc, hNp⟩ := exists_compact_mem_nhds p
    refine ⟨N, hNp, ?_⟩
    have hC : IsCompact ((fun pm : ((AdelicGL2 (𝓞 L) L × AdelicGL2 (𝓞 L) L) × (AdeleRing (𝓞 L) L)ˣ) ×
        AdelicGL2 (𝓞 L) L => pm.1.1.1 * pm.2 *
          (sigmaAdelicAct K L D σ (centralScalar (𝓞 L) L pm.1.2 * pm.1.1.2))⁻¹) '' (N ×ˢ tsupport φ)) :=
      (hNc.prod hφs.isCompact).image ((continuous_fst.fst.fst.mul continuous_snd).mul
        ((continuous_sigmaAdelicAct K L D σ).comp (((continuous_centralScalar L).comp continuous_fst.snd).mul
          continuous_fst.fst.snd)).inv)
    refine (finite_setOf_globalPoints_mem L hC).subset ?_
    rintro γ ⟨p', hp's, hp'N⟩
    have hne : φ (p'.1.1⁻¹ * globalPoints (𝓞 L) L γ *
        sigmaAdelicAct K L D σ (centralScalar (𝓞 L) L p'.2 * p'.1.2)) ≠ 0 := fun h0 =>
      hp's (Set.indicator_apply_eq_zero.mpr fun _ => h0)
    refine ⟨(p', p'.1.1⁻¹ * globalPoints (𝓞 L) L γ * sigmaAdelicAct K L D σ (centralScalar (𝓞 L) L p'.2 * p'.1.2)),
      Set.mk_mem_prod hp'N (subset_tsupport φ (Function.mem_support.mpr hne)), ?_⟩
    simp only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one]

end Continuity

section Fold

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
variable (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
  (A : Set L) (φ : AdelicGL2 (𝓞 L) L → ℂ) (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)

def ξf (z : (AdeleRing (𝓞 L) L)ˣ) : ℂ := ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)

theorem ξf_mul (u v : (AdeleRing (𝓞 L) L)ˣ) : ξf L ξL (u * v) = ξf L ξL u * ξf L ξL v := by
  have : (⟨u * v, Subgroup.mem_top (u * v)⟩ : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ)) =
      ⟨u, Subgroup.mem_top u⟩ * ⟨v, Subgroup.mem_top v⟩ := rfl
  simp only [ξf, this, map_mul, Units.val_mul]

theorem ξf_princ_mul
    (hξt : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
        ξL ⟨z, Subgroup.mem_top z⟩ = 1)
    (u : Lˣ) (z : (AdeleRing (𝓞 L) L)ˣ) : ξf L ξL (princ L u * z) = ξf L ξL z := by
  rw [ξf_mul, show ξf L ξL (princ L u) = 1 from ?_, one_mul]
  simp only [ξf, hξt (princ L u) ⟨u, rfl⟩, Units.val_one]

theorem princ_injective : Function.Injective (princ L) := by
  intro u v h
  have := congrArg (fun u : (AdeleRing (𝓞 L) L)ˣ => (u : AdeleRing (𝓞 L) L)) h
  exact Units.ext (NumberField.AdeleRing.algebraMap_injective (𝓞 L) L this)

def princEquiv : Lˣ ≃ (princ L).range := (MonoidHom.ofInjective (princ_injective L)).toEquiv

variable [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ]
  (νZ : Measure (AdeleRing (𝓞 L) L)ˣ) [νZ.IsHaarMeasure] (Ω : Set (AdeleRing (𝓞 L) L)ˣ)

theorem setLIntegral_tsum_princ_mul (hΩ : IsFundamentalDomain (princ L).range Ω νZ)
    (g : (AdeleRing (𝓞 L) L)ˣ → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ z in Ω, ∑' q : Lˣ, g (princ L q * z) ∂νZ = ∫⁻ w, g w ∂νZ := by
  haveI := countable_units L
  haveI : Countable (princ L).range :=
    Function.Surjective.countable (MonoidHom.rangeRestrict_surjective (princ L))
  have hpt : ∀ z, ∑' q : Lˣ, g (princ L q * z) = ∑' γ : (princ L).range, g (γ • z) := fun z => by
    rw [← Equiv.tsum_eq (princEquiv L) (fun γ : (princ L).range => g (γ • z))]
    rfl
  simp_rw [hpt]
  rw [lintegral_tsum fun γ => ?_]
  · exact (hΩ.lintegral_eq_tsum'' g).symm
  · show AEMeasurable (fun z => g ((γ : (AdeleRing (𝓞 L) L)ˣ) * z)) (νZ.restrict Ω)
    exact (hg.comp (measurable_const_mul _)).aemeasurable

theorem exists_setLIntegral_le (hΩ : IsFundamentalDomain (princ L).range Ω νZ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
        ξL ⟨z, Subgroup.mem_top z⟩ = 1)
    (hφc : Continuous φ) (hφs : HasCompactSupport φ)
    {P : Set (AdelicGL2 (𝓞 L) L × AdelicGL2 (𝓞 L) L)} (hP : IsCompact P) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ x y, (x, y) ∈ P →
      ∫⁻ z in Ω, ‖ξf L ξL z * kfun K L D σ A φ ((x, y), z)‖ₑ ∂νZ ≤ C := by
  classical

  have hfin := finite_RP K L D σ φ hφs hP
  set T : Finset (Lˣ × L) := hfin.toFinset.filter fun r => ((r.1 : Lˣ) : L) ∈ A with hTdef
  have hT : ∀ r, r ∈ RP K L D σ φ P → ((r.1 : Lˣ) : L) ∈ A → r ∈ T := fun r h1 h2 => by
    rw [hTdef, Finset.mem_filter, Set.Finite.mem_toFinset]; exact ⟨h1, h2⟩
  have hT' : ∀ r ∈ T, ((r.1 : Lˣ) : L) ∈ A := fun r hr => by
    rw [hTdef, Finset.mem_filter] at hr; exact hr.2
  set W := WP' K L D σ φ P with hWdef
  have hW : IsCompact W := isCompact_WP' K L D σ φ hφs hP

  obtain ⟨Cξ, hCξ⟩ := hW.exists_bound_of_continuousOn hξc.continuousOn
  obtain ⟨Cφ, hCφ⟩ := hφc.bounded_above_of_compact_support hφs

  set g : (AdeleRing (𝓞 L) L)ˣ → ℝ≥0∞ := W.indicator fun _ => ENNReal.ofReal (Cξ * Cφ) with hgdef
  have hgm : Measurable g := measurable_const.indicator hW.measurableSet
  have hdom : ∀ x y, (x, y) ∈ P → ∀ (r : Lˣ × L) (w : (AdeleRing (𝓞 L) L)ˣ),
      ‖ξf L ξL w * F' K L D σ φ x y r w‖ₑ ≤ g w := by
    intro x y hxy r w
    by_cases h0 : F' K L D σ φ x y r w = 0
    · rw [h0, mul_zero, enorm_zero]; exact zero_le
    · have hw : w ∈ W := mem_WP'_of_F'_ne_zero K L D σ φ hxy h0
      rw [hgdef, Set.indicator_of_mem hw, ← ofReal_norm]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [norm_mul]
      exact mul_le_mul (hCξ w hw) (hCφ _) (norm_nonneg _) ((norm_nonneg _).trans (hCξ w hw))

  have hpt : ∀ x y, (x, y) ∈ P → ∀ z,
      ‖ξf L ξL z * kfun K L D σ A φ ((x, y), z)‖ₑ ≤ (T.card : ℝ≥0∞) * ∑' q : Lˣ, g (princ L q * z) := by
    intro x y hxy z
    have hk : kfun K L D σ A φ ((x, y), z) = ∑ r ∈ T, ∑ᶠ q : Lˣ, F' K L D σ φ x y r (princ L q * z) :=
      finsum_BA_eq K L D σ A φ hφs hxy T hT hT' z
    rw [hk, Finset.mul_sum]
    refine (enorm_sum_le T _).trans ?_
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_le_sum fun r _ => ?_

    have hfq : (Function.support fun q : Lˣ => F' K L D σ φ x y r (princ L q * z)).Finite := by
      refine (finite_setOf_princ_mul_mem L hW (isCompact_singleton (x := z))).subset ?_
      intro q hq
      exact ⟨z, rfl, mem_WP'_of_F'_ne_zero K L D σ φ hxy hq⟩
    have hfq' : (Function.support fun q : Lˣ => ξf L ξL (princ L q * z) * F' K L D σ φ x y r (princ L q * z)).Finite :=
      hfq.subset fun q hq h0 => hq (by simp only [h0, mul_zero])
    rw [mul_finsum' _ _ hfq]
    have heq : (fun q : Lˣ => ξf L ξL z * F' K L D σ φ x y r (princ L q * z)) =
        fun q => ξf L ξL (princ L q * z) * F' K L D σ φ x y r (princ L q * z) := by
      funext q; rw [ξf_princ_mul L ξL hξt]
    rw [heq, ← tsum_eq_finsum (L := SummationFilter.unconditional Lˣ) hfq']
    exact enorm_tsum_le_tsum_enorm.trans (ENNReal.tsum_le_tsum fun q => hdom x y hxy r _)

  refine ⟨(T.card : ℝ≥0∞) * (ENNReal.ofReal (Cξ * Cφ) * νZ W), ?_, ?_⟩
  · exact ENNReal.mul_lt_top (ENNReal.natCast_lt_top _) (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hW.measure_lt_top)
  · intro x y hxy
    calc ∫⁻ z in Ω, ‖ξf L ξL z * kfun K L D σ A φ ((x, y), z)‖ₑ ∂νZ
        ≤ ∫⁻ z in Ω, (T.card : ℝ≥0∞) * ∑' q : Lˣ, g (princ L q * z) ∂νZ := lintegral_mono fun z => hpt x y hxy z
      _ = (T.card : ℝ≥0∞) * ∫⁻ z in Ω, ∑' q : Lˣ, g (princ L q * z) ∂νZ :=
          lintegral_const_mul' _ _ (ENNReal.natCast_ne_top _)
      _ = (T.card : ℝ≥0∞) * ∫⁻ w, g w ∂νZ := by rw [setLIntegral_tsum_princ_mul L νZ Ω hΩ g hgm]
      _ = (T.card : ℝ≥0∞) * (ENNReal.ofReal (Cξ * Cφ) * νZ W) := by
          rw [hgdef, lintegral_indicator_const hW.measurableSet]

end Fold

section Main

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar NumberField.AdelicHaar.glBorel
  NumberField.AdelicHaar.borelSpace_glBorel

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
variable (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
  (A : Set L) (φ : AdelicGL2 (𝓞 L) L → ℂ) (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)

abbrev μA : Measure (AdeleRing (𝓞 L) L) := NumberField.AdelicHaar.adelicAddHaar (𝓞 L) L

abbrev μB : Measure (AdeleRing (𝓞 L) L) := ProbabilityTheory.cond (μA L) (NumberField.AdelicBox.adelicBox L)

scoped instance isProbabilityMeasure_μB : IsProbabilityMeasure (μB L) :=
  NumberField.AdelicBox.isProbabilityMeasure_cond_adelicBox L

theorem ae_mem_box : ∀ᵐ t ∂(μB L), t ∈ NumberField.AdelicBox.adelicBox L :=
  ProbabilityTheory.ae_cond_mem (NumberField.AdelicBox.measurableSet_adelicBox L)

theorem centralScalar_unipotent_comm (z : (AdeleRing (𝓞 L) L)ˣ) (t : AdeleRing (𝓞 L) L) (x : AdelicGL2 (𝓞 L) L) :
    centralScalar (𝓞 L) L z * (unipotentGL2 t * x) = unipotentGL2 t * (centralScalar (𝓞 L) L z * x) := by
  rw [← mul_assoc, centralScalar_comm L, mul_assoc]

variable [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ]
  (νZL : Measure (AdeleRing (𝓞 L) L)ˣ) [νZL.IsHaarMeasure] (ΩL : Set (AdeleRing (𝓞 L) L)ˣ)

theorem main
    (hΩL : IsFundamentalDomain (princ L).range ΩL νZL)
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
        ξL ⟨z, Subgroup.mem_top z⟩ = 1)
    (hφc : Continuous φ) (hφs : HasCompactSupport φ) :
    (∀ x : AdelicGL2 (𝓞 L) L, IntegrableOn (fun z : (AdeleRing (𝓞 L) L)ˣ => ξf L ξL z *
        ∑ᶠ γ ∈ BA A, φ (x⁻¹ * globalPoints (𝓞 L) L γ *
          sigmaAdelicAct K L D σ (centralScalar (𝓞 L) L z * x))) ΩL νZL) ∧
    (∀ x : AdelicGL2 (𝓞 L) L, IntegrableOn (fun z : (AdeleRing (𝓞 L) L)ˣ => ξf L ξL z *
        constantTerm (μB L) (fun t => unipotentGL2 t)
          (fun y => ∑ᶠ γ ∈ BA A, φ (x⁻¹ * globalPoints (𝓞 L) L γ * sigmaAdelicAct K L D σ y))
          (centralScalar (𝓞 L) L z * x)) ΩL νZL) ∧
    Measurable (fun x : AdelicGL2 (𝓞 L) L => ∫ z in ΩL, ξf L ξL z *
        ∑ᶠ γ ∈ BA A, φ (x⁻¹ * globalPoints (𝓞 L) L γ *
          sigmaAdelicAct K L D σ (centralScalar (𝓞 L) L z * x)) ∂νZL) ∧
    Measurable (fun x : AdelicGL2 (𝓞 L) L => ∫ z in ΩL, ξf L ξL z *
        constantTerm (μB L) (fun t => unipotentGL2 t)
          (fun y => ∑ᶠ γ ∈ BA A, φ (x⁻¹ * globalPoints (𝓞 L) L γ * sigmaAdelicAct K L D σ y))
          (centralScalar (𝓞 L) L z * x) ∂νZL) ∧
    ∀ x : AdelicGL2 (𝓞 L) L,
      constantTerm (μB L) (fun t => unipotentGL2 t)
          (fun x' : AdelicGL2 (𝓞 L) L => ∫ z in ΩL, ξf L ξL z *
            ∑ᶠ γ ∈ BA A, φ (x'⁻¹ * globalPoints (𝓞 L) L γ *
              sigmaAdelicAct K L D σ (centralScalar (𝓞 L) L z * x')) ∂νZL) x =
        ∫ z in ΩL, ξf L ξL z * ∫ t, ∑ᶠ γ ∈ BA A,
            φ ((unipotentGL2 t * x)⁻¹ * globalPoints (𝓞 L) L γ *
              sigmaAdelicAct K L D σ (unipotentGL2 t * (centralScalar (𝓞 L) L z * x))) ∂(μB L) ∂νZL := by

  haveI : SecondCountableTopology (AdeleRing (𝓞 L) L) := NumberField.AdeleRing.secondCountableTopology L
  haveI : SecondCountableTopology (AdelicGL2 (𝓞 L) L) :=
    NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo L
  haveI := secondCountableTopology_ideles L
  haveI := locallyCompactSpace_ideles L
  haveI : SigmaFinite νZL := by infer_instance

  set k := kfun K L D σ A φ with hkdef
  have hk : Continuous k := continuous_kfun K L D σ A φ hφc hφs
  have hξk : Continuous fun p : (AdelicGL2 (𝓞 L) L × AdelicGL2 (𝓞 L) L) × (AdeleRing (𝓞 L) L)ˣ =>
      ξf L ξL p.2 * k p := (hξc.comp continuous_snd).mul hk
  have hkap : ∀ (x y : AdelicGL2 (𝓞 L) L) (z : (AdeleRing (𝓞 L) L)ˣ), k ((x, y), z) =
      ∑ᶠ γ ∈ BA A, φ (x⁻¹ * globalPoints (𝓞 L) L γ * sigmaAdelicAct K L D σ (centralScalar (𝓞 L) L z * y)) :=
    fun _ _ _ => rfl

  have hbound := fun (P : Set (AdelicGL2 (𝓞 L) L × AdelicGL2 (𝓞 L) L)) (hP : IsCompact P) =>
    exists_setLIntegral_le K L D σ A φ ξL νZL ΩL hΩL hξc hξt hφc hφs hP

  obtain ⟨CB, hCB, hBCB⟩ := NumberField.AdelicBox.exists_isCompact_adelicBox_subset L
  have hcn : Continuous fun t : AdeleRing (𝓞 L) L => (unipotentGL2 t : AdelicGL2 (𝓞 L) L) := continuous_unipotentGL2'

  have hCT : ∀ (x : AdelicGL2 (𝓞 L) L) (z : (AdeleRing (𝓞 L) L)ˣ),
      constantTerm (μB L) (fun t => unipotentGL2 t)
        (fun y => ∑ᶠ γ ∈ BA A, φ (x⁻¹ * globalPoints (𝓞 L) L γ * sigmaAdelicAct K L D σ y))
        (centralScalar (𝓞 L) L z * x) = ∫ t, k ((x, unipotentGL2 t * x), z) ∂(μB L) := by
    intro x z
    show ∫ t, _ ∂(μB L) = _
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    show (∑ᶠ γ ∈ BA A, φ (x⁻¹ * globalPoints (𝓞 L) L γ *
      sigmaAdelicAct K L D σ (unipotentGL2 t * (centralScalar (𝓞 L) L z * x)))) = k ((x, unipotentGL2 t * x), z)
    rw [hkap, centralScalar_unipotent_comm]

  have h1 : ∀ x : AdelicGL2 (𝓞 L) L, IntegrableOn (fun z => ξf L ξL z * k ((x, x), z)) ΩL νZL := by
    intro x
    obtain ⟨C, hCtop, hC⟩ := hbound {(x, x)} isCompact_singleton
    refine ⟨(hξk.comp (Continuous.prodMk continuous_const continuous_id)).aestronglyMeasurable, ?_⟩
    exact lt_of_le_of_lt (hC x x rfl) hCtop

  have hTon : ∀ (x : AdelicGL2 (𝓞 L) L) (e : AdeleRing (𝓞 L) L → AdelicGL2 (𝓞 L) L × AdelicGL2 (𝓞 L) L),
      Continuous e → ∫⁻ t, ∫⁻ z in ΩL, ‖ξf L ξL z * k (e t, z)‖ₑ ∂νZL ∂(μB L) < ⊤ := by
    intro x e he
    obtain ⟨C, hCtop, hC⟩ := hbound (e '' CB) (hCB.image he)
    calc ∫⁻ t, ∫⁻ z in ΩL, ‖ξf L ξL z * k (e t, z)‖ₑ ∂νZL ∂(μB L)
        ≤ ∫⁻ _t, C ∂(μB L) := by
          refine lintegral_mono_ae ((ae_mem_box L).mono fun t ht => ?_)
          have := hC (e t).1 (e t).2 ⟨t, hBCB ht, rfl⟩
          exact this
      _ = C := by rw [lintegral_const, measure_univ, mul_one]
      _ < ⊤ := hCtop

  have h5 : ∀ x : AdelicGL2 (𝓞 L) L,
      constantTerm (μB L) (fun t => unipotentGL2 t) (fun x' => ∫ z in ΩL, ξf L ξL z * k ((x', x'), z) ∂νZL) x =
        ∫ z in ΩL, ξf L ξL z * ∫ t, k ((unipotentGL2 t * x, unipotentGL2 t * x), z) ∂(μB L) ∂νZL := by
    intro x
    set e : AdeleRing (𝓞 L) L → AdelicGL2 (𝓞 L) L × AdelicGL2 (𝓞 L) L :=
      fun t => (unipotentGL2 t * x, unipotentGL2 t * x) with hedef
    have he : Continuous e := (hcn.mul continuous_const).prodMk (hcn.mul continuous_const)
    have hf : Continuous (Function.uncurry fun (t : AdeleRing (𝓞 L) L) (z : (AdeleRing (𝓞 L) L)ˣ) =>
        ξf L ξL z * k (e t, z)) :=
      hξk.comp ((he.comp continuous_fst).prodMk continuous_snd)
    have hint : Integrable (Function.uncurry fun (t : AdeleRing (𝓞 L) L) (z : (AdeleRing (𝓞 L) L)ˣ) =>
        ξf L ξL z * k (e t, z)) ((μB L).prod (νZL.restrict ΩL)) := by
      refine ⟨hf.aestronglyMeasurable, ?_⟩
      show ∫⁻ p, ‖Function.uncurry (fun (t : AdeleRing (𝓞 L) L) (z : (AdeleRing (𝓞 L) L)ˣ) =>
        ξf L ξL z * k (e t, z)) p‖ₑ ∂((μB L).prod (νZL.restrict ΩL)) < ⊤
      rw [lintegral_prod _ hf.measurable.enorm.aemeasurable]
      exact hTon x e he
    show ∫ t, (∫ z in ΩL, ξf L ξL z * k ((unipotentGL2 t * x, unipotentGL2 t * x), z) ∂νZL) ∂(μB L) = _
    rw [integral_integral_swap hint]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    exact integral_const_mul _ _

  have h2 : ∀ x : AdelicGL2 (𝓞 L) L,
      IntegrableOn (fun z => ξf L ξL z * ∫ t, k ((x, unipotentGL2 t * x), z) ∂(μB L)) ΩL νZL := by
    intro x
    set e : AdeleRing (𝓞 L) L → AdelicGL2 (𝓞 L) L × AdelicGL2 (𝓞 L) L := fun t => (x, unipotentGL2 t * x) with hedef
    have he : Continuous e := continuous_const.prodMk (hcn.mul continuous_const)
    have hF2 : Continuous fun p : (AdeleRing (𝓞 L) L)ˣ × AdeleRing (𝓞 L) L => k (e p.2, p.1) :=
      hk.comp ((he.comp continuous_snd).prodMk continuous_fst)
    have hsm : StronglyMeasurable fun z : (AdeleRing (𝓞 L) L)ˣ => ∫ t, k (e t, z) ∂(μB L) :=
      hF2.stronglyMeasurable.integral_prod_right'
    refine ⟨(hξc.stronglyMeasurable.mul hsm).aestronglyMeasurable, ?_⟩
    have hG : Continuous (Function.uncurry fun (z : (AdeleRing (𝓞 L) L)ˣ) (t : AdeleRing (𝓞 L) L) =>
        ‖ξf L ξL z * k (e t, z)‖ₑ) :=
      (hξk.comp ((he.comp continuous_snd).prodMk continuous_fst)).enorm
    calc ∫⁻ z in ΩL, ‖ξf L ξL z * ∫ t, k (e t, z) ∂(μB L)‖ₑ ∂νZL
        ≤ ∫⁻ z in ΩL, ∫⁻ t, ‖ξf L ξL z * k (e t, z)‖ₑ ∂(μB L) ∂νZL := by
          refine lintegral_mono fun z => ?_
          rw [← integral_const_mul]
          exact enorm_integral_le_lintegral_enorm _
      _ = ∫⁻ t, ∫⁻ z in ΩL, ‖ξf L ξL z * k (e t, z)‖ₑ ∂νZL ∂(μB L) :=
          lintegral_lintegral_swap hG.measurable.aemeasurable
      _ < ⊤ := hTon x e he

  have h3 : Measurable fun x : AdelicGL2 (𝓞 L) L => ∫ z in ΩL, ξf L ξL z * k ((x, x), z) ∂νZL := by
    have hF3 : Continuous fun p : AdelicGL2 (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ => ξf L ξL p.2 * k ((p.1, p.1), p.2) :=
      hξk.comp ((continuous_fst.prodMk continuous_fst).prodMk continuous_snd)
    exact (hF3.stronglyMeasurable.integral_prod_right' (ν := νZL.restrict ΩL)).measurable

  have h4 : Measurable fun x : AdelicGL2 (𝓞 L) L =>
      ∫ z in ΩL, ξf L ξL z * ∫ t, k ((x, unipotentGL2 t * x), z) ∂(μB L) ∂νZL := by
    have hF4 : Continuous fun p : (AdelicGL2 (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ) × AdeleRing (𝓞 L) L =>
        k ((p.1.1, unipotentGL2 p.2 * p.1.1), p.1.2) :=
      hk.comp ((continuous_fst.fst.prodMk ((hcn.comp continuous_snd).mul continuous_fst.fst)).prodMk continuous_fst.snd)
    have hsm : StronglyMeasurable fun p : AdelicGL2 (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ =>
        ∫ t, k ((p.1, unipotentGL2 t * p.1), p.2) ∂(μB L) :=
      hF4.stronglyMeasurable.integral_prod_right'
    have hsm' : StronglyMeasurable fun p : AdelicGL2 (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ =>
        ξf L ξL p.2 * ∫ t, k ((p.1, unipotentGL2 t * p.1), p.2) ∂(μB L) :=
      (hξc.comp continuous_snd).stronglyMeasurable.mul hsm
    exact (hsm'.integral_prod_right' (ν := νZL.restrict ΩL)).measurable

  refine ⟨h1, fun x => ?_, h3, ?_, fun x => ?_⟩
  · have hfun : (fun z : (AdeleRing (𝓞 L) L)ˣ => ξf L ξL z * constantTerm (μB L) (fun t => unipotentGL2 t)
        (fun y => ∑ᶠ γ ∈ BA A, φ (x⁻¹ * globalPoints (𝓞 L) L γ * sigmaAdelicAct K L D σ y))
        (centralScalar (𝓞 L) L z * x)) = fun z => ξf L ξL z * ∫ t, k ((x, unipotentGL2 t * x), z) ∂(μB L) := by
      funext z; rw [hCT]
    rw [hfun]
    exact h2 x
  · have hfun : (fun x : AdelicGL2 (𝓞 L) L => ∫ z in ΩL, ξf L ξL z * constantTerm (μB L) (fun t => unipotentGL2 t)
        (fun y => ∑ᶠ γ ∈ BA A, φ (x⁻¹ * globalPoints (𝓞 L) L γ * sigmaAdelicAct K L D σ y))
        (centralScalar (𝓞 L) L z * x) ∂νZL) =
        fun x => ∫ z in ΩL, ξf L ξL z * ∫ t, k ((x, unipotentGL2 t * x), z) ∂(μB L) ∂νZL := by
      funext x
      refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      show ξf L ξL z * _ = ξf L ξL z * _
      rw [hCT]
    rw [hfun]
    exact h4
  · show constantTerm (μB L) (fun t => unipotentGL2 t) (fun x' => ∫ z in ΩL, ξf L ξL z * k ((x', x'), z) ∂νZL) x = _
    rw [h5 x]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    show ξf L ξL z * _ = ξf L ξL z * _
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    show k ((unipotentGL2 t * x, unipotentGL2 t * x), z) = _
    rw [hkap, centralScalar_unipotent_comm]

end Main

end R4FoldCT
p2m_reactivate "P2MW.S_AutomorphicForm_integrableOn_and_measurable_and_constantTerm_setIntegral_mul_finsum_borel_div_mem_eq_setIntegral_mul_integral_finsum_inv_unipotentGL2_mul.R4FoldCT"

end
p2m_reactivate "P2MW.S_AutomorphicForm_integrableOn_and_measurable_and_constantTerm_setIntegral_mul_finsum_borel_div_mem_eq_setIntegral_mul_integral_finsum_inv_unipotentGL2_mul.R4FoldCT"

section

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicBox

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem solution
    (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ] (νZL : Measure (AdeleRing (𝓞 L) L)ˣ)
    [νZL.IsHaarMeasure] (ΩL : Set (AdeleRing (𝓞 L) L)ˣ)
    (hΩL : IsFundamentalDomain
      (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range ΩL νZL)
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
        ξL ⟨z, Subgroup.mem_top z⟩ = 1)
    (A : Set L)
    (φ : AutomorphicForm.AdelicGL2 (𝓞 L) L → ℂ) (hφc : Continuous φ) (hφs : HasCompactSupport φ) :
    (∀ x : AutomorphicForm.AdelicGL2 (𝓞 L) L,
      IntegrableOn (fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
        ∑ᶠ γ ∈ {γ : Matrix.GeneralLinearGroup (Fin 2) L |
            (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
              (γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1 ∈ A},
          φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L γ *
            AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x))) ΩL νZL) ∧
    (∀ x : AutomorphicForm.AdelicGL2 (𝓞 L) L,
      IntegrableOn (fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
        @AutomorphicForm.constantTerm _ (adeleBorel (𝓞 L) L) _ _
          (@ProbabilityTheory.cond _ (adeleBorel (𝓞 L) L) (adelicAddHaar (𝓞 L) L) (adelicBox L))
          (fun t => AutomorphicForm.unipotentGL2 t)
          (fun y => ∑ᶠ γ ∈ {γ : Matrix.GeneralLinearGroup (Fin 2) L |
              (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
                (γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1 ∈ A},
            φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L γ * AutomorphicForm.sigmaAdelicAct K L D σ y))
          (AutomorphicForm.centralScalar (𝓞 L) L z * x)) ΩL νZL) ∧
    Measurable (fun x : AutomorphicForm.AdelicGL2 (𝓞 L) L =>
      ∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
        ∑ᶠ γ ∈ {γ : Matrix.GeneralLinearGroup (Fin 2) L |
            (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
              (γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1 ∈ A},
          φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L γ *
            AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x)) ∂νZL) ∧
    Measurable (fun x : AutomorphicForm.AdelicGL2 (𝓞 L) L =>
      ∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
        @AutomorphicForm.constantTerm _ (adeleBorel (𝓞 L) L) _ _
          (@ProbabilityTheory.cond _ (adeleBorel (𝓞 L) L) (adelicAddHaar (𝓞 L) L) (adelicBox L))
          (fun t => AutomorphicForm.unipotentGL2 t)
          (fun y => ∑ᶠ γ ∈ {γ : Matrix.GeneralLinearGroup (Fin 2) L |
              (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
                (γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1 ∈ A},
            φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L γ * AutomorphicForm.sigmaAdelicAct K L D σ y))
          (AutomorphicForm.centralScalar (𝓞 L) L z * x) ∂νZL) ∧
    ∀ x : AutomorphicForm.AdelicGL2 (𝓞 L) L,
      @AutomorphicForm.constantTerm _ (adeleBorel (𝓞 L) L) _ _
          (@ProbabilityTheory.cond _ (adeleBorel (𝓞 L) L) (adelicAddHaar (𝓞 L) L) (adelicBox L))
          (fun t => AutomorphicForm.unipotentGL2 t)
          (fun x' : AutomorphicForm.AdelicGL2 (𝓞 L) L =>
            ∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
              ∑ᶠ γ ∈ {γ : Matrix.GeneralLinearGroup (Fin 2) L |
                  (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
                    (γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1 ∈ A},
                φ (x'⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L γ *
                  AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x')) ∂νZL)
          x =
        ∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
          ∫ t, ∑ᶠ γ ∈ {γ : Matrix.GeneralLinearGroup (Fin 2) L |
              (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
                (γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1 ∈ A},
            φ ((AutomorphicForm.unipotentGL2 t * x)⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L γ *
              AutomorphicForm.sigmaAdelicAct K L D σ
                (AutomorphicForm.unipotentGL2 t * (AutomorphicForm.centralScalar (𝓞 L) L z * x)))
            ∂(@ProbabilityTheory.cond _ (adeleBorel (𝓞 L) L) (adelicAddHaar (𝓞 L) L) (adelicBox L)) ∂νZL :=
  R4FoldCT.main K L D σ A φ ξL νZL ΩL hΩL hξc hξt hφc hφs

end
p2m_reactivate "P2MW.S_AutomorphicForm_integrableOn_and_measurable_and_constantTerm_setIntegral_mul_finsum_borel_div_mem_eq_setIntegral_mul_integral_finsum_inv_unipotentGL2_mul.R4FoldCT"

end S_AutomorphicForm_integrableOn_and_measurable_and_constantTerm_setIntegral_mul_finsum_borel_div_mem_eq_setIntegral_mul_integral_finsum_inv_unipotentGL2_mul
end P2MW
export P2MW.S_AutomorphicForm_integrableOn_and_measurable_and_constantTerm_setIntegral_mul_finsum_borel_div_mem_eq_setIntegral_mul_integral_finsum_inv_unipotentGL2_mul (solution)
