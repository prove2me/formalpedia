-- Prove2me | solution 1 for AutomorphicForm.setIntegral_mul_indicator_highSet_constantTerm_finsum_eq_indicator_mul_tsum_integral_unipotentGL2_twistedOrbital
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/3ff08dd1-a863-502c-86c1-16ec001d0a15

import Mathlib
import Theorems.Thm_AutomorphicForm_integrableOn_and_setIntegral_mul_constantTerm_finsum_borelSigmaConjClassOrbit_eq_inv_measure_mul_tsum_integral_integral
import Theorems.Thm_AutomorphicForm_integral_integral_unipotentGL2_conj_twistedOrbital_eq_integral_mul_integral_and_lintegral_lt_top_of_norm_div_ne_one
import Theorems.Thm_LT_TwistedNorm_setOf_exists_mem_center_inter_setOf_apply_one_zero_eq_zero_eq_union_and_disjoint
import Theorems.Thm_LT_TwistedNorm_exists_subgroup_and_mul_mul_map_inv_mem_center_iff_of_diagonal_of_norm_div_ne_one
import Theorems.Thm_NumberField_AdelicHeight_adelicHeight_unipotentGL2_mul_and_centralScalar_mul
import Theorems.Thm_NumberField_AdeleRing_finite_setOf_algebraMap_mem_of_isCompact
import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_TwistedNormClasses
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_TwistedAdelicKernel
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_HaarQuotient
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_setIntegral_mul_indicator_highSet_constantTerm_finsum_eq_indicator_mul_tsum_integral_unipotentGL2_twistedOrbital
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply FLT.HaarFiniteOrderGates.negContinuousAddEquiv_apply FLT.HaarFiniteOrderGates.doublingContinuousAddEquiv_apply FLT.HaarFiniteOrderGates.invContinuousMulEquiv_apply"

set_option autoImplicit false

noncomputable section

namespace R4C3aUnfold

set_option maxHeartbeats 1600000

open MeasureTheory NumberField Filter Function Set AutomorphicForm
open scoped ENNReal NNReal Topology

section FieldGL2

variable {L : Type} [Field L]

theorem det_ne_zero_entries (d : GL (Fin 2) L) (h10 : (d : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) :
    (d : Matrix (Fin 2) (Fin 2) L) 0 0 ≠ 0 ∧ (d : Matrix (Fin 2) (Fin 2) L) 1 1 ≠ 0 := by
  have hdet : (d : Matrix (Fin 2) (Fin 2) L).det ≠ 0 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply]
    exact (Matrix.GeneralLinearGroup.det d).ne_zero
  rw [Matrix.det_fin_two, h10, mul_zero, sub_zero] at hdet
  exact ⟨left_ne_zero_of_mul hdet, right_ne_zero_of_mul hdet⟩

theorem norm_div_ne_one_symm {K : Type} [Field K] [Algebra K L] {a b : L} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : Algebra.norm K (a / b) ≠ 1) : Algebra.norm K (b / a) ≠ 1 := by
  intro h1
  apply h
  have hprod : (a / b) * (b / a) = 1 := by field_simp
  have h2 := congrArg (Algebra.norm K) hprod
  rw [map_mul, map_one, h1, mul_one] at h2
  exact h2

theorem gl2Weyl_conj_diag (h : GL (Fin 2) L)
    (h10 : (h : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) (h01 : (h : Matrix (Fin 2) (Fin 2) L) 0 1 = 0) :
    ((gl2Weyl * h * gl2Weyl⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) =
      !![(h : Matrix (Fin 2) (Fin 2) L) 1 1, 0; 0, (h : Matrix (Fin 2) (Fin 2) L) 0 0] := by
  rw [gl2Weyl_inv]
  ext i j
  rw [Units.val_mul, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, Matrix.mul_apply, Matrix.mul_apply,
    Fin.sum_univ_two, Fin.sum_univ_two, gl2Weyl_val]
  fin_cases i <;> fin_cases j <;> simp [h10, h01]

theorem map_gl2Weyl (τ : L →+* L) :
    Matrix.GeneralLinearGroup.map τ (gl2Weyl : GL (Fin 2) L) = gl2Weyl := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  change τ ((gl2Weyl : GL (Fin 2) L) i j) = (gl2Weyl : GL (Fin 2) L) i j
  rw [gl2Weyl_val]
  fin_cases i <;> fin_cases j <;> simp

variable {K : Type} [Field K] [Algebra K L]

theorem mem_iff_diag_and_stab [FiniteDimensional K L] [IsGalois K L] {σ : L ≃ₐ[K] L}
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) (t : GL (Fin 2) L)
    (h10 : (t : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) (h01 : (t : Matrix (Fin 2) (Fin 2) L) 0 1 = 0)
    (hN : Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0 / (t : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1)
    (Λ' : Subgroup (GL (Fin 2) L))
    (hΛ' : ∀ a : GL (Fin 2) L, a ∈ Λ' ↔ ((a : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (a : Matrix (Fin 2) (Fin 2) L) 0 1 = 0) ∧
      (a : Matrix (Fin 2) (Fin 2) L) 0 0 / (a : Matrix (Fin 2) (Fin 2) L) 1 1 ∈ Set.range (algebraMap K L))
    (m : GL (Fin 2) L) :
    m ∈ Λ' ↔ ((m : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (m : Matrix (Fin 2) (Fin 2) L) 0 1 = 0) ∧
      t⁻¹ * (m * t * (Matrix.GeneralLinearGroup.map (σ : L →+* L) m)⁻¹) ∈ Subgroup.center (GL (Fin 2) L) := by
  have key := (LT.TwistedNorm.exists_subgroup_and_mul_mul_map_inv_mem_center_iff_of_diagonal_of_norm_div_ne_one
    hgen t h10 h01 hN).2 m
  rw [hΛ']
  constructor
  · rintro ⟨hd, hr⟩
    exact ⟨hd, key.mpr (Or.inl ⟨hd, hr⟩)⟩
  · rintro ⟨hd, hc⟩
    rcases key.mp hc with h | ⟨h00, -, -⟩
    · exact h
    · exact absurd h00 (det_ne_zero_entries m hd.1).1

end FieldGL2

section Adelic

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
variable (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)

abbrev ιA : L →+* AdeleRing (𝓞 L) L := algebraMap L (AdeleRing (𝓞 L) L)

theorem centralScalar_comm (z : (AdeleRing (𝓞 L) L)ˣ) (g : AdelicGL2 (𝓞 L) L) :
    centralScalar (𝓞 L) L z * g = g * centralScalar (𝓞 L) L z := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul]
  exact (Matrix.scalar_commute (n := Fin 2) (z : AdeleRing (𝓞 L) L) (fun r' => Commute.all _ r') _).eq

theorem sigmaAdelicAct_centralScalar (z : (AdeleRing (𝓞 L) L)ˣ) :
    sigmaAdelicAct K L D σ (centralScalar (𝓞 L) L z) = centralScalar (𝓞 L) L (D.unitsAct σ z) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  change ((D.act σ : RingAut (AdeleRing (𝓞 L) L)).toRingHom) (Matrix.scalar (Fin 2) (z : AdeleRing (𝓞 L) L) i j) =
    Matrix.scalar (Fin 2) ((D.act σ : RingAut (AdeleRing (𝓞 L) L)) (z : AdeleRing (𝓞 L) L)) i j
  rw [Matrix.scalar_apply, Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.diagonal_apply]
  split_ifs <;> simp

theorem sigmaAdelicAct_adelicWeyl_inv :
    sigmaAdelicAct K L D σ (adelicWeyl (𝓞 L) L)⁻¹ = (adelicWeyl (𝓞 L) L)⁻¹ := by
  rw [show adelicWeyl (𝓞 L) L = globalPoints (𝓞 L) L gl2Weyl from rfl, ← map_inv]
  refine (AutomorphicForm.sigmaAdelicAct_globalPoints K L D σ gl2Weyl⁻¹).trans ?_
  rw [map_inv (Matrix.GeneralLinearGroup.map (σ : L →+* L)) gl2Weyl, map_gl2Weyl]
  rfl

theorem argW_eq (δ₀ : GL (Fin 2) L) (y : AdelicGL2 (𝓞 L) L) (s : AdeleRing (𝓞 L) L) (z : (AdeleRing (𝓞 L) L)ˣ) :
    ((adelicWeyl (𝓞 L) L)⁻¹ * unipotentGL2 s * y)⁻¹ * globalPoints (𝓞 L) L δ₀ *
        sigmaAdelicAct K L D σ (centralScalar (𝓞 L) L z * ((adelicWeyl (𝓞 L) L)⁻¹ * unipotentGL2 s * y)) =
      (unipotentGL2 s * y)⁻¹ * globalPoints (𝓞 L) L (gl2Weyl * δ₀ * gl2Weyl⁻¹) *
        sigmaAdelicAct K L D σ (centralScalar (𝓞 L) L z * (unipotentGL2 s * y)) := by
  set gp := globalPoints (𝓞 L) L with hgp
  set σA := sigmaAdelicAct K L D σ with hσA
  set cs := centralScalar (𝓞 L) L with hcs
  set W : AdelicGL2 (𝓞 L) L := adelicWeyl (𝓞 L) L with hW
  have hWdef : W = gp gl2Weyl := rfl
  have e1 : σA W⁻¹ = W⁻¹ := sigmaAdelicAct_adelicWeyl_inv K L D σ
  have hcomm : ∀ (u : (AdeleRing (𝓞 L) L)ˣ) (g : AdelicGL2 (𝓞 L) L), g * cs u = cs u * g := fun u g =>
    (centralScalar_comm L u g).symm
  calc (W⁻¹ * unipotentGL2 s * y)⁻¹ * gp δ₀ * σA (cs z * (W⁻¹ * unipotentGL2 s * y))
      = (unipotentGL2 s * y)⁻¹ * W * gp δ₀ * (σA (cs z) * W⁻¹) * σA (unipotentGL2 s * y) := by
        rw [map_mul, map_mul, map_mul, e1, map_mul]; group
    _ = (unipotentGL2 s * y)⁻¹ * (W * gp δ₀ * W⁻¹) * σA (cs z) * σA (unipotentGL2 s * y) := by
        rw [show σA (cs z) = cs (D.unitsAct σ z) from sigmaAdelicAct_centralScalar K L D σ z, ← hcomm]
        group
    _ = (unipotentGL2 s * y)⁻¹ * gp (gl2Weyl * δ₀ * gl2Weyl⁻¹) * σA (cs z * (unipotentGL2 s * y)) := by
        rw [map_mul σA (cs z), map_mul gp, map_mul gp, map_inv gp, ← hWdef]; group

theorem finite_setOf_globalPoints_mem {C : Set (AdelicGL2 (𝓞 L) L)} (hC : IsCompact C) :
    {γ : GL (Fin 2) L | globalPoints (𝓞 L) L γ ∈ C}.Finite := by
  have hent : ∀ i j : Fin 2, {t : L | ιA L t ∈
      (fun m : AdelicGL2 (𝓞 L) L => (m : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i j) '' C}.Finite :=
    fun i j => NumberField.AdeleRing.finite_setOf_algebraMap_mem_of_isCompact L
      (hC.image (Units.continuous_val.matrix_elem i j))
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

theorem finite_support_kernel (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφs : HasCompactSupport φ) (x y : AdelicGL2 (𝓞 L) L) :
    (Function.support fun γ : GL (Fin 2) L => φ (x⁻¹ * globalPoints (𝓞 L) L γ * y)).Finite := by
  have hC : IsCompact ((fun m => x * m * y⁻¹) '' tsupport φ) :=
    hφs.isCompact.image ((continuous_const.mul continuous_id).mul continuous_const)
  refine (finite_setOf_globalPoints_mem L hC).subset ?_
  intro γ hγ
  refine ⟨_, subset_tsupport φ hγ, ?_⟩
  simp only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one]

end Adelic

section Objects

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
variable [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ]
  (νZL : Measure (AdeleRing (𝓞 L) L)ˣ)
variable (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
  (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
  (φ : AdelicGL2 (𝓞 L) L → ℂ) (x : AdelicGL2 (𝓞 L) L)

abbrev μA : Measure (AdeleRing (𝓞 L) L) := NumberField.AdelicHaar.adelicAddHaar (𝓞 L) L

abbrev μB : Measure (AdeleRing (𝓞 L) L) := ProbabilityTheory.cond (μA L) (NumberField.AdelicBox.adelicBox L)

def ξf (z : (AdeleRing (𝓞 L) L)ˣ) : ℂ := ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)

def Aconj (δ : GL (Fin 2) L) (y : AdelicGL2 (𝓞 L) L) : ℂ :=
  ∫ s, ∫ z, ξf L ξL z * φ ((unipotentGL2 s * y)⁻¹ * globalPoints (𝓞 L) L δ *
    sigmaAdelicAct K L D σ (centralScalar (𝓞 L) L z * (unipotentGL2 s * y))) ∂νZL ∂(μA L)

def AconjW (δ : GL (Fin 2) L) (y : AdelicGL2 (𝓞 L) L) : ℂ :=
  ∫ s, ∫ z, ξf L ξL z * φ (((adelicWeyl (𝓞 L) L)⁻¹ * unipotentGL2 s * y)⁻¹ * globalPoints (𝓞 L) L δ *
    sigmaAdelicAct K L D σ (centralScalar (𝓞 L) L z * ((adelicWeyl (𝓞 L) L)⁻¹ * unipotentGL2 s * y))) ∂νZL ∂(μA L)

def Lconj (δ : GL (Fin 2) L) (y : AdelicGL2 (𝓞 L) L) : ℝ≥0∞ :=
  ∫⁻ s, ∫⁻ z, ‖ξf L ξL z‖ₑ * ‖φ ((unipotentGL2 s * y)⁻¹ * globalPoints (𝓞 L) L δ *
    sigmaAdelicAct K L D σ (centralScalar (𝓞 L) L z * (unipotentGL2 s * y)))‖ₑ ∂νZL ∂(μA L)

def LconjW (δ : GL (Fin 2) L) (y : AdelicGL2 (𝓞 L) L) : ℝ≥0∞ :=
  ∫⁻ s, ∫⁻ z, ‖ξf L ξL z‖ₑ * ‖φ (((adelicWeyl (𝓞 L) L)⁻¹ * unipotentGL2 s * y)⁻¹ * globalPoints (𝓞 L) L δ *
    sigmaAdelicAct K L D σ (centralScalar (𝓞 L) L z * ((adelicWeyl (𝓞 L) L)⁻¹ * unipotentGL2 s * y)))‖ₑ ∂νZL ∂(μA L)

def Atr (δ : GL (Fin 2) L) (y : AdelicGL2 (𝓞 L) L) : ℂ :=
  ∫ w, ξf L ξL w * ∫ t, φ (y⁻¹ * globalPoints (𝓞 L) L δ *
    sigmaAdelicAct K L D σ (unipotentGL2 t * (centralScalar (𝓞 L) L w * y))) ∂(μA L) ∂νZL

def Ltr (δ : GL (Fin 2) L) (y : AdelicGL2 (𝓞 L) L) : ℝ≥0∞ :=
  ∫⁻ w, ‖ξf L ξL w‖ₑ * ∫⁻ t, ‖φ (y⁻¹ * globalPoints (𝓞 L) L δ *
    sigmaAdelicAct K L D σ (unipotentGL2 t * (centralScalar (𝓞 L) L w * y)))‖ₑ ∂(μA L) ∂νZL

def KJ (S : Set (GL (Fin 2) L)) (y : AdelicGL2 (𝓞 L) L) : ℂ :=
  ∑ᶠ γ ∈ S, φ (x⁻¹ * globalPoints (𝓞 L) L γ * sigmaAdelicAct K L D σ y)

def CTJ (S : Set (GL (Fin 2) L)) (g : AdelicGL2 (𝓞 L) L) : ℂ :=
  constantTerm (μB L) (fun t => unipotentGL2 t) (KJ K L D σ φ x S) g

omit [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] in
theorem CTJ_eq (S : Set (GL (Fin 2) L)) (g : AdelicGL2 (𝓞 L) L) :
    CTJ K L D σ φ x S g = ∫ q, KJ K L D σ φ x S (unipotentGL2 q * g) ∂(μB L) := rfl

def yv {κ : Type} (ra : κ → GL (Fin 2) L) (j : κ) : AdelicGL2 (𝓞 L) L := (globalPoints (𝓞 L) L (ra j))⁻¹ * x

theorem AconjW_eq (δ : GL (Fin 2) L) (y : AdelicGL2 (𝓞 L) L) :
    AconjW K L νZL D σ ξL φ δ y = Aconj K L νZL D σ ξL φ (gl2Weyl * δ * gl2Weyl⁻¹) y := by
  unfold AconjW Aconj
  simp only [argW_eq K L D σ δ y]

theorem LconjW_eq (δ : GL (Fin 2) L) (y : AdelicGL2 (𝓞 L) L) :
    LconjW K L νZL D σ ξL φ δ y = Lconj K L νZL D σ ξL φ (gl2Weyl * δ * gl2Weyl⁻¹) y := by
  unfold LconjW Lconj
  simp only [argW_eq K L D σ δ y]

omit [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] in

theorem KJ_union (hφs : HasCompactSupport φ) {S T : Set (GL (Fin 2) L)} (hST : Disjoint S T)
    (y : AdelicGL2 (𝓞 L) L) : KJ K L D σ φ x (S ∪ T) y = KJ K L D σ φ x S y + KJ K L D σ φ x T y := by
  unfold KJ
  have hfin := finite_support_kernel L φ hφs x (sigmaAdelicAct K L D σ y)
  exact finsum_mem_union' hST (hfin.subset Set.inter_subset_right) (hfin.subset Set.inter_subset_right)

end Objects

section Main

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.AdelicHaar.glBorel

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
variable [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ]
  (νZL : Measure (AdeleRing (𝓞 L) L)ˣ) [νZL.IsHaarMeasure] (ΩL : Set (AdeleRing (𝓞 L) L)ˣ)
variable (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
  (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
  (δ₀ : GL (Fin 2) L) (I : Set (GL (Fin 2) L)) (Λ' : Subgroup (GL (Fin 2) L))
  {κ : Type} (ra : κ → GL (Fin 2) L)
  (φ : AdelicGL2 (𝓞 L) L → ℂ) (x : AdelicGL2 (𝓞 L) L) (R : ℝ)

theorem brick
    (hΩL : IsFundamentalDomain (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range ΩL νZL)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
        ξL ⟨z, Subgroup.mem_top z⟩ = 1)
    (hΛ' : ∀ a : GL (Fin 2) L, a ∈ Λ' ↔ ((a : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (a : Matrix (Fin 2) (Fin 2) L) 0 1 = 0) ∧
      (a : Matrix (Fin 2) (Fin 2) L) 0 0 / (a : Matrix (Fin 2) (Fin 2) L) 1 1 ∈ Set.range (algebraMap K L))
    (hrad : ∀ j, ((ra j : Matrix (Fin 2) (Fin 2) L)) 1 0 = 0 ∧ ((ra j : Matrix (Fin 2) (Fin 2) L)) 0 1 = 0)
    (hra : ∀ a : GL (Fin 2) L, ((a : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (a : Matrix (Fin 2) (Fin 2) L) 0 1 = 0) →
      ∃! j, (ra j)⁻¹ * a ∈ Λ')
    (hφc : Continuous φ) (hφs : HasCompactSupport φ)
    (t : GL (Fin 2) L) (ht10 : (t : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) (ht01 : (t : Matrix (Fin 2) (Fin 2) L) 0 1 = 0)
    (htN : Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0 / (t : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1) :
    {j : κ | ∃ (w : (AdeleRing (𝓞 L) L)ˣ) (t₁ : AdeleRing (𝓞 L) L),
        φ ((yv L x ra j)⁻¹ * globalPoints (𝓞 L) L t *
          sigmaAdelicAct K L D σ (unipotentGL2 t₁ * (centralScalar (𝓞 L) L w * yv L x ra j))) ≠ 0}.Finite ∧
    (∀ z : (AdeleRing (𝓞 L) L)ˣ, Integrable (fun q : AdeleRing (𝓞 L) L =>
        KJ K L D σ φ x {γ : GL (Fin 2) L | ∃ b : GL (Fin 2) L, (b : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
          t⁻¹ * (b⁻¹ * γ * Matrix.GeneralLinearGroup.map (σ : L →+* L) b) ∈ Subgroup.center (GL (Fin 2) L)}
          (unipotentGL2 q * (centralScalar (𝓞 L) L z * x))) (μB L)) ∧
    IntegrableOn (fun z : (AdeleRing (𝓞 L) L)ˣ => ξf L ξL z *
        CTJ K L D σ φ x {γ : GL (Fin 2) L | ∃ b : GL (Fin 2) L, (b : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
          t⁻¹ * (b⁻¹ * γ * Matrix.GeneralLinearGroup.map (σ : L →+* L) b) ∈ Subgroup.center (GL (Fin 2) L)}
          (centralScalar (𝓞 L) L z * x)) ΩL νZL ∧
    (∫ z in ΩL, ξf L ξL z *
        CTJ K L D σ φ x {γ : GL (Fin 2) L | ∃ b : GL (Fin 2) L, (b : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
          t⁻¹ * (b⁻¹ * γ * Matrix.GeneralLinearGroup.map (σ : L →+* L) b) ∈ Subgroup.center (GL (Fin 2) L)}
          (centralScalar (𝓞 L) L z * x) ∂νZL) =
      ((μA L (NumberField.AdelicBox.adelicBox L)).toReal : ℂ)⁻¹ * ∑' j : κ, Atr K L νZL D σ ξL φ t (yv L x ra j) := by
  haveI : FiniteDimensional K L := Module.Finite.of_restrictScalars_finite ℚ K L
  have hM := mem_iff_diag_and_stab hgen t ht10 ht01 htN Λ' hΛ'
  obtain ⟨h1, -, -, h4, h5, h6⟩ :=
    AutomorphicForm.integrableOn_and_setIntegral_mul_constantTerm_finsum_borelSigmaConjClassOrbit_eq_inv_measure_mul_tsum_integral_integral
      K L νZL ΩL hΩL D σ ξL hξc hξt t ht10 ht01 htN
      {γ : GL (Fin 2) L | ∃ b : GL (Fin 2) L, (b : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
          t⁻¹ * (b⁻¹ * γ * Matrix.GeneralLinearGroup.map (σ : L →+* L) b) ∈ Subgroup.center (GL (Fin 2) L)}
      (fun _ => Iff.rfl) Λ' hM ra hrad (fun d hd1 hd2 => hra d ⟨hd1, hd2⟩) φ hφc hφs x
  exact ⟨h1, h4, h5, h6⟩

theorem cov
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hφc : Continuous φ) (hφs : HasCompactSupport φ)
    (t : GL (Fin 2) L) (ht10 : (t : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) (ht01 : (t : Matrix (Fin 2) (Fin 2) L) 0 1 = 0)
    (htN : Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0 / (t : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1)
    (y : AdelicGL2 (𝓞 L) L) :
    Lconj K L νZL D σ ξL φ t y = Ltr K L νZL D σ ξL φ t y ∧ Ltr K L νZL D σ ξL φ t y < ⊤ ∧
      Aconj K L νZL D σ ξL φ t y = Atr K L νZL D σ ξL φ t y :=
  AutomorphicForm.integral_integral_unipotentGL2_conj_twistedOrbital_eq_integral_mul_integral_and_lintegral_lt_top_of_norm_div_ne_one
    K L νZL D σ hgen (ξf L ξL) hξc t ht10 ht01 htN φ hφc hφs y

omit [NumberField K] [IsGalois K L] [BorelSpace (AdeleRing (𝓞 L) L)ˣ] [νZL.IsHaarMeasure] in

theorem Atr_eq_zero_and_Ltr_eq_zero (t : GL (Fin 2) L) {j : κ}
    (hj : j ∉ {j : κ | ∃ (w : (AdeleRing (𝓞 L) L)ˣ) (t₁ : AdeleRing (𝓞 L) L),
        φ ((yv L x ra j)⁻¹ * globalPoints (𝓞 L) L t *
          sigmaAdelicAct K L D σ (unipotentGL2 t₁ * (centralScalar (𝓞 L) L w * yv L x ra j))) ≠ 0}) :
    Atr K L νZL D σ ξL φ t (yv L x ra j) = 0 ∧ Ltr K L νZL D σ ξL φ t (yv L x ra j) = 0 := by
  have h0 : ∀ (w : (AdeleRing (𝓞 L) L)ˣ) (t₁ : AdeleRing (𝓞 L) L),
      φ ((yv L x ra j)⁻¹ * globalPoints (𝓞 L) L t *
        sigmaAdelicAct K L D σ (unipotentGL2 t₁ * (centralScalar (𝓞 L) L w * yv L x ra j))) = 0 := by
    intro w t₁
    by_contra h
    exact hj ⟨w, t₁, h⟩
  constructor
  · unfold Atr
    simp only [h0, integral_zero, mul_zero]
  · unfold Ltr
    simp only [h0, enorm_zero, lintegral_zero, mul_zero]

open scoped Classical in

theorem main
    (hΩL : IsFundamentalDomain (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range ΩL νZL)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
        ξL ⟨z, Subgroup.mem_top z⟩ = 1)
    (hδ₀u : (δ₀ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) (hδ₀l : (δ₀ : Matrix (Fin 2) (Fin 2) L) 0 1 = 0)
    (hreg : Algebra.norm K ((δ₀ : Matrix (Fin 2) (Fin 2) L) 0 0 / (δ₀ : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1)
    (hI : ∀ δ, δ ∈ I ↔ ∃ g : GL (Fin 2) L,
      δ₀⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ∈ Subgroup.center (GL (Fin 2) L))
    (hΛ' : ∀ a : GL (Fin 2) L, a ∈ Λ' ↔ ((a : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (a : Matrix (Fin 2) (Fin 2) L) 0 1 = 0) ∧
      (a : Matrix (Fin 2) (Fin 2) L) 0 0 / (a : Matrix (Fin 2) (Fin 2) L) 1 1 ∈ Set.range (algebraMap K L))
    [Countable κ]
    (hrad : ∀ j, ((ra j : Matrix (Fin 2) (Fin 2) L)) 1 0 = 0 ∧ ((ra j : Matrix (Fin 2) (Fin 2) L)) 0 1 = 0)
    (hra : ∀ a : GL (Fin 2) L, ((a : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (a : Matrix (Fin 2) (Fin 2) L) 0 1 = 0) →
      ∃! j, (ra j)⁻¹ * a ∈ Λ')
    (hφc : Continuous φ) (hφs : HasCompactSupport φ) :
    (∑' j, (Lconj K L νZL D σ ξL φ δ₀ (yv L x ra j) + LconjW K L νZL D σ ξL φ δ₀ (yv L x ra j))) < ⊤ ∧
    IntegrableOn (fun z : (AdeleRing (𝓞 L) L)ˣ => ξf L ξL z *
        Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight L) (Real.exp R))
          (CTJ K L D σ φ x {γ : GL (Fin 2) L | (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ γ ∈ I})
          (centralScalar (𝓞 L) L z * x)) ΩL νZL ∧
    Summable (fun j => Aconj K L νZL D σ ξL φ δ₀ (yv L x ra j) + AconjW K L νZL D σ ξL φ δ₀ (yv L x ra j)) ∧
    ∫ z in ΩL, ξf L ξL z *
        Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight L) (Real.exp R))
          (CTJ K L D σ φ x {γ : GL (Fin 2) L | (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ γ ∈ I})
          (centralScalar (𝓞 L) L z * x) ∂νZL =
      Set.indicator {y : AdelicGL2 (𝓞 L) L | Real.exp R < NumberField.AdelicHeight.adelicHeight L y} (fun _ => (1 : ℂ)) x *
        ((if Algebra.norm K ((δ₀ : Matrix (Fin 2) (Fin 2) L) 0 0 / (δ₀ : Matrix (Fin 2) (Fin 2) L) 1 1) = -1
          then (1 / 2 : ℂ) else 1) * (((μA L (NumberField.AdelicBox.adelicBox L)).toReal⁻¹ : ℝ) : ℂ) *
          ∑' j, (Aconj K L νZL D σ ξL φ δ₀ (yv L x ra j) + AconjW K L νZL D σ ξL φ δ₀ (yv L x ra j))) := by
  classical
  haveI : FiniteDimensional K L := Module.Finite.of_restrictScalars_finite ℚ K L
  have hne := det_ne_zero_entries δ₀ hδ₀u

  set tw : GL (Fin 2) L := gl2Weyl * δ₀ * gl2Weyl⁻¹ with htw
  have htwval : ((tw : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) =
      !![(δ₀ : Matrix (Fin 2) (Fin 2) L) 1 1, 0; 0, (δ₀ : Matrix (Fin 2) (Fin 2) L) 0 0] :=
    gl2Weyl_conj_diag δ₀ hδ₀u hδ₀l
  have htw10 : ((tw : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 := by rw [htwval]; simp
  have htw01 : ((tw : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 0 1 = 0 := by rw [htwval]; simp
  have htw00 : ((tw : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 0 0 = (δ₀ : Matrix (Fin 2) (Fin 2) L) 1 1 := by
    rw [htwval]; simp
  have htw11 : ((tw : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 1 = (δ₀ : Matrix (Fin 2) (Fin 2) L) 0 0 := by
    rw [htwval]; simp
  have hregw : Algebra.norm K (((tw : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 0 0 /
      ((tw : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1 := by
    rw [htw00, htw11]
    exact norm_div_ne_one_symm hne.1 hne.2 hreg

  set J₁ : Set (GL (Fin 2) L) := {γ | ∃ b : GL (Fin 2) L, (b : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
    δ₀⁻¹ * (b⁻¹ * γ * Matrix.GeneralLinearGroup.map (σ : L →+* L) b) ∈ Subgroup.center (GL (Fin 2) L)} with hJ₁
  set J₂ : Set (GL (Fin 2) L) := {γ | ∃ b : GL (Fin 2) L, (b : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
    tw⁻¹ * (b⁻¹ * γ * Matrix.GeneralLinearGroup.map (σ : L →+* L) b) ∈ Subgroup.center (GL (Fin 2) L)} with hJ₂
  set Jset : Set (GL (Fin 2) L) := {γ | (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ γ ∈ I} with hJset
  obtain ⟨hunion, hdisj, hequal⟩ :=
    LT.TwistedNorm.setOf_exists_mem_center_inter_setOf_apply_one_zero_eq_zero_eq_union_and_disjoint
      hgen δ₀ tw hδ₀u hδ₀l hreg ⟨htw10, htw01⟩ htw00 htw11
  have hJU : Jset = J₁ ∪ J₂ := by
    rw [hJ₁, hJ₂, ← hunion, hJset]
    ext γ
    simp only [Set.mem_setOf_eq, hI]

  obtain ⟨hfin₁, hint₁, hIO₁, heq₁⟩ := brick K L νZL ΩL D σ ξL Λ' ra φ x hΩL hgen hξc hξt hΛ' hrad hra hφc hφs
    δ₀ hδ₀u hδ₀l hreg
  obtain ⟨hfin₂, hint₂, hIO₂, heq₂⟩ := brick K L νZL ΩL D σ ξL Λ' ra φ x hΩL hgen hξc hξt hΛ' hrad hra hφc hφs
    tw htw10 htw01 hregw
  have cov₁ := fun j => cov K L νZL D σ ξL φ hgen hξc hφc hφs δ₀ hδ₀u hδ₀l hreg (yv L x ra j)
  have cov₂ := fun j => cov K L νZL D σ ξL φ hgen hξc hφc hφs tw htw10 htw01 hregw (yv L x ra j)

  set F : Finset κ := (hfin₁.union hfin₂).toFinset with hF
  have hz₁ : ∀ j ∉ F, Atr K L νZL D σ ξL φ δ₀ (yv L x ra j) = 0 ∧ Ltr K L νZL D σ ξL φ δ₀ (yv L x ra j) = 0 := by
    intro j hj
    rw [hF, Set.Finite.mem_toFinset, Set.mem_union, not_or] at hj
    exact Atr_eq_zero_and_Ltr_eq_zero K L νZL D σ ξL ra φ x δ₀ hj.1
  have hz₂ : ∀ j ∉ F, Atr K L νZL D σ ξL φ tw (yv L x ra j) = 0 ∧ Ltr K L νZL D σ ξL φ tw (yv L x ra j) = 0 := by
    intro j hj
    rw [hF, Set.Finite.mem_toFinset, Set.mem_union, not_or] at hj
    exact Atr_eq_zero_and_Ltr_eq_zero K L νZL D σ ξL ra φ x tw hj.2
  have hsum₁ : Summable fun j => Atr K L νZL D σ ξL φ δ₀ (yv L x ra j) :=
    summable_of_ne_finset_zero (s := F) fun j hj => (hz₁ j hj).1
  have hsum₂ : Summable fun j => Atr K L νZL D σ ξL φ tw (yv L x ra j) :=
    summable_of_ne_finset_zero (s := F) fun j hj => (hz₂ j hj).1

  have hA : (fun j => Aconj K L νZL D σ ξL φ δ₀ (yv L x ra j) + AconjW K L νZL D σ ξL φ δ₀ (yv L x ra j)) =
      fun j => Atr K L νZL D σ ξL φ δ₀ (yv L x ra j) + Atr K L νZL D σ ξL φ tw (yv L x ra j) := by
    funext j
    rw [AconjW_eq, ← htw, (cov₁ j).2.2, (cov₂ j).2.2]
  have hLf : (fun j => Lconj K L νZL D σ ξL φ δ₀ (yv L x ra j) + LconjW K L νZL D σ ξL φ δ₀ (yv L x ra j)) =
      fun j => Ltr K L νZL D σ ξL φ δ₀ (yv L x ra j) + Ltr K L νZL D σ ξL φ tw (yv L x ra j) := by
    funext j
    rw [LconjW_eq, ← htw, (cov₁ j).1, (cov₂ j).1]

  set e1x : ℂ := Set.indicator {y : AdelicGL2 (𝓞 L) L | Real.exp R < NumberField.AdelicHeight.adelicHeight L y}
    (fun _ => (1 : ℂ)) x with he1x
  have hind : ∀ (f : AdelicGL2 (𝓞 L) L → ℂ) (z : (AdeleRing (𝓞 L) L)ˣ),
      Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)) f
        (centralScalar (𝓞 L) L z * x) = e1x * f (centralScalar (𝓞 L) L z * x) := by
    intro f z
    have hH : NumberField.AdelicHeight.adelicHeight L (centralScalar (𝓞 L) L z * x) =
        NumberField.AdelicHeight.adelicHeight L x :=
      (NumberField.AdelicHeight.adelicHeight_unipotentGL2_mul_and_centralScalar_mul L).2 z x
    by_cases hx : Real.exp R < NumberField.AdelicHeight.adelicHeight L x
    · rw [Set.indicator_of_mem (show centralScalar (𝓞 L) L z * x ∈
          AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight L) (Real.exp R) from
          AutomorphicForm.mem_highSet_iff.mpr (hH.symm ▸ hx)),
        he1x, Set.indicator_of_mem (show x ∈ {y : AdelicGL2 (𝓞 L) L |
          Real.exp R < NumberField.AdelicHeight.adelicHeight L y} from hx), one_mul]
    · rw [Set.indicator_of_notMem (show centralScalar (𝓞 L) L z * x ∉
          AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight L) (Real.exp R) from
          fun h => hx (hH ▸ AutomorphicForm.mem_highSet_iff.mp h)),
        he1x, Set.indicator_of_notMem (show x ∉ {y : AdelicGL2 (𝓞 L) L |
          Real.exp R < NumberField.AdelicHeight.adelicHeight L y} from hx), zero_mul]
  have hfun : (fun z : (AdeleRing (𝓞 L) L)ˣ => ξf L ξL z *
      Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight L) (Real.exp R))
        (CTJ K L D σ φ x Jset) (centralScalar (𝓞 L) L z * x)) =
      fun z => e1x * (ξf L ξL z * CTJ K L D σ φ x Jset (centralScalar (𝓞 L) L z * x)) := by
    funext z
    rw [hind, mul_left_comm]

  set Vinv : ℂ := ((μA L (NumberField.AdelicBox.adelicBox L)).toReal : ℂ)⁻¹ with hVinv
  have hVof : (((μA L (NumberField.AdelicBox.adelicBox L)).toReal⁻¹ : ℝ) : ℂ) = Vinv := by
    rw [hVinv, Complex.ofReal_inv]
  have hcore : IntegrableOn (fun z : (AdeleRing (𝓞 L) L)ˣ => ξf L ξL z * CTJ K L D σ φ x Jset (centralScalar (𝓞 L) L z * x)) ΩL νZL ∧
      ∫ z in ΩL, ξf L ξL z * CTJ K L D σ φ x Jset (centralScalar (𝓞 L) L z * x) ∂νZL =
        (if Algebra.norm K ((δ₀ : Matrix (Fin 2) (Fin 2) L) 0 0 / (δ₀ : Matrix (Fin 2) (Fin 2) L) 1 1) = -1
          then (1 / 2 : ℂ) else 1) * Vinv *
          ((∑' j, Atr K L νZL D σ ξL φ δ₀ (yv L x ra j)) + ∑' j, Atr K L νZL D σ ξL φ tw (yv L x ra j)) := by
    by_cases hN : Algebra.norm K ((δ₀ : Matrix (Fin 2) (Fin 2) L) 0 0 / (δ₀ : Matrix (Fin 2) (Fin 2) L) 1 1) = -1
    ·
      have hJ12 : J₁ = J₂ := hequal hN
      have hJs1 : Jset = J₁ := by rw [hJU, hJ12, Set.union_self]
      have hJs2 : Jset = J₂ := by rw [hJs1, hJ12]
      rw [if_pos hN]
      refine ⟨by rw [hJs1]; exact hIO₁, ?_⟩
      have e₁ : ∫ z in ΩL, ξf L ξL z * CTJ K L D σ φ x Jset (centralScalar (𝓞 L) L z * x) ∂νZL =
          Vinv * ∑' j, Atr K L νZL D σ ξL φ δ₀ (yv L x ra j) := by rw [hJs1]; exact heq₁
      have e₂ : ∫ z in ΩL, ξf L ξL z * CTJ K L D σ φ x Jset (centralScalar (𝓞 L) L z * x) ∂νZL =
          Vinv * ∑' j, Atr K L νZL D σ ξL φ tw (yv L x ra j) := by rw [hJs2]; exact heq₂
      linear_combination (1 / 2 : ℂ) * e₁ + (1 / 2 : ℂ) * e₂
    ·
      have hd : Disjoint J₁ J₂ := hdisj hN
      have hCT : ∀ z : (AdeleRing (𝓞 L) L)ˣ, CTJ K L D σ φ x Jset (centralScalar (𝓞 L) L z * x) =
          CTJ K L D σ φ x J₁ (centralScalar (𝓞 L) L z * x) + CTJ K L D σ φ x J₂ (centralScalar (𝓞 L) L z * x) := by
        intro z
        rw [CTJ_eq, CTJ_eq, CTJ_eq, ← integral_add (hint₁ z) (hint₂ z)]
        refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
        show KJ K L D σ φ x Jset _ = _
        rw [hJU]
        exact KJ_union K L D σ φ x hφs hd _
      have hf2 : (fun z : (AdeleRing (𝓞 L) L)ˣ => ξf L ξL z * CTJ K L D σ φ x Jset (centralScalar (𝓞 L) L z * x)) =
          fun z => ξf L ξL z * CTJ K L D σ φ x J₁ (centralScalar (𝓞 L) L z * x) +
            ξf L ξL z * CTJ K L D σ φ x J₂ (centralScalar (𝓞 L) L z * x) := by
        funext z
        rw [hCT, mul_add]
      rw [if_neg hN, hf2]
      refine ⟨hIO₁.add hIO₂, ?_⟩
      rw [integral_add hIO₁ hIO₂, heq₁, heq₂]
      ring
  obtain ⟨hIOJ, heqJ⟩ := hcore
  refine ⟨?_, ?_, ?_, ?_⟩
  ·
    rw [hLf, tsum_eq_sum (L := SummationFilter.unconditional κ) (s := F) ?_]
    · refine ENNReal.sum_lt_top.mpr fun j _ => ENNReal.add_lt_top.mpr ⟨(cov₁ j).2.1, (cov₂ j).2.1⟩
    · intro j hj
      rw [(hz₁ j hj).2, (hz₂ j hj).2, add_zero]
  ·
    rw [hfun]
    exact hIOJ.const_mul e1x
  ·
    rw [hA]
    exact hsum₁.add hsum₂
  ·
    rw [hfun, integral_const_mul, heqJ, hA, hsum₁.tsum_add hsum₂, hVof]

end Main

end R4C3aUnfold

end

section

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate
open AutomorphicForm

attribute [local instance] NumberField.AdelicHaar.glBorel

set_option maxHeartbeats 1600000 in
attribute [local instance] NumberField.AdelicHaar.adeleBorel in
open scoped TensorProduct.RightActions Classical in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ] (νZL : Measure (AdeleRing (𝓞 L) L)ˣ)
    [νZL.IsHaarMeasure] (ΩL : Set (AdeleRing (𝓞 L) L)ˣ)
    (hΩL : IsFundamentalDomain
      (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range ΩL νZL)
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
        ξL ⟨z, Subgroup.mem_top z⟩ = 1)
    (δ₀ : GL (Fin 2) L) (hδ₀u : (δ₀ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) (hδ₀l : (δ₀ : Matrix (Fin 2) (Fin 2) L) 0 1 = 0)
    (hreg : Algebra.norm K ((δ₀ : Matrix (Fin 2) (Fin 2) L) 0 0 / (δ₀ : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1)
    (I : Set (GL (Fin 2) L))
    (hI : ∀ δ, δ ∈ I ↔ ∃ g : GL (Fin 2) L,
      δ₀⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ∈ Subgroup.center (GL (Fin 2) L))
    (Λ : Subgroup (GL (Fin 2) L))
    (hΛ : ∀ γ, γ ∈ Λ ↔
      δ₀⁻¹ * (γ * δ₀ * (Matrix.GeneralLinearGroup.map (σ : L →+* L) γ)⁻¹) ∈ Subgroup.center (GL (Fin 2) L))
    {ι : Type} [Countable ι] (r : ι → GL (Fin 2) L) (hr : ∀ γ : GL (Fin 2) L, ∃! i, (r i)⁻¹ * γ ∈ Λ)
    (ΦL : Set (AdelicGL2 (𝓞 L) L))
    (Λ' : Subgroup (GL (Fin 2) L))
    (hΛ' : ∀ a : GL (Fin 2) L, a ∈ Λ' ↔ ((a : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (a : Matrix (Fin 2) (Fin 2) L) 0 1 = 0) ∧ (a : Matrix (Fin 2) (Fin 2) L) 0 0 / (a : Matrix (Fin 2) (Fin 2) L) 1 1 ∈ Set.range (algebraMap K L))
    {κ : Type} [Countable κ] (ra : κ → GL (Fin 2) L)
    (hrad : ∀ j, ((ra j : Matrix (Fin 2) (Fin 2) L)) 1 0 = 0 ∧ ((ra j : Matrix (Fin 2) (Fin 2) L)) 0 1 = 0)
    (hra : ∀ a : GL (Fin 2) L, ((a : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (a : Matrix (Fin 2) (Fin 2) L) 0 1 = 0) → ∃! j, (ra j)⁻¹ * a ∈ Λ')
    (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφc : Continuous φ) (hφs : HasCompactSupport φ)
    (x : AdelicGL2 (𝓞 L) L) (R : ℝ) :
    (∑' j, ((∫⁻ s : AdeleRing (𝓞 L) L, (∫⁻ z, ‖((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ₑ * ‖φ ((AutomorphicForm.unipotentGL2 s * ((AutomorphicForm.globalPoints (𝓞 L) L (ra j))⁻¹ * x))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ * AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * (AutomorphicForm.unipotentGL2 s * ((AutomorphicForm.globalPoints (𝓞 L) L (ra j))⁻¹ * x))))‖ₑ ∂νZL) ∂(adelicAddHaar (𝓞 L) L)) +
        (∫⁻ s : AdeleRing (𝓞 L) L, (∫⁻ z, ‖((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ₑ * ‖φ (((AutomorphicForm.adelicWeyl (𝓞 L) L)⁻¹ * AutomorphicForm.unipotentGL2 s * ((AutomorphicForm.globalPoints (𝓞 L) L (ra j))⁻¹ * x))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ * AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * ((AutomorphicForm.adelicWeyl (𝓞 L) L)⁻¹ * AutomorphicForm.unipotentGL2 s * ((AutomorphicForm.globalPoints (𝓞 L) L (ra j))⁻¹ * x))))‖ₑ ∂νZL) ∂(adelicAddHaar (𝓞 L) L)))) < ⊤ ∧
    IntegrableOn (fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
        Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)) (@AutomorphicForm.constantTerm _ (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L) (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _ (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L) (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν (fun t => AutomorphicForm.unipotentGL2 t) (fun y => ∑ᶠ δ ∈ {γ : GL (Fin 2) L | (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ γ ∈ I}, φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ * AutomorphicForm.sigmaAdelicAct K L D σ y))) (AutomorphicForm.centralScalar (𝓞 L) L z * x)) ΩL νZL ∧
    Summable (fun j => ((∫ s : AdeleRing (𝓞 L) L, (∫ z, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
          φ ((AutomorphicForm.unipotentGL2 s * ((AutomorphicForm.globalPoints (𝓞 L) L (ra j))⁻¹ * x))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ * AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * (AutomorphicForm.unipotentGL2 s * ((AutomorphicForm.globalPoints (𝓞 L) L (ra j))⁻¹ * x)))) ∂νZL) ∂(adelicAddHaar (𝓞 L) L)) +
          (∫ s : AdeleRing (𝓞 L) L, (∫ z, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
          φ (((AutomorphicForm.adelicWeyl (𝓞 L) L)⁻¹ * AutomorphicForm.unipotentGL2 s * ((AutomorphicForm.globalPoints (𝓞 L) L (ra j))⁻¹ * x))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ * AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * ((AutomorphicForm.adelicWeyl (𝓞 L) L)⁻¹ * AutomorphicForm.unipotentGL2 s * ((AutomorphicForm.globalPoints (𝓞 L) L (ra j))⁻¹ * x)))) ∂νZL) ∂(adelicAddHaar (𝓞 L) L)))) ∧
    ∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
        Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)) (@AutomorphicForm.constantTerm _ (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L) (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _ (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L) (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν (fun t => AutomorphicForm.unipotentGL2 t) (fun y => ∑ᶠ δ ∈ {γ : GL (Fin 2) L | (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ γ ∈ I}, φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ * AutomorphicForm.sigmaAdelicAct K L D σ y))) (AutomorphicForm.centralScalar (𝓞 L) L z * x) ∂νZL =
      Set.indicator {y : AdelicGL2 (𝓞 L) L | Real.exp R < NumberField.AdelicHeight.adelicHeight L y} (fun _ => (1 : ℂ)) x *
        ((if Algebra.norm K ((δ₀ : Matrix (Fin 2) (Fin 2) L) 0 0 / (δ₀ : Matrix (Fin 2) (Fin 2) L) 1 1) = -1
          then (1 / 2 : ℂ) else 1) * (((adelicAddHaar (𝓞 L) L (adelicBox L)).toReal⁻¹ : ℝ) : ℂ) *
          ∑' j, ((∫ s : AdeleRing (𝓞 L) L, (∫ z, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
          φ ((AutomorphicForm.unipotentGL2 s * ((AutomorphicForm.globalPoints (𝓞 L) L (ra j))⁻¹ * x))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ * AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * (AutomorphicForm.unipotentGL2 s * ((AutomorphicForm.globalPoints (𝓞 L) L (ra j))⁻¹ * x)))) ∂νZL) ∂(adelicAddHaar (𝓞 L) L)) +
          (∫ s : AdeleRing (𝓞 L) L, (∫ z, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
          φ (((AutomorphicForm.adelicWeyl (𝓞 L) L)⁻¹ * AutomorphicForm.unipotentGL2 s * ((AutomorphicForm.globalPoints (𝓞 L) L (ra j))⁻¹ * x))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ * AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * ((AutomorphicForm.adelicWeyl (𝓞 L) L)⁻¹ * AutomorphicForm.unipotentGL2 s * ((AutomorphicForm.globalPoints (𝓞 L) L (ra j))⁻¹ * x)))) ∂νZL) ∂(adelicAddHaar (𝓞 L) L)))) :=
  R4C3aUnfold.main K L νZL ΩL D σ ξL δ₀ I Λ' ra φ x R hΩL hgen hξc hξt hδ₀u hδ₀l hreg hI hΛ' hrad hra hφc hφs

end

end S_AutomorphicForm_setIntegral_mul_indicator_highSet_constantTerm_finsum_eq_indicator_mul_tsum_integral_unipotentGL2_twistedOrbital
end P2MW
export P2MW.S_AutomorphicForm_setIntegral_mul_indicator_highSet_constantTerm_finsum_eq_indicator_mul_tsum_integral_unipotentGL2_twistedOrbital (solution)
