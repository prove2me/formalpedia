-- Prove2me | solution 1 for AutomorphicForm.TwistedBruhat.integral_iwasawa_cuspKernel_sub_cuspTruncation_eq_integral_tsum_normOneFibre_of_fibrewise
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/e2b30136-d6cb-525f-b78d-1b9400e2506c

import Definitions.Def_AutomorphicForm_TwistedCuspKernel
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_AdelicTracePushforward
import Definitions.Def_AutomorphicForm_TransversalMeasure
import Definitions.Def_AutomorphicForm_AdelicKernel
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm
import Theorems.Thm_AutomorphicForm_continuous_unipotentGL2
import Theorems.Thm_AutomorphicForm_adelicKernelLocalFiniteness
import Theorems.Thm_NumberField_AdelicHeight_continuous_adelicHeight
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_TwistedBruhat_integral_iwasawa_cuspKernel_sub_cuspTruncation_eq_integral_tsum_normOneFibre_of_fibrewise
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open MeasureTheory NumberField
open scoped Pointwise ENNReal NNReal

noncomputable section

namespace R1IwCentre

open NumberField IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel NumberField.AdelicLevel NumberField.AdelicHeight

section Height

variable {K : Type*} [NormedField K]

theorem rowMaxNorm_scalar_entries_mul {s : GL (Fin 2) K} {z : K}
    (h10 : (s : Matrix (Fin 2) (Fin 2) K) 1 0 = 0) (h11 : (s : Matrix (Fin 2) (Fin 2) K) 1 1 = z)
    (g : GL (Fin 2) K) :
    rowMaxNorm ((s * g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      = ‖z‖ * rowMaxNorm (g : Matrix (Fin 2) (Fin 2) K) := by
  have hbot : ∀ j : Fin 2,
      ((s : Matrix (Fin 2) (Fin 2) K) * (g : Matrix (Fin 2) (Fin 2) K)) 1 j
        = z * (g : Matrix (Fin 2) (Fin 2) K) 1 j := by
    intro j
    rw [Matrix.mul_apply, Fin.sum_univ_two, h10, h11]
    ring
  unfold rowMaxNorm
  rw [Matrix.GeneralLinearGroup.coe_mul, hbot 0, hbot 1, norm_mul, norm_mul,
    mul_max_of_nonneg _ _ (norm_nonneg z)]
theorem finLocalHeight_scalar_entries_mul {s : GL (Fin 2) K} {z : K} (hz : z ≠ 0)
    (h00 : (s : Matrix (Fin 2) (Fin 2) K) 0 0 = z) (h01 : (s : Matrix (Fin 2) (Fin 2) K) 0 1 = 0)
    (h10 : (s : Matrix (Fin 2) (Fin 2) K) 1 0 = 0) (h11 : (s : Matrix (Fin 2) (Fin 2) K) 1 1 = z)
    (g : GL (Fin 2) K) :
    finLocalHeight (s * g) = finLocalHeight g := by
  have hdets : (s : Matrix (Fin 2) (Fin 2) K).det = z ^ 2 := by
    rw [Matrix.det_fin_two, h00, h01, h10, h11]; ring
  have hdet : ‖((s * g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det‖
      = ‖z‖ ^ 2 * ‖(g : Matrix (Fin 2) (Fin 2) K).det‖ := by
    rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.det_mul, hdets, norm_mul, norm_pow]
  have hz2 : (0 : ℝ) < ‖z‖ ^ 2 := pow_pos (norm_pos_iff.2 hz) 2
  unfold finLocalHeight
  rw [hdet, rowMaxNorm_scalar_entries_mul h10 h11 g, mul_pow,
    mul_div_mul_left _ _ hz2.ne']

variable (F : Type) [Field F] [NumberField F]

theorem adelicHeight_centralScalar_mul (z : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F) :
    adelicHeight F (centralScalar (𝓞 F) F z * g) = adelicHeight F g := by
  have hcoe : ∀ i j : Fin 2, ((centralScalar (𝓞 F) F z : AdelicGL2 (𝓞 F) F) :
      Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j = if i = j then (z : AdeleRing (𝓞 F) F) else 0 := by
    intro i j
    show Matrix.scalar (Fin 2) (z : AdeleRing (𝓞 F) F) i j = _
    rw [Matrix.scalar_apply, Matrix.diagonal_apply]
  unfold adelicHeight
  rw [map_mul, map_mul]
  congr 1
  · refine archHeight_scalar_entries_mul F (z := (z : AdeleRing (𝓞 F) F).1) (fun v => ?_) ?_ ?_ ?_ ?_ _
    · exact (Units.map ((archEval F v).comp (adeleArch (𝓞 F) F)).toMonoidHom z).ne_zero
    all_goals rw [glArch_apply, hcoe]; rfl
  · unfold finHeight
    refine finprod_congr fun v => ?_
    rw [map_mul]
    refine finLocalHeight_scalar_entries_mul (z := ((z : AdeleRing (𝓞 F) F).2) v) ?_ ?_ ?_ ?_ ?_ _
    · exact (Units.map ((finAdeleEval (𝓞 F) F v).comp (adeleFin (𝓞 F) F)).toMonoidHom z).ne_zero
    all_goals rw [finComponent_apply, glFin_apply, hcoe]; rfl

end Height

end R1IwCentre

open Polynomial

namespace R1IwCentre

section Cells

open AutomorphicForm

variable {K : Type*} [Field K]

theorem X_sub_C_sq (a : K) : ((X - C a) ^ 2 : K[X]) = X ^ 2 - C (2 * a) * X + C (a ^ 2) := by
  rw [map_mul, map_pow, show (C (2 : K)) = 2 from map_ofNat C 2]; ring
theorem trace_det_of_charpoly_eq {M : Matrix (Fin 2) (Fin 2) K} {a : K} (h : M.charpoly = (X - C a) ^ 2) :
    M.trace = 2 * a ∧ M.det = a ^ 2 := by
  rw [Matrix.charpoly_fin_two, X_sub_C_sq] at h
  have h1 := congrArg (fun p : K[X] => p.coeff 1) h
  have h0 := congrArg (fun p : K[X] => p.coeff 0) h
  simp only [coeff_add, coeff_sub, coeff_X_pow, coeff_C_mul, coeff_X_one, coeff_C, if_true,
    mul_one] at h1 h0
  norm_num at h1 h0
  exact ⟨h1, h0⟩
theorem isCentralType_smul_iff {M : Matrix (Fin 2) (Fin 2) K} {t : K} (ht : t ≠ 0) :
    IsCentralType (t • M) ↔ IsCentralType M := by
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨t⁻¹ * c, ?_⟩
    have := congrArg (fun N : Matrix (Fin 2) (Fin 2) K => t⁻¹ • N) hc
    simpa only [smul_smul, inv_mul_cancel₀ ht, one_smul] using this
  · rintro ⟨c, rfl⟩
    exact ⟨t * c, by rw [smul_smul]⟩
theorem isUnipotentType_smul {M : Matrix (Fin 2) (Fin 2) K} {t : K} (ht : t ≠ 0) (h : IsUnipotentType M) :
    IsUnipotentType (t • M) := by
  obtain ⟨hnc, a, ha⟩ := h
  obtain ⟨htr, hdet⟩ := trace_det_of_charpoly_eq ha
  refine ⟨(isCentralType_smul_iff ht).not.mpr hnc, t * a, ?_⟩
  rw [Matrix.charpoly_fin_two, Matrix.trace_smul, Matrix.det_smul, Fintype.card_fin, htr, hdet, X_sub_C_sq,
    smul_eq_mul]
  congr 2 <;> [(congr 2; ring); (congr 1; ring)]
theorem isUnipotentType_smul_iff {M : Matrix (Fin 2) (Fin 2) K} {t : K} (ht : t ≠ 0) :
    IsUnipotentType (t • M) ↔ IsUnipotentType M := by
  refine ⟨fun h => ?_, isUnipotentType_smul ht⟩
  have := isUnipotentType_smul (inv_ne_zero ht) h
  rwa [smul_smul, inv_mul_cancel₀ ht, one_smul] at this
theorem coe_mul_scalar (γ : GL (Fin 2) K) (t : Kˣ) :
    ((γ * Matrix.GeneralLinearGroup.scalar (Fin 2) t : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      (t : K) • (γ : Matrix (Fin 2) (Fin 2) K) := by
  rw [Matrix.GeneralLinearGroup.coe_mul]
  show (γ : Matrix (Fin 2) (Fin 2) K) * Matrix.scalar (Fin 2) (t : K) = _
  rw [← (Matrix.scalar_commute (t : K) (fun r' => mul_comm _ r') _).eq, Matrix.scalar_apply,
    ← Matrix.smul_eq_diagonal_mul]
theorem mul_scalar_mem_unipotentCell_iff (γ : GL (Fin 2) K) (t : Kˣ) :
    γ * Matrix.GeneralLinearGroup.scalar (Fin 2) t ∈ unipotentCell K ↔ γ ∈ unipotentCell K := by
  rw [mem_unipotentCell_iff, mem_unipotentCell_iff, coe_mul_scalar]
  exact isUnipotentType_smul_iff t.ne_zero

end Cells

section NormClasses

open LT.TwistedNorm AutomorphicForm

theorem sigmaPartialNorm_mul_of_mem_center {G : Type*} [Group G] (σ : G →* G) (x : G) {y : G}
    (hy : y ∈ Subgroup.center G) (r : ℕ) :
    sigmaPartialNorm σ (x * y) r = sigmaPartialNorm σ x r * sigmaPartialNorm σ y r := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [sigmaPartialNorm_succ', sigmaPartialNorm_succ', sigmaPartialNorm_succ', ih, map_mul]
      have hc := Subgroup.mem_center_iff.mp hy (σ (sigmaPartialNorm σ x r))
      calc x * y * (σ (sigmaPartialNorm σ x r) * σ (sigmaPartialNorm σ y r))
          = x * (y * σ (sigmaPartialNorm σ x r)) * σ (sigmaPartialNorm σ y r) := by group
        _ = x * (σ (sigmaPartialNorm σ x r) * y) * σ (sigmaPartialNorm σ y r) := by rw [hc]
        _ = x * σ (sigmaPartialNorm σ x r) * (y * σ (sigmaPartialNorm σ y r)) := by group

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

theorem scalar_mem_center (s : Lˣ) : Matrix.GeneralLinearGroup.scalar (Fin 2) s ∈ Subgroup.center (GL (Fin 2) L) := by
  rw [Subgroup.mem_center_iff]
  intro g
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul]
  exact congrFun (congrFun (Matrix.scalar_commute (n := Fin 2) (s : L) (fun r' => mul_comm _ r')
    (g : Matrix (Fin 2) (Fin 2) L)).eq i) j |>.symm

theorem map_scalar {R S : Type*} [CommRing R] [CommRing S] (σ : R →+* S) (s : Rˣ) :
    Matrix.GeneralLinearGroup.map σ (Matrix.GeneralLinearGroup.scalar (Fin 2) s) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (σ : R →* S) s) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  show σ (Matrix.scalar (Fin 2) (s : R) i j) = Matrix.scalar (Fin 2) (σ (s : R)) i j
  rw [Matrix.scalar_apply, Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.diagonal_apply]
  split_ifs <;> simp

theorem map_algebraMap_scalar (t : Kˣ) :
    Matrix.GeneralLinearGroup.map (algebraMap K L) (Matrix.GeneralLinearGroup.scalar (Fin 2) t) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (algebraMap K L : K →* L) t) :=
  map_scalar (algebraMap K L) t

variable [FiniteDimensional K L] [IsGalois K L]

theorem sigmaNormPow_mul_scalar {σ : L ≃ₐ[K] L} (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (δ : GL (Fin 2) L) (s : Lˣ) :
    sigmaNormPow (Matrix.GeneralLinearGroup.map (σ : L →+* L)) (Module.finrank K L)
        (δ * Matrix.GeneralLinearGroup.scalar (Fin 2) s) =
      sigmaNormPow (Matrix.GeneralLinearGroup.map (σ : L →+* L)) (Module.finrank K L) δ *
        Matrix.GeneralLinearGroup.map (algebraMap K L)
          (Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (Algebra.norm K : L →* K) s)) := by
  rw [sigmaNormPow_def, sigmaPartialNorm_mul_of_mem_center _ _ (scalar_mem_center s), ← sigmaNormPow_def,
    ← sigmaNormPow_def]
  congr 1
  have h := hom_sigmaNormPow (Units.map ((σ : L →+* L) : L →* L)) (Matrix.GeneralLinearGroup.map (σ : L →+* L))
    (Matrix.GeneralLinearGroup.scalar (Fin 2)) (fun x => (map_scalar (σ : L →+* L) x).symm) (Module.finrank K L) s
  rw [← h, map_algebraMap_scalar]
  congr 1
  ext
  rw [coe_sigmaNormPow_units_eq_algebraMap_norm hgen]
  rfl

omit [FiniteDimensional K L] [IsGalois K L] in
theorem isNormRep_of_isConj {σ : L ≃ₐ[K] L} {γ γ' : GL (Fin 2) K} {δ : GL (Fin 2) L}
    (h : IsNormRep σ γ δ) (hc : IsConj γ γ') : IsNormRep σ γ' δ := by
  obtain ⟨P, hP⟩ := h
  obtain ⟨c, rfl⟩ := isConj_iff.mp hc
  refine ⟨P * Matrix.GeneralLinearGroup.map (algebraMap K L) c⁻¹, ?_⟩
  rw [map_mul, map_mul, ← hP, map_inv]
  group

omit [FiniteDimensional K L] [IsGalois K L] in
theorem isNormRep_mul_scalar {σ : L ≃ₐ[K] L} (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    [FiniteDimensional K L] [IsGalois K L]
    {γ : GL (Fin 2) K} {δ : GL (Fin 2) L} (h : IsNormRep σ γ δ) (s : Lˣ) :
    IsNormRep σ (γ * Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (Algebra.norm K : L →* K) s))
      (δ * Matrix.GeneralLinearGroup.scalar (Fin 2) s) := by
  obtain ⟨P, hP⟩ := h
  refine ⟨P, ?_⟩
  rw [sigmaNormPow_mul_scalar hgen, map_mul, ← hP]
  have hc := Subgroup.mem_center_iff.mp
    (scalar_mem_center (Units.map (algebraMap K L : K →* L) (Units.map (Algebra.norm K : L →* K) s))) P
  rw [← map_algebraMap_scalar] at hc
  simp only [mul_assoc, hc]

theorem sigmaPartialNorm_upper (σ : L ≃ₐ[K] L) (δ : GL (Fin 2) L) (d₀ d₁ : Lˣ)
    (h10 : (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) (h00 : (δ : Matrix (Fin 2) (Fin 2) L) 0 0 = d₀)
    (h11 : (δ : Matrix (Fin 2) (Fin 2) L) 1 1 = d₁) (r : ℕ) :
    ((sigmaPartialNorm (Matrix.GeneralLinearGroup.map (σ : L →+* L)) δ r : GL (Fin 2) L) :
        Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
    ((sigmaPartialNorm (Matrix.GeneralLinearGroup.map (σ : L →+* L)) δ r : GL (Fin 2) L) :
        Matrix (Fin 2) (Fin 2) L) 0 0 = (sigmaPartialNorm (Units.map ((σ : L →+* L) : L →* L)) d₀ r : Lˣ) ∧
    ((sigmaPartialNorm (Matrix.GeneralLinearGroup.map (σ : L →+* L)) δ r : GL (Fin 2) L) :
        Matrix (Fin 2) (Fin 2) L) 1 1 = (sigmaPartialNorm (Units.map ((σ : L →+* L) : L →* L)) d₁ r : Lˣ) := by
  induction r with
  | zero =>
      simp only [sigmaPartialNorm_zero, Matrix.GeneralLinearGroup.coe_one, Units.val_one]
      exact ⟨Matrix.one_apply_ne (by decide), Matrix.one_apply_eq 0, Matrix.one_apply_eq 1⟩
  | succ r ih =>
      obtain ⟨i10, i00, i11⟩ := ih
      set M := (sigmaPartialNorm (Matrix.GeneralLinearGroup.map (σ : L →+* L)) δ r : GL (Fin 2) L) with hM
      have hmap : ∀ i j, ((Matrix.GeneralLinearGroup.map (σ : L →+* L) M : GL (Fin 2) L) :
          Matrix (Fin 2) (Fin 2) L) i j = σ ((M : Matrix (Fin 2) (Fin 2) L) i j) := fun i j => rfl
      have hmul : ∀ i j, ((sigmaPartialNorm (Matrix.GeneralLinearGroup.map (σ : L →+* L)) δ (r + 1) :
          GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) i j =
            (δ : Matrix (Fin 2) (Fin 2) L) i 0 * σ ((M : Matrix (Fin 2) (Fin 2) L) 0 j) +
              (δ : Matrix (Fin 2) (Fin 2) L) i 1 * σ ((M : Matrix (Fin 2) (Fin 2) L) 1 j) := by
        intro i j
        rw [sigmaPartialNorm_succ', Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, ← hM,
          hmap, hmap]
      have hu : ∀ d : Lˣ, ((sigmaPartialNorm (Units.map ((σ : L →+* L) : L →* L)) d (r + 1) : Lˣ) : L) =
          (d : L) * σ ((sigmaPartialNorm (Units.map ((σ : L →+* L) : L →* L)) d r : Lˣ) : L) := fun d => rfl
      refine ⟨?_, ?_, ?_⟩
      · rw [hmul, h10, i10, zero_mul, map_zero, mul_zero, add_zero]
      · rw [hmul, i10, map_zero, mul_zero, add_zero, h00, i00, hu]
      · rw [hmul, h10, zero_mul, zero_add, h11, i11, hu]

theorem norm_div_eq_one_of_isNormRep_of_upper {σ : L ≃ₐ[K] L} (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    {γ : GL (Fin 2) K} (hγ : γ ∈ unipotentCell K) {δ : GL (Fin 2) L} (hrep : IsNormRep σ γ δ)
    (h10 : (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) :
    Algebra.norm K ((δ : Matrix (Fin 2) (Fin 2) L) 0 0 / (δ : Matrix (Fin 2) (Fin 2) L) 1 1) = 1 := by
  have hdet : (δ : Matrix (Fin 2) (Fin 2) L).det ≠ 0 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply]; exact (Matrix.GeneralLinearGroup.det δ).ne_zero
  rw [Matrix.det_fin_two, h10, mul_zero, sub_zero] at hdet
  have h0 : (δ : Matrix (Fin 2) (Fin 2) L) 0 0 ≠ 0 := left_ne_zero_of_mul hdet
  have h1 : (δ : Matrix (Fin 2) (Fin 2) L) 1 1 ≠ 0 := right_ne_zero_of_mul hdet
  set d₀ : Lˣ := Units.mk0 _ h0 with hd₀
  set d₁ : Lˣ := Units.mk0 _ h1 with hd₁
  obtain ⟨n10, n00, n11⟩ := sigmaPartialNorm_upper σ δ d₀ d₁ h10 rfl rfl (Module.finrank K L)
  rw [← sigmaNormPow_def] at n10
  rw [← sigmaNormPow_def, ← sigmaNormPow_def, coe_sigmaNormPow_units_eq_algebraMap_norm hgen] at n00 n11
  obtain ⟨P, hP⟩ := hrep
  obtain ⟨_, a, ha⟩ := (mem_unipotentCell_iff.mp hγ)
  have hchar := charpoly_map_eq_charpoly_of_conj_eq_map hP
  rw [ha, Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C] at hchar
  obtain ⟨htr, hdt⟩ := trace_det_of_charpoly_eq hchar.symm
  rw [Matrix.trace_fin_two, n00, n11] at htr
  rw [Matrix.det_fin_two, n00, n11, n10, mul_zero, sub_zero] at hdt

  set A := algebraMap K L (Algebra.norm K (d₀ : L))
  set B := algebraMap K L (Algebra.norm K (d₁ : L))
  have hsq : (A - B) ^ 2 = 0 := by
    have : (A - B) ^ 2 = (A + B) ^ 2 - 4 * (A * B) := by ring
    rw [this, htr, hdt]; ring
  have hAB : A = B := sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp hsq)
  have hN : Algebra.norm K (d₀ : L) = Algebra.norm K (d₁ : L) := (algebraMap K L).injective hAB
  have hd₁N : Algebra.norm K (d₁ : L) ≠ 0 := Algebra.norm_ne_zero_iff.mpr d₁.ne_zero
  show Algebra.norm K ((d₀ : L) / (d₁ : L)) = 1
  have h := map_mul (Algebra.norm K) ((d₀ : L) / (d₁ : L)) (d₁ : L)
  rw [div_mul_cancel₀ _ d₁.ne_zero, hN] at h
  exact (mul_eq_right₀ hd₁N).mp h.symm

end NormClasses

section CuspIndex

open LT.TwistedNorm AutomorphicForm AutomorphicForm.TwistedBruhat

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]

theorem mul_scalar_mem_normUnipotentSet {σ : L ≃ₐ[K] L} (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    {δ : GL (Fin 2) L} (hδ : δ ∈ normUnipotentSet K L σ hgen) (s : Lˣ) :
    δ * Matrix.GeneralLinearGroup.scalar (Fin 2) s ∈ normUnipotentSet K L σ hgen := by
  obtain ⟨γ, hγ, hcls⟩ := hδ
  rw [normClassMap_mk, ConjClasses.mk_eq_mk_iff_isConj] at hcls
  have hrep : IsNormRep σ γ δ := isNormRep_of_isConj (isNormRep_normRep hgen δ) hcls
  refine ⟨_, ?_, normClassMap_mk_eq_of_isNormRep hgen (isNormRep_mul_scalar hgen hrep s)⟩
  exact (mul_scalar_mem_unipotentCell_iff γ _).mpr hγ

theorem norm_div_eq_one_of_mem_normUnipotentSet {σ : L ≃ₐ[K] L} (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    {δ : GL (Fin 2) L} (hδ : δ ∈ normUnipotentSet K L σ hgen) (h10 : (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) :
    Algebra.norm K ((δ : Matrix (Fin 2) (Fin 2) L) 0 0 / (δ : Matrix (Fin 2) (Fin 2) L) 1 1) = 1 := by
  obtain ⟨γ, hγ, hcls⟩ := hδ
  rw [normClassMap_mk, ConjClasses.mk_eq_mk_iff_isConj] at hcls
  exact norm_div_eq_one_of_isNormRep_of_upper hgen hγ (isNormRep_of_isConj (isNormRep_normRep hgen δ) hcls) h10

end CuspIndex

end R1IwCentre

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicBox
open IsDedekindDomain AutomorphicForm
open scoped Pointwise

namespace R1IwCentre

section AdelicAlgebra

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
variable (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)

theorem sigmaAdelicAct_centralScalar (z : (AdeleRing (𝓞 L) L)ˣ) :
    sigmaAdelicAct K L D σ (centralScalar (𝓞 L) L z) = centralScalar (𝓞 L) L (D.unitsAct σ z) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  change ((D.act σ : RingAut (AdeleRing (𝓞 L) L)).toRingHom) (Matrix.scalar (Fin 2) (z : AdeleRing (𝓞 L) L) i j) =
    Matrix.scalar (Fin 2) ((D.act σ : RingAut (AdeleRing (𝓞 L) L)) (z : AdeleRing (𝓞 L) L)) i j
  rw [Matrix.scalar_apply, Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.diagonal_apply]
  split_ifs <;> simp
theorem centralScalar_comm (w : (AdeleRing (𝓞 L) L)ˣ) (y : AdelicGL2 (𝓞 L) L) :
    centralScalar (𝓞 L) L w * y = y * centralScalar (𝓞 L) L w := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul]
  exact congrFun (congrFun (Matrix.scalar_commute (w : AdeleRing (𝓞 L) L) (fun r' => mul_comm _ r')
    (y : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L))).eq i) j
theorem mul_cs_left (g y : AdelicGL2 (𝓞 L) L) (w : (AdeleRing (𝓞 L) L)ˣ) :
    g * (centralScalar (𝓞 L) L w * y) = centralScalar (𝓞 L) L w * (g * y) := by
  rw [← mul_assoc, ← centralScalar_comm, mul_assoc]
theorem centralScalar_principal (q : Lˣ) :
    centralScalar (𝓞 L) L (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) q) =
      globalPoints (𝓞 L) L (Matrix.GeneralLinearGroup.scalar (Fin 2) q) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  show Matrix.scalar (Fin 2) (algebraMap L (AdeleRing (𝓞 L) L) (q : L)) i j =
    algebraMap L (AdeleRing (𝓞 L) L) (Matrix.scalar (Fin 2) (q : L) i j)
  rw [Matrix.scalar_apply, Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.diagonal_apply]
  split_ifs <;> simp
theorem unitsAct_principal (q : Lˣ) :
    D.unitsAct σ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) q) =
      Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) (Units.map (σ : L →* L) q) :=
  Units.ext (D.compat σ (q : L))
theorem sigmaAdelicAct_centralScalar_principal (q : Lˣ) :
    sigmaAdelicAct K L D σ (centralScalar (𝓞 L) L (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) q)) =
      globalPoints (𝓞 L) L (Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (σ : L →* L) q)) := by
  rw [sigmaAdelicAct_centralScalar, unitsAct_principal, centralScalar_principal]

end AdelicAlgebra

end R1IwCentre

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicBox NumberField.AdelicLevel
open IsDedekindDomain AutomorphicForm
open scoped Pointwise ENNReal

namespace R1IwCentre

section Fibres

open AutomorphicForm.TwistedBruhat NumberField.AdelicHeight

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
variable (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
variable (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)

def Iset (s : Lˣ) (a : {α : Lˣ // Algebra.norm K (α : L) = 1}) : Set (GL (Fin 2) L) :=
  {δ : GL (Fin 2) L | δ ∈ TwistedBruhat.normUnipotentSet K L σ hgen ∧
    (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (δ : Matrix (Fin 2) (Fin 2) L) 1 1 = (s : L) ∧
    (δ : Matrix (Fin 2) (Fin 2) L) 0 0 = (s : L) * ((a : Lˣ) : L)}

def Jset (s : Lˣ) (a : {α : Lˣ // Algebra.norm K (α : L) = 1}) : Set (GL (Fin 2) L) :=
  {δ : GL (Fin 2) L |
    (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (δ : Matrix (Fin 2) (Fin 2) L) 1 1 = (s : L) ∧
    (δ : Matrix (Fin 2) (Fin 2) L) 0 0 = (s : L) * ((a : Lˣ) : L)}

def I1 (a : {α : Lˣ // Algebra.norm K (α : L) = 1}) : Set (GL (Fin 2) L) :=
  {δ : GL (Fin 2) L | δ ∈ TwistedBruhat.normUnipotentSet K L σ hgen ∧
    (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (δ : Matrix (Fin 2) (Fin 2) L) 1 1 = 1 ∧
    (δ : Matrix (Fin 2) (Fin 2) L) 0 0 = ((a : Lˣ) : L)}

def J1 (a : {α : Lˣ // Algebra.norm K (α : L) = 1}) : Set (GL (Fin 2) L) :=
  {δ : GL (Fin 2) L |
    (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (δ : Matrix (Fin 2) (Fin 2) L) 1 1 = 1 ∧
    (δ : Matrix (Fin 2) (Fin 2) L) 0 0 = ((a : Lˣ) : L)}

theorem Iset_one (a : {α : Lˣ // Algebra.norm K (α : L) = 1}) : Iset K L σ hgen 1 a = I1 K L σ hgen a := by
  ext δ; simp only [Iset, I1, Set.mem_setOf_eq, Units.val_one, one_mul]

theorem Jset_one (a : {α : Lˣ // Algebra.norm K (α : L) = 1}) : Jset K L 1 a = J1 K L a := by
  ext δ; simp only [Jset, J1, Set.mem_setOf_eq, Units.val_one, one_mul]

def Kgen (T : Set (GL (Fin 2) L)) (φ : AdelicGL2 (𝓞 L) L → ℂ) (z : (AdeleRing (𝓞 L) L)ˣ) (g : AdelicGL2 (𝓞 L) L) : ℂ :=
  ∑ᶠ δ ∈ T, φ (g⁻¹ * globalPoints (𝓞 L) L δ * sigmaAdelicAct K L D σ (centralScalar (𝓞 L) L z * g))

def Tgen (T : Set (GL (Fin 2) L)) (R : ℝ) (φ : AdelicGL2 (𝓞 L) L → ℂ) (z : (AdeleRing (𝓞 L) L)ˣ)
    (g : AdelicGL2 (𝓞 L) L) : ℂ :=
  Set.indicator (highSet (adelicHeight L) (Real.exp R))
    (@constantTerm _ (adeleBorel (𝓞 L) L) _ _
      (@ProbabilityTheory.cond _ (adeleBorel (𝓞 L) L) (adelicAddHaar (𝓞 L) L) (adelicBox L))
      (fun t => unipotentGL2 t)
      (fun y => ∑ᶠ δ ∈ T, φ (g⁻¹ * globalPoints (𝓞 L) L δ * sigmaAdelicAct K L D σ y)))
    (centralScalar (𝓞 L) L z * g)

theorem mul_scalar_apply (δ : GL (Fin 2) L) (c : Lˣ) (i j : Fin 2) :
    ((δ * Matrix.GeneralLinearGroup.scalar (Fin 2) c : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) i j =
      (δ : Matrix (Fin 2) (Fin 2) L) i j * (c : L) := by
  rw [coe_mul_scalar, Matrix.smul_apply, smul_eq_mul, mul_comm]

theorem bijOn_mul_scalar_Iset (s c : Lˣ) (a : {α : Lˣ // Algebra.norm K (α : L) = 1}) :
    Set.BijOn (fun δ : GL (Fin 2) L => δ * Matrix.GeneralLinearGroup.scalar (Fin 2) c)
      (Iset K L σ hgen s a) (Iset K L σ hgen (s * c) a) := by
  have hmaps : ∀ (s c : Lˣ), Set.MapsTo (fun δ : GL (Fin 2) L => δ * Matrix.GeneralLinearGroup.scalar (Fin 2) c)
      (Iset K L σ hgen s a) (Iset K L σ hgen (s * c) a) := by
    intro s c δ hδ
    obtain ⟨h1, h2, h3, h4⟩ := hδ
    refine ⟨mul_scalar_mem_normUnipotentSet hgen h1 c, ?_, ?_, ?_⟩
    · rw [mul_scalar_apply, h2, zero_mul]
    · rw [mul_scalar_apply, h3, Units.val_mul]
    · rw [mul_scalar_apply, h4, Units.val_mul]; ring
  refine ⟨hmaps s c, fun δ _ δ' _ h => mul_right_cancel h, fun δ hδ => ?_⟩
  refine ⟨δ * Matrix.GeneralLinearGroup.scalar (Fin 2) c⁻¹, ?_, by simp only [map_inv, inv_mul_cancel_right]⟩
  have h := hmaps (s * c) c⁻¹ hδ
  rwa [mul_inv_cancel_right] at h

theorem bijOn_mul_scalar_Jset (s c : Lˣ) (a : {α : Lˣ // Algebra.norm K (α : L) = 1}) :
    Set.BijOn (fun δ : GL (Fin 2) L => δ * Matrix.GeneralLinearGroup.scalar (Fin 2) c)
      (Jset K L s a) (Jset K L (s * c) a) := by
  have hmaps : ∀ (s c : Lˣ), Set.MapsTo (fun δ : GL (Fin 2) L => δ * Matrix.GeneralLinearGroup.scalar (Fin 2) c)
      (Jset K L s a) (Jset K L (s * c) a) := by
    intro s c δ hδ
    obtain ⟨h2, h3, h4⟩ := hδ
    refine ⟨?_, ?_, ?_⟩
    · rw [mul_scalar_apply, h2, zero_mul]
    · rw [mul_scalar_apply, h3, Units.val_mul]
    · rw [mul_scalar_apply, h4, Units.val_mul]; ring
  refine ⟨hmaps s c, fun δ _ δ' _ h => mul_right_cancel h, fun δ hδ => ?_⟩
  refine ⟨δ * Matrix.GeneralLinearGroup.scalar (Fin 2) c⁻¹, ?_, by simp only [map_inv, inv_mul_cancel_right]⟩
  have h := hmaps (s * c) c⁻¹ hδ
  rwa [mul_inv_cancel_right] at h

theorem Kgen_Iset_principal_mul (φ : AdelicGL2 (𝓞 L) L → ℂ) (q : Lˣ) (z : (AdeleRing (𝓞 L) L)ˣ)
    (g : AdelicGL2 (𝓞 L) L) (s : Lˣ) (a : {α : Lˣ // Algebra.norm K (α : L) = 1}) :
    Kgen K L D σ (Iset K L σ hgen s a) φ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) q * z) g =
      Kgen K L D σ (Iset K L σ hgen (s * Units.map (σ : L →* L) q) a) φ z g := by
  unfold Kgen
  refine finsum_mem_eq_of_bijOn _ (bijOn_mul_scalar_Iset K L σ hgen s (Units.map (σ : L →* L) q) a) fun δ _ => ?_
  rw [map_mul (centralScalar (𝓞 L) L), mul_assoc (centralScalar (𝓞 L) L _), map_mul (sigmaAdelicAct K L D σ),
    sigmaAdelicAct_centralScalar_principal, map_mul (globalPoints (𝓞 L) L)]
  simp only [mul_assoc]

theorem Tgen_Jset_principal_mul (R : ℝ) (φ : AdelicGL2 (𝓞 L) L → ℂ) (q : Lˣ) (z : (AdeleRing (𝓞 L) L)ˣ)
    (g : AdelicGL2 (𝓞 L) L) (s : Lˣ) (a : {α : Lˣ // Algebra.norm K (α : L) = 1}) :
    Tgen K L D σ (Jset K L s a) R φ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) q * z) g =
      Tgen K L D σ (Jset K L (s * Units.map (σ : L →* L) q) a) R φ z g := by
  unfold Tgen
  have hmem : centralScalar (𝓞 L) L (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) q * z) * g ∈
        highSet (adelicHeight L) (Real.exp R) ↔
      centralScalar (𝓞 L) L z * g ∈ highSet (adelicHeight L) (Real.exp R) := by
    rw [mem_highSet_iff, mem_highSet_iff, map_mul, mul_assoc, adelicHeight_centralScalar_mul,
      adelicHeight_centralScalar_mul]
  by_cases hx : centralScalar (𝓞 L) L z * g ∈ highSet (adelicHeight L) (Real.exp R)
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (hmem.mpr hx)]
    unfold constantTerm constantTermIntegrand
    refine integral_congr_ae (Filter.Eventually.of_forall fun n => ?_)
    show (∑ᶠ δ ∈ Jset K L s a, φ (g⁻¹ * globalPoints (𝓞 L) L δ * sigmaAdelicAct K L D σ
        (unipotentGL2 n * (centralScalar (𝓞 L) L (Units.map _ q * z) * g)))) =
      ∑ᶠ δ ∈ Jset K L (s * Units.map (σ : L →* L) q) a, φ (g⁻¹ * globalPoints (𝓞 L) L δ * sigmaAdelicAct K L D σ
        (unipotentGL2 n * (centralScalar (𝓞 L) L z * g)))
    rw [map_mul (centralScalar (𝓞 L) L), mul_assoc (centralScalar (𝓞 L) L _), mul_cs_left]
    refine finsum_mem_eq_of_bijOn _ (bijOn_mul_scalar_Jset K L s (Units.map (σ : L →* L) q) a) fun δ _ => ?_
    rw [map_mul (sigmaAdelicAct K L D σ), sigmaAdelicAct_centralScalar_principal, map_mul (globalPoints (𝓞 L) L)]
    simp only [mul_assoc]
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun h' => hx (hmem.mp h'))]

def Gfun (R : ℝ) (φ : AdelicGL2 (𝓞 L) L → ℂ) (z : (AdeleRing (𝓞 L) L)ˣ) (g : AdelicGL2 (𝓞 L) L) : ℝ≥0∞ :=
  ∑' s : Lˣ, ∑' a : {α : Lˣ // Algebra.norm K (α : L) = 1},
    ‖Kgen K L D σ (Iset K L σ hgen s a) φ z g - Tgen K L D σ (Jset K L s a) R φ z g‖ₑ

end Fibres

section Small

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
variable (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
variable (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)

theorem countable_units : Countable Lˣ := by
  haveI : Countable L := (Module.Free.chooseBasis ℚ L).equivFun.toEquiv.countable_iff.2 inferInstance
  exact Function.Injective.countable (f := (Units.val : Lˣ → L)) Units.val_injective
def toTop (G : Type*) [Group G] : G →* (⊤ : Subgroup G) where
  toFun z := ⟨z, Subgroup.mem_top z⟩
  map_one' := rfl
  map_mul' _ _ := rfl
def prin (s : Lˣ) : (AdeleRing (𝓞 L) L)ˣ :=
  Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) (Units.map ((σ.symm : L ≃ₐ[K] L) : L →* L) s)
theorem one_mul_map_symm (s : Lˣ) : 1 * Units.map (σ : L →* L) (Units.map ((σ.symm : L ≃ₐ[K] L) : L →* L) s) = s := by
  rw [one_mul]; ext; simp
theorem prin_mem_range (s : Lˣ) :
    prin K L σ s ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range := ⟨_, rfl⟩
theorem bijective_prin :
    Function.Bijective fun s : Lˣ =>
      (⟨prin K L σ s, prin_mem_range K L σ s⟩ :
        (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range) := by
  have hinj : Function.Injective (algebraMap L (AdeleRing (𝓞 L) L)) := NumberField.AdeleRing.algebraMap_injective (𝓞 L) L
  constructor
  · intro s s' h
    have h' : prin K L σ s = prin K L σ s' := congrArg Subtype.val h
    have h'' : (σ.symm (s : L) : L) = σ.symm (s' : L) := hinj (congrArg (fun u : (AdeleRing (𝓞 L) L)ˣ => (u : AdeleRing (𝓞 L) L)) h')
    exact Units.ext (σ.symm.injective h'')
  · rintro ⟨_, q, rfl⟩
    refine ⟨Units.map (σ : L →* L) q, Subtype.ext ?_⟩
    show prin K L σ _ = _
    unfold prin
    congr 1
    ext
    simp
theorem countable_range :
    Countable (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range := by
  haveI := countable_units L
  exact (MonoidHom.rangeRestrict_surjective _).countable

theorem Kgen_Iset_eq_Kgen_I1_prin (φ : AdelicGL2 (𝓞 L) L → ℂ) (z : (AdeleRing (𝓞 L) L)ˣ) (g : AdelicGL2 (𝓞 L) L)
    (s : Lˣ) (a : {α : Lˣ // Algebra.norm K (α : L) = 1}) :
    Kgen K L D σ (Iset K L σ hgen s a) φ z g = Kgen K L D σ (I1 K L σ hgen a) φ (prin K L σ s * z) g := by
  rw [← Iset_one, prin, Kgen_Iset_principal_mul, one_mul_map_symm]
theorem Tgen_Jset_eq_Tgen_J1_prin (R : ℝ) (φ : AdelicGL2 (𝓞 L) L → ℂ) (z : (AdeleRing (𝓞 L) L)ˣ)
    (g : AdelicGL2 (𝓞 L) L) (s : Lˣ) (a : {α : Lˣ // Algebra.norm K (α : L) = 1}) :
    Tgen K L D σ (Jset K L s a) R φ z g = Tgen K L D σ (J1 K L a) R φ (prin K L σ s * z) g := by
  rw [← Jset_one, prin, Tgen_Jset_principal_mul, one_mul_map_symm]

end Small

end R1IwCentre

namespace R1IwCentre

open scoped Topology

section Topology

variable (F : Type) [Field F] [NumberField F]

theorem secondCountableTopology_idele : SecondCountableTopology (AdeleRing (𝓞 F) F)ˣ := by
  haveI : SecondCountableTopology (AdeleRing (𝓞 F) F) := NumberField.AdeleRing.secondCountableTopology F
  haveI : SecondCountableTopology (AdeleRing (𝓞 F) F)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology
theorem continuous_diagOne :
    Continuous (diagOne : (AdeleRing (𝓞 F) F)ˣ → AdelicGL2 (𝓞 F) F) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · show Continuous fun t : (AdeleRing (𝓞 F) F)ˣ => Matrix.diagonal ![(t : AdeleRing (𝓞 F) F), 1]
    exact (Units.continuous_val.matrixVecCons continuous_const).matrix_diagonal
  · show Continuous fun t : (AdeleRing (𝓞 F) F)ˣ =>
      Matrix.diagonal ![((t⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F), 1]
    exact (Units.continuous_coe_inv.matrixVecCons continuous_const).matrix_diagonal
theorem continuous_centralScalar :
    Continuous (centralScalar (𝓞 F) F : (AdeleRing (𝓞 F) F)ˣ → AdelicGL2 (𝓞 F) F) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · show Continuous fun u : (AdeleRing (𝓞 F) F)ˣ => Matrix.diagonal fun _ : Fin 2 => (u : AdeleRing (𝓞 F) F)
    exact (continuous_pi fun _ => Units.continuous_val).matrix_diagonal
  · show Continuous fun u : (AdeleRing (𝓞 F) F)ˣ =>
      Matrix.diagonal fun _ : Fin 2 => ((u⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)
    exact (continuous_pi fun _ => Units.continuous_coe_inv).matrix_diagonal

end Topology

section Generic

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

theorem continuous_comp_pair {X W P : Type} [TopologicalSpace X] [TopologicalSpace W] [TopologicalSpace P]
    (G : X → W → ℂ) (hG : Continuous fun q : X × W => G q.1 q.2) (a : P → X) (ha : Continuous a) (e : P → W)
    (he : Continuous e) : Continuous fun p : P => G (a p) (e p) :=
  hG.comp (ha.prodMk he)

variable (L : Type) [Field L] [NumberField L]

theorem exists_finite_forall_ne_zero_mem (hfin : AutomorphicForm.AdelicKernelLocalFiniteness L)
    (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφs : HasCompactSupport φ)
    {X Y : Set (AdelicGL2 (𝓞 L) L)} (hX : IsCompact X) (hY : IsCompact Y) :
    ∃ Γ : Set (GL (Fin 2) L), Γ.Finite ∧ ∀ x ∈ X, ∀ y ∈ Y, ∀ δ : GL (Fin 2) L,
      φ (x⁻¹ * globalPoints (𝓞 L) L δ * y) ≠ 0 → δ ∈ Γ := by
  have hC : IsCompact (X * tsupport φ * Y⁻¹) := (hX.mul hφs).mul hY.inv
  refine ⟨{δ | (1 : AdelicGL2 (𝓞 L) L)⁻¹ * globalPoints (𝓞 L) L δ * 1 ∈ X * tsupport φ * Y⁻¹},
    hfin _ hC 1 1, ?_⟩
  intro x hx y hy δ hδ
  have hmem : x⁻¹ * globalPoints (𝓞 L) L δ * y ∈ tsupport φ := subset_tsupport φ hδ
  have h : globalPoints (𝓞 L) L δ = x * (x⁻¹ * globalPoints (𝓞 L) L δ * y) * y⁻¹ := by group
  change (1 : AdelicGL2 (𝓞 L) L)⁻¹ * globalPoints (𝓞 L) L δ * 1 ∈ X * tsupport φ * Y⁻¹
  rw [inv_one, one_mul, mul_one, h]
  exact Set.mul_mem_mul (Set.mul_mem_mul hx hmem) (Set.inv_mem_inv.mpr hy)

theorem finsum_mem_eq_sum_of_mem (hfin : AutomorphicForm.AdelicKernelLocalFiniteness L)
    (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφs : HasCompactSupport φ) (T : Set (GL (Fin 2) L))
    {X Y : Set (AdelicGL2 (𝓞 L) L)} (hX : IsCompact X) (hY : IsCompact Y) :
    ∃ t : Finset (GL (Fin 2) L), (t : Set (GL (Fin 2) L)) ⊆ T ∧ ∀ x ∈ X, ∀ y ∈ Y,
      ∑ᶠ δ ∈ T, φ (x⁻¹ * globalPoints (𝓞 L) L δ * y) = ∑ δ ∈ t, φ (x⁻¹ * globalPoints (𝓞 L) L δ * y) := by
  obtain ⟨Γ, hΓ, hmem⟩ := exists_finite_forall_ne_zero_mem L hfin φ hφs hX hY
  have hΓT : (Γ ∩ T).Finite := hΓ.subset Set.inter_subset_left
  refine ⟨hΓT.toFinset, fun δ hδ => (hΓT.mem_toFinset.mp hδ).2, fun x hx y hy => ?_⟩
  apply finsum_mem_eq_sum_of_subset
  · rintro δ ⟨hδT, hδs⟩
    exact hΓT.mem_toFinset.mpr ⟨hmem x hx y hy δ hδs, hδT⟩
  · intro δ hδ
    exact (hΓT.mem_toFinset.mp hδ).2

theorem continuous_finsum_mem (hfin : AutomorphicForm.AdelicKernelLocalFiniteness L)
    (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφc : Continuous φ) (hφs : HasCompactSupport φ) (T : Set (GL (Fin 2) L)) :
    Continuous fun p : AdelicGL2 (𝓞 L) L × AdelicGL2 (𝓞 L) L =>
      ∑ᶠ δ ∈ T, φ (p.1⁻¹ * globalPoints (𝓞 L) L δ * p.2) := by
  rw [continuous_iff_continuousAt]
  intro p
  obtain ⟨X, hX, hXn⟩ := exists_compact_mem_nhds p.1
  obtain ⟨Y, hY, hYn⟩ := exists_compact_mem_nhds p.2
  obtain ⟨t, -, ht⟩ := finsum_mem_eq_sum_of_mem L hfin φ hφs T hX hY
  have hsum : Continuous fun q : AdelicGL2 (𝓞 L) L × AdelicGL2 (𝓞 L) L =>
      ∑ δ ∈ t, φ (q.1⁻¹ * globalPoints (𝓞 L) L δ * q.2) := by
    refine continuous_finsetSum t fun δ _ => hφc.comp ?_
    exact (continuous_fst.inv.mul continuous_const).mul continuous_snd
  refine ((hsum.continuousOn (s := X ×ˢ Y)).congr fun q hq => ht q.1 hq.1 q.2 hq.2).continuousAt ?_
  exact prod_mem_nhds hXn hYn

variable (K : Type) [Field K] [Algebra K L]
variable (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)

theorem continuous_glMap {A B : Type*} [CommRing A] [CommRing B] [TopologicalSpace A]
    [TopologicalSpace B] [IsTopologicalRing A] [IsTopologicalRing B] (f : A →+* B)
    (hf : Continuous f) : Continuous (Matrix.GeneralLinearGroup.map (n := Fin 2) f) :=
  Continuous.units_map _ ((continuous_id.matrix_map hf) :
    Continuous fun m : Matrix (Fin 2) (Fin 2) A => m.map f)

theorem continuous_sigmaAdelicAct : Continuous (sigmaAdelicAct K L D σ) :=
  continuous_glMap (D.act σ : RingAut (AdeleRing (𝓞 L) L)).toRingHom (D.continuous_act σ)

theorem continuous_fold (hloc : AutomorphicForm.AdelicKernelLocalFiniteness L) (φ : AdelicGL2 (𝓞 L) L → ℂ)
    (hφc : Continuous φ) (hφs : HasCompactSupport φ) (T' : Set (GL (Fin 2) L)) :
    Continuous fun p : AdelicGL2 (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ => Kgen K L D σ T' φ p.2 p.1 :=
  continuous_comp_pair (fun g w : AdelicGL2 (𝓞 L) L => ∑ᶠ δ ∈ T', φ (g⁻¹ * globalPoints (𝓞 L) L δ * w))
    (continuous_finsum_mem L hloc φ hφc hφs T') Prod.fst continuous_fst _
    ((continuous_sigmaAdelicAct L K D σ).comp (((continuous_centralScalar L).comp continuous_snd).mul continuous_fst))

theorem continuous_truncationIntegrand (hloc : AutomorphicForm.AdelicKernelLocalFiniteness L)
    (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφc : Continuous φ) (hφs : HasCompactSupport φ) (T' : Set (GL (Fin 2) L)) :
    Continuous fun r : (AdelicGL2 (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ) × AdeleRing (𝓞 L) L =>
      ∑ᶠ δ ∈ T',
        φ (r.1.1⁻¹ * globalPoints (𝓞 L) L δ * sigmaAdelicAct K L D σ
          (unipotentGL2 r.2 * (centralScalar (𝓞 L) L r.1.2 * r.1.1))) :=
  continuous_comp_pair (fun g w : AdelicGL2 (𝓞 L) L => ∑ᶠ δ ∈ T', φ (g⁻¹ * globalPoints (𝓞 L) L δ * w))
    (continuous_finsum_mem L hloc φ hφc hφs T') (fun r => r.1.1) (continuous_fst.comp continuous_fst)
    (fun r : (AdelicGL2 (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ) × AdeleRing (𝓞 L) L =>
      sigmaAdelicAct K L D σ (unipotentGL2 r.2 * (centralScalar (𝓞 L) L r.1.2 * r.1.1)))
    ((continuous_sigmaAdelicAct L K D σ).comp
      (((AutomorphicForm.continuous_unipotentGL2 (R := AdeleRing (𝓞 L) L)).comp continuous_snd).mul
        ((((continuous_centralScalar L).comp (continuous_snd.comp continuous_fst))).mul
          (continuous_fst.comp continuous_fst))))

open Classical in
theorem Tgen_eq_ite (T' : Set (GL (Fin 2) L)) (R : ℝ) (φ : AdelicGL2 (𝓞 L) L → ℂ) (z : (AdeleRing (𝓞 L) L)ˣ)
    (g : AdelicGL2 (𝓞 L) L) :
    Tgen K L D σ T' R φ z g =
      if Real.exp R < NumberField.AdelicHeight.adelicHeight L (centralScalar (𝓞 L) L z * g) then
        ∫ q, ∑ᶠ δ ∈ T',
          φ (g⁻¹ * globalPoints (𝓞 L) L δ * sigmaAdelicAct K L D σ
            (unipotentGL2 q * (centralScalar (𝓞 L) L z * g)))
          ∂(@ProbabilityTheory.cond _ (adeleBorel (𝓞 L) L) (adelicAddHaar (𝓞 L) L) (adelicBox L))
      else 0 := by
  unfold Tgen
  rw [Set.indicator_apply]
  rfl

theorem measurable_Kgen_sub_Tgen [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ]
    (hloc : AutomorphicForm.AdelicKernelLocalFiniteness L) (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφc : Continuous φ)
    (hφs : HasCompactSupport φ) (R : ℝ) (T' T'' : Set (GL (Fin 2) L)) :
    Measurable fun p : AdelicGL2 (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ =>
      Kgen K L D σ T' φ p.2 p.1 - Tgen K L D σ T'' R φ p.2 p.1 := by
  classical
  haveI : SecondCountableTopology (AdeleRing (𝓞 L) L) := NumberField.AdeleRing.secondCountableTopology L
  haveI : SecondCountableTopology (AdeleRing (𝓞 L) L)ˣ := secondCountableTopology_idele L
  have hKm : Measurable fun p : AdelicGL2 (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ => Kgen K L D σ T' φ p.2 p.1 :=
    (continuous_fold L K D σ hloc φ hφc hφs T').measurable
  have hhigh : MeasurableSet {p : AdelicGL2 (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ |
      Real.exp R < NumberField.AdelicHeight.adelicHeight L (centralScalar (𝓞 L) L p.2 * p.1)} :=
    ((NumberField.AdelicHeight.continuous_adelicHeight L).comp
      (((continuous_centralScalar L).comp continuous_snd).mul continuous_fst)).measurable measurableSet_Ioi
  have hCT : StronglyMeasurable fun p : AdelicGL2 (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ =>
      ∫ q, (fun r : (AdelicGL2 (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ) × AdeleRing (𝓞 L) L =>
        ∑ᶠ δ ∈ T'',
          φ (r.1.1⁻¹ * globalPoints (𝓞 L) L δ * sigmaAdelicAct K L D σ
            (unipotentGL2 r.2 * (centralScalar (𝓞 L) L r.1.2 * r.1.1)))) (p, q)
        ∂(@ProbabilityTheory.cond _ (adeleBorel (𝓞 L) L) (adelicAddHaar (𝓞 L) L) (adelicBox L)) :=
    (continuous_truncationIntegrand L K D σ hloc φ hφc hφs T'').stronglyMeasurable.integral_prod_right'
  have hTm : Measurable fun p : AdelicGL2 (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ => Tgen K L D σ T'' R φ p.2 p.1 := by
    simp_rw [Tgen_eq_ite]
    exact Measurable.ite hhigh hCT.measurable measurable_const
  exact hKm.sub hTm

end Generic

section Partition

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

variable (L : Type) [Field L] [NumberField L]

def fib {ι : Type*} (T : Set (GL (Fin 2) L)) (ind : GL (Fin 2) L → ι) (i : ι) : Set (GL (Fin 2) L) :=
  {δ | δ ∈ T ∧ ind δ = i}

theorem finsum_mem_eq_tsum_fib {ι : Type*} (T : Set (GL (Fin 2) L)) (ind : GL (Fin 2) L → ι) (f : GL (Fin 2) L → ℂ)
    (hf : (T ∩ Function.support f).Finite) :
    (∑ᶠ δ ∈ T, f δ) = ∑' i, ∑ᶠ δ ∈ fib L T ind i, f δ ∧
      Function.HasFiniteSupport (fun i => ∑ᶠ δ ∈ fib L T ind i, f δ) := by
  classical
  set sT := hf.toFinset with hsT
  have hT : (∑ᶠ δ ∈ T, f δ) = ∑ δ ∈ sT, f δ :=
    finsum_mem_eq_sum_of_subset f (fun δ hδ => hf.mem_toFinset.mpr hδ) fun δ hδ => (hf.mem_toFinset.mp hδ).1
  have hfib : ∀ i, (∑ᶠ δ ∈ fib L T ind i, f δ) = ∑ δ ∈ sT with ind δ = i, f δ := by
    intro i
    refine finsum_mem_eq_sum_of_subset f ?_ ?_
    · rintro δ ⟨⟨hδT, hδi⟩, hδs⟩
      exact Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hf.mem_toFinset.mpr ⟨hδT, hδs⟩, hδi⟩)
    · intro δ hδ
      obtain ⟨h1, h2⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hδ)
      exact ⟨(hf.mem_toFinset.mp h1).1, h2⟩
  have hzero : ∀ i ∉ sT.image ind, (∑ᶠ δ ∈ fib L T ind i, f δ) = 0 := by
    intro i hi
    rw [hfib, Finset.sum_eq_zero]
    intro δ hδ
    obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hδ
    exact absurd (Finset.mem_image.mpr ⟨δ, h1, h2⟩) hi
  refine ⟨?_, ?_⟩
  · rw [tsum_eq_sum (s := sT.image ind) hzero, hT]
    simp_rw [hfib]
    exact (Finset.sum_fiberwise_of_maps_to (fun δ hδ => Finset.mem_image_of_mem ind hδ) f).symm
  · exact (sT.image ind).finite_toSet.subset fun i hi => by
      by_contra h
      exact Function.mem_support.mp hi (hzero i h)

variable (K : Type) [Field K] [Algebra K L]
variable (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)

theorem Kgen_eq_tsum_fib (hloc : AutomorphicForm.AdelicKernelLocalFiniteness L) {ι : Type*}
    (T : Set (GL (Fin 2) L)) (ind : GL (Fin 2) L → ι) (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφs : HasCompactSupport φ)
    (z : (AdeleRing (𝓞 L) L)ˣ) (g : AdelicGL2 (𝓞 L) L) :
    Kgen K L D σ T φ z g = ∑' i, Kgen K L D σ (fib L T ind i) φ z g ∧
      Function.HasFiniteSupport (fun i => Kgen K L D σ (fib L T ind i) φ z g) := by
  obtain ⟨Γ, hΓ, hmem⟩ := exists_finite_forall_ne_zero_mem L hloc φ hφs (isCompact_singleton (x := g))
    (isCompact_singleton (x := sigmaAdelicAct K L D σ (centralScalar (𝓞 L) L z * g)))
  exact finsum_mem_eq_tsum_fib L T ind _ ((hΓ.subset fun δ hδ => hmem g rfl _ rfl δ hδ).subset Set.inter_subset_right)

theorem ae_mem_adelicBox :
    ∀ᵐ q ∂(@ProbabilityTheory.cond _ (adeleBorel (𝓞 L) L) (adelicAddHaar (𝓞 L) L) (adelicBox L)), q ∈ adelicBox L := by
  rw [ProbabilityTheory.cond]
  exact Measure.ae_smul_measure (ae_restrict_mem (measurableSet_adelicBox L)) _

theorem Tgen_eq_tsum_fib (hloc : AutomorphicForm.AdelicKernelLocalFiniteness L) {ι : Type*}
    (T : Set (GL (Fin 2) L)) (ind : GL (Fin 2) L → ι) (R : ℝ) (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφc : Continuous φ)
    (hφs : HasCompactSupport φ) (z : (AdeleRing (𝓞 L) L)ˣ) (g : AdelicGL2 (𝓞 L) L) :
    Tgen K L D σ T R φ z g = ∑' i, Tgen K L D σ (fib L T ind i) R φ z g ∧
      Function.HasFiniteSupport (fun i => Tgen K L D σ (fib L T ind i) R φ z g) := by
  classical
  simp only [Tgen_eq_ite]
  split_ifs with hhigh
  swap
  · exact ⟨tsum_zero.symm, by simp [Function.HasFiniteSupport]⟩
  set μ := @ProbabilityTheory.cond _ (adeleBorel (𝓞 L) L) (adelicAddHaar (𝓞 L) L) (adelicBox L) with hμ
  haveI : IsProbabilityMeasure μ := isProbabilityMeasure_cond_adelicBox L
  set y : AdeleRing (𝓞 L) L → AdelicGL2 (𝓞 L) L :=
    fun q => sigmaAdelicAct K L D σ (unipotentGL2 q * (centralScalar (𝓞 L) L z * g)) with hy
  have hyc : Continuous y :=
    (continuous_sigmaAdelicAct L K D σ).comp
      ((AutomorphicForm.continuous_unipotentGL2 (R := AdeleRing (𝓞 L) L)).mul continuous_const)
  set f : GL (Fin 2) L → AdeleRing (𝓞 L) L → ℂ := fun δ q => φ (g⁻¹ * globalPoints (𝓞 L) L δ * y q) with hf

  obtain ⟨C, hC, hboxC⟩ := exists_isCompact_adelicBox_subset L
  obtain ⟨Γ, hΓ, hmem⟩ := exists_finite_forall_ne_zero_mem L hloc φ hφs (isCompact_singleton (x := g)) (hC.image hyc)
  have hΓT : (Γ ∩ T).Finite := hΓ.subset Set.inter_subset_left
  set sT := hΓT.toFinset with hsT
  have hsum : ∀ (S : Set (GL (Fin 2) L)), S ⊆ T → ∀ q ∈ C,
      (∑ᶠ δ ∈ S, f δ q) = ∑ δ ∈ sT with δ ∈ S, f δ q := by
    intro S hS q hq
    refine finsum_mem_eq_sum_of_subset _ ?_ ?_
    · rintro δ ⟨hδS, hδs⟩
      refine Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hΓT.mem_toFinset.mpr ⟨?_, hS hδS⟩, hδS⟩)
      exact hmem g rfl (y q) ⟨q, hq, rfl⟩ δ hδs
    · intro δ hδ
      exact (Finset.mem_filter.mp (Finset.mem_coe.mp hδ)).2
  have hint : ∀ δ, Integrable (f δ) μ := by
    intro δ
    obtain ⟨B, hB⟩ := hφc.bounded_above_of_compact_support hφs
    have hcont : Continuous (f δ) := hφc.comp (continuous_const.mul hyc)
    exact Integrable.of_bound hcont.aestronglyMeasurable B (Filter.Eventually.of_forall fun q => hB _)
  have hae : ∀ᵐ q ∂μ, q ∈ C := (ae_mem_adelicBox L).mono fun q hq => hboxC hq

  have hI : ∀ (S : Set (GL (Fin 2) L)), S ⊆ T →
      ∫ q, ∑ᶠ δ ∈ S, f δ q ∂μ = ∑ δ ∈ sT with δ ∈ S, ∫ q, f δ q ∂μ := by
    intro S hS
    rw [← integral_finsetSum _ fun δ _ => hint δ]
    exact integral_congr_ae (hae.mono fun q hq => hsum S hS q hq)
  have hfibT : ∀ i, fib L T ind i ⊆ T := fun i δ hδ => hδ.1
  have hzero : ∀ i ∉ sT.image ind, ∫ q, ∑ᶠ δ ∈ fib L T ind i, f δ q ∂μ = 0 := by
    intro i hi
    rw [hI _ (hfibT i), Finset.sum_eq_zero]
    intro δ hδ
    obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hδ
    exact absurd (Finset.mem_image.mpr ⟨δ, h1, h2.2⟩) hi
  refine ⟨?_, ?_⟩
  · change ∫ q, ∑ᶠ δ ∈ T, f δ q ∂μ = ∑' i, ∫ q, ∑ᶠ δ ∈ fib L T ind i, f δ q ∂μ
    rw [tsum_eq_sum (s := sT.image ind) hzero, hI T subset_rfl]
    simp_rw [hI _ (hfibT _)]
    have hfil : ∀ i, (sT.filter fun δ => δ ∈ fib L T ind i) = sT.filter fun δ => ind δ = i := by
      intro i
      ext δ
      simp only [Finset.mem_filter, fib, Set.mem_setOf_eq, and_congr_right_iff]
      intro hδ
      exact ⟨fun h => h.2, fun h => ⟨(hΓT.mem_toFinset.mp hδ).2, h⟩⟩
    have hfilT : (sT.filter fun δ => δ ∈ T) = sT := by
      ext δ
      simp only [Finset.mem_filter, and_iff_left_iff_imp]
      exact fun hδ => (hΓT.mem_toFinset.mp hδ).2
    simp_rw [hfil, hfilT]
    exact (Finset.sum_fiberwise_of_maps_to (fun δ hδ => Finset.mem_image_of_mem ind hδ) _).symm
  · exact (sT.image ind).finite_toSet.subset fun i hi => by
      by_contra h
      exact Function.mem_support.mp hi (hzero i h)

end Partition

end R1IwCentre

namespace R1IwCentre

section Index

open AutomorphicForm.TwistedBruhat

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
variable (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
variable (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)

abbrev N1 : Type := {α : Lˣ // Algebra.norm K (α : L) = 1}

open Classical in
def u11 (δ : GL (Fin 2) L) : Lˣ :=
  if h : (δ : Matrix (Fin 2) (Fin 2) L) 1 1 = 0 then 1 else Units.mk0 _ h

open Classical in
def aOf (δ : GL (Fin 2) L) : N1 K L :=
  if h : (δ : Matrix (Fin 2) (Fin 2) L) 1 1 ≠ 0 ∧ (δ : Matrix (Fin 2) (Fin 2) L) 0 0 ≠ 0 ∧
      Algebra.norm K ((δ : Matrix (Fin 2) (Fin 2) L) 0 0 / (δ : Matrix (Fin 2) (Fin 2) L) 1 1) = 1 then
    ⟨Units.mk0 _ h.2.1 / Units.mk0 _ h.1, by rw [Units.val_div_eq_div_val, Units.val_mk0, Units.val_mk0]; exact h.2.2⟩
  else ⟨1, by simp⟩
def ind₂ (δ : GL (Fin 2) L) : Lˣ × N1 K L := (u11 L δ, aOf K L δ)
theorem ne_zero_of_upper (δ : GL (Fin 2) L) (h10 : (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) :
    (δ : Matrix (Fin 2) (Fin 2) L) 0 0 ≠ 0 ∧ (δ : Matrix (Fin 2) (Fin 2) L) 1 1 ≠ 0 := by
  have hdet : (δ : Matrix (Fin 2) (Fin 2) L).det ≠ 0 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply]; exact (Matrix.GeneralLinearGroup.det δ).ne_zero
  rw [Matrix.det_fin_two, h10, mul_zero, sub_zero] at hdet
  exact ⟨left_ne_zero_of_mul hdet, right_ne_zero_of_mul hdet⟩
theorem u11_eq_iff {δ : GL (Fin 2) L} {s : Lˣ} (h : (δ : Matrix (Fin 2) (Fin 2) L) 1 1 ≠ 0) :
    u11 L δ = s ↔ (δ : Matrix (Fin 2) (Fin 2) L) 1 1 = (s : L) := by
  unfold u11
  rw [dif_neg h, Units.ext_iff, Units.val_mk0]
theorem aOf_eq_iff {δ : GL (Fin 2) L} {s : Lˣ} (h11 : (δ : Matrix (Fin 2) (Fin 2) L) 1 1 = (s : L))
    (hN : Algebra.norm K ((δ : Matrix (Fin 2) (Fin 2) L) 0 0 / (δ : Matrix (Fin 2) (Fin 2) L) 1 1) = 1) (a : N1 K L) :
    aOf K L δ = a ↔ (δ : Matrix (Fin 2) (Fin 2) L) 0 0 = (s : L) * ((a : Lˣ) : L) := by
  have h1 : (δ : Matrix (Fin 2) (Fin 2) L) 1 1 ≠ 0 := by rw [h11]; exact s.ne_zero
  have h0 : (δ : Matrix (Fin 2) (Fin 2) L) 0 0 ≠ 0 := by
    intro h0
    rw [h0, zero_div, Algebra.norm_zero] at hN
    exact zero_ne_one hN
  unfold aOf
  rw [dif_pos ⟨h1, h0, hN⟩, Subtype.ext_iff, Units.ext_iff, Units.val_div_eq_div_val, Units.val_mk0, Units.val_mk0, h11,
    div_eq_iff s.ne_zero, mul_comm]
theorem fib_cusp_eq_Iset (p : Lˣ × N1 K L) :
    fib L (normUnipotentSet K L σ hgen ∩ (borelSubgroup L : Set (GL (Fin 2) L))) (ind₂ K L) p =
      Iset K L σ hgen p.1 p.2 := by
  ext δ
  simp only [fib, Iset, ind₂, Set.mem_setOf_eq, Set.mem_inter_iff, SetLike.mem_coe, Prod.ext_iff]
  constructor
  · rintro ⟨⟨hNU, hB⟩, hu, ha⟩
    have h10 : (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 := hB
    have h11 := (u11_eq_iff L (ne_zero_of_upper L δ h10).2).mp hu
    exact ⟨hNU, h10, h11, (aOf_eq_iff K L h11 (norm_div_eq_one_of_mem_normUnipotentSet hgen hNU h10) p.2).mp ha⟩
  · rintro ⟨hNU, h10, h11, h00⟩
    have hN : Algebra.norm K ((δ : Matrix (Fin 2) (Fin 2) L) 0 0 / (δ : Matrix (Fin 2) (Fin 2) L) 1 1) = 1 := by
      rw [h00, h11, mul_div_cancel_left₀ _ p.1.ne_zero]; exact p.2.2
    exact ⟨⟨hNU, h10⟩, (u11_eq_iff L (ne_zero_of_upper L δ h10).2).mpr h11, (aOf_eq_iff K L h11 hN p.2).mpr h00⟩
theorem fib_borelNormOne_eq_Jset (p : Lˣ × N1 K L) :
    fib L (borelNormOneSet K L) (ind₂ K L) p = Jset K L p.1 p.2 := by
  ext δ
  simp only [fib, Jset, ind₂, borelNormOneSet, Set.mem_setOf_eq, Prod.ext_iff]
  constructor
  · rintro ⟨⟨h10, hN⟩, hu, ha⟩
    have h11 := (u11_eq_iff L (ne_zero_of_upper L δ h10).2).mp hu
    exact ⟨h10, h11, (aOf_eq_iff K L h11 hN p.2).mp ha⟩
  · rintro ⟨h10, h11, h00⟩
    have hN : Algebra.norm K ((δ : Matrix (Fin 2) (Fin 2) L) 0 0 / (δ : Matrix (Fin 2) (Fin 2) L) 1 1) = 1 := by
      rw [h00, h11, mul_div_cancel_left₀ _ p.1.ne_zero]; exact p.2.2
    exact ⟨⟨h10, hN⟩, (u11_eq_iff L (ne_zero_of_upper L δ h10).2).mpr h11, (aOf_eq_iff K L h11 hN p.2).mpr h00⟩
def I1u : Set (GL (Fin 2) L) :=
  {δ | δ ∈ normUnipotentSet K L σ hgen ∧ (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (δ : Matrix (Fin 2) (Fin 2) L) 1 1 = 1}
def J1u : Set (GL (Fin 2) L) :=
  {δ | (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (δ : Matrix (Fin 2) (Fin 2) L) 1 1 = 1 ∧
    Algebra.norm K ((δ : Matrix (Fin 2) (Fin 2) L) 0 0 / (δ : Matrix (Fin 2) (Fin 2) L) 1 1) = 1}
theorem fib_I1u_eq_I1 (a : N1 K L) : fib L (I1u K L σ hgen) (aOf K L) a = I1 K L σ hgen a := by
  ext δ
  simp only [fib, I1, I1u, Set.mem_setOf_eq]
  constructor
  · rintro ⟨⟨hNU, h10, h11⟩, ha⟩
    have h11' : (δ : Matrix (Fin 2) (Fin 2) L) 1 1 = ((1 : Lˣ) : L) := h11
    have h := (aOf_eq_iff K L h11' (norm_div_eq_one_of_mem_normUnipotentSet hgen hNU h10) a).mp ha
    rw [Units.val_one, one_mul] at h
    exact ⟨hNU, h10, h11, h⟩
  · rintro ⟨hNU, h10, h11, h00⟩
    have h11' : (δ : Matrix (Fin 2) (Fin 2) L) 1 1 = ((1 : Lˣ) : L) := h11
    have hN : Algebra.norm K ((δ : Matrix (Fin 2) (Fin 2) L) 0 0 / (δ : Matrix (Fin 2) (Fin 2) L) 1 1) = 1 := by
      rw [h00, h11, div_one]; exact a.2
    exact ⟨⟨hNU, h10, h11⟩, (aOf_eq_iff K L h11' hN a).mpr (by rw [h00, Units.val_one, one_mul])⟩
theorem fib_J1u_eq_J1 (a : N1 K L) : fib L (J1u K L) (aOf K L) a = J1 K L a := by
  ext δ
  simp only [fib, J1, J1u, Set.mem_setOf_eq]
  constructor
  · rintro ⟨⟨h10, h11, hN⟩, ha⟩
    have h11' : (δ : Matrix (Fin 2) (Fin 2) L) 1 1 = ((1 : Lˣ) : L) := h11
    have h := (aOf_eq_iff K L h11' hN a).mp ha
    rw [Units.val_one, one_mul] at h
    exact ⟨h10, h11, h⟩
  · rintro ⟨h10, h11, h00⟩
    have h11' : (δ : Matrix (Fin 2) (Fin 2) L) 1 1 = ((1 : Lˣ) : L) := h11
    have hN : Algebra.norm K ((δ : Matrix (Fin 2) (Fin 2) L) 0 0 / (δ : Matrix (Fin 2) (Fin 2) L) 1 1) = 1 := by
      rw [h00, h11, div_one]; exact a.2
    exact ⟨⟨h10, h11, hN⟩, (aOf_eq_iff K L h11' hN a).mpr (by rw [h00, Units.val_one, one_mul])⟩

end Index

section FiniteSupport

variable {β γ M : Type*}

theorem hasFiniteSupport_curry [Zero M] {f : β × γ → M} (h : Function.HasFiniteSupport f) (b : β) :
    Function.HasFiniteSupport fun c => f (b, c) :=
  Set.Finite.preimage (f := fun c : γ => (b, c)) (fun _ _ _ _ e => congrArg Prod.snd e) h
theorem hasFiniteSupport_fst [AddCommMonoid M] [TopologicalSpace M] {f : β × γ → M}
    (h : Function.HasFiniteSupport f) : Function.HasFiniteSupport fun b => ∑' c, f (b, c) := by
  refine (Set.Finite.image Prod.fst h).subset fun b hb => ?_
  by_contra hb'
  refine Function.mem_support.mp hb ?_
  have hz : (fun c => f (b, c)) = fun _ => 0 := by
    funext c
    by_contra hc
    exact hb' ⟨(b, c), Function.mem_support.mpr hc, rfl⟩
  rw [hz, tsum_zero]

end FiniteSupport

section Pointwise

open AutomorphicForm.TwistedBruhat

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
variable (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
variable (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)

theorem cusp_sub_eq_tsum_tsum (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφc : Continuous φ) (hφs : HasCompactSupport φ)
    (R : ℝ) (z : (AdeleRing (𝓞 L) L)ˣ) (g : AdelicGL2 (𝓞 L) L) :
    (Kgen K L D σ (normUnipotentSet K L σ hgen ∩ (borelSubgroup L : Set (GL (Fin 2) L))) φ z g -
        Tgen K L D σ (borelNormOneSet K L) R φ z g =
      ∑' s : Lˣ, ∑' a : N1 K L, (Kgen K L D σ (Iset K L σ hgen s a) φ z g - Tgen K L D σ (Jset K L s a) R φ z g)) ∧
    Function.HasFiniteSupport (fun p : Lˣ × N1 K L =>
      Kgen K L D σ (Iset K L σ hgen p.1 p.2) φ z g - Tgen K L D σ (Jset K L p.1 p.2) R φ z g) := by
  have hloc := AutomorphicForm.adelicKernelLocalFiniteness L
  obtain ⟨hK, hKf⟩ := Kgen_eq_tsum_fib L K D σ hloc
    (normUnipotentSet K L σ hgen ∩ (borelSubgroup L : Set (GL (Fin 2) L))) (ind₂ K L) φ hφs z g
  obtain ⟨hT, hTf⟩ := Tgen_eq_tsum_fib L K D σ hloc (borelNormOneSet K L) (ind₂ K L) R φ hφc hφs z g
  simp only [fib_cusp_eq_Iset, fib_borelNormOne_eq_Jset] at hK hKf hT hTf
  have hsub : Function.HasFiniteSupport (fun p : Lˣ × N1 K L =>
      Kgen K L D σ (Iset K L σ hgen p.1 p.2) φ z g - Tgen K L D σ (Jset K L p.1 p.2) R φ z g) :=
    ((hKf.union hTf).subset (Function.support_sub _ _))
  refine ⟨?_, hsub⟩
  rw [hK, hT, ← (summable_of_hasFiniteSupport hKf).tsum_sub (summable_of_hasFiniteSupport hTf)]
  exact (summable_of_hasFiniteSupport hsub).tsum_prod' fun s => summable_of_hasFiniteSupport (hasFiniteSupport_curry hsub s)

def Hfun (R : ℝ) (φ : AdelicGL2 (𝓞 L) L → ℂ) (ζ : (AdeleRing (𝓞 L) L)ˣ) (g : AdelicGL2 (𝓞 L) L) : ℂ :=
  ∑' a : N1 K L, (Kgen K L D σ (I1 K L σ hgen a) φ ζ g - Tgen K L D σ (J1 K L a) R φ ζ g)

theorem Hfun_eq (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφc : Continuous φ) (hφs : HasCompactSupport φ)
    (R : ℝ) (ζ : (AdeleRing (𝓞 L) L)ˣ) (g : AdelicGL2 (𝓞 L) L) :
    Hfun K L D σ hgen R φ ζ g = Kgen K L D σ (I1u K L σ hgen) φ ζ g - Tgen K L D σ (J1u K L) R φ ζ g ∧
      Function.HasFiniteSupport (fun a : N1 K L =>
        Kgen K L D σ (I1 K L σ hgen a) φ ζ g - Tgen K L D σ (J1 K L a) R φ ζ g) := by
  have hloc := AutomorphicForm.adelicKernelLocalFiniteness L
  obtain ⟨hK, hKf⟩ := Kgen_eq_tsum_fib L K D σ hloc (I1u K L σ hgen) (aOf K L) φ hφs ζ g
  obtain ⟨hT, hTf⟩ := Tgen_eq_tsum_fib L K D σ hloc (J1u K L) (aOf K L) R φ hφc hφs ζ g
  simp only [fib_I1u_eq_I1, fib_J1u_eq_J1] at hK hKf hT hTf
  refine ⟨?_, ((hKf.union hTf).subset (Function.support_sub _ _))⟩
  rw [Hfun, hK, hT, ← (summable_of_hasFiniteSupport hKf).tsum_sub (summable_of_hasFiniteSupport hTf)]

theorem tsum_fibre_eq_Hfun_prin (R : ℝ) (φ : AdelicGL2 (𝓞 L) L → ℂ) (z : (AdeleRing (𝓞 L) L)ˣ)
    (g : AdelicGL2 (𝓞 L) L) (s : Lˣ) :
    ∑' a : N1 K L, (Kgen K L D σ (Iset K L σ hgen s a) φ z g - Tgen K L D σ (Jset K L s a) R φ z g) =
      Hfun K L D σ hgen R φ (prin K L σ s * z) g :=
  tsum_congr fun a => by rw [Kgen_Iset_eq_Kgen_I1_prin, Tgen_Jset_eq_Tgen_J1_prin]

end Pointwise

section Unfold

open AutomorphicForm.TwistedBruhat

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
variable (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
variable (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
variable [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ]
variable (νZL : Measure (AdeleRing (𝓞 L) L)ˣ) [νZL.IsHaarMeasure] (ΩL : Set (AdeleRing (𝓞 L) L)ˣ)
variable (ξ' : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ)

def Ffun (R : ℝ) (φ : AdelicGL2 (𝓞 L) L → ℂ) (g : AdelicGL2 (𝓞 L) L) : ℝ≥0∞ :=
  ∫⁻ z in ΩL, ‖((ξ' z : ℂˣ) : ℂ)‖ₑ * Gfun K L D σ hgen R φ z g ∂νZL

theorem smulInvariantMeasure_range :
    SMulInvariantMeasure (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range
      (AdeleRing (𝓞 L) L)ˣ νZL := by
  refine ⟨fun c s _ => ?_⟩
  exact measure_preimage_mul νZL (c : (AdeleRing (𝓞 L) L)ˣ) s

theorem measurable_fibre_abs (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφc : Continuous φ) (hφs : HasCompactSupport φ) (R : ℝ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξ' z : ℂˣ) : ℂ)) (g : AdelicGL2 (𝓞 L) L) (s : Lˣ) :
    Measurable fun z : (AdeleRing (𝓞 L) L)ˣ => ‖((ξ' z : ℂˣ) : ℂ)‖ₑ *
      ∑' a : N1 K L, ‖Kgen K L D σ (Iset K L σ hgen s a) φ z g - Tgen K L D σ (Jset K L s a) R φ z g‖ₑ := by
  haveI : Countable Lˣ := countable_units L
  refine hξc.measurable.enorm.mul (Measurable.ennreal_tsum fun a => ?_)
  exact ((measurable_Kgen_sub_Tgen L K D σ (AutomorphicForm.adelicKernelLocalFiniteness L) φ hφc hφs R
    (Iset K L σ hgen s a) (Jset K L s a)).comp measurable_prodMk_left).enorm

theorem tsum_setLIntegral_fibre_eq_Ffun (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφc : Continuous φ)
    (hφs : HasCompactSupport φ) (R : ℝ) (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξ' z : ℂˣ) : ℂ))
    (g : AdelicGL2 (𝓞 L) L) :
    ∑' s : Lˣ, ∫⁻ z in ΩL, ‖((ξ' z : ℂˣ) : ℂ)‖ₑ *
        ∑' a : N1 K L, ‖Kgen K L D σ (Iset K L σ hgen s a) φ z g - Tgen K L D σ (Jset K L s a) R φ z g‖ₑ ∂νZL =
      Ffun K L D σ hgen νZL ΩL ξ' R φ g := by
  haveI : Countable Lˣ := countable_units L
  rw [Ffun, ← lintegral_tsum fun s => (measurable_fibre_abs K L D σ hgen ξ' φ hφc hφs R hξc g s).aemeasurable]
  refine lintegral_congr fun z => ?_
  rw [ENNReal.tsum_mul_left]
  rfl

def prinEquiv : Lˣ ≃ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range :=
  Equiv.ofBijective _ (bijective_prin K L σ)

theorem prinEquiv_smul (s : Lˣ) (z : (AdeleRing (𝓞 L) L)ˣ) : prinEquiv K L σ s • z = prin K L σ s * z := by
  rw [prinEquiv, Equiv.ofBijective_apply, Subgroup.mk_smul, smul_eq_mul]

variable {ξ'} in
theorem xi_prin_mul (hξt : ∀ q : Lˣ, ξ' (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) q) = 1)
    (s : Lˣ) (z : (AdeleRing (𝓞 L) L)ˣ) : ξ' (prin K L σ s * z) = ξ' z := by
  rw [map_mul, prin, hξt, one_mul]

theorem lintegral_unit_eq_Ffun (hΩL : IsFundamentalDomain
      (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range ΩL νZL)
    (hξt : ∀ q : Lˣ, ξ' (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) q) = 1)
    (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφc : Continuous φ) (hφs : HasCompactSupport φ) (R : ℝ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξ' z : ℂˣ) : ℂ)) (g : AdelicGL2 (𝓞 L) L) :
    ∫⁻ ζ, ‖((ξ' ζ : ℂˣ) : ℂ)‖ₑ *
        ∑' a : N1 K L, ‖Kgen K L D σ (I1 K L σ hgen a) φ ζ g - Tgen K L D σ (J1 K L a) R φ ζ g‖ₑ ∂νZL =
      Ffun K L D σ hgen νZL ΩL ξ' R φ g := by
  haveI := countable_range L
  haveI := smulInvariantMeasure_range L νZL
  have hpt : ∀ (s : Lˣ) (z : (AdeleRing (𝓞 L) L)ˣ),
      ‖((ξ' (prinEquiv K L σ s • z) : ℂˣ) : ℂ)‖ₑ *
        ∑' a : N1 K L, ‖Kgen K L D σ (I1 K L σ hgen a) φ (prinEquiv K L σ s • z) g -
          Tgen K L D σ (J1 K L a) R φ (prinEquiv K L σ s • z) g‖ₑ = ‖((ξ' z : ℂˣ) : ℂ)‖ₑ *
      ∑' a : N1 K L, ‖Kgen K L D σ (Iset K L σ hgen s a) φ z g - Tgen K L D σ (Jset K L s a) R φ z g‖ₑ := by
    intro s z
    rw [prinEquiv_smul, xi_prin_mul K L σ hξt]
    refine congrArg _ (tsum_congr fun a => ?_)
    rw [Kgen_Iset_eq_Kgen_I1_prin, Tgen_Jset_eq_Tgen_J1_prin]
  rw [hΩL.lintegral_eq_tsum'' fun ζ => ‖((ξ' ζ : ℂˣ) : ℂ)‖ₑ *
        ∑' a : N1 K L, ‖Kgen K L D σ (I1 K L σ hgen a) φ ζ g - Tgen K L D σ (J1 K L a) R φ ζ g‖ₑ,
    ← (prinEquiv K L σ).tsum_eq]
  simp_rw [hpt]
  exact tsum_setLIntegral_fibre_eq_Ffun K L D σ hgen νZL ΩL ξ' φ hφc hφs R hξc g

def HH (R : ℝ) (φ : AdelicGL2 (𝓞 L) L → ℂ) (ζ : (AdeleRing (𝓞 L) L)ˣ) (g : AdelicGL2 (𝓞 L) L) : ℂ :=
  ((ξ' ζ : ℂˣ) : ℂ) * Hfun K L D σ hgen R φ ζ g

theorem measurable_HH (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφc : Continuous φ) (hφs : HasCompactSupport φ) (R : ℝ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξ' z : ℂˣ) : ℂ)) (g : AdelicGL2 (𝓞 L) L) :
    Measurable fun ζ => HH K L D σ hgen ξ' R φ ζ g := by
  have h1 : (fun ζ => Hfun K L D σ hgen R φ ζ g) =
      fun ζ => Kgen K L D σ (I1u K L σ hgen) φ ζ g - Tgen K L D σ (J1u K L) R φ ζ g :=
    funext fun ζ => (Hfun_eq K L D σ hgen φ hφc hφs R ζ g).1
  have h0 := measurable_Kgen_sub_Tgen L K D σ (AutomorphicForm.adelicKernelLocalFiniteness L) φ hφc hφs R
      (I1u K L σ hgen) (J1u K L)
  have h2 : Measurable fun ζ => Kgen K L D σ (I1u K L σ hgen) φ ζ g - Tgen K L D σ (J1u K L) R φ ζ g :=
    Measurable.of_uncurry_left (f := fun (g' : AdelicGL2 (𝓞 L) L) (ζ : (AdeleRing (𝓞 L) L)ˣ) =>
      Kgen K L D σ (I1u K L σ hgen) φ ζ g' - Tgen K L D σ (J1u K L) R φ ζ g') h0
  rw [← h1] at h2
  exact hξc.measurable.mul h2

variable {ξ'} in
theorem HH_prin_mul (hξt : ∀ q : Lˣ, ξ' (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) q) = 1)
    (R : ℝ) (φ : AdelicGL2 (𝓞 L) L → ℂ) (s : Lˣ) (z : (AdeleRing (𝓞 L) L)ˣ) (g : AdelicGL2 (𝓞 L) L) :
    HH K L D σ hgen ξ' R φ (prin K L σ s * z) g = ((ξ' z : ℂˣ) : ℂ) *
      ∑' a : N1 K L, (Kgen K L D σ (Iset K L σ hgen s a) φ z g - Tgen K L D σ (Jset K L s a) R φ z g) := by
  rw [HH, xi_prin_mul K L σ hξt, tsum_fibre_eq_Hfun_prin]

variable {ξ'} in
theorem enorm_HH_prin_mul_le
    (hξt : ∀ q : Lˣ, ξ' (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) q) = 1)
    (R : ℝ) (φ : AdelicGL2 (𝓞 L) L → ℂ) (s : Lˣ) (z : (AdeleRing (𝓞 L) L)ˣ) (g : AdelicGL2 (𝓞 L) L) :
    ‖HH K L D σ hgen ξ' R φ (prin K L σ s * z) g‖ₑ ≤ ‖((ξ' z : ℂˣ) : ℂ)‖ₑ *
      ∑' a : N1 K L, ‖Kgen K L D σ (Iset K L σ hgen s a) φ z g - Tgen K L D σ (Jset K L s a) R φ z g‖ₑ := by
  rw [HH_prin_mul K L D σ hgen hξt, enorm_mul]
  exact mul_le_mul_right enorm_tsum_le_tsum_enorm _

theorem xi_mul_cusp_sub_eq_tsum_HH
    (hξt : ∀ q : Lˣ, ξ' (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) q) = 1)
    (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφc : Continuous φ) (hφs : HasCompactSupport φ) (R : ℝ)
    (z : (AdeleRing (𝓞 L) L)ˣ) (g : AdelicGL2 (𝓞 L) L) :
    ((ξ' z : ℂˣ) : ℂ) *
        (Kgen K L D σ (normUnipotentSet K L σ hgen ∩ (borelSubgroup L : Set (GL (Fin 2) L))) φ z g -
          Tgen K L D σ (borelNormOneSet K L) R φ z g) =
      ∑' s : Lˣ, HH K L D σ hgen ξ' R φ (prin K L σ s * z) g := by
  rw [(cusp_sub_eq_tsum_tsum K L D σ hgen φ hφc hφs R z g).1, ← tsum_mul_left]
  exact tsum_congr fun s => (HH_prin_mul K L D σ hgen hξt R φ s z g).symm

theorem setIntegral_cusp_eq_integral_unit (hΩL : IsFundamentalDomain
      (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range ΩL νZL)
    (hξt : ∀ q : Lˣ, ξ' (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) q) = 1)
    (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφc : Continuous φ) (hφs : HasCompactSupport φ) (R : ℝ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξ' z : ℂˣ) : ℂ)) (g : AdelicGL2 (𝓞 L) L)
    (hF : Ffun K L D σ hgen νZL ΩL ξ' R φ g < ⊤) :
    ∫ z in ΩL, ((ξ' z : ℂˣ) : ℂ) *
        (Kgen K L D σ (normUnipotentSet K L σ hgen ∩ (borelSubgroup L : Set (GL (Fin 2) L))) φ z g -
          Tgen K L D σ (borelNormOneSet K L) R φ z g) ∂νZL =
      ∫ ζ, HH K L D σ hgen ξ' R φ ζ g ∂νZL := by
  haveI := countable_range L
  haveI : Countable Lˣ := countable_units L
  haveI := smulInvariantMeasure_range L νZL
  have hHm := measurable_HH K L D σ hgen ξ' φ hφc hφs R hξc g
  have hsum_le : ∑' s : Lˣ, ∫⁻ z in ΩL, ‖HH K L D σ hgen ξ' R φ (prin K L σ s * z) g‖ₑ ∂νZL ≤
      Ffun K L D σ hgen νZL ΩL ξ' R φ g := by
    rw [← tsum_setLIntegral_fibre_eq_Ffun K L D σ hgen νZL ΩL ξ' φ hφc hφs R hξc g]
    exact ENNReal.tsum_le_tsum fun s => lintegral_mono fun z => enorm_HH_prin_mul_le K L D σ hgen hξt R φ s z g

  have hint : Integrable (fun ζ => HH K L D σ hgen ξ' R φ ζ g) νZL := by
    refine ⟨hHm.aestronglyMeasurable, ?_⟩
    show ∫⁻ ζ, ‖HH K L D σ hgen ξ' R φ ζ g‖ₑ ∂νZL < ⊤
    rw [hΩL.lintegral_eq_tsum'' fun ζ => ‖HH K L D σ hgen ξ' R φ ζ g‖ₑ, ← (prinEquiv K L σ).tsum_eq]
    simp_rw [prinEquiv_smul]
    exact hsum_le.trans_lt hF

  calc ∫ z in ΩL, ((ξ' z : ℂˣ) : ℂ) *
        (Kgen K L D σ (normUnipotentSet K L σ hgen ∩ (borelSubgroup L : Set (GL (Fin 2) L))) φ z g -
          Tgen K L D σ (borelNormOneSet K L) R φ z g) ∂νZL
      = ∫ z in ΩL, ∑' s : Lˣ, HH K L D σ hgen ξ' R φ (prin K L σ s * z) g ∂νZL :=
        integral_congr_ae (Filter.Eventually.of_forall fun z =>
          xi_mul_cusp_sub_eq_tsum_HH K L D σ hgen ξ' hξt φ hφc hφs R z g)
    _ = ∑' s : Lˣ, ∫ z in ΩL, HH K L D σ hgen ξ' R φ (prin K L σ s * z) g ∂νZL :=
        integral_tsum (fun s => ((hHm.comp (measurable_const_mul (prin K L σ s))).aestronglyMeasurable))
          (ne_of_lt (hsum_le.trans_lt hF))
    _ = ∑' γ : (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range,
          ∫ z in ΩL, HH K L D σ hgen ξ' R φ (γ • z) g ∂νZL := by
        rw [← (prinEquiv K L σ).tsum_eq]; simp_rw [prinEquiv_smul]
    _ = ∫ ζ, HH K L D σ hgen ξ' R φ ζ g ∂νZL := (hΩL.integral_eq_tsum'' _ hint).symm

theorem measurable_Ffun (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφc : Continuous φ) (hφs : HasCompactSupport φ) (R : ℝ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξ' z : ℂˣ) : ℂ)) :
    Measurable (Ffun K L D σ hgen νZL ΩL ξ' R φ) := by
  haveI : SecondCountableTopology (AdeleRing (𝓞 L) L)ˣ := secondCountableTopology_idele L
  haveI : SigmaFinite νZL := inferInstance
  haveI : Countable Lˣ := countable_units L
  have hG : Measurable fun p : AdelicGL2 (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ => Gfun K L D σ hgen R φ p.2 p.1 := by
    unfold Gfun
    refine Measurable.ennreal_tsum fun s => Measurable.ennreal_tsum fun a => ?_
    exact (measurable_Kgen_sub_Tgen L K D σ (AutomorphicForm.adelicKernelLocalFiniteness L) φ hφc hφs R _ _).enorm
  have h : Measurable fun p : AdelicGL2 (𝓞 L) L × (AdeleRing (𝓞 L) L)ˣ =>
      ‖((ξ' p.2 : ℂˣ) : ℂ)‖ₑ * Gfun K L D σ hgen R φ p.2 p.1 :=
    (hξc.comp continuous_snd).measurable.enorm.mul hG
  exact h.lintegral_prod_right' (ν := νZL.restrict ΩL)

end Unfold

end R1IwCentre

namespace R1IwCentre

section Outer

variable (F : Type) [Field F] [NumberField F]

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel
  NumberField.Idele.isHaarMeasure_idelicHaar

theorem sigmaFinite_idelicHaar : SigmaFinite (NumberField.Idele.idelicHaar F) := by
  haveI := secondCountableTopology_idele F
  infer_instance

theorem iwasawa_integral_congr (Φ : AdelicGL2 (𝓞 F) F → ℝ≥0∞) (hΦ : Measurable Φ) (P Q : AdelicGL2 (𝓞 F) F → ℂ)
    (hPQ : ∀ g, Φ g < ⊤ → P g = Q g) (X : Set (AdeleRing (𝓞 F) F)) (Ω₂ : Set (AdeleRing (𝓞 F) F)ˣ)
    (hfin : ∫⁻ x in X, ∫⁻ t in Ω₂, ∫⁻ k, Φ (unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 F) F)) *
        ENNReal.ofReal (NumberField.TateGlobal.ideleNorm F t)⁻¹
        ∂(maximalCompactHaar F) ∂(NumberField.Idele.idelicHaar F) ∂(adelicAddHaar (𝓞 F) F) ≠ ⊤) :
    (∫ x in X, ∫ t in Ω₂, ∫ k, P (unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 F) F)) *
        (((NumberField.TateGlobal.ideleNorm F t)⁻¹ : ℝ) : ℂ)
        ∂(maximalCompactHaar F) ∂(NumberField.Idele.idelicHaar F) ∂(adelicAddHaar (𝓞 F) F)) =
      ∫ x in X, ∫ t in Ω₂, ∫ k, Q (unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 F) F)) *
        (((NumberField.TateGlobal.ideleNorm F t)⁻¹ : ℝ) : ℂ)
        ∂(maximalCompactHaar F) ∂(NumberField.Idele.idelicHaar F) ∂(adelicAddHaar (𝓞 F) F) := by
  haveI : SecondCountableTopology (AdeleRing (𝓞 F) F) := NumberField.AdeleRing.secondCountableTopology F
  haveI : SecondCountableTopology (AdeleRing (𝓞 F) F)ˣ := secondCountableTopology_idele F
  haveI := sigmaFinite_idelicHaar F
  set C : ((AdeleRing (𝓞 F) F) × (AdeleRing (𝓞 F) F)ˣ) × adelicMaximalCompact F → ℝ≥0∞ := fun r =>
    Φ (unipotentGL2 r.1.1 * diagOne r.1.2 * (r.2 : AdelicGL2 (𝓞 F) F)) *
      ENNReal.ofReal (NumberField.TateGlobal.ideleNorm F r.1.2)⁻¹ with hC
  have hw : Continuous fun r : ((AdeleRing (𝓞 F) F) × (AdeleRing (𝓞 F) F)ˣ) × adelicMaximalCompact F =>
      unipotentGL2 r.1.1 * diagOne r.1.2 * (r.2 : AdelicGL2 (𝓞 F) F) :=
    (((AutomorphicForm.continuous_unipotentGL2 (R := AdeleRing (𝓞 F) F)).comp
      (continuous_fst.comp continuous_fst)).mul
      ((continuous_diagOne F).comp (continuous_snd.comp continuous_fst))).mul
      (continuous_subtype_val.comp continuous_snd)
  have hwt : Measurable fun t : (AdeleRing (𝓞 F) F)ˣ => ENNReal.ofReal (NumberField.TateGlobal.ideleNorm F t)⁻¹ :=
    ENNReal.measurable_ofReal.comp (NumberField.TateGlobal.continuous_ideleNorm F).measurable.inv
  have hCm : Measurable C := (hΦ.comp hw.measurable).mul (hwt.comp (measurable_snd.comp measurable_fst))
  have hBm : Measurable fun q : (AdeleRing (𝓞 F) F) × (AdeleRing (𝓞 F) F)ˣ =>
      ∫⁻ k, C (q, k) ∂(maximalCompactHaar F) := hCm.lintegral_prod_right'
  have hAm : Measurable fun x : AdeleRing (𝓞 F) F =>
      ∫⁻ t in Ω₂, ∫⁻ k, C ((x, t), k) ∂(maximalCompactHaar F) ∂(NumberField.Idele.idelicHaar F) :=
    hBm.lintegral_prod_right' (ν := (NumberField.Idele.idelicHaar F).restrict Ω₂)
  have h1 : ∀ᵐ x ∂(adelicAddHaar (𝓞 F) F).restrict X,
      ∫⁻ t in Ω₂, ∫⁻ k, C ((x, t), k) ∂(maximalCompactHaar F) ∂(NumberField.Idele.idelicHaar F) < ⊤ :=
    ae_lt_top' hAm.aemeasurable hfin
  refine integral_congr_ae (h1.mono fun x hx => ?_)
  have h2 : ∀ᵐ t ∂(NumberField.Idele.idelicHaar F).restrict Ω₂, ∫⁻ k, C ((x, t), k) ∂(maximalCompactHaar F) < ⊤ :=
    ae_lt_top' (hBm.comp measurable_prodMk_left).aemeasurable hx.ne
  refine integral_congr_ae (h2.mono fun t ht => ?_)
  have h3 : ∀ᵐ k ∂(maximalCompactHaar F), C ((x, t), k) < ⊤ :=
    ae_lt_top' (hCm.comp measurable_prodMk_left).aemeasurable ht.ne
  refine integral_congr_ae (h3.mono fun k hk => ?_)
  have hpos : ENNReal.ofReal (NumberField.TateGlobal.ideleNorm F t)⁻¹ ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (inv_pos.mpr (NumberField.TateGlobal.ideleNorm_pos t))).ne'
  have hΦk : Φ (unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 F) F)) < ⊤ :=
    ENNReal.lt_top_of_mul_ne_top_left hk.ne hpos
  show P _ * _ = Q _ * _
  rw [hPQ _ hΦk]

end Outer

end R1IwCentre

end

section Solution

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open AutomorphicForm AutomorphicForm.AdelicTracePushforward
open scoped TensorProduct Pointwise ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem solution
    (K L : Type)
    [Field K]
    [NumberField K]
    [Field L]
    [NumberField L]
    [Algebra K L]
    [IsGalois K L]
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ]
    [BorelSpace (AdeleRing (𝓞 L) L)ˣ]
    (νZL : Measure (AdeleRing (𝓞 L) L)ˣ)
    [νZL.IsHaarMeasure]
    (ΩL : Set (AdeleRing (𝓞 L) L)ˣ)
    (hΩL : IsFundamentalDomain
      (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range ΩL νZL)
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L)
    (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
        ξL ⟨z, Subgroup.mem_top z⟩ = 1)
    (φ : AdelicGL2 (𝓞 L) L → ℂ)
    (hφc : Continuous φ)
    (hφs : HasCompactSupport φ)
    (R : ℝ)
    (X : Set (AdeleRing (𝓞 L) L))
    (Ω₂ : Set (AdeleRing (𝓞 L) L)ˣ)
    (hfin : ∫⁻ x in X, ∫⁻ t in Ω₂, ∫⁻ k,
            (∫⁻ z in ΩL, ‖((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ₑ *
                ∑' s : Lˣ, ∑' a : {α : Lˣ // Algebra.norm K (α : L) = 1},
              ‖(∑ᶠ δ ∈ {δ : GL (Fin 2) L | δ ∈ TwistedBruhat.normUnipotentSet K L σ hgen ∧
                  (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (δ : Matrix (Fin 2) (Fin 2) L) 1 1 = (s : L) ∧
                  (δ : Matrix (Fin 2) (Fin 2) L) 0 0 = (s : L) * ((a : Lˣ) : L)},
                  φ ((unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 L) L))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
                    AutomorphicForm.sigmaAdelicAct K L D σ
                      (AutomorphicForm.centralScalar (𝓞 L) L z * (unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 L) L))))) -
                Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight L) (Real.exp R))
                (@AutomorphicForm.constantTerm _
                  (adeleBorel (𝓞 L) L) _ _
                  (@ProbabilityTheory.cond _ (adeleBorel (𝓞 L) L) (adelicAddHaar (𝓞 L) L) (adelicBox L))
                  (fun t => AutomorphicForm.unipotentGL2 t)
                  (fun y => ∑ᶠ δ ∈ {δ : GL (Fin 2) L |
                      (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (δ : Matrix (Fin 2) (Fin 2) L) 1 1 = (s : L) ∧
                      (δ : Matrix (Fin 2) (Fin 2) L) 0 0 = (s : L) * ((a : Lˣ) : L)},
                    φ ((unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 L) L))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
                      AutomorphicForm.sigmaAdelicAct K L D σ y)))
                  (AutomorphicForm.centralScalar (𝓞 L) L z * (unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 L) L)))‖ₑ ∂νZL) *
              ENNReal.ofReal (NumberField.TateGlobal.ideleNorm L t)⁻¹
          ∂(maximalCompactHaar L) ∂(NumberField.Idele.idelicHaar L)
        ∂(adelicAddHaar (𝓞 L) L) ≠ ⊤) :
    (∫ x in X, ∫ t in Ω₂, ∫ k,
            (∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
                (TwistedBruhat.cuspKernel K L D σ hgen φ z (unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 L) L)) - TwistedBruhat.cuspTruncation K L D σ R φ z (unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 L) L))) ∂νZL) *
              (((NumberField.TateGlobal.ideleNorm L t)⁻¹ : ℝ) : ℂ)
          ∂(maximalCompactHaar L) ∂(NumberField.Idele.idelicHaar L)
        ∂(adelicAddHaar (𝓞 L) L) =
      ∫ x in X, ∫ t in Ω₂, ∫ k,
            (∫ ζ, ((ξL ⟨ζ, Subgroup.mem_top ζ⟩ : ℂˣ) : ℂ) *
                ∑' a : {α : Lˣ // Algebra.norm K (α : L) = 1},
              ((∑ᶠ δ ∈ {δ : GL (Fin 2) L | δ ∈ TwistedBruhat.normUnipotentSet K L σ hgen ∧
                  (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (δ : Matrix (Fin 2) (Fin 2) L) 1 1 = 1 ∧
                  (δ : Matrix (Fin 2) (Fin 2) L) 0 0 = ((a : Lˣ) : L)},
                  φ ((unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 L) L))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
                    AutomorphicForm.sigmaAdelicAct K L D σ
                      (AutomorphicForm.centralScalar (𝓞 L) L ζ * (unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 L) L))))) -
                Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight L) (Real.exp R))
                (@AutomorphicForm.constantTerm _
                  (adeleBorel (𝓞 L) L) _ _
                  (@ProbabilityTheory.cond _ (adeleBorel (𝓞 L) L) (adelicAddHaar (𝓞 L) L) (adelicBox L))
                  (fun t => AutomorphicForm.unipotentGL2 t)
                  (fun y => ∑ᶠ δ ∈ {δ : GL (Fin 2) L |
                      (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (δ : Matrix (Fin 2) (Fin 2) L) 1 1 = 1 ∧
                      (δ : Matrix (Fin 2) (Fin 2) L) 0 0 = ((a : Lˣ) : L)},
                    φ ((unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 L) L))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
                      AutomorphicForm.sigmaAdelicAct K L D σ y)))
                  (AutomorphicForm.centralScalar (𝓞 L) L ζ * (unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 L) L)))) ∂νZL) *
              (((NumberField.TateGlobal.ideleNorm L t)⁻¹ : ℝ) : ℂ)
          ∂(maximalCompactHaar L) ∂(NumberField.Idele.idelicHaar L)
        ∂(adelicAddHaar (𝓞 L) L)) ∧
    (∫⁻ x in X, ∫⁻ t in Ω₂, ∫⁻ k,
            (∫⁻ ζ, ‖((ξL ⟨ζ, Subgroup.mem_top ζ⟩ : ℂˣ) : ℂ)‖ₑ *
                ∑' a : {α : Lˣ // Algebra.norm K (α : L) = 1},
              ‖(∑ᶠ δ ∈ {δ : GL (Fin 2) L | δ ∈ TwistedBruhat.normUnipotentSet K L σ hgen ∧
                  (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (δ : Matrix (Fin 2) (Fin 2) L) 1 1 = 1 ∧
                  (δ : Matrix (Fin 2) (Fin 2) L) 0 0 = ((a : Lˣ) : L)},
                  φ ((unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 L) L))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
                    AutomorphicForm.sigmaAdelicAct K L D σ
                      (AutomorphicForm.centralScalar (𝓞 L) L ζ * (unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 L) L))))) -
                Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight L) (Real.exp R))
                (@AutomorphicForm.constantTerm _
                  (adeleBorel (𝓞 L) L) _ _
                  (@ProbabilityTheory.cond _ (adeleBorel (𝓞 L) L) (adelicAddHaar (𝓞 L) L) (adelicBox L))
                  (fun t => AutomorphicForm.unipotentGL2 t)
                  (fun y => ∑ᶠ δ ∈ {δ : GL (Fin 2) L |
                      (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (δ : Matrix (Fin 2) (Fin 2) L) 1 1 = 1 ∧
                      (δ : Matrix (Fin 2) (Fin 2) L) 0 0 = ((a : Lˣ) : L)},
                    φ ((unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 L) L))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
                      AutomorphicForm.sigmaAdelicAct K L D σ y)))
                  (AutomorphicForm.centralScalar (𝓞 L) L ζ * (unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 L) L)))‖ₑ ∂νZL) *
              ENNReal.ofReal (NumberField.TateGlobal.ideleNorm L t)⁻¹
          ∂(maximalCompactHaar L) ∂(NumberField.Idele.idelicHaar L)
        ∂(adelicAddHaar (𝓞 L) L) ≠ ⊤) := by
  set ξ' : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ := ξL.comp (R1IwCentre.toTop (AdeleRing (𝓞 L) L)ˣ) with hξ'
  have hξ'_apply : ∀ z : (AdeleRing (𝓞 L) L)ˣ, ξ' z = ξL ⟨z, Subgroup.mem_top z⟩ := fun z => rfl
  have hξt' : ∀ q : Lˣ, ξ' (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) q) = 1 :=
    fun q => (hξ'_apply _).trans (hξt _ ⟨q, rfl⟩)
  have hξc' : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξ' z : ℂˣ) : ℂ) := hξc
  have hA : (fun g : AdelicGL2 (𝓞 L) L => ∫⁻ ζ, ‖((ξ' ζ : ℂˣ) : ℂ)‖ₑ *
      ∑' a : R1IwCentre.N1 K L, ‖R1IwCentre.Kgen K L D σ (R1IwCentre.I1 K L σ hgen a) φ ζ g -
        R1IwCentre.Tgen K L D σ (R1IwCentre.J1 K L a) R φ ζ g‖ₑ ∂νZL) =
      R1IwCentre.Ffun K L D σ hgen νZL ΩL ξ' R φ :=
    funext fun g => R1IwCentre.lintegral_unit_eq_Ffun K L D σ hgen νZL ΩL ξ' hΩL hξt' φ hφc hφs R hξc' g
  refine ⟨?_, ?_⟩
  · exact R1IwCentre.iwasawa_integral_congr L (R1IwCentre.Ffun K L D σ hgen νZL ΩL ξ' R φ)
      (R1IwCentre.measurable_Ffun K L D σ hgen νZL ΩL ξ' φ hφc hφs R hξc')
      (fun g => ∫ z in ΩL, ((ξ' z : ℂˣ) : ℂ) *
        (R1IwCentre.Kgen K L D σ (TwistedBruhat.normUnipotentSet K L σ hgen ∩ (borelSubgroup L : Set (GL (Fin 2) L))) φ z g -
          R1IwCentre.Tgen K L D σ (TwistedBruhat.borelNormOneSet K L) R φ z g) ∂νZL)
      (fun g => ∫ ζ, R1IwCentre.HH K L D σ hgen ξ' R φ ζ g ∂νZL)
      (fun g hg => R1IwCentre.setIntegral_cusp_eq_integral_unit K L D σ hgen νZL ΩL ξ' hΩL hξt' φ hφc hφs R hξc' g hg)
      X Ω₂ hfin
  · show (∫⁻ x in X, ∫⁻ t in Ω₂, ∫⁻ k,
        (fun g : AdelicGL2 (𝓞 L) L => ∫⁻ ζ, ‖((ξ' ζ : ℂˣ) : ℂ)‖ₑ *
          ∑' a : R1IwCentre.N1 K L, ‖R1IwCentre.Kgen K L D σ (R1IwCentre.I1 K L σ hgen a) φ ζ g -
            R1IwCentre.Tgen K L D σ (R1IwCentre.J1 K L a) R φ ζ g‖ₑ ∂νZL)
          (unipotentGL2 x * diagOne t * (k : AdelicGL2 (𝓞 L) L)) *
        ENNReal.ofReal (NumberField.TateGlobal.ideleNorm L t)⁻¹
        ∂(maximalCompactHaar L) ∂(NumberField.Idele.idelicHaar L) ∂(adelicAddHaar (𝓞 L) L)) ≠ ⊤
    rw [hA]
    exact hfin

end Solution

end S_AutomorphicForm_TwistedBruhat_integral_iwasawa_cuspKernel_sub_cuspTruncation_eq_integral_tsum_normOneFibre_of_fibrewise
end P2MW
export P2MW.S_AutomorphicForm_TwistedBruhat_integral_iwasawa_cuspKernel_sub_cuspTruncation_eq_integral_tsum_normOneFibre_of_fibrewise (solution)
