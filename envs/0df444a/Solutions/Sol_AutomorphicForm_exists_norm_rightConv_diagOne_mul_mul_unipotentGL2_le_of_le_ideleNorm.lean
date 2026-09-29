-- Prove2me | solution 1 for AutomorphicForm.exists_norm_rightConv_diagOne_mul_mul_unipotentGL2_le_of_le_ideleNorm
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/9eaef54d-08d2-504e-ab14-f1f1ca460b3f

import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_BoundedGenuineCuspRealization
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_AdelicFourier
import Definitions.Def_NumberField_AdelicHeight
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm
import Theorems.Thm_AutomorphicForm_isIdeleClassChar_and_continuous_of_isLsXiFunction_of_continuous
import Theorems.Thm_NumberField_TateGlobal_exists_norm_apply_eq_ideleNorm_rpow
import Theorems.Thm_AutomorphicForm_exists_forall_norm_rightConv_le_of_ideleNorm_det_mem_Icc
import Theorems.Thm_AutomorphicForm_exists_norm_rightConv_le_mul_inv_adelicHeight_pow_of_ideleNorm_det_mem_Icc
import Theorems.Thm_NumberField_AdelicHeight_adelicHeight_diagOne_mul
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm_det
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_norm_rightConv_diagOne_mul_mul_unipotentGL2_le_of_le_ideleNorm
p2m_attr_erase "instance" "instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar MeasureTheory
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain NumberField.TateGlobal NumberField.AdelicHeight
open NumberField.InfinitePlace AutomorphicForm.SiegelCoordinates AutomorphicForm.SiegelReduction

noncomputable section

namespace C5aD4

section Local
variable {K : Type*} [NormedField K]

theorem finLocalHeight_upper_entries_mul {s : GL (Fin 2) K} {a t : K} (ht : t ≠ 0)
    (h00 : (s : Matrix (Fin 2) (Fin 2) K) 0 0 = a) (h10 : (s : Matrix (Fin 2) (Fin 2) K) 1 0 = 0)
    (h11 : (s : Matrix (Fin 2) (Fin 2) K) 1 1 = t) (g : GL (Fin 2) K) :
    finLocalHeight (s * g) = ‖a‖ / ‖t‖ * finLocalHeight g := by
  have hrow : rowMaxNorm ((s * g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      = ‖t‖ * rowMaxNorm (g : Matrix (Fin 2) (Fin 2) K) := by
    have e10 : ((s * g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 0 = t * (g : Matrix (Fin 2) (Fin 2) K) 1 0 := by
      rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, h10, h11, zero_mul, zero_add]
    have e11 : ((s * g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 1 = t * (g : Matrix (Fin 2) (Fin 2) K) 1 1 := by
      rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, h10, h11, zero_mul, zero_add]
    simp only [rowMaxNorm, e10, e11, norm_mul]
    exact (mul_max_of_nonneg _ _ (norm_nonneg t)).symm
  have hdet : ‖((s * g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det‖
      = ‖a‖ * ‖t‖ * ‖(g : Matrix (Fin 2) (Fin 2) K).det‖ := by
    rw [Units.val_mul, Matrix.det_mul, norm_mul, Matrix.det_fin_two, h00, h10, h11, mul_zero, sub_zero, norm_mul]
  have hr : 0 < rowMaxNorm (g : Matrix (Fin 2) (Fin 2) K) := rowMaxNorm_pos g
  have htn : 0 < ‖t‖ := norm_pos_iff.mpr ht
  rw [finLocalHeight, finLocalHeight, hrow, hdet]
  field_simp

end Local

variable (F : Type) [Field F] [NumberField F]

theorem adelicHeight_centralScalar_mul (z : (AdeleRing (𝓞 F) F)ˣ) (h : AdelicGL2 (𝓞 F) F) :
    adelicHeight F (centralScalar (𝓞 F) F z * h) = adelicHeight F h := by
  have harch : archHeight F (glArch (𝓞 F) F (centralScalar (𝓞 F) F z) * glArch (𝓞 F) F h)
      = archHeight F (glArch (𝓞 F) F h) := by
    unfold archHeight
    refine Finset.prod_congr rfl fun w _ => ?_
    have hz : ((z : AdeleRing (𝓞 F) F).1 w) ≠ 0 := by
      intro h0
      have := congrArg (fun x : AdeleRing (𝓞 F) F => x.1 w) z.mul_inv
      try simp only [Units.val_mul] at this
      change (z : AdeleRing (𝓞 F) F).1 w * ((z⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 w = 1 at this
      rw [h0, zero_mul] at this
      exact zero_ne_one this
    rw [map_mul, localHeight_upper_entries_mul (a := (z : AdeleRing (𝓞 F) F).1 w) (t := (z : AdeleRing (𝓞 F) F).1 w)
      hz ?_ ?_ ?_ (archComponent F w (glArch (𝓞 F) F h)), div_self (norm_ne_zero_iff.mpr hz), one_mul]
    · rw [archComponent_apply, glArch_apply]; rfl
    · rw [archComponent_apply, glArch_apply]; rfl
    · rw [archComponent_apply, glArch_apply]; rfl
  have hfin : finHeight F (glFin (𝓞 F) F (centralScalar (𝓞 F) F z) * glFin (𝓞 F) F h)
      = finHeight F (glFin (𝓞 F) F h) := by
    unfold finHeight
    refine finprod_congr fun v => ?_
    have hz : ((z : AdeleRing (𝓞 F) F).2 v) ≠ 0 := by
      intro h0
      have := congrArg (fun x : AdeleRing (𝓞 F) F => x.2 v) z.mul_inv
      change (z : AdeleRing (𝓞 F) F).2 v * ((z⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v = 1 at this
      rw [h0, zero_mul] at this
      exact zero_ne_one this
    rw [map_mul, finLocalHeight_upper_entries_mul (a := (z : AdeleRing (𝓞 F) F).2 v) (t := (z : AdeleRing (𝓞 F) F).2 v)
      hz ?_ ?_ ?_ (finComponent (𝓞 F) F v (glFin (𝓞 F) F h)), div_self (norm_ne_zero_iff.mpr hz), one_mul]
    · rw [finComponent_apply, glFin_apply]; rfl
    · rw [finComponent_apply, glFin_apply]; rfl
    · rw [finComponent_apply, glFin_apply]; rfl
  unfold adelicHeight
  rw [map_mul, map_mul, harch, hfin]

theorem det_diagOne_mul_mul_unipotentGL2 (a : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F)
    (x : AdeleRing (𝓞 F) F) :
    Matrix.GeneralLinearGroup.det (diagOne a * g * unipotentGL2 x) = a * Matrix.GeneralLinearGroup.det g := by
  have h1 : Matrix.GeneralLinearGroup.det (diagOne a : AdelicGL2 (𝓞 F) F) = a := by
    refine Units.ext ?_
    simp [diagOne, Matrix.GeneralLinearGroup.val_det_apply]
  have h2 : Matrix.GeneralLinearGroup.det (unipotentGL2 x : AdelicGL2 (𝓞 F) F) = 1 := by
    refine Units.ext ?_
    simp [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two_of]
  rw [map_mul, map_mul, h1, h2, mul_one]

end C5aD4

namespace C5aD4

variable (F : Type) [Field F] [NumberField F]

theorem exists_one_lt_ideleNorm : ∃ z : (AdeleRing (𝓞 F) F)ˣ, 1 < ideleNorm F z := by
  classical
  obtain ⟨w₀⟩ := (inferInstance : Nonempty (InfinitePlace F))
  have h2 : ((2 : F) : w₀.Completion) ≠ 0 := by
    rw [← norm_pos_iff, norm_coe_completion]
    exact InfinitePlace.pos_iff.mpr two_ne_zero
  refine ⟨archUnitHom w₀ (Units.mk0 _ h2), ?_⟩
  have hmod := NumberField.AdeleRing.distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm F
    (archUnitHom w₀ (Units.mk0 _ h2))
  have hval1 : ∀ w : InfinitePlace F, ((archUnitHom w₀ (Units.mk0 _ h2) : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 w
      = Function.update (1 : InfiniteAdeleRing F) w₀ ((2 : F) : w₀.Completion) w := fun w => rfl
  have hval2 : ((archUnitHom w₀ (Units.mk0 _ h2) : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 = 1 := rfl
  have hw2 : w₀ (2 : F) = 2 := by
    rw [← mk_embedding w₀, InfinitePlace.apply, map_ofNat, Complex.norm_ofNat]
  unfold ideleNorm
  rw [hmod, hval2]
  simp only [hval1]
  rw [finprod_eq_one_of_forall_eq_one (fun v => by rw [show (1 : FiniteAdeleRing (𝓞 F) F) v = 1 from rfl, norm_one]), mul_one,
    Finset.prod_eq_single w₀ (fun w _ hw => by rw [Function.update_of_ne hw, show (1 : InfiniteAdeleRing F) w = 1 from rfl, norm_one, one_pow]) (fun h => absurd (Finset.mem_univ _) h),
    Function.update_self, norm_coe_completion, hw2]
  have hm : 1 ≤ w₀.mult := Nat.one_le_iff_ne_zero.mpr (mult_ne_zero)
  exact one_lt_pow₀ one_lt_two (by omega)

end C5aD4

namespace C5aD4

variable {F : Type} [Field F] [NumberField F]

theorem ideleNorm_one' : ideleNorm F (1 : (AdeleRing (𝓞 F) F)ˣ) = 1 := by
  simp [ideleNorm]

theorem ideleNorm_pow (z : (AdeleRing (𝓞 F) F)ˣ) (n : ℕ) : ideleNorm F (z ^ n) = ideleNorm F z ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero]; exact ideleNorm_one'
  | succ n ih => rw [pow_succ, ideleNorm_mul, ih, pow_succ]

theorem ideleNorm_inv (z : (AdeleRing (𝓞 F) F)ˣ) : ideleNorm F z⁻¹ = (ideleNorm F z)⁻¹ := by
  have h := ideleNorm_mul (F := F) z z⁻¹
  rw [mul_inv_cancel, ideleNorm_one'] at h
  exact (eq_inv_of_mul_eq_one_right h.symm)

theorem ideleNorm_zpow (z : (AdeleRing (𝓞 F) F)ˣ) (m : ℤ) : ideleNorm F (z ^ m) = ideleNorm F z ^ m := by
  cases m with
  | ofNat n => rw [Int.ofNat_eq_coe, zpow_natCast, zpow_natCast, ideleNorm_pow]
  | negSucc n => rw [zpow_negSucc, zpow_negSucc, ideleNorm_inv, ideleNorm_pow]

theorem det_centralScalar (z : (AdeleRing (𝓞 F) F)ˣ) :
    Matrix.GeneralLinearGroup.det (centralScalar (𝓞 F) F z) = z ^ 2 := by
  refine Units.ext ?_
  simp [centralScalar, Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, pow_two]

theorem rightConv_centralScalar_mul {φ : AdelicGL2 (𝓞 F) F → ℂ} {z : (AdeleRing (𝓞 F) F)ˣ} {cz : ℂ}
    (hφ : ∀ g : AdelicGL2 (𝓞 F) F, φ (centralScalar (𝓞 F) F z * g) = cz * φ g)
    (f : AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F) :
    rightConv F φ f (centralScalar (𝓞 F) F z * g) = cz * rightConv F φ f g := by
  rw [← rightConv_comp_mul_left]
  simp only [rightConv, hφ, mul_assoc]
  exact integral_const_mul _ _

theorem zpow_rpow_le {b y t : ℝ} (hb : 1 < b) (hy : 0 < y) {m : ℤ}
    (h1 : (b ^ 2) ^ m ≤ y) (h2 : y < (b ^ 2) ^ (m + 1)) :
    (b ^ m) ^ t ≤ (b ^ 2) ^ (|t| / 2) * y ^ (t / 2) := by
  have hb0 : 0 < b := lt_trans zero_lt_one hb
  have hbm : 0 < b ^ m := zpow_pos hb0 m
  have hB : 1 ≤ b ^ 2 := by nlinarith
  have hsq : (b ^ m) ^ (2 : ℝ) = (b ^ 2) ^ m := by
    rw [Real.rpow_two, ← zpow_natCast, ← zpow_mul, ← zpow_natCast, ← zpow_mul, mul_comm]
  rcases le_or_gt 0 t with ht | ht
  ·
    have e : (b ^ m) ^ t = ((b ^ m) ^ (2 : ℝ)) ^ (t / 2) := by
      rw [← Real.rpow_mul hbm.le]; congr 1; ring
    rw [e, hsq]
    calc ((b ^ 2) ^ m) ^ (t / 2) ≤ y ^ (t / 2) :=
          Real.rpow_le_rpow (zpow_pos (by positivity) m).le h1 (by linarith)
      _ ≤ (b ^ 2) ^ (|t| / 2) * y ^ (t / 2) :=
          le_mul_of_one_le_left (Real.rpow_nonneg hy.le _) (Real.one_le_rpow hB (by positivity))
  ·
    have e : (b ^ m) ^ t = ((b ^ m) ^ (2 : ℝ)) ^ (t / 2) := by
      rw [← Real.rpow_mul hbm.le]; congr 1; ring
    rw [e, hsq]
    have hlt : y / b ^ 2 < (b ^ 2) ^ m := by
      rw [div_lt_iff₀ (by positivity), ← zpow_add_one₀ (by positivity)]
      exact h2
    have ht2 : t / 2 ≤ 0 := by linarith
    calc ((b ^ 2) ^ m) ^ (t / 2) ≤ (y / b ^ 2) ^ (t / 2) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) hlt.le ht2
      _ = (b ^ 2) ^ (|t| / 2) * y ^ (t / 2) := by
          rw [Real.div_rpow hy.le (by positivity), abs_of_neg ht, div_eq_mul_inv, mul_comm,
            ← Real.rpow_neg (by positivity)]
          congr 1; ring_nf

end C5aD4

end

open C5aD4 in
theorem solution
    (F : Type) [Field F] [NumberField F]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (ξ : (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).Z →* ℂˣ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hφ : IsCuspAutomorphicFnAt F
      (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ φ)
    (hcont : Continuous φ)
    (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : IsFactorizableTestFn F f)
    (C : Set (AdelicGL2 (𝓞 F) F)) (hC : IsCompact C) (k : ℕ) :
    ∃ A₀ Cst : ℝ, ∃ M : ℕ, ∀ (a : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F) (x : AdeleRing (𝓞 F) F),
      g ∈ C → A₀ ≤ ideleNorm F a →
        ‖rightConv F φ f (diagOne a * g * unipotentGL2 x)‖ ≤
          Cst * (ideleNorm F a)⁻¹ ^ k * (adelicHeight F (g * unipotentGL2 x))⁻¹ ^ M := by
  classical

  by_cases hφ0 : ¬ ∃ g, φ g ≠ 0
  · push Not at hφ0
    refine ⟨0, 0, 0, fun a g x _ _ => ?_⟩
    have hz : φ = fun _ => (0 : ℂ) := funext hφ0
    rw [hz, rightConv_zero_left]
    simp
  push Not at hφ0
  rcases C.eq_empty_or_nonempty with hCe | hCne
  · exact ⟨0, 0, 0, fun a g x hg => by simp [hCe] at hg⟩

  have hls : IsLsXiFunction (𝓞 F) F _ ξ φ := by
    letI := (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).mS
    exact ((lsXiMemberAt_iff _ _ _ _ ξ _ φ).mp hφ.1).1
  obtain ⟨hcls, hξc⟩ :=
    AutomorphicForm.isIdeleClassChar_and_continuous_of_isLsXiFunction_of_continuous F ξ φ hls hcont hφ0
  let μ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ :=
    { toFun := fun z => ξ ⟨z, Subgroup.mem_top z⟩
      map_one' := by
        show ξ 1 = 1
        exact map_one ξ
      map_mul' := fun z z' => by
        show ξ (⟨z, Subgroup.mem_top z⟩ * ⟨z', Subgroup.mem_top z'⟩) = _
        exact map_mul ξ _ _ }
  have hμ : ∀ z, μ z = ξ ⟨z, Subgroup.mem_top z⟩ := fun z => rfl
  obtain ⟨t, ht⟩ := NumberField.TateGlobal.exists_norm_apply_eq_ideleNorm_rpow F μ (fun u => hcls u) hξc

  obtain ⟨z₀, hz₀⟩ := exists_one_lt_ideleNorm F
  set b : ℝ := ideleNorm F z₀ with hbdef
  have hb0 : 0 < b := lt_trans zero_lt_one hz₀
  have hB1 : 1 < b ^ 2 := by nlinarith

  have hdetc := (NumberField.TateGlobal.continuous_ideleNorm_det F).continuousOn (s := C)
  obtain ⟨gmin, hgmin, hmin⟩ := hC.exists_isMinOn hCne hdetc
  obtain ⟨gmax, hgmax, hmax⟩ := hC.exists_isMaxOn hCne hdetc
  set α : ℝ := ideleNorm F (Matrix.GeneralLinearGroup.det gmin) with hαdef
  set β : ℝ := ideleNorm F (Matrix.GeneralLinearGroup.det gmax) with hβdef
  have hα : 0 < α := ideleNorm_pos _

  set τ : ℕ := ⌈|t| / 2⌉₊ with hτdef
  obtain ⟨H₀, Cst₁, hdecay⟩ :=
    AutomorphicForm.exists_norm_rightConv_le_mul_inv_adelicHeight_pow_of_ideleNorm_det_mem_Icc F c u d₁ d₂ T hd hcov ξ φ
      hφ hcont f hf 1 (b ^ 2) one_pos (k + τ)
  obtain ⟨M₁, hslab⟩ :=
    AutomorphicForm.exists_forall_norm_rightConv_le_of_ideleNorm_det_mem_Icc F c u d₁ d₂ T hd hcov ξ φ hφ hcont f hf
      1 (b ^ 2) one_pos

  set H₁ : ℝ := max H₀ 1 with hH₁def
  set K₂ : ℝ := max (α ^ (t / 2)) (β ^ (t / 2)) with hK₂def
  set K₃ : ℝ := (b ^ 2) ^ (|t| / 2) * K₂ with hK₃def
  refine ⟨1, K₃ * (max Cst₁ 0 + max M₁ 0 * H₁ ^ (k + τ)), k + τ, fun a g x hg ha => ?_⟩

  obtain ⟨h, hhdef⟩ : ∃ h : AdelicGL2 (𝓞 F) F, h = diagOne a * g * unipotentGL2 x := ⟨_, rfl⟩
  obtain ⟨Hgx, hHgxdef⟩ : ∃ H : ℝ, H = adelicHeight F (g * unipotentGL2 x) := ⟨_, rfl⟩
  rw [← hhdef, ← hHgxdef]
  obtain ⟨y, hydef⟩ : ∃ y : ℝ, y = ideleNorm F (Matrix.GeneralLinearGroup.det h) := ⟨_, rfl⟩
  have hdetg : α ≤ ideleNorm F (Matrix.GeneralLinearGroup.det g) ∧ ideleNorm F (Matrix.GeneralLinearGroup.det g) ≤ β :=
    ⟨hmin hg, hmax hg⟩
  have hy : y = ideleNorm F a * ideleNorm F (Matrix.GeneralLinearGroup.det g) := by
    rw [hydef, hhdef, det_diagOne_mul_mul_unipotentGL2, ideleNorm_mul]
  have ha0 : 0 < ideleNorm F a := ideleNorm_pos a
  have ha1 : 1 ≤ ideleNorm F a := ha
  have hy0 : 0 < y := by rw [hy]; exact mul_pos ha0 (lt_of_lt_of_le hα hdetg.1)
  have hHgx : 0 < Hgx := by rw [hHgxdef]; exact adelicHeight_pos _
  have hHh : adelicHeight F h = ideleNorm F a * Hgx := by
    rw [hhdef, hHgxdef, mul_assoc, NumberField.AdelicHeight.adelicHeight_diagOne_mul]

  obtain ⟨m, hm1, hm2⟩ := exists_mem_Ico_zpow hy0 hB1
  obtain ⟨z, hzdef⟩ : ∃ z : (AdeleRing (𝓞 F) F)ˣ, z = z₀ ^ (-m) := ⟨_, rfl⟩
  have hnz : ideleNorm F z = b ^ (-m) := by rw [hzdef, ideleNorm_zpow]
  obtain ⟨h', hh'def⟩ : ∃ h' : AdelicGL2 (𝓞 F) F, h' = centralScalar (𝓞 F) F z * h := ⟨_, rfl⟩
  have hdet' : ideleNorm F (Matrix.GeneralLinearGroup.det h') ∈ Set.Icc 1 (b ^ 2) := by
    have e : ideleNorm F (Matrix.GeneralLinearGroup.det h') = (b ^ 2) ^ (-m) * y := by
      rw [hh'def, map_mul, ideleNorm_mul, det_centralScalar, ideleNorm_pow, hnz, ← hydef]
      congr 1
      rw [← zpow_natCast, ← zpow_natCast b 2, ← zpow_mul, ← zpow_mul, mul_comm]
    rw [e]
    constructor
    ·
      have := mul_le_mul_of_nonneg_left hm1 (zpow_nonneg (by positivity : (0:ℝ) ≤ b ^ 2) (-m))
      rwa [← zpow_add₀ (by positivity), neg_add_cancel, zpow_zero] at this
    · have := mul_le_mul_of_nonneg_left hm2.le (zpow_nonneg (by positivity : (0:ℝ) ≤ b ^ 2) (-m))
      rwa [← zpow_add₀ (by positivity), show -m + (m + 1) = (1 : ℤ) by ring, zpow_one] at this
  have hH' : adelicHeight F h' = adelicHeight F h := by rw [hh'def]; exact adelicHeight_centralScalar_mul F z h

  have hcen : rightConv F φ f h' = ((μ z : ℂˣ) : ℂ) * rightConv F φ f h := by
    rw [hh'def]
    exact rightConv_centralScalar_mul (fun g' => hls.central_transform ⟨z, Subgroup.mem_top z⟩ g') f h
  have hμn : ‖((μ z : ℂˣ) : ℂ)‖ = (b ^ (-m)) ^ t := by rw [ht z, hnz]
  have hμpos : 0 < ‖((μ z : ℂˣ) : ℂ)‖ := by rw [hμn]; exact Real.rpow_pos_of_pos (zpow_pos hb0 _) t
  have hnorm : ‖rightConv F φ f h‖ = (b ^ m) ^ t * ‖rightConv F φ f h'‖ := by
    rw [hcen, norm_mul, hμn, ← mul_assoc, ← Real.mul_rpow (zpow_pos hb0 m).le (zpow_pos hb0 (-m)).le,
      ← zpow_add₀ hb0.ne', add_neg_cancel, zpow_zero, Real.one_rpow, one_mul]

  have hbt : (b ^ m) ^ t ≤ (b ^ 2) ^ (|t| / 2) * y ^ (t / 2) := zpow_rpow_le hz₀ hy0 hm1 hm2
  have hyt : y ^ (t / 2) ≤ K₂ * ideleNorm F a ^ (|t| / 2) := by
    rw [hy, Real.mul_rpow ha0.le (lt_of_lt_of_le hα hdetg.1).le, mul_comm]
    refine mul_le_mul ?_ ?_ (Real.rpow_nonneg ha0.le _) (le_trans (Real.rpow_nonneg hα.le _) (le_max_left _ _))
    ·
      rcases le_or_gt 0 t with ht0 | ht0
      · exact (Real.rpow_le_rpow (lt_of_lt_of_le hα hdetg.1).le hdetg.2 (by linarith)).trans (le_max_right _ _)
      · exact (Real.rpow_le_rpow_of_nonpos hα hdetg.1 (by linarith)).trans (le_max_left _ _)
    ·
      exact Real.rpow_le_rpow_of_exponent_le ha1 (by linarith [le_abs_self t])
  have hK₂0 : 0 ≤ K₂ := le_trans (Real.rpow_nonneg hα.le _) (le_max_left _ _)
  have hK₃0 : 0 ≤ K₃ := mul_nonneg (Real.rpow_nonneg (by positivity) _) hK₂0
  have hcoef : (b ^ m) ^ t ≤ K₃ * ideleNorm F a ^ (|t| / 2) := by
    refine hbt.trans ?_
    rw [hK₃def, mul_assoc]
    exact mul_le_mul_of_nonneg_left hyt (Real.rpow_nonneg (by positivity) _)

  have hτ : |t| / 2 ≤ (τ : ℝ) := Nat.le_ceil _
  have hat : ideleNorm F a ^ (|t| / 2) ≤ ideleNorm F a ^ (τ : ℝ) := Real.rpow_le_rpow_of_exponent_le ha1 hτ

  have hgoalform : K₃ * (max Cst₁ 0 + max M₁ 0 * H₁ ^ (k + τ)) * (ideleNorm F a)⁻¹ ^ k * Hgx⁻¹ ^ (k + τ)
      = K₃ * max Cst₁ 0 * ((ideleNorm F a)⁻¹ ^ k * Hgx⁻¹ ^ (k + τ))
        + K₃ * (max M₁ 0 * H₁ ^ (k + τ)) * ((ideleNorm F a)⁻¹ ^ k * Hgx⁻¹ ^ (k + τ)) := by ring
  rw [hgoalform, hnorm]
  by_cases hreg : H₀ ≤ adelicHeight F h'
  ·
    have h1 := hdecay h' hdet' hreg
    rw [hH', hHh] at h1

    have h2 : (b ^ m) ^ t * ‖rightConv F φ f h'‖
        ≤ (K₃ * ideleNorm F a ^ (τ : ℝ)) * (max Cst₁ 0 * (ideleNorm F a * Hgx)⁻¹ ^ (k + τ)) := by
      refine mul_le_mul (hcoef.trans (mul_le_mul_of_nonneg_left hat hK₃0)) (h1.trans ?_) (norm_nonneg _)
        (mul_nonneg hK₃0 (Real.rpow_nonneg ha0.le _))
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    refine h2.trans ?_
    have e : K₃ * ideleNorm F a ^ (τ : ℝ) * (max Cst₁ 0 * (ideleNorm F a * Hgx)⁻¹ ^ (k + τ))
        = K₃ * max Cst₁ 0 * ((ideleNorm F a)⁻¹ ^ k * Hgx⁻¹ ^ (k + τ)) := by
      have ha' : ideleNorm F a ≠ 0 := ha0.ne'
      have hH' : Hgx ≠ 0 := hHgx.ne'
      rw [Real.rpow_natCast]
      simp only [mul_inv, mul_pow, inv_pow]
      field_simp
      ring
    rw [e]
    exact le_add_of_nonneg_right (by positivity)
  ·
    push Not at hreg
    have h1 := hslab h' hdet'
    rw [hH', hHh] at hreg

    have hprod : (ideleNorm F a * Hgx) ^ (k + τ) ≤ H₁ ^ (k + τ) :=
      pow_le_pow_left₀ (by positivity) (hreg.le.trans (le_max_left _ _)) _
    have h2 : (b ^ m) ^ t * ‖rightConv F φ f h'‖ ≤ (K₃ * ideleNorm F a ^ (τ : ℝ)) * max M₁ 0 :=
      mul_le_mul (hcoef.trans (mul_le_mul_of_nonneg_left hat hK₃0)) (h1.trans (le_max_left _ _)) (norm_nonneg _)
        (mul_nonneg hK₃0 (Real.rpow_nonneg ha0.le _))
    refine h2.trans (le_add_of_nonneg_of_le (by positivity) ?_)

    rw [Real.rpow_natCast]
    have hH₁ : 1 ≤ H₁ := le_max_right _ _
    have key : ideleNorm F a ^ τ ≤ H₁ ^ (k + τ) * ((ideleNorm F a)⁻¹ ^ k * Hgx⁻¹ ^ (k + τ)) := by

      rw [inv_pow, inv_pow, ← mul_inv, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
      calc ideleNorm F a ^ τ * (ideleNorm F a ^ k * Hgx ^ (k + τ))
          = (ideleNorm F a * Hgx) ^ (k + τ) := by rw [mul_pow, pow_add]; ring
        _ ≤ H₁ ^ (k + τ) := hprod
    calc K₃ * ideleNorm F a ^ τ * max M₁ 0 = K₃ * max M₁ 0 * ideleNorm F a ^ τ := by ring
      _ ≤ K₃ * max M₁ 0 * (H₁ ^ (k + τ) * ((ideleNorm F a)⁻¹ ^ k * Hgx⁻¹ ^ (k + τ))) :=
          mul_le_mul_of_nonneg_left key (by positivity)
      _ = K₃ * (max M₁ 0 * H₁ ^ (k + τ)) * ((ideleNorm F a)⁻¹ ^ k * Hgx⁻¹ ^ (k + τ)) := by ring

end S_AutomorphicForm_exists_norm_rightConv_diagOne_mul_mul_unipotentGL2_le_of_le_ideleNorm
end P2MW
export P2MW.S_AutomorphicForm_exists_norm_rightConv_diagOne_mul_mul_unipotentGL2_le_of_le_ideleNorm (solution)
