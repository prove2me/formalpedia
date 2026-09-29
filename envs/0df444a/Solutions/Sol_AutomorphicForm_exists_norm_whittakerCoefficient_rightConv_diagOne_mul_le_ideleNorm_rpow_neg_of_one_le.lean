-- Prove2me | solution 1 for AutomorphicForm.exists_norm_whittakerCoefficient_rightConv_diagOne_mul_le_ideleNorm_rpow_neg_of_one_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/a11e737a-5b0a-54f8-a0df-27c33df6a788

import Mathlib
import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_AdelicTraceFin
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace

import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Theorems.Thm_AutomorphicForm_hasDerivAt_rightConv_mul_unipotentGL2_and_isFactorizableTestFn_leftDeriv_and_linear
import Theorems.Thm_AutomorphicForm_exists_norm_whittakerCoefficient_le_mul_of_hasDerivAt_unipotentGL2_of_forall_norm_le
import Theorems.Thm_AutomorphicForm_exists_norm_rightConv_le_mul_max_ideleNorm_det_pow
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_eq_prod_norm_infinitePlace_pow_mult_of_snd_eq_one
import Theorems.Thm_AutomorphicForm_whittakerCoefficient_sum_smul_of_continuous
import Theorems.Thm_AutomorphicForm_continuous_rightConv_and_contDiff_of_isFactorizableTestFn
import Theorems.Thm_AutomorphicForm_rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply
import Theorems.Thm_AutomorphicForm_continuous_and_hasCompactSupport_of_isFactorizableTestFn
import Theorems.Thm_NumberField_StandardAddChar_stdAddChar_single_infinitePlace_of_isReal
import Theorems.Thm_NumberField_StandardAddChar_stdAddChar_apply_mk_zero_eq_fourierChar_trace
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_norm_whittakerCoefficient_rightConv_diagOne_mul_le_ideleNorm_rpow_neg_of_one_le
p2m_attr_erase "instance" "instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one"
p2m_attr_erase "simp" "LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.TateGlobal
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain

noncomputable section
open MeasureTheory Complex
open scoped Real

namespace EvalCoords

variable {X : Type*}

def vanishingOn (E : Submodule ℂ (X → ℂ)) (s : Finset X) : Submodule ℂ E where
  carrier := {e | ∀ x ∈ s, (e : X → ℂ) x = 0}
  zero_mem' := fun _ _ => rfl
  add_mem' := fun {a b} ha hb x hx => by
    simp only [Submodule.coe_add, Pi.add_apply, ha x hx, hb x hx, add_zero]
  smul_mem' := fun c {a} ha x hx => by
    simp only [Submodule.coe_smul, Pi.smul_apply, ha x hx, smul_zero]

theorem vanishingOn_mono (E : Submodule ℂ (X → ℂ)) {s t : Finset X} (h : s ⊆ t) :
    vanishingOn E t ≤ vanishingOn E s := fun _ he x hx => he x (h hx)

theorem exists_finset_separating (E : Submodule ℂ (X → ℂ)) [FiniteDimensional ℂ E] :
    ∃ s : Finset X, ∀ e ∈ E, (∀ x ∈ s, e x = 0) → e = 0 := by
  classical

  have key : ∀ k : ℕ, k ≤ Module.finrank ℂ E →
      ∃ s : Finset X, Module.finrank ℂ (vanishingOn E s) ≤ Module.finrank ℂ E - k := by
    intro k
    induction k with
    | zero =>
      intro _
      exact ⟨∅, (Submodule.finrank_le _).trans le_rfl⟩
    | succ k ih =>
      intro hk
      obtain ⟨s, hs⟩ := ih (Nat.le_of_succ_le hk)
      by_cases hbot : vanishingOn E s = ⊥
      · refine ⟨s, ?_⟩
        rw [hbot, finrank_bot]
        exact Nat.zero_le _
      · obtain ⟨e, he, hne⟩ := (Submodule.ne_bot_iff _).mp hbot
        have hne' : (e : X → ℂ) ≠ 0 := fun h => hne (Subtype.ext h)
        obtain ⟨x, hx⟩ := Function.ne_iff.mp hne'
        refine ⟨insert x s, ?_⟩
        have hlt : vanishingOn E (insert x s) < vanishingOn E s := by
          refine lt_of_le_of_ne (vanishingOn_mono E (Finset.subset_insert x s)) fun h => ?_
          have : e ∈ vanishingOn E (insert x s) := h ▸ he
          exact hx (this x (Finset.mem_insert_self x s))
        have := Submodule.finrank_lt_finrank_of_lt hlt
        omega
  obtain ⟨s, hs⟩ := key (Module.finrank ℂ E) le_rfl
  rw [Nat.sub_self, Nat.le_zero] at hs
  refine ⟨s, fun e he h0 => ?_⟩
  have hmem : (⟨e, he⟩ : E) ∈ vanishingOn E s := h0
  rw [Submodule.finrank_eq_zero.mp hs, Submodule.mem_bot] at hmem
  exact congrArg Subtype.val hmem

theorem exists_eval_coords (E : Submodule ℂ (X → ℂ)) [FiniteDimensional ℂ E] :
    ∃ (s : Finset X) (b : X → X → ℂ), (∀ x, b x ∈ E) ∧ ∀ e ∈ E, e = ∑ x ∈ s, e x • b x := by
  classical
  obtain ⟨s, hs⟩ := exists_finset_separating E

  let res : E →ₗ[ℂ] (s → ℂ) :=
    { toFun := fun e x => (e : X → ℂ) x
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hker : LinearMap.ker res = ⊥ := by
    refine (Submodule.eq_bot_iff _).mpr fun e he => ?_
    rw [LinearMap.mem_ker] at he
    apply Subtype.ext
    exact hs e e.2 fun x hx => congrFun he ⟨x, hx⟩
  obtain ⟨g, hg⟩ := res.exists_leftInverse_of_injective hker
  let b : X → X → ℂ := fun x => if hx : x ∈ s then ((g (Pi.single (⟨x, hx⟩ : s) 1) : E) : X → ℂ) else 0
  refine ⟨s, b, fun x => ?_, fun e he => ?_⟩
  · simp only [b]
    split_ifs
    · exact Submodule.coe_mem _
    · exact E.zero_mem
  · have h1 : (⟨e, he⟩ : E) = g (res ⟨e, he⟩) := (LinearMap.congr_fun hg ⟨e, he⟩).symm
    have h2 : res ⟨e, he⟩ = ∑ x : s, e x • (Pi.single x (1 : ℂ) : s → ℂ) := by
      ext y
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [Finset.sum_eq_single y]
      · simp [res]
      · intro z _ hzy; simp [Ne.symm hzy]
      · intro hy; exact absurd (Finset.mem_univ y) hy
    have h3 : e = ((g (res ⟨e, he⟩) : E) : X → ℂ) := congrArg Subtype.val h1
    conv_lhs => rw [h3, h2, map_sum]
    rw [Submodule.coe_sum, Finset.univ_eq_attach, ← Finset.sum_attach s (fun x => e x • b x)]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [map_smul, Submodule.coe_smul]
    simp only [b, dif_pos x.2]

end EvalCoords

end

noncomputable section

namespace KUNIFPlace

open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open AutomorphicForm AutomorphicForm.WindowedSiegel NumberField.AdelicLevel

variable {L : Type*} [NormedField L]

theorem diagOne_coe (t : Lˣ) :
    ((diagOne t : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) = Matrix.diagonal ![(t : L), 1] := rfl

theorem isRowIsometry_diagOne (t : Lˣ) (ht : ‖(t : L)‖ = 1) : IsRowIsometry (diagOne t) := by
  have h00 : ((diagOne t : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 0 0 = t := by simp [diagOne_coe]
  have h01 : ((diagOne t : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 0 1 = 0 := by simp [diagOne_coe]
  have h10 : ((diagOne t : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 := by simp [diagOne_coe]
  have h11 : ((diagOne t : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 1 = 1 := by simp [diagOne_coe]
  refine ⟨?_, fun x y => ?_⟩
  · rw [diagOne_coe, Matrix.det_diagonal]
    simp [ht]
  · rw [h00, h01, h10, h11, mul_zero, add_zero, mul_zero, zero_add, mul_one, norm_mul, ht, mul_one]

theorem scalar_coe (u : Lˣ) :
    ((Matrix.GeneralLinearGroup.scalar (Fin 2) u : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) =
      Matrix.diagonal fun _ => (u : L) := by
  show Matrix.scalar (Fin 2) (u : L) = _
  exact Matrix.scalar_apply _

theorem isRowIsometry_scalar (u : Lˣ) (hu : ‖(u : L)‖ = 1) :
    IsRowIsometry (Matrix.GeneralLinearGroup.scalar (Fin 2) u) := by
  have h00 : ((Matrix.GeneralLinearGroup.scalar (Fin 2) u : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 0 0 = u := by
    simp
  have h01 : ((Matrix.GeneralLinearGroup.scalar (Fin 2) u : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 0 1 = 0 := by
    simp
  have h10 : ((Matrix.GeneralLinearGroup.scalar (Fin 2) u : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 := by
    simp
  have h11 : ((Matrix.GeneralLinearGroup.scalar (Fin 2) u : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 1 = u := by
    simp
  refine ⟨?_, fun x y => ?_⟩
  · rw [scalar_coe, Matrix.det_diagonal]
    simp [hu]
  · rw [h00, h01, h10, h11, mul_zero, add_zero, mul_zero, zero_add, norm_mul, norm_mul, hu, mul_one, mul_one]

theorem det_scalar_two (u : Lˣ) :
    ((Matrix.GeneralLinearGroup.scalar (Fin 2) u : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L).det = (u : L) * u := by
  rw [scalar_coe, Matrix.det_diagonal, Fin.prod_univ_two]

theorem det_diagOne (t : Lˣ) : ((diagOne t : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L).det = t := by
  rw [diagOne_coe, Matrix.det_diagonal, Fin.prod_univ_two]
  simp

variable {K : Type*} [Field K] [NumberField K]

theorem exists_sq_eq_of_norm_eq_one (c : ℂ) (hc : ‖c‖ = 1) : ∃ ζ : ℂ, ‖ζ‖ = 1 ∧ ζ * ζ = c := by
  refine ⟨Complex.exp (((Complex.arg c / 2 : ℝ) : ℂ) * Complex.I), Complex.norm_exp_ofReal_mul_I _, ?_⟩
  rw [← Complex.exp_add]
  have : ((Complex.arg c / 2 : ℝ) : ℂ) * Complex.I + ((Complex.arg c / 2 : ℝ) : ℂ) * Complex.I = Complex.arg c * Complex.I := by
    push_cast; ring
  rw [this]
  have h := Complex.norm_mul_exp_arg_mul_I c
  rwa [hc, Complex.ofReal_one, one_mul] at h

omit [NumberField K] in
theorem norm_extensionEmbedding (w : InfinitePlace K) (x : w.Completion) : ‖extensionEmbedding w x‖ = ‖x‖ :=
  (isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) x

omit [NumberField K] in

theorem sq_eq_one_or_exists_sqrt (w : InfinitePlace K) (δ : w.Completion) (hδ : ‖δ‖ = 1) :
    δ * δ = 1 ∨ ∃ ζ : w.Completion, ‖ζ‖ = 1 ∧ ζ * ζ = δ := by
  by_cases hw : w.IsReal
  · left
    set e := ringEquivRealOfIsReal hw
    have hr : ‖e δ‖ = 1 := by
      rw [ringEquivRealOfIsReal_apply]
      rw [← hδ]
      exact (isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero (map_zero _) δ
    have hsq : e δ * e δ = 1 := by
      rcases (abs_eq (zero_le_one : (0 : ℝ) ≤ 1)).mp (by rw [← Real.norm_eq_abs]; exact hr) with h | h
      · rw [h]; norm_num
      · rw [h]; norm_num
    apply e.injective
    rw [map_mul, map_one, hsq]
  · right
    have hw' : w.IsComplex := not_isReal_iff_isComplex.mp hw
    set e := ringEquivComplexOfIsComplex hw'
    have hc : ‖e δ‖ = 1 := by rw [ringEquivComplexOfIsComplex_apply, norm_extensionEmbedding, hδ]
    obtain ⟨ζ, hζ, hζζ⟩ := exists_sq_eq_of_norm_eq_one (e δ) hc
    refine ⟨e.symm ζ, ?_, ?_⟩
    · have := norm_extensionEmbedding w (e.symm ζ)
      rw [← ringEquivComplexOfIsComplex_apply hw', RingEquiv.apply_symm_apply] at this
      rw [← this, hζ]
    · apply e.injective
      rw [map_mul, RingEquiv.apply_symm_apply, hζζ]

omit [NumberField K] in

private theorem _root_.KUNIFPlace.exists_factor (w : InfinitePlace K) (κ : GL (Fin 2) w.Completion) (hκ : IsRowIsometry κ) :
    ∃ (s ζ : (w.Completion)ˣ) (κ' : rowIsometrySubgroup₀ w.Completion),
      ‖(s : w.Completion)‖ = 1 ∧ ‖(ζ : w.Completion)‖ = 1 ∧
      κ = diagOne s * (κ' : GL (Fin 2) w.Completion) * Matrix.GeneralLinearGroup.scalar (Fin 2) ζ := by
  set δ := ((κ : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion).det with hδ
  have hδ1 : ‖δ‖ = 1 := hκ.1
  have hδ0 : δ ≠ 0 := fun h => by rw [h, norm_zero] at hδ1; exact zero_ne_one hδ1
  rcases sq_eq_one_or_exists_sqrt w δ hδ1 with hsq | ⟨ζ, hζ1, hζζ⟩
  ·
    let s : (w.Completion)ˣ := ⟨δ, δ, hsq, hsq⟩
    have hs : ‖(s : w.Completion)‖ = 1 := hδ1
    have hiso : IsRowIsometry ((diagOne s)⁻¹ * κ) := (isRowIsometry_diagOne s hs).inv.mul hκ
    have hdet : ((((diagOne s)⁻¹ * κ : GL (Fin 2) w.Completion)) : Matrix (Fin 2) (Fin 2) w.Completion).det = 1 := by
      rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.det_mul, ← map_inv, det_diagOne, ← hδ]
      show ((s⁻¹ : (w.Completion)ˣ) : w.Completion) * δ = 1
      rw [Units.val_inv_eq_inv_val]
      exact inv_mul_cancel₀ hδ0
    refine ⟨s, 1, ⟨(diagOne s)⁻¹ * κ, (mem_rowIsometrySubgroup₀_iff _).mpr ⟨hdet, hiso⟩⟩, hs, by simp, ?_⟩
    rw [map_one, mul_one]
    show κ = diagOne s * ((diagOne s)⁻¹ * κ)
    rw [mul_inv_cancel_left]
  ·
    have hζ0 : ζ ≠ 0 := fun h => by rw [h, norm_zero] at hζ1; exact zero_ne_one hζ1
    let u : (w.Completion)ˣ := Units.mk0 ζ hζ0
    have hu : ‖(u : w.Completion)‖ = 1 := hζ1
    have hiso : IsRowIsometry (κ * (Matrix.GeneralLinearGroup.scalar (Fin 2) u)⁻¹) :=
      hκ.mul (isRowIsometry_scalar u hu).inv
    have hdet : (((κ * (Matrix.GeneralLinearGroup.scalar (Fin 2) u)⁻¹ : GL (Fin 2) w.Completion)) :
        Matrix (Fin 2) (Fin 2) w.Completion).det = 1 := by
      rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.det_mul, ← map_inv, det_scalar_two, ← hδ, ← hζζ]
      show ζ * ζ * (((u⁻¹ : (w.Completion)ˣ) : w.Completion) * ((u⁻¹ : (w.Completion)ˣ) : w.Completion)) = 1
      rw [Units.val_inv_eq_inv_val]
      show ζ * ζ * (ζ⁻¹ * ζ⁻¹) = 1
      field_simp
    refine ⟨1, u, ⟨κ * (Matrix.GeneralLinearGroup.scalar (Fin 2) u)⁻¹, (mem_rowIsometrySubgroup₀_iff _).mpr ⟨hdet, hiso⟩⟩,
      by simp, hu, ?_⟩
    rw [map_one, one_mul]
    show κ = κ * (Matrix.GeneralLinearGroup.scalar (Fin 2) u)⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 2) u
    rw [inv_mul_cancel_right]

p2m_export "KUNIFPlace" "exists_factor"
end KUNIFPlace

end

noncomputable section

namespace KUNIFAdelic

open scoped Classical
open NumberField NumberField.InfinitePlace IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel NumberField.AdelicLevel

variable (K : Type) [Field K] [NumberField K]

noncomputable def archIdele (t : ∀ w : InfinitePlace K, (w.Completion)ˣ) : (AdeleRing (𝓞 K) K)ˣ where
  val := ((fun w => ((t w : (w.Completion)ˣ) : w.Completion)), 1)
  inv := ((fun w => (((t w)⁻¹ : (w.Completion)ˣ) : w.Completion)), 1)
  val_inv := by
    refine Prod.ext ?_ ?_
    · funext w
      change ((t w : (w.Completion)ˣ) : w.Completion) * (((t w)⁻¹ : (w.Completion)ˣ) : w.Completion) = 1
      exact Units.mul_inv _
    · change (1 : FiniteAdeleRing (𝓞 K) K) * 1 = 1
      exact one_mul 1
  inv_val := by
    refine Prod.ext ?_ ?_
    · funext w
      change (((t w)⁻¹ : (w.Completion)ˣ) : w.Completion) * ((t w : (w.Completion)ˣ) : w.Completion) = 1
      exact Units.inv_mul _
    · change (1 : FiniteAdeleRing (𝓞 K) K) * 1 = 1
      exact one_mul 1

theorem archIdele_fst (t : ∀ w : InfinitePlace K, (w.Completion)ˣ) (w : InfinitePlace K) :
    ((archIdele K t : (AdeleRing (𝓞 K) K))).1 w = t w := rfl

theorem archIdele_snd (t : ∀ w : InfinitePlace K, (w.Completion)ˣ) :
    ((archIdele K t : (AdeleRing (𝓞 K) K))).2 = 1 := rfl

theorem gl_ext {g h : AdelicGL2 (𝓞 K) K} (h₁ : glFin (𝓞 K) K g = glFin (𝓞 K) K h)
    (h₂ : ∀ w : InfinitePlace K, archComponent K w (glArch (𝓞 K) K g) = archComponent K w (glArch (𝓞 K) K h)) :
    g = h := by
  apply Units.ext
  refine Matrix.ext fun i j => ?_
  apply Prod.ext
  · funext w
    exact congrArg (fun m : GL (Fin 2) w.Completion => (m : Matrix (Fin 2) (Fin 2) w.Completion) i j) (h₂ w)
  · exact congrArg (fun m : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) => (m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) i j) h₁

theorem glFin_diagOne_archIdele (t : ∀ w : InfinitePlace K, (w.Completion)ˣ) :
    glFin (𝓞 K) K (diagOne (archIdele K t)) = 1 := by
  apply Units.ext
  refine Matrix.ext fun i j => ?_
  show (((diagOne (archIdele K t) : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j).2 =
    (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) i j
  rw [diagOne_coe_apply]
  fin_cases i <;> fin_cases j <;> rfl

theorem archComponent_diagOne_archIdele (t : ∀ w : InfinitePlace K, (w.Completion)ˣ) (w : InfinitePlace K) :
    archComponent K w (glArch (𝓞 K) K (diagOne (archIdele K t))) = diagOne (t w) := by
  apply Units.ext
  refine Matrix.ext fun i j => ?_
  show (((diagOne (archIdele K t) : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j).1 w =
    ((diagOne (t w) : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) i j
  rw [diagOne_coe_apply, diagOne_coe_apply]
  fin_cases i <;> fin_cases j <;> rfl

theorem glFin_centralScalar_archIdele (t : ∀ w : InfinitePlace K, (w.Completion)ˣ) :
    glFin (𝓞 K) K (centralScalar (𝓞 K) K (archIdele K t)) = 1 := by
  apply Units.ext
  refine Matrix.ext fun i j => ?_
  show ((Matrix.scalar (Fin 2) ((archIdele K t : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)) i j).2 =
    (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) i j
  rw [Matrix.scalar_apply]
  fin_cases i <;> fin_cases j <;> rfl

theorem archComponent_centralScalar_archIdele (t : ∀ w : InfinitePlace K, (w.Completion)ˣ) (w : InfinitePlace K) :
    archComponent K w (glArch (𝓞 K) K (centralScalar (𝓞 K) K (archIdele K t))) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (t w) := by
  apply Units.ext
  refine Matrix.ext fun i j => ?_
  show ((Matrix.scalar (Fin 2) ((archIdele K t : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)) i j).1 w =
    (Matrix.scalar (Fin 2) ((t w : (w.Completion)ˣ) : w.Completion)) i j
  rw [Matrix.scalar_apply, Matrix.scalar_apply]
  fin_cases i <;> fin_cases j <;> rfl

theorem glFin_adelicArchGLInclAt (w : InfinitePlace K) (k : GL (Fin 2) w.Completion) :
    glFin (𝓞 K) K (adelicArchGLInclAt K w k) = 1 :=
  glFin_adelicArchGLIncl K _

theorem archComponent_adelicArchGLInclAt_self (w : InfinitePlace K) (k : GL (Fin 2) w.Completion) :
    archComponent K w (glArch (𝓞 K) K (adelicArchGLInclAt K w k)) = k := by
  rw [adelicArchGLInclAt, MonoidHom.comp_apply, glArch_adelicArchGLIncl, archComponent_archGLIncl_self]

theorem archComponent_adelicArchGLInclAt_of_ne {v w : InfinitePlace K} (hvw : v ≠ w) (k : GL (Fin 2) w.Completion) :
    archComponent K v (glArch (𝓞 K) K (adelicArchGLInclAt K w k)) = 1 := by
  rw [adelicArchGLInclAt, MonoidHom.comp_apply, glArch_adelicArchGLIncl, archComponent_archGLIncl_of_ne K hvw]

def archProd (κ : ∀ w : InfinitePlace K, GL (Fin 2) w.Completion) : AdelicGL2 (𝓞 K) K :=
  (Finset.univ : Finset (InfinitePlace K)).noncommProd (fun w => adelicArchGLInclAt K w (κ w))
    fun _ _ _ _ hvw => commute_adelicArchGLInclAt_of_ne K hvw _ _

theorem glFin_archProd (κ : ∀ w : InfinitePlace K, GL (Fin 2) w.Completion) : glFin (𝓞 K) K (archProd K κ) = 1 := by
  rw [archProd, Finset.map_noncommProd]
  rw [Finset.noncommProd_eq_pow_card _ _ _ 1 fun w _ => ?_]
  · exact one_pow _
  · exact glFin_adelicArchGLInclAt K w (κ w)

theorem archComponent_archProd (κ : ∀ w : InfinitePlace K, GL (Fin 2) w.Completion) (w : InfinitePlace K) :
    archComponent K w (glArch (𝓞 K) K (archProd K κ)) = κ w := by
  let A : AdelicGL2 (𝓞 K) K →* GL (Fin 2) w.Completion := (archComponent K w).comp (glArch (𝓞 K) K)
  show A (archProd K κ) = κ w
  rw [archProd, Finset.map_noncommProd]
  rw [← Finset.mul_noncommProd_erase Finset.univ (Finset.mem_univ w)]
  rw [Finset.noncommProd_eq_pow_card _ _ _ 1 fun v hv => ?_]
  · rw [one_pow, mul_one]
    exact archComponent_adelicArchGLInclAt_self K w (κ w)
  · exact archComponent_adelicArchGLInclAt_of_ne K (Finset.ne_of_mem_erase hv).symm (κ v)

theorem archProd_induction (κ : ∀ w : InfinitePlace K, GL (Fin 2) w.Completion) (p : AdelicGL2 (𝓞 K) K → Prop)
    (hone : p 1) (hmul : ∀ a b, p a → p b → p (a * b)) (hbase : ∀ w, p (adelicArchGLInclAt K w (κ w))) :
    p (archProd K κ) :=
  Finset.noncommProd_induction _ _ _ p hmul hone fun w _ => hbase w

theorem adelicArchGLInclAt_mem_adelicMaximalCompact (w : InfinitePlace K) (k : GL (Fin 2) w.Completion)
    (hk : IsRowIsometry k) : adelicArchGLInclAt K w k ∈ adelicMaximalCompact K := by
  refine mem_adelicMaximalCompact_iff.mpr ⟨?_, fun v => ?_⟩
  · rw [glFin_adelicArchGLInclAt]; exact Subgroup.one_mem _
  · by_cases hvw : v = w
    · subst hvw; rw [archComponent_adelicArchGLInclAt_self]; exact hk
    · rw [archComponent_adelicArchGLInclAt_of_ne K hvw]; exact isRowIsometry_one

theorem archProd_mem_adelicMaximalCompact (κ : ∀ w : InfinitePlace K, GL (Fin 2) w.Completion)
    (hκ : ∀ w, IsRowIsometry (κ w)) : archProd K κ ∈ adelicMaximalCompact K :=
  archProd_induction K κ (fun g => g ∈ adelicMaximalCompact K) (Subgroup.one_mem _)
    (fun _ _ ha hb => Subgroup.mul_mem _ ha hb) fun w => adelicArchGLInclAt_mem_adelicMaximalCompact K w _ (hκ w)

theorem ideleNorm_archIdele_eq_one (t : ∀ w : InfinitePlace K, (w.Completion)ˣ) (ht : ∀ w, ‖((t w : (w.Completion)ˣ) : w.Completion)‖ = 1) :
    NumberField.TateGlobal.ideleNorm K (archIdele K t) = 1 := by
  rw [NumberField.TateGlobal.ideleNorm_eq_prod_norm_infinitePlace_pow_mult_of_snd_eq_one K _ (archIdele_snd K t)]
  refine Finset.prod_eq_one fun w _ => ?_
  rw [archIdele_fst, ht w, one_pow]

theorem mul_centralScalar_comm (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K) :
    g * centralScalar (𝓞 K) K z = centralScalar (𝓞 K) K z * g := by
  apply Units.ext
  show (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) * Matrix.scalar (Fin 2) (z : AdeleRing (𝓞 K) K) =
    Matrix.scalar (Fin 2) (z : AdeleRing (𝓞 K) K) * g
  exact (Matrix.scalar_commute (z : AdeleRing (𝓞 K) K) (fun _ => Commute.all _ _) _).symm.eq

private theorem _root_.KUNIFAdelic.exists_factor (k : AdelicGL2 (𝓞 K) K) (hk1 : glFin (𝓞 K) K k = 1)
    (hk2 : ∀ w : InfinitePlace K, IsRowIsometry (archComponent K w (glArch (𝓞 K) K k))) :
    ∃ (s ζ : ∀ w : InfinitePlace K, (w.Completion)ˣ) (κ' : ∀ w : InfinitePlace K, rowIsometrySubgroup₀ w.Completion),
      (∀ w, ‖((s w : (w.Completion)ˣ) : w.Completion)‖ = 1) ∧ (∀ w, ‖((ζ w : (w.Completion)ˣ) : w.Completion)‖ = 1) ∧
      k = diagOne (archIdele K s) * archProd K (fun w => (κ' w : GL (Fin 2) w.Completion)) *
        centralScalar (𝓞 K) K (archIdele K ζ) := by
  choose s ζ κ' hs hζ hfac using fun w => KUNIFPlace.exists_factor w _ (hk2 w)
  refine ⟨s, ζ, κ', hs, hζ, gl_ext K ?_ fun w => ?_⟩
  · rw [hk1, map_mul, map_mul, glFin_diagOne_archIdele, glFin_archProd, glFin_centralScalar_archIdele, one_mul, one_mul]
  · rw [map_mul, map_mul, map_mul, map_mul, archComponent_diagOne_archIdele, archComponent_archProd,
      archComponent_centralScalar_archIdele]
    exact hfac w

p2m_export "KUNIFAdelic" "exists_factor"
end KUNIFAdelic

namespace ArchLarge

set_option linter.unusedSectionVars false

open scoped Classical
open NumberField NumberField.InfinitePlace NumberField.AdelicLevel IsDedekindDomain AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.CuspidalConstituent MeasureTheory Set Filter Topology

variable (K : Type) [Field K] [NumberField K]

abbrev G := AdelicGL2 (𝓞 K) K

def Harch : Set (G K) := {h | glFin (𝓞 K) K h = 1 ∧ ∀ w : InfinitePlace K, IsRowIsometry (archComponent K w (glArch (𝓞 K) K h))}

theorem one_mem_Harch : (1 : G K) ∈ Harch K :=
  ⟨map_one _, fun w => by rw [map_one, map_one]; exact isRowIsometry_one⟩

theorem mul_mem_Harch {a b : G K} (ha : a ∈ Harch K) (hb : b ∈ Harch K) : a * b ∈ Harch K :=
  ⟨by rw [map_mul, ha.1, hb.1, one_mul], fun w => by rw [map_mul, map_mul]; exact (ha.2 w).mul (hb.2 w)⟩

theorem rowIsometryInclAt₀_mem_Harch (w : InfinitePlace K) (k : rowIsometrySubgroup₀ w.Completion) :
    rowIsometryInclAt₀ K w k ∈ Harch K := by
  rw [rowIsometryInclAt₀_apply]
  refine ⟨glFin_adelicArchGLIncl K _, fun v => ?_⟩
  rw [adelicArchGLInclAt, MonoidHom.comp_apply, glArch_adelicArchGLIncl]
  by_cases hvw : v = w
  · subst hvw
    rw [archComponent_archGLIncl_self]
    exact ((mem_rowIsometrySubgroup₀_iff _).mp k.2).2
  · rw [archComponent_archGLIncl_of_ne K hvw]
    exact isRowIsometry_one

theorem Harch_subset_adelicMaximalCompact : Harch K ⊆ (adelicMaximalCompact K : Set (G K)) := fun h hh =>
  mem_adelicMaximalCompact_iff.mpr ⟨by rw [hh.1]; exact Subgroup.one_mem _, hh.2⟩

theorem map_map_rightRegular (a b : G K) (p : Submodule ℂ (G K → ℂ)) :
    (p.map (rightRegular K a)).map (rightRegular K b) = p.map (rightRegular K (b * a)) := by
  rw [← Submodule.map_comp, map_mul, Module.End.mul_eq_comp]

def trSpan (x : G K → ℂ) : Submodule ℂ (G K → ℂ) :=
  Submodule.span ℂ ((fun h => rightTranslate K h x) '' Harch K)

theorem mem_trSpan_self (x : G K → ℂ) : x ∈ trSpan K x := by
  refine Submodule.subset_span ⟨1, one_mem_Harch K, ?_⟩
  funext y; simp [rightTranslate]

theorem map_trSpan_le (x : G K → ℂ) {a : G K} (ha : a ∈ Harch K) : (trSpan K x).map (rightRegular K a) ≤ trSpan K x := by
  rw [trSpan, Submodule.map_span, Submodule.span_le]
  rintro _ ⟨_, ⟨h, hh, rfl⟩, rfl⟩
  refine Submodule.subset_span ⟨a * h, mul_mem_Harch K ha hh, ?_⟩
  show rightTranslate K (a * h) x = rightRegular K a (rightTranslate K h x)
  rw [rightRegular_apply, rightTranslate_rightTranslate]

theorem exists_hull (C : Submodule ℂ (G K → ℂ))
    (hC_stab : ∀ (w : InfinitePlace K) (k : rowIsometrySubgroup₀ w.Completion), ∀ φ ∈ C,
      rightTranslate K (rowIsometryInclAt₀ K w k) φ ∈ C)
    (hC_fd : ∀ φ ∈ C, ∀ w : InfinitePlace K, ∃ W : Submodule ℂ (G K → ℂ), FiniteDimensional ℂ W ∧
      ∀ k : rowIsometrySubgroup₀ w.Completion, rightTranslate K (rowIsometryInclAt₀ K w k) φ ∈ W)
    {x : G K → ℂ} (hx : x ∈ C) :
    ∃ E : Submodule ℂ (G K → ℂ), FiniteDimensional ℂ E ∧ E ≤ C ∧ x ∈ E ∧ E ≤ trSpan K x ∧
      ∀ (w : InfinitePlace K) (k : rowIsometrySubgroup₀ w.Completion), ∀ φ ∈ E,
        rightTranslate K (rowIsometryInclAt₀ K w k) φ ∈ E := by
  suffices H : ∀ P : Finset (InfinitePlace K), ∃ E : Submodule ℂ (G K → ℂ),
      FiniteDimensional ℂ E ∧ E ≤ C ∧ x ∈ E ∧ E ≤ trSpan K x ∧
      ∀ w ∈ P, ∀ (k : rowIsometrySubgroup₀ w.Completion), ∀ φ ∈ E, rightTranslate K (rowIsometryInclAt₀ K w k) φ ∈ E by
    obtain ⟨E, h1, h2, h3, h4, h5⟩ := H Finset.univ
    exact ⟨E, h1, h2, h3, h4, fun w k φ hφ => h5 w (Finset.mem_univ w) k φ hφ⟩
  intro P
  induction P using Finset.induction_on with
  | empty =>
    exact ⟨ℂ ∙ x, inferInstance, (Submodule.span_singleton_le_iff_mem _ _).mpr hx, Submodule.mem_span_singleton_self x,
      (Submodule.span_singleton_le_iff_mem _ _).mpr (mem_trSpan_self K x), fun w hw => absurd hw (Finset.notMem_empty w)⟩
  | insert w P hwP ih =>
    obtain ⟨E, hEfd, hEC, hxE, hEtr, hEstab⟩ := ih
    haveI := hEfd
    let R : rowIsometrySubgroup₀ w.Completion → (G K → ℂ) →ₗ[ℂ] (G K → ℂ) :=
      fun k => rightRegular K (rowIsometryInclAt₀ K w k)
    let E' : Submodule ℂ (G K → ℂ) := ⨆ k, E.map (R k)
    have hEE' : E ≤ E' := by
      have h1 : E.map (R 1) = E := by
        simp only [R, map_one, Module.End.one_eq_id, Submodule.map_id]
      calc E = E.map (R 1) := h1.symm
        _ ≤ E' := le_iSup (fun k => E.map (R k)) 1
    obtain ⟨S, hS⟩ := (Submodule.fg_iff_finiteDimensional E).mpr hEfd
    have hSE : ∀ s ∈ S, (s : G K → ℂ) ∈ E := fun s hs => hS ▸ Submodule.subset_span hs
    choose W hWfd hW using fun s : S => hC_fd s (hEC (hSE s s.2)) w
    haveI : ∀ s : S, FiniteDimensional ℂ (W s) := hWfd
    have hE'le : E' ≤ ⨆ s : S, W s := by
      refine iSup_le fun k => ?_
      rw [← hS, Submodule.map_span, Submodule.span_le]
      rintro _ ⟨s, hs, rfl⟩
      exact Submodule.mem_iSup_of_mem ⟨s, hs⟩ (hW ⟨s, hs⟩ k)
    refine ⟨E', Submodule.finiteDimensional_of_le hE'le, ?_, hEE' hxE, ?_, ?_⟩
    · exact iSup_le fun k => Submodule.map_le_iff_le_comap.mpr fun φ hφ => hC_stab w k φ (hEC hφ)
    · exact iSup_le fun k => (Submodule.map_mono hEtr).trans (map_trSpan_le K x (rowIsometryInclAt₀_mem_Harch K w k))
    · intro v hv k φ hφ
      rcases Finset.mem_insert.mp hv with rfl | hvP
      · have hle : E'.map (R k) ≤ E' := by
          rw [Submodule.map_iSup]
          refine iSup_le fun k' => ?_
          rw [show (E.map (R k')).map (R k) = E.map (R (k * k')) by
            simp only [R, map_map_rightRegular, ← map_mul]]
          exact le_iSup (fun k => E.map (R k)) (k * k')
        exact hle (Submodule.mem_map_of_mem hφ)
      · have hvw : v ≠ w := fun h => hwP (h ▸ hvP)
        have hle : E'.map (rightRegular K (rowIsometryInclAt₀ K v k)) ≤ E' := by
          rw [Submodule.map_iSup]
          refine iSup_le fun k' => ?_
          have hcomm : rowIsometryInclAt₀ K v k * rowIsometryInclAt₀ K w k' =
              rowIsometryInclAt₀ K w k' * rowIsometryInclAt₀ K v k := by
            rw [rowIsometryInclAt₀_apply, rowIsometryInclAt₀_apply]
            exact (commute_adelicArchGLInclAt_of_ne K hvw _ _).eq
          rw [show (E.map (R k')).map (rightRegular K (rowIsometryInclAt₀ K v k)) =
              (E.map (rightRegular K (rowIsometryInclAt₀ K v k))).map (R k') by
            simp only [R, map_map_rightRegular, hcomm]]
          refine (Submodule.map_mono ?_).trans (le_iSup (fun k => E.map (R k)) k')
          exact Submodule.map_le_iff_le_comap.mpr fun ψ hψ => hEstab v hvP k ψ hψ
        exact hle (Submodule.mem_map_of_mem hφ)

section Translates

variable {K}
variable {φ f : G K → ℂ}

theorem isFactorizableTestFn_comp_mul (hf : IsFactorizableTestFn K f) {h : G K} (hh : glFin (𝓞 K) K h = 1) :
    IsFactorizableTestFn K (fun y => f (h⁻¹ * y)) := by
  obtain ⟨fa, ff, ⟨⟨Φ, hΦ, hfa⟩, hsupp⟩, hff, hfeq⟩ := hf
  set A : GL (Fin 2) (InfiniteAdeleRing K) := glArch (𝓞 K) K h⁻¹ with hA

  let e := InfiniteAdeleRing.ringEquiv_mixedSpace K
  let MLin : (Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K) →ₗ[ℝ] (Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K) :=
    { toFun := fun m i j => ∑ k, e ((A : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) i k) * m k j
      map_add' := fun m m' => by funext i j; simp [mul_add, Finset.sum_add_distrib]
      map_smul' := fun c m => by funext i j; simp }
  let ML := LinearMap.toContinuousLinearMap MLin
  have hML : ∀ z : GL (Fin 2) (InfiniteAdeleRing K), archEntries K (A * z) = ML (archEntries K z) := by
    intro z
    funext i j
    show e (((A * z : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) i j) =
      ∑ k, e ((A : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) i k) * e ((z : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) k j)
    rw [Units.val_mul, Matrix.mul_apply, map_sum]
    simp only [map_mul]
  refine ⟨fun z => fa (A * z), ff, ⟨⟨Φ ∘ ML, hΦ.comp ML.contDiff, fun z => ?_⟩, ?_⟩, hff, fun y => ?_⟩
  · show fa (A * z) = Φ (ML (archEntries K z))
    rw [hfa, hML]
  · exact hsupp.comp_homeomorph (Homeomorph.mulLeft A)
  · show f (h⁻¹ * y) = fa (A * glArch (𝓞 K) K y) * ff (glFin (𝓞 K) K y)
    rw [hfeq, map_mul, map_mul, map_inv (glFin (𝓞 K) K), hh, inv_one, one_mul]

theorem rightTranslate_rightConv (φ f : G K → ℂ) (h : G K) :
    rightTranslate K h (rightConv K φ f) = rightConv K φ (fun y => f (h⁻¹ * y)) := by
  funext g
  exact AutomorphicForm.rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply K φ f g h

theorem continuous_rightConv_of (hcont : Continuous φ) (hf : IsFactorizableTestFn K f) : Continuous (rightConv K φ f) :=
  (AutomorphicForm.continuous_rightConv_and_contDiff_of_isFactorizableTestFn K φ hcont f hf).1

theorem rightConv_centralScalar {pins : CarrierPins K} {ξ : pins.Z →* ℂˣ} (hφ : IsCuspAutomorphicFnAt K pins ξ φ)
    (z : pins.Z) (g : G K) :
    rightConv K φ f (centralScalar (𝓞 K) K (z : (AdeleRing (𝓞 K) K)ˣ) * g) = ((ξ z : ℂˣ) : ℂ) * rightConv K φ f g := by
  letI := pins.mS
  have hls := ((lsXiMemberAt_iff (𝓞 K) K pins.μ pins.Z ξ pins.D φ).mp hφ.1).1
  rw [rightConv_apply, rightConv_apply]
  letI := AdelicHaar.glBorel (Fin 2) (𝓞 K) K
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  show φ (centralScalar (𝓞 K) K (z : (AdeleRing (𝓞 K) K)ˣ) * g * y) * f y = _
  rw [mul_assoc, hls.central_transform z (g * y), mul_assoc]

theorem trSpan_props {pins : CarrierPins K} {ξ : pins.Z →* ℂˣ} (hφ : IsCuspAutomorphicFnAt K pins ξ φ)
    (hcont : Continuous φ) (hf : IsFactorizableTestFn K f) {y : G K → ℂ} (hy : y ∈ trSpan K (rightConv K φ f)) :
    Continuous y ∧ ∀ (z : pins.Z) (g : G K), y (centralScalar (𝓞 K) K (z : (AdeleRing (𝓞 K) K)ˣ) * g) = ((ξ z : ℂˣ) : ℂ) * y g := by
  refine Submodule.span_induction (p := fun y _ => Continuous y ∧
    ∀ (z : pins.Z) (g : G K), y (centralScalar (𝓞 K) K (z : (AdeleRing (𝓞 K) K)ˣ) * g) = ((ξ z : ℂˣ) : ℂ) * y g) ?_ ?_ ?_ ?_ hy
  · rintro _ ⟨h, hh, rfl⟩
    refine ⟨continuous_rightTranslate K (continuous_rightConv_of hcont hf) h, fun z g => ?_⟩
    show rightConv K φ f (centralScalar (𝓞 K) K (z : (AdeleRing (𝓞 K) K)ˣ) * g * h) = _
    rw [mul_assoc, rightConv_centralScalar hφ]
    rfl
  · exact ⟨continuous_const, fun z g => by simp⟩
  · rintro u v - - ⟨hu, hu'⟩ ⟨hv, hv'⟩
    exact ⟨hu.add hv, fun z g => by simp only [Pi.add_apply, hu', hv', mul_add]⟩
  · rintro c u - ⟨hu, hu'⟩
    exact ⟨hu.const_smul c, fun z g => by simp only [Pi.smul_apply, hu', smul_eq_mul]; ring⟩

theorem exists_repr_of_mem_trSpan (φ f : G K → ℂ) {y : G K → ℂ} (hy : y ∈ trSpan K (rightConv K φ f)) :
    ∃ (n : ℕ) (cs : Fin n → ℂ) (hs : Fin n → G K), (∀ l, hs l ∈ Harch K) ∧
      y = fun g => ∑ l, cs l * rightConv K φ (fun y' => f ((hs l)⁻¹ * y')) g := by
  obtain ⟨n, c, gens, hsum⟩ := Submodule.mem_span_set'.mp hy
  refine ⟨n, c, fun l => (gens l).2.choose, fun l => (gens l).2.choose_spec.1, ?_⟩
  funext g
  rw [← hsum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Pi.smul_apply, smul_eq_mul]
  congr 1
  have h := (gens l).2.choose_spec.2

  rw [← h]
  show rightTranslate K _ (rightConv K φ f) g = _
  rw [rightTranslate_rightConv]

end Translates

theorem exists_finiteDimensional_of_mem_archCutSubmodule (tys : ArchTypeFamily K) {φ : G K → ℂ}
    (hφ : φ ∈ archCutSubmodule K tys) (w : InfinitePlace K) :
    ∃ W : Submodule ℂ (G K → ℂ), FiniteDimensional ℂ W ∧
      ∀ k : rowIsometrySubgroup₀ w.Completion, rightTranslate K (rowIsometryInclAt₀ K w k) φ ∈ W := by
  have hw := (mem_archCutSubmodule_iff K tys φ).mp hφ w
  refine Submodule.iSup_induction _
    (motive := fun φ => ∃ W : Submodule ℂ (G K → ℂ), FiniteDimensional ℂ W ∧
      ∀ k : rowIsometrySubgroup₀ w.Completion, rightTranslate K (rowIsometryInclAt₀ K w k) φ ∈ W) hw ?_ ?_ ?_
  · intro i φ hφi
    refine Submodule.span_induction (p := fun φ _ => ∃ W : Submodule ℂ (G K → ℂ),
      FiniteDimensional ℂ W ∧ ∀ k : rowIsometrySubgroup₀ w.Completion,
        rightTranslate K (rowIsometryInclAt₀ K w k) φ ∈ W) ?_ ?_ ?_ ?_ hφi
    · rintro _ ⟨T, hT, v, rfl⟩
      refine ⟨LinearMap.range T, inferInstance, fun k => ?_⟩
      have : rightTranslate K (rowIsometryInclAt₀ K w k) (T v) = T ((tys.rep w i).ρ k v) := by
        funext x; exact (hT k v x).symm
      rw [this]; exact LinearMap.mem_range_self T _
    · exact ⟨⊥, inferInstance, fun k => by rw [rightTranslate_zero]; exact Submodule.zero_mem _⟩
    · rintro φ ψ - - ⟨W₁, hW₁, h₁⟩ ⟨W₂, hW₂, h₂⟩
      haveI := hW₁; haveI := hW₂
      exact ⟨W₁ ⊔ W₂, inferInstance, fun k => by
        rw [rightTranslate_add]; exact Submodule.add_mem_sup (h₁ k) (h₂ k)⟩
    · rintro c φ - ⟨W, hW, h⟩
      exact ⟨W, hW, fun k => by rw [rightTranslate_smul]; exact W.smul_mem c (h k)⟩
  · exact ⟨⊥, inferInstance, fun k => by rw [rightTranslate_zero]; exact Submodule.zero_mem _⟩
  · rintro φ ψ ⟨W₁, hW₁, h₁⟩ ⟨W₂, hW₂, h₂⟩
    haveI := hW₁; haveI := hW₂
    exact ⟨W₁ ⊔ W₂, inferInstance, fun k => by
      rw [rightTranslate_add]; exact Submodule.add_mem_sup (h₁ k) (h₂ k)⟩

theorem exists_bound {x : G K → ℂ} (hx : Continuous x) (g : G K) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ k ∈ adelicMaximalCompact K, ‖x (g * k)‖ ≤ B := by
  obtain ⟨B, hB⟩ := (isCompact_adelicMaximalCompact K).exists_bound_of_continuousOn
    (f := fun k => x (g * k)) ((hx.comp (continuous_const.mul continuous_id)).continuousOn)
  exact ⟨max B 0, le_max_right _ _, fun k hk => (hB k hk).trans (le_max_left _ _)⟩

theorem whittakerCoefficient_mul (pins : CarrierPins K) (ψ : AddChar (AdeleRing (𝓞 K) K) ℂ)
    (φ : G K → ℂ) (α : K) (g k : G K) :
    whittakerCoefficient K pins ψ φ α (g * k) = whittakerCoefficient K pins ψ (rightTranslate K k φ) α g := by
  simp only [whittakerCoefficient, rightTranslate, mul_assoc]

theorem kred (D : Set (G K)) (U : Ideal (𝓞 K) → Subgroup (G K)) (gen : HeightOneSpectrum (𝓞 K) → G K)
    (χ : (productionPinsOf K D U gen (adelicBox K)).Z →* ℂˣ)
    {φ f : G K → ℂ} (hφ : IsCuspAutomorphicFnAt K (productionPinsOf K D U gen (adelicBox K)) χ φ)
    (hcont : Continuous φ) (hf : IsFactorizableTestFn K f)
    (tys : ArchTypeFamily K) (hxt : rightConv K φ f ∈ archCutSubmodule K tys)
    (w₀ : ℝ) (hχ : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      ‖((χ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm K z ^ w₀) :
    ∃ (n : ℕ) (hs : Fin n → G K) (_ : ∀ l, glFin (𝓞 K) K (hs l) = 1) (Bc : ℝ),
      ∀ k ∈ Harch K, ∃ (cs : Fin n → ℂ) (ε : (AdeleRing (𝓞 K) K)ˣ),
        ((ε : AdeleRing (𝓞 K) K)).2 = 1 ∧ NumberField.TateGlobal.ideleNorm K ε = 1 ∧
        (∀ w : InfinitePlace K, ‖((ε : AdeleRing (𝓞 K) K)).1 w‖ = 1) ∧ (∀ l, ‖cs l‖ ≤ Bc) ∧
        ∀ g : G K,
          whittakerCoefficient K (productionPinsOf K D U gen (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K)
              (rightConv K φ f) 1 (g * k) =
            ∑ l, cs l * whittakerCoefficient K (productionPinsOf K D U gen (adelicBox K))
              (NumberField.StandardAddChar.stdAddChar K) (rightConv K φ (fun y => f ((hs l)⁻¹ * y))) 1 (g * diagOne ε) := by
  set x := rightConv K φ f with hxdef
  set C : Submodule ℂ (G K → ℂ) := archCutSubmodule K tys with hC
  have hC_stab : ∀ (w : InfinitePlace K) (k : rowIsometrySubgroup₀ w.Completion), ∀ φ' ∈ C,
      rightTranslate K (rowIsometryInclAt₀ K w k) φ' ∈ C := fun w k φ' hφ' =>
    rightTranslate_rowIsometryInclAt₀_mem_archCutSubmodule K tys hφ' w k
  have hC_fd := fun φ' (hφ' : φ' ∈ C) w => exists_finiteDimensional_of_mem_archCutSubmodule K tys hφ' w
  obtain ⟨E, hEfd, hEC, hxE, hEtr, hEstab⟩ := exists_hull K C hC_stab hC_fd hxt
  haveI := hEfd
  obtain ⟨S, b, hb, hcoord⟩ := EvalCoords.exists_eval_coords E

  have hrep : ∀ g' : G K, ∃ (n : ℕ) (cs : Fin n → ℂ) (hs : Fin n → G K), (∀ l, hs l ∈ Harch K) ∧
      b g' = fun g => ∑ l, cs l * rightConv K φ (fun y' => f ((hs l)⁻¹ * y')) g := fun g' =>
    exists_repr_of_mem_trSpan φ f (hEtr (hb g'))
  choose nrep crep hrepH hrepmem hrepeq using hrep

  let N : ℕ := Fintype.card (Σ g' : S, Fin (nrep g'))
  let eι : (Σ g' : S, Fin (nrep g')) ≃ Fin N := Fintype.equivFin _
  let pt : Fin N → G K := fun i => ((eι.symm i).1 : G K)
  let hsF : Fin N → G K := fun i => hrepH (pt i) (eι.symm i).2
  let dF : Fin N → ℂ := fun i => crep (pt i) (eι.symm i).2

  have hxcont : Continuous x := continuous_rightConv_of hcont hf
  choose B hB0 hB using fun g : G K => exists_bound K hxcont g
  refine ⟨N, hsF, fun i => (hrepmem _ _).1, ∑ i, B (pt i) * ‖dF i‖, fun k hk => ?_⟩

  obtain ⟨s, ζ, κ', hs, hζ, hfac⟩ := KUNIFAdelic.exists_factor K k hk.1 hk.2
  set ε := KUNIFAdelic.archIdele K s with hε
  set z := KUNIFAdelic.archIdele K ζ with hz
  set k₁ := KUNIFAdelic.archProd K (fun w => (κ' w : GL (Fin 2) w.Completion)) with hk₁
  have hk₁K : k₁ ∈ adelicMaximalCompact K :=
    KUNIFAdelic.archProd_mem_adelicMaximalCompact K _ fun w => ((mem_rowIsometrySubgroup₀_iff _).mp (κ' w).2).2
  have hk₁E : ∀ φ' ∈ E, rightTranslate K k₁ φ' ∈ E := by
    refine KUNIFAdelic.archProd_induction K _ (fun h => ∀ φ' ∈ E, rightTranslate K h φ' ∈ E) ?_ ?_ ?_
    · intro φ' hφ'
      have : rightTranslate K 1 φ' = φ' := by funext y; simp [rightTranslate]
      rw [this]; exact hφ'
    · intro a a' ha ha' φ' hφ'
      rw [← rightTranslate_rightTranslate]
      exact ha _ (ha' φ' hφ')
    · intro w φ' hφ'
      exact hEstab w (κ' w) φ' hφ'

  have hξz : ‖((χ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = 1 := by
    rw [hχ, KUNIFAdelic.ideleNorm_archIdele_eq_one K ζ hζ, Real.one_rpow]
  let cs : Fin N → ℂ := fun i => ((χ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * x (pt i * k₁) * dF i
  refine ⟨cs, ε, KUNIFAdelic.archIdele_snd K s, KUNIFAdelic.ideleNorm_archIdele_eq_one K s hs, fun w => ?_, fun i => ?_,
    fun g => ?_⟩
  · rw [KUNIFAdelic.archIdele_fst]; exact hs w
  · calc ‖cs i‖ = ‖x (pt i * k₁)‖ * ‖dF i‖ := by
          show ‖((χ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * x (pt i * k₁) * dF i‖ = _
          rw [norm_mul, norm_mul, hξz, one_mul]
      _ ≤ B (pt i) * ‖dF i‖ := mul_le_mul_of_nonneg_right (hB _ k₁ hk₁K) (norm_nonneg _)
      _ ≤ ∑ j, B (pt j) * ‖dF j‖ :=
          Finset.single_le_sum (fun j _ => mul_nonneg (hB0 _) (norm_nonneg _)) (Finset.mem_univ i)
  ·
    have hcentral : ∀ y, x (centralScalar (𝓞 K) K z * y) = ((χ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * x y :=
      fun y => (trSpan_props hφ hcont hf (mem_trSpan_self K x)).2 ⟨z, Subgroup.mem_top z⟩ y
    have hpt : ∀ y, x (y * k) = ∑ i, cs i * rightConv K φ (fun y' => f ((hsF i)⁻¹ * y')) (y * diagOne ε) := by
      intro y
      have e1 : x (y * k) = ((χ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * x (y * diagOne ε * k₁) := by
        rw [hfac, ← mul_assoc, ← mul_assoc, KUNIFAdelic.mul_centralScalar_comm, hcentral]
      have e2 : x (y * diagOne ε * k₁) = ∑ g' ∈ S, x (g' * k₁) * b g' (y * diagOne ε) := by
        have h := congrFun (hcoord _ (hk₁E x hxE)) (y * diagOne ε)
        simpa only [rightTranslate, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using h
      have e3 : ∀ g' : S, b g' (y * diagOne ε) =
          ∑ l : Fin (nrep g'), crep g' l * rightConv K φ (fun y' => f ((hrepH g' l)⁻¹ * y')) (y * diagOne ε) := by
        intro g'
        have := congrFun (hrepeq g') (y * diagOne ε)
        exact this
      rw [e1, e2, Finset.mul_sum, ← Finset.sum_coe_sort S]
      simp_rw [e3, Finset.mul_sum]
      rw [← Equiv.sum_comp eι, Fintype.sum_sigma]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun l _ => ?_
      have hsa : eι.symm (eι ⟨a, l⟩) = ⟨a, l⟩ := Equiv.symm_apply_apply _ _
      simp only [cs, pt, hsF, dF]
      rw [hsa]
      ring
    have hfun : rightTranslate K k x = fun y => ∑ i, cs i *
        rightTranslate K (diagOne ε) (rightConv K φ (fun y' => f ((hsF i)⁻¹ * y'))) y := by
      funext y; exact hpt y
    have hcont_i : ∀ i, Continuous (rightTranslate K (diagOne ε) (rightConv K φ (fun y' => f ((hsF i)⁻¹ * y')))) :=
      fun i => continuous_rightTranslate K (continuous_rightConv_of hcont (isFactorizableTestFn_comp_mul hf (hrepmem _ _).1)) _
    have hψ : Continuous (NumberField.StandardAddChar.stdAddChar K) :=
      (NumberField.StandardAddChar.adelicTraceData K).continuous_psiK
    rw [whittakerCoefficient_mul, show rightTranslate K k (rightConv K φ f) = rightTranslate K k x from rfl, hfun,
      AutomorphicForm.whittakerCoefficient_sum_smul_of_continuous K D U gen (NumberField.StandardAddChar.stdAddChar K) hψ N
        _ hcont_i cs 1 g]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [whittakerCoefficient_mul]

theorem det_unipotentGL2 {R : Type*} [CommRing R] (u : R) :
    Matrix.GeneralLinearGroup.det (unipotentGL2 u) = 1 := by
  apply Units.ext
  show ((unipotentGL2 u : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R).det = 1
  rw [unipotentGL2_coe, Matrix.det_fin_two_of]
  ring

theorem det_diagOne' {R : Type*} [CommRing R] (a : Rˣ) : Matrix.GeneralLinearGroup.det (diagOne a) = a := by
  apply Units.ext
  show (Matrix.diagonal ![(a : R), 1]).det = a
  rw [Matrix.det_diagonal, Fin.prod_univ_two]
  simp

theorem det_centralScalar (z : (AdeleRing (𝓞 K) K)ˣ) :
    Matrix.GeneralLinearGroup.det (centralScalar (𝓞 K) K z) = z * z := by
  apply Units.ext
  show (Matrix.scalar (Fin 2) (z : AdeleRing (𝓞 K) K)).det = z * z
  rw [Matrix.scalar_apply, Matrix.det_diagonal, Fin.prod_univ_two]

theorem unipotentGL2_algebraMap (β : K) :
    unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β) = globalPoints (𝓞 K) K (unipotentGL2 β) := by
  apply Units.ext
  refine Matrix.ext fun i j => ?_
  show (!![(1 : AdeleRing (𝓞 K) K), algebraMap K (AdeleRing (𝓞 K) K) β; 0, 1] : Matrix (Fin 2) (Fin 2) _) i j =
    algebraMap K (AdeleRing (𝓞 K) K) ((!![(1 : K), β; 0, 1] : Matrix (Fin 2) (Fin 2) K) i j)
  fin_cases i <;> fin_cases j <;> simp

section Pins

variable {K}
variable {pins : CarrierPins K} {ξ : pins.Z →* ℂˣ} {φ : G K → ℂ}

theorem rightConv_globalUnipotent_mul (hφ : IsCuspAutomorphicFnAt K pins ξ φ) (f' : G K → ℂ) (β : K) (h : G K) :
    rightConv K φ f' (unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β) * h) = rightConv K φ f' h := by
  letI := pins.mS
  have hls := ((lsXiMemberAt_iff (𝓞 K) K pins.μ pins.Z ξ pins.D φ).mp hφ.1).1
  rw [rightConv_apply, rightConv_apply]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  show φ (unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β) * h * y) * f' y = φ (h * y) * f' y
  rw [unipotentGL2_algebraMap, mul_assoc, hls.left_invariant]

end Pins

theorem rightConv_lincomb {φ : G K → ℂ} (hcont : Continuous φ) {g₁ g₂ : G K → ℂ}
    (h₁ : Continuous g₁) (h₁s : HasCompactSupport g₁) (h₂ : Continuous g₂) (h₂s : HasCompactSupport g₂) (a b : ℂ) (g : G K) :
    rightConv K φ (fun y => a * g₁ y + b * g₂ y) g = a * rightConv K φ g₁ g + b * rightConv K φ g₂ g := by
  letI := AdelicHaar.glBorel (Fin 2) (𝓞 K) K
  haveI := AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 K) K
  haveI := AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K
  rw [rightConv_apply, rightConv_apply, rightConv_apply, ← integral_const_mul, ← integral_const_mul]
  have hint : ∀ {g' : G K → ℂ}, Continuous g' → HasCompactSupport g' →
      Integrable (fun y => φ (g * y) * g' y) (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K) := fun hc hs =>
    ((hcont.comp (continuous_const.mul continuous_id)).mul hc).integrable_of_hasCompactSupport hs.mul_left
  rw [← integral_add ((hint h₁ h₁s).const_mul a) ((hint h₂ h₂s).const_mul b)]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  show φ (g * y) * (a * g₁ y + b * g₂ y) = a * (φ (g * y) * g₁ y) + b * (φ (g * y) * g₂ y)
  ring

theorem exists_archIdele_norm_eq (r : ℝ) (hr : 0 < r) :
    ∃ t : ∀ w : InfinitePlace K, (w.Completion)ˣ, ∀ w, ‖((t w : (w.Completion)ˣ) : w.Completion)‖ = r := by
  have key : ∀ w : InfinitePlace K, ∃ u : (w.Completion)ˣ, ‖(u : w.Completion)‖ = r := by
    intro w
    by_cases hw : w.IsReal
    · let e := InfinitePlace.Completion.isometryEquivRealOfIsReal hw
      have hnorm : ‖e.symm r‖ = r := by
        have h1 : ‖e.symm r‖ = dist (e.symm r) (e.symm 0) := by
          rw [show e.symm 0 = 0 from map_zero (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm, dist_zero_right]
        rw [h1, e.symm.dist_eq, Real.dist_eq, sub_zero, abs_of_pos hr]
      have hne : e.symm r ≠ 0 := fun h => by rw [h, norm_zero] at hnorm; exact hr.ne' hnorm.symm
      exact ⟨Units.mk0 _ hne, hnorm⟩
    · have hw' : w.IsComplex := InfinitePlace.not_isReal_iff_isComplex.mp hw
      let e := InfinitePlace.Completion.isometryEquivComplexOfIsComplex hw'
      have hnorm : ‖e.symm (r : ℂ)‖ = r := by
        have h1 : ‖e.symm (r : ℂ)‖ = dist (e.symm r) (e.symm 0) := by
          rw [show e.symm 0 = 0 from map_zero (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw').symm, dist_zero_right]
        rw [h1, e.symm.dist_eq, dist_zero_right, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
      have hne : e.symm (r : ℂ) ≠ 0 := fun h => by rw [h, norm_zero] at hnorm; exact hr.ne' hnorm.symm
      exact ⟨Units.mk0 _ hne, hnorm⟩
  choose t ht using key
  exact ⟨t, ht⟩

theorem ubnd (c u d₁ d₂ : ℝ) (T : Finset (G K)) (hd : d₁ < d₂)
    (hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂))
    (χ : (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)).Z →* ℂˣ)
    {φ : G K → ℂ}
    (hφ : IsCuspAutomorphicFnAt K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) χ φ)
    (hcont : Continuous φ) {f' : G K → ℂ} (hf' : IsFactorizableTestFn K f')
    (w₀ : ℝ) (hχ : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      ‖((χ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm K z ^ w₀) :
    ∃ C' : ℝ, 0 ≤ C' ∧ ∀ g : G K,
      ‖rightConv K φ f' g‖ ≤ C' * NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ^ (w₀ / 2) := by
  obtain ⟨C, M, hCM⟩ := AutomorphicForm.exists_norm_rightConv_le_mul_max_ideleNorm_det_pow K c u d₁ d₂ T hd hcov χ φ hφ
    hcont f' hf'
  refine ⟨max C 0, le_max_right _ _, fun g => ?_⟩
  set Nd : ℝ := NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) with hNd
  have hNpos : 0 < Nd := NumberField.TateGlobal.ideleNorm_pos _
  set dK : ℕ := Module.finrank ℚ K with hdK
  have hdpos : 0 < (dK : ℝ) := by exact_mod_cast Module.finrank_pos

  set r : ℝ := Nd ^ (-(1 / (2 * (dK : ℝ)))) with hr
  have hrpos : 0 < r := Real.rpow_pos_of_pos hNpos _
  obtain ⟨t, ht⟩ := exists_archIdele_norm_eq K r hrpos
  set z := KUNIFAdelic.archIdele K t with hz
  have hznorm : NumberField.TateGlobal.ideleNorm K z = r ^ dK := by
    rw [NumberField.TateGlobal.ideleNorm_eq_prod_norm_infinitePlace_pow_mult_of_snd_eq_one K _ (KUNIFAdelic.archIdele_snd K t)]
    simp_rw [KUNIFAdelic.archIdele_fst, ht]
    rw [Finset.prod_pow_eq_pow_sum, InfinitePlace.sum_mult_eq]
  have hzsq : NumberField.TateGlobal.ideleNorm K z ^ 2 * Nd = 1 := by
    rw [hznorm, ← pow_mul, hr, ← Real.rpow_natCast, ← Real.rpow_mul hNpos.le]
    have : -(1 / (2 * (dK : ℝ))) * ((dK * 2 : ℕ) : ℝ) = -1 := by
      push_cast; field_simp
    rw [this, Real.rpow_neg_one, inv_mul_cancel₀ hNpos.ne']

  have hhom : rightConv K φ f' (centralScalar (𝓞 K) K z * g) = ((χ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * rightConv K φ f' g :=
    rightConv_centralScalar hφ ⟨z, Subgroup.mem_top z⟩ g
  have hχz : ‖((χ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = r ^ ((dK : ℝ) * w₀) := by
    rw [hχ, hznorm, ← Real.rpow_natCast, ← Real.rpow_mul hrpos.le]

  have hdet1 : NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 K) K z * g)) = 1 := by
    rw [map_mul, det_centralScalar, NumberField.TateGlobal.ideleNorm_mul, NumberField.TateGlobal.ideleNorm_mul, ← hzsq, hNd]
    ring
  have hzg := hCM (centralScalar (𝓞 K) K z * g)
  rw [hdet1, inv_one, max_self, one_pow, mul_one, hhom, norm_mul, hχz] at hzg

  have hχpos : 0 < r ^ ((dK : ℝ) * w₀) := Real.rpow_pos_of_pos hrpos _
  have h1 : ‖rightConv K φ f' g‖ ≤ C * (r ^ ((dK : ℝ) * w₀))⁻¹ := by
    rw [le_mul_inv_iff₀ hχpos, mul_comm]; exact hzg
  have h2 : (r ^ ((dK : ℝ) * w₀))⁻¹ = Nd ^ (w₀ / 2) := by
    rw [hr, ← Real.rpow_mul hNpos.le, ← Real.rpow_neg hNpos.le]
    congr 1
    field_simp
  rw [h2] at h1
  exact h1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hNpos.le _))

abbrev MS := mixedEmbedding.mixedSpace K
abbrev eA := InfiniteAdeleRing.ringEquiv_mixedSpace K

def vR (w : {w : InfinitePlace K // w.IsReal}) : MS K := (Pi.single w 1, 0)

def vC (w : {w : InfinitePlace K // w.IsComplex}) : MS K := (0, Pi.single w 1)
def vCI (w : {w : InfinitePlace K // w.IsComplex}) : MS K := (0, Pi.single w Complex.I)

theorem smul_vR (w : {w : InfinitePlace K // w.IsReal}) (c : ℝ) : c • vR K w = (Pi.single w c, 0) := by
  refine Prod.ext ?_ ?_
  · show c • (Pi.single w (1 : ℝ) : {w : InfinitePlace K // w.IsReal} → ℝ) = Pi.single w c
    rw [← Pi.single_smul, smul_eq_mul, mul_one]
  · show c • (0 : {w : InfinitePlace K // w.IsComplex} → ℂ) = 0; rw [smul_zero]

theorem mul_vR (ρ : MS K) (w : {w : InfinitePlace K // w.IsReal}) : ρ * vR K w = (ρ.1 w) • vR K w := by
  rw [smul_vR]
  refine Prod.ext ?_ ?_
  · show ρ.1 * Pi.single w (1 : ℝ) = Pi.single w (ρ.1 w)
    funext v
    rw [Pi.mul_apply]
    by_cases hv : v = w
    · subst hv; simp
    · simp [Pi.single_eq_of_ne hv]
  · show ρ.2 * 0 = 0; rw [mul_zero]

theorem mul_vC (ρ : MS K) (w : {w : InfinitePlace K // w.IsComplex}) :
    ρ * vC K w = (ρ.2 w).re • vC K w + (ρ.2 w).im • vCI K w := by
  have h2 : ρ.2 * (Pi.single w (1 : ℂ) : {w : InfinitePlace K // w.IsComplex} → ℂ) =
      (ρ.2 w).re • (Pi.single w (1 : ℂ) : {w : InfinitePlace K // w.IsComplex} → ℂ) +
        (ρ.2 w).im • (Pi.single w Complex.I : {w : InfinitePlace K // w.IsComplex} → ℂ) := by
    funext v
    simp only [Pi.mul_apply, Pi.add_apply, Pi.smul_apply, Complex.real_smul]
    by_cases hv : v = w
    · subst hv
      simp only [Pi.single_eq_same, mul_one]
      conv_lhs => rw [← Complex.re_add_im (ρ.2 v)]
    · simp [Pi.single_eq_of_ne hv]
  refine Prod.ext ?_ ?_
  · show ρ.1 * 0 = (ρ.2 w).re • (0 : {w : InfinitePlace K // w.IsReal} → ℝ) + (ρ.2 w).im • (0 : {w : InfinitePlace K // w.IsReal} → ℝ)
    rw [mul_zero, smul_zero, smul_zero, add_zero]
  · exact h2

theorem unipotentGL2_mul_diagOne {R : Type*} [CommRing R] (X : R) (a : Rˣ) :
    unipotentGL2 X * diagOne a = diagOne a * unipotentGL2 (((a⁻¹ : Rˣ) : R) * X) := by
  apply Units.ext
  show !![(1 : R), X; 0, 1] * Matrix.diagonal ![(a : R), 1] = Matrix.diagonal ![(a : R), 1] * !![(1 : R), ((a⁻¹ : Rˣ) : R) * X; 0, 1]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, ← mul_assoc, Units.mul_inv]

theorem unipotentGL2_comm {R : Type*} [CommRing R] (X Y : R) :
    unipotentGL2 X * unipotentGL2 Y = unipotentGL2 Y * unipotentGL2 X := by
  rw [← unipotentGL2_add, ← unipotentGL2_add, add_comm]

def ρA (a : (AdeleRing (𝓞 K) K)ˣ) : MS K := eA K (((a⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).1

theorem inv_mul_arch (a : (AdeleRing (𝓞 K) K)ˣ) (s : MS K) :
    ((a⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K) * (show AdeleRing (𝓞 K) K from ((eA K).symm s, 0)) =
      (show AdeleRing (𝓞 K) K from ((eA K).symm (ρA K a * s), 0)) := by
  refine Prod.ext ?_ ?_
  · show (((a⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).1 * (eA K).symm s = (eA K).symm (ρA K a * s)
    rw [ρA, map_mul, RingEquiv.symm_apply_apply]
  · show (((a⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).2 * 0 = 0; rw [mul_zero]

theorem orbit_identity (a : (AdeleRing (𝓞 K) K)ˣ) (u : AdeleRing (𝓞 K) K) (v : MS K) (t : ℝ) :
    unipotentGL2 (R := AdeleRing (𝓞 K) K) ((eA K).symm (t • v), 0) * (unipotentGL2 u * diagOne a) =
      unipotentGL2 u * diagOne a * unipotentGL2 (R := AdeleRing (𝓞 K) K) ((eA K).symm (t • (ρA K a * v)), 0) := by
  rw [← mul_assoc, unipotentGL2_comm, mul_assoc, unipotentGL2_mul_diagOne, inv_mul_arch, mul_smul_comm, ← mul_assoc]

theorem norm_inv_arch_mul (a : (AdeleRing (𝓞 K) K)ˣ) (w : InfinitePlace K) :
    ‖(((a⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).1 w‖ * ‖((a : AdeleRing (𝓞 K) K)).1 w‖ = 1 := by
  have h : (((a⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).1 w * ((a : AdeleRing (𝓞 K) K)).1 w = 1 := by
    have := congrArg (fun x : AdeleRing (𝓞 K) K => x.1 w) a.inv_mul
    exact this
  rw [← norm_mul, h, norm_one]

theorem ρA_fst (a : (AdeleRing (𝓞 K) K)ˣ) (w : {w : InfinitePlace K // w.IsReal}) :
    |(ρA K a).1 w| = ‖(((a⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).1 w.1‖ := by
  show |InfinitePlace.Completion.extensionEmbeddingOfIsReal w.2 ((((a⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).1 w.1)| = _
  rw [← Real.norm_eq_abs]
  exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal w.2).norm_map_of_map_zero (map_zero _) _

theorem ρA_snd (a : (AdeleRing (𝓞 K) K)ˣ) (w : {w : InfinitePlace K // w.IsComplex}) :
    ‖(ρA K a).2 w‖ = ‖(((a⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).1 w.1‖ := by
  show ‖InfinitePlace.Completion.extensionEmbedding w.1 ((((a⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).1 w.1)‖ = _
  exact (InfinitePlace.Completion.isometry_extensionEmbedding w.1).norm_map_of_map_zero (map_zero _) _

theorem eA_symm_apply_of_isReal (z : MS K) {w : InfinitePlace K} (hw : w.IsReal) :
    (eA K).symm z w = (InfinitePlace.Completion.isometryEquivRealOfIsReal hw).symm (z.1 ⟨w, hw⟩) := by
  have hy : eA K ((eA K).symm z) = z := RingEquiv.apply_symm_apply _ _
  have h1 : InfinitePlace.Completion.extensionEmbeddingOfIsReal hw ((eA K).symm z w) = z.1 ⟨w, hw⟩ := by
    have := congrArg (fun p : MS K => p.1 ⟨w, hw⟩) hy
    simpa [InfiniteAdeleRing.ringEquiv_mixedSpace_apply] using this
  apply (InfinitePlace.Completion.isometryEquivRealOfIsReal hw).injective
  rw [IsometryEquiv.apply_symm_apply]
  exact h1

theorem eA_symm_apply_of_isComplex (z : MS K) {w : InfinitePlace K} (hw : w.IsComplex) :
    (eA K).symm z w = (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hw).symm (z.2 ⟨w, hw⟩) := by
  have hy : eA K ((eA K).symm z) = z := RingEquiv.apply_symm_apply _ _
  have h1 : InfinitePlace.Completion.extensionEmbedding w ((eA K).symm z w) = z.2 ⟨w, hw⟩ := by
    have := congrArg (fun p : MS K => p.2 ⟨w, hw⟩) hy
    simpa [InfiniteAdeleRing.ringEquiv_mixedSpace_apply] using this
  apply (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hw).injective
  rw [IsometryEquiv.apply_symm_apply]
  exact h1

theorem eA_symm_smul_vR (w : {w : InfinitePlace K // w.IsReal}) (t : ℝ) :
    (eA K).symm (t • vR K w) = Pi.single w.1 ((InfinitePlace.Completion.ringEquivRealOfIsReal w.2).symm t) := by
  rw [smul_vR]
  funext v
  by_cases hv : v.IsReal
  · rw [eA_symm_apply_of_isReal K _ hv]
    by_cases hvw : v = w.1
    · subst hvw
      show (InfinitePlace.Completion.isometryEquivRealOfIsReal hv).symm
        ((Pi.single w t : {w : InfinitePlace K // w.IsReal} → ℝ) ⟨w.1, hv⟩) = _
      rw [show (⟨w.1, hv⟩ : {w : InfinitePlace K // w.IsReal}) = w from rfl, Pi.single_eq_same, Pi.single_eq_same]
      rfl
    · show (InfinitePlace.Completion.isometryEquivRealOfIsReal hv).symm
        ((Pi.single w t : {w : InfinitePlace K // w.IsReal} → ℝ) ⟨v, hv⟩) = _
      rw [Pi.single_eq_of_ne (fun h => hvw (congrArg Subtype.val h)), Pi.single_eq_of_ne hvw]
      exact map_zero (InfinitePlace.Completion.ringEquivRealOfIsReal hv).symm
  · have hv' : v.IsComplex := InfinitePlace.not_isReal_iff_isComplex.mp hv
    rw [eA_symm_apply_of_isComplex K _ hv']
    have hvw : v ≠ w.1 := fun h => hv (h ▸ w.2)
    show (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hv').symm ((0 : {w : InfinitePlace K // w.IsComplex} → ℂ) ⟨v, hv'⟩) = _
    rw [Pi.zero_apply, Pi.single_eq_of_ne hvw]
    exact map_zero (InfinitePlace.Completion.ringEquivComplexOfIsComplex hv').symm

theorem hv_real (w : {w : InfinitePlace K // w.IsReal}) :
    ∃ t : ℝ, NumberField.StandardAddChar.stdAddChar K ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (t • vR K w), 0) ≠ 1 := by
  refine ⟨1 / 2, ?_⟩
  rw [show (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm ((1 / 2 : ℝ) • vR K w) = _ from eA_symm_smul_vR K w (1 / 2)]
  rw [NumberField.StandardAddChar.stdAddChar_single_infinitePlace_of_isReal K w.1 w.2 (1 / 2)]
  rw [show (2 * Real.pi * Complex.I * (1 / 2 : ℝ) : ℂ) = Real.pi * Complex.I by push_cast; ring, Complex.exp_pi_mul_I]
  norm_num

theorem trace_vC (w : {w : InfinitePlace K // w.IsComplex}) : Algebra.trace ℝ (MS K) (vC K w) = 2 := by
  rw [vC, Algebra.trace_prod_apply, map_zero, zero_add, Algebra.trace_apply]

  set P : ({w : InfinitePlace K // w.IsComplex} → ℂ) →ₗ[ℝ] ({w : InfinitePlace K // w.IsComplex} → ℂ) :=
    Algebra.lmul ℝ _ (Pi.single w (1 : ℂ)) with hP
  have hPapply : ∀ y, P y = Pi.single w (y w) := by
    intro y
    show Pi.single w (1 : ℂ) * y = Pi.single w (y w)
    funext v
    rw [Pi.mul_apply]
    by_cases hv : v = w
    · subst hv; simp
    · simp [Pi.single_eq_of_ne hv]
  let p : Submodule ℝ ({w : InfinitePlace K // w.IsComplex} → ℂ) := LinearMap.range (LinearMap.single ℝ (fun _ => ℂ) w)
  have hproj : LinearMap.IsProj p P := by
    refine ⟨fun y => ⟨y w, ?_⟩, fun y hy => ?_⟩
    · rw [hPapply]; rfl
    · obtain ⟨c, rfl⟩ := hy
      rw [hPapply]
      show (Pi.single w ((Pi.single w c : {w : InfinitePlace K // w.IsComplex} → ℂ) w) : {w : InfinitePlace K // w.IsComplex} → ℂ) =
        (Pi.single w c : {w : InfinitePlace K // w.IsComplex} → ℂ)
      rw [Pi.single_eq_same]
  rw [hproj.trace]
  have hfin : Module.finrank ℝ p = 2 := by
    rw [LinearMap.finrank_range_of_inj (fun x y h => Pi.single_injective w h : Function.Injective (LinearMap.single ℝ (fun _ => ℂ) w)),
      Complex.finrank_real_complex]
  rw [hfin]
  norm_num

theorem hv_complex (w : {w : InfinitePlace K // w.IsComplex}) :
    ∃ t : ℝ, NumberField.StandardAddChar.stdAddChar K ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (t • vC K w), 0) ≠ 1 := by
  refine ⟨1 / 4, ?_⟩
  rw [NumberField.StandardAddChar.stdAddChar_apply_mk_zero_eq_fourierChar_trace K, RingEquiv.apply_symm_apply, map_smul,
    trace_vC, Real.fourierChar_apply]
  rw [show ((2 * Real.pi * ((1 / 4 : ℝ) • (2 : ℝ)) : ℝ) : ℂ) * Complex.I = Real.pi * Complex.I by
    simp only [smul_eq_mul]; push_cast; ring]
  rw [Complex.exp_pi_mul_I]
  norm_num

section Chain

variable {K}

def Lop (v : MS K) (g : G K → ℂ) : G K → ℂ :=
  fun y => deriv (fun t : ℝ => g (unipotentGL2 (R := AdeleRing (𝓞 K) K) ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (-(t • v)), 0) * y)) 0

variable (vb : Bool → MS K) (f' : G K → ℂ)

def fT : (j : ℕ) → (Fin j → Bool) → (G K → ℂ)
  | 0, _ => f'
  | j + 1, ws => Lop (vb (ws 0)) (fT j (Fin.tail ws))

theorem fT_succ (j : ℕ) (b : Bool) (ws : Fin j → Bool) : fT vb f' (j + 1) (Fin.cons b ws) = Lop (vb b) (fT vb f' j ws) := by
  show Lop (vb ((Fin.cons b ws : Fin (j + 1) → Bool) 0)) (fT vb f' j (Fin.tail (Fin.cons b ws : Fin (j + 1) → Bool))) = _
  rw [Fin.cons_zero, Fin.tail_cons]

variable (γb : Bool → ℝ)

def coeff (j : ℕ) (ws : Fin j → Bool) : ℂ := ∏ i, (γb (ws i) : ℂ)

theorem coeff_succ (j : ℕ) (b : Bool) (ws : Fin j → Bool) : coeff γb (j + 1) (Fin.cons b ws) = γb b * coeff γb j ws := by
  simp only [coeff, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]

theorem norm_coeff_le (j : ℕ) (ws : Fin j → Bool) {Γ : ℝ} (hΓ : ∀ b, |γb b| ≤ Γ) : ‖coeff γb j ws‖ ≤ Γ ^ j := by
  rw [coeff, norm_prod]
  calc ∏ i, ‖(γb (ws i) : ℂ)‖ ≤ ∏ _i : Fin j, Γ :=
        Finset.prod_le_prod (fun i _ => norm_nonneg _) fun i _ => by rw [Complex.norm_real, Real.norm_eq_abs]; exact hΓ _
    _ = Γ ^ j := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

variable (φ : G K → ℂ)

def xs (j : ℕ) (h : G K) : ℂ := ∑ ws : Fin j → Bool, coeff γb j ws * rightConv K φ (fT vb f' j ws) h

theorem xs_zero : xs vb f' γb φ 0 = rightConv K φ f' := by
  funext h
  rw [xs, Fintype.sum_unique]
  show (∏ i : Fin 0, (γb ((default : Fin 0 → Bool) i) : ℂ)) * rightConv K φ f' h = _
  rw [Finset.univ_eq_empty, Finset.prod_empty, one_mul]

end Chain

section PerPlace

variable (c u d₁ d₂ : ℝ) (T : Finset (G K)) (hd : d₁ < d₂)
    (hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂))
    (χ : (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)).Z →* ℂˣ)
    {φ : G K → ℂ}
    (hφ : IsCuspAutomorphicFnAt K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) χ φ)
    (hcont : Continuous φ)
    (w₀ : ℝ) (hχ : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      ‖((χ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm K z ^ w₀)

include hd hcov hφ hcont hχ

theorem perplace {f' : G K → ℂ} (hf' : IsFactorizableTestFn K f') (v₀ : MS K)
    (hv₀ : ∃ t : ℝ, NumberField.StandardAddChar.stdAddChar K ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (t • v₀), 0) ≠ 1)
    (vb : Bool → MS K) (M : ℕ) :
    ∃ Cw : ℝ, 0 ≤ Cw ∧ ∀ (a : (AdeleRing (𝓞 K) K)ˣ) (Γ : ℝ), 0 ≤ Γ →
      (∃ γb : Bool → ℝ, (∀ b, |γb b| ≤ Γ) ∧ ρA K a * v₀ = γb false • vb false + γb true • vb true) →
      ‖whittakerCoefficient K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
          (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
          (NumberField.StandardAddChar.stdAddChar K) (rightConv K φ f') 1 (diagOne a)‖ ≤
        Cw * NumberField.TateGlobal.ideleNorm K a ^ (w₀ / 2) * Γ ^ M := by

  have C1 := fun (g : G K → ℂ) (hg : IsFactorizableTestFn K g) =>
    AutomorphicForm.hasDerivAt_rightConv_mul_unipotentGL2_and_isFactorizableTestFn_leftDeriv_and_linear K φ hcont g hg

  have hfT : ∀ (j : ℕ) (ws : Fin j → Bool), IsFactorizableTestFn K (fT vb f' j ws) := by
    intro j
    induction j with
    | zero => intro ws; exact hf'
    | succ j ih => intro ws; exact (C1 _ (ih (Fin.tail ws))).2.1 (vb (ws 0))

  choose C' hC'0 hC' using fun ws : Fin M → Bool => ubnd K c u d₁ d₂ T hd hcov χ hφ hcont (hfT M ws) w₀ hχ

  obtain ⟨c3, hc3pos, hC3⟩ :=
    AutomorphicForm.exists_norm_whittakerCoefficient_le_mul_of_hasDerivAt_unipotentGL2_of_forall_norm_le K
      (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
      (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) M v₀ hv₀
  refine ⟨c3 * ∑ ws : Fin M → Bool, C' ws, mul_nonneg hc3pos.le (Finset.sum_nonneg fun ws _ => hC'0 ws), ?_⟩
  rintro a Γ hΓ ⟨γb, hγb, hdir⟩

  set X : ℕ → G K → ℂ := fun j => xs vb f' γb φ j with hX
  have hcontRC : ∀ (j : ℕ) (ws : Fin j → Bool), Continuous (rightConv K φ (fT vb f' j ws)) := fun j ws =>
    continuous_rightConv_of hcont (hfT j ws)
  have hX_cont : ∀ j, Continuous (X j) := fun j =>
    continuous_finsetSum _ fun ws _ => continuous_const.mul (hcontRC j ws)
  have hX_inv : ∀ (j : ℕ) (β : K) (h : G K), X j (unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β) * h) = X j h := by
    intro j β h
    simp only [hX, xs, rightConv_globalUnipotent_mul hφ]
  have hX_deriv : ∀ (j : ℕ) (u' : AdeleRing (𝓞 K) K),
      HasDerivAt (fun t : ℝ => X j (unipotentGL2 (R := AdeleRing (𝓞 K) K)
          ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (t • v₀), 0) * (unipotentGL2 u' * diagOne a)))
        (X (j + 1) (unipotentGL2 u' * diagOne a)) 0 := by
    intro j u'
    set g₀ : G K := unipotentGL2 u' * diagOne a with hg₀

    have hfun : (fun t : ℝ => X j (unipotentGL2 (R := AdeleRing (𝓞 K) K)
        ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (t • v₀), 0) * g₀)) =
        fun t => ∑ ws : Fin j → Bool, coeff γb j ws * rightConv K φ (fT vb f' j ws)
          (g₀ * unipotentGL2 (R := AdeleRing (𝓞 K) K)
            ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (t • (γb false • vb false + γb true • vb true)), 0)) := by
      funext t
      rw [hg₀, orbit_identity, hdir]
      rfl
    rw [hfun]

    have hterm : ∀ ws : Fin j → Bool, HasDerivAt (fun t : ℝ => coeff γb j ws * rightConv K φ (fT vb f' j ws)
        (g₀ * unipotentGL2 (R := AdeleRing (𝓞 K) K)
          ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (t • (γb false • vb false + γb true • vb true)), 0)))
        (coeff γb j ws * (γb false * rightConv K φ (fT vb f' (j + 1) (Fin.cons false ws)) g₀ +
          γb true * rightConv K φ (fT vb f' (j + 1) (Fin.cons true ws)) g₀)) 0 := by
      intro ws
      have h1 := ((C1 _ (hfT j ws)).1 (γb false • vb false + γb true • vb true) g₀).const_mul (coeff γb j ws)
      refine HasDerivAt.congr_deriv h1 ?_
      congr 1

      have hsplit : (fun y => deriv (fun t : ℝ => fT vb f' j ws (unipotentGL2 (R := AdeleRing (𝓞 K) K)
          ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (-(t • (γb false • vb false + γb true • vb true))), 0) * y)) 0) =
          fun y => (γb false : ℂ) * Lop (vb false) (fT vb f' j ws) y + (γb true : ℂ) * Lop (vb true) (fT vb f' j ws) y := by
        funext y
        exact (C1 _ (hfT j ws)).2.2 (γb false) (γb true) (vb false) (vb true) y
      rw [hsplit, fT_succ, fT_succ]
      obtain ⟨hLf, hLfs⟩ := AutomorphicForm.continuous_and_hasCompactSupport_of_isFactorizableTestFn K _
        ((C1 _ (hfT j ws)).2.1 (vb false))
      obtain ⟨hLt, hLts⟩ := AutomorphicForm.continuous_and_hasCompactSupport_of_isFactorizableTestFn K _
        ((C1 _ (hfT j ws)).2.1 (vb true))
      exact rightConv_lincomb K hcont hLf hLfs hLt hLts _ _ g₀
    have hsum := HasDerivAt.fun_sum fun ws (_ : ws ∈ (Finset.univ : Finset (Fin j → Bool))) => hterm ws
    refine HasDerivAt.congr_deriv hsum ?_

    show ∑ ws : Fin j → Bool, coeff γb j ws * (γb false * rightConv K φ (fT vb f' (j + 1) (Fin.cons false ws)) g₀ +
        γb true * rightConv K φ (fT vb f' (j + 1) (Fin.cons true ws)) g₀) = X (j + 1) g₀
    simp only [hX, xs]
    rw [← (Fin.consEquiv fun _ : Fin (j + 1) => Bool).sum_comp, Fintype.sum_prod_type, Fintype.sum_bool]
    simp only [Fin.consEquiv, Equiv.coe_fn_mk, coeff_succ]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun ws _ => ?_
    ring

  have hdet : ∀ u' : AdeleRing (𝓞 K) K, NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det
      (unipotentGL2 u' * diagOne a)) = NumberField.TateGlobal.ideleNorm K a := by
    intro u'
    rw [map_mul, det_unipotentGL2, one_mul, det_diagOne']
  have hA : ∀ u' : AdeleRing (𝓞 K) K, ‖X M (unipotentGL2 u' * diagOne a)‖ ≤
      Γ ^ M * NumberField.TateGlobal.ideleNorm K a ^ (w₀ / 2) * ∑ ws : Fin M → Bool, C' ws := by
    intro u'
    calc ‖X M (unipotentGL2 u' * diagOne a)‖
        = ‖∑ ws : Fin M → Bool, coeff γb M ws * rightConv K φ (fT vb f' M ws) (unipotentGL2 u' * diagOne a)‖ := rfl
      _ ≤ ∑ ws : Fin M → Bool, ‖coeff γb M ws * rightConv K φ (fT vb f' M ws) (unipotentGL2 u' * diagOne a)‖ :=
          norm_sum_le _ _
      _ ≤ ∑ ws : Fin M → Bool, Γ ^ M * (C' ws * NumberField.TateGlobal.ideleNorm K a ^ (w₀ / 2)) :=
          Finset.sum_le_sum fun ws _ => by
            rw [norm_mul]
            refine mul_le_mul (norm_coeff_le γb M ws hγb) ?_ (norm_nonneg _) (pow_nonneg hΓ M)
            have := hC' ws (unipotentGL2 u' * diagOne a)
            rwa [hdet] at this
      _ = Γ ^ M * NumberField.TateGlobal.ideleNorm K a ^ (w₀ / 2) * ∑ ws : Fin M → Bool, C' ws := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun ws _ => ?_
          ring
  have key := hC3 X (diagOne a) (Γ ^ M * NumberField.TateGlobal.ideleNorm K a ^ (w₀ / 2) * ∑ ws : Fin M → Bool, C' ws)
    hX_cont hX_inv (fun j u' => hX_deriv j u') hA
  rw [show X 0 = rightConv K φ f' from xs_zero vb f' γb φ] at key
  calc _ ≤ c3 * (Γ ^ M * NumberField.TateGlobal.ideleNorm K a ^ (w₀ / 2) * ∑ ws : Fin M → Bool, C' ws) := key
    _ = c3 * (∑ ws : Fin M → Bool, C' ws) * NumberField.TateGlobal.ideleNorm K a ^ (w₀ / 2) * Γ ^ M := by ring

end PerPlace

end ArchLarge

end

open ArchLarge in
theorem solution
    (K : Type) [Field K] [NumberField K]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hd : d₁ < d₂)
    (hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂))
    (χ : (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)).Z →* ℂˣ)
    (φ : AdelicGL2 (𝓞 K) K → ℂ)
    (hφ : IsCuspAutomorphicFnAt K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) χ φ)
    (hcont : Continuous φ)
    (f : AdelicGL2 (𝓞 K) K → ℂ) (hf : IsFactorizableTestFn K f)
    (tys : AutomorphicForm.ArchTypeFamily K) (hxt : rightConv K φ f ∈ archCutSubmodule K tys)
    (w₀ : ℝ) (hχ : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ‖((χ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = ideleNorm K z ^ w₀)
    (m : ℕ) :
    ∃ C : ℝ, ∀ k : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K k = 1 →
      (∀ w : InfinitePlace K, IsRowIsometry (archComponent K w (glArch (𝓞 K) K k))) →
      ∀ a : (AdeleRing (𝓞 K) K)ˣ, ((a : AdeleRing (𝓞 K) K)).2 = 1 → 1 ≤ ideleNorm K a →
        ‖whittakerCoefficient K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) (rightConv K φ f) 1
            (diagOne a * k)‖ ≤ C * ideleNorm K a ^ (-(m : ℝ)) := by
  classical
  set dK : ℕ := Module.finrank ℚ K with hdK
  have hdKpos : 0 < (dK : ℝ) := by exact_mod_cast Module.finrank_pos
  set M : ℕ := ⌈(dK : ℝ) * ((m : ℝ) + |w₀| / 2)⌉₊ with hM
  have hMge : (dK : ℝ) * ((m : ℝ) + |w₀| / 2) ≤ M := Nat.le_ceil _

  obtain ⟨n, hs, hhs, Bc, hkred⟩ := kred K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
    (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) χ hφ hcont hf tys hxt w₀ hχ
  have hfl : ∀ l : Fin n, IsFactorizableTestFn K (fun y => f ((hs l)⁻¹ * y)) := fun l =>
    isFactorizableTestFn_comp_mul hf (hhs l)

  choose CR hCR0 hCR using fun (l : Fin n) (w : {w : InfinitePlace K // w.IsReal}) =>
    perplace K c u d₁ d₂ T hd hcov χ hφ hcont w₀ hχ (hfl l) (vR K w) (hv_real K w) (fun _ => vR K w) M
  choose CC hCC0 hCC using fun (l : Fin n) (w : {w : InfinitePlace K // w.IsComplex}) =>
    perplace K c u d₁ d₂ T hd hcov χ hφ hcont w₀ hχ (hfl l) (vC K w) (hv_complex K w)
      (fun b => if b then vCI K w else vC K w) M
  set Ctot : Fin n → ℝ := fun l => ∑ w, CR l w + ∑ w, CC l w with hCtot
  have hCtot0 : ∀ l, 0 ≤ Ctot l := fun l =>
    add_nonneg (Finset.sum_nonneg fun w _ => hCR0 l w) (Finset.sum_nonneg fun w _ => hCC0 l w)
  refine ⟨∑ l, Bc * Ctot l, ?_⟩
  intro k hk1 hk2 a ha2 ha1
  obtain ⟨cs, ε, hε2, hεN, hεw, hcs, hW⟩ := hkred k ⟨hk1, hk2⟩
  have hBc0 : ∀ l : Fin n, 0 ≤ Bc := fun l => (norm_nonneg _).trans (hcs l)
  rw [hW (diagOne a)]
  set a' : (AdeleRing (𝓞 K) K)ˣ := a * ε with ha'
  have hDa : diagOne a * diagOne ε = diagOne a' := by rw [ha', map_mul]
  simp_rw [hDa]
  have ha'N : ideleNorm K a' = ideleNorm K a := by rw [ha', NumberField.TateGlobal.ideleNorm_mul, hεN, mul_one]
  have ha'w : ∀ w : InfinitePlace K, ‖((a' : AdeleRing (𝓞 K) K)).1 w‖ = ‖((a : AdeleRing (𝓞 K) K)).1 w‖ := by
    intro w
    have h1 : ((a' : AdeleRing (𝓞 K) K)).1 w = ((a : AdeleRing (𝓞 K) K)).1 w * ((ε : AdeleRing (𝓞 K) K)).1 w := rfl
    rw [h1, norm_mul, hεw w, mul_one]

  obtain ⟨ws, hws⟩ := Finite.exists_max (fun w : InfinitePlace K => ‖((a : AdeleRing (𝓞 K) K)).1 w‖)
  have hNa : 0 < ideleNorm K a := NumberField.TateGlobal.ideleNorm_pos _
  have hprod := NumberField.TateGlobal.ideleNorm_eq_prod_norm_infinitePlace_pow_mult_of_snd_eq_one K a ha2
  have hbig : 1 ≤ ‖((a : AdeleRing (𝓞 K) K)).1 ws‖ := by
    by_contra hlt
    push Not at hlt
    have hlt1 : ideleNorm K a < 1 := by
      rw [hprod]
      calc ∏ w : InfinitePlace K, ‖((a : AdeleRing (𝓞 K) K)).1 w‖ ^ w.mult
          ≤ ∏ _w : InfinitePlace K, ‖((a : AdeleRing (𝓞 K) K)).1 ws‖ :=
            Finset.prod_le_prod (fun w _ => pow_nonneg (norm_nonneg _) _) fun w _ =>
              (pow_le_of_le_one (norm_nonneg _) ((hws w).trans hlt.le) InfinitePlace.mult_ne_zero).trans (hws w)
        _ = ‖((a : AdeleRing (𝓞 K) K)).1 ws‖ ^ Fintype.card (InfinitePlace K) := by
            rw [Finset.prod_const, Finset.card_univ]
        _ < 1 := pow_lt_one₀ (norm_nonneg _) hlt Fintype.card_ne_zero
    linarith
  have hle : ideleNorm K a ≤ ‖((a : AdeleRing (𝓞 K) K)).1 ws‖ ^ dK := by
    rw [hprod, hdK, ← InfinitePlace.sum_mult_eq, ← Finset.prod_pow_eq_pow_sum]
    exact Finset.prod_le_prod (fun w _ => pow_nonneg (norm_nonneg _) _) fun w _ =>
      pow_le_pow_left₀ (norm_nonneg _) (hws w) _
  set Γ : ℝ := ‖((a : AdeleRing (𝓞 K) K)).1 ws‖⁻¹ with hΓ
  have hΓ0 : 0 ≤ Γ := inv_nonneg.mpr (norm_nonneg _)

  have hΓM : Γ ^ M ≤ ideleNorm K a ^ (-((M : ℝ) / dK)) := by
    have h1 : ideleNorm K a ^ ((1 : ℝ) / dK) ≤ ‖((a : AdeleRing (𝓞 K) K)).1 ws‖ := by
      have := Real.rpow_le_rpow hNa.le hle (by positivity : (0 : ℝ) ≤ 1 / dK)
      rwa [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _), mul_one_div_cancel hdKpos.ne', Real.rpow_one] at this
    have h2 : ideleNorm K a ^ ((M : ℝ) / dK) ≤ ‖((a : AdeleRing (𝓞 K) K)).1 ws‖ ^ M := by
      have := pow_le_pow_left₀ (Real.rpow_nonneg hNa.le _) h1 M
      rwa [← Real.rpow_natCast, ← Real.rpow_mul hNa.le, div_mul_eq_mul_div, one_mul] at this
    rw [hΓ, inv_pow, Real.rpow_neg hNa.le]
    exact inv_anti₀ (Real.rpow_pos_of_pos hNa _) h2

  have hΓ' : Γ = ‖(((a'⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).1 ws‖ := by
    have h := norm_inv_arch_mul K a' ws
    rw [ha'w] at h
    rw [hΓ]
    exact (eq_inv_of_mul_eq_one_left h).symm

  have hper : ∀ l : Fin n,
      ‖whittakerCoefficient K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K)
        (rightConv K φ (fun y => f ((hs l)⁻¹ * y))) 1 (diagOne a')‖ ≤ Ctot l * ideleNorm K a ^ (w₀ / 2) * Γ ^ M := by
    intro l
    by_cases hw : ws.IsReal
    · have hb := hCR l ⟨ws, hw⟩ a' Γ hΓ0 ⟨fun b => if b then 0 else (ρA K a').1 ⟨ws, hw⟩, ?_, ?_⟩
      · rw [ha'N] at hb
        refine hb.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hNa.le _))
          (pow_nonneg hΓ0 M))
        show CR l ⟨ws, hw⟩ ≤ ∑ w, CR l w + ∑ w, CC l w
        exact (Finset.single_le_sum (fun w _ => hCR0 l w) (Finset.mem_univ _)).trans
          (le_add_of_nonneg_right (Finset.sum_nonneg fun w _ => hCC0 l w))
      · intro b
        cases b
        · show |(ρA K a').1 ⟨ws, hw⟩| ≤ Γ
          rw [ρA_fst, hΓ']
        · show |(0 : ℝ)| ≤ Γ
          rw [abs_zero]; exact hΓ0
      · show ρA K a' * vR K ⟨ws, hw⟩ = (ρA K a').1 ⟨ws, hw⟩ • vR K ⟨ws, hw⟩ + (0 : ℝ) • vR K ⟨ws, hw⟩
        rw [mul_vR, zero_smul, add_zero]
    · have hw' : ws.IsComplex := InfinitePlace.not_isReal_iff_isComplex.mp hw
      have hb := hCC l ⟨ws, hw'⟩ a' Γ hΓ0
        ⟨fun b => if b then ((ρA K a').2 ⟨ws, hw'⟩).im else ((ρA K a').2 ⟨ws, hw'⟩).re, ?_, ?_⟩
      · rw [ha'N] at hb
        refine hb.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hNa.le _))
          (pow_nonneg hΓ0 M))
        show CC l ⟨ws, hw'⟩ ≤ ∑ w, CR l w + ∑ w, CC l w
        exact (Finset.single_le_sum (fun w _ => hCC0 l w) (Finset.mem_univ _)).trans
          (le_add_of_nonneg_left (Finset.sum_nonneg fun w _ => hCR0 l w))
      · intro b
        have hn : ‖(ρA K a').2 ⟨ws, hw'⟩‖ = Γ := by rw [ρA_snd, hΓ']
        cases b
        · show |((ρA K a').2 ⟨ws, hw'⟩).re| ≤ Γ
          exact (Complex.abs_re_le_norm _).trans hn.le
        · show |((ρA K a').2 ⟨ws, hw'⟩).im| ≤ Γ
          exact (Complex.abs_im_le_norm _).trans hn.le
      · show ρA K a' * vC K ⟨ws, hw'⟩ =
          ((ρA K a').2 ⟨ws, hw'⟩).re • vC K ⟨ws, hw'⟩ + ((ρA K a').2 ⟨ws, hw'⟩).im • vCI K ⟨ws, hw'⟩
        exact mul_vC K _ _

  have hexp : ideleNorm K a ^ (w₀ / 2) * Γ ^ M ≤ ideleNorm K a ^ (-(m : ℝ)) := by
    calc ideleNorm K a ^ (w₀ / 2) * Γ ^ M ≤ ideleNorm K a ^ (w₀ / 2) * ideleNorm K a ^ (-((M : ℝ) / dK)) :=
          mul_le_mul_of_nonneg_left hΓM (Real.rpow_nonneg hNa.le _)
      _ = ideleNorm K a ^ (w₀ / 2 + -((M : ℝ) / dK)) := (Real.rpow_add hNa _ _).symm
      _ ≤ ideleNorm K a ^ (-(m : ℝ)) := by
          refine Real.rpow_le_rpow_of_exponent_le ha1 ?_
          have h1 : (dK : ℝ) * ((m : ℝ) + w₀ / 2) ≤ M :=
            (mul_le_mul_of_nonneg_left (by linarith [le_abs_self w₀]) hdKpos.le).trans hMge
          have h2 : (m : ℝ) + w₀ / 2 ≤ (M : ℝ) / dK := by rw [le_div_iff₀ hdKpos, mul_comm]; exact h1
          linarith

  calc ‖∑ l, cs l * whittakerCoefficient K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K)
          (rightConv K φ (fun y => f ((hs l)⁻¹ * y))) 1 (diagOne a')‖
      ≤ ∑ l, ‖cs l * whittakerCoefficient K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K)
          (rightConv K φ (fun y => f ((hs l)⁻¹ * y))) 1 (diagOne a')‖ := norm_sum_le _ _
    _ ≤ ∑ l, Bc * (Ctot l * ideleNorm K a ^ (w₀ / 2) * Γ ^ M) := Finset.sum_le_sum fun l _ => by
          rw [norm_mul]
          exact mul_le_mul (hcs l) (hper l) (norm_nonneg _) (hBc0 l)
    _ = (∑ l, Bc * Ctot l) * (ideleNorm K a ^ (w₀ / 2) * Γ ^ M) := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun l _ => by ring
    _ ≤ (∑ l, Bc * Ctot l) * ideleNorm K a ^ (-(m : ℝ)) :=
          mul_le_mul_of_nonneg_left hexp (Finset.sum_nonneg fun l _ => mul_nonneg (hBc0 l) (hCtot0 l))

end S_AutomorphicForm_exists_norm_whittakerCoefficient_rightConv_diagOne_mul_le_ideleNorm_rpow_neg_of_one_le
end P2MW
export P2MW.S_AutomorphicForm_exists_norm_whittakerCoefficient_rightConv_diagOne_mul_le_ideleNorm_rpow_neg_of_one_le (solution)
