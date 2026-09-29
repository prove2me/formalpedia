-- Prove2me | solution 1 for AutomorphicForm.exists_mem_archCutSubmodule_isIsotypicCuspFormAt_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/aa61c3ac-0e3b-54cd-8884-35e1cbc29a65

import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_LocalLanglands_HeckeCosetSystem
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Theorems.Thm_HeckeIntegralSeam_exists_isHeckeCosetSystem_localRep_heckeGen
import Theorems.Thm_AutomorphicForm_isIsotypicCuspFormAt_rightConv_of_isUnitFactorizableAt_of_forall_isHeckeCosetEigenfunctionAt
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Topology.ContinuousMap.Algebra
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_mem_archCutSubmodule_isIsotypicCuspFormAt_ne_zero
p2m_attr_erase "instance" "RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions IsDedekindDomain.HeightOneSpectrum.instSeparableSpaceAdicCompletionOfCountable_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.whittakerCoefficient_zero NumberField.StandardAddChar.ratArchLine_apply"
p2m_attr_erase "simp" "NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply"

set_option autoImplicit false

namespace IsotypicArchCut

open AutomorphicForm AutomorphicForm.WindowedSiegel Matrix NumberField NumberField.InfinitePlace
open NumberField.AdelicLevel
open scoped Classical

variable {K : Type*} [NormedField K]

private
def entrySq (m : Matrix (Fin 2) (Fin 2) K) : ℝ :=
  ‖m 0 0‖ ^ 2 + ‖m 0 1‖ ^ 2 + (‖m 1 0‖ ^ 2 + ‖m 1 1‖ ^ 2)

private
theorem entrySq_nonneg (m : Matrix (Fin 2) (Fin 2) K) : 0 ≤ entrySq m := by
  unfold entrySq
  positivity

private
theorem entrySq_mul_of_isRowIsometry (m : Matrix (Fin 2) (Fin 2) K) {k : GL (Fin 2) K}
    (hk : IsRowIsometry k) : entrySq (m * (k : Matrix (Fin 2) (Fin 2) K)) = entrySq m := by
  simp only [entrySq, Matrix.mul_apply, Fin.sum_univ_two]
  rw [hk.2 (m 0 0) (m 0 1), hk.2 (m 1 0) (m 1 1)]

private
theorem entrySq_adjugate (m : Matrix (Fin 2) (Fin 2) K) : entrySq m.adjugate = entrySq m := by
  rw [Matrix.adjugate_fin_two]
  simp only [entrySq, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, norm_neg]
  ring

private
theorem adjugate_eq_inv_of_mem {k : GL (Fin 2) K} (hk : k ∈ rowIsometrySubgroup₀ K) :
    (k : Matrix (Fin 2) (Fin 2) K).adjugate = ((k⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
  have hdet : (k : Matrix (Fin 2) (Fin 2) K).det = 1 := ((mem_rowIsometrySubgroup₀_iff K).mp hk).1
  rw [Matrix.coe_units_inv, Matrix.inv_def, hdet, Ring.inverse_one, one_smul]

private
theorem entrySq_mul_of_mem {k : GL (Fin 2) K} (hk : k ∈ rowIsometrySubgroup₀ K)
    (m : Matrix (Fin 2) (Fin 2) K) : entrySq ((k : Matrix (Fin 2) (Fin 2) K) * m) = entrySq m := by
  have hk' : IsRowIsometry (k⁻¹ : GL (Fin 2) K) :=
    ((mem_rowIsometrySubgroup₀_iff K).mp (inv_mem hk)).2
  rw [← entrySq_adjugate, Matrix.adjugate_mul_distrib, adjugate_eq_inv_of_mem hk,
    entrySq_mul_of_isRowIsometry _ hk', entrySq_adjugate]

private
theorem entrySq_mul_of_mem' (m : Matrix (Fin 2) (Fin 2) K) {k : GL (Fin 2) K}
    (hk : k ∈ rowIsometrySubgroup₀ K) : entrySq (m * (k : Matrix (Fin 2) (Fin 2) K)) = entrySq m :=
  entrySq_mul_of_isRowIsometry m ((mem_rowIsometrySubgroup₀_iff K).mp hk).2

private
theorem entrySq_conj {k : GL (Fin 2) K} (hk : k ∈ rowIsometrySubgroup₀ K) (m : Matrix (Fin 2) (Fin 2) K) :
    entrySq ((k : Matrix (Fin 2) (Fin 2) K) * m * ((k⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K))
      = entrySq m := by
  rw [entrySq_mul_of_mem' _ (inv_mem hk), entrySq_mul_of_mem hk]

private
theorem det_mul_of_mem {k : GL (Fin 2) K} (hk : k ∈ rowIsometrySubgroup₀ K) (m : Matrix (Fin 2) (Fin 2) K) :
    ((k : Matrix (Fin 2) (Fin 2) K) * m).det = m.det := by
  rw [Matrix.det_mul, ((mem_rowIsometrySubgroup₀_iff K).mp hk).1, one_mul]

private
theorem det_mul_of_mem' (m : Matrix (Fin 2) (Fin 2) K) {k : GL (Fin 2) K} (hk : k ∈ rowIsometrySubgroup₀ K) :
    (m * (k : Matrix (Fin 2) (Fin 2) K)).det = m.det := by
  rw [Matrix.det_mul, ((mem_rowIsometrySubgroup₀_iff K).mp hk).1, mul_one]

private
theorem conj_sub_one (k : GL (Fin 2) K) (g : Matrix (Fin 2) (Fin 2) K) :
    (k : Matrix (Fin 2) (Fin 2) K) * g * ((k⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) - 1
      = (k : Matrix (Fin 2) (Fin 2) K) * (g - 1) * ((k⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
  have h : (k : Matrix (Fin 2) (Fin 2) K) * ((k⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  rw [Matrix.mul_sub, Matrix.sub_mul, mul_one, h]

private
theorem entrySq_conj_sub_one {k : GL (Fin 2) K} (hk : k ∈ rowIsometrySubgroup₀ K)
    (g : Matrix (Fin 2) (Fin 2) K) :
    entrySq ((k : Matrix (Fin 2) (Fin 2) K) * g * ((k⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) - 1)
      = entrySq (g - 1) := by
  rw [conj_sub_one, entrySq_conj hk]

private
def localBump (β₁ β₂ : ℝ → ℝ) (m : Matrix (Fin 2) (Fin 2) K) : ℝ :=
  β₁ (entrySq m) * β₂ (‖m.det‖ ^ 2)

private
theorem localBump_mul_of_mem (β₁ β₂ : ℝ → ℝ) {k : GL (Fin 2) K} (hk : k ∈ rowIsometrySubgroup₀ K)
    (m : Matrix (Fin 2) (Fin 2) K) :
    localBump β₁ β₂ ((k : Matrix (Fin 2) (Fin 2) K) * m) = localBump β₁ β₂ m := by
  rw [localBump, localBump, entrySq_mul_of_mem hk, det_mul_of_mem hk]

private
theorem localBump_mul_of_mem' (β₁ β₂ : ℝ → ℝ) (m : Matrix (Fin 2) (Fin 2) K) {k : GL (Fin 2) K}
    (hk : k ∈ rowIsometrySubgroup₀ K) :
    localBump β₁ β₂ (m * (k : Matrix (Fin 2) (Fin 2) K)) = localBump β₁ β₂ m := by
  rw [localBump, localBump, entrySq_mul_of_mem' m hk, det_mul_of_mem' m hk]

private
theorem sq_norm_entry_le (m : Matrix (Fin 2) (Fin 2) K) (i j : Fin 2) : ‖m i j‖ ^ 2 ≤ entrySq m := by
  have h00 := sq_nonneg ‖m 0 0‖
  have h01 := sq_nonneg ‖m 0 1‖
  have h10 := sq_nonneg ‖m 1 0‖
  have h11 := sq_nonneg ‖m 1 1‖
  fin_cases i <;> fin_cases j <;> simp only [entrySq, Fin.zero_eta, Fin.mk_one, Fin.isValue] <;> linarith

private
theorem norm_entry_le_sqrt {m : Matrix (Fin 2) (Fin 2) K} {A : ℝ} (hm : entrySq m ≤ A) (i j : Fin 2) :
    ‖m i j‖ ≤ Real.sqrt A :=
  Real.le_sqrt_of_sq_le ((sq_norm_entry_le m i j).trans hm)

private
theorem norm_inv_entry_le {m : Matrix (Fin 2) (Fin 2) K} {A a : ℝ} (ha : 0 < a) (hm : entrySq m ≤ A)
    (hd : a ≤ ‖m.det‖ ^ 2) (i j : Fin 2) : ‖m⁻¹ i j‖ ≤ Real.sqrt A / Real.sqrt a := by
  rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, norm_mul]
  have hadj : ‖m.adjugate i j‖ ≤ Real.sqrt A :=
    norm_entry_le_sqrt (by rw [entrySq_adjugate]; exact hm) i j
  have hdet : Real.sqrt a ≤ ‖m.det‖ := by
    calc Real.sqrt a ≤ Real.sqrt (‖m.det‖ ^ 2) := Real.sqrt_le_sqrt hd
      _ = ‖m.det‖ := Real.sqrt_sq (norm_nonneg _)
  rw [Ring.inverse_eq_inv, norm_inv, div_eq_inv_mul]
  exact mul_le_mul (inv_anti₀ (Real.sqrt_pos.mpr ha) hdet) hadj (norm_nonneg _)
    (inv_nonneg.mpr (Real.sqrt_nonneg _))

variable {L : Type*} [NormedField L]

private
theorem localBump_map (β₁ β₂ : ℝ → ℝ) (f : K →+* L) (hf : Isometry f) (m : Matrix (Fin 2) (Fin 2) K) :
    localBump β₁ β₂ (m.map f) = localBump β₁ β₂ m := by
  have hn : ∀ x : K, ‖f x‖ = ‖x‖ := fun x => by
    simpa [dist_eq_norm] using hf.dist_eq x 0
  have hdet : (m.map f).det = f m.det := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply]
  simp only [localBump, entrySq, Matrix.map_apply, hn, hdet]

section Witness

variable (F : Type) [Field F] [NumberField F]

private
def realCoord (X : Fin 2 → Fin 2 → mixedEmbedding.mixedSpace F) (v : {w : InfinitePlace F // IsReal w}) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of fun i j => (X i j).1 v

private
def complexCoord (X : Fin 2 → Fin 2 → mixedEmbedding.mixedSpace F)
    (v : {w : InfinitePlace F // IsComplex w}) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of fun i j => (X i j).2 v

private
noncomputable def witness (β₁ β₂ : ℝ → ℝ) (X : Fin 2 → Fin 2 → mixedEmbedding.mixedSpace F) : ℂ :=
  (∏ v : {w : InfinitePlace F // IsReal w}, (localBump β₁ β₂ (realCoord F X v) : ℂ)) *
    ∏ v : {w : InfinitePlace F // IsComplex w}, (localBump β₁ β₂ (complexCoord F X v) : ℂ)

private
noncomputable def archFactor (β₁ β₂ : ℝ → ℝ) (g : GL (Fin 2) (InfiniteAdeleRing F)) : ℂ :=
  ∏ w : InfinitePlace F,
    (localBump β₁ β₂ (AdelicLevel.archComponent F w g : Matrix (Fin 2) (Fin 2) w.Completion) : ℂ)

omit [NumberField F] in
private
theorem realCoord_archEntries (β₁ β₂ : ℝ → ℝ) (g : GL (Fin 2) (InfiniteAdeleRing F))
    (v : {w : InfinitePlace F // IsReal w}) :
    localBump β₁ β₂ (realCoord F (archEntries F g) v)
      = localBump β₁ β₂ (AdelicLevel.archComponent F v.1 g : Matrix (Fin 2) (Fin 2) v.1.Completion) := by
  rw [← localBump_map β₁ β₂ (Completion.extensionEmbeddingOfIsReal v.2)
    (Completion.isometry_extensionEmbeddingOfIsReal v.2)]
  congr 1

omit [NumberField F] in
private
theorem complexCoord_archEntries (β₁ β₂ : ℝ → ℝ) (g : GL (Fin 2) (InfiniteAdeleRing F))
    (v : {w : InfinitePlace F // IsComplex w}) :
    localBump β₁ β₂ (complexCoord F (archEntries F g) v)
      = localBump β₁ β₂ (AdelicLevel.archComponent F v.1 g : Matrix (Fin 2) (Fin 2) v.1.Completion) := by
  rw [← localBump_map β₁ β₂ (Completion.extensionEmbedding v.1) (Completion.isometry_extensionEmbedding v.1)]
  congr 1

private
theorem archFactor_eq_witness (β₁ β₂ : ℝ → ℝ) (g : GL (Fin 2) (InfiniteAdeleRing F)) :
    archFactor F β₁ β₂ g = witness F β₁ β₂ (archEntries F g) := by
  unfold archFactor witness
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun w : InfinitePlace F => IsReal w)]
  congr 1
  · exact Fintype.prod_congr _ _ fun v => by rw [realCoord_archEntries]
  · exact Fintype.prod_equiv (Equiv.subtypeEquivRight (p := fun w : InfinitePlace F => ¬ IsReal w)
      (q := fun w : InfinitePlace F => IsComplex w) fun _ => not_isReal_iff_isComplex) _ _
      fun v => by rw [complexCoord_archEntries]; rfl

private
theorem contDiff_det_of {E 𝔸 : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedCommRing 𝔸]
    [NormedAlgebra ℝ 𝔸] {a b c d : E → 𝔸} (ha : ContDiff ℝ (⊤ : ℕ∞) a) (hb : ContDiff ℝ (⊤ : ℕ∞) b)
    (hc : ContDiff ℝ (⊤ : ℕ∞) c) (hd : ContDiff ℝ (⊤ : ℕ∞) d) :
    ContDiff ℝ (⊤ : ℕ∞) fun x => (Matrix.of ![![a x, b x], ![c x, d x]]).det := by
  simp only [Matrix.det_fin_two_of]
  exact (ha.mul hd).sub (hb.mul hc)

private
theorem contDiff_localBump_of {E 𝕂 : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [RCLike 𝕂]
    {β₁ β₂ : ℝ → ℝ} (hβ₁ : ContDiff ℝ (⊤ : ℕ∞) β₁) (hβ₂ : ContDiff ℝ (⊤ : ℕ∞) β₂) {a b c d : E → 𝕂}
    (ha : ContDiff ℝ (⊤ : ℕ∞) a) (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hc : ContDiff ℝ (⊤ : ℕ∞) c)
    (hd : ContDiff ℝ (⊤ : ℕ∞) d) :
    ContDiff ℝ (⊤ : ℕ∞) fun x => localBump β₁ β₂ (Matrix.of ![![a x, b x], ![c x, d x]]) := by
  have hsq : ContDiff ℝ (⊤ : ℕ∞) fun x => entrySq (Matrix.of ![![a x, b x], ![c x, d x]]) := by
    simp only [entrySq, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one]
    exact ((ha.norm_sq (𝕜 := 𝕂)).add (hb.norm_sq (𝕜 := 𝕂))).add
      ((hc.norm_sq (𝕜 := 𝕂)).add (hd.norm_sq (𝕜 := 𝕂)))
  have hdet : ContDiff ℝ (⊤ : ℕ∞) fun x => ‖(Matrix.of ![![a x, b x], ![c x, d x]]).det‖ ^ 2 :=
    (contDiff_det_of ha hb hc hd).norm_sq (𝕜 := 𝕂)
  exact (hβ₁.comp hsq).mul (hβ₂.comp hdet)

private
theorem contDiff_coord_real (v : {w : InfinitePlace F // IsReal w}) (i j : Fin 2) :
    ContDiff ℝ (⊤ : ℕ∞) fun X : Fin 2 → Fin 2 → mixedEmbedding.mixedSpace F => (X i j).1 v := by
  have h : ContDiff ℝ (⊤ : ℕ∞) fun X : Fin 2 → Fin 2 → mixedEmbedding.mixedSpace F => X i j :=
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => mixedEmbedding.mixedSpace F) j).comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => Fin 2 → mixedEmbedding.mixedSpace F) i)).contDiff
  exact (ContinuousLinearMap.proj (R := ℝ) v).contDiff.comp h.fst

private
theorem contDiff_coord_complex (v : {w : InfinitePlace F // IsComplex w}) (i j : Fin 2) :
    ContDiff ℝ (⊤ : ℕ∞) fun X : Fin 2 → Fin 2 → mixedEmbedding.mixedSpace F => (X i j).2 v := by
  have h : ContDiff ℝ (⊤ : ℕ∞) fun X : Fin 2 → Fin 2 → mixedEmbedding.mixedSpace F => X i j :=
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => mixedEmbedding.mixedSpace F) j).comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => Fin 2 → mixedEmbedding.mixedSpace F) i)).contDiff
  exact (ContinuousLinearMap.proj (R := ℝ) v).contDiff.comp h.snd

omit [NumberField F] in
private
theorem realCoord_eq (X : Fin 2 → Fin 2 → mixedEmbedding.mixedSpace F) (v : {w : InfinitePlace F // IsReal w}) :
    realCoord F X v = Matrix.of ![![(X 0 0).1 v, (X 0 1).1 v], ![(X 1 0).1 v, (X 1 1).1 v]] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

omit [NumberField F] in
private
theorem complexCoord_eq (X : Fin 2 → Fin 2 → mixedEmbedding.mixedSpace F)
    (v : {w : InfinitePlace F // IsComplex w}) :
    complexCoord F X v = Matrix.of ![![(X 0 0).2 v, (X 0 1).2 v], ![(X 1 0).2 v, (X 1 1).2 v]] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

private
theorem contDiff_witness {β₁ β₂ : ℝ → ℝ} (hβ₁ : ContDiff ℝ (⊤ : ℕ∞) β₁) (hβ₂ : ContDiff ℝ (⊤ : ℕ∞) β₂) :
    ContDiff ℝ (⊤ : ℕ∞) (witness F β₁ β₂) := by
  unfold witness
  refine ContDiff.mul (contDiff_prod fun v _ => ?_) (contDiff_prod fun v _ => ?_)
  · simp only [realCoord_eq]
    exact Complex.ofRealCLM.contDiff.comp (contDiff_localBump_of hβ₁ hβ₂ (contDiff_coord_real F v 0 0)
      (contDiff_coord_real F v 0 1) (contDiff_coord_real F v 1 0) (contDiff_coord_real F v 1 1))
  · simp only [complexCoord_eq]
    exact Complex.ofRealCLM.contDiff.comp (contDiff_localBump_of hβ₁ hβ₂ (contDiff_coord_complex F v 0 0)
      (contDiff_coord_complex F v 0 1) (contDiff_coord_complex F v 1 0) (contDiff_coord_complex F v 1 1))

private
theorem archFactor_smooth {β₁ β₂ : ℝ → ℝ} (hβ₁ : ContDiff ℝ (⊤ : ℕ∞) β₁) (hβ₂ : ContDiff ℝ (⊤ : ℕ∞) β₂) :
    ∃ Φ : (Fin 2 → Fin 2 → mixedEmbedding.mixedSpace F) → ℂ,
      ContDiff ℝ (⊤ : ℕ∞) Φ ∧ ∀ g, archFactor F β₁ β₂ g = Φ (archEntries F g) :=
  ⟨witness F β₁ β₂, contDiff_witness F hβ₁ hβ₂, archFactor_eq_witness F β₁ β₂⟩

end Witness

section Support

variable (F : Type) [Field F] [NumberField F]

private
def compMat (w : InfinitePlace F) (m : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) :
    Matrix (Fin 2) (Fin 2) w.Completion :=
  m.map fun x => x w

omit [NumberField F] in
private
theorem compMat_coe (w : InfinitePlace F) (g : GL (Fin 2) (InfiniteAdeleRing F)) :
    compMat F w (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F))
      = (archComponent F w g : Matrix (Fin 2) (Fin 2) w.Completion) := by
  ext i j
  rfl

omit [NumberField F] in
private
theorem continuous_compMat (w : InfinitePlace F) : Continuous (compMat F w) :=
  show Continuous (fun m : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F) => m.map fun x => x w) from
    continuous_id.matrix_map (continuous_apply w)

private
def boundedSet (A a : ℝ) : Set (GL (Fin 2) (InfiniteAdeleRing F)) :=
  {g | ∀ w : InfinitePlace F, entrySq (archComponent F w g : Matrix (Fin 2) (Fin 2) w.Completion) ≤ A ∧
    a ≤ ‖(archComponent F w g : Matrix (Fin 2) (Fin 2) w.Completion).det‖ ^ 2}

private
theorem support_archFactor_subset {β₁ β₂ : ℝ → ℝ} {A a : ℝ} (hβ₁ : ∀ t, A < t → β₁ t = 0)
    (hβ₂ : ∀ t, t < a → β₂ t = 0) : Function.support (archFactor F β₁ β₂) ⊆ boundedSet F A a := by
  intro g hg w
  by_contra hw
  apply hg
  unfold archFactor
  refine Finset.prod_eq_zero (Finset.mem_univ w) ?_
  rw [not_and_or] at hw
  rcases hw with hw | hw
  · rw [localBump, hβ₁ _ (not_le.mp hw), zero_mul, Complex.ofReal_zero]
  · rw [localBump, hβ₂ _ (not_le.mp hw), mul_zero, Complex.ofReal_zero]

private
def entryBall (r : ℝ) : Set (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) :=
  Set.pi Set.univ fun _ : Fin 2 => Set.pi Set.univ fun _ : Fin 2 =>
    (Set.pi Set.univ (fun w : InfinitePlace F => Metric.closedBall (0 : w.Completion) r) :
      Set (InfiniteAdeleRing F))

omit [NumberField F] in
private
theorem mem_entryBall {r : ℝ} {m : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)}
    (h : ∀ (i j : Fin 2) (w : InfinitePlace F), ‖m i j w‖ ≤ r) : m ∈ entryBall F r :=
  Set.mem_univ_pi.mpr fun i => Set.mem_univ_pi.mpr fun j => Set.mem_univ_pi.mpr fun w => by
    simpa [Metric.mem_closedBall, dist_zero_right] using h i j w

omit [NumberField F] in
private
theorem isCompact_entryBall (r : ℝ) : IsCompact (entryBall F r) := by
  have hball : ∀ w : InfinitePlace F, IsCompact (Metric.closedBall (0 : w.Completion) r) := fun w => by
    have h := (Completion.isometry_extensionEmbedding w).isClosedEmbedding.isCompact_preimage
      (isCompact_closedBall (0 : ℂ) r)
    rwa [← map_zero (Completion.extensionEmbedding w),
      (Completion.isometry_extensionEmbedding w).preimage_closedBall] at h
  have hB : IsCompact (Set.pi Set.univ (fun w : InfinitePlace F => Metric.closedBall (0 : w.Completion) r) :
      Set (InfiniteAdeleRing F)) :=
    isCompact_univ_pi fun w => hball w
  exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hB

omit [NumberField F] in

private
theorem isCompact_boundedSet {A a : ℝ} (ha : 0 < a) : IsCompact (boundedSet F A a) := by
  rw [Units.isEmbedding_embedProduct.isCompact_iff]
  set M := Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)
  let C : Set (M × Mᵐᵒᵖ) :=
    {p | p.1 * MulOpposite.unop p.2 = 1 ∧ MulOpposite.unop p.2 * p.1 = 1 ∧
      ∀ w : InfinitePlace F, entrySq (compMat F w p.1) ≤ A ∧ a ≤ ‖(compMat F w p.1).det‖ ^ 2}
  have himage : Units.embedProduct M '' boundedSet F A a = C := by
    ext p
    constructor
    · rintro ⟨g, hg, rfl⟩
      refine ⟨?_, ?_, fun w => ?_⟩
      · simp [Units.embedProduct_apply]
      · simp [Units.embedProduct_apply]
      · simpa [Units.embedProduct_apply, compMat_coe] using hg w
    · rintro ⟨h₁, h₂, hw⟩
      refine ⟨⟨p.1, MulOpposite.unop p.2, h₁, h₂⟩, fun w => ?_, ?_⟩
      · simpa [← compMat_coe] using hw w
      · simp [Units.embedProduct_apply]
  rw [himage]
  have hclosed : IsClosed C := by
    have h1 : IsClosed {p : M × Mᵐᵒᵖ | p.1 * MulOpposite.unop p.2 = 1} :=
      isClosed_eq (continuous_fst.mul MulOpposite.continuous_unop.snd') continuous_const
    have h2 : IsClosed {p : M × Mᵐᵒᵖ | MulOpposite.unop p.2 * p.1 = 1} :=
      isClosed_eq (MulOpposite.continuous_unop.snd'.mul continuous_fst) continuous_const
    have h3 : IsClosed {p : M × Mᵐᵒᵖ | ∀ w : InfinitePlace F,
        entrySq (compMat F w p.1) ≤ A ∧ a ≤ ‖(compMat F w p.1).det‖ ^ 2} := by
      rw [Set.setOf_forall]
      refine isClosed_iInter fun w => ?_
      have hc : Continuous fun p : M × Mᵐᵒᵖ => compMat F w p.1 := (continuous_compMat F w).comp continuous_fst
      have he : ∀ i j : Fin 2, Continuous fun p : M × Mᵐᵒᵖ => compMat F w p.1 i j := fun i j =>
        hc.matrix_elem i j
      have hsq : Continuous fun p : M × Mᵐᵒᵖ => entrySq (compMat F w p.1) :=
        (((he 0 0).norm.pow 2).add ((he 0 1).norm.pow 2)).add
          (((he 1 0).norm.pow 2).add ((he 1 1).norm.pow 2))
      have hdet : Continuous fun p : M × Mᵐᵒᵖ => ‖(compMat F w p.1).det‖ ^ 2 := (hc.matrix_det.norm).pow 2
      exact (isClosed_le hsq continuous_const).inter (isClosed_le continuous_const hdet)
    exact h1.inter (h2.inter h3)
  have hsub : C ⊆ entryBall F (Real.sqrt A) ×ˢ (MulOpposite.op '' entryBall F (Real.sqrt A / Real.sqrt a)) := by
    rintro ⟨x, y⟩ ⟨h₁, h₂, hw⟩
    refine ⟨mem_entryBall F fun i j w => ?_, MulOpposite.unop y, mem_entryBall F fun i j w => ?_,
      MulOpposite.op_unop y⟩
    · have := norm_entry_le_sqrt (hw w).1 i j
      simpa [compMat, Matrix.map_apply] using this
    · have hinv : compMat F w (MulOpposite.unop y) = (compMat F w x)⁻¹ := by
        have hmul : compMat F w x * compMat F w (MulOpposite.unop y) = 1 := by
          calc compMat F w x * compMat F w (MulOpposite.unop y)
              = compMat F w (x * MulOpposite.unop y) :=
                (Matrix.map_mul (f := Pi.evalRingHom (fun w : InfinitePlace F => w.Completion) w)).symm
            _ = compMat F w 1 := by rw [h₁]
            _ = 1 := Matrix.map_one _ rfl rfl
        exact (Matrix.inv_eq_right_inv hmul).symm
      have := norm_inv_entry_le ha (hw w).1 (hw w).2 i j
      rw [← hinv] at this
      simpa [compMat, Matrix.map_apply] using this
  exact ((isCompact_entryBall F _).prod ((isCompact_entryBall F _).image MulOpposite.continuous_op)).of_isClosed_subset
    hclosed hsub

private
theorem hasCompactSupport_archFactor {β₁ β₂ : ℝ → ℝ} {A a : ℝ} (ha : 0 < a) (hβ₁ : ∀ t, A < t → β₁ t = 0)
    (hβ₂ : ∀ t, t < a → β₂ t = 0) : HasCompactSupport (archFactor F β₁ β₂) :=
  HasCompactSupport.of_support_subset_isCompact (isCompact_boundedSet F ha) (support_archFactor_subset F hβ₁ hβ₂)

end Support

section Kernel

variable (F : Type) [Field F] [NumberField F]

variable {K L : Type*} [NormedField K] [NormedField L] in

private
theorem entrySq_map (f : K →+* L) (hf : Isometry f) (m : Matrix (Fin 2) (Fin 2) K) :
    entrySq (m.map f) = entrySq m := by
  simp only [entrySq, Matrix.map_apply, hf.norm_map_of_map_zero (map_zero f)]

variable {K : Type*} [NormedField K] in
private
theorem entrySq_of_sub_one (a b c d : K) :
    entrySq (Matrix.of ![![a, b], ![c, d]] - 1) = ‖a - 1‖ ^ 2 + ‖b‖ ^ 2 + (‖c‖ ^ 2 + ‖d - 1‖ ^ 2) := by
  simp [entrySq, Matrix.one_fin_two]

private
noncomputable def dispArch (g : GL (Fin 2) (InfiniteAdeleRing F)) : ℂ :=
  ((∑ w : InfinitePlace F, entrySq ((archComponent F w g : Matrix (Fin 2) (Fin 2) w.Completion) - 1) : ℝ) : ℂ)

private
noncomputable def dispWitness (X : Fin 2 → Fin 2 → mixedEmbedding.mixedSpace F) : ℝ :=
  (∑ v : {w : InfinitePlace F // IsReal w}, entrySq (realCoord F X v - 1)) +
    ∑ v : {w : InfinitePlace F // IsComplex w}, entrySq (complexCoord F X v - 1)

omit [NumberField F] in
private
theorem realCoord_archEntries_eq (g : GL (Fin 2) (InfiniteAdeleRing F)) (v : {w : InfinitePlace F // IsReal w}) :
    realCoord F (archEntries F g) v
      = (archComponent F v.1 g : Matrix (Fin 2) (Fin 2) v.1.Completion).map
          (Completion.extensionEmbeddingOfIsReal v.2) :=
  rfl

omit [NumberField F] in
private
theorem complexCoord_archEntries_eq (g : GL (Fin 2) (InfiniteAdeleRing F))
    (v : {w : InfinitePlace F // IsComplex w}) :
    complexCoord F (archEntries F g) v
      = (archComponent F v.1 g : Matrix (Fin 2) (Fin 2) v.1.Completion).map (Completion.extensionEmbedding v.1) :=
  rfl

omit [NumberField F] in
private
theorem entrySq_realCoord_archEntries_sub_one (g : GL (Fin 2) (InfiniteAdeleRing F))
    (v : {w : InfinitePlace F // IsReal w}) :
    entrySq (realCoord F (archEntries F g) v - 1)
      = entrySq ((archComponent F v.1 g : Matrix (Fin 2) (Fin 2) v.1.Completion) - 1) := by
  rw [realCoord_archEntries_eq, ← entrySq_map (Completion.extensionEmbeddingOfIsReal v.2)
    (Completion.isometry_extensionEmbeddingOfIsReal v.2) (_ - 1), Matrix.map_sub _ (map_sub _),
    Matrix.map_one _ (map_zero _) (map_one _)]

omit [NumberField F] in
private
theorem entrySq_complexCoord_archEntries_sub_one (g : GL (Fin 2) (InfiniteAdeleRing F))
    (v : {w : InfinitePlace F // IsComplex w}) :
    entrySq (complexCoord F (archEntries F g) v - 1)
      = entrySq ((archComponent F v.1 g : Matrix (Fin 2) (Fin 2) v.1.Completion) - 1) := by
  rw [complexCoord_archEntries_eq, ← entrySq_map (Completion.extensionEmbedding v.1)
    (Completion.isometry_extensionEmbedding v.1) (_ - 1), Matrix.map_sub _ (map_sub _),
    Matrix.map_one _ (map_zero _) (map_one _)]

private
theorem dispArch_eq_witness (g : GL (Fin 2) (InfiniteAdeleRing F)) :
    dispArch F g = ((dispWitness F (archEntries F g) : ℝ) : ℂ) := by
  unfold dispArch dispWitness
  congr 1
  rw [← Fintype.sum_subtype_add_sum_subtype (fun w : InfinitePlace F => IsReal w)]
  congr 1
  · exact Fintype.sum_congr _ _ fun v => by rw [entrySq_realCoord_archEntries_sub_one]
  · exact Fintype.sum_equiv (Equiv.subtypeEquivRight (p := fun w : InfinitePlace F => ¬ IsReal w)
      (q := fun w : InfinitePlace F => IsComplex w) fun _ => not_isReal_iff_isComplex) _ _
      fun v => by rw [entrySq_complexCoord_archEntries_sub_one]; rfl

private
theorem contDiff_dispWitness : ContDiff ℝ (⊤ : ℕ∞) (dispWitness F) := by
  unfold dispWitness
  refine ContDiff.add (ContDiff.sum fun v _ => ?_) (ContDiff.sum fun v _ => ?_)
  · simp only [realCoord_eq, entrySq_of_sub_one]
    exact (((contDiff_coord_real F v 0 0).sub contDiff_const).norm_sq (𝕜 := ℝ)).add
      ((contDiff_coord_real F v 0 1).norm_sq (𝕜 := ℝ)) |>.add
      (((contDiff_coord_real F v 1 0).norm_sq (𝕜 := ℝ)).add
        (((contDiff_coord_real F v 1 1).sub contDiff_const).norm_sq (𝕜 := ℝ)))
  · simp only [complexCoord_eq, entrySq_of_sub_one]
    exact (((contDiff_coord_complex F v 0 0).sub contDiff_const).norm_sq (𝕜 := ℂ)).add
      ((contDiff_coord_complex F v 0 1).norm_sq (𝕜 := ℂ)) |>.add
      (((contDiff_coord_complex F v 1 0).norm_sq (𝕜 := ℂ)).add
        (((contDiff_coord_complex F v 1 1).sub contDiff_const).norm_sq (𝕜 := ℂ)))

private
noncomputable def kernelFactor (R : ℂ) (m : ℕ) (β₁ β₂ : ℝ → ℝ) (g : GL (Fin 2) (InfiniteAdeleRing F)) : ℂ :=
  (R - dispArch F g) ^ m * archFactor F β₁ β₂ g

private
theorem kernelFactor_apply (R : ℂ) (m : ℕ) (β₁ β₂ : ℝ → ℝ) (g : GL (Fin 2) (InfiniteAdeleRing F)) :
    kernelFactor F R m β₁ β₂ g = (R - dispArch F g) ^ m * archFactor F β₁ β₂ g :=
  rfl

private
theorem isArchTestFactor_kernelFactor (R : ℂ) (m : ℕ) {β₁ β₂ : ℝ → ℝ} {A a : ℝ} (ha : 0 < a)
    (hβ₁ : ContDiff ℝ (⊤ : ℕ∞) β₁) (hβ₂ : ContDiff ℝ (⊤ : ℕ∞) β₂) (hβ₁A : ∀ t, A < t → β₁ t = 0)
    (hβ₂a : ∀ t, t < a → β₂ t = 0) : IsArchTestFactor F (kernelFactor F R m β₁ β₂) := by
  refine ⟨⟨fun X => (R - ((dispWitness F X : ℝ) : ℂ)) ^ m * witness F β₁ β₂ X, ?_, fun g => ?_⟩, ?_⟩
  · exact ((contDiff_const.sub (Complex.ofRealCLM.contDiff.comp (contDiff_dispWitness F))).pow m).mul
      (contDiff_witness F hβ₁ hβ₂)
  · rw [kernelFactor_apply, dispArch_eq_witness, archFactor_eq_witness]
  · exact (hasCompactSupport_archFactor F ha hβ₁A hβ₂a).mul_left

omit [NumberField F] in

private
theorem archComponent_inv_incl_mul_self (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion)
    (y : GL (Fin 2) (InfiniteAdeleRing F)) :
    archComponent F w ((archRowIsometryInclAt₀ F w k)⁻¹ * y)
      = ((k : GL (Fin 2) w.Completion))⁻¹ * archComponent F w y := by
  rw [map_mul, map_inv]
  exact congrArg (· * _) (congrArg (·⁻¹) (archComponent_archGLIncl_self F w _))

omit [NumberField F] in
private
theorem archComponent_inv_incl_mul_of_ne {v w : InfinitePlace F} (hvw : v ≠ w) (k : rowIsometrySubgroup₀ w.Completion)
    (y : GL (Fin 2) (InfiniteAdeleRing F)) :
    archComponent F v ((archRowIsometryInclAt₀ F w k)⁻¹ * y) = archComponent F v y := by
  rw [map_mul, map_inv]
  have h : archComponent F v (archRowIsometryInclAt₀ F w k) = 1 := archComponent_archGLIncl_of_ne F hvw _
  rw [h, inv_one, one_mul]

omit [NumberField F] in
private
theorem archComponent_conj_self (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion)
    (y : GL (Fin 2) (InfiniteAdeleRing F)) :
    archComponent F w (archRowIsometryInclAt₀ F w k * y * (archRowIsometryInclAt₀ F w k)⁻¹)
      = (k : GL (Fin 2) w.Completion) * archComponent F w y * ((k : GL (Fin 2) w.Completion))⁻¹ := by
  rw [map_mul, map_mul, map_inv]
  have h : archComponent F w (archRowIsometryInclAt₀ F w k) = (k : GL (Fin 2) w.Completion) :=
    archComponent_archGLIncl_self F w _
  rw [h]

omit [NumberField F] in
private
theorem archComponent_conj_of_ne {v w : InfinitePlace F} (hvw : v ≠ w) (k : rowIsometrySubgroup₀ w.Completion)
    (y : GL (Fin 2) (InfiniteAdeleRing F)) :
    archComponent F v (archRowIsometryInclAt₀ F w k * y * (archRowIsometryInclAt₀ F w k)⁻¹) = archComponent F v y := by
  rw [map_mul, map_mul, map_inv]
  have h : archComponent F v (archRowIsometryInclAt₀ F w k) = 1 := archComponent_archGLIncl_of_ne F hvw _
  rw [h, inv_one, one_mul, mul_one]

private
theorem archFactor_inv_incl_mul (β₁ β₂ : ℝ → ℝ) (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion)
    (y : GL (Fin 2) (InfiniteAdeleRing F)) :
    archFactor F β₁ β₂ ((archRowIsometryInclAt₀ F w k)⁻¹ * y) = archFactor F β₁ β₂ y := by
  unfold archFactor
  refine Fintype.prod_congr _ _ fun v => ?_
  by_cases hvw : v = w
  · subst hvw
    rw [archComponent_inv_incl_mul_self, Units.val_mul, localBump_mul_of_mem β₁ β₂ (inv_mem k.2)]
  · rw [archComponent_inv_incl_mul_of_ne F hvw]

private
theorem archFactor_conj (β₁ β₂ : ℝ → ℝ) (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion)
    (y : GL (Fin 2) (InfiniteAdeleRing F)) :
    archFactor F β₁ β₂ (archRowIsometryInclAt₀ F w k * y * (archRowIsometryInclAt₀ F w k)⁻¹)
      = archFactor F β₁ β₂ y := by
  unfold archFactor
  refine Fintype.prod_congr _ _ fun v => ?_
  by_cases hvw : v = w
  · subst hvw
    rw [archComponent_conj_self, Units.val_mul, Units.val_mul, localBump_mul_of_mem' β₁ β₂ _ (inv_mem k.2),
      localBump_mul_of_mem β₁ β₂ k.2]
  · rw [archComponent_conj_of_ne F hvw]

private
theorem dispArch_conj (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion)
    (y : GL (Fin 2) (InfiniteAdeleRing F)) :
    dispArch F (archRowIsometryInclAt₀ F w k * y * (archRowIsometryInclAt₀ F w k)⁻¹) = dispArch F y := by
  unfold dispArch
  congr 1
  refine Fintype.sum_congr _ _ fun v => ?_
  by_cases hvw : v = w
  · subst hvw
    rw [archComponent_conj_self, Units.val_mul, Units.val_mul, entrySq_conj_sub_one k.2]
  · rw [archComponent_conj_of_ne F hvw]

private
theorem kernelFactor_conj (R : ℂ) (m : ℕ) (β₁ β₂ : ℝ → ℝ) (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion)
    (y : GL (Fin 2) (InfiniteAdeleRing F)) :
    kernelFactor F R m β₁ β₂ (archRowIsometryInclAt₀ F w k * y * (archRowIsometryInclAt₀ F w k)⁻¹)
      = kernelFactor F R m β₁ β₂ y := by
  rw [kernelFactor_apply, kernelFactor_apply, dispArch_conj, archFactor_conj]

end Kernel

end IsotypicArchCut

namespace IsotypicArchCut
namespace FiniteFactor

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum AutomorphicForm
open NumberField.AdelicLevel LocalGL2 HeckeIntegralSeam AdelicDock

variable (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

private theorem mem_U_of_components {N : Ideal (𝓞 F)} {h : GL (Fin 2) (AdeleRing (𝓞 F) F)}
    (harch : glArch (𝓞 F) F h = 1)
    (hfin : ∀ w : HeightOneSpectrum (𝓞 F),
      finComponent (𝓞 F) F w (glFin (𝓞 F) F h) ∈ localLevelOne (𝓞 F) F w N) :
    h ∈ levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F := by
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · rw [mem_levelOne_iff, mem_finiteLevelOne_iff]
    have hlocal : ∀ w, IsLocalLevelOne (𝓞 F) F w N
          (finComponent (𝓞 F) F w (glFin (𝓞 F) F h) : Matrix (Fin 2) (Fin 2) _)
        ∧ IsLocalLevelOne (𝓞 F) F w N
          ((finComponent (𝓞 F) F w (glFin (𝓞 F) F h))⁻¹ : GL (Fin 2) _) := by
      intro w
      exact (mem_localLevelOne_iff (𝓞 F) F w (finComponent (𝓞 F) F w (glFin (𝓞 F) F h))).mp
        (hfin w)
    constructor
    · exact ⟨⟨fun i j w => (hlocal w).1.integral i j, fun w => (hlocal w).1.lowerLeft⟩,
        fun w => by
          rw [AdelicLevel.coe_sub_apply, AdelicLevel.coe_one_apply]
          exact (hlocal w).1.lowerRight⟩
    · refine ⟨⟨fun i j w => ?_, fun w => ?_⟩, fun w => ?_⟩
      · have := (hlocal w).2.integral i j
        rwa [← map_inv] at this
      · have := (hlocal w).2.lowerLeft
        rwa [← map_inv] at this
      · rw [AdelicLevel.coe_sub_apply, AdelicLevel.coe_one_apply]
        have := (hlocal w).2.lowerRight
        rwa [← map_inv] at this
  · exact (mem_finiteAdelicGL2Subgroup_iff F h).mpr harch

private theorem components_of_mem_U {N : Ideal (𝓞 F)} {h : GL (Fin 2) (AdeleRing (𝓞 F) F)}
    (hh : h ∈ levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) :
    glArch (𝓞 F) F h = 1 ∧ ∀ w : HeightOneSpectrum (𝓞 F),
      finComponent (𝓞 F) F w (glFin (𝓞 F) F h) ∈ localLevelOne (𝓞 F) F w N := by
  obtain ⟨h1, h2⟩ := Subgroup.mem_inf.mp hh
  refine ⟨(mem_finiteAdelicGL2Subgroup_iff F h).mp h2, fun w => ?_⟩
  rw [mem_levelOne_iff, mem_finiteLevelOne_iff] at h1
  rw [mem_localLevelOne_iff]
  obtain ⟨ha, hb⟩ := h1
  constructor
  · exact ⟨fun i j => ha.integral i j w, ha.lowerLeft w, by
      have := ha.lowerRight w
      rwa [AdelicLevel.coe_sub_apply, AdelicLevel.coe_one_apply] at this⟩
  · rw [← map_inv]
    exact ⟨fun i j => hb.integral i j w, hb.lowerLeft w, by
      have := hb.lowerRight w
      rwa [AdelicLevel.coe_sub_apply, AdelicLevel.coe_one_apply] at this⟩

private theorem comp_self (z : GL (Fin 2) (v.adicCompletion F)) :
    finComponent (𝓞 F) F v (glFin (𝓞 F) F (finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v z))) = z := by
  rw [glFin_finEmbed, finComponent_localEmbed_self]

private theorem comp_of_ne (z : GL (Fin 2) (v.adicCompletion F)) {w : HeightOneSpectrum (𝓞 F)}
    (hw : w ≠ v) :
    finComponent (𝓞 F) F w (glFin (𝓞 F) F (finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v z))) = 1 := by
  rw [glFin_finEmbed, finComponent_localEmbed_of_ne _ _ _ _ hw]

omit [NumberField F] in
private theorem ne_bot_of_not_dvd {N : Ideal (𝓞 F)} (hv : ¬ v.asIdeal ∣ N) : N ≠ ⊥ := by
  rintro rfl
  exact hv (dvd_zero _)

private theorem isLocalLevelOne_of_integral {N : Ideal (𝓞 F)} (hv : ¬ v.asIdeal ∣ N)
    {m : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)}
    (hm : ∀ i j, m i j ∈ v.adicCompletionIntegers F) : IsLocalLevelOne (𝓞 F) F v N m := by
  have hb : idealBound (𝓞 F) N v = 1 := idealBound_eq_one_of_not_dvd (ne_bot_of_not_dvd F v hv) hv
  refine ⟨hm, ?_, ?_⟩
  · rw [hb]
    exact (mem_adicCompletionIntegers _ _ _).mp (hm 1 0)
  · rw [hb]
    exact (mem_adicCompletionIntegers _ _ _).mp (sub_mem (hm 1 1) (one_mem _))

private theorem mem_localLevelOne_of_integral {N : Ideal (𝓞 F)} (hv : ¬ v.asIdeal ∣ N)
    {k : GL (Fin 2) (v.adicCompletion F)}
    (hk : ∀ i j, (k : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j ∈ v.adicCompletionIntegers F)
    (hk' : ∀ i j, ((k⁻¹ : GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F))
      i j ∈ v.adicCompletionIntegers F) :
    k ∈ localLevelOne (𝓞 F) F v N := by
  rw [mem_localLevelOne_iff]
  exact ⟨isLocalLevelOne_of_integral F v hv hk, isLocalLevelOne_of_integral F v hv hk'⟩

private noncomputable abbrev wc (w : HeightOneSpectrum (𝓞 F)) : GL (Fin 2) (w.adicCompletion F) :=
  finComponent (𝓞 F) F w (glFin (𝓞 F) F (weyl (𝓞 F) F))

private theorem weyl_mul_self : weyl (𝓞 F) F * weyl (𝓞 F) F = 1 :=
  Units.ext (by simp [weyl, Matrix.one_fin_two])

private theorem wc_mul_self (w : HeightOneSpectrum (𝓞 F)) : wc F w * wc F w = 1 := by
  simp only [wc, ← map_mul, weyl_mul_self, map_one]

private theorem weyl_entry_mem (w : HeightOneSpectrum (𝓞 F)) (i j : Fin 2) :
    (wc F w : Matrix (Fin 2) (Fin 2) (w.adicCompletion F)) i j ∈ w.adicCompletionIntegers F := by
  rw [finComponent_apply, glFin_apply]
  fin_cases i <;> fin_cases j <;> simp [weyl] <;>
    first
      | exact zero_mem_integralFiniteAdeles w
      | exact one_mem_integralFiniteAdeles w

private theorem wc_mem {N : Ideal (𝓞 F)} {w : HeightOneSpectrum (𝓞 F)} (hw : ¬ w.asIdeal ∣ N) :
    wc F w ∈ localLevelOne (𝓞 F) F w N := by
  refine mem_localLevelOne_of_integral F w hw (weyl_entry_mem F w) fun i j => ?_
  rw [inv_eq_of_mul_eq_one_right (wc_mul_self F w)]
  exact weyl_entry_mem F w i j

private theorem comp_conj (w : HeightOneSpectrum (𝓞 F)) (h : GL (Fin 2) (AdeleRing (𝓞 F) F)) :
    finComponent (𝓞 F) F w (glFin (𝓞 F) F ((weyl (𝓞 F) F)⁻¹ * h * weyl (𝓞 F) F))
      = (wc F w)⁻¹ * finComponent (𝓞 F) F w (glFin (𝓞 F) F h) * wc F w := by
  simp only [wc, map_mul, map_inv]

private theorem isOpen_setOf_isLocalLevelOne {N : Ideal (𝓞 F)} (hN : N ≠ ⊥) {X : Type*} [TopologicalSpace X]
    {φ : X → Matrix (Fin 2) (Fin 2) (v.adicCompletion F)} (hφ : Continuous φ) :
    IsOpen {x | IsLocalLevelOne (𝓞 F) F v N (φ x)} := by
  have hO : IsOpen (v.adicCompletionIntegers F : Set (v.adicCompletion F)) :=
    (AdelicHaar.fact_isOpen_adicCompletionIntegers (𝓞 F) F).out v
  have hB : IsOpen {y : v.adicCompletion F | Valued.v y ≤ idealBound (𝓞 F) N v} :=
    isOpen_setOf_valued_le_idealBound (R := 𝓞 F) (K := F) (v := v) hN
  have hset : {x | IsLocalLevelOne (𝓞 F) F v N (φ x)} =
      (⋂ i : Fin 2, ⋂ j : Fin 2, (fun x => φ x i j) ⁻¹' (v.adicCompletionIntegers F : Set (v.adicCompletion F))) ∩
        ((fun x => φ x 1 0) ⁻¹' {y | Valued.v y ≤ idealBound (𝓞 F) N v} ∩
          (fun x => φ x 1 1 - 1) ⁻¹' {y | Valued.v y ≤ idealBound (𝓞 F) N v}) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]
    exact ⟨fun h => ⟨h.integral, h.lowerLeft, h.lowerRight⟩, fun h => ⟨h.1, h.2.1, h.2.2⟩⟩
  rw [hset]
  refine (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => hO.preimage (hφ.matrix_elem i j)).inter
    ((hB.preimage (hφ.matrix_elem 1 0)).inter (hB.preimage ((hφ.matrix_elem 1 1).sub continuous_const)))

private theorem isOpen_localLevelOne {N : Ideal (𝓞 F)} (hN : N ≠ ⊥) :
    IsOpen (localLevelOne (𝓞 F) F v N : Set (GL (Fin 2) (v.adicCompletion F))) := by
  have hset : (localLevelOne (𝓞 F) F v N : Set (GL (Fin 2) (v.adicCompletion F))) =
      {k : GL (Fin 2) (v.adicCompletion F) |
          IsLocalLevelOne (𝓞 F) F v N (k : Matrix (Fin 2) (Fin 2) (v.adicCompletion F))} ∩
        {k : GL (Fin 2) (v.adicCompletion F) |
          IsLocalLevelOne (𝓞 F) F v N ((k⁻¹ : GL (Fin 2) (v.adicCompletion F)) : Matrix _ _ _)} := by
    ext k
    exact mem_localLevelOne_iff (𝓞 F) F v k
  rw [hset]
  exact (isOpen_setOf_isLocalLevelOne F v hN Units.continuous_val).inter
    (isOpen_setOf_isLocalLevelOne F v hN Units.continuous_coe_inv)

private theorem isClosed_localLevelOne {N : Ideal (𝓞 F)} (hN : N ≠ ⊥) :
    IsClosed (localLevelOne (𝓞 F) F v N : Set (GL (Fin 2) (v.adicCompletion F))) :=
  (localLevelOne (𝓞 F) F v N).isClosed_of_isOpen (isOpen_localLevelOne F v hN)

private theorem mem_localIntegralSet_of_mem {N : Ideal (𝓞 F)} {k : GL (Fin 2) (v.adicCompletion F)}
    (hk : k ∈ localLevelOne (𝓞 F) F v N) : k ∈ localIntegralSet F v := by
  obtain ⟨h1, h2⟩ := (mem_localLevelOne_iff (𝓞 F) F v k).mp hk
  exact (mem_localIntegralSet F v).mpr ⟨h1.integral, h2.integral⟩

private def localPrincipal (N : Ideal (𝓞 F)) : Set (GL (Fin 2) (v.adicCompletion F)) :=
  {k | k ∈ localLevelOne (𝓞 F) F v N ∧ (wc F v)⁻¹ * k * wc F v ∈ localLevelOne (𝓞 F) F v N}

private theorem _root_.IsotypicArchCut.FiniteFactor.continuous_conj : Continuous fun k : GL (Fin 2) (v.adicCompletion F) => (wc F v)⁻¹ * k * wc F v :=
  (continuous_const.mul continuous_id).mul continuous_const

p2m_export "IsotypicArchCut.FiniteFactor" "continuous_conj"
private theorem isOpen_localPrincipal {N : Ideal (𝓞 F)} (hN : N ≠ ⊥) : IsOpen (localPrincipal F v N) :=
  (isOpen_localLevelOne F v hN).inter ((isOpen_localLevelOne F v hN).preimage (continuous_conj F v))

private theorem isClosed_localPrincipal {N : Ideal (𝓞 F)} (hN : N ≠ ⊥) : IsClosed (localPrincipal F v N) :=
  (isClosed_localLevelOne F v hN).inter ((isClosed_localLevelOne F v hN).preimage (continuous_conj F v))

private theorem isCompact_localPrincipal {N : Ideal (𝓞 F)} (hN : N ≠ ⊥) : IsCompact (localPrincipal F v N) :=
  (isCompact_localIntegralSet F v).of_isClosed_subset (isClosed_localPrincipal F v hN)
    fun _ hk => mem_localIntegralSet_of_mem F v hk.1

private theorem mem_localPrincipal_of_integral {N : Ideal (𝓞 F)} (hv : ¬ v.asIdeal ∣ N)
    {k : GL (Fin 2) (v.adicCompletion F)} (hk : k ∈ localIntegralSet F v) : k ∈ localPrincipal F v N := by
  obtain ⟨hk1, hk2⟩ := (mem_localIntegralSet F v).mp hk
  refine ⟨mem_localLevelOne_of_integral F v hv hk1 hk2, ?_⟩
  exact mul_mem (mul_mem (inv_mem (wc_mem F hv)) (mem_localLevelOne_of_integral F v hv hk1 hk2)) (wc_mem F hv)

private theorem isLocalTestFn_indicator_localPrincipal {N : Ideal (𝓞 F)} (hN : N ≠ ⊥) :
    IsLocalTestFn F v ((localPrincipal F v N).indicator fun _ => (1 : ℂ)) :=
  ⟨isLocallyConstant_indicator_one (isOpen_localPrincipal F v hN) (isClosed_localPrincipal F v hN),
    HasCompactSupport.intro (isCompact_localPrincipal F v hN) fun _ hg => by simp [hg]⟩

private noncomputable abbrev wf : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) := glFin (𝓞 F) F (weyl (𝓞 F) F)

private theorem wc_eq (w : HeightOneSpectrum (𝓞 F)) : wc F w = finComponent (𝓞 F) F w (wf F) := rfl

private noncomputable def finPrincipal (N : Ideal (𝓞 F)) : Subgroup (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :=
  finiteLevelOne (𝓞 F) F N ⊓ (finiteLevelOne (𝓞 F) F N).comap (MulAut.conj (wf F)⁻¹).toMonoidHom

private theorem mem_finPrincipal_iff {N : Ideal (𝓞 F)} {h : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)} :
    h ∈ finPrincipal F N ↔
      h ∈ finiteLevelOne (𝓞 F) F N ∧ (wf F)⁻¹ * h * wf F ∈ finiteLevelOne (𝓞 F) F N := by
  simp only [finPrincipal, Subgroup.mem_inf, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
    inv_inv]

private theorem continuous_finConj :
    Continuous fun h : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) => (wf F)⁻¹ * h * wf F :=
  (continuous_const.mul continuous_id).mul continuous_const

private theorem finPrincipal_eq (N : Ideal (𝓞 F)) :
    (finPrincipal F N : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F))) =
      (finiteLevelOne (𝓞 F) F N : Set _) ∩
        (fun h => (wf F)⁻¹ * h * wf F) ⁻¹' (finiteLevelOne (𝓞 F) F N : Set _) := by
  ext h
  exact mem_finPrincipal_iff F

private theorem isOpen_finPrincipal {N : Ideal (𝓞 F)} (hN : N ≠ ⊥) :
    IsOpen (finPrincipal F N : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F))) := by
  rw [finPrincipal_eq]
  exact (isOpen_finiteLevelOne (R := 𝓞 F) (K := F) (N := N) hN).inter
    ((isOpen_finiteLevelOne (R := 𝓞 F) (K := F) (N := N) hN).preimage (continuous_finConj F))

private theorem isClosed_finPrincipal (N : Ideal (𝓞 F)) :
    IsClosed (finPrincipal F N : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F))) := by
  rw [finPrincipal_eq]
  exact (isClosed_finiteLevelOne (R := 𝓞 F) (K := F) (N := N)).inter
    ((isClosed_finiteLevelOne (R := 𝓞 F) (K := F) (N := N)).preimage (continuous_finConj F))

private theorem isCompact_finPrincipal (N : Ideal (𝓞 F)) :
    IsCompact (finPrincipal F N : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F))) :=
  (isCompact_finiteLevelOne (R := 𝓞 F) (K := F) (N := N)).of_isClosed_subset (isClosed_finPrincipal F N)
    fun _ hh => ((mem_finPrincipal_iff F).mp hh).1

private theorem isFinTestFactor_indicator_finPrincipal {N : Ideal (𝓞 F)} (hN : N ≠ ⊥) :
    IsFinTestFactor F ((finPrincipal F N : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F))).indicator fun _ => (1 : ℂ)) :=
  ⟨isLocallyConstant_indicator_one (isOpen_finPrincipal F hN) (isClosed_finPrincipal F N),
    HasCompactSupport.intro (isCompact_finPrincipal F N) fun _ hg => by simp [hg]⟩

private theorem mem_principalLevel_iff_glFin {N : Ideal (𝓞 F)} (g : GL (Fin 2) (AdeleRing (𝓞 F) F)) :
    g ∈ principalLevel (𝓞 F) F N ↔ glFin (𝓞 F) F g ∈ finPrincipal F N := by
  rw [mem_principalLevel_iff, mem_finPrincipal_iff, mem_levelOne_iff, Subgroup.mem_map_equiv]
  simp only [MulAut.conj_symm_apply, mem_levelOne_iff, map_mul, map_inv]

private theorem mem_finiteLevelOne_iff_components {N : Ideal (𝓞 F)} (h : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
    h ∈ finiteLevelOne (𝓞 F) F N ↔
      ∀ w : HeightOneSpectrum (𝓞 F), finComponent (𝓞 F) F w h ∈ localLevelOne (𝓞 F) F w N := by
  constructor
  · intro hh w
    have hU : finEmbed (𝓞 F) F h ∈ levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F :=
      Subgroup.mem_inf.mpr ⟨(finEmbed_mem_levelOne_iff (𝓞 F) F h).mpr hh,
        (mem_finiteAdelicGL2Subgroup_iff F _).mpr (glArch_finEmbed (𝓞 F) F h)⟩
    have := (components_of_mem_U F hU).2 w
    rwa [glFin_finEmbed] at this
  · intro hw
    have hU : finEmbed (𝓞 F) F h ∈ levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F :=
      mem_U_of_components F (glArch_finEmbed (𝓞 F) F h) fun w => by rw [glFin_finEmbed]; exact hw w
    exact (finEmbed_mem_levelOne_iff (𝓞 F) F h).mp (Subgroup.mem_inf.mp hU).1

private theorem mem_finPrincipal_iff_components {N : Ideal (𝓞 F)} (h : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
    h ∈ finPrincipal F N ↔ ∀ w : HeightOneSpectrum (𝓞 F), finComponent (𝓞 F) F w h ∈ localPrincipal F w N := by
  rw [mem_finPrincipal_iff, mem_finiteLevelOne_iff_components, mem_finiteLevelOne_iff_components]
  simp only [map_mul, map_inv, ← wc_eq]
  exact ⟨fun hh w => ⟨hh.1 w, hh.2 w⟩, fun hh => ⟨fun w => (hh w).1, fun w => (hh w).2⟩⟩

private noncomputable def ff (N : Ideal (𝓞 F)) : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) → ℂ :=
  (finPrincipal F N : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F))).indicator fun _ => (1 : ℂ)

private theorem ff_mul_left {N : Ideal (𝓞 F)} {x : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)} (hx : x ∈ finPrincipal F N)
    (h : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) : ff F N (x * h) = ff F N h := by
  unfold ff
  by_cases hh : h ∈ finPrincipal F N
  · rw [Set.indicator_of_mem (mul_mem hx hh : x * h ∈ finPrincipal F N), Set.indicator_of_mem hh]
  · have hxh : x * h ∉ finPrincipal F N := fun hm => hh ((Subgroup.mul_mem_cancel_left _ hx).mp hm)
    rw [Set.indicator_of_notMem hxh, Set.indicator_of_notMem hh]

private theorem ff_eq_prod {N : Ideal (𝓞 F)} {S : Finset (HeightOneSpectrum (𝓞 F))}
    (hNS : ∀ w : HeightOneSpectrum (𝓞 F), w.asIdeal ∣ N → w ∈ S) (h : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F))
    (hS : ∀ w ∉ S, finComponent (𝓞 F) F w h ∈ localIntegralSet F w) :
    ff F N h = ∏ w ∈ S, (localPrincipal F w N).indicator (fun _ => (1 : ℂ)) (finComponent (𝓞 F) F w h) := by
  unfold ff
  by_cases hh : h ∈ finPrincipal F N
  · rw [Set.indicator_of_mem hh]
    have hw := (mem_finPrincipal_iff_components F h).mp hh
    exact (Finset.prod_eq_one fun w _ => Set.indicator_of_mem (hw w) _).symm
  · rw [Set.indicator_of_notMem hh]
    obtain ⟨w, hw⟩ : ∃ w, finComponent (𝓞 F) F w h ∉ localPrincipal F w N := by
      by_contra hcon
      exact hh ((mem_finPrincipal_iff_components F h).mpr fun w => not_not.mp (not_exists.mp hcon w))
    have hwS : w ∈ S := by
      by_contra hwS
      have hdvd : ¬ w.asIdeal ∣ N := fun hd => hwS (hNS w hd)
      exact hw (mem_localPrincipal_of_integral F w hdvd (hS w hwS))
    exact (Finset.prod_eq_zero hwS (Set.indicator_of_notMem hw _)).symm

private theorem ff_eq_zero {N : Ideal (𝓞 F)} {S : Finset (HeightOneSpectrum (𝓞 F))}
    (h : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F))
    (hS : ∃ w ∉ S, finComponent (𝓞 F) F w h ∉ localIntegralSet F w) : ff F N h = 0 := by
  obtain ⟨w, -, hw⟩ := hS
  have hnot : h ∉ finPrincipal F N := fun hh =>
    hw (mem_localIntegralSet_of_mem F w (((mem_finPrincipal_iff_components F h).mp hh w).1))
  exact Set.indicator_of_notMem hnot _

private noncomputable def testFn (fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ) (N : Ideal (𝓞 F))
    (g : GL (Fin 2) (AdeleRing (𝓞 F) F)) : ℂ :=
  fa (glArch (𝓞 F) F g) * ff F N (glFin (𝓞 F) F g)

private theorem isUnitFactorizableAt_testFn {fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ} (hfa : IsArchTestFactor F fa)
    {N : Ideal (𝓞 F)} (hN : N ≠ ⊥) {S : Finset (HeightOneSpectrum (𝓞 F))}
    (hNS : ∀ w : HeightOneSpectrum (𝓞 F), w.asIdeal ∣ N → w ∈ S) :
    IsUnitFactorizableAt F ⊥ S (testFn F fa N) :=
  ⟨isBiInvariantUnder_bot F _, fa, ff F N, fun w => (localPrincipal F w N).indicator fun _ => (1 : ℂ), hfa,
    isFinTestFactor_indicator_finPrincipal F hN, fun w _ => isLocalTestFn_indicator_localPrincipal F w hN,
    fun h hS => ff_eq_prod F hNS h hS, fun h hS => ff_eq_zero F h hS, fun _ => rfl⟩

private theorem testFn_mul_left (fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ) (N : Ideal (𝓞 F)) :
    ∀ x ∈ principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F, ∀ g : GL (Fin 2) (AdeleRing (𝓞 F) F),
      testFn F fa N (x * g) = testFn F fa N g := by
  intro x hx g
  obtain ⟨hxP, hxfin⟩ := Subgroup.mem_inf.mp hx
  unfold testFn
  rw [map_mul, map_mul, (mem_finiteAdelicGL2Subgroup_iff F x).mp hxfin, one_mul,
    ff_mul_left F ((mem_principalLevel_iff_glFin F x).mp hxP)]

private theorem exists_notMem (SK : Finset (HeightOneSpectrum (𝓞 F))) :
    ∃ w : HeightOneSpectrum (𝓞 F), w ∉ SK := by
  have key : ∀ p : Nat.Primes, ∃ w : HeightOneSpectrum (𝓞 F),
      w.asIdeal.comap (algebraMap ℤ (𝓞 F)) = Ideal.span {((p : ℕ) : ℤ)} := by
    intro p
    have hp : Prime ((p : ℕ) : ℤ) := Nat.prime_iff_prime_int.mp p.2
    haveI : (Ideal.span {((p : ℕ) : ℤ)}).IsPrime := (Ideal.span_singleton_prime hp.ne_zero).mpr hp
    obtain ⟨Q, -, hQ, hQc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (Ideal.span {((p : ℕ) : ℤ)})
      (⊥ : Ideal (𝓞 F)) (Ideal.comap_bot_le_of_injective _ (algebraMap ℤ (𝓞 F)).injective_int)
    have hQ0 : Q ≠ ⊥ := by
      rintro rfl
      rw [Ideal.comap_bot_of_injective _ (algebraMap ℤ (𝓞 F)).injective_int] at hQc
      exact hp.ne_zero (Ideal.span_singleton_eq_bot.mp hQc.symm)
    exact ⟨⟨Q, hQ, hQ0⟩, hQc⟩
  choose f hf using key
  have hinj : Function.Injective f := by
    intro p q hpq
    have h := hf p
    rw [hpq, hf q] at h
    have h' := Int.associated_iff_natAbs.mp (Ideal.span_singleton_eq_span_singleton.mp h)
    exact Subtype.ext (by simpa using h'.symm)
  haveI : Infinite (HeightOneSpectrum (𝓞 F)) := Infinite.of_injective f hinj
  exact Infinite.exists_notMem_finset SK

private theorem ne_bot_of_forall_dvd_mem {N : Ideal (𝓞 F)} {S : Finset (HeightOneSpectrum (𝓞 F))}
    (hNS : ∀ w : HeightOneSpectrum (𝓞 F), w.asIdeal ∣ N → w ∈ S) : N ≠ ⊥ := by
  rintro rfl
  obtain ⟨w, hw⟩ := exists_notMem F S
  exact hw (hNS w (dvd_zero _))

end IsotypicArchCut.FiniteFactor

namespace IsotypicArchCut
namespace ConjugationInvariance

open AutomorphicForm AutomorphicForm.WindowedSiegel Matrix NumberField NumberField.AdelicLevel IsDedekindDomain

section Arch

variable (F : Type) [Field F] [NumberField F]

private
theorem tensor_conj {fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ}
    (hfa : ∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion) (y : GL (Fin 2) (InfiniteAdeleRing F)),
      fa (archRowIsometryInclAt₀ F w k * y * (archRowIsometryInclAt₀ F w k)⁻¹) = fa y)
    (ffn : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) → ℂ) :
    ∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion) (y : AdelicGL2 (𝓞 F) F),
      fa (glArch (𝓞 F) F (rowIsometryInclAt₀ F w k * y * (rowIsometryInclAt₀ F w k)⁻¹)) *
          ffn (glFin (𝓞 F) F (rowIsometryInclAt₀ F w k * y * (rowIsometryInclAt₀ F w k)⁻¹))
        = fa (glArch (𝓞 F) F y) * ffn (glFin (𝓞 F) F y) := by
  intro w k y
  rw [map_mul, map_mul, map_inv, glArch_rowIsometryInclAt₀, hfa, map_mul, map_mul, map_inv,
    glFin_rowIsometryInclAt₀, one_mul, inv_one, mul_one]

end Arch

end IsotypicArchCut.ConjugationInvariance

namespace IsotypicArchCut
namespace CutStep

open AutomorphicForm IsDedekindDomain NumberField

section Generic

variable {H G : Type*} [Group H] [Group G]

private
def rightTranslate (ι : H →* G) (k : H) : (G → ℂ) →ₗ[ℂ] (G → ℂ) where
  toFun f := fun x => f (x * ι k)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private
theorem rightTranslate_apply (ι : H →* G) (k : H) (f : G → ℂ) (x : G) :
    rightTranslate ι k f x = f (x * ι k) :=
  rfl

private
def stableRep (ι : H →* G) (V : Submodule ℂ (G → ℂ))
    (hV : ∀ (k : H), ∀ f ∈ V, (fun x => f (x * ι k)) ∈ V) : Representation ℂ H V where
  toFun k := (rightTranslate ι k).restrict fun f hf => hV k f hf
  map_one' := by
    refine LinearMap.ext fun v => Subtype.ext (funext fun x => ?_)
    simp only [LinearMap.coe_restrict_apply, rightTranslate_apply, map_one, mul_one, Module.End.one_apply]
  map_mul' k₁ k₂ := by
    refine LinearMap.ext fun v => Subtype.ext (funext fun x => ?_)
    simp only [LinearMap.coe_restrict_apply, rightTranslate_apply, map_mul, mul_assoc, Module.End.mul_apply]

private
theorem stableRep_apply_coe (ι : H →* G) (V : Submodule ℂ (G → ℂ))
    (hV : ∀ (k : H), ∀ f ∈ V, (fun x => f (x * ι k)) ∈ V) (k : H) (v : V) (x : G) :
    (stableRep ι V hV k v : G → ℂ) x = (v : G → ℂ) (x * ι k) :=
  rfl

private
noncomputable def finRep (ι : H →* G) (V : Submodule ℂ (G → ℂ)) [FiniteDimensional ℂ V]
    (hV : ∀ (k : H), ∀ f ∈ V, (fun x => f (x * ι k)) ∈ V) :
    Representation ℂ H (Fin (Module.finrank ℂ V) → ℂ) where
  toFun k := (Module.finBasis ℂ V).equivFun.conj (stableRep ι V hV k)
  map_one' := by
    rw [map_one, Module.End.one_eq_id, LinearEquiv.conj_id, Module.End.one_eq_id]
  map_mul' k₁ k₂ := by
    rw [map_mul, Module.End.mul_eq_comp, LinearEquiv.conj_comp, Module.End.mul_eq_comp]

private
noncomputable def finIntertwiner (V : Submodule ℂ (G → ℂ)) [FiniteDimensional ℂ V] :
    (Fin (Module.finrank ℂ V) → ℂ) →ₗ[ℂ] (G → ℂ) :=
  V.subtype ∘ₗ ((Module.finBasis ℂ V).equivFun.symm : (Fin (Module.finrank ℂ V) → ℂ) →ₗ[ℂ] V)

omit [Group G] in
private
theorem finIntertwiner_apply (V : Submodule ℂ (G → ℂ)) [FiniteDimensional ℂ V]
    (c : Fin (Module.finrank ℂ V) → ℂ) :
    finIntertwiner V c = ((Module.finBasis ℂ V).equivFun.symm c : G → ℂ) :=
  rfl

private
theorem isRightEquivariant_finIntertwiner (ι : H →* G) (V : Submodule ℂ (G → ℂ)) [FiniteDimensional ℂ V]
    (hV : ∀ (k : H), ∀ f ∈ V, (fun x => f (x * ι k)) ∈ V) :
    IsRightEquivariant ι (finRep ι V hV) (finIntertwiner V) := by
  intro k c x
  rw [finIntertwiner_apply, finIntertwiner_apply]
  show (((Module.finBasis ℂ V).equivFun.symm
      ((Module.finBasis ℂ V).equivFun.conj (stableRep ι V hV k) c)) : G → ℂ) x = _
  rw [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  exact stableRep_apply_coe ι V hV k _ x

private
theorem exists_mem_typeSubmodule_of_finite_stable (ι : H →* G) (V : Submodule ℂ (G → ℂ))
    [FiniteDimensional ℂ V] (hV : ∀ (k : H), ∀ f ∈ V, (fun x => f (x * ι k)) ∈ V) {f : G → ℂ}
    (hf : f ∈ V) :
    ∃ (n : ℕ) (ρ : Representation ℂ H (Fin n → ℂ)), f ∈ typeSubmodule ι ρ := by
  refine ⟨Module.finrank ℂ V, finRep ι V hV, ?_⟩
  have hmem := mem_typeSubmodule_of_isRightEquivariant (isRightEquivariant_finIntertwiner ι V hV)
    ((Module.finBasis ℂ V).equivFun ⟨f, hf⟩)
  rwa [finIntertwiner_apply, LinearEquiv.symm_apply_apply] at hmem

end Generic

section Arch

variable (F : Type) [Field F] [NumberField F]

private
theorem exists_mem_archTypeSubmoduleAt_of_finite_stable (w : InfinitePlace F)
    (V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) [FiniteDimensional ℂ V]
    (hV : ∀ (k : rowIsometrySubgroup₀ w.Completion), ∀ f ∈ V, (fun x => f (x * rowIsometryInclAt₀ F w k)) ∈ V)
    {u : AdelicGL2 (𝓞 F) F → ℂ} (hu : u ∈ V) :
    ∃ τ : ArchRepAt F w, u ∈ archTypeSubmoduleAt F w τ := by
  obtain ⟨n, ρ, h⟩ := exists_mem_typeSubmodule_of_finite_stable (rowIsometryInclAt₀ F w) V hV hu
  exact ⟨⟨n, ρ⟩, h⟩

private
theorem exists_mem_archCutSubmodule_of_forall_exists (u : AdelicGL2 (𝓞 F) F → ℂ)
    (h : ∀ w : InfinitePlace F, ∃ τ : ArchRepAt F w, u ∈ archTypeSubmoduleAt F w τ) :
    ∃ tys : ArchTypeFamily F, u ∈ archCutSubmodule F tys := by
  choose τ hτ using h
  refine ⟨⟨fun _ => 1, fun w _ => τ w⟩, (mem_archCutSubmodule_iff F _ u).mpr fun w => ?_⟩
  exact Submodule.mem_iSup_of_mem (0 : Fin 1) (hτ w)

private
theorem rightConv_mul_right (φ f : AdelicGL2 (𝓞 F) F → ℂ) (h g : AdelicGL2 (𝓞 F) F) :
    rightConv F φ f (g * h) = rightConv F φ (fun y => f (h⁻¹ * y)) g := by
  letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := AdelicHaar.glBorel (Fin 2) (𝓞 F) F
  haveI : BorelSpace (AdelicGL2 (𝓞 F) F) := AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 F) F
  haveI : (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F).IsHaarMeasure :=
    AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  rw [rightConv_apply, rightConv_apply]
  have key : (fun x => φ (g * h * x) * f x) =
      fun x => (fun y => φ (g * y) * f (h⁻¹ * y)) (h * x) := by
    funext x
    simp only [mul_assoc, inv_mul_cancel_left]
  rw [key, MeasureTheory.integral_mul_left_eq_self (fun y => φ (g * y) * f (h⁻¹ * y)) h]

private
theorem rightConv_add_right {φ f₁ f₂ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : Continuous φ)
    (hf₁ : Continuous f₁) (hf₁c : HasCompactSupport f₁) (hf₂ : Continuous f₂) (hf₂c : HasCompactSupport f₂) :
    rightConv F φ (f₁ + f₂) = rightConv F φ f₁ + rightConv F φ f₂ := by
  letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := AdelicHaar.glBorel (Fin 2) (𝓞 F) F
  haveI : BorelSpace (AdelicGL2 (𝓞 F) F) := AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 F) F
  haveI : (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F).IsHaarMeasure :=
    AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  have hint : ∀ {f : AdelicGL2 (𝓞 F) F → ℂ}, Continuous f → HasCompactSupport f → ∀ g : AdelicGL2 (𝓞 F) F,
      MeasureTheory.Integrable (fun x => φ (g * x) * f x) (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F) := by
    intro f hf hfc g
    have hc : Continuous fun x : AdelicGL2 (𝓞 F) F => φ (g * x) * f x :=
      (hφ.comp (continuous_const.mul continuous_id)).mul hf
    have hs : HasCompactSupport fun x : AdelicGL2 (𝓞 F) F => φ (g * x) * f x := hfc.mul_left
    exact hc.integrable_of_hasCompactSupport hs
  funext g
  simp only [rightConv_apply, Pi.add_apply, mul_add]
  exact MeasureTheory.integral_add (hint hf₁ hf₁c g) (hint hf₂ hf₂c g)

private
theorem rightConv_smul_right (φ f : AdelicGL2 (𝓞 F) F → ℂ) (c : ℂ) :
    rightConv F φ (c • f) = c • rightConv F φ f := by
  funext g
  simp only [rightConv_apply, Pi.smul_apply, smul_eq_mul, mul_left_comm _ c]
  exact MeasureTheory.integral_const_mul c _

private
noncomputable def convMap {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : Continuous φ) (Ψ : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))
    (hΨ : ∀ f ∈ Ψ, Continuous f ∧ HasCompactSupport f) : Ψ →ₗ[ℂ] (AdelicGL2 (𝓞 F) F → ℂ) where
  toFun f := rightConv F φ f
  map_add' f₁ f₂ := rightConv_add_right F hφ (hΨ f₁ f₁.2).1 (hΨ f₁ f₁.2).2 (hΨ f₂ f₂.2).1 (hΨ f₂ f₂.2).2
  map_smul' c f := rightConv_smul_right F φ f c

private
theorem convMap_apply {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : Continuous φ) (Ψ : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))
    (hΨ : ∀ f ∈ Ψ, Continuous f ∧ HasCompactSupport f) (f : Ψ) : convMap F hφ Ψ hΨ f = rightConv F φ f :=
  rfl

private
theorem exists_rightConv_mem_archTypeSubmoduleAt (w : InfinitePlace F) {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : Continuous φ) (Ψ : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) [FiniteDimensional ℂ Ψ]
    (hΨ : ∀ f ∈ Ψ, Continuous f ∧ HasCompactSupport f)
    (hstab : ∀ (k : rowIsometrySubgroup₀ w.Completion), ∀ f ∈ Ψ,
      (fun y => f ((rowIsometryInclAt₀ F w k)⁻¹ * y)) ∈ Ψ)
    {P : AdelicGL2 (𝓞 F) F → ℂ} (hP : P ∈ Ψ) :
    ∃ τ : ArchRepAt F w, rightConv F φ P ∈ archTypeSubmoduleAt F w τ := by
  refine exists_mem_archTypeSubmoduleAt_of_finite_stable F w (LinearMap.range (convMap F hφ Ψ hΨ)) ?_ ?_
  · rintro k _ ⟨f, rfl⟩
    refine ⟨⟨fun y => (f : AdelicGL2 (𝓞 F) F → ℂ) ((rowIsometryInclAt₀ F w k)⁻¹ * y), hstab k f f.2⟩, ?_⟩
    funext x
    rw [convMap_apply, convMap_apply]
    exact (rightConv_mul_right F φ f (rowIsometryInclAt₀ F w k) x).symm
  · exact ⟨⟨P, hP⟩, rfl⟩

private
theorem exists_rightConv_mem_archCutSubmodule {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : Continuous φ)
    (Ψ : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) [FiniteDimensional ℂ Ψ]
    (hΨ : ∀ f ∈ Ψ, Continuous f ∧ HasCompactSupport f)
    (hstab : ∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion), ∀ f ∈ Ψ,
      (fun y => f ((rowIsometryInclAt₀ F w k)⁻¹ * y)) ∈ Ψ)
    {P : AdelicGL2 (𝓞 F) F → ℂ} (hP : P ∈ Ψ) :
    ∃ tys : ArchTypeFamily F, rightConv F φ P ∈ archCutSubmodule F tys :=
  exists_mem_archCutSubmodule_of_forall_exists F _ fun w =>
    exists_rightConv_mem_archTypeSubmoduleAt F w hφ Ψ hΨ (hstab w) hP

end Arch

end IsotypicArchCut.CutStep

namespace IsotypicArchCut
namespace KernelSpace

open AutomorphicForm AutomorphicForm.WindowedSiegel Matrix

section EntrySq

variable {K : Type*} [NormedField K]

end EntrySq

section Algebra

variable {G : Type*}

private
theorem pow_le_toSubmodule (A : Subalgebra ℂ (G → ℂ)) {L : Submodule ℂ (G → ℂ)}
    (hL : L ≤ Subalgebra.toSubmodule A) : ∀ m : ℕ, L ^ m ≤ Subalgebra.toSubmodule A
  | 0 => by
    rw [pow_zero]
    exact Submodule.one_le.mpr A.one_mem
  | m + 1 => by
    rw [pow_succ]
    exact Submodule.mul_le.mpr fun a ha b hb => A.mul_mem (pow_le_toSubmodule A hL m ha) (hL hb)

private
def precomp (σ : G → G) : (G → ℂ) →ₐ[ℂ] (G → ℂ) where
  toFun f := fun y => f (σ y)
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

private
theorem precomp_apply (σ : G → G) (f : G → ℂ) (y : G) : precomp σ f y = f (σ y) := rfl

private
theorem pow_mem_of_map_le {L : Submodule ℂ (G → ℂ)} {τ : (G → ℂ) →ₐ[ℂ] (G → ℂ)}
    (hτ : L.map τ.toLinearMap ≤ L) (m : ℕ) {p : G → ℂ} (hp : p ∈ L ^ m) : τ p ∈ L ^ m := by
  have h : (L ^ m).map τ.toLinearMap ≤ L ^ m := by
    rw [Submodule.map_pow]
    exact pow_le_pow_left' hτ m
  exact h ⟨p, hp, rfl⟩

end Algebra

section Kernel

open NumberField NumberField.InfinitePlace NumberField.AdelicLevel

variable (F : Type) [Field F] [NumberField F]

private
noncomputable abbrev compAt (w : InfinitePlace F) (g : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) w.Completion :=
  (archComponent F w (glArch (𝓞 F) F g) : Matrix (Fin 2) (Fin 2) w.Completion)

private
noncomputable def coord (w : InfinitePlace F) (i j : Fin 2) (g : AdelicGL2 (𝓞 F) F) : ℂ :=
  Completion.extensionEmbedding w (compAt F w g i j)

private
noncomputable def coordBar (w : InfinitePlace F) (i j : Fin 2) (g : AdelicGL2 (𝓞 F) F) : ℂ :=
  (starRingEnd ℂ) (coord F w i j g)

private
noncomputable def disp (g : AdelicGL2 (𝓞 F) F) : ℂ :=
  ((∑ w : InfinitePlace F, entrySq (compAt F w g - 1) : ℝ) : ℂ)

private
def gens : Set (AdelicGL2 (𝓞 F) F → ℂ) :=
  {1, disp F} ∪ Set.range (fun p : InfinitePlace F × Fin 2 × Fin 2 => coord F p.1 p.2.1 p.2.2) ∪
    Set.range (fun p : InfinitePlace F × Fin 2 × Fin 2 => coordBar F p.1 p.2.1 p.2.2)

private
noncomputable def L : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) := Submodule.span ℂ (gens F)

private
theorem gens_finite : (gens F).Finite :=
  ((Set.toFinite _).union (Set.finite_range _)).union (Set.finite_range _)

private
theorem L_fg : (L F).FG := Submodule.fg_span (gens_finite F)

private
theorem one_mem_L : (1 : AdelicGL2 (𝓞 F) F → ℂ) ∈ L F :=
  Submodule.subset_span (Or.inl (Or.inl (Or.inl rfl)))

private
theorem disp_mem_L : disp F ∈ L F :=
  Submodule.subset_span (Or.inl (Or.inl (Or.inr rfl)))

private
theorem coord_mem_L (w : InfinitePlace F) (i j : Fin 2) : coord F w i j ∈ L F :=
  Submodule.subset_span (Or.inl (Or.inr ⟨(w, i, j), rfl⟩))

private
theorem coordBar_mem_L (w : InfinitePlace F) (i j : Fin 2) : coordBar F w i j ∈ L F :=
  Submodule.subset_span (Or.inr ⟨(w, i, j), rfl⟩)

private
theorem continuous_compAt (w : InfinitePlace F) : Continuous (compAt F w) :=
  Units.continuous_val.comp ((continuous_archComponent F w).comp (continuous_glArch (𝓞 F) F))

private
theorem continuous_coord (w : InfinitePlace F) (i j : Fin 2) : Continuous (coord F w i j) :=
  (Completion.isometry_extensionEmbedding w).continuous.comp ((continuous_compAt F w).matrix_elem i j)

private
theorem continuous_coordBar (w : InfinitePlace F) (i j : Fin 2) : Continuous (coordBar F w i j) :=
  Complex.continuous_conj.comp (continuous_coord F w i j)

omit [NumberField F] in
private
theorem continuous_entrySq_comp {X : Type*} [TopologicalSpace X] {w : InfinitePlace F}
    {φ : X → Matrix (Fin 2) (Fin 2) w.Completion} (hφ : Continuous φ) : Continuous fun x => entrySq (φ x) := by
  unfold entrySq
  fun_prop

private
theorem continuous_disp : Continuous (disp F) := by
  unfold disp
  refine Complex.continuous_ofReal.comp (continuous_finsetSum _ fun w _ => ?_)
  exact continuous_entrySq_comp F ((continuous_compAt F w).sub continuous_const)

private
theorem L_le_continuous :
    L F ≤ Subalgebra.toSubmodule (continuousSubalgebra : Subalgebra ℂ (AdelicGL2 (𝓞 F) F → ℂ)) := by
  refine Submodule.span_le.mpr ?_
  rintro f (((rfl | rfl) | ⟨p, rfl⟩) | ⟨p, rfl⟩)
  · exact continuous_const
  · exact continuous_disp F
  · exact continuous_coord F _ _ _
  · exact continuous_coordBar F _ _ _

private
theorem continuous_of_mem_L_pow (m : ℕ) {p : AdelicGL2 (𝓞 F) F → ℂ} (hp : p ∈ L F ^ m) : Continuous p :=
  pow_le_toSubmodule _ (L_le_continuous F) m hp

private
noncomputable def translate (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion) :
    (AdelicGL2 (𝓞 F) F → ℂ) →ₐ[ℂ] (AdelicGL2 (𝓞 F) F → ℂ) :=
  precomp fun y => (rowIsometryInclAt₀ F w k)⁻¹ * y

private
theorem translate_apply (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion) (f : AdelicGL2 (𝓞 F) F → ℂ)
    (y : AdelicGL2 (𝓞 F) F) : translate F w k f y = f ((rowIsometryInclAt₀ F w k)⁻¹ * y) :=
  rfl

omit [NumberField F] in
private
theorem archRowIsometryInclAt₀_apply' (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion) :
    archRowIsometryInclAt₀ F w k = archGLIncl F w (k : GL (Fin 2) w.Completion) :=
  rfl

private
theorem compAt_translate_self (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion) (y : AdelicGL2 (𝓞 F) F) :
    compAt F w ((rowIsometryInclAt₀ F w k)⁻¹ * y)
      = (((k : GL (Fin 2) w.Completion)⁻¹ : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) *
          compAt F w y := by
  unfold compAt
  rw [map_mul, map_inv, glArch_rowIsometryInclAt₀, map_mul, map_inv, archRowIsometryInclAt₀_apply',
    archComponent_archGLIncl_self, Units.val_mul]

private
theorem compAt_translate_of_ne {v w : InfinitePlace F} (hvw : v ≠ w) (k : rowIsometrySubgroup₀ w.Completion)
    (y : AdelicGL2 (𝓞 F) F) : compAt F v ((rowIsometryInclAt₀ F w k)⁻¹ * y) = compAt F v y := by
  unfold compAt
  rw [map_mul, map_inv, glArch_rowIsometryInclAt₀, map_mul, map_inv, archRowIsometryInclAt₀_apply',
    archComponent_archGLIncl_of_ne F hvw, inv_one, one_mul]

private
theorem translate_one (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion) :
    translate F w k (1 : AdelicGL2 (𝓞 F) F → ℂ) = 1 :=
  map_one _

private
theorem translate_coord_self (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion) (i j : Fin 2) :
    translate F w k (coord F w i j) = ∑ l : Fin 2,
      Completion.extensionEmbedding w
          ((((k : GL (Fin 2) w.Completion)⁻¹ : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) i l) •
        coord F w l j := by
  funext y
  simp only [translate_apply, coord, compAt_translate_self, Matrix.mul_apply, map_sum, map_mul, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul]

private
theorem translate_coord_of_ne {v w : InfinitePlace F} (hvw : v ≠ w) (k : rowIsometrySubgroup₀ w.Completion)
    (i j : Fin 2) : translate F w k (coord F v i j) = coord F v i j := by
  funext y
  simp only [translate_apply, coord, compAt_translate_of_ne F hvw]

private
theorem translate_coordBar (w v : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion) (i j : Fin 2) :
    translate F w k (coordBar F v i j) = fun y => (starRingEnd ℂ) (translate F w k (coord F v i j) y) := by
  funext y
  rfl

private
theorem translate_coord_mem (w v : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion) (i j : Fin 2) :
    translate F w k (coord F v i j) ∈ L F := by
  by_cases hvw : v = w
  · subst hvw
    rw [translate_coord_self]
    exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (coord_mem_L F v l j)
  · rw [translate_coord_of_ne F hvw]
    exact coord_mem_L F v i j

private
theorem translate_coordBar_mem (w v : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion) (i j : Fin 2) :
    translate F w k (coordBar F v i j) ∈ L F := by
  rw [translate_coordBar]
  by_cases hvw : v = w
  · subst hvw
    rw [translate_coord_self]
    have : (fun y => (starRingEnd ℂ) ((∑ l : Fin 2, Completion.extensionEmbedding v
        ((((k : GL (Fin 2) v.Completion)⁻¹ : GL (Fin 2) v.Completion) : Matrix (Fin 2) (Fin 2) v.Completion) i l) •
          coord F v l j) y)) = ∑ l : Fin 2, (starRingEnd ℂ) (Completion.extensionEmbedding v
        ((((k : GL (Fin 2) v.Completion)⁻¹ : GL (Fin 2) v.Completion) : Matrix (Fin 2) (Fin 2) v.Completion) i l)) •
          coordBar F v l j := by
      funext y
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, coordBar]
    rw [this]
    exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (coordBar_mem_L F v l j)
  · rw [translate_coord_of_ne F hvw]
    exact coordBar_mem_L F v i j

omit [NumberField F] in

private
theorem ofReal_norm_sub_sq (w : InfinitePlace F) (a b : w.Completion) :
    ((‖a - b‖ ^ 2 : ℝ) : ℂ) = (Completion.extensionEmbedding w a - Completion.extensionEmbedding w b) *
      (starRingEnd ℂ) (Completion.extensionEmbedding w a - Completion.extensionEmbedding w b) := by
  rw [← map_sub, Complex.mul_conj, Complex.normSq_eq_norm_sq,
    (Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _)]

private
theorem shift_mem (w : InfinitePlace F) (B : Matrix (Fin 2) (Fin 2) w.Completion) :
    (fun y => ((entrySq (compAt F w y - B) : ℝ) : ℂ) - ((entrySq (compAt F w y - 1) : ℝ) : ℂ)) ∈ L F := by
  have key : (fun y => ((entrySq (compAt F w y - B) : ℝ) : ℂ) - ((entrySq (compAt F w y - 1) : ℝ) : ℂ)) =
      ∑ i : Fin 2, ∑ j : Fin 2,
        (((starRingEnd ℂ) (Completion.extensionEmbedding w ((1 : Matrix (Fin 2) (Fin 2) w.Completion) i j)) -
            (starRingEnd ℂ) (Completion.extensionEmbedding w (B i j))) • coord F w i j +
          ((Completion.extensionEmbedding w ((1 : Matrix (Fin 2) (Fin 2) w.Completion) i j) -
              Completion.extensionEmbedding w (B i j)) • coordBar F w i j +
            (Completion.extensionEmbedding w (B i j) * (starRingEnd ℂ) (Completion.extensionEmbedding w (B i j)) -
                Completion.extensionEmbedding w ((1 : Matrix (Fin 2) (Fin 2) w.Completion) i j) *
                  (starRingEnd ℂ) (Completion.extensionEmbedding w ((1 : Matrix (Fin 2) (Fin 2) w.Completion) i j))) •
              (1 : AdelicGL2 (𝓞 F) F → ℂ))) := by
    funext y
    simp only [entrySq, Matrix.sub_apply, Complex.ofReal_add, ofReal_norm_sub_sq, map_sub, Finset.sum_apply,
      Fin.sum_univ_two, Pi.add_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one, coordBar, coord]
    ring
  rw [key]
  refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => ?_
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ (coord_mem_L F w i j))
    (Submodule.add_mem _ (Submodule.smul_mem _ _ (coordBar_mem_L F w i j)) (Submodule.smul_mem _ _ (one_mem_L F)))

private
theorem translate_disp (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion) :
    translate F w k (disp F) = disp F + fun y =>
      ((entrySq (compAt F w y - ((k : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion)) : ℝ) : ℂ) -
        ((entrySq (compAt F w y - 1) : ℝ) : ℂ) := by
  funext y
  simp only [Pi.add_apply, translate_apply, disp]
  have hw : entrySq (compAt F w ((rowIsometryInclAt₀ F w k)⁻¹ * y) - 1)
      = entrySq (compAt F w y - ((k : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion)) := by
    rw [compAt_translate_self, ← entrySq_mul_of_mem (inv_mem k.2)
      (compAt F w y - ((k : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion)), Matrix.mul_sub,
      Units.inv_mul]
  have hdiff : (∑ v : InfinitePlace F, entrySq (compAt F v ((rowIsometryInclAt₀ F w k)⁻¹ * y) - 1))
      - ∑ v : InfinitePlace F, entrySq (compAt F v y - 1)
      = entrySq (compAt F w y - ((k : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion))
        - entrySq (compAt F w y - 1) := by
    rw [← Finset.sum_sub_distrib, Finset.sum_eq_single w]
    · rw [hw]
    · intro v _ hvw
      rw [compAt_translate_of_ne F hvw, sub_self]
    · intro h
      exact absurd (Finset.mem_univ w) h
  rw [eq_add_of_sub_eq hdiff]
  push_cast
  ring

private
theorem translate_disp_mem (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion) :
    translate F w k (disp F) ∈ L F := by
  rw [translate_disp]
  exact Submodule.add_mem _ (disp_mem_L F) (shift_mem F w _)

private
theorem map_translate_L_le (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion) :
    (L F).map (translate F w k).toLinearMap ≤ L F := by
  refine (Submodule.map_span_le _ _ _).mpr fun f hf => ?_
  rw [AlgHom.toLinearMap_apply]
  rcases hf with ((rfl | rfl) | ⟨p, rfl⟩) | ⟨p, rfl⟩
  · rw [translate_one]
    exact one_mem_L F
  · exact translate_disp_mem F w k
  · exact translate_coord_mem F w p.1 k p.2.1 p.2.2
  · exact translate_coordBar_mem F w p.1 k p.2.1 p.2.2

variable {F}

private
noncomputable def Ψ (m : ℕ) (F₀ : AdelicGL2 (𝓞 F) F → ℂ) : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) :=
  (L F ^ m).map (LinearMap.mulRight ℂ F₀)

private
theorem Ψ_fg (m : ℕ) (F₀ : AdelicGL2 (𝓞 F) F → ℂ) : (Ψ m F₀).FG := ((L_fg F).pow m).map _

private
scoped instance finiteDimensional_Ψ (m : ℕ) (F₀ : AdelicGL2 (𝓞 F) F → ℂ) : FiniteDimensional ℂ (Ψ m F₀) :=
  Module.Finite.iff_fg.mpr (Ψ_fg m F₀)

private
theorem continuous_and_hasCompactSupport_of_mem_Ψ (m : ℕ) {F₀ : AdelicGL2 (𝓞 F) F → ℂ} (hF₀ : Continuous F₀)
    (hF₀c : HasCompactSupport F₀) : ∀ f ∈ Ψ m F₀, Continuous f ∧ HasCompactSupport f := by
  rintro _ ⟨p, hp, rfl⟩
  rw [LinearMap.mulRight_apply]
  exact ⟨(continuous_of_mem_L_pow F m hp).mul hF₀, hF₀c.mul_left⟩

private
theorem translate_mem_Ψ (m : ℕ) {F₀ : AdelicGL2 (𝓞 F) F → ℂ}
    (hinv : ∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion) (y : AdelicGL2 (𝓞 F) F),
      F₀ ((rowIsometryInclAt₀ F w k)⁻¹ * y) = F₀ y) :
    ∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion), ∀ f ∈ Ψ m F₀,
      (fun y => f ((rowIsometryInclAt₀ F w k)⁻¹ * y)) ∈ Ψ m F₀ := by
  rintro w k _ ⟨p, hp, rfl⟩
  refine ⟨translate F w k p, pow_mem_of_map_le (map_translate_L_le F w k) m hp, ?_⟩
  funext y
  simp only [LinearMap.mulRight_apply, Pi.mul_apply, translate_apply, hinv]

private
theorem kernel_mem_Ψ (m : ℕ) (R : ℂ) (F₀ : AdelicGL2 (𝓞 F) F → ℂ) :
    (R • (1 : AdelicGL2 (𝓞 F) F → ℂ) - disp F) ^ m * F₀ ∈ Ψ m F₀ :=
  ⟨_, Submodule.pow_mem_pow _ (Submodule.sub_mem _ (Submodule.smul_mem _ R (one_mem_L F)) (disp_mem_L F)) m, rfl⟩

end Kernel

end IsotypicArchCut.KernelSpace
p2m_reactivate "P2MW.S_AutomorphicForm_exists_mem_archCutSubmodule_isIsotypicCuspFormAt_ne_zero.IsotypicArchCut P2MW.S_AutomorphicForm_exists_mem_archCutSubmodule_isIsotypicCuspFormAt_ne_zero.IsotypicArchCut.KernelSpace"
p2m_reactivate "P2MW.S_AutomorphicForm_exists_mem_archCutSubmodule_isIsotypicCuspFormAt_ne_zero.IsotypicArchCut"

namespace IsotypicArchCut
namespace NonVanishing

open AutomorphicForm IsDedekindDomain NumberField MeasureTheory

variable (F : Type) [Field F] [NumberField F]

private
theorem exists_rightConv_ne_zero {u : AdelicGL2 (𝓞 F) F → ℂ} (hu : Continuous u) {x₀ : AdelicGL2 (𝓞 F) F}
    (hx₀ : u x₀ ≠ 0) {F₀ : AdelicGL2 (𝓞 F) F → ℝ} (hF₀ : Continuous F₀) (hF₀c : HasCompactSupport F₀)
    (hF₀nn : ∀ x, 0 ≤ F₀ x) (hF₀1 : 0 < F₀ 1) {q : AdelicGL2 (𝓞 F) F → ℝ} (hq : Continuous q) (hq1 : q 1 = 0)
    (hctrl : ∀ ε > 0, ∃ δ > 0, ∀ x, F₀ x ≠ 0 → q x < δ → ‖u (x₀ * x) - u x₀‖ ≤ ε) :
    ∃ (R : ℝ) (m : ℕ), rightConv F u (fun x => (((R - q x) ^ m * F₀ x : ℝ) : ℂ)) x₀ ≠ 0 := by
  letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := AdelicHaar.glBorel (Fin 2) (𝓞 F) F
  haveI : BorelSpace (AdelicGL2 (𝓞 F) F) := AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 F) F
  haveI : (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F).IsHaarMeasure :=
    AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  set μ : Measure (AdelicGL2 (𝓞 F) F) := AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F with hμ

  obtain ⟨R₀, hR₀⟩ := hF₀c.isCompact.exists_bound_of_continuousOn hq.continuousOn
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = max R₀ 0 + 1 := ⟨_, rfl⟩
  have hR1 : (1 : ℝ) ≤ R := by linarith [le_max_right R₀ 0]
  have hRq : ∀ x, F₀ x ≠ 0 → 0 < R - q x := fun x hx => by
    have h1 : ‖q x‖ ≤ R₀ := hR₀ x (subset_tsupport _ hx)
    linarith [Real.le_norm_self (q x), le_max_left R₀ 0]

  obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = ‖u x₀‖ / 2 := ⟨_, rfl⟩
  have hε0 : 0 < ε := by linarith [norm_pos_iff.mpr hx₀]
  obtain ⟨δ₀, hδ₀, hδ₀ctrl⟩ := hctrl ε hε0
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = min δ₀ 1 := ⟨_, rfl⟩
  have hδ0 : 0 < δ := hδ ▸ lt_min hδ₀ one_pos
  have hδ1 : δ ≤ 1 := hδ ▸ min_le_right _ _
  have hδctrl : ∀ x, F₀ x ≠ 0 → q x < δ → ‖u (x₀ * x) - u x₀‖ ≤ ε := fun x hx hqx =>
    hδ₀ctrl x hx (lt_of_lt_of_le hqx (hδ ▸ min_le_left _ _))
  have hRδ : 0 ≤ R - δ := by linarith
  have hRδ2 : 0 < R - δ / 2 := by linarith

  have hvar : Continuous fun x => u (x₀ * x) - u x₀ :=
    (hu.comp (continuous_const.mul continuous_id)).sub continuous_const
  obtain ⟨M₀, hM₀⟩ := hF₀c.isCompact.exists_bound_of_continuousOn hvar.norm.continuousOn
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = max M₀ 0 := ⟨_, rfl⟩
  have hM0 : 0 ≤ M := hM ▸ le_max_right _ _
  have hMvar : ∀ x, F₀ x ≠ 0 → ‖u (x₀ * x) - u x₀‖ ≤ M := fun x hx => by
    have h := hM₀ x (subset_tsupport _ hx)
    rw [norm_norm] at h
    exact h.trans (hM ▸ le_max_left _ _)

  have hF₀int : Integrable F₀ μ := hF₀.integrable_of_hasCompactSupport hF₀c
  obtain ⟨C₁, hC₁⟩ : ∃ C₁ : ℝ, C₁ = ∫ x, F₀ x ∂μ := ⟨_, rfl⟩
  have hC₁0 : 0 ≤ C₁ := hC₁ ▸ integral_nonneg hF₀nn

  obtain ⟨W, hW⟩ : ∃ W : Set (AdelicGL2 (𝓞 F) F), W = {x | q x < δ / 2} ∩ {x | F₀ 1 / 2 < F₀ x} := ⟨_, rfl⟩
  have hWopen : IsOpen W := hW ▸ (isOpen_lt hq continuous_const).inter (isOpen_lt continuous_const hF₀)
  have h1W : (1 : AdelicGL2 (𝓞 F) F) ∈ W := by
    rw [hW]
    exact ⟨show q 1 < δ / 2 by rw [hq1]; linarith, half_lt_self hF₀1⟩
  have hmemW : ∀ x ∈ W, q x < δ / 2 ∧ F₀ 1 / 2 < F₀ x := fun x hx => by
    rw [hW] at hx
    exact hx
  have hWsub : W ⊆ tsupport F₀ := fun x hx =>
    subset_tsupport _ (ne_of_gt (lt_of_le_of_lt (by linarith) (hmemW x hx).2))
  have hWpos : 0 < μ W := hWopen.measure_pos μ ⟨1, h1W⟩
  have hWfin : μ W < ⊤ := lt_of_le_of_lt (measure_mono hWsub) hF₀c.isCompact.measure_lt_top
  have hWreal : 0 < μ.real W := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos hWpos.ne' hWfin.ne
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = μ.real W * (F₀ 1 / 2) := ⟨_, rfl⟩
  have hc0 : 0 < c := hc ▸ mul_pos hWreal (by linarith)

  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = (R - δ) / (R - δ / 2) := ⟨_, rfl⟩
  have hr0 : 0 ≤ r := hr ▸ div_nonneg hRδ hRδ2.le
  have hr1 : r < 1 := hr ▸ (div_lt_one hRδ2).mpr (by linarith)
  have hrδ : R - δ = r * (R - δ / 2) := by
    rw [hr, div_mul_cancel₀ _ hRδ2.ne']
  have hMC : (0 : ℝ) < M * C₁ + 1 := by positivity
  obtain ⟨m, hm⟩ := ((tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).eventually
    (gt_mem_nhds (div_pos (mul_pos hε0 hc0) hMC))).exists
  have hm' : M * C₁ * r ^ m < ε * c := by
    have h1 : (M * C₁ + 1) * r ^ m < ε * c := by
      have h := (lt_div_iff₀ hMC).mp hm
      linarith
    have h2 : M * C₁ * r ^ m ≤ (M * C₁ + 1) * r ^ m :=
      mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg hr0 m)
    linarith
  refine ⟨R, m, ?_⟩

  obtain ⟨P, hP⟩ : ∃ P : AdelicGL2 (𝓞 F) F → ℝ, P = fun x => (R - q x) ^ m * F₀ x := ⟨_, rfl⟩
  have hPx : ∀ x, P x = (R - q x) ^ m * F₀ x := fun x => by rw [hP]
  have hPcont : Continuous P := hP ▸ ((continuous_const.sub hq).pow m).mul hF₀
  have hPsupp : HasCompactSupport P := hP ▸ hF₀c.mul_left
  have hPnn : ∀ x, 0 ≤ P x := fun x => by
    rw [hPx]
    by_cases hx : F₀ x = 0
    · rw [hx, mul_zero]
    · exact mul_nonneg (pow_nonneg (hRq x hx).le m) (hF₀nn x)
  have hPint : Integrable P μ := hPcont.integrable_of_hasCompactSupport hPsupp
  obtain ⟨I, hI⟩ : ∃ I : ℝ, I = ∫ x, P x ∂μ := ⟨_, rfl⟩
  have hI0 : 0 ≤ I := hI ▸ integral_nonneg hPnn

  have hPCsupp : HasCompactSupport fun x => ((P x : ℝ) : ℂ) := hPsupp.comp_left Complex.ofReal_zero
  have hPCcont : Continuous fun x => ((P x : ℝ) : ℂ) := Complex.continuous_ofReal.comp hPcont
  have hPCint : Integrable (fun x => ((P x : ℝ) : ℂ)) μ := hPCcont.integrable_of_hasCompactSupport hPCsupp
  have hEint : Integrable (fun x => (u (x₀ * x) - u x₀) * ((P x : ℝ) : ℂ)) μ :=
    (hvar.mul hPCcont).integrable_of_hasCompactSupport hPCsupp.mul_left
  obtain ⟨E, hE⟩ : ∃ E : ℂ, E = ∫ x, (u (x₀ * x) - u x₀) * ((P x : ℝ) : ℂ) ∂μ := ⟨_, rfl⟩
  have hdecomp : rightConv F u (fun x => (((R - q x) ^ m * F₀ x : ℝ) : ℂ)) x₀ = u x₀ * (I : ℂ) + E := by
    rw [rightConv_apply, ← hμ]
    have hsplit : (fun x => u (x₀ * x) * (((R - q x) ^ m * F₀ x : ℝ) : ℂ)) =
        fun x => u x₀ * ((P x : ℝ) : ℂ) + (u (x₀ * x) - u x₀) * ((P x : ℝ) : ℂ) := by
      funext x
      rw [hPx]
      ring
    rw [hsplit, integral_add (hPCint.const_mul _) hEint, integral_const_mul, integral_complex_ofReal, hI, hE]

  have hEbound : ‖E‖ ≤ ε * I + M * (R - δ) ^ m * C₁ := by
    have hpt : ∀ x, ‖(u (x₀ * x) - u x₀) * ((P x : ℝ) : ℂ)‖ ≤ ε * P x + M * (R - δ) ^ m * F₀ x := fun x => by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hPnn x)]
      by_cases hx : F₀ x = 0
      · have h0 : P x = 0 := by rw [hPx, hx, mul_zero]
        rw [h0, hx]
        simp
      · have hsecond : 0 ≤ M * (R - δ) ^ m * F₀ x := mul_nonneg (mul_nonneg hM0 (pow_nonneg hRδ m)) (hF₀nn x)
        by_cases hqx : q x < δ
        · have h := mul_le_mul_of_nonneg_right (hδctrl x hx hqx) (hPnn x)
          linarith
        · push Not at hqx
          have hPle : P x ≤ (R - δ) ^ m * F₀ x := by
            rw [hPx]
            exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (hRq x hx).le (by linarith) m) (hF₀nn x)
          have h1 : ‖u (x₀ * x) - u x₀‖ * P x ≤ M * P x := mul_le_mul_of_nonneg_right (hMvar x hx) (hPnn x)
          have h2 : M * P x ≤ M * ((R - δ) ^ m * F₀ x) := mul_le_mul_of_nonneg_left hPle hM0
          have h3 : 0 ≤ ε * P x := mul_nonneg hε0.le (hPnn x)
          linarith
    have hg : Integrable (fun x => ε * P x + M * (R - δ) ^ m * F₀ x) μ :=
      (hPint.const_mul ε).add (hF₀int.const_mul _)
    calc ‖E‖ = ‖∫ x, (u (x₀ * x) - u x₀) * ((P x : ℝ) : ℂ) ∂μ‖ := by rw [hE]
      _ ≤ ∫ x, ‖(u (x₀ * x) - u x₀) * ((P x : ℝ) : ℂ)‖ ∂μ := norm_integral_le_integral_norm _
      _ ≤ ∫ x, (ε * P x + M * (R - δ) ^ m * F₀ x) ∂μ := integral_mono hEint.norm hg hpt
      _ = ε * I + M * (R - δ) ^ m * C₁ := by
        rw [integral_add (hPint.const_mul ε) (hF₀int.const_mul _), integral_const_mul, integral_const_mul, hI, hC₁]

  have hIlow : (R - δ / 2) ^ m * c ≤ I := by
    have hWm : MeasurableSet W := hWopen.measurableSet
    have hind : Integrable (W.indicator fun _ => (R - δ / 2) ^ m * (F₀ 1 / 2)) μ :=
      (integrable_indicator_iff hWm).mpr (integrableOn_const hWfin.ne)
    have hpt : ∀ x, W.indicator (fun _ => (R - δ / 2) ^ m * (F₀ 1 / 2)) x ≤ P x := fun x => by
      by_cases hx : x ∈ W
      · rw [Set.indicator_of_mem hx, hPx]
        obtain ⟨hx1, hx2⟩ := hmemW x hx
        exact mul_le_mul (pow_le_pow_left₀ hRδ2.le (by linarith) m) hx2.le (by linarith)
          (pow_nonneg (by linarith) m)
      · rw [Set.indicator_of_notMem hx]
        exact hPnn x
    calc (R - δ / 2) ^ m * c = ∫ x, W.indicator (fun _ => (R - δ / 2) ^ m * (F₀ 1 / 2)) x ∂μ := by
          rw [integral_indicator_const _ hWm, smul_eq_mul, hc]
          ring
      _ ≤ I := hI ▸ integral_mono hind hPint hpt

  rw [hdecomp]
  intro hzero
  have hmain : ‖u x₀ * (I : ℂ)‖ = 2 * ε * I := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hI0, hε]
    ring
  have hnorm : ‖u x₀ * (I : ℂ)‖ ≤ ‖u x₀ * (I : ℂ) + E‖ + ‖E‖ := by
    have h := norm_sub_le (u x₀ * (I : ℂ) + E) E
    rwa [add_sub_cancel_right] at h
  rw [hzero, norm_zero, zero_add, hmain] at hnorm
  have h1 : ε * ((R - δ / 2) ^ m * c) ≤ ε * I := mul_le_mul_of_nonneg_left hIlow hε0.le
  have h2 : M * (R - δ) ^ m * C₁ = (R - δ / 2) ^ m * (M * C₁ * r ^ m) := by
    rw [hrδ, mul_pow]
    ring
  have h3 : 0 < (R - δ / 2) ^ m * (ε * c - M * C₁ * r ^ m) := mul_pos (pow_pos hRδ2 m) (by linarith)
  nlinarith [h1, h2, h3, hEbound, hnorm]

end IsotypicArchCut.NonVanishing
p2m_reactivate "P2MW.S_AutomorphicForm_exists_mem_archCutSubmodule_isIsotypicCuspFormAt_ne_zero.IsotypicArchCut P2MW.S_AutomorphicForm_exists_mem_archCutSubmodule_isIsotypicCuspFormAt_ne_zero.IsotypicArchCut.KernelSpace"
p2m_reactivate "P2MW.S_AutomorphicForm_exists_mem_archCutSubmodule_isIsotypicCuspFormAt_ne_zero.IsotypicArchCut P2MW.S_AutomorphicForm_exists_mem_archCutSubmodule_isIsotypicCuspFormAt_ne_zero.IsotypicArchCut.KernelSpace"

namespace PrincipalCosetSystems

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum AutomorphicForm
open NumberField.AdelicLevel LocalGL2 HeckeIntegralSeam AdelicDock

variable (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

private theorem mem_U_of_components {N : Ideal (𝓞 F)} {h : GL (Fin 2) (AdeleRing (𝓞 F) F)}
    (harch : glArch (𝓞 F) F h = 1)
    (hfin : ∀ w : HeightOneSpectrum (𝓞 F),
      finComponent (𝓞 F) F w (glFin (𝓞 F) F h) ∈ localLevelOne (𝓞 F) F w N) :
    h ∈ levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F := by
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · rw [mem_levelOne_iff, mem_finiteLevelOne_iff]
    have hlocal : ∀ w, IsLocalLevelOne (𝓞 F) F w N
          (finComponent (𝓞 F) F w (glFin (𝓞 F) F h) : Matrix (Fin 2) (Fin 2) _)
        ∧ IsLocalLevelOne (𝓞 F) F w N
          ((finComponent (𝓞 F) F w (glFin (𝓞 F) F h))⁻¹ : GL (Fin 2) _) := by
      intro w
      exact (mem_localLevelOne_iff (𝓞 F) F w (finComponent (𝓞 F) F w (glFin (𝓞 F) F h))).mp
        (hfin w)
    constructor
    · exact ⟨⟨fun i j w => (hlocal w).1.integral i j, fun w => (hlocal w).1.lowerLeft⟩,
        fun w => by
          rw [AdelicLevel.coe_sub_apply, AdelicLevel.coe_one_apply]
          exact (hlocal w).1.lowerRight⟩
    · refine ⟨⟨fun i j w => ?_, fun w => ?_⟩, fun w => ?_⟩
      · have := (hlocal w).2.integral i j
        rwa [← map_inv] at this
      · have := (hlocal w).2.lowerLeft
        rwa [← map_inv] at this
      · rw [AdelicLevel.coe_sub_apply, AdelicLevel.coe_one_apply]
        have := (hlocal w).2.lowerRight
        rwa [← map_inv] at this
  · exact (mem_finiteAdelicGL2Subgroup_iff F h).mpr harch

private theorem components_of_mem_U {N : Ideal (𝓞 F)} {h : GL (Fin 2) (AdeleRing (𝓞 F) F)}
    (hh : h ∈ levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) :
    glArch (𝓞 F) F h = 1 ∧ ∀ w : HeightOneSpectrum (𝓞 F),
      finComponent (𝓞 F) F w (glFin (𝓞 F) F h) ∈ localLevelOne (𝓞 F) F w N := by
  obtain ⟨h1, h2⟩ := Subgroup.mem_inf.mp hh
  refine ⟨(mem_finiteAdelicGL2Subgroup_iff F h).mp h2, fun w => ?_⟩
  rw [mem_levelOne_iff, mem_finiteLevelOne_iff] at h1
  rw [mem_localLevelOne_iff]
  obtain ⟨ha, hb⟩ := h1
  constructor
  · exact ⟨fun i j => ha.integral i j w, ha.lowerLeft w, by
      have := ha.lowerRight w
      rwa [AdelicLevel.coe_sub_apply, AdelicLevel.coe_one_apply] at this⟩
  · rw [← map_inv]
    exact ⟨fun i j => hb.integral i j w, hb.lowerLeft w, by
      have := hb.lowerRight w
      rwa [AdelicLevel.coe_sub_apply, AdelicLevel.coe_one_apply] at this⟩

private theorem comp_self (z : GL (Fin 2) (v.adicCompletion F)) :
    finComponent (𝓞 F) F v (glFin (𝓞 F) F (finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v z))) = z := by
  rw [glFin_finEmbed, finComponent_localEmbed_self]

private theorem comp_of_ne (z : GL (Fin 2) (v.adicCompletion F)) {w : HeightOneSpectrum (𝓞 F)}
    (hw : w ≠ v) :
    finComponent (𝓞 F) F w (glFin (𝓞 F) F (finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v z))) = 1 := by
  rw [glFin_finEmbed, finComponent_localEmbed_of_ne _ _ _ _ hw]

omit [NumberField F] in
private theorem ne_bot_of_not_dvd {N : Ideal (𝓞 F)} (hv : ¬ v.asIdeal ∣ N) : N ≠ ⊥ := by
  rintro rfl
  exact hv (dvd_zero _)

private theorem isLocalLevelOne_of_integral {N : Ideal (𝓞 F)} (hv : ¬ v.asIdeal ∣ N)
    {m : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)}
    (hm : ∀ i j, m i j ∈ v.adicCompletionIntegers F) : IsLocalLevelOne (𝓞 F) F v N m := by
  have hb : idealBound (𝓞 F) N v = 1 := idealBound_eq_one_of_not_dvd (ne_bot_of_not_dvd F v hv) hv
  refine ⟨hm, ?_, ?_⟩
  · rw [hb]
    exact (mem_adicCompletionIntegers _ _ _).mp (hm 1 0)
  · rw [hb]
    exact (mem_adicCompletionIntegers _ _ _).mp (sub_mem (hm 1 1) (one_mem _))

private theorem mem_localLevelOne_of_integral {N : Ideal (𝓞 F)} (hv : ¬ v.asIdeal ∣ N)
    {k : GL (Fin 2) (v.adicCompletion F)}
    (hk : ∀ i j, (k : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j ∈ v.adicCompletionIntegers F)
    (hk' : ∀ i j, ((k⁻¹ : GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F))
      i j ∈ v.adicCompletionIntegers F) :
    k ∈ localLevelOne (𝓞 F) F v N := by
  rw [mem_localLevelOne_iff]
  exact ⟨isLocalLevelOne_of_integral F v hv hk, isLocalLevelOne_of_integral F v hv hk'⟩

private noncomputable abbrev wc (w : HeightOneSpectrum (𝓞 F)) : GL (Fin 2) (w.adicCompletion F) :=
  finComponent (𝓞 F) F w (glFin (𝓞 F) F (weyl (𝓞 F) F))

private theorem weyl_mul_self : weyl (𝓞 F) F * weyl (𝓞 F) F = 1 :=
  Units.ext (by simp [weyl, Matrix.one_fin_two])

private theorem wc_mul_self (w : HeightOneSpectrum (𝓞 F)) : wc F w * wc F w = 1 := by
  simp only [wc, ← map_mul, weyl_mul_self, map_one]

private theorem weyl_entry_mem (w : HeightOneSpectrum (𝓞 F)) (i j : Fin 2) :
    (wc F w : Matrix (Fin 2) (Fin 2) (w.adicCompletion F)) i j ∈ w.adicCompletionIntegers F := by
  rw [finComponent_apply, glFin_apply]
  fin_cases i <;> fin_cases j <;> simp [weyl] <;>
    first
      | exact zero_mem_integralFiniteAdeles w
      | exact one_mem_integralFiniteAdeles w

private theorem wc_mem {N : Ideal (𝓞 F)} {w : HeightOneSpectrum (𝓞 F)} (hw : ¬ w.asIdeal ∣ N) :
    wc F w ∈ localLevelOne (𝓞 F) F w N := by
  refine mem_localLevelOne_of_integral F w hw (weyl_entry_mem F w) fun i j => ?_
  rw [inv_eq_of_mul_eq_one_right (wc_mul_self F w)]
  exact weyl_entry_mem F w i j

private theorem comp_conj (w : HeightOneSpectrum (𝓞 F)) (h : GL (Fin 2) (AdeleRing (𝓞 F) F)) :
    finComponent (𝓞 F) F w (glFin (𝓞 F) F ((weyl (𝓞 F) F)⁻¹ * h * weyl (𝓞 F) F))
      = (wc F w)⁻¹ * finComponent (𝓞 F) F w (glFin (𝓞 F) F h) * wc F w := by
  simp only [wc, map_mul, map_inv]

private theorem mem_P_of_components {N : Ideal (𝓞 F)} {h : GL (Fin 2) (AdeleRing (𝓞 F) F)}
    (hU : h ∈ levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
    (hconj : ∀ w : HeightOneSpectrum (𝓞 F),
      (wc F w)⁻¹ * finComponent (𝓞 F) F w (glFin (𝓞 F) F h) * wc F w ∈ localLevelOne (𝓞 F) F w N) :
    h ∈ principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F := by
  obtain ⟨h1, h2⟩ := Subgroup.mem_inf.mp hU
  refine Subgroup.mem_inf.mpr ⟨(mem_principalLevel_iff (𝓞 F) F N).mpr ⟨h1, ?_⟩, h2⟩
  have harch : glArch (𝓞 F) F h = 1 := (components_of_mem_U F hU).1
  have hz : (weyl (𝓞 F) F)⁻¹ * h * weyl (𝓞 F) F ∈ levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F := by
    refine mem_U_of_components F ?_ fun w => ?_
    · simp only [map_mul, map_inv, harch, mul_one, inv_mul_cancel]
    · rw [comp_conj]
      exact hconj w
  refine Subgroup.mem_map.mpr ⟨(weyl (𝓞 F) F)⁻¹ * h * weyl (𝓞 F) F, (Subgroup.mem_inf.mp hz).1, ?_⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  group

private theorem components_of_mem_P {N : Ideal (𝓞 F)} {p : GL (Fin 2) (AdeleRing (𝓞 F) F)}
    (hp : p ∈ principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (w : HeightOneSpectrum (𝓞 F)) :
    (wc F w)⁻¹ * finComponent (𝓞 F) F w (glFin (𝓞 F) F p) * wc F w ∈ localLevelOne (𝓞 F) F w N := by
  obtain ⟨h1, h2⟩ := Subgroup.mem_inf.mp hp
  obtain ⟨-, hmap⟩ := (mem_principalLevel_iff (𝓞 F) F N).mp h1
  obtain ⟨z, hz, hzp⟩ := Subgroup.mem_map.mp hmap
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hzp
  have hz' : (weyl (𝓞 F) F)⁻¹ * p * weyl (𝓞 F) F = z := by
    rw [← hzp]; group
  have harch : glArch (𝓞 F) F p = 1 := (mem_finiteAdelicGL2Subgroup_iff F p).mp h2
  have hzU : z ∈ levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F := by
    refine Subgroup.mem_inf.mpr ⟨hz, (mem_finiteAdelicGL2Subgroup_iff F z).mpr ?_⟩
    rw [← hz']
    simp only [map_mul, map_inv, harch, mul_one, inv_mul_cancel]
  rw [← comp_conj, hz']
  exact (components_of_mem_U F hzU).2 w

private theorem P_le_U (N : Ideal (𝓞 F)) :
    principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F ≤ levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F :=
  inf_le_inf_right _ (principalLevel_le_levelOne (𝓞 F) F N)

private theorem supported_mem_P {N : Ideal (𝓞 F)} (hv : ¬ v.asIdeal ∣ N)
    {z : GL (Fin 2) (v.adicCompletion F)} (hz : z ∈ localLevelOne (𝓞 F) F v N) :
    finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v z) ∈ principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F := by
  have hU : finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v z) ∈ levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F := by
    refine mem_U_of_components F (glArch_finEmbed _ _ _) fun w => ?_
    by_cases hw : w = v
    · rw [hw, comp_self]
      exact hz
    · rw [comp_of_ne F v z hw]
      exact one_mem _
  refine mem_P_of_components F hU fun w => ?_
  by_cases hw : w = v
  · rw [hw, comp_self]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ (wc_mem F hv)) hz) (wc_mem F hv)
  · rw [comp_of_ne F v z hw, mul_one, inv_mul_cancel]
    exact one_mem _

private
theorem isHeckeCosetSystem_principal_of_not_dvd {N : Ideal (𝓞 F)} (hv : ¬ v.asIdeal ∣ N)
    (d : GL (Fin 2) (v.adicCompletion F)) {ι : Type} (r : ι → GL (Fin 2) (v.adicCompletion F))
    (hsys : IsHeckeCosetSystem (levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
      (finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v d))
      (fun i => finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v (r i)))) :
    IsHeckeCosetSystem (principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
      (finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v d))
      (fun i => finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v (r i))) := by
  refine ⟨fun i => ?_, fun x hx => ?_, fun i j hij => ?_⟩
  ·
    obtain ⟨u₁, hu₁, u₂, hu₂, hrep⟩ := HeckePair.mem_doubleCoset_iff.mp (hsys.mem_doubleCoset i)
    set a₁ := finComponent (𝓞 F) F v (glFin (𝓞 F) F u₁) with ha₁
    set a₂ := finComponent (𝓞 F) F v (glFin (𝓞 F) F u₂) with ha₂
    have hloc : a₁ * d * a₂ = r i := by
      have h := congrArg (fun y => finComponent (𝓞 F) F v (glFin (𝓞 F) F y)) hrep
      simpa only [map_mul, comp_self] using h
    refine HeckePair.mem_doubleCoset_iff.mpr
      ⟨finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v a₁),
        supported_mem_P F v hv ((components_of_mem_U F hu₁).2 v),
        finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v a₂),
        supported_mem_P F v hv ((components_of_mem_U F hu₂).2 v), ?_⟩
    simp only [← map_mul, hloc]
  ·
    have hxU : x ∈ HeckePair.doubleCoset (levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v d)) := by
      obtain ⟨p₁, hp₁, p₂, hp₂, hxeq⟩ := HeckePair.mem_doubleCoset_iff.mp hx
      exact HeckePair.mem_doubleCoset_iff.mpr ⟨p₁, P_le_U F N hp₁, p₂, P_le_U F N hp₂, hxeq⟩
    obtain ⟨i, hi⟩ := hsys.covers x hxU
    refine ⟨i, ?_⟩
    rw [QuotientGroup.eq] at hi ⊢
    obtain ⟨p₁, hp₁, p₂, hp₂, hxeq⟩ := HeckePair.mem_doubleCoset_iff.mp hx
    refine mem_P_of_components F hi fun w => ?_
    by_cases hw : w = v
    · rw [hw]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ (wc_mem F hv))
        ((components_of_mem_U F hi).2 v)) (wc_mem F hv)
    · have hx' : finComponent (𝓞 F) F w (glFin (𝓞 F) F x)
          = finComponent (𝓞 F) F w (glFin (𝓞 F) F p₁) * finComponent (𝓞 F) F w (glFin (𝓞 F) F p₂) := by
        rw [← hxeq]
        simp only [map_mul, comp_of_ne F v d hw, mul_one]
      have hr : finComponent (𝓞 F) F w (glFin (𝓞 F) F
          (finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v (r i)))) = 1 := comp_of_ne F v (r i) hw
      simp only [map_mul, map_inv, hx', hr, mul_one, mul_inv_rev]
      have h₁ := components_of_mem_P F hp₁ w
      have h₂ := components_of_mem_P F hp₂ w
      have key : (wc F w)⁻¹ * ((finComponent (𝓞 F) F w (glFin (𝓞 F) F p₂))⁻¹
            * (finComponent (𝓞 F) F w (glFin (𝓞 F) F p₁))⁻¹) * wc F w
          = ((wc F w)⁻¹ * finComponent (𝓞 F) F w (glFin (𝓞 F) F p₂) * wc F w)⁻¹
            * ((wc F w)⁻¹ * finComponent (𝓞 F) F w (glFin (𝓞 F) F p₁) * wc F w)⁻¹ := by
        group
      rw [key]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ h₂) (Subgroup.inv_mem _ h₁)
  ·
    apply hsys.mk_injective
    beta_reduce at hij ⊢
    rw [QuotientGroup.eq] at hij ⊢
    exact P_le_U F N hij

private
theorem exists_isHeckeCosetSystem_principalLevel_heckeGen_option {N : Ideal (𝓞 F)}
    (hv : ¬ v.asIdeal ∣ N) :
    ∃ reps : Option (𝓞 F ⧸ v.asIdeal) → AdelicGL2 (𝓞 F) F,
      IsHeckeCosetSystem (principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (heckeGen (𝓞 F) F v) reps := by
  obtain ⟨ϖ, hϖ0, -, hgen, sec, -, hM⟩ :=
    HeckeIntegralSeam.exists_isHeckeCosetSystem_localRep_heckeGen F v
  have S := hM N hv
  rw [← hgen] at S ⊢
  exact ⟨_, isHeckeCosetSystem_principal_of_not_dvd F v hv (diagPi ϖ hϖ0)
    (fun i : Option (𝓞 F ⧸ v.asIdeal) => i.elim (localRepInf ϖ hϖ0)
      (fun c => localRepSome ϖ hϖ0 (algebraMap (𝓞 F) (v.adicCompletionIntegers F) (sec c)))) S⟩

private theorem reindex {G : Type} [Group G] {U : Subgroup G} {g : G} {ι κ : Type} {reps : ι → G}
    (h : IsHeckeCosetSystem U g reps) (e : κ ≃ ι) : IsHeckeCosetSystem U g (reps ∘ e) := by
  refine ⟨fun k => h.mem_doubleCoset (e k), fun x hx => ?_, fun k k' hkk' => ?_⟩
  · obtain ⟨i, hi⟩ := h.covers x hx
    exact ⟨e.symm i, by simpa using hi⟩
  · exact e.injective (h.mk_injective hkk')

private theorem card_option_quotient [Fintype (𝓞 F ⧸ v.asIdeal)] :
    Fintype.card (Option (𝓞 F ⧸ v.asIdeal)) = Ideal.absNorm v.asIdeal + 1 := by
  rw [Fintype.card_option, ← Nat.card_eq_fintype_card, Ideal.absNorm_apply, Submodule.cardQuot_apply]

private
theorem exists_isHeckeCosetSystem_principalLevel_heckeGen {N : Ideal (𝓞 F)} (hv : ¬ v.asIdeal ∣ N) :
    ∃ reps : Fin (Ideal.absNorm v.asIdeal + 1) → AdelicGL2 (𝓞 F) F,
      IsHeckeCosetSystem (principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (heckeGen (𝓞 F) F v) reps := by
  obtain ⟨reps, hreps⟩ := exists_isHeckeCosetSystem_principalLevel_heckeGen_option F v hv
  have habs : Ideal.absNorm v.asIdeal ≠ 0 :=
    Ideal.absNorm_ne_zero_iff_mem_nonZeroDivisors.mpr (mem_nonZeroDivisors_of_ne_zero v.ne_bot)
  haveI : Finite (𝓞 F ⧸ v.asIdeal) := (Ideal.absNorm_ne_zero_iff v.asIdeal).mp habs
  haveI : Fintype (𝓞 F ⧸ v.asIdeal) := Fintype.ofFinite _
  exact ⟨reps ∘ (Fintype.equivFinOfCardEq (card_option_quotient F v)).symm,
    reindex hreps (Fintype.equivFinOfCardEq (card_option_quotient F v)).symm⟩

end PrincipalCosetSystems
p2m_reactivate "P2MW.S_AutomorphicForm_exists_mem_archCutSubmodule_isIsotypicCuspFormAt_ne_zero.IsotypicArchCut P2MW.S_AutomorphicForm_exists_mem_archCutSubmodule_isIsotypicCuspFormAt_ne_zero.IsotypicArchCut.KernelSpace"

namespace AdelicTestFunctions

open NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering AutomorphicForm.SmoothCusp
open IsDedekindDomain MeasureTheory

section Basics

variable {K : Type} [Field K] [NumberField K]

private
theorem continuous_val_finEmbed :
    Continuous fun g : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) =>
      ((AdelicDock.finEmbed (𝓞 K) K g : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) :=
  continuous_pi fun i => continuous_pi fun j =>
    continuous_const.prodMk (Units.continuous_val.matrix_elem i j)

private
theorem continuous_finEmbed : Continuous (AdelicDock.finEmbed (𝓞 K) K) :=
  Units.continuous_iff.mpr ⟨continuous_val_finEmbed,
    (continuous_val_finEmbed.comp continuous_inv).congr fun g => by
      rw [Function.comp_apply, map_inv]⟩

private
theorem val_adelicArchGLIncl_apply (k : GL (Fin 2) (InfiniteAdeleRing K)) (i j : Fin 2) :
    ((adelicArchGLIncl K k : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j =
      ((k : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) i j,
        (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) i j) :=
  rfl

private
theorem continuous_val_adelicArchGLIncl :
    Continuous fun k : GL (Fin 2) (InfiniteAdeleRing K) =>
      ((adelicArchGLIncl K k : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [val_adelicArchGLIncl_apply]
  exact (Units.continuous_val.matrix_elem i j).prodMk continuous_const

private
theorem continuous_adelicArchGLIncl : Continuous (adelicArchGLIncl K) :=
  Units.continuous_iff.mpr ⟨continuous_val_adelicArchGLIncl,
    (continuous_val_adelicArchGLIncl.comp continuous_inv).congr fun g => by
      rw [Function.comp_apply, map_inv]⟩

private
theorem adelicGL_ext' {x y : AdelicGL2 (𝓞 K) K} (h₁ : glArch (𝓞 K) K x = glArch (𝓞 K) K y)
    (h₂ : glFin (𝓞 K) K x = glFin (𝓞 K) K y) : x = y := by
  refine Matrix.GeneralLinearGroup.ext fun i j => Prod.ext ?_ ?_
  · simpa only [glArch_apply] using
      congrArg (fun g : GL (Fin 2) (InfiniteAdeleRing K) => (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) i j) h₁
  · simpa only [glFin_apply] using
      congrArg (fun g : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) =>
        (g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) i j) h₂

private
theorem eq_archIncl_mul_finEmbed (x : AdelicGL2 (𝓞 K) K) :
    x = adelicArchGLIncl K (glArch (𝓞 K) K x) * AdelicDock.finEmbed (𝓞 K) K (glFin (𝓞 K) K x) :=
  adelicGL_ext'
    (by rw [map_mul, glArch_adelicArchGLIncl, AdelicDock.glArch_finEmbed, mul_one])
    (by rw [map_mul, glFin_adelicArchGLIncl, AdelicDock.glFin_finEmbed, one_mul])

open scoped Classical in
private
theorem continuous_of_isFactorizableTestFn {f : AdelicGL2 (𝓞 K) K → ℂ} (hf : IsFactorizableTestFn K f) :
    Continuous f := by
  obtain ⟨fa, ff, ⟨⟨Φ, hΦ, hfaΦ⟩, -⟩, ⟨hffl, -⟩, hfg⟩ := hf
  have hfa : Continuous fa := by
    rw [show fa = fun g => Φ (archEntries K g) from funext hfaΦ]
    refine hΦ.continuous.comp ?_
    exact continuous_pi fun i => continuous_pi fun j =>
      (continuous_ringEquiv_mixedSpace K).comp (Units.continuous_val.matrix_elem i j)
  rw [show f = fun g => fa (glArch (𝓞 K) K g) * ff (glFin (𝓞 K) K g) from funext hfg]
  exact (hfa.comp (continuous_glArch (𝓞 K) K)).mul (hffl.continuous.comp (continuous_glFin (𝓞 K) K))

private
theorem hasCompactSupport_of_isFactorizableTestFn {f : AdelicGL2 (𝓞 K) K → ℂ} (hf : IsFactorizableTestFn K f) :
    HasCompactSupport f := by
  obtain ⟨fa, ff, ⟨-, hfa⟩, ⟨-, hff⟩, hfg⟩ := hf
  have hK : IsCompact ((fun p : GL (Fin 2) (InfiniteAdeleRing K) × GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) =>
      adelicArchGLIncl K p.1 * AdelicDock.finEmbed (𝓞 K) K p.2) '' (tsupport fa ×ˢ tsupport ff)) :=
    (hfa.isCompact.prod hff.isCompact).image
      ((continuous_adelicArchGLIncl.comp continuous_fst).mul (continuous_finEmbed.comp continuous_snd))
  refine HasCompactSupport.intro hK fun x hx => ?_
  by_cases ha : glArch (𝓞 K) K x ∈ tsupport fa
  · by_cases hb : glFin (𝓞 K) K x ∈ tsupport ff
    · exact absurd ⟨(glArch (𝓞 K) K x, glFin (𝓞 K) K x), ⟨ha, hb⟩, (eq_archIncl_mul_finEmbed x).symm⟩ hx
    · exact IsFactorizableTestFn.eq_zero_of_glFin K hfg (image_eq_zero_of_notMem_tsupport hb)
  · exact IsFactorizableTestFn.eq_zero_of_glArch K hfg (image_eq_zero_of_notMem_tsupport ha)

end Basics
p2m_reactivate "P2MW.S_AutomorphicForm_exists_mem_archCutSubmodule_isIsotypicCuspFormAt_ne_zero.IsotypicArchCut P2MW.S_AutomorphicForm_exists_mem_archCutSubmodule_isIsotypicCuspFormAt_ne_zero.IsotypicArchCut.KernelSpace"

end AdelicTestFunctions
p2m_reactivate "P2MW.S_AutomorphicForm_exists_mem_archCutSubmodule_isIsotypicCuspFormAt_ne_zero.IsotypicArchCut P2MW.S_AutomorphicForm_exists_mem_archCutSubmodule_isIsotypicCuspFormAt_ne_zero.IsotypicArchCut.KernelSpace"

namespace IsotypicArchCut
namespace Main

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum AutomorphicForm
open NumberField.AdelicLevel NumberField.AdelicBox LocalGL2 HeckeIntegralSeam AdelicDock
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsotypicArchCut IsotypicArchCut.FiniteFactor IsotypicArchCut.ConjugationInvariance IsotypicArchCut.CutStep
open IsotypicArchCut.KernelSpace IsotypicArchCut.NonVanishing PrincipalCosetSystems AdelicTestFunctions

private noncomputable def bump₁ : ContDiffBump (0 : ℝ) := ⟨3, 4, by norm_num, by norm_num⟩

private noncomputable def bump₂ : ContDiffBump (1 : ℝ) := ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩

private noncomputable def β₁ : ℝ → ℝ := fun t => bump₁ t

private noncomputable def β₂ : ℝ → ℝ := fun t => bump₂ t

private theorem β₁_contDiff : ContDiff ℝ (⊤ : ℕ∞) β₁ := bump₁.contDiff

private theorem β₂_contDiff : ContDiff ℝ (⊤ : ℕ∞) β₂ := bump₂.contDiff

private theorem β₁_nonneg (t : ℝ) : 0 ≤ β₁ t := bump₁.nonneg

private theorem β₂_nonneg (t : ℝ) : 0 ≤ β₂ t := bump₂.nonneg

private theorem β₁_eq_zero (t : ℝ) (ht : (4 : ℝ) < t) : β₁ t = 0 := by
  refine bump₁.zero_of_le_dist ?_
  show (4 : ℝ) ≤ dist t 0
  rw [Real.dist_eq, sub_zero, abs_of_pos (by linarith)]
  exact ht.le

private theorem β₂_eq_zero (t : ℝ) (ht : t < (1 / 2 : ℝ)) : β₂ t = 0 := by
  refine bump₂.zero_of_le_dist ?_
  show (1 / 2 : ℝ) ≤ dist t 1
  rw [Real.dist_eq, abs_sub_comm, abs_of_pos (by linarith)]
  linarith

private theorem β₁_two : 0 < β₁ 2 := by
  have h : β₁ 2 = 1 := by
    refine bump₁.one_of_mem_closedBall ?_
    show (2 : ℝ) ∈ Metric.closedBall (0 : ℝ) 3
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero]
    norm_num
  rw [h]
  exact one_pos

private theorem β₂_one : 0 < β₂ 1 := by
  have h : β₂ 1 = 1 := by
    refine bump₂.one_of_mem_closedBall ?_
    show (1 : ℝ) ∈ Metric.closedBall (1 : ℝ) (1 / 4)
    rw [Metric.mem_closedBall, dist_self]
    norm_num
  rw [h]
  exact one_pos

section Weight

variable (F : Type) [Field F] [NumberField F]

private noncomputable def archFactorR (g : GL (Fin 2) (InfiniteAdeleRing F)) : ℝ :=
  ∏ w : InfinitePlace F, localBump β₁ β₂ (archComponent F w g : Matrix (Fin 2) (Fin 2) w.Completion)

private theorem archFactor_eq (g : GL (Fin 2) (InfiniteAdeleRing F)) :
    archFactor F β₁ β₂ g = ((archFactorR F g : ℝ) : ℂ) := by
  simp only [archFactor, archFactorR, Complex.ofReal_prod]

private theorem archFactorR_nonneg (g : GL (Fin 2) (InfiniteAdeleRing F)) : 0 ≤ archFactorR F g :=
  Finset.prod_nonneg fun _ _ => mul_nonneg (β₁_nonneg _) (β₂_nonneg _)

private theorem archFactorR_hasCompactSupport : HasCompactSupport (archFactorR F) := by
  have h : archFactorR F = fun g => (archFactor F β₁ β₂ g).re := by
    funext g
    rw [archFactor_eq, Complex.ofReal_re]
  rw [h]
  exact (hasCompactSupport_archFactor F (by norm_num : (0 : ℝ) < 1 / 2) β₁_eq_zero β₂_eq_zero).comp_left
    Complex.zero_re

omit [NumberField F] in
private theorem entrySq_one' {L : Type*} [NormedField L] : entrySq (1 : Matrix (Fin 2) (Fin 2) L) = 2 := by
  norm_num [entrySq, Matrix.one_fin_two]

private theorem archFactorR_one_pos : 0 < archFactorR F 1 := by
  unfold archFactorR
  refine Finset.prod_pos fun w _ => ?_
  rw [map_one, Units.val_one, localBump, entrySq_one', Matrix.det_one, norm_one, one_pow]
  exact mul_pos β₁_two β₂_one

private noncomputable def ffR (N : Ideal (𝓞 F)) : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) → ℝ :=
  (finPrincipal F N : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F))).indicator fun _ => (1 : ℝ)

private theorem ff_eq (N : Ideal (𝓞 F)) (h : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
    ff F N h = ((ffR F N h : ℝ) : ℂ) := by
  unfold ff ffR
  by_cases hh : h ∈ (finPrincipal F N : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)))
  · rw [Set.indicator_of_mem hh, Set.indicator_of_mem hh, Complex.ofReal_one]
  · rw [Set.indicator_of_notMem hh, Set.indicator_of_notMem hh, Complex.ofReal_zero]

private noncomputable def F₀ (N : Ideal (𝓞 F)) : AdelicGL2 (𝓞 F) F → ℂ := testFn F (archFactor F β₁ β₂) N

private noncomputable def F₀R (N : Ideal (𝓞 F)) (g : AdelicGL2 (𝓞 F) F) : ℝ :=
  archFactorR F (glArch (𝓞 F) F g) * ffR F N (glFin (𝓞 F) F g)

private theorem F₀_eq (N : Ideal (𝓞 F)) (g : AdelicGL2 (𝓞 F) F) : F₀ F N g = ((F₀R F N g : ℝ) : ℂ) := by
  simp only [F₀, testFn, F₀R, archFactor_eq, ff_eq, Complex.ofReal_mul]

private theorem F₀R_eq_re (N : Ideal (𝓞 F)) : F₀R F N = fun g => (F₀ F N g).re := by
  funext g
  rw [F₀_eq, Complex.ofReal_re]

private theorem isFactorizableTestFn_F₀ {N : Ideal (𝓞 F)} (hN : N ≠ ⊥) : IsFactorizableTestFn F (F₀ F N) :=
  ⟨archFactor F β₁ β₂, ff F N,
    ⟨archFactor_smooth F β₁_contDiff β₂_contDiff,
      hasCompactSupport_archFactor F (by norm_num : (0 : ℝ) < 1 / 2) β₁_eq_zero β₂_eq_zero⟩,
    isFinTestFactor_indicator_finPrincipal F hN, fun _ => rfl⟩

private theorem F₀_continuous {N : Ideal (𝓞 F)} (hN : N ≠ ⊥) : Continuous (F₀ F N) :=
  continuous_of_isFactorizableTestFn (isFactorizableTestFn_F₀ F hN)

private theorem F₀_hasCompactSupport {N : Ideal (𝓞 F)} (hN : N ≠ ⊥) : HasCompactSupport (F₀ F N) :=
  hasCompactSupport_of_isFactorizableTestFn (isFactorizableTestFn_F₀ F hN)

private theorem F₀R_continuous {N : Ideal (𝓞 F)} (hN : N ≠ ⊥) : Continuous (F₀R F N) := by
  rw [F₀R_eq_re]
  exact Complex.continuous_re.comp (F₀_continuous F hN)

private theorem F₀R_hasCompactSupport {N : Ideal (𝓞 F)} (hN : N ≠ ⊥) : HasCompactSupport (F₀R F N) := by
  rw [F₀R_eq_re]
  exact (F₀_hasCompactSupport F hN).comp_left Complex.zero_re

private theorem F₀R_nonneg (N : Ideal (𝓞 F)) (g : AdelicGL2 (𝓞 F) F) : 0 ≤ F₀R F N g :=
  mul_nonneg (archFactorR_nonneg F _) (Set.indicator_nonneg (fun _ _ => zero_le_one) _)

private theorem F₀R_one_pos (N : Ideal (𝓞 F)) : 0 < F₀R F N 1 := by
  unfold F₀R
  rw [map_one, map_one]
  have h : ffR F N 1 = 1 := Set.indicator_of_mem (finPrincipal F N).one_mem _
  rw [h, mul_one]
  exact archFactorR_one_pos F

private theorem F₀_inv_incl_mul (N : Ideal (𝓞 F)) (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion)
    (y : AdelicGL2 (𝓞 F) F) : F₀ F N ((rowIsometryInclAt₀ F w k)⁻¹ * y) = F₀ F N y := by
  simp only [F₀, testFn]
  rw [map_mul, map_inv, glArch_rowIsometryInclAt₀, archFactor_inv_incl_mul, map_mul, map_inv,
    glFin_rowIsometryInclAt₀, inv_one, one_mul]

private noncomputable def dispArchR (a : GL (Fin 2) (InfiniteAdeleRing F)) : ℝ :=
  ∑ w : InfinitePlace F, entrySq ((archComponent F w a : Matrix (Fin 2) (Fin 2) w.Completion) - 1)

private noncomputable def dispR (g : AdelicGL2 (𝓞 F) F) : ℝ := dispArchR F (glArch (𝓞 F) F g)

private theorem disp_eq_ofReal (g : AdelicGL2 (𝓞 F) F) : disp F g = ((dispR F g : ℝ) : ℂ) := rfl

private theorem dispArch_glArch (g : AdelicGL2 (𝓞 F) F) :
    dispArch F (glArch (𝓞 F) F g) = ((dispR F g : ℝ) : ℂ) := rfl

private theorem disp_eq_dispArch (g : AdelicGL2 (𝓞 F) F) : disp F g = dispArch F (glArch (𝓞 F) F g) := rfl

private theorem dispArchR_nonneg (a : GL (Fin 2) (InfiniteAdeleRing F)) : 0 ≤ dispArchR F a :=
  Finset.sum_nonneg fun _ _ => entrySq_nonneg _

private theorem dispR_continuous : Continuous (dispR F) := by
  have h : dispR F = fun g => (disp F g).re := by
    funext g
    rw [disp_eq_ofReal, Complex.ofReal_re]
  rw [h]
  exact Complex.continuous_re.comp (continuous_disp F)

omit [NumberField F] in
private theorem entrySq_zero' {L : Type*} [NormedField L] : entrySq (0 : Matrix (Fin 2) (Fin 2) L) = 0 := by
  simp [entrySq]

private theorem dispR_one : dispR F 1 = 0 := by
  unfold dispR dispArchR
  refine Finset.sum_eq_zero fun w _ => ?_
  rw [map_one, map_one, Units.val_one, sub_self, entrySq_zero']

omit [NumberField F] in
private theorem eq_zero_of_entrySq_eq_zero {L : Type*} [NormedField L] {m : Matrix (Fin 2) (Fin 2) L}
    (h : entrySq m = 0) : m = 0 := by
  unfold entrySq at h
  have h00 : ‖m 0 0‖ ^ 2 = 0 := by
    linarith [sq_nonneg ‖m 0 0‖, sq_nonneg ‖m 0 1‖, sq_nonneg ‖m 1 0‖, sq_nonneg ‖m 1 1‖]
  have h01 : ‖m 0 1‖ ^ 2 = 0 := by
    linarith [sq_nonneg ‖m 0 0‖, sq_nonneg ‖m 0 1‖, sq_nonneg ‖m 1 0‖, sq_nonneg ‖m 1 1‖]
  have h10 : ‖m 1 0‖ ^ 2 = 0 := by
    linarith [sq_nonneg ‖m 0 0‖, sq_nonneg ‖m 0 1‖, sq_nonneg ‖m 1 0‖, sq_nonneg ‖m 1 1‖]
  have h11 : ‖m 1 1‖ ^ 2 = 0 := by
    linarith [sq_nonneg ‖m 0 0‖, sq_nonneg ‖m 0 1‖, sq_nonneg ‖m 1 0‖, sq_nonneg ‖m 1 1‖]
  have e00 : m 0 0 = 0 := norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h00)
  have e01 : m 0 1 = 0 := norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h01)
  have e10 : m 1 0 = 0 := norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h10)
  have e11 : m 1 1 = 0 := norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h11)
  ext i j
  fin_cases i <;> fin_cases j <;> simp [e00, e01, e10, e11]

private theorem eq_one_of_dispArchR_eq_zero {a : GL (Fin 2) (InfiniteAdeleRing F)} (h : dispArchR F a = 0) :
    a = 1 := by
  have hw : ∀ w : InfinitePlace F, (archComponent F w a : Matrix (Fin 2) (Fin 2) w.Completion) = 1 := by
    intro w
    have h0 : entrySq ((archComponent F w a : Matrix (Fin 2) (Fin 2) w.Completion) - 1) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun _ _ => entrySq_nonneg _).mp h w (Finset.mem_univ w)
    exact sub_eq_zero.mp (eq_zero_of_entrySq_eq_zero h0)
  refine Units.ext ?_
  rw [Units.val_one]
  ext i j
  apply funext
  intro w
  have h2 := congrArg (fun M : Matrix (Fin 2) (Fin 2) w.Completion => M i j) (hw w)
  beta_reduce at h2
  rw [archComponent_apply] at h2
  rw [h2, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> rfl

private theorem tsupport_F₀R_subset (N : Ideal (𝓞 F)) :
    tsupport (F₀R F N) ⊆ {x | glFin (𝓞 F) F x ∈ finPrincipal F N} := by
  refine closure_minimal ?_ ((isClosed_finPrincipal F N).preimage (continuous_glFin (𝓞 F) F))
  intro x hx
  have hx' : archFactorR F (glArch (𝓞 F) F x) * ffR F N (glFin (𝓞 F) F x) ≠ 0 := hx
  have h1 : (finPrincipal F N : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F))).indicator (fun _ => (1 : ℝ))
      (glFin (𝓞 F) F x) ≠ 0 := right_ne_zero_of_mul hx'
  have hmem : glFin (𝓞 F) F x ∈ (finPrincipal F N : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F))) :=
    Set.mem_of_indicator_ne_zero h1
  exact hmem

private theorem mem_level_of_dispR_eq_zero {N : Ideal (𝓞 F)} {x : AdelicGL2 (𝓞 F) F} (hx : x ∈ tsupport (F₀R F N))
    (hd : dispR F x = 0) : x ∈ principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F := by
  have harch : glArch (𝓞 F) F x = 1 := eq_one_of_dispArchR_eq_zero F hd
  refine ⟨?_, harch⟩
  show x ∈ principalLevel (𝓞 F) F N
  rw [mem_principalLevel_iff_glFin]
  exact tsupport_F₀R_subset F N hx

private theorem ctrl {N : Ideal (𝓞 F)} {u : AdelicGL2 (𝓞 F) F → ℂ} (hN : N ≠ ⊥)
    (hlev : ∀ g : AdelicGL2 (𝓞 F) F, ∀ x ∈ principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F, u (g * x) = u g)
    (hu : Continuous u) (x₀ : AdelicGL2 (𝓞 F) F) :
    ∀ ε > 0, ∃ δ > 0, ∀ x, F₀R F N x ≠ 0 → dispR F x < δ → ‖u (x₀ * x) - u x₀‖ ≤ ε := by
  intro ε hε
  have hvar : Continuous fun x => ‖u (x₀ * x) - u x₀‖ :=
    ((hu.comp (continuous_const.mul continuous_id)).sub continuous_const).norm
  obtain ⟨S, hS⟩ : ∃ S : Set (AdelicGL2 (𝓞 F) F),
      S = tsupport (F₀R F N) ∩ {x | ε ≤ ‖u (x₀ * x) - u x₀‖} := ⟨_, rfl⟩
  have hS_compact : IsCompact S :=
    hS ▸ (F₀R_hasCompactSupport F hN).isCompact.inter_right (isClosed_le continuous_const hvar)
  have hmemS : ∀ x, x ∈ S ↔ x ∈ tsupport (F₀R F N) ∧ ε ≤ ‖u (x₀ * x) - u x₀‖ := fun x => by
    rw [hS]
    rfl
  have key : ∃ δ > 0, ∀ x ∈ tsupport (F₀R F N), dispR F x < δ → ‖u (x₀ * x) - u x₀‖ < ε := by
    by_cases hne : S.Nonempty
    · obtain ⟨x₁, hx₁S, hx₁min⟩ := hS_compact.exists_isMinOn hne (dispR_continuous F).continuousOn
      refine ⟨dispR F x₁, ?_, fun x hx hdx => ?_⟩
      · rcases (dispArchR_nonneg F (glArch (𝓞 F) F x₁)).lt_or_eq with hpos | hzero
        · exact hpos
        · exfalso
          have h1 : u (x₀ * x₁) = u x₀ :=
            hlev x₀ x₁ (mem_level_of_dispR_eq_zero F ((hmemS x₁).mp hx₁S).1 hzero.symm)
          have h2 : ε ≤ ‖u (x₀ * x₁) - u x₀‖ := ((hmemS x₁).mp hx₁S).2
          rw [h1, sub_self, norm_zero] at h2
          linarith
      · by_contra hcon
        push Not at hcon
        have hxS : x ∈ S := (hmemS x).mpr ⟨hx, hcon⟩
        have hle : dispR F x₁ ≤ dispR F x := hx₁min hxS
        linarith
    · refine ⟨1, one_pos, fun x hx _ => ?_⟩
      by_contra hcon
      push Not at hcon
      exact hne ⟨x, (hmemS x).mpr ⟨hx, hcon⟩⟩
  obtain ⟨δ, hδ, hkey⟩ := key
  exact ⟨δ, hδ, fun x hx hdx => (hkey x (subset_tsupport _ hx) hdx).le⟩

private theorem exists_local_system (v : HeightOneSpectrum (𝓞 F)) {N : Ideal (𝓞 F)} (hv : ¬ v.asIdeal ∣ N) :
    ∃ r : Fin (Ideal.absNorm v.asIdeal + 1) → GL (Fin 2) (v.adicCompletion F),
      IsHeckeCosetSystem (principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (heckeGen (𝓞 F) F v)
        (fun i => finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v (r i))) := by
  obtain ⟨ϖ, hϖ0, -, hgen, sec, -, hM⟩ := HeckeIntegralSeam.exists_isHeckeCosetSystem_localRep_heckeGen F v
  have S := hM N hv
  rw [← hgen] at S
  have S' := isHeckeCosetSystem_principal_of_not_dvd F v hv (diagPi ϖ hϖ0)
    (fun i : Option (𝓞 F ⧸ v.asIdeal) => i.elim (localRepInf ϖ hϖ0)
      (fun c => localRepSome ϖ hϖ0 (algebraMap (𝓞 F) (v.adicCompletionIntegers F) (sec c)))) S
  rw [hgen] at S'
  have habs : Ideal.absNorm v.asIdeal ≠ 0 :=
    Ideal.absNorm_ne_zero_iff_mem_nonZeroDivisors.mpr (mem_nonZeroDivisors_of_ne_zero v.ne_bot)
  haveI : Finite (𝓞 F ⧸ v.asIdeal) := (Ideal.absNorm_ne_zero_iff v.asIdeal).mp habs
  haveI : Fintype (𝓞 F ⧸ v.asIdeal) := Fintype.ofFinite _
  exact ⟨fun i => ((Fintype.equivFinOfCardEq (card_option_quotient F v)).symm i).elim (localRepInf ϖ hϖ0)
      (fun c => localRepSome ϖ hϖ0 (algebraMap (𝓞 F) (v.adicCompletionIntegers F) (sec c))),
    reindex S' (Fintype.equivFinOfCardEq (card_option_quotient F v)).symm⟩

end Weight
p2m_reactivate "P2MW.S_AutomorphicForm_exists_mem_archCutSubmodule_isIsotypicCuspFormAt_ne_zero.IsotypicArchCut P2MW.S_AutomorphicForm_exists_mem_archCutSubmodule_isIsotypicCuspFormAt_ne_zero.IsotypicArchCut.KernelSpace"

private theorem main
    (K : Type) [Field K] [NumberField K]
    (cK uK d₁K d₂K : ℝ) (TK : Finset (AdelicGL2 (𝓞 K) K))
    (hcK : 0 < cK) (hd₁K : 0 < d₁K) (hdK : d₁K < d₂K)
    (hcovK : CoversModCentre K (⋃ x ∈ TK, (· * x) '' centreCutSiegelSet K cK uK d₁K d₂K))
    (SK : Finset (HeightOneSpectrum (𝓞 K)))
    (ξ : (productionPinsOf K (⋃ x ∈ TK, (· * x) '' centreCutSiegelSet K cK uK d₁K d₂K)
        (fun N => principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)).Z →* ℂˣ)
    (N' : Ideal (𝓞 K)) (hN' : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N' → v ∈ SK)
    (π : HeckeEigensystem K ℂ) (u : AdelicGL2 (𝓞 K) K → ℂ)
    (hu : IsIsotypicCuspFormAt K
      (productionPinsOf K (⋃ x ∈ TK, (· * x) '' centreCutSiegelSet K cK uK d₁K d₂K)
        (fun N => principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) ξ N' SK π u)
    (hu0 : u ≠ 0) :
    ∃ (tys : ArchTypeFamily K) (u' : AdelicGL2 (𝓞 K) K → ℂ),
      IsIsotypicCuspFormAt K
        (productionPinsOf K (⋃ x ∈ TK, (· * x) '' centreCutSiegelSet K cK uK d₁K d₂K)
          (fun N => principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) ξ N' SK π u' ∧
      u' ∈ archCutSubmodule K tys ∧ u' ≠ 0 := by

  obtain ⟨x₀, hx₀⟩ := Function.ne_iff.mp hu0
  have hN'ne : N' ≠ ⊥ := ne_bot_of_forall_dvd_mem K hN'
  have hlev : ∀ g : AdelicGL2 (𝓞 K) K, ∀ x ∈ principalLevel (𝓞 K) K N' ⊓ finiteAdelicGL2Subgroup K,
      u (g * x) = u g := fun g x hx => hu.level_invariant g x hx

  obtain ⟨R, m, hne⟩ := exists_rightConv_ne_zero K hu.continuous hx₀ (F₀R_continuous K hN'ne)
    (F₀R_hasCompactSupport K hN'ne) (F₀R_nonneg K N') (F₀R_one_pos K N') (dispR_continuous K) (dispR_one K)
    (ctrl K hN'ne hlev hu.continuous x₀)

  obtain ⟨P, hPdef⟩ : ∃ P : AdelicGL2 (𝓞 K) K → ℂ, P = testFn K (kernelFactor K (R : ℂ) m β₁ β₂) N' := ⟨_, rfl⟩
  have hP1 : P = fun x => ((((R - dispR K x) ^ m * F₀R K N' x : ℝ)) : ℂ) := by
    funext x
    rw [hPdef]
    simp only [testFn, kernelFactor_apply, dispArch_glArch, archFactor_eq, ff_eq, F₀R]
    push_cast
    ring
  have hP2 : P = ((R : ℂ) • (1 : AdelicGL2 (𝓞 K) K → ℂ) - disp K) ^ m * F₀ K N' := by
    funext x
    rw [hPdef]
    simp only [Pi.mul_apply, Pi.pow_apply, Pi.sub_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one,
      testFn, kernelFactor_apply, disp_eq_dispArch, F₀]
    ring
  have hne' : rightConv K u P x₀ ≠ 0 := by
    rw [hP1]
    exact hne

  have hT :=
    AutomorphicForm.isIsotypicCuspFormAt_rightConv_of_isUnitFactorizableAt_of_forall_isHeckeCosetEigenfunctionAt
    K cK uK d₁K d₂K TK hcK hd₁K hdK hcovK (fun N => principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) ξ N' N' SK
    hN' π u hu
    (fun v hv => by
      obtain ⟨r, hr⟩ := exists_local_system K v (fun hdvd => hv (hN' v hdvd))
      exact ⟨r, hr, hr⟩)
    P
    (by
      rw [hPdef]
      exact isUnitFactorizableAt_testFn K (isArchTestFactor_kernelFactor K (R : ℂ) m (by norm_num : (0 : ℝ) < 1 / 2)
        β₁_contDiff β₂_contDiff β₁_eq_zero β₂_eq_zero) hN'ne hN')
    (by
      rw [hPdef]
      exact testFn_mul_left K _ N')
    (by
      rw [hPdef]
      exact tensor_conj K (kernelFactor_conj K (R : ℂ) m β₁ β₂) (ff K N'))

  have hP : P ∈ Ψ m (F₀ K N') := by
    rw [hP2]
    exact kernel_mem_Ψ m (R : ℂ) (F₀ K N')
  obtain ⟨tys, hcut⟩ := exists_rightConv_mem_archCutSubmodule K hu.continuous (Ψ m (F₀ K N'))
    (continuous_and_hasCompactSupport_of_mem_Ψ m (F₀_continuous K hN'ne) (F₀_hasCompactSupport K hN'ne))
    (translate_mem_Ψ m (F₀_inv_incl_mul K N')) hP
  exact ⟨tys, rightConv K u P, hT.1, hcut, fun h => hne' (by rw [h]; rfl)⟩

end IsotypicArchCut.Main
p2m_reactivate "P2MW.S_AutomorphicForm_exists_mem_archCutSubmodule_isIsotypicCuspFormAt_ne_zero.IsotypicArchCut P2MW.S_AutomorphicForm_exists_mem_archCutSubmodule_isIsotypicCuspFormAt_ne_zero.IsotypicArchCut.KernelSpace"
p2m_reactivate "P2MW.S_AutomorphicForm_exists_mem_archCutSubmodule_isIsotypicCuspFormAt_ne_zero.IsotypicArchCut P2MW.S_AutomorphicForm_exists_mem_archCutSubmodule_isIsotypicCuspFormAt_ne_zero.IsotypicArchCut.KernelSpace"

open AutomorphicForm AutomorphicForm.SiegelCovering AutomorphicForm.WindowedSiegel IsDedekindDomain NumberField NumberField.AdelicBox NumberField.AdelicLevel in

theorem solution
    (K : Type) [Field K] [NumberField K]
    (cK uK d₁K d₂K : ℝ) (TK : Finset (AdelicGL2 (𝓞 K) K))
    (hcK : 0 < cK) (hd₁K : 0 < d₁K) (hdK : d₁K < d₂K)
    (hcovK : CoversModCentre K (⋃ x ∈ TK, (· * x) '' centreCutSiegelSet K cK uK d₁K d₂K))
    (SK : Finset (HeightOneSpectrum (𝓞 K)))
    (ξ : (productionPinsOf K (⋃ x ∈ TK, (· * x) '' centreCutSiegelSet K cK uK d₁K d₂K)
        (fun N => principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)).Z →* ℂˣ)
    (N' : Ideal (𝓞 K)) (hN' : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N' → v ∈ SK)
    (π : HeckeEigensystem K ℂ) (u : AdelicGL2 (𝓞 K) K → ℂ)
    (hu : IsIsotypicCuspFormAt K
      (productionPinsOf K (⋃ x ∈ TK, (· * x) '' centreCutSiegelSet K cK uK d₁K d₂K)
        (fun N => principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) ξ N' SK π u)
    (hu0 : u ≠ 0) :
    ∃ (tys : ArchTypeFamily K) (u' : AdelicGL2 (𝓞 K) K → ℂ),
      IsIsotypicCuspFormAt K
        (productionPinsOf K (⋃ x ∈ TK, (· * x) '' centreCutSiegelSet K cK uK d₁K d₂K)
          (fun N => principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) ξ N' SK π u' ∧
      u' ∈ archCutSubmodule K tys ∧ u' ≠ 0 := by
  exact IsotypicArchCut.Main.main K cK uK d₁K d₂K TK hcK hd₁K hdK hcovK SK ξ N' hN' π u hu hu0

#print axioms solution

end S_AutomorphicForm_exists_mem_archCutSubmodule_isIsotypicCuspFormAt_ne_zero
end P2MW
export P2MW.S_AutomorphicForm_exists_mem_archCutSubmodule_isIsotypicCuspFormAt_ne_zero (solution)
