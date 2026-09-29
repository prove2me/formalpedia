-- Prove2me | solution 1 for AutomorphicForm.exists_forall_lintegral_semiLocalHaar_eq_mul_lintegral_pi_norm_algebraNorm_det_inv_sq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/f1a138f5-493f-588e-a07c-2c6cf9aba285

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_AdelicHaar
import Theorems.Thm_NumberField_AdicCompletion_map_linearMap_eq_norm_det_inv_smul_of_isAddHaarMeasure
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_AutomorphicForm_exists_forall_lintegral_semiLocalHaar_eq_mul_lintegral_pi_norm_algebraNorm_det_inv_sq
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "LanglandsTunnell.TateLocal.conductorExponentAt_one LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq AutomorphicForm.whittakerCoefficient_zero NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply"

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory Set Function
open scoped ENNReal NNReal TensorProduct TensorProduct.RightActions Pointwise

noncomputable section

namespace KcSemiLocalToolkit

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable {v : HeightOneSpectrum (𝓞 K)}

local notation "F" => v.adicCompletion K
local notation "E" => L ⊗[K] v.adicCompletion K

attribute [local instance 9999] Algebra.toModule

theorem isTopologicalRing_E : IsTopologicalRing E := AutomorphicForm.isTopologicalRing_tensor K L F
theorem t2Space_E : T2Space E := AutomorphicForm.t2Space_tensor K L F
theorem locallyCompactSpace_E : LocallyCompactSpace E := AutomorphicForm.locallyCompactSpace_tensor K L F
theorem continuousSMul_E : ContinuousSMul F E := IsModuleTopology.toContinuousSMul F E

attribute [local instance] isTopologicalRing_E t2Space_E locallyCompactSpace_E continuousSMul_E

theorem isTopologicalAddGroup_E : IsTopologicalAddGroup E := inferInstance

theorem isScalarTower_FEE : IsScalarTower F E E :=
  @IsScalarTower.right F E _ _ (TensorProduct.RightActions.instAlgebra_definitions K (v.adicCompletion K) L)
theorem smulCommClass_FEE : SMulCommClass F E E :=
  @Algebra.to_smulCommClass F E _ _ (TensorProduct.RightActions.instAlgebra_definitions K (v.adicCompletion K) L)

attribute [local instance] isScalarTower_FEE smulCommClass_FEE

def triv : E ≃L[F] (Fin (Module.finrank F E) → F) :=
  let e : E ≃ₗ[F] (Fin (Module.finrank F E) → F) := (Module.finBasis F E).equivFun
  { e with
    continuous_toFun := IsModuleTopology.continuous_of_linearMap e.toLinearMap
    continuous_invFun := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap }

theorem secondCountableTopology_E : SecondCountableTopology E :=
  (triv (K := K) (L := L) (v := v)).toHomeomorph.secondCountableTopology

attribute [local instance] secondCountableTopology_E

theorem continuous_algebraNorm : Continuous (Algebra.norm F : E → F) := by
  classical
  let b := Module.finBasis F E
  have h1 : Continuous fun x : E => Algebra.leftMulMatrix b x :=
    IsModuleTopology.continuous_of_linearMap (Algebra.leftMulMatrix b).toLinearMap
  have h2 : (Algebra.norm F : E → F) = fun x => (Algebra.leftMulMatrix b x).det := by
    funext x; exact Algebra.norm_eq_matrix_det b x
  rw [h2]
  exact h1.matrix_det

theorem isUnit_iff_norm_ne_zero (x : E) : IsUnit x ↔ Algebra.norm F x ≠ 0 := by
  constructor
  · intro hx h0
    obtain ⟨u, rfl⟩ := hx
    have h1 : Algebra.norm F ((u : E)) * Algebra.norm F ((u⁻¹ : Eˣ) : E) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    rw [h0, zero_mul] at h1
    exact zero_ne_one h1
  · intro h
    have hdet : LinearMap.det (Algebra.lmul F E x) ≠ 0 := by
      rwa [← Algebra.norm_apply]
    have hbij : Function.Bijective (Algebra.lmul F E x) := by
      have hu : IsUnit (Algebra.lmul F E x) :=
        (LinearMap.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hdet)
      exact (Module.End.isUnit_iff _).1 hu
    obtain ⟨y, hy⟩ := hbij.2 1
    have hy' : x * y = 1 := by
      rw [Algebra.coe_lmul_eq_mul, LinearMap.mul_apply'] at hy; exact hy
    exact IsUnit.of_mul_eq_one y hy'

section Inverse

open scoped Classical in

def adjLin : Matrix (Fin (Module.finrank F E)) (Fin (Module.finrank F E)) F →ₗ[F] E :=
  (LinearMap.applyₗ (1 : E)) ∘ₗ
    (Matrix.toLin (Module.finBasis F E) (Module.finBasis F E)).toLinearMap

open scoped Classical in

def adjE (y : E) : E := adjLin (K := K) (L := L) (v := v) (Algebra.leftMulMatrix (Module.finBasis F E) y).adjugate

theorem adjE_eq (y : E) :
    adjE y = Matrix.toLin (Module.finBasis F E) (Module.finBasis F E)
      (Algebra.leftMulMatrix (Module.finBasis F E) y).adjugate 1 := rfl

theorem mul_adjE (y : E) : y * adjE y = algebraMap F E (Algebra.norm F y) := by
  classical
  set b := Module.finBasis F E with hb
  have h1 : Matrix.toLin b b (Algebra.leftMulMatrix b y) = Algebra.lmul F E y := by
    rw [Algebra.leftMulMatrix_apply, Matrix.toLin_toMatrix]
  have h2 : Matrix.toLin b b (Algebra.leftMulMatrix b y * (Algebra.leftMulMatrix b y).adjugate) =
      (Algebra.lmul F E y) ∘ₗ Matrix.toLin b b (Algebra.leftMulMatrix b y).adjugate := by
    rw [Matrix.toLin_mul b b b, h1]
  have h3 : y * adjE y = Matrix.toLin b b
      (Algebra.leftMulMatrix b y * (Algebra.leftMulMatrix b y).adjugate) 1 := by
    rw [h2, LinearMap.comp_apply, Algebra.coe_lmul_eq_mul, LinearMap.mul_apply', adjE_eq]
  rw [h3, Matrix.mul_adjugate, map_smul, Matrix.toLin_one, LinearMap.smul_apply, LinearMap.id_apply,
    Algebra.norm_eq_matrix_det b, Algebra.algebraMap_eq_smul_one]

theorem continuous_adjE : Continuous (adjE : E → E) := by
  classical
  have h1 : Continuous fun y : E => Algebra.leftMulMatrix (Module.finBasis F E) y :=
    IsModuleTopology.continuous_of_linearMap (Algebra.leftMulMatrix (Module.finBasis F E)).toLinearMap
  haveI : IsModuleTopology F (Matrix (Fin (Module.finrank F E)) (Fin (Module.finrank F E)) F) :=
    inferInstanceAs (IsModuleTopology F (Fin (Module.finrank F E) → Fin (Module.finrank F E) → F))
  have h2 : Continuous (adjLin (K := K) (L := L) (v := v)) := IsModuleTopology.continuous_of_linearMap _
  exact h2.comp h1.matrix_adjugate

theorem ringInverse_eq {y : E} (hy : IsUnit y) :
    Ring.inverse y = (Algebra.norm F y)⁻¹ • adjE y := by
  have hN : Algebra.norm F y ≠ 0 := (isUnit_iff_norm_ne_zero y).1 hy
  have hmul := mul_adjE (K := K) (L := L) (v := v) y

  have h1 : Ring.inverse y * (y * adjE y) = adjE y := by
    rw [← mul_assoc, Ring.inverse_mul_cancel _ hy, one_mul]
  rw [hmul, Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one] at h1
  rw [← h1, smul_smul, inv_mul_cancel₀ hN, one_smul]

theorem continuous_ringInverse_comp {X : Type*} [TopologicalSpace X] {f : X → E}
    (hf : Continuous f) (hu : ∀ x, IsUnit (f x)) :
    Continuous fun x => Ring.inverse (f x) := by
  have : (fun x => Ring.inverse (f x)) = fun x => (Algebra.norm F (f x))⁻¹ • adjE (f x) := by
    funext x; exact ringInverse_eq (hu x)
  rw [this]
  refine Continuous.fun_smul ?_ (continuous_adjE.comp hf)
  refine Continuous.inv₀ (continuous_algebraNorm.comp hf) fun x => ?_
  exact (isUnit_iff_norm_ne_zero _).1 (hu x)

end Inverse

section Measure

variable [MeasurableSpace (L ⊗[K] v.adicCompletion K)] [BorelSpace (L ⊗[K] v.adicCompletion K)]
variable (ν : Measure (L ⊗[K] v.adicCompletion K)) [ν.IsAddHaarMeasure]

def wt (e : E) : ℝ≥0∞ := ENNReal.ofReal ‖Algebra.norm F e‖

omit [MeasurableSpace (L ⊗[K] v.adicCompletion K)] [BorelSpace (L ⊗[K] v.adicCompletion K)] in
theorem wt_mul (a b : E) : wt (K := K) (L := L) (v := v) (a * b) = wt a * wt b := by
  simp only [wt, map_mul, norm_mul]
  exact ENNReal.ofReal_mul (norm_nonneg _)

omit [MeasurableSpace (L ⊗[K] v.adicCompletion K)] [BorelSpace (L ⊗[K] v.adicCompletion K)] in
theorem wt_ne_zero {a : E} (ha : IsUnit a) : wt (K := K) (L := L) (v := v) a ≠ 0 := by
  simp only [wt, ne_eq, ENNReal.ofReal_eq_zero, not_le, norm_pos_iff]
  exact (isUnit_iff_norm_ne_zero a).1 ha

omit [MeasurableSpace (L ⊗[K] v.adicCompletion K)] [BorelSpace (L ⊗[K] v.adicCompletion K)] in
theorem wt_ne_top (a : E) : wt (K := K) (L := L) (v := v) a ≠ ⊤ := ENNReal.ofReal_ne_top

theorem measurable_wt : Measurable (wt : E → ℝ≥0∞) :=
  ENNReal.measurable_ofReal.comp (continuous_algebraNorm.norm).measurable

theorem map_mul_left {a : E} (ha : IsUnit a) :
    Measure.map (fun x : E => a * x) ν = (wt a)⁻¹ • ν := by
  have hdet : LinearMap.det (Algebra.lmul F E a) = Algebra.norm F a := (Algebra.norm_apply F a).symm
  have hne : LinearMap.det (Algebra.lmul F E a) ≠ 0 := by
    rw [hdet]; exact (isUnit_iff_norm_ne_zero a).1 ha
  have h := NumberField.AdicCompletion.map_linearMap_eq_norm_det_inv_smul_of_isAddHaarMeasure K v E ν
    (Algebra.lmul F E a) hne
  rw [hdet] at h
  have hfun : ((Algebra.lmul F E a : E →ₗ[F] E) : E → E) = fun x => a * x := by
    funext x; rw [Algebra.coe_lmul_eq_mul, LinearMap.mul_apply']
  rw [hfun] at h
  rw [h, wt, ENNReal.ofReal_inv_of_pos (norm_pos_iff.2 ((isUnit_iff_norm_ne_zero a).1 ha))]

def mulLeftEquiv (a : Eˣ) : E ≃ᵐ E where
  toFun x := (a : E) * x
  invFun x := ((a⁻¹ : Eˣ) : E) * x
  left_inv x := by simp [← mul_assoc]
  right_inv x := by simp [← mul_assoc]
  measurable_toFun := measurable_const_mul _
  measurable_invFun := measurable_const_mul _

theorem lintegral_comp_affine (H : E → ℝ≥0∞) {a : E} (ha : IsUnit a) (c : E) :
    ∫⁻ y, H (a * y + c) ∂ν = (wt a)⁻¹ * ∫⁻ y, H y ∂ν := by
  set e : E ≃ᵐ E := (mulLeftEquiv ha.unit).trans (MeasurableEquiv.addRight c) with he
  have hfun : (e : E → E) = (fun y => y + c) ∘ fun y => a * y := by
    funext y; simp [he, mulLeftEquiv, MeasurableEquiv.coe_addRight]
  have hmap : Measure.map e ν = (wt a)⁻¹ • ν := by
    rw [hfun, ← Measure.map_map (measurable_add_const c) (measurable_const_mul a),
      map_mul_left ν ha, Measure.map_smul, map_add_right_eq_self]
  have hfun' : ∀ y, a * y + c = e y := fun y => by rw [hfun]; rfl
  calc ∫⁻ y, H (a * y + c) ∂ν = ∫⁻ y, H (e y) ∂ν := by simp_rw [hfun']
    _ = ∫⁻ y, H y ∂(Measure.map e ν) := (lintegral_map_equiv H e).symm
    _ = (wt a)⁻¹ * ∫⁻ y, H y ∂ν := by rw [hmap, lintegral_smul_measure, smul_eq_mul]

theorem lintegral_comp_affine_mul (H : E → ℝ≥0∞) {a : E} (ha : IsUnit a) (c : E) :
    ∫⁻ y, H (a * y + c) * wt a ∂ν = ∫⁻ y, H y ∂ν := by
  rw [lintegral_mul_const' _ _ (wt_ne_top a), lintegral_comp_affine ν H ha c, mul_comm, ← mul_assoc,
    ENNReal.mul_inv_cancel (wt_ne_zero ha) (wt_ne_top a), one_mul]

omit [NumberField L] [MeasurableSpace (L ⊗[K] v.adicCompletion K)] [BorelSpace (L ⊗[K] v.adicCompletion K)] in

theorem exists_ne_zero_norm_lt_one : ∃ c : F, c ≠ 0 ∧ ‖c‖ < 1 := by
  obtain ⟨x, hxv, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
  set c : F := FinitePlace.embedding v (x : K) with hc
  have hc0 : c ≠ 0 := by
    intro h; apply hx0
    have h' : ((x : K) : F) = 0 := h
    have h2 : (x : K) = 0 := (algebraMap K F).injective (by rw [map_zero]; first | exact h' | simpa using h')
    exact_mod_cast h2
  exact ⟨c, hc0, (FinitePlace.norm_lt_one_iff_mem (K := K) v x).2 hxv⟩

theorem measure_submodule_eq_zero (W : Submodule F E) (hW : W ≠ ⊤) : ν W = 0 := by
  by_contra hpos
  have hpos' : 0 < ν W := pos_iff_ne_zero.2 hpos

  have hclosed : IsClosed (W : Set E) := by
    letI : TopologicalSpace (E ⧸ W) := moduleTopology F (E ⧸ W)
    haveI : IsModuleTopology F (E ⧸ W) := ⟨rfl⟩
    haveI : ContinuousAdd (E ⧸ W) := IsModuleTopology.toContinuousAdd F _
    haveI : ContinuousSMul F (E ⧸ W) := IsModuleTopology.toContinuousSMul F _
    haveI : T2Space (E ⧸ W) := IsModuleTopology.t2Space F
    have hc : Continuous (W.mkQ : E → E ⧸ W) := IsModuleTopology.continuous_of_linearMap W.mkQ
    have : (W : Set E) = W.mkQ ⁻¹' {0} := by
      ext x; simp [Submodule.Quotient.mk_eq_zero]
    rw [this]
    exact isClosed_singleton.preimage hc
  haveI : ν.Regular := inferInstance
  have hnhds : (W : Set E) - (W : Set E) ∈ nhds (0 : E) :=
    Measure.sub_mem_nhds_zero_of_addHaar_pos ν (W : Set E) hclosed.measurableSet hpos'
  have hsub : (W : Set E) - (W : Set E) ⊆ W := by
    rintro _ ⟨x, hx, y, hy, rfl⟩; exact W.sub_mem hx hy
  have hWn : (W : Set E) ∈ nhds (0 : E) := Filter.mem_of_superset hnhds hsub

  obtain ⟨x, hx⟩ : ∃ x : E, x ∉ W := by
    by_contra h
    push Not at h
    exact hW (eq_top_iff.2 fun x _ => h x)
  have hcont : Continuous fun c : F => c • x := continuous_id.smul continuous_const
  have htend : Filter.Tendsto (fun c : F => c • x) (nhds 0) (nhds 0) := by
    simpa using hcont.tendsto 0
  have hev : ∀ᶠ c : F in nhds 0, c • x ∈ W := htend hWn

  obtain ⟨c₀, hc₀0, hc₀1⟩ := exists_ne_zero_norm_lt_one (K := K) (v := v)
  have hpow : Filter.Tendsto (fun n : ℕ => c₀ ^ n) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one hc₀1
  obtain ⟨n, hn⟩ := (hpow.eventually hev).exists
  set c : F := c₀ ^ n with hc
  have hc0 : c ≠ 0 := pow_ne_zero n hc₀0
  have hcx : c • x ∈ W := hn
  apply hx
  have : x = c⁻¹ • (c • x) := by rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]
  rw [this]
  exact W.smul_mem c⁻¹ hcx

theorem measure_nonunits_eq_zero : ν {x : E | ¬ IsUnit x} = 0 := by
  haveI : IsArtinianRing E := IsArtinianRing.of_finite F E
  have hfin : {I : Ideal E | I.IsMaximal}.Finite := IsArtinianRing.setOf_isMaximal_finite E
  have hcover : {x : E | ¬ IsUnit x} ⊆ ⋃ I ∈ {I : Ideal E | I.IsMaximal}, (I : Set E) := by
    intro x hx
    obtain ⟨I, hI, hxI⟩ := exists_max_ideal_of_mem_nonunits (mem_nonunits_iff.2 hx)
    exact Set.mem_biUnion hI hxI
  refine measure_mono_null hcover ?_
  refine (measure_biUnion_null_iff hfin.countable).2 fun I hI => ?_

  let W : Submodule F E :=
    { carrier := (I : Set E)
      add_mem' := fun ha hb => I.add_mem ha hb
      zero_mem' := I.zero_mem
      smul_mem' := fun c x hx => by
        have h1 : c • x = algebraMap F E c * x := Algebra.smul_def c x
        show c • x ∈ I
        rw [h1]
        exact I.mul_mem_left _ hx }
  have hW : W ≠ ⊤ := by
    intro h
    apply hI.ne_top
    rw [eq_top_iff]
    intro x _
    have : x ∈ W := by rw [h]; trivial
    exact this
  exact measure_submodule_eq_zero ν W hW

end Measure

end KcSemiLocalToolkit

namespace KcSemiLocalGLHaar

open KcSemiLocalToolkit Matrix

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable {v : HeightOneSpectrum (𝓞 K)}
variable [MeasurableSpace (L ⊗[K] v.adicCompletion K)] [BorelSpace (L ⊗[K] v.adicCompletion K)]

local notation "F" => v.adicCompletion K
local notation "E" => L ⊗[K] v.adicCompletion K
local notation "P" => Fin 4 → L ⊗[K] v.adicCompletion K
local notation "G" => GL (Fin 2) (L ⊗[K] v.adicCompletion K)

attribute [local instance 9999] Algebra.toModule
attribute [local instance] isTopologicalRing_E t2Space_E locallyCompactSpace_E continuousSMul_E
  secondCountableTopology_E isScalarTower_FEE smulCommClass_FEE

open scoped Classical

def mat (x : P) : Matrix (Fin 2) (Fin 2) E := !![x 0, x 1; x 2, x 3]

def flat (M : Matrix (Fin 2) (Fin 2) E) : P := ![M 0 0, M 0 1, M 1 0, M 1 1]

omit [NumberField L] [MeasurableSpace (L ⊗[K] v.adicCompletion K)]
  [BorelSpace (L ⊗[K] v.adicCompletion K)] in
@[scoped simp] theorem mat_flat (M : Matrix (Fin 2) (Fin 2) E) : mat (flat M) = M := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

omit [NumberField L] [MeasurableSpace (L ⊗[K] v.adicCompletion K)]
  [BorelSpace (L ⊗[K] v.adicCompletion K)] in
@[scoped simp] theorem flat_mat (x : P) : flat (mat x) = x := by
  funext i; fin_cases i <;> rfl

omit [NumberField L] [MeasurableSpace (L ⊗[K] v.adicCompletion K)]
  [BorelSpace (L ⊗[K] v.adicCompletion K)] in
theorem det_mat (x : P) : (mat x).det = x 0 * x 3 - x 1 * x 2 := by
  simp [mat, Matrix.det_fin_two_of]

omit [MeasurableSpace (L ⊗[K] v.adicCompletion K)] [BorelSpace (L ⊗[K] v.adicCompletion K)] in
theorem continuous_mat : Continuous (mat : P → Matrix (Fin 2) (Fin 2) E) := by
  refine continuous_matrix fun i j => ?_
  fin_cases i <;> fin_cases j
  · exact continuous_apply 0
  · exact continuous_apply 1
  · exact continuous_apply 2
  · exact continuous_apply 3

omit [MeasurableSpace (L ⊗[K] v.adicCompletion K)] [BorelSpace (L ⊗[K] v.adicCompletion K)] in
theorem continuous_flat : Continuous (flat : Matrix (Fin 2) (Fin 2) E → P) := by
  refine continuous_pi fun i => ?_
  fin_cases i
  · exact (continuous_apply_apply 0 0)
  · exact (continuous_apply_apply 0 1)
  · exact (continuous_apply_apply 1 0)
  · exact (continuous_apply_apply 1 1)

omit [MeasurableSpace (L ⊗[K] v.adicCompletion K)] [BorelSpace (L ⊗[K] v.adicCompletion K)] in
theorem continuous_det_mat : Continuous fun x : P => (mat x).det :=
  continuous_mat.matrix_det

omit [MeasurableSpace (L ⊗[K] v.adicCompletion K)] [BorelSpace (L ⊗[K] v.adicCompletion K)] in
theorem continuous_norm_det_mat : Continuous fun x : P => Algebra.norm F (mat x).det :=
  continuous_algebraNorm.comp continuous_det_mat

def good : Set P := {x | IsUnit (mat x).det}

omit [MeasurableSpace (L ⊗[K] v.adicCompletion K)] [BorelSpace (L ⊗[K] v.adicCompletion K)] in
theorem good_eq : (good : Set P) = {x : P | Algebra.norm F (mat x).det ≠ 0} := by
  ext x; exact isUnit_iff_norm_ne_zero _

omit [MeasurableSpace (L ⊗[K] v.adicCompletion K)] [BorelSpace (L ⊗[K] v.adicCompletion K)] in
theorem isOpen_good : IsOpen (good : Set P) := by
  rw [good_eq]
  exact isOpen_ne_fun continuous_norm_det_mat continuous_const

theorem measurableSet_good : MeasurableSet (good : Set P) := isOpen_good.measurableSet

def chart (x : P) : G :=
  if h : IsUnit (mat x).det then Matrix.GeneralLinearGroup.mk'' (mat x) h else 1

omit [NumberField L] [MeasurableSpace (L ⊗[K] v.adicCompletion K)]
  [BorelSpace (L ⊗[K] v.adicCompletion K)] in
theorem chart_of_mem {x : P} (h : IsUnit (mat x).det) :
    chart x = Matrix.GeneralLinearGroup.mk'' (mat x) h := by
  simp [chart, h]

omit [NumberField L] [MeasurableSpace (L ⊗[K] v.adicCompletion K)]
  [BorelSpace (L ⊗[K] v.adicCompletion K)] in
theorem coe_chart_of_mem {x : P} (h : IsUnit (mat x).det) :
    ((chart x : G) : Matrix (Fin 2) (Fin 2) E) = mat x := by
  rw [chart_of_mem h]; rfl

omit [NumberField L] [MeasurableSpace (L ⊗[K] v.adicCompletion K)]
  [BorelSpace (L ⊗[K] v.adicCompletion K)] in
theorem chart_flat (g : G) : chart (flat (g : Matrix (Fin 2) (Fin 2) E)) = g := by
  have h : IsUnit (mat (flat (g : Matrix (Fin 2) (Fin 2) E))).det := by
    rw [mat_flat]; exact Matrix.isUnits_det_units g
  apply Units.ext
  rw [coe_chart_of_mem h, mat_flat]

omit [MeasurableSpace (L ⊗[K] v.adicCompletion K)] [BorelSpace (L ⊗[K] v.adicCompletion K)] in
theorem t2Space_GL : T2Space G := AutomorphicForm.t2Space_tensorGL K L F

omit [MeasurableSpace (L ⊗[K] v.adicCompletion K)] [BorelSpace (L ⊗[K] v.adicCompletion K)] in
theorem secondCountableTopology_GL : SecondCountableTopology G := by
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) E) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → E))
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) E)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

omit [MeasurableSpace (L ⊗[K] v.adicCompletion K)] [BorelSpace (L ⊗[K] v.adicCompletion K)] in
theorem locallyCompactSpace_GL : LocallyCompactSpace G := AutomorphicForm.locallyCompactSpace_tensorGL K L F

omit [MeasurableSpace (L ⊗[K] v.adicCompletion K)] [BorelSpace (L ⊗[K] v.adicCompletion K)] in
theorem isTopologicalGroup_GL : IsTopologicalGroup G := AutomorphicForm.isTopologicalGroup_tensorGL K L F

@[reducible] def measurableSpace_GL : MeasurableSpace G := AutomorphicForm.glBorelOf E

attribute [local instance] t2Space_GL secondCountableTopology_GL locallyCompactSpace_GL
  isTopologicalGroup_GL measurableSpace_GL

omit [MeasurableSpace (L ⊗[K] v.adicCompletion K)] [BorelSpace (L ⊗[K] v.adicCompletion K)] in
theorem borelSpace_GL : BorelSpace G := AutomorphicForm.borelSpace_glBorelOf E

omit [MeasurableSpace (L ⊗[K] v.adicCompletion K)] [BorelSpace (L ⊗[K] v.adicCompletion K)] in
private theorem _root_.KcSemiLocalGLHaar.isHaarMeasure_semiLocalHaar : (AutomorphicForm.semiLocalHaar K L v).IsHaarMeasure :=
  AutomorphicForm.isHaarMeasure_semiLocalHaar K L v

p2m_export "KcSemiLocalGLHaar" "isHaarMeasure_semiLocalHaar"
attribute [local instance] borelSpace_GL isHaarMeasure_semiLocalHaar

omit [MeasurableSpace (L ⊗[K] v.adicCompletion K)] [BorelSpace (L ⊗[K] v.adicCompletion K)] in
theorem measurableMul_GL : MeasurableMul G := inferInstance

theorem borelSpace_P : BorelSpace P := inferInstance
theorem opensMeasurableSpace_P : OpensMeasurableSpace P := inferInstance
theorem opensMeasurableSpace_good : OpensMeasurableSpace (good : Set P) := inferInstance

attribute [local instance] measurableMul_GL borelSpace_P opensMeasurableSpace_P opensMeasurableSpace_good

theorem continuous_GL_of {X : Type*} [TopologicalSpace X] {f : X → G}
    (hval : ∀ i j, Continuous fun x => ((f x : G) : Matrix (Fin 2) (Fin 2) E) i j)
    (hinv : ∀ i j, Continuous fun x => (((f x)⁻¹ : G) : Matrix (Fin 2) (Fin 2) E) i j) :
    Continuous f := by
  rw [Units.continuous_iff]
  exact ⟨continuous_matrix fun i j => hval i j, continuous_matrix fun i j => hinv i j⟩

omit [NumberField L] [MeasurableSpace (L ⊗[K] v.adicCompletion K)]
  [BorelSpace (L ⊗[K] v.adicCompletion K)] in

theorem coe_chart_inv_of_mem {x : P} (h : IsUnit (mat x).det) :
    (((chart x)⁻¹ : G) : Matrix (Fin 2) (Fin 2) E) = Ring.inverse (mat x).det • (mat x).adjugate := by
  rw [Matrix.coe_units_inv, coe_chart_of_mem h, Matrix.inv_def]

theorem continuousOn_ringInverse_det :
    Continuous fun x : (good : Set P) => Ring.inverse (mat (x : P)).det :=
  continuous_ringInverse_comp (continuous_det_mat.comp continuous_subtype_val) fun x => x.2

theorem continuous_chart_restrict : Continuous ((good : Set P).domRestrict (chart : P → G)) := by
  have hent : ∀ i j, Continuous fun x : (good : Set P) => mat (x : P) i j := fun i j =>
    (continuous_mat.matrix_elem i j).comp continuous_subtype_val
  refine continuous_GL_of (fun i j => ?_) (fun i j => ?_)
  · have : (fun x : (good : Set P) => (((good : Set P).domRestrict chart x : G) : Matrix (Fin 2) (Fin 2) E) i j)
        = fun x : (good : Set P) => mat (x : P) i j := by
      funext x; rw [Set.restrict_apply, coe_chart_of_mem x.2]
    rw [this]; exact hent i j
  · have : (fun x : (good : Set P) =>
        ((((good : Set P).domRestrict chart x)⁻¹ : G) : Matrix (Fin 2) (Fin 2) E) i j)
        = fun x : (good : Set P) => Ring.inverse (mat (x : P)).det * (mat (x : P)).adjugate i j := by
      funext x
      rw [Set.restrict_apply, coe_chart_inv_of_mem x.2, Matrix.smul_apply, smul_eq_mul]
    rw [this]
    refine continuousOn_ringInverse_det.mul ?_
    have hadj : Continuous fun x : (good : Set P) => (mat (x : P)).adjugate :=
      (continuous_mat.comp continuous_subtype_val).matrix_adjugate
    exact hadj.matrix_elem i j

theorem measurable_chart : Measurable (chart : P → G) := by
  refine measurable_of_restrict_of_restrict_compl measurableSet_good ?_ ?_
  · exact continuous_chart_restrict.measurable
  · have : (goodᶜ : Set P).domRestrict (chart : P → G) = fun _ => 1 := by
      funext x
      have hx : ¬ IsUnit (mat (x : P)).det := x.2
      simp [Set.restrict_apply, chart, hx]
    rw [this]; exact measurable_const

theorem measurable_flat_coe : Measurable fun g : G => flat (g : Matrix (Fin 2) (Fin 2) E) :=
  (continuous_flat.comp Units.continuous_val).measurable

def Lmat (g : Matrix (Fin 2) (Fin 2) E) : Matrix (Fin 4) (Fin 4) E :=
  !![g 0 0, 0, g 0 1, 0; 0, g 0 0, 0, g 0 1; g 1 0, 0, g 1 1, 0; 0, g 1 0, 0, g 1 1]

omit [NumberField L] [MeasurableSpace (L ⊗[K] v.adicCompletion K)]
  [BorelSpace (L ⊗[K] v.adicCompletion K)] in
theorem mat_Lmat_mulVec (g : Matrix (Fin 2) (Fin 2) E) (x : P) :
    mat ((Lmat g).mulVec x) = g * mat x := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [mat, Lmat, Matrix.mulVec, dotProduct, Fin.sum_univ_four, Matrix.mul_apply, Fin.sum_univ_two,
      mul_comm]

omit [NumberField L] [MeasurableSpace (L ⊗[K] v.adicCompletion K)]
  [BorelSpace (L ⊗[K] v.adicCompletion K)] in
theorem det_Lmat (g : Matrix (Fin 2) (Fin 2) E) : (Lmat g).det = g.det ^ 2 := by
  simp [Lmat, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  ring

theorem measurable_Lmat_mulVec (g : Matrix (Fin 2) (Fin 2) E) :
    Measurable fun x : P => (Lmat g).mulVec x :=
  (continuous_const.matrix_mulVec continuous_id).measurable

section CV

variable (ν : Measure (L ⊗[K] v.adicCompletion K)) [ν.IsAddHaarMeasure]

local notation "π" => Measure.pi fun _ : Fin 4 => ν

theorem map_mulVec {M : Matrix (Fin 4) (Fin 4) E} (hM : IsUnit M.det) :
    Measure.map (fun x : P => M.mulVec x) π =
      ENNReal.ofReal ‖Algebra.norm F M.det‖⁻¹ • π := by

  set T : P →ₗ[F] P := (Matrix.mulVecLin M).restrictScalars F with hT
  have hTdet : LinearMap.det T = Algebra.norm F M.det := by
    rw [hT, LinearMap.det_restrictScalars]
    congr 1
    rw [show Matrix.mulVecLin M = Matrix.toLin' M from rfl, LinearMap.det_toLin']
  have hTne : LinearMap.det T ≠ 0 := by
    rw [hTdet]; exact (isUnit_iff_norm_ne_zero _).1 hM
  haveI : IsModuleTopology F P := IsModuleTopology.instPi
  haveI : (π).IsAddHaarMeasure := inferInstance
  have h := NumberField.AdicCompletion.map_linearMap_eq_norm_det_inv_smul_of_isAddHaarMeasure K v P π T hTne
  have hfun : (T : P → P) = fun x => M.mulVec x := by
    funext x; rfl
  rw [hfun, hTdet] at h
  exact h

end CV

section Main

variable (ν : Measure (L ⊗[K] v.adicCompletion K)) [ν.IsAddHaarMeasure]

local notation "π" => Measure.pi fun _ : Fin 4 => ν

def Dinv (x : P) : ℝ≥0∞ := ENNReal.ofReal ((‖Algebra.norm F (mat x).det‖ ^ 2)⁻¹)

theorem measurable_Dinv : Measurable (Dinv : P → ℝ≥0∞) :=
  ENNReal.measurable_ofReal.comp ((continuous_norm_det_mat.norm.pow 2).measurable.inv)

omit [MeasurableSpace (L ⊗[K] v.adicCompletion K)] [BorelSpace (L ⊗[K] v.adicCompletion K)] in
theorem Dinv_ne_zero {x : P} (hx : x ∈ good) : Dinv x ≠ 0 := by
  simp only [Dinv, ne_eq, ENNReal.ofReal_eq_zero, not_le]
  have : 0 < ‖Algebra.norm F (mat x).det‖ := norm_pos_iff.2 ((isUnit_iff_norm_ne_zero _).1 hx)
  positivity

def m : Measure G := Measure.map chart (((π).restrict good).withDensity Dinv)

theorem lintegral_m {H : G → ℝ≥0∞} (hH : Measurable H) :
    ∫⁻ g, H g ∂(m ν) = ∫⁻ x in good, H (chart x) * Dinv x ∂π := by
  rw [m, lintegral_map hH measurable_chart]
  rw [show (fun a => H (chart a)) = H ∘ chart from rfl,
    lintegral_withDensity_eq_lintegral_mul _ measurable_Dinv (hH.comp measurable_chart)]
  refine lintegral_congr fun x => ?_
  simp only [Pi.mul_apply, Function.comp_apply, mul_comm]

theorem m_apply {A : Set G} (hA : MeasurableSet A) :
    m ν A = ∫⁻ x in good, A.indicator 1 (chart x) * Dinv x ∂π := by
  rw [← lintegral_indicator_one hA, lintegral_m ν (measurable_one.indicator hA)]

omit [MeasurableSpace (L ⊗[K] v.adicCompletion K)] [BorelSpace (L ⊗[K] v.adicCompletion K)] in

theorem chart_Lmat_mulVec (g : G) {x : P} (hx : x ∈ good) :
    chart ((Lmat (g : Matrix (Fin 2) (Fin 2) E)).mulVec x) = g * chart x := by
  have hdet : IsUnit (mat ((Lmat (g : Matrix (Fin 2) (Fin 2) E)).mulVec x)).det := by
    rw [mat_Lmat_mulVec, Matrix.det_mul]
    exact (Matrix.isUnits_det_units g).mul hx
  apply Units.ext
  rw [coe_chart_of_mem hdet, mat_Lmat_mulVec, Units.val_mul, coe_chart_of_mem hx]

omit [MeasurableSpace (L ⊗[K] v.adicCompletion K)] [BorelSpace (L ⊗[K] v.adicCompletion K)] in
theorem mem_good_Lmat_mulVec_iff (g : G) (x : P) :
    (Lmat (g : Matrix (Fin 2) (Fin 2) E)).mulVec x ∈ good ↔ x ∈ good := by
  simp only [good, mem_setOf_eq, mat_Lmat_mulVec, Matrix.det_mul]
  constructor
  · intro h
    exact isUnit_of_mul_isUnit_right h
  · intro h
    exact (Matrix.isUnits_det_units g).mul h

omit [MeasurableSpace (L ⊗[K] v.adicCompletion K)] [BorelSpace (L ⊗[K] v.adicCompletion K)] in
theorem Dinv_Lmat_mulVec (g : G) (x : P) :
    Dinv ((Lmat (g : Matrix (Fin 2) (Fin 2) E)).mulVec x) =
      ENNReal.ofReal ((‖Algebra.norm F (g : Matrix (Fin 2) (Fin 2) E).det‖ ^ 2)⁻¹) * Dinv x := by
  simp only [Dinv, mat_Lmat_mulVec, Matrix.det_mul, map_mul, norm_mul, mul_pow, mul_inv]
  rw [ENNReal.ofReal_mul (by positivity)]

omit [MeasurableSpace (L ⊗[K] v.adicCompletion K)] [BorelSpace (L ⊗[K] v.adicCompletion K)] in

theorem cg_ne_zero (g : G) :
    ENNReal.ofReal ((‖Algebra.norm F (g : Matrix (Fin 2) (Fin 2) E).det‖ ^ 2)⁻¹) ≠ 0 := by
  simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
  have : 0 < ‖Algebra.norm F (g : Matrix (Fin 2) (Fin 2) E).det‖ :=
    norm_pos_iff.2 ((isUnit_iff_norm_ne_zero _).1 (Matrix.isUnits_det_units g))
  positivity

theorem setLIntegral_comp_mul_left (g : G) {A : Set G} (hA : MeasurableSet A) :
    ∫⁻ x in good, A.indicator 1 (g * chart x) * Dinv x ∂π =
      ∫⁻ x in good, A.indicator 1 (chart x) * Dinv x ∂π := by
  set Lg : Matrix (Fin 4) (Fin 4) E := Lmat (g : Matrix (Fin 2) (Fin 2) E) with hL
  have hLdet : IsUnit Lg.det := by
    rw [hL, det_Lmat]; exact (Matrix.isUnits_det_units g).pow 2
  set cg : ℝ≥0∞ := ENNReal.ofReal ((‖Algebra.norm F (g : Matrix (Fin 2) (Fin 2) E).det‖ ^ 2)⁻¹) with hcg

  have hmap := map_mulVec ν hLdet
  have hnorm : ENNReal.ofReal ‖Algebra.norm F Lg.det‖⁻¹ = cg := by
    rw [hcg, hL, det_Lmat, map_pow, norm_pow]
  rw [hnorm] at hmap
  set Hh : P → ℝ≥0∞ := good.indicator fun x => A.indicator 1 (chart x) * Dinv x with hHh
  have hHm : Measurable Hh := by
    refine Measurable.indicator ?_ measurableSet_good
    exact ((measurable_one.indicator hA).comp measurable_chart).mul measurable_Dinv

  have h1 : ∫⁻ x, Hh (Lg.mulVec x) ∂π = cg * ∫⁻ x, Hh x ∂π := by
    have hlm : ∫⁻ x, Hh x ∂(Measure.map (fun x : P => Lg.mulVec x) π) = ∫⁻ x, Hh (Lg.mulVec x) ∂π :=
      lintegral_map hHm (measurable_Lmat_mulVec _)
    rw [hmap, lintegral_smul_measure, smul_eq_mul] at hlm
    exact hlm.symm

  have h2 : ∀ x : P, Hh (Lg.mulVec x) =
      cg * good.indicator (fun x => A.indicator 1 (g * chart x) * Dinv x) x := by
    intro x
    by_cases hx : x ∈ good
    · rw [hHh, indicator_of_mem ((mem_good_Lmat_mulVec_iff g x).2 hx), indicator_of_mem hx,
        chart_Lmat_mulVec g hx, Dinv_Lmat_mulVec, ← hcg]
      ring
    · rw [hHh, indicator_of_notMem (fun h => hx ((mem_good_Lmat_mulVec_iff g x).1 h)),
        indicator_of_notMem hx, mul_zero]
  simp_rw [h2] at h1
  rw [lintegral_const_mul _ (by
      refine Measurable.indicator ?_ measurableSet_good
      exact ((measurable_one.indicator hA).comp ((measurable_const_mul g).comp measurable_chart)).mul
        measurable_Dinv)] at h1
  have h3 := (ENNReal.mul_right_inj (cg_ne_zero g) ENNReal.ofReal_ne_top).1 h1
  rw [lintegral_indicator measurableSet_good, hHh, lintegral_indicator measurableSet_good] at h3
  exact h3

theorem isMulLeftInvariant_m : (m ν).IsMulLeftInvariant := by
  refine ⟨fun g => ?_⟩
  ext A hA
  rw [Measure.map_apply (measurable_const_mul g) hA, m_apply ν hA,
    m_apply ν (measurable_const_mul g hA)]
  have : ∀ x : P, ((fun h : G => g * h) ⁻¹' A).indicator (1 : G → ℝ≥0∞) (chart x) =
      A.indicator 1 (g * chart x) := by
    intro x
    simp only [Set.indicator, mem_preimage, Pi.one_apply]
  simp_rw [this]
  exact setLIntegral_comp_mul_left ν g hA

theorem isFiniteMeasureOnCompacts_m : IsFiniteMeasureOnCompacts (m ν) := by
  refine ⟨fun C hC => ?_⟩
  rw [m_apply ν hC.measurableSet]
  by_cases hCe : C = ∅
  · subst hCe; simp

  have hne : C.Nonempty := Set.nonempty_iff_ne_empty.2 hCe
  have hcont : Continuous fun g : G => ‖Algebra.norm F ((g : G) : Matrix (Fin 2) (Fin 2) E).det‖ :=
    (continuous_algebraNorm.comp ((Units.continuous_val (M := Matrix (Fin 2) (Fin 2) E)).matrix_det)).norm
  obtain ⟨g₀, hg₀, hmin⟩ := hC.exists_isMinOn hne (hcont.continuousOn (s := C))
  set δ : ℝ := ‖Algebra.norm F ((g₀ : G) : Matrix (Fin 2) (Fin 2) E).det‖ with hδ
  have hδ0 : 0 < δ :=
    norm_pos_iff.2 ((isUnit_iff_norm_ne_zero _).1 (Matrix.isUnits_det_units g₀))

  set Cf : Set P := (fun g : G => flat (g : Matrix (Fin 2) (Fin 2) E)) '' C with hCf
  have hCfc : IsCompact Cf := hC.image (continuous_flat.comp Units.continuous_val)
  have hbound : ∀ x : P, good.indicator (fun x => C.indicator (1 : G → ℝ≥0∞) (chart x) * Dinv x) x ≤
      Cf.indicator (fun _ => ENNReal.ofReal ((δ ^ 2)⁻¹)) x := by
    intro x
    by_cases hx : x ∈ good
    · rw [indicator_of_mem hx]
      by_cases hxC : chart x ∈ C
      · have hxCf : x ∈ Cf := by
          refine ⟨chart x, hxC, ?_⟩
          show flat ((chart x : G) : Matrix (Fin 2) (Fin 2) E) = x
          rw [coe_chart_of_mem hx, flat_mat]
        rw [indicator_of_mem hxC, indicator_of_mem hxCf, Pi.one_apply, one_mul]
        simp only [Dinv]
        apply ENNReal.ofReal_le_ofReal
        have hle : δ ≤ ‖Algebra.norm F (mat x).det‖ := by
          have := hmin hxC
          simp only [mem_setOf_eq] at this
          rw [coe_chart_of_mem hx] at this
          exact this
        have h1 : δ ^ 2 ≤ ‖Algebra.norm F (mat x).det‖ ^ 2 := by gcongr
        exact inv_anti₀ (by positivity) h1
      · rw [indicator_of_notMem hxC, zero_mul]; exact zero_le
    · rw [indicator_of_notMem hx]; exact zero_le
  calc ∫⁻ x in good, C.indicator (1 : G → ℝ≥0∞) (chart x) * Dinv x ∂π
      = ∫⁻ x, good.indicator (fun x => C.indicator (1 : G → ℝ≥0∞) (chart x) * Dinv x) x ∂π := by
        rw [lintegral_indicator measurableSet_good]
    _ ≤ ∫⁻ x, Cf.indicator (fun _ => ENNReal.ofReal ((δ ^ 2)⁻¹)) x ∂π := lintegral_mono hbound
    _ = ENNReal.ofReal ((δ ^ 2)⁻¹) * π Cf := lintegral_indicator_const hCfc.measurableSet _
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hCfc.measure_lt_top

theorem m_univ_ne_zero : m ν Set.univ ≠ 0 := by
  rw [m_apply ν MeasurableSet.univ]
  simp only [indicator_univ, Pi.one_apply, one_mul]
  intro h
  rw [← lintegral_indicator measurableSet_good,
    lintegral_eq_zero_iff (measurable_Dinv.indicator measurableSet_good)] at h

  have h1 : flat (1 : Matrix (Fin 2) (Fin 2) E) ∈ (good : Set P) := by
    show IsUnit (mat (flat (1 : Matrix (Fin 2) (Fin 2) E))).det
    rw [mat_flat, Matrix.det_one]; exact isUnit_one
  have hpos : 0 < π good := isOpen_good.measure_pos π ⟨_, h1⟩
  have hae : ∀ᵐ x ∂π, x ∉ good := by
    filter_upwards [h] with x hx
    intro hxg
    rw [Pi.zero_apply, indicator_of_mem hxg] at hx
    exact Dinv_ne_zero hxg hx
  rw [← measure_eq_zero_iff_ae_notMem] at hae
  exact absurd hae hpos.ne'

theorem main : ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧
    ∀ H : G → ℝ≥0∞, Measurable H →
      ∫⁻ g, H g ∂(AutomorphicForm.semiLocalHaar K L v) = c * ∫⁻ x in good, H (chart x) * Dinv x ∂π := by
  haveI := isMulLeftInvariant_m ν
  haveI := isFiniteMeasureOnCompacts_m ν
  have heq := Measure.isMulLeftInvariant_eq_smul (m ν) (AutomorphicForm.semiLocalHaar K L v)
  set c₀ : ℝ≥0 := (m ν).haarScalarFactor (AutomorphicForm.semiLocalHaar K L v) with hc₀
  have hc₀0 : c₀ ≠ 0 := by
    intro h0
    apply m_univ_ne_zero ν
    rw [heq, h0]; simp
  refine ⟨(c₀ : ℝ≥0∞)⁻¹, ENNReal.inv_ne_zero.2 ENNReal.coe_ne_top,
    ENNReal.inv_ne_top.2 (ENNReal.coe_ne_zero.2 hc₀0), fun H hH => ?_⟩
  rw [← lintegral_m ν hH, heq, lintegral_smul_measure, ENNReal.smul_def, smul_eq_mul, ← mul_assoc,
    ENNReal.inv_mul_cancel (ENNReal.coe_ne_zero.2 hc₀0) ENNReal.coe_ne_top, one_mul]

theorem integrand_eq (H : G → ℝ≥0∞) :
    ∫⁻ x in good, H (chart x) * Dinv x ∂π =
      ∫⁻ x : P, (if h : IsUnit (mat x).det then H (Matrix.GeneralLinearGroup.mk'' _ h) else 0) *
        ENNReal.ofReal ((‖Algebra.norm F (mat x).det‖ ^ 2)⁻¹) ∂π := by
  rw [← lintegral_indicator measurableSet_good]
  refine lintegral_congr fun x => ?_
  by_cases hx : IsUnit (mat x).det
  · rw [indicator_of_mem (show x ∈ good from hx), dif_pos hx, chart_of_mem hx]; rfl
  · rw [indicator_of_notMem (show x ∉ good from hx), dif_neg hx, zero_mul]

end Main

end KcSemiLocalGLHaar
p2m_reactivate "P2MW.S_AutomorphicForm_exists_forall_lintegral_semiLocalHaar_eq_mul_lintegral_pi_norm_algebraNorm_det_inv_sq.KcSemiLocalGLHaar"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_forall_lintegral_semiLocalHaar_eq_mul_lintegral_pi_norm_algebraNorm_det_inv_sq.KcSemiLocalGLHaar"

open scoped Classical in
open KcSemiLocalGLHaar in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K))
    [MeasurableSpace (L ⊗[K] v.adicCompletion K)] [BorelSpace (L ⊗[K] v.adicCompletion K)]
    (ν : Measure (L ⊗[K] v.adicCompletion K)) [ν.IsAddHaarMeasure] :
    ∃ c : ENNReal, c ≠ 0 ∧ c ≠ ⊤ ∧
      ∀ H : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ENNReal,
        Measurable[AutomorphicForm.glBorelOf (L ⊗[K] v.adicCompletion K)] H →
        (letI := AutomorphicForm.glBorelOf (L ⊗[K] v.adicCompletion K)
         ∫⁻ g, H g ∂(AutomorphicForm.semiLocalHaar K L v)) =
          c * ∫⁻ x : Fin 4 → L ⊗[K] v.adicCompletion K,
            (if h : IsUnit (!![x 0, x 1; x 2, x 3] :
                Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)).det then
                H (Matrix.GeneralLinearGroup.mk'' _ h) else 0) *
              ENNReal.ofReal
                ((‖Algebra.norm (v.adicCompletion K) (!![x 0, x 1; x 2, x 3] :
                    Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)).det‖ ^ 2)⁻¹)
            ∂(Measure.pi fun _ : Fin 4 => ν) := by
  obtain ⟨c, hc0, hct, h⟩ := main (K := K) (L := L) (v := v) ν
  refine ⟨c, hc0, hct, fun H hH => ?_⟩
  rw [h H hH, integrand_eq]
  rfl

end S_AutomorphicForm_exists_forall_lintegral_semiLocalHaar_eq_mul_lintegral_pi_norm_algebraNorm_det_inv_sq
end P2MW
export P2MW.S_AutomorphicForm_exists_forall_lintegral_semiLocalHaar_eq_mul_lintegral_pi_norm_algebraNorm_det_inv_sq (solution)
