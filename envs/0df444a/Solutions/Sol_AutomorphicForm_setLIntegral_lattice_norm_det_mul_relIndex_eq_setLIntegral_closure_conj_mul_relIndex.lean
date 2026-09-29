-- Prove2me | solution 1 for AutomorphicForm.setLIntegral_lattice_norm_det_mul_relIndex_eq_setLIntegral_closure_conj_mul_relIndex
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/001aeee0-7a9c-5644-83bb-a6fbee98b35f

import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_AutomorphicForm_TwistedCommutant
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_GodementSection
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_TateGlobalZeta
import Theorems.Thm_NumberField_AdicCompletion_map_linearMap_eq_norm_det_inv_smul_of_isAddHaarMeasure
import Theorems.Thm_AutomorphicForm_exists_homeomorph_twistedCommutant_map_mul_scalar_forall_coe_eq_sum_map_tmul_of_linearIndependent
import Theorems.Thm_AutomorphicForm_setLIntegral_twistedCentralizer_norm_det_mul_measure_pi_integers_eq_setLIntegral_lattice_mul_measure_preimage_of_isAddHaarMeasure
import Theorems.Thm_AutomorphicForm_measure_setOf_algebraNorm_det_sum_map_tmul_eq_zero_eq_zero_of_isUnit
import Theorems.Thm_AutomorphicForm_exists_linearIndependent_forall_mul_eq_mul_map_iff_mem_span_of_normString_eq_toTensorGL_centralScalar_of_forall_ne_scalar
import Theorems.Thm_MeasureTheory_Measure_measure_coe_eq_relIndex_mul_of_le_of_isAddLeftInvariant
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
p2m_attr_erase "ext" "NumberField.InfinitePlace.Completion.ext"
namespace P2MW.S_AutomorphicForm_setLIntegral_lattice_norm_det_mul_relIndex_eq_setLIntegral_closure_conj_mul_relIndex
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "LanglandsTunnell.TateLocal.conductorExponentAt_one LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply"

set_option autoImplicit false

open MeasureTheory Filter NumberField NumberField.AdelicHaar NumberField.AdelicFourier NumberField.AdelicBox NumberField.TateGlobal IsDedekindDomain AutomorphicForm

open scoped TensorProduct TensorProduct.RightActions ENNReal Topology SchwartzMap

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel
  AutomorphicForm.twistedCentralizerBorel

open scoped Classical

open Set Function
open scoped Pointwise NNReal

noncomputable section

namespace L1Toolkit

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
  refine Continuous.fun_smul (Continuous.inv₀ (continuous_algebraNorm.comp hf) fun x => ?_) (continuous_adjE.comp hf)
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
    have h2 : (x : K) = 0 := (algebraMap K F).injective (by rw [map_zero]; exact h')
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

end L1Toolkit

namespace L1Main

open L1Toolkit Matrix

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable {v : HeightOneSpectrum (𝓞 K)}

local notation "F" => v.adicCompletion K
local notation "E" => L ⊗[K] v.adicCompletion K
local notation "M2" => Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)
local notation "G" => GL (Fin 2) (L ⊗[K] v.adicCompletion K)

attribute [local instance 9999] Algebra.toModule
attribute [local instance] isTopologicalRing_E t2Space_E locallyCompactSpace_E continuousSMul_E
  secondCountableTopology_E isScalarTower_FEE smulCommClass_FEE

variable (σ : L ≃ₐ[K] L) (δ₀ : GL (Fin 2) L) (c : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ)

abbrev δv : G :=
  AutomorphicForm.tensorPlace K L v (Matrix.GeneralLinearGroup.map
    (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
    Matrix.GeneralLinearGroup.scalar (Fin 2) c)

def cv : (L ⊗[K] v.adicCompletion K)ˣ :=
  Units.map (AutomorphicForm.tensorPlaceHom K L v).toRingHom.toMonoidHom c

theorem tensorPlaceHom_includeLeft (l : L) :
    AutomorphicForm.tensorPlaceHom K L v
      ((Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) l) =
      (Algebra.TensorProduct.includeLeftRingHom : L →+* E) l := by
  show AutomorphicForm.tensorPlaceHom K L v (l ⊗ₜ[K] (1 : AdeleRing (𝓞 K) K)) = l ⊗ₜ[K] (1 : F)
  rw [AutomorphicForm.tensorPlaceHom_tmul]
  rfl

theorem tensorPlace_map_includeLeft :
    AutomorphicForm.tensorPlace K L v (Matrix.GeneralLinearGroup.map
      (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀) =
      Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* E) δ₀ := by
  apply Units.ext
  ext i j
  show AutomorphicForm.tensorPlaceHom K L v
      ((Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) ((δ₀ : Matrix (Fin 2) (Fin 2) L) i j)) =
    (Algebra.TensorProduct.includeLeftRingHom : L →+* E) ((δ₀ : Matrix (Fin 2) (Fin 2) L) i j)
  exact tensorPlaceHom_includeLeft (v := v) _

theorem tensorPlace_scalar :
    AutomorphicForm.tensorPlace K L v (Matrix.GeneralLinearGroup.scalar (Fin 2) c) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (cv (v := v) c) := by
  apply Units.ext
  ext i j
  show AutomorphicForm.tensorPlaceHom K L v
      (((Matrix.GeneralLinearGroup.scalar (Fin 2) c : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) :
        Matrix (Fin 2) (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) i j) =
    ((Matrix.GeneralLinearGroup.scalar (Fin 2) (cv (v := v) c) : G) : M2) i j
  by_cases hij : i = j
  · subst hij
    simp [Matrix.GeneralLinearGroup.scalar, cv]
  · simp [Matrix.GeneralLinearGroup.scalar, cv, hij]

theorem δv_eq :
    δv (v := v) δ₀ c = Matrix.GeneralLinearGroup.map
      (Algebra.TensorProduct.includeLeftRingHom : L →+* E) δ₀ *
      Matrix.GeneralLinearGroup.scalar (Fin 2) (cv (v := v) c) := by
  show AutomorphicForm.tensorPlace K L v (_ * _) = _
  rw [map_mul, tensorPlace_map_includeLeft, tensorPlace_scalar]

abbrev Dv : Subalgebra K M2 := AutomorphicForm.twistedCommutant K L F σ (δv (v := v) δ₀ c)
abbrev Tv : Subgroup G := AutomorphicForm.twistedCentralizer K L F σ (δv (v := v) δ₀ c)

variable {ι : Type} [Fintype ι] [DecidableEq ι] (b : ι → Matrix (Fin 2) (Fin 2) L)

def B (i : ι) : M2 := (b i).map fun l : L => l ⊗ₜ[K] (1 : F)

def mat (a : ι → F) : M2 := ∑ i, (b i).map fun l : L => l ⊗ₜ[K] a i

theorem tmul_eq_smul_tmul_one (l : L) (a : F) : l ⊗ₜ[K] a = a • (l ⊗ₜ[K] (1 : F)) := by
  rw [AutomorphicForm.rightActions_smul_eq, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]

theorem mat_eq_sum_smul (a : ι → F) : mat (v := v) b a = ∑ i, a i • B (v := v) b i := by
  unfold mat B
  refine Finset.sum_congr rfl fun i _ => ?_
  ext j k
  simp only [Matrix.map_apply, Matrix.smul_apply, B]
  exact tmul_eq_smul_tmul_one (v := v) _ _

def matLin : (ι → F) →ₗ[F] M2 where
  toFun := mat (v := v) b
  map_add' a a' := by
    simp only [mat_eq_sum_smul, Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' r a := by
    simp only [mat_eq_sum_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.smul_sum, smul_smul]

@[scoped simp] theorem matLin_apply (a : ι → F) : matLin (v := v) b a = mat (v := v) b a := rfl

theorem mat_add (a a' : ι → F) : mat (v := v) b (a + a') = mat (v := v) b a + mat (v := v) b a' :=
  (matLin (v := v) b).map_add a a'

theorem mat_smul (r : F) (a : ι → F) : mat (v := v) b (r • a) = r • mat (v := v) b a :=
  (matLin (v := v) b).map_smul r a

theorem continuous_mat : Continuous (mat (v := v) b : (ι → F) → M2) := by
  haveI : ContinuousAdd M2 := inferInstanceAs (ContinuousAdd (Fin 2 → Fin 2 → E))
  haveI : ContinuousSMul F M2 := inferInstanceAs (ContinuousSMul F (Fin 2 → Fin 2 → E))
  exact IsModuleTopology.continuous_of_linearMap (matLin (v := v) b)

theorem mat_single (j : ι) (r : F) : mat (v := v) b (Pi.single j r) = r • B (v := v) b j := by
  rw [mat_eq_sum_smul, Finset.sum_eq_single j]
  · rw [Pi.single_eq_same]
  · intro i _ hij; rw [Pi.single_eq_of_ne hij, zero_smul]
  · intro h; exact absurd (Finset.mem_univ j) h

section Chart

variable (hb : LinearIndependent K b)
  (hbspan : ∀ X : Matrix (Fin 2) (Fin 2) L,
    X * (δ₀ : Matrix (Fin 2) (Fin 2) L) = (δ₀ : Matrix (Fin 2) (Fin 2) L) * X.map σ ↔
      X ∈ Submodule.span K (Set.range b))

include hb hbspan in
theorem exists_homeomorph :
    ∃ e : (ι → F) ≃ₜ ↥(Dv (v := v) σ δ₀ c), ∀ a : ι → F, ((e a : Dv (v := v) σ δ₀ c) : M2) = mat (v := v) b a := by
  have h := AutomorphicForm.exists_homeomorph_twistedCommutant_map_mul_scalar_forall_coe_eq_sum_map_tmul_of_linearIndependent
    K L F σ δ₀ (cv (v := v) c) ι b hb hbspan
  rw [← δv_eq] at h
  exact h

def ee : (ι → F) ≃ₜ ↥(Dv (v := v) σ δ₀ c) := (exists_homeomorph (v := v) σ δ₀ c b hb hbspan).choose

theorem coe_ee (a : ι → F) : ((ee (v := v) σ δ₀ c b hb hbspan a : Dv (v := v) σ δ₀ c) : M2) = mat (v := v) b a :=
  (exists_homeomorph (v := v) σ δ₀ c b hb hbspan).choose_spec a

include hb hbspan in
theorem mat_mem (a : ι → F) : mat (v := v) b a ∈ Dv (v := v) σ δ₀ c := by
  rw [← coe_ee (v := v) σ δ₀ c b hb hbspan a]; exact (ee (v := v) σ δ₀ c b hb hbspan a).2

include σ δ₀ c hb hbspan in
theorem mat_injective : Function.Injective (mat (v := v) b : (ι → F) → M2) := by
  intro a a' h
  apply (ee (v := v) σ δ₀ c b hb hbspan).injective
  exact Subtype.ext (by rw [coe_ee, coe_ee, h])

theorem ee_symm_apply (a : ι → F) (h : mat (v := v) b a ∈ Dv (v := v) σ δ₀ c) :
    (ee (v := v) σ δ₀ c b hb hbspan).symm ⟨mat (v := v) b a, h⟩ = a := by
  apply (ee (v := v) σ δ₀ c b hb hbspan).injective
  rw [Homeomorph.apply_symm_apply]
  exact Subtype.ext (coe_ee (v := v) σ δ₀ c b hb hbspan a).symm

theorem mat_ee_symm (X : ↥(Dv (v := v) σ δ₀ c)) :
    mat (v := v) b ((ee (v := v) σ δ₀ c b hb hbspan).symm X) = (X : M2) := by
  rw [← coe_ee (v := v) σ δ₀ c b hb hbspan, Homeomorph.apply_symm_apply]

def good : Set (ι → F) := {a | IsUnit (mat (v := v) b a).det}

theorem continuous_norm_det_mat : Continuous fun a : ι → F => Algebra.norm F (mat (v := v) b a).det :=
  continuous_algebraNorm.comp (continuous_mat (v := v) b).matrix_det

theorem good_eq : (good (v := v) b : Set (ι → F)) = {a | Algebra.norm F (mat (v := v) b a).det ≠ 0} := by
  ext a; exact isUnit_iff_norm_ne_zero _

theorem isOpen_good : IsOpen (good (v := v) b : Set (ι → F)) := by
  rw [good_eq]; exact isOpen_ne_fun (continuous_norm_det_mat (v := v) b) continuous_const

include hb hbspan in
theorem mk''_mem {a : ι → F} (h : IsUnit (mat (v := v) b a).det) :
    Matrix.GeneralLinearGroup.mk'' (mat (v := v) b a) h ∈ Tv (v := v) σ δ₀ c :=
  (AutomorphicForm.mem_twistedCentralizer_iff_coe_mem_twistedCommutant _ _).2
    (mat_mem (v := v) σ δ₀ c b hb hbspan a)

def chart (a : ι → F) : ↥(Tv (v := v) σ δ₀ c) :=
  if h : IsUnit (mat (v := v) b a).det then
    ⟨Matrix.GeneralLinearGroup.mk'' (mat (v := v) b a) h, mk''_mem (v := v) σ δ₀ c b hb hbspan h⟩
  else 1

theorem coe_chart_of_mem {a : ι → F} (h : IsUnit (mat (v := v) b a).det) :
    (((chart (v := v) σ δ₀ c b hb hbspan a : Tv (v := v) σ δ₀ c) : G) : M2) = mat (v := v) b a := by
  simp only [chart, dif_pos h]; rfl

theorem coe_chart_inv_of_mem {a : ι → F} (h : IsUnit (mat (v := v) b a).det) :
    ((((chart (v := v) σ δ₀ c b hb hbspan a : Tv (v := v) σ δ₀ c) : G)⁻¹ : G) : M2) =
      Ring.inverse (mat (v := v) b a).det • (mat (v := v) b a).adjugate := by
  rw [Matrix.coe_units_inv, coe_chart_of_mem (v := v) σ δ₀ c b hb hbspan h, Matrix.inv_def]

def coord (t : ↥(Tv (v := v) σ δ₀ c)) : ι → F :=
  (ee (v := v) σ δ₀ c b hb hbspan).symm ⟨((t : G) : M2),
    (AutomorphicForm.mem_twistedCentralizer_iff_coe_mem_twistedCommutant _ _).1 t.2⟩

theorem mat_coord (t : ↥(Tv (v := v) σ δ₀ c)) : mat (v := v) b (coord (v := v) σ δ₀ c b hb hbspan t) = ((t : G) : M2) :=
  mat_ee_symm (v := v) σ δ₀ c b hb hbspan _

theorem continuous_coord : Continuous (coord (v := v) σ δ₀ c b hb hbspan) := by
  unfold coord
  refine (ee (v := v) σ δ₀ c b hb hbspan).symm.continuous.comp ?_
  refine Continuous.subtype_mk ?_ _
  exact Units.continuous_val.comp continuous_subtype_val

theorem coord_mem_good (t : ↥(Tv (v := v) σ δ₀ c)) : coord (v := v) σ δ₀ c b hb hbspan t ∈ good (v := v) b := by
  show IsUnit (mat (v := v) b (coord (v := v) σ δ₀ c b hb hbspan t)).det
  rw [mat_coord]; exact Matrix.isUnits_det_units _

theorem chart_coord (t : ↥(Tv (v := v) σ δ₀ c)) : chart (v := v) σ δ₀ c b hb hbspan (coord (v := v) σ δ₀ c b hb hbspan t) = t := by
  apply Subtype.ext; apply Units.ext
  rw [coe_chart_of_mem (v := v) σ δ₀ c b hb hbspan (coord_mem_good (v := v) σ δ₀ c b hb hbspan t), mat_coord]

theorem coord_chart {a : ι → F} (h : a ∈ good (v := v) b) : coord (v := v) σ δ₀ c b hb hbspan (chart (v := v) σ δ₀ c b hb hbspan a) = a := by
  apply mat_injective (v := v) σ δ₀ c b hb hbspan
  rw [mat_coord, coe_chart_of_mem (v := v) σ δ₀ c b hb hbspan h]

include hb hbspan in
theorem mul_mat_mem (t : ↥(Tv (v := v) σ δ₀ c)) (a : ι → F) : ((t : G) : M2) * mat (v := v) b a ∈ Dv (v := v) σ δ₀ c :=
  Subalgebra.mul_mem _ ((AutomorphicForm.mem_twistedCentralizer_iff_coe_mem_twistedCommutant _ _).1 t.2)
    (mat_mem (v := v) σ δ₀ c b hb hbspan a)

theorem coe_mk_Dv (X : M2) (h : X ∈ Dv (v := v) σ δ₀ c) : ((⟨X, h⟩ : ↥(Dv (v := v) σ δ₀ c)) : M2) = X := rfl

def Lam (t : ↥(Tv (v := v) σ δ₀ c)) : (ι → F) →ₗ[F] (ι → F) where
  toFun a := (ee (v := v) σ δ₀ c b hb hbspan).symm ⟨((t : G) : M2) * mat (v := v) b a, mul_mat_mem (v := v) σ δ₀ c b hb hbspan t a⟩
  map_add' a a' := by
    apply mat_injective (v := v) σ δ₀ c b hb hbspan
    rw [mat_ee_symm, coe_mk_Dv, mat_add, mat_add, mat_ee_symm, mat_ee_symm, coe_mk_Dv, coe_mk_Dv, Matrix.mul_add]
  map_smul' r a := by
    apply mat_injective (v := v) σ δ₀ c b hb hbspan
    rw [mat_ee_symm, coe_mk_Dv, RingHom.id_apply, mat_smul, mat_smul, mat_ee_symm, coe_mk_Dv, Matrix.mul_smul]

theorem mat_Lam (t : ↥(Tv (v := v) σ δ₀ c)) (a : ι → F) :
    mat (v := v) b (Lam (v := v) σ δ₀ c b hb hbspan t a) = ((t : G) : M2) * mat (v := v) b a :=
  mat_ee_symm (v := v) σ δ₀ c b hb hbspan _

end Chart

end L1Main
p2m_reactivate "P2MW.S_AutomorphicForm_setLIntegral_lattice_norm_det_mul_relIndex_eq_setLIntegral_closure_conj_mul_relIndex.L1Main"

namespace ISMain

open L1Toolkit L1Main Matrix

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable {v : HeightOneSpectrum (𝓞 K)}

local notation "F" => v.adicCompletion K
local notation "E" => L ⊗[K] v.adicCompletion K
local notation "M2" => Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)
local notation "G" => GL (Fin 2) (L ⊗[K] v.adicCompletion K)
local notation "MF" => Matrix (Fin 2) (Fin 2) (v.adicCompletion K)

attribute [local instance 9999] Algebra.toModule
attribute [local instance] isTopologicalRing_E t2Space_E locallyCompactSpace_E continuousSMul_E
  secondCountableTopology_E isScalarTower_FEE smulCommClass_FEE

variable (σ : L ≃ₐ[K] L) (δ₀ : GL (Fin 2) L) (c : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ)

theorem mem_Dv_iff (X : M2) :
    X ∈ AutomorphicForm.twistedCommutant K L F σ (Matrix.GeneralLinearGroup.map
        (Algebra.TensorProduct.includeLeftRingHom : L →+* E) δ₀) ↔ X ∈ Dv (v := v) σ δ₀ c := by
  rw [AutomorphicForm.mem_twistedCommutant_iff,
    show (X ∈ Dv (v := v) σ δ₀ c ↔ _) from AutomorphicForm.mem_twistedCommutant_iff _ _, δv_eq, Units.val_mul]
  set d : M2 := ((Matrix.GeneralLinearGroup.map
    (Algebra.TensorProduct.includeLeftRingHom : L →+* E) δ₀ : G) : M2) with hd
  set S : G := Matrix.GeneralLinearGroup.scalar (Fin 2) (cv (v := v) c) with hS
  have hSc : ∀ M : M2, (S : M2) * M = M * (S : M2) := fun M => by
    rw [hS]
    show Matrix.scalar (Fin 2) ((cv (v := v) c : E)) * M = M * Matrix.scalar (Fin 2) ((cv (v := v) c : E))
    exact Matrix.scalar_commute _ (fun r' => Commute.all _ _) M
  have hSS : ((S : G) : M2) * (((S⁻¹ : G)) : M2) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  constructor
  · intro h
    calc X * (d * (S : M2)) = (X * d) * (S : M2) := (mul_assoc _ _ _).symm
      _ = (d * X.map (AutomorphicForm.sigmaTensor K L F σ)) * (S : M2) := by rw [h]
      _ = d * (X.map (AutomorphicForm.sigmaTensor K L F σ) * (S : M2)) := mul_assoc _ _ _
      _ = d * ((S : M2) * X.map (AutomorphicForm.sigmaTensor K L F σ)) := by rw [hSc]
      _ = d * (S : M2) * X.map (AutomorphicForm.sigmaTensor K L F σ) := (mul_assoc _ _ _).symm
  · intro h
    have h' : X * d * (S : M2) = d * X.map (AutomorphicForm.sigmaTensor K L F σ) * (S : M2) := by
      rw [mul_assoc, h, mul_assoc, hSc, ← mul_assoc]
    calc X * d = X * d * (S : M2) * ((S⁻¹ : G) : M2) := by rw [mul_assoc (X * d), hSS, mul_one]
      _ = d * X.map (AutomorphicForm.sigmaTensor K L F σ) * (S : M2) * ((S⁻¹ : G) : M2) := by rw [h']
      _ = d * X.map (AutomorphicForm.sigmaTensor K L F σ) := by rw [mul_assoc (d * _), hSS, mul_one]

variable {ι : Type} [Fintype ι] [DecidableEq ι] (b : ι → Matrix (Fin 2) (Fin 2) L)
  (hb : LinearIndependent K b)
  (hbspan : ∀ X : Matrix (Fin 2) (Fin 2) L,
    X * (δ₀ : Matrix (Fin 2) (Fin 2) L) = (δ₀ : Matrix (Fin 2) (Fin 2) L) * X.map σ ↔
      X ∈ Submodule.span K (Set.range b))
  (h2 : Module.finrank K L = 2) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
  (u : (AdeleRing (𝓞 K) K)ˣ)
  (hN : AutomorphicForm.normString K L (AdeleRing (𝓞 K) K) σ
      (Matrix.GeneralLinearGroup.map
          (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
        Matrix.GeneralLinearGroup.scalar (Fin 2) c) =
    AutomorphicForm.toTensorGL K L (AdeleRing (𝓞 K) K) (AutomorphicForm.centralScalar (𝓞 K) K u))
  (hns : ∀ (x : GL (Fin 2) L) (z : Lˣ),
    x⁻¹ * δ₀ * Matrix.GeneralLinearGroup.map (σ : L →+* L) x ≠
      Matrix.GeneralLinearGroup.scalar (Fin 2) z)

include hb hbspan h2 hgen u hN hns in
theorem card_eq_four : Fintype.card ι = 4 := by
  obtain ⟨b', hb', hspan'⟩ :=
    AutomorphicForm.exists_linearIndependent_forall_mul_eq_mul_map_iff_mem_span_of_normString_eq_toTensorGL_centralScalar_of_forall_ne_scalar
      K L h2 σ hgen δ₀ c u hN hns
  have hspan : Submodule.span K (Set.range b) = Submodule.span K (Set.range b') := by
    ext X; rw [← hbspan X, hspan' X]
  have h1 : Module.finrank K (Submodule.span K (Set.range b)) = Fintype.card ι := finrank_span_eq_card hb
  have h1' : Module.finrank K (Submodule.span K (Set.range b')) = Fintype.card (Fin 4) := finrank_span_eq_card hb'
  rw [hspan, h1', Fintype.card_fin] at h1
  exact h1.symm

variable (y : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
  (hyD : ∀ g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K),
    (y : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) * g.map (Algebra.TensorProduct.includeRight : v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K) * ((y⁻¹ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) ∈
      AutomorphicForm.twistedCommutant K L (v.adicCompletion K) σ
        (Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] v.adicCompletion K) δ₀))

def conjF (g : MF) : M2 :=
  (y : M2) * g.map (Algebra.TensorProduct.includeRight : F →ₐ[K] E) * ((y⁻¹ : G) : M2)

theorem map_includeRight_add (g g' : MF) :
    (g + g').map (Algebra.TensorProduct.includeRight : F →ₐ[K] E) =
      g.map (Algebra.TensorProduct.includeRight : F →ₐ[K] E) + g'.map (Algebra.TensorProduct.includeRight : F →ₐ[K] E) := by
  ext i j; simp only [Matrix.map_apply, Matrix.add_apply, map_add]

theorem map_includeRight_smul (r : F) (g : MF) :
    (r • g).map (Algebra.TensorProduct.includeRight : F →ₐ[K] E) =
      r • g.map (Algebra.TensorProduct.includeRight : F →ₐ[K] E) := by
  ext i j
  simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]
  rw [AutomorphicForm.rightActions_smul_eq, Algebra.TensorProduct.includeRight_apply]

theorem conjF_add (g g' : MF) : conjF (v := v) y (g + g') = conjF (v := v) y g + conjF (v := v) y g' := by
  simp only [conjF, map_includeRight_add, Matrix.mul_add, Matrix.add_mul]

theorem conjF_smul (r : F) (g : MF) : conjF (v := v) y (r • g) = r • conjF (v := v) y g := by
  simp only [conjF, map_includeRight_smul, Matrix.mul_smul, Matrix.smul_mul]

def conjFHom : MF →+ M2 where
  toFun := conjF (v := v) y
  map_zero' := by simp [conjF, Matrix.map_zero _ (map_zero _)]
  map_add' := conjF_add (v := v) y

theorem continuous_conjF : Continuous (conjF (v := v) y) := by
  unfold conjF
  refine (continuous_const.mul ?_).mul continuous_const
  refine continuous_id.matrix_map ?_
  have : (Algebra.TensorProduct.includeRight : F →ₐ[K] E) = fun r : F => r • (1 : E) := by
    funext r
    rw [Algebra.TensorProduct.includeRight_apply, AutomorphicForm.rightActions_smul_eq, mul_one]
  rw [this]
  exact continuous_id.fun_smul continuous_const

include hyD in
theorem conjF_mem (g : MF) : conjF (v := v) y g ∈ Dv (v := v) σ δ₀ c :=
  (mem_Dv_iff (v := v) σ δ₀ c _).1 (hyD g)

def theta : MF →ₗ[F] (ι → F) where
  toFun g := (ee (v := v) σ δ₀ c b hb hbspan).symm ⟨conjF (v := v) y g, conjF_mem (v := v) σ δ₀ c y hyD g⟩
  map_add' g g' := by
    apply mat_injective (v := v) σ δ₀ c b hb hbspan
    rw [mat_ee_symm, coe_mk_Dv, conjF_add, mat_add, mat_ee_symm, mat_ee_symm, coe_mk_Dv, coe_mk_Dv]
  map_smul' r g := by
    apply mat_injective (v := v) σ δ₀ c b hb hbspan
    rw [mat_ee_symm, coe_mk_Dv, RingHom.id_apply, conjF_smul, mat_smul, mat_ee_symm, coe_mk_Dv]

theorem mat_theta (g : MF) :
    mat (v := v) b (theta (v := v) σ δ₀ c b hb hbspan y hyD g) = conjF (v := v) y g :=
  mat_ee_symm (v := v) σ δ₀ c b hb hbspan _

include hb hbspan h2 hgen u hN hns in

theorem nontrivial_E : Nontrivial E := by
  have h4 := card_eq_four σ δ₀ c b hb hbspan h2 hgen u hN hns
  haveI : Nonempty ι := Fintype.card_pos_iff.1 (by omega)
  obtain ⟨i⟩ := ‹Nonempty ι›
  by_contra hE
  rw [not_nontrivial_iff_subsingleton] at hE
  have hsub : Subsingleton M2 := inferInstance
  have h1 : mat (v := v) b (Pi.single i (1 : F)) = mat (v := v) b 0 := hsub.elim _ _
  have h2' := congrFun (mat_injective (v := v) σ δ₀ c b hb hbspan h1) i
  simp at h2'

include hb hbspan h2 hgen u hN hns in
theorem includeRight_injective :
    Function.Injective (Algebra.TensorProduct.includeRight : F →ₐ[K] E) := by
  haveI := nontrivial_E (v := v) σ δ₀ c b hb hbspan h2 hgen u hN hns
  exact (Algebra.TensorProduct.includeRight : F →ₐ[K] E).toRingHom.injective

include hb hbspan h2 hgen u hN hns in
theorem conjF_injective : Function.Injective (conjF (v := v) y) := by
  intro g g' h
  unfold conjF at h
  have h1 : g.map (Algebra.TensorProduct.includeRight : F →ₐ[K] E) =
      g'.map (Algebra.TensorProduct.includeRight : F →ₐ[K] E) := by
    have hy1 : (((y⁻¹ : G)) : M2) * (y : M2) = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have hy2 : (y : M2) * (((y⁻¹ : G)) : M2) = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have := congrArg (fun Z : M2 => ((y⁻¹ : G) : M2) * Z * (y : M2)) h
    beta_reduce at this
    rwa [mul_assoc, mul_assoc, mul_assoc, hy1, mul_one, ← mul_assoc, ← mul_assoc, hy1, one_mul,
      mul_assoc, mul_assoc, hy1, mul_one, ← mul_assoc, hy1, one_mul] at this
  ext i j
  have := congrFun (congrFun h1 i) j
  simp only [Matrix.map_apply] at this
  exact includeRight_injective (v := v) σ δ₀ c b hb hbspan h2 hgen u hN hns this

include h2 hgen u hN hns in
theorem theta_injective : Function.Injective (theta (v := v) σ δ₀ c b hb hbspan y hyD) := by
  intro g g' h
  apply conjF_injective (v := v) σ δ₀ c b hb hbspan h2 hgen u hN hns y
  rw [← mat_theta (v := v) σ δ₀ c b hb hbspan y hyD g, ← mat_theta (v := v) σ δ₀ c b hb hbspan y hyD g', h]

include h2 hgen u hN hns in
theorem theta_bijective : Function.Bijective (theta (v := v) σ δ₀ c b hb hbspan y hyD) := by
  refine ⟨theta_injective (v := v) σ δ₀ c b hb hbspan h2 hgen u hN hns y hyD, ?_⟩
  have hdim : Module.finrank F MF = Module.finrank F (ι → F) := by
    rw [Module.finrank_matrix, Module.finrank_pi, card_eq_four σ δ₀ c b hb hbspan h2 hgen u hN hns]
    simp
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).1
    (theta_injective (v := v) σ δ₀ c b hb hbspan h2 hgen u hN hns y hyD)

def thetaEquiv : MF ≃ₗ[F] (ι → F) :=
  LinearEquiv.ofBijective (theta (v := v) σ δ₀ c b hb hbspan y hyD)
    (theta_bijective (v := v) σ δ₀ c b hb hbspan h2 hgen u hN hns y hyD)

def thetaHomeo : MF ≃ₜ (ι → F) :=
  haveI : IsModuleTopology F MF := inferInstanceAs (IsModuleTopology F (Fin 2 → Fin 2 → F))
  haveI : IsModuleTopology F (ι → F) := IsModuleTopology.instPi
  haveI : ContinuousAdd MF := inferInstanceAs (ContinuousAdd (Fin 2 → Fin 2 → F))
  haveI : ContinuousSMul F MF := inferInstanceAs (ContinuousSMul F (Fin 2 → Fin 2 → F))
  { (thetaEquiv (v := v) σ δ₀ c b hb hbspan h2 hgen u hN hns y hyD).toEquiv with
    continuous_toFun := IsModuleTopology.continuous_of_linearMap
      (thetaEquiv (v := v) σ δ₀ c b hb hbspan h2 hgen u hN hns y hyD).toLinearMap
    continuous_invFun := IsModuleTopology.continuous_of_linearMap
      (thetaEquiv (v := v) σ δ₀ c b hb hbspan h2 hgen u hN hns y hyD).symm.toLinearMap }

theorem thetaHomeo_apply (g : MF) :
    thetaHomeo (v := v) σ δ₀ c b hb hbspan h2 hgen u hN hns y hyD g = theta (v := v) σ δ₀ c b hb hbspan y hyD g := rfl

def Box : Set MF := {g | ∀ i j, g i j ∈ v.adicCompletionIntegers K}

def Obox : Set (ι → F) := {a | ∀ k, a k ∈ v.adicCompletionIntegers K}

theorem isCompact_integers : IsCompact ((v.adicCompletionIntegers K : Set F)) := by
  have h := isCompact_range (continuous_subtype_val (p := fun x : F => x ∈ v.adicCompletionIntegers K))
  convert h using 1
  ext x
  simp

theorem isOpen_integers : IsOpen ((v.adicCompletionIntegers K : Set F)) := by
  have h1 : ((v.adicCompletionIntegers K : Set F)) = ((Valued.v.integer : Subring F) : Set F) := by
    ext x
    rw [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 K) K v, SetLike.mem_coe,
      Valuation.mem_integer_iff]
  rw [h1]; exact Valued.isOpen_integer F

theorem Box_eq : (Box (v := v) : Set MF) =
    Set.pi Set.univ (fun _ : Fin 2 => Set.pi Set.univ (fun _ : Fin 2 => (v.adicCompletionIntegers K : Set F))) := by
  ext g
  exact ⟨fun h => Set.mem_univ_pi.mpr fun i => Set.mem_univ_pi.mpr fun j => h i j,
    fun h i j => Set.mem_univ_pi.mp (Set.mem_univ_pi.mp h i) j⟩

theorem isCompact_Box : IsCompact (Box (v := v) : Set MF) := by
  rw [Box_eq]
  exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_integers (v := v)

theorem isOpen_Box : IsOpen (Box (v := v) : Set MF) := by
  rw [Box_eq]
  exact isOpen_set_pi Set.finite_univ fun _ _ => isOpen_set_pi Set.finite_univ fun _ _ => isOpen_integers (v := v)

theorem Obox_eq : (Obox (v := v) : Set (ι → F)) = Set.pi Set.univ (fun _ : ι => (v.adicCompletionIntegers K : Set F)) := by
  ext a
  exact ⟨fun h => Set.mem_univ_pi.mpr fun k => h k, fun h k => Set.mem_univ_pi.mp h k⟩

theorem isCompact_Obox : IsCompact (Obox (v := v) : Set (ι → F)) := by
  rw [Obox_eq]; exact isCompact_univ_pi fun _ => isCompact_integers (v := v)

theorem isOpen_Obox : IsOpen (Obox (v := v) : Set (ι → F)) := by
  rw [Obox_eq]; exact isOpen_set_pi Set.finite_univ fun _ _ => isOpen_integers (v := v)

theorem zero_mem_Obox : (0 : ι → F) ∈ Obox (v := v) := fun _ => ZeroMemClass.zero_mem _

def BoxSub : AddSubgroup MF where
  carrier := Box (v := v)
  add_mem' ha hb := fun i j => by rw [Matrix.add_apply]; exact AddMemClass.add_mem (ha i j) (hb i j)
  zero_mem' := fun i j => by rw [Matrix.zero_apply]; exact ZeroMemClass.zero_mem _
  neg_mem' ha := fun i j => by rw [Matrix.neg_apply]; exact NegMemClass.neg_mem (ha i j)

def OboxSub : AddSubgroup (ι → F) where
  carrier := Obox (v := v)
  add_mem' ha hb := fun k => by rw [Pi.add_apply]; exact AddMemClass.add_mem (ha k) (hb k)
  zero_mem' := fun k => ZeroMemClass.zero_mem _
  neg_mem' ha := fun k => by rw [Pi.neg_apply]; exact NegMemClass.neg_mem (ha k)

end ISMain
p2m_reactivate "P2MW.S_AutomorphicForm_setLIntegral_lattice_norm_det_mul_relIndex_eq_setLIntegral_closure_conj_mul_relIndex.L1Main"

namespace ISMain

open L1Toolkit L1Main Matrix

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable {v : HeightOneSpectrum (𝓞 K)}

local notation "F" => v.adicCompletion K
local notation "E" => L ⊗[K] v.adicCompletion K
local notation "M2" => Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)
local notation "G" => GL (Fin 2) (L ⊗[K] v.adicCompletion K)
local notation "MF" => Matrix (Fin 2) (Fin 2) (v.adicCompletion K)

attribute [local instance 9999] Algebra.toModule
attribute [local instance] isTopologicalRing_E t2Space_E locallyCompactSpace_E continuousSMul_E
  secondCountableTopology_E isScalarTower_FEE smulCommClass_FEE

variable (σ : L ≃ₐ[K] L) (δ₀ : GL (Fin 2) L) (c : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ)
  {ι : Type} [Fintype ι] [DecidableEq ι] (b : ι → Matrix (Fin 2) (Fin 2) L)
  (hb : LinearIndependent K b)
  (hbspan : ∀ X : Matrix (Fin 2) (Fin 2) L,
    X * (δ₀ : Matrix (Fin 2) (Fin 2) L) = (δ₀ : Matrix (Fin 2) (Fin 2) L) * X.map σ ↔
      X ∈ Submodule.span K (Set.range b))
  (h2 : Module.finrank K L = 2) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
  (u : (AdeleRing (𝓞 K) K)ˣ)
  (hN : AutomorphicForm.normString K L (AdeleRing (𝓞 K) K) σ
      (Matrix.GeneralLinearGroup.map
          (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
        Matrix.GeneralLinearGroup.scalar (Fin 2) c) =
    AutomorphicForm.toTensorGL K L (AdeleRing (𝓞 K) K) (AutomorphicForm.centralScalar (𝓞 K) K u))
  (hns : ∀ (x : GL (Fin 2) L) (z : Lˣ),
    x⁻¹ * δ₀ * Matrix.GeneralLinearGroup.map (σ : L →+* L) x ≠
      Matrix.GeneralLinearGroup.scalar (Fin 2) z)
  (y : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
  (hyD : ∀ g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K),
    (y : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) * g.map (Algebra.TensorProduct.includeRight : v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K) * ((y⁻¹ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) ∈
      AutomorphicForm.twistedCommutant K L (v.adicCompletion K) σ
        (Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] v.adicCompletion K) δ₀))
  (SΛ SM : AddSubgroup (Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)))
  (hSΛ : SΛ = (AddSubgroup.closure
        {X : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K) | ∃ (i : ι) (a : v.adicCompletion K), a ∈ v.adicCompletionIntegers K ∧ X = (b i).map (fun l : L => l ⊗ₜ[K] a)}))
  (hSM : SM = (AddSubgroup.closure
        {X : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K) | ∃ g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K), (∀ i j, g i j ∈ v.adicCompletionIntegers K) ∧
            X = (y : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) * g.map (Algebra.TensorProduct.includeRight : v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K) * ((y⁻¹ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K))}))

def matHom : (ι → F) →+ M2 := (matLin (v := v) b).toAddMonoidHom

@[scoped simp] theorem matHom_apply (a : ι → F) : matHom (v := v) b a = mat (v := v) b a := rfl

include hSM in
theorem SM_eq_map : SM = (BoxSub (v := v)).map (conjFHom (v := v) y) := by
  rw [hSM, ← AddSubgroup.closure_eq (BoxSub (v := v)), AddMonoidHom.map_closure]
  congr 1
  ext X
  simp only [Set.mem_setOf_eq, Set.mem_image]
  constructor
  · rintro ⟨g, hg, rfl⟩; exact ⟨g, hg, rfl⟩
  · rintro ⟨g, hg, rfl⟩; exact ⟨g, hg, rfl⟩

include hSM in
theorem coe_SM : (SM : Set M2) = conjF (v := v) y '' Box (v := v) := by
  rw [SM_eq_map (v := v) y SM hSM]; rfl

include σ δ₀ c hb hbspan hSM hyD in
theorem SM_le_range : SM ≤ (matHom (v := v) b).range := by
  intro X hX
  rw [← SetLike.mem_coe, coe_SM (v := v) y SM hSM] at hX
  obtain ⟨g, _, rfl⟩ := hX
  exact ⟨theta (v := v) σ δ₀ c b hb hbspan y hyD g, mat_theta (v := v) σ δ₀ c b hb hbspan y hyD g⟩

include hSM in

theorem coe_comap_SM :
    ((SM.comap (matHom (v := v) b)) : Set (ι → F)) =
      theta (v := v) σ δ₀ c b hb hbspan y hyD '' Box (v := v) := by
  ext a
  rw [AddSubgroup.coe_comap, Set.mem_preimage, matHom_apply, coe_SM (v := v) y SM hSM]
  constructor
  · rintro ⟨g, hg, hga⟩
    refine ⟨g, hg, mat_injective (v := v) σ δ₀ c b hb hbspan ?_⟩
    rw [mat_theta, hga]
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g, hg, (mat_theta (v := v) σ δ₀ c b hb hbspan y hyD g).symm⟩

include hSΛ in
theorem SΛ_eq_map : SΛ = (OboxSub (v := v)).map (matHom (v := v) b) := by
  rw [hSΛ]
  apply le_antisymm
  · rw [AddSubgroup.closure_le]
    rintro X ⟨i, a, ha, rfl⟩
    refine ⟨Pi.single i a, ?_, ?_⟩
    · intro k
      by_cases hk : k = i
      · subst hk; rw [Pi.single_eq_same]; exact ha
      · rw [Pi.single_eq_of_ne hk]; exact ZeroMemClass.zero_mem _
    · show mat (v := v) b (Pi.single i a) = _
      rw [mat_single]
      ext j k
      simp only [Matrix.smul_apply, B, Matrix.map_apply]
      exact (tmul_eq_smul_tmul_one (v := v) _ _).symm
  · rintro X ⟨a, ha, rfl⟩
    show mat (v := v) b a ∈ _
    unfold mat
    refine AddSubgroup.sum_mem _ fun i _ => AddSubgroup.subset_closure ⟨i, a i, ha i, rfl⟩

include σ δ₀ c hb hbspan hSΛ in
theorem comap_SΛ : SΛ.comap (matHom (v := v) b) = OboxSub (v := v) := by
  rw [SΛ_eq_map (v := v) b SΛ hSΛ]
  exact AddSubgroup.comap_map_eq_self_of_injective (mat_injective (v := v) σ δ₀ c b hb hbspan) _

include hSΛ in
theorem SΛ_le_range : SΛ ≤ (matHom (v := v) b).range := by
  rw [SΛ_eq_map (v := v) b SΛ hSΛ]; exact AddSubgroup.map_le_range _ _

include σ δ₀ c hb hbspan y hyD hSΛ hSM in
theorem relIndex_SΛ_SM :
    SΛ.relIndex SM = (OboxSub (v := v) : AddSubgroup (ι → F)).relIndex (SM.comap (matHom (v := v) b)) := by
  rw [← comap_SΛ (v := v) σ δ₀ c b hb hbspan SΛ hSΛ, AddSubgroup.relIndex_comap,
    AddSubgroup.map_comap_eq_self (SM_le_range (v := v) σ δ₀ c b hb hbspan y hyD SM hSM)]

include σ δ₀ c hb hbspan hSΛ hSM in
theorem relIndex_SM_SΛ :
    SM.relIndex SΛ = (SM.comap (matHom (v := v) b)).relIndex (OboxSub (v := v) : AddSubgroup (ι → F)) := by
  rw [← comap_SΛ (v := v) σ δ₀ c b hb hbspan SΛ hSΛ, AddSubgroup.relIndex_comap,
    AddSubgroup.map_comap_eq_self (SΛ_le_range (v := v) b SΛ hSΛ)]

theorem relIndex_ne_zero_of_isCompact_of_isOpen {X : Type*} [AddCommGroup X] [TopologicalSpace X]
    [IsTopologicalAddGroup X] (A B : AddSubgroup X) (hA : IsCompact (A : Set X)) (hB : IsOpen (B : Set X)) :
    B.relIndex A ≠ 0 := by
  haveI : CompactSpace A := isCompact_iff_compactSpace.1 hA
  have hBo : IsOpen ((B.addSubgroupOf A : AddSubgroup A) : Set A) := by
    show IsOpen ((fun x : A => (x : X)) ⁻¹' (B : Set X))
    exact hB.preimage continuous_subtype_val
  haveI : DiscreteTopology (A ⧸ B.addSubgroupOf A) := QuotientAddGroup.discreteTopology hBo
  haveI : Finite (A ⧸ B.addSubgroupOf A) := finite_of_compact_of_discrete
  exact AddSubgroup.index_ne_zero_of_finite

include σ δ₀ c hb hbspan h2 hgen u hN hns y hyD hSM in
theorem isCompact_comap_SM : IsCompact ((SM.comap (matHom (v := v) b)) : Set (ι → F)) := by
  rw [coe_comap_SM (v := v) σ δ₀ c b hb hbspan y hyD SM hSM]
  exact (isCompact_Box (v := v)).image
    ((thetaHomeo (v := v) σ δ₀ c b hb hbspan h2 hgen u hN hns y hyD).continuous)

include σ δ₀ c hb hbspan h2 hgen u hN hns y hyD hSM in
theorem isOpen_comap_SM : IsOpen ((SM.comap (matHom (v := v) b)) : Set (ι → F)) := by
  rw [coe_comap_SM (v := v) σ δ₀ c b hb hbspan y hyD SM hSM]
  exact (thetaHomeo (v := v) σ δ₀ c b hb hbspan h2 hgen u hN hns y hyD).isOpenMap _ (isOpen_Box (v := v))

end ISMain
p2m_reactivate "P2MW.S_AutomorphicForm_setLIntegral_lattice_norm_det_mul_relIndex_eq_setLIntegral_closure_conj_mul_relIndex.L1Main P2MW.S_AutomorphicForm_setLIntegral_lattice_norm_det_mul_relIndex_eq_setLIntegral_closure_conj_mul_relIndex.ISMain"

namespace ISMain

open L1Toolkit L1Main Matrix

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable {v : HeightOneSpectrum (𝓞 K)}

local notation "F" => v.adicCompletion K
local notation "E" => L ⊗[K] v.adicCompletion K
local notation "M2" => Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)
local notation "G" => GL (Fin 2) (L ⊗[K] v.adicCompletion K)
local notation "MF" => Matrix (Fin 2) (Fin 2) (v.adicCompletion K)

attribute [local instance 9999] Algebra.toModule
attribute [local instance] isTopologicalRing_E t2Space_E locallyCompactSpace_E continuousSMul_E
  secondCountableTopology_E isScalarTower_FEE smulCommClass_FEE

theorem main
    (σ : L ≃ₐ[K] L) (δ₀ : GL (Fin 2) L) (c : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ)
    {ι : Type} [Fintype ι] [DecidableEq ι] (b : ι → Matrix (Fin 2) (Fin 2) L)
    (hb : LinearIndependent K b)
    (hbspan : ∀ X : Matrix (Fin 2) (Fin 2) L,
      X * (δ₀ : Matrix (Fin 2) (Fin 2) L) = (δ₀ : Matrix (Fin 2) (Fin 2) L) * X.map σ ↔
        X ∈ Submodule.span K (Set.range b))
    (h2 : Module.finrank K L = 2) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (u : (AdeleRing (𝓞 K) K)ˣ)
    (hN : AutomorphicForm.normString K L (AdeleRing (𝓞 K) K) σ
        (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c) =
      AutomorphicForm.toTensorGL K L (AdeleRing (𝓞 K) K) (AutomorphicForm.centralScalar (𝓞 K) K u))
    (hns : ∀ (x : GL (Fin 2) L) (z : Lˣ),
      x⁻¹ * δ₀ * Matrix.GeneralLinearGroup.map (σ : L →+* L) x ≠
        Matrix.GeneralLinearGroup.scalar (Fin 2) z)
    (y : G)
    (hyD : ∀ g : MF,
      (y : M2) * g.map (Algebra.TensorProduct.includeRight : F →ₐ[K] E) * ((y⁻¹ : G) : M2) ∈
        AutomorphicForm.twistedCommutant K L F σ
          (Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* E) δ₀))
    (SΛ SM : AddSubgroup M2)
    (hSΛ : SΛ = (AddSubgroup.closure
          {X : M2 | ∃ (i : ι) (a : F), a ∈ v.adicCompletionIntegers K ∧ X = (b i).map (fun l : L => l ⊗ₜ[K] a)}))
    (hSM : SM = (AddSubgroup.closure
          {X : M2 | ∃ g : MF, (∀ i j, g i j ∈ v.adicCompletionIntegers K) ∧
              X = (y : M2) * g.map (Algebra.TensorProduct.includeRight : F →ₐ[K] E) * ((y⁻¹ : G) : M2)}))
    (τ : Measure ↥(Tv (v := v) σ δ₀ c)) (hτ : τ.IsHaarMeasure) :
    SΛ.relIndex SM ≠ 0 ∧ SM.relIndex SΛ ≠ 0 ∧
    (∫⁻ t in {t : ↥(Tv (v := v) σ δ₀ c) | ∃ a : ι → F, (∀ k, a k ∈ v.adicCompletionIntegers K) ∧
          ((t : G) : M2) = (∑ k, (b k).map fun l : L => l ⊗ₜ[K] a k)}, ENNReal.ofReal ‖Algebra.norm F (Matrix.det ((t : G) : M2))‖ ∂τ) * ((SΛ.relIndex SM : ℕ) : ℝ≥0∞) =
      (∫⁻ t in {t : ↥(Tv (v := v) σ δ₀ c) | ((t : G) : M2) ∈ (SM : Set M2)}, ENNReal.ofReal ‖Algebra.norm F (Matrix.det ((t : G) : M2))‖ ∂τ) *
        ((SM.relIndex SΛ : ℕ) : ℝ≥0∞) := by

  set HM : AddSubgroup (ι → F) := SM.comap (matHom (v := v) b) with hHMdef
  set HO : AddSubgroup (ι → F) := OboxSub (v := v) with hHOdef
  have hHMc : IsCompact (HM : Set (ι → F)) := isCompact_comap_SM (v := v) σ δ₀ c b hb hbspan h2 hgen u hN hns y hyD SM hSM
  have hHMo : IsOpen (HM : Set (ι → F)) := isOpen_comap_SM (v := v) σ δ₀ c b hb hbspan h2 hgen u hN hns y hyD SM hSM
  have hHOc : IsCompact (HO : Set (ι → F)) := isCompact_Obox (v := v)
  have hHOo : IsOpen (HO : Set (ι → F)) := isOpen_Obox (v := v)
  have r1eq : SΛ.relIndex SM = HO.relIndex HM := relIndex_SΛ_SM (v := v) σ δ₀ c b hb hbspan y hyD SΛ SM hSΛ hSM
  have r2eq : SM.relIndex SΛ = HM.relIndex HO := relIndex_SM_SΛ (v := v) σ δ₀ c b hb hbspan y SΛ SM hSΛ hSM
  have hr1 : HO.relIndex HM ≠ 0 := relIndex_ne_zero_of_isCompact_of_isOpen HM HO hHMc hHOo
  have hr2 : HM.relIndex HO ≠ 0 := relIndex_ne_zero_of_isCompact_of_isOpen HO HM hHOc hHMo
  refine ⟨by rw [r1eq]; exact hr1, by rw [r2eq]; exact hr2, ?_⟩

  letI mF : MeasurableSpace F := borel F
  haveI : BorelSpace F := ⟨rfl⟩
  haveI : BorelSpace (ι → F) := inferInstance
  set μ : Measure (ι → F) := Measure.addHaar with hμ
  haveI : MeasurableAdd (ι → F) := inferInstance

  haveI : T2Space M2 := inferInstanceAs (T2Space (Fin 2 → Fin 2 → E))
  have hSMclosed : IsClosed (SM : Set M2) := by
    rw [coe_SM (v := v) y SM hSM]
    exact ((isCompact_Box (v := v)).image (continuous_conjF (v := v) y)).isClosed
  set W : Set G := {g : G | (g : M2) ∈ (SM : Set M2)} with hWdef
  have hW : MeasurableSet[AutomorphicForm.glBorelOf (L ⊗[K] v.adicCompletion K)] W := by
    letI : MeasurableSpace G := AutomorphicForm.glBorelOf (L ⊗[K] v.adicCompletion K)
    haveI : BorelSpace G := AutomorphicForm.borelSpace_glBorelOf _
    exact (hSMclosed.preimage Units.continuous_val).measurableSet

  have hL1 := AutomorphicForm.setLIntegral_twistedCentralizer_norm_det_mul_measure_pi_integers_eq_setLIntegral_lattice_mul_measure_preimage_of_isAddHaarMeasure
    K L h2 σ hgen δ₀ c u hN hns v τ hτ ι b hb hbspan μ W hW

  have hPre : {a : ι → F | ∃ t : ↥(Tv (v := v) σ δ₀ c), (t : G) ∈ W ∧ ((t : G) : M2) = (∑ k, (b k).map fun l : L => l ⊗ₜ[K] a k)} =
      good (v := v) b ∩ (HM : Set (ι → F)) := by
    ext a
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, hWdef, hHMdef, AddSubgroup.coe_comap, Set.mem_preimage,
      matHom_apply]
    constructor
    · rintro ⟨t, htW, hta⟩
      have hta' : ((t : G) : M2) = mat (v := v) b a := hta
      refine ⟨?_, ?_⟩
      · show IsUnit (mat (v := v) b a).det
        rw [← hta']; exact Matrix.isUnits_det_units _
      · show mat (v := v) b a ∈ (SM : Set M2)
        rw [← hta']; exact htW
    · rintro ⟨ha, haM⟩
      exact ⟨⟨Matrix.GeneralLinearGroup.mk'' (mat (v := v) b a) ha, mk''_mem (v := v) σ δ₀ c b hb hbspan ha⟩,
        haM, rfl⟩
  have hnull : μ (good (v := v) b)ᶜ = 0 := by
    have h := AutomorphicForm.measure_setOf_algebraNorm_det_sum_map_tmul_eq_zero_eq_zero_of_isUnit K L v ι b
      (coord (v := v) σ δ₀ c b hb hbspan 1) (coord_mem_good (v := v) σ δ₀ c b hb hbspan 1) μ
    have hset : (good (v := v) b)ᶜ = {a : ι → F |
        Algebra.norm F (Matrix.det (∑ i : ι, (b i).map fun l : L => l ⊗ₜ[K] a i : M2)) = 0} := by
      ext a
      rw [Set.mem_compl_iff, Set.mem_setOf_eq]
      show ¬ IsUnit (mat (v := v) b a).det ↔ _
      rw [isUnit_iff_norm_ne_zero, not_not]
      rfl
    rw [hset]; exact h
  have hμPre : μ (good (v := v) b ∩ (HM : Set (ι → F))) = μ (HM : Set (ι → F)) := by
    rw [Set.inter_comm]
    have h := measure_inter_add_diff (μ := μ) (HM : Set (ι → F)) (isOpen_good (v := v) b).measurableSet
    have h0 : μ ((HM : Set (ι → F)) \ good (v := v) b) = 0 := measure_mono_null (fun a ha => ha.2) hnull
    rw [h0, add_zero] at h
    exact h

  have hIm : MeasurableSet ((HO ⊓ HM : AddSubgroup (ι → F)) : Set (ι → F)) := by
    rw [AddSubgroup.coe_inf]
    exact (hHOc.isClosed.inter hHMc.isClosed).measurableSet
  have hμHO : μ (HO : Set (ι → F)) = ((HM.relIndex HO : ℕ) : ℝ≥0∞) * μ ((HO ⊓ HM : AddSubgroup (ι → F)) : Set (ι → F)) := by
    rw [← AddSubgroup.inf_relIndex_left HO HM]
    refine MeasureTheory.Measure.measure_coe_eq_relIndex_mul_of_le_of_isAddLeftInvariant μ (HO ⊓ HM) HO
      inf_le_left hIm ?_
    rw [AddSubgroup.inf_relIndex_left]; exact hr2
  have hμHM : μ (HM : Set (ι → F)) = ((HO.relIndex HM : ℕ) : ℝ≥0∞) * μ ((HO ⊓ HM : AddSubgroup (ι → F)) : Set (ι → F)) := by
    rw [← AddSubgroup.inf_relIndex_right HO HM]
    refine MeasureTheory.Measure.measure_coe_eq_relIndex_mul_of_le_of_isAddLeftInvariant μ (HO ⊓ HM) HM
      inf_le_right hIm ?_
    rw [AddSubgroup.inf_relIndex_right]; exact hr1

  have hO0 : μ (HO : Set (ι → F)) ≠ 0 := (hHOo.measure_pos μ ⟨0, zero_mem_Obox (v := v)⟩).ne'
  have hOt : μ (HO : Set (ι → F)) ≠ ⊤ := hHOc.measure_lt_top.ne

  have hOset : {a : ι → F | ∀ k, a k ∈ v.adicCompletionIntegers K} = (HO : Set (ι → F)) := rfl
  rw [hPre, hμPre, hOset] at hL1

  have hWset : {t : ↥(Tv (v := v) σ δ₀ c) | (t : G) ∈ W} =
      {t : ↥(Tv (v := v) σ δ₀ c) | ((t : G) : M2) ∈ (SM : Set M2)} := rfl
  rw [hWset] at hL1
  rw [r1eq, r2eq]
  refine (ENNReal.mul_left_inj hO0 hOt).1 ?_
  have e1 : ∀ (A R : ℝ≥0∞), A * R * μ (HO : Set (ι → F)) = R * (A * μ (HO : Set (ι → F))) := fun A R => by ring
  rw [e1, e1, hL1, hμHM, hμHO]
  ring

end ISMain
p2m_reactivate "P2MW.S_AutomorphicForm_setLIntegral_lattice_norm_det_mul_relIndex_eq_setLIntegral_closure_conj_mul_relIndex.L1Main P2MW.S_AutomorphicForm_setLIntegral_lattice_norm_det_mul_relIndex_eq_setLIntegral_closure_conj_mul_relIndex.ISMain"

end
p2m_reactivate "P2MW.S_AutomorphicForm_setLIntegral_lattice_norm_det_mul_relIndex_eq_setLIntegral_closure_conj_mul_relIndex.L1Main P2MW.S_AutomorphicForm_setLIntegral_lattice_norm_det_mul_relIndex_eq_setLIntegral_closure_conj_mul_relIndex.ISMain"

open L1Toolkit L1Main ISMain in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (δ₀ : GL (Fin 2) L) (c : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ) (u : (AdeleRing (𝓞 K) K)ˣ)
    (hN : AutomorphicForm.normString K L (AdeleRing (𝓞 K) K) σ
        (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c) =
      AutomorphicForm.toTensorGL K L (AdeleRing (𝓞 K) K) (AutomorphicForm.centralScalar (𝓞 K) K u))
    (hns : ∀ (x : GL (Fin 2) L) (z : Lˣ),
      x⁻¹ * δ₀ * Matrix.GeneralLinearGroup.map (σ : L →+* L) x ≠
        Matrix.GeneralLinearGroup.scalar (Fin 2) z)
    (v : HeightOneSpectrum (𝓞 K))
    (τ : Measure ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ
          (AutomorphicForm.tensorPlace K L v (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c))))
    (hτ : τ.IsHaarMeasure)
    (y : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hyD : ∀ g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K),
      (y : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) *
          g.map (Algebra.TensorProduct.includeRight : v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K) *
          ((y⁻¹ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) ∈
        AutomorphicForm.twistedCommutant K L (v.adicCompletion K) σ
          (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] v.adicCompletion K) δ₀))
    (ι : Type) [Fintype ι] [DecidableEq ι]
    (b : ι → Matrix (Fin 2) (Fin 2) L) (hb : LinearIndependent K b)
    (hbspan : ∀ X : Matrix (Fin 2) (Fin 2) L,
      X * (δ₀ : Matrix (Fin 2) (Fin 2) L) = (δ₀ : Matrix (Fin 2) (Fin 2) L) * X.map σ ↔
        X ∈ Submodule.span K (Set.range b))
    (SΛ SM : AddSubgroup (Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)))
    (hSΛ : SΛ = (AddSubgroup.closure
          {X : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K) |
            ∃ (i : ι) (a : v.adicCompletion K), a ∈ v.adicCompletionIntegers K ∧
              X = (b i).map (fun l : L => l ⊗ₜ[K] a)}))
    (hSM : SM = (AddSubgroup.closure
          {X : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K) |
            ∃ g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K),
              (∀ i j, g i j ∈ v.adicCompletionIntegers K) ∧
              X = (y : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) *
                g.map (Algebra.TensorProduct.includeRight :
                  v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K) *
                ((y⁻¹ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
                  Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K))})) :
    SΛ.relIndex SM ≠ 0 ∧ SM.relIndex SΛ ≠ 0 ∧
    (∫⁻ t in {t : ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ
          (AutomorphicForm.tensorPlace K L v (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c))) |
          ∃ a : ι → v.adicCompletion K, (∀ k, a k ∈ v.adicCompletionIntegers K) ∧
            ((t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) = (∑ k, (b k).map fun l : L => l ⊗ₜ[K] a k)}, ENNReal.ofReal ‖Algebra.norm (v.adicCompletion K) (Matrix.det ((t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
            Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)))‖ ∂τ) * ((SΛ.relIndex SM : ℕ) : ℝ≥0∞) =
      (∫⁻ t in {t : ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ
          (AutomorphicForm.tensorPlace K L v (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c))) |
        ((t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) ∈ (SM : Set (Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)))}, ENNReal.ofReal ‖Algebra.norm (v.adicCompletion K) (Matrix.det ((t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
            Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)))‖ ∂τ) * ((SM.relIndex SΛ : ℕ) : ℝ≥0∞) := by
  exact ISMain.main (v := v) σ δ₀ c b hb hbspan h2 hgen u hN hns y hyD SΛ SM hSΛ hSM τ hτ

end S_AutomorphicForm_setLIntegral_lattice_norm_det_mul_relIndex_eq_setLIntegral_closure_conj_mul_relIndex
end P2MW
export P2MW.S_AutomorphicForm_setLIntegral_lattice_norm_det_mul_relIndex_eq_setLIntegral_closure_conj_mul_relIndex (solution)
