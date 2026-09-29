-- Prove2me | solution 1 for AutomorphicForm.setLIntegral_twistedCentralizer_norm_det_mul_measure_pi_integers_eq_setLIntegral_lattice_mul_measure_preimage_of_isAddHaarMeasure
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/4a9836c6-d8e5-5f6e-996c-54e7df542bb6

import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_GodementSection
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_TwistedCommutant
import Theorems.Thm_AutomorphicForm_exists_homeomorph_twistedCommutant_map_mul_scalar_forall_coe_eq_sum_map_tmul_of_linearIndependent
import Theorems.Thm_NumberField_AdicCompletion_map_linearMap_eq_norm_det_inv_smul_of_isAddHaarMeasure
import Theorems.Thm_AutomorphicForm_det_eq_algebraNorm_det_of_forall_mul_map_tmul_one_eq_sum_map_tmul_of_mem_twistedCommutant
import Theorems.Thm_AutomorphicForm_measure_setOf_algebraNorm_det_sum_map_tmul_eq_zero_eq_zero_of_isUnit
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_AutomorphicForm_setLIntegral_twistedCentralizer_norm_det_mul_measure_pi_integers_eq_setLIntegral_lattice_mul_measure_preimage_of_isAddHaarMeasure
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
  exact Continuous.smul (Continuous.inv₀ (continuous_algebraNorm.comp hf) fun x =>
    (isUnit_iff_norm_ne_zero _).1 (hu x)) (continuous_adjE.comp hf)

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
    have h2 : (x : K) = 0 := (algebraMap K F).injective (by first | simpa using h' | (rw [map_zero]; exact h'))
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

section PieceB

variable (h2 : Module.finrank K L = 2) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
  (u : (AdeleRing (𝓞 K) K)ˣ)
  (hN : AutomorphicForm.normString K L (AdeleRing (𝓞 K) K) σ
      (Matrix.GeneralLinearGroup.map
          (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
        Matrix.GeneralLinearGroup.scalar (Fin 2) c) =
    AutomorphicForm.toTensorGL K L (AdeleRing (𝓞 K) K) (AutomorphicForm.centralScalar (𝓞 K) K u))
  (hns : ∀ (x : GL (Fin 2) L) (z : Lˣ),
    x⁻¹ * δ₀ * Matrix.GeneralLinearGroup.map (σ : L →+* L) x ≠
      Matrix.GeneralLinearGroup.scalar (Fin 2) z)
  (hb : LinearIndependent K b)
  (hbspan : ∀ X : Matrix (Fin 2) (Fin 2) L,
    X * (δ₀ : Matrix (Fin 2) (Fin 2) L) = (δ₀ : Matrix (Fin 2) (Fin 2) L) * X.map σ ↔
      X ∈ Submodule.span K (Set.range b))

include h2 hgen u hN hns in
theorem det_Lam (t : ↥(Tv (v := v) σ δ₀ c)) :
    LinearMap.det (Lam (v := v) σ δ₀ c b hb hbspan t) = Algebra.norm F ((t : G) : M2).det := by
  rw [← LinearMap.det_toMatrix (Pi.basisFun F ι)]
  refine AutomorphicForm.det_eq_algebraNorm_det_of_forall_mul_map_tmul_one_eq_sum_map_tmul_of_mem_twistedCommutant
    K L h2 σ hgen δ₀ c u hN hns v ι b hb hbspan ((t : G) : M2)
    ((AutomorphicForm.mem_twistedCentralizer_iff_coe_mem_twistedCommutant _ _).1 t.2) _ fun j => ?_
  have h1 : (b j).map (fun l : L => l ⊗ₜ[K] (1 : F)) = mat (v := v) b (Pi.basisFun F ι j) := by
    rw [Pi.basisFun_apply, mat_single, one_smul]; rfl
  rw [h1, ← mat_Lam (v := v) σ δ₀ c b hb hbspan t]
  unfold mat
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 2
  funext l
  rw [LinearMap.toMatrix_apply, Pi.basisFun_repr]

end PieceB

section Pure

variable (hb : LinearIndependent K b)
  (hbspan : ∀ X : Matrix (Fin 2) (Fin 2) L,
    X * (δ₀ : Matrix (Fin 2) (Fin 2) L) = (δ₀ : Matrix (Fin 2) (Fin 2) L) * X.map σ ↔
      X ∈ Submodule.span K (Set.range b))

theorem t2Space_G : T2Space G := AutomorphicForm.t2Space_tensorGL K L F

theorem secondCountableTopology_G : SecondCountableTopology G := by
  haveI : SecondCountableTopology M2 := inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → E))
  haveI : SecondCountableTopology M2ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

theorem locallyCompactSpace_G : LocallyCompactSpace G := AutomorphicForm.locallyCompactSpace_tensorGL K L F

theorem isTopologicalGroup_G : IsTopologicalGroup G := AutomorphicForm.isTopologicalGroup_tensorGL K L F

attribute [local instance] t2Space_G secondCountableTopology_G locallyCompactSpace_G isTopologicalGroup_G

theorem isClosed_Tv : IsClosed ((Tv (v := v) σ δ₀ c : Subgroup G) : Set G) := by
  have h : ((Tv (v := v) σ δ₀ c : Subgroup G) : Set G) =
      (fun t : G => (t : M2)) ⁻¹' ((Dv (v := v) σ δ₀ c : Subalgebra K M2) : Set M2) := by
    ext t; exact AutomorphicForm.mem_twistedCentralizer_iff_coe_mem_twistedCommutant _ _
  rw [h]
  exact (AutomorphicForm.isClosed_twistedCommutant K L F σ _).preimage Units.continuous_val

theorem locallyCompactSpace_Tv : LocallyCompactSpace ↥(Tv (v := v) σ δ₀ c) :=
  (isClosed_Tv (v := v) σ δ₀ c).isClosedEmbedding_subtypeVal.locallyCompactSpace

theorem secondCountableTopology_Tv : SecondCountableTopology ↥(Tv (v := v) σ δ₀ c) :=
  TopologicalSpace.Subtype.secondCountableTopology _

theorem borelSpace_Tv : BorelSpace ↥(Tv (v := v) σ δ₀ c) := ⟨rfl⟩

attribute [local instance] locallyCompactSpace_Tv secondCountableTopology_Tv borelSpace_Tv

def wt (t : ↥(Tv (v := v) σ δ₀ c)) : ℝ≥0∞ := ENNReal.ofReal ‖Algebra.norm F ((t : G) : M2).det‖

theorem norm_det_pos (t : ↥(Tv (v := v) σ δ₀ c)) : 0 < ‖Algebra.norm F ((t : G) : M2).det‖ :=
  norm_pos_iff.2 ((isUnit_iff_norm_ne_zero _).1 (Matrix.isUnits_det_units _))

theorem wt_ne_zero (t : ↥(Tv (v := v) σ δ₀ c)) : wt (v := v) σ δ₀ c t ≠ 0 := by
  simp only [wt, ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact norm_det_pos (v := v) σ δ₀ c t

theorem wt_ne_top (t : ↥(Tv (v := v) σ δ₀ c)) : wt (v := v) σ δ₀ c t ≠ ⊤ := ENNReal.ofReal_ne_top

theorem continuous_wt : Continuous (wt (v := v) σ δ₀ c) :=
  ENNReal.continuous_ofReal.comp
    (continuous_algebraNorm.comp ((Units.continuous_val.comp continuous_subtype_val).matrix_det)).norm

def Dinv (a : ι → F) : ℝ≥0∞ := ENNReal.ofReal (‖Algebra.norm F (mat (v := v) b a).det‖⁻¹)

theorem Dinv_ne_zero {a : ι → F} (ha : a ∈ good (v := v) b) : Dinv (v := v) b a ≠ 0 := by
  simp only [Dinv, ne_eq, ENNReal.ofReal_eq_zero, not_le]
  have : 0 < ‖Algebra.norm F (mat (v := v) b a).det‖ := norm_pos_iff.2 ((isUnit_iff_norm_ne_zero _).1 ha)
  positivity

theorem Dinv_ne_top (a : ι → F) : Dinv (v := v) b a ≠ ⊤ := ENNReal.ofReal_ne_top

theorem mem_good_Lam_iff (t : ↥(Tv (v := v) σ δ₀ c)) (a : ι → F) :
    Lam (v := v) σ δ₀ c b hb hbspan t a ∈ good (v := v) b ↔ a ∈ good (v := v) b := by
  show IsUnit (mat (v := v) b _).det ↔ IsUnit (mat (v := v) b a).det
  rw [mat_Lam, Matrix.det_mul]
  constructor
  · intro h; exact isUnit_of_mul_isUnit_right h
  · intro h; exact (Matrix.isUnits_det_units _).mul h

theorem chart_Lam (t : ↥(Tv (v := v) σ δ₀ c)) {a : ι → F} (ha : a ∈ good (v := v) b) :
    chart (v := v) σ δ₀ c b hb hbspan (Lam (v := v) σ δ₀ c b hb hbspan t a) = t * chart (v := v) σ δ₀ c b hb hbspan a := by
  have h' : Lam (v := v) σ δ₀ c b hb hbspan t a ∈ good (v := v) b := (mem_good_Lam_iff (v := v) σ δ₀ c b hb hbspan t a).2 ha
  apply Subtype.ext; apply Units.ext
  show (((chart (v := v) σ δ₀ c b hb hbspan _ : Tv (v := v) σ δ₀ c) : G) : M2) = ((t : G) : M2) * (((chart (v := v) σ δ₀ c b hb hbspan a : Tv (v := v) σ δ₀ c) : G) : M2)
  rw [coe_chart_of_mem (v := v) σ δ₀ c b hb hbspan h', coe_chart_of_mem (v := v) σ δ₀ c b hb hbspan ha, mat_Lam]

theorem Dinv_Lam (t : ↥(Tv (v := v) σ δ₀ c)) (a : ι → F) :
    Dinv (v := v) b (Lam (v := v) σ δ₀ c b hb hbspan t a) = (wt (v := v) σ δ₀ c t)⁻¹ * Dinv (v := v) b a := by
  simp only [Dinv, mat_Lam, Matrix.det_mul, map_mul, norm_mul, mul_inv, wt]
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_inv_of_pos (norm_det_pos (v := v) σ δ₀ c t)]

theorem wt_chart_mul_Dinv {a : ι → F} (ha : a ∈ good (v := v) b) :
    wt (v := v) σ δ₀ c (chart (v := v) σ δ₀ c b hb hbspan a) * Dinv (v := v) b a = 1 := by
  simp only [wt, Dinv, coe_chart_of_mem (v := v) σ δ₀ c b hb hbspan ha]
  have hpos : 0 < ‖Algebra.norm F (mat (v := v) b a).det‖ := norm_pos_iff.2 ((isUnit_iff_norm_ne_zero _).1 ha)
  rw [← ENNReal.ofReal_mul (norm_nonneg _), mul_inv_cancel₀ hpos.ne', ENNReal.ofReal_one]

theorem continuous_chart_restrict :
    Continuous ((good (v := v) b).domRestrict (chart (v := v) σ δ₀ c b hb hbspan)) := by

  have hval : ∀ i j, Continuous fun a : ↥(good (v := v) b) =>
      ((((good (v := v) b).domRestrict (chart (v := v) σ δ₀ c b hb hbspan) a : Tv (v := v) σ δ₀ c) : G) : M2) i j := by
    intro i j
    have : (fun a : ↥(good (v := v) b) =>
        ((((good (v := v) b).domRestrict (chart (v := v) σ δ₀ c b hb hbspan) a : Tv (v := v) σ δ₀ c) : G) : M2) i j) =
        fun a : ↥(good (v := v) b) => mat (v := v) b (a : ι → F) i j := by
      funext a; rw [Set.domRestrict_apply, coe_chart_of_mem (v := v) σ δ₀ c b hb hbspan a.2]
    rw [this]
    exact ((continuous_mat (v := v) b).matrix_elem i j).comp continuous_subtype_val
  have hinv : ∀ i j, Continuous fun a : ↥(good (v := v) b) =>
      (((((good (v := v) b).domRestrict (chart (v := v) σ δ₀ c b hb hbspan) a : Tv (v := v) σ δ₀ c) : G)⁻¹ : G) : M2) i j := by
    intro i j
    have : (fun a : ↥(good (v := v) b) =>
        (((((good (v := v) b).domRestrict (chart (v := v) σ δ₀ c b hb hbspan) a : Tv (v := v) σ δ₀ c) : G)⁻¹ : G) : M2) i j) =
        fun a : ↥(good (v := v) b) => Ring.inverse (mat (v := v) b (a : ι → F)).det * (mat (v := v) b (a : ι → F)).adjugate i j := by
      funext a
      rw [Set.domRestrict_apply, coe_chart_inv_of_mem (v := v) σ δ₀ c b hb hbspan a.2, Matrix.smul_apply, smul_eq_mul]
    rw [this]
    refine Continuous.mul ?_ ?_
    · exact continuous_ringInverse_comp ((continuous_mat (v := v) b).matrix_det.comp continuous_subtype_val) fun a => a.2
    · exact (((continuous_mat (v := v) b).comp continuous_subtype_val).matrix_adjugate).matrix_elem i j
  have hG : Continuous fun a : ↥(good (v := v) b) =>
      (((good (v := v) b).domRestrict (chart (v := v) σ δ₀ c b hb hbspan) a : Tv (v := v) σ δ₀ c) : G) := by
    rw [Units.continuous_iff]
    exact ⟨continuous_matrix fun i j => hval i j, continuous_matrix fun i j => hinv i j⟩
  exact Continuous.subtype_mk hG _

include hb hbspan in
theorem one_mem_good_coord : coord (v := v) σ δ₀ c b hb hbspan 1 ∈ good (v := v) b :=
  coord_mem_good (v := v) σ δ₀ c b hb hbspan 1

theorem setOf_exists_eq_preimage_coord (O : Set (ι → F)) :
    {t : ↥(Tv (v := v) σ δ₀ c) | ∃ a : ι → F, a ∈ O ∧ ((t : G) : M2) = mat (v := v) b a} =
      coord (v := v) σ δ₀ c b hb hbspan ⁻¹' O := by
  ext t
  simp only [Set.mem_setOf_eq, Set.mem_preimage]
  constructor
  · rintro ⟨a, ha, hta⟩
    have : coord (v := v) σ δ₀ c b hb hbspan t = a :=
      mat_injective (v := v) σ δ₀ c b hb hbspan (by rw [mat_coord, hta])
    rw [this]; exact ha
  · intro h
    exact ⟨_, h, (mat_coord (v := v) σ δ₀ c b hb hbspan t).symm⟩

theorem preimage_chart_inter_good (W : Set G) :
    chart (v := v) σ δ₀ c b hb hbspan ⁻¹' {t : ↥(Tv (v := v) σ δ₀ c) | (t : G) ∈ W} ∩ good (v := v) b =
      {a : ι → F | ∃ t : ↥(Tv (v := v) σ δ₀ c), (t : G) ∈ W ∧ ((t : G) : M2) = mat (v := v) b a} := by
  ext a
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hW, ha⟩
    exact ⟨_, hW, coe_chart_of_mem (v := v) σ δ₀ c b hb hbspan ha⟩
  · rintro ⟨t, htW, hta⟩
    have ha : a ∈ good (v := v) b := by
      show IsUnit (mat (v := v) b a).det
      rw [← hta]; exact Matrix.isUnits_det_units _
    have hct : chart (v := v) σ δ₀ c b hb hbspan a = t := by
      apply Subtype.ext; apply Units.ext
      rw [coe_chart_of_mem (v := v) σ δ₀ c b hb hbspan ha, hta]
    rw [hct]
    exact ⟨htW, ha⟩

theorem preimage_chart_preimage_coord_inter_good (O : Set (ι → F)) :
    chart (v := v) σ δ₀ c b hb hbspan ⁻¹' (coord (v := v) σ δ₀ c b hb hbspan ⁻¹' O) ∩ good (v := v) b =
      O ∩ good (v := v) b := by
  ext a
  simp only [Set.mem_inter_iff, Set.mem_preimage]
  constructor
  · rintro ⟨hO, ha⟩; rw [coord_chart (v := v) σ δ₀ c b hb hbspan ha] at hO; exact ⟨hO, ha⟩
  · rintro ⟨hO, ha⟩; rw [coord_chart (v := v) σ δ₀ c b hb hbspan ha]; exact ⟨hO, ha⟩

end Pure

section Haar

variable [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]
  (μ : Measure (ι → v.adicCompletion K)) [μ.IsAddHaarMeasure]
  (hb : LinearIndependent K b)
  (hbspan : ∀ X : Matrix (Fin 2) (Fin 2) L,
    X * (δ₀ : Matrix (Fin 2) (Fin 2) L) = (δ₀ : Matrix (Fin 2) (Fin 2) L) * X.map σ ↔
      X ∈ Submodule.span K (Set.range b))

attribute [local instance] t2Space_G secondCountableTopology_G locallyCompactSpace_G isTopologicalGroup_G
  locallyCompactSpace_Tv secondCountableTopology_Tv borelSpace_Tv

theorem measurableMul_Tv : MeasurableMul ↥(Tv (v := v) σ δ₀ c) := inferInstance
theorem borelSpace_coords : BorelSpace (ι → F) := inferInstance

attribute [local instance] measurableMul_Tv borelSpace_coords

theorem measurableSet_good : MeasurableSet (good (v := v) b) := (isOpen_good (v := v) b).measurableSet

theorem measurable_chart : Measurable (chart (v := v) σ δ₀ c b hb hbspan) := by
  refine measurable_of_restrict_of_restrict_compl (measurableSet_good (v := v) b) ?_ ?_
  · exact (continuous_chart_restrict (v := v) σ δ₀ c b hb hbspan).measurable
  · have : (good (v := v) b)ᶜ.domRestrict (chart (v := v) σ δ₀ c b hb hbspan) = fun _ => 1 := by
      funext a
      have ha : ¬ IsUnit (mat (v := v) b (a : ι → F)).det := a.2
      simp [Set.domRestrict_apply, chart, ha]
    rw [this]; exact measurable_const

theorem measurable_coord : Measurable (coord (v := v) σ δ₀ c b hb hbspan) :=
  (continuous_coord (v := v) σ δ₀ c b hb hbspan).measurable

theorem measurable_Dinv : Measurable (Dinv (v := v) b) :=
  ENNReal.measurable_ofReal.comp (continuous_norm_det_mat (v := v) b).norm.measurable.inv

theorem measurable_wt : Measurable (wt (v := v) σ δ₀ c) := (continuous_wt (v := v) σ δ₀ c).measurable

theorem map_Lam (hdet : ∀ t : ↥(Tv (v := v) σ δ₀ c),
      LinearMap.det (Lam (v := v) σ δ₀ c b hb hbspan t) = Algebra.norm F ((t : G) : M2).det)
    (t : ↥(Tv (v := v) σ δ₀ c)) :
    Measure.map (Lam (v := v) σ δ₀ c b hb hbspan t) μ = (wt (v := v) σ δ₀ c t)⁻¹ • μ := by
  haveI : IsModuleTopology F (ι → F) := IsModuleTopology.instPi
  have hne : LinearMap.det (Lam (v := v) σ δ₀ c b hb hbspan t) ≠ 0 := by
    rw [hdet]; exact (isUnit_iff_norm_ne_zero _).1 (Matrix.isUnits_det_units _)
  have h := NumberField.AdicCompletion.map_linearMap_eq_norm_det_inv_smul_of_isAddHaarMeasure K v (ι → F) μ
    (Lam (v := v) σ δ₀ c b hb hbspan t) hne
  rw [hdet] at h
  rw [h, wt, ENNReal.ofReal_inv_of_pos (norm_det_pos (v := v) σ δ₀ c t)]

def mm : Measure ↥(Tv (v := v) σ δ₀ c) :=
  Measure.map (chart (v := v) σ δ₀ c b hb hbspan) ((μ.restrict (good (v := v) b)).withDensity (Dinv (v := v) b))

theorem lintegral_mm {H : ↥(Tv (v := v) σ δ₀ c) → ℝ≥0∞} (hH : Measurable H) :
    ∫⁻ t, H t ∂(mm (v := v) σ δ₀ c b μ hb hbspan) =
      ∫⁻ a in good (v := v) b, H (chart (v := v) σ δ₀ c b hb hbspan a) * Dinv (v := v) b a ∂μ := by
  rw [mm, lintegral_map hH (measurable_chart (v := v) σ δ₀ c b hb hbspan)]
  rw [show (fun a => H (chart (v := v) σ δ₀ c b hb hbspan a)) = H ∘ chart (v := v) σ δ₀ c b hb hbspan from rfl,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_Dinv (v := v) b)
      (hH.comp (measurable_chart (v := v) σ δ₀ c b hb hbspan))]
  refine lintegral_congr fun a => ?_
  simp only [Pi.mul_apply, Function.comp_apply, mul_comm]

theorem mm_apply {A : Set ↥(Tv (v := v) σ δ₀ c)} (hA : MeasurableSet A) :
    mm (v := v) σ δ₀ c b μ hb hbspan A =
      ∫⁻ a in good (v := v) b, A.indicator 1 (chart (v := v) σ δ₀ c b hb hbspan a) * Dinv (v := v) b a ∂μ := by
  rw [← lintegral_indicator_one hA, lintegral_mm (v := v) σ δ₀ c b μ hb hbspan (measurable_one.indicator hA)]

theorem setLIntegral_comp_mul_left
    (hdet : ∀ t : ↥(Tv (v := v) σ δ₀ c),
      LinearMap.det (Lam (v := v) σ δ₀ c b hb hbspan t) = Algebra.norm F ((t : G) : M2).det)
    (t : ↥(Tv (v := v) σ δ₀ c)) {A : Set ↥(Tv (v := v) σ δ₀ c)} (hA : MeasurableSet A) :
    ∫⁻ a in good (v := v) b, A.indicator 1 (t * chart (v := v) σ δ₀ c b hb hbspan a) * Dinv (v := v) b a ∂μ =
      ∫⁻ a in good (v := v) b, A.indicator 1 (chart (v := v) σ δ₀ c b hb hbspan a) * Dinv (v := v) b a ∂μ := by
  set cg : ℝ≥0∞ := (wt (v := v) σ δ₀ c t)⁻¹ with hcg
  have hcg0 : cg ≠ 0 := ENNReal.inv_ne_zero.2 (wt_ne_top (v := v) σ δ₀ c t)
  have hcgt : cg ≠ ⊤ := ENNReal.inv_ne_top.2 (wt_ne_zero (v := v) σ δ₀ c t)
  have hmap := map_Lam (v := v) σ δ₀ c b μ hb hbspan hdet t
  have hLm : Measurable (Lam (v := v) σ δ₀ c b hb hbspan t) := by
    haveI : IsModuleTopology F (ι → F) := IsModuleTopology.instPi
    exact (IsModuleTopology.continuous_of_linearMap (Lam (v := v) σ δ₀ c b hb hbspan t)).measurable
  set Hh : (ι → F) → ℝ≥0∞ := (good (v := v) b).indicator fun a =>
    A.indicator 1 (chart (v := v) σ δ₀ c b hb hbspan a) * Dinv (v := v) b a with hHh
  have hHm : Measurable Hh := by
    refine Measurable.indicator ?_ (measurableSet_good (v := v) b)
    exact ((measurable_one.indicator hA).comp (measurable_chart (v := v) σ δ₀ c b hb hbspan)).mul
      (measurable_Dinv (v := v) b)
  have h1 : ∫⁻ a, Hh (Lam (v := v) σ δ₀ c b hb hbspan t a) ∂μ = cg * ∫⁻ a, Hh a ∂μ := by
    have hlm : ∫⁻ a, Hh a ∂(Measure.map (Lam (v := v) σ δ₀ c b hb hbspan t) μ) =
        ∫⁻ a, Hh (Lam (v := v) σ δ₀ c b hb hbspan t a) ∂μ := lintegral_map hHm hLm
    rw [hmap, lintegral_smul_measure, smul_eq_mul] at hlm
    exact hlm.symm
  have h2 : ∀ a : ι → F, Hh (Lam (v := v) σ δ₀ c b hb hbspan t a) =
      cg * (good (v := v) b).indicator (fun a => A.indicator 1 (t * chart (v := v) σ δ₀ c b hb hbspan a) * Dinv (v := v) b a) a := by
    intro a
    by_cases ha : a ∈ good (v := v) b
    · rw [hHh, Set.indicator_of_mem ((mem_good_Lam_iff (v := v) σ δ₀ c b hb hbspan t a).2 ha), Set.indicator_of_mem ha,
        chart_Lam (v := v) σ δ₀ c b hb hbspan t ha, Dinv_Lam, ← hcg]
      ring
    · rw [hHh, Set.indicator_of_notMem (fun h => ha ((mem_good_Lam_iff (v := v) σ δ₀ c b hb hbspan t a).1 h)),
        Set.indicator_of_notMem ha, mul_zero]
  simp_rw [h2] at h1
  rw [lintegral_const_mul _ (by
      refine Measurable.indicator ?_ (measurableSet_good (v := v) b)
      exact ((measurable_one.indicator hA).comp ((measurable_const_mul t).comp
        (measurable_chart (v := v) σ δ₀ c b hb hbspan))).mul (measurable_Dinv (v := v) b))] at h1
  have h3 := (ENNReal.mul_right_inj hcg0 hcgt).1 h1
  rw [lintegral_indicator (measurableSet_good (v := v) b), hHh, lintegral_indicator (measurableSet_good (v := v) b)] at h3
  exact h3

theorem isMulLeftInvariant_mm
    (hdet : ∀ t : ↥(Tv (v := v) σ δ₀ c),
      LinearMap.det (Lam (v := v) σ δ₀ c b hb hbspan t) = Algebra.norm F ((t : G) : M2).det) :
    (mm (v := v) σ δ₀ c b μ hb hbspan).IsMulLeftInvariant := by
  refine ⟨fun t => ?_⟩
  ext A hA
  rw [Measure.map_apply (measurable_const_mul t) hA, mm_apply (v := v) σ δ₀ c b μ hb hbspan hA,
    mm_apply (v := v) σ δ₀ c b μ hb hbspan (measurable_const_mul t hA)]
  have : ∀ a : ι → F, ((fun s : ↥(Tv (v := v) σ δ₀ c) => t * s) ⁻¹' A).indicator (1 : ↥(Tv (v := v) σ δ₀ c) → ℝ≥0∞)
      (chart (v := v) σ δ₀ c b hb hbspan a) = A.indicator 1 (t * chart (v := v) σ δ₀ c b hb hbspan a) := by
    intro a; simp only [Set.indicator, Set.mem_preimage, Pi.one_apply]
  simp_rw [this]
  exact setLIntegral_comp_mul_left (v := v) σ δ₀ c b μ hb hbspan hdet t hA

theorem isFiniteMeasureOnCompacts_mm : IsFiniteMeasureOnCompacts (mm (v := v) σ δ₀ c b μ hb hbspan) := by
  refine ⟨fun C hC => ?_⟩
  rw [mm_apply (v := v) σ δ₀ c b μ hb hbspan hC.measurableSet]
  by_cases hCe : C = ∅
  · subst hCe; simp
  have hne : C.Nonempty := Set.nonempty_iff_ne_empty.2 hCe
  have hcont : Continuous fun t : ↥(Tv (v := v) σ δ₀ c) => ‖Algebra.norm F ((t : G) : M2).det‖ :=
    (continuous_algebraNorm.comp ((Units.continuous_val.comp continuous_subtype_val).matrix_det)).norm
  obtain ⟨t₀, ht₀, hmin⟩ := hC.exists_isMinOn hne (hcont.continuousOn (s := C))
  set δ : ℝ := ‖Algebra.norm F ((t₀ : G) : M2).det‖ with hδ
  have hδ0 : 0 < δ := norm_det_pos (v := v) σ δ₀ c t₀
  set Cf : Set (ι → F) := coord (v := v) σ δ₀ c b hb hbspan '' C with hCf
  have hCfc : IsCompact Cf := hC.image (continuous_coord (v := v) σ δ₀ c b hb hbspan)
  have hbound : ∀ a : ι → F,
      (good (v := v) b).indicator (fun a => C.indicator (1 : ↥(Tv (v := v) σ δ₀ c) → ℝ≥0∞)
        (chart (v := v) σ δ₀ c b hb hbspan a) * Dinv (v := v) b a) a ≤
      Cf.indicator (fun _ => ENNReal.ofReal δ⁻¹) a := by
    intro a
    by_cases ha : a ∈ good (v := v) b
    · rw [Set.indicator_of_mem ha]
      by_cases haC : chart (v := v) σ δ₀ c b hb hbspan a ∈ C
      · have haCf : a ∈ Cf := ⟨_, haC, coord_chart (v := v) σ δ₀ c b hb hbspan ha⟩
        rw [Set.indicator_of_mem haC, Set.indicator_of_mem haCf, Pi.one_apply, one_mul]
        simp only [Dinv]
        apply ENNReal.ofReal_le_ofReal
        have hle : δ ≤ ‖Algebra.norm F (mat (v := v) b a).det‖ := by
          have := hmin haC
          simp only [Set.mem_setOf_eq] at this
          rw [coe_chart_of_mem (v := v) σ δ₀ c b hb hbspan ha] at this
          exact this
        exact inv_anti₀ hδ0 hle
      · rw [Set.indicator_of_notMem haC, zero_mul]; exact zero_le
    · rw [Set.indicator_of_notMem ha]; exact zero_le
  calc ∫⁻ a in good (v := v) b, C.indicator (1 : ↥(Tv (v := v) σ δ₀ c) → ℝ≥0∞) (chart (v := v) σ δ₀ c b hb hbspan a) * Dinv (v := v) b a ∂μ
      = ∫⁻ a, (good (v := v) b).indicator (fun a => C.indicator (1 : ↥(Tv (v := v) σ δ₀ c) → ℝ≥0∞)
          (chart (v := v) σ δ₀ c b hb hbspan a) * Dinv (v := v) b a) a ∂μ := by
        rw [lintegral_indicator (measurableSet_good (v := v) b)]
    _ ≤ ∫⁻ a, Cf.indicator (fun _ => ENNReal.ofReal δ⁻¹) a ∂μ := lintegral_mono hbound
    _ = ENNReal.ofReal δ⁻¹ * μ Cf := lintegral_indicator_const hCfc.measurableSet _
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hCfc.measure_lt_top

theorem mm_univ_ne_zero : mm (v := v) σ δ₀ c b μ hb hbspan Set.univ ≠ 0 := by
  rw [mm_apply (v := v) σ δ₀ c b μ hb hbspan MeasurableSet.univ]
  simp only [Set.indicator_univ, Pi.one_apply, one_mul]
  intro h
  rw [← lintegral_indicator (measurableSet_good (v := v) b),
    lintegral_eq_zero_iff ((measurable_Dinv (v := v) b).indicator (measurableSet_good (v := v) b))] at h
  have hpos : 0 < μ (good (v := v) b) :=
    (isOpen_good (v := v) b).measure_pos μ ⟨_, one_mem_good_coord (v := v) σ δ₀ c b hb hbspan⟩
  have hae : ∀ᵐ a ∂μ, a ∉ good (v := v) b := by
    filter_upwards [h] with a ha
    intro hag
    rw [Pi.zero_apply, Set.indicator_of_mem hag] at ha
    exact Dinv_ne_zero (v := v) b hag ha
  rw [← measure_eq_zero_iff_ae_notMem] at hae
  exact absurd hae hpos.ne'

theorem mm_eq_smul (τ : Measure ↥(Tv (v := v) σ δ₀ c)) [τ.IsHaarMeasure]
    (hdet : ∀ t : ↥(Tv (v := v) σ δ₀ c),
      LinearMap.det (Lam (v := v) σ δ₀ c b hb hbspan t) = Algebra.norm F ((t : G) : M2).det) :
    ∃ c₀ : ℝ≥0∞, c₀ ≠ 0 ∧ c₀ ≠ ⊤ ∧ mm (v := v) σ δ₀ c b μ hb hbspan = c₀ • τ := by
  haveI := isMulLeftInvariant_mm (v := v) σ δ₀ c b μ hb hbspan hdet
  haveI := isFiniteMeasureOnCompacts_mm (v := v) σ δ₀ c b μ hb hbspan
  have heq := Measure.isMulLeftInvariant_eq_smul (mm (v := v) σ δ₀ c b μ hb hbspan) τ
  set c₀ : ℝ≥0 := (mm (v := v) σ δ₀ c b μ hb hbspan).haarScalarFactor τ with hc₀
  have hc₀0 : c₀ ≠ 0 := by
    intro h0
    apply mm_univ_ne_zero (v := v) σ δ₀ c b μ hb hbspan
    rw [heq, h0]; simp
  refine ⟨(c₀ : ℝ≥0∞), ENNReal.coe_ne_zero.2 hc₀0, ENNReal.coe_ne_top, ?_⟩
  rw [heq, ENNReal.smul_def]

theorem setLIntegral_wt_eq (τ : Measure ↥(Tv (v := v) σ δ₀ c)) {c₀ : ℝ≥0∞} (hc0 : c₀ ≠ 0) (hct : c₀ ≠ ⊤)
    (hmm : mm (v := v) σ δ₀ c b μ hb hbspan = c₀ • τ)
    {A : Set ↥(Tv (v := v) σ δ₀ c)} (hA : MeasurableSet A) :
    ∫⁻ t in A, wt (v := v) σ δ₀ c t ∂τ = c₀⁻¹ * μ (chart (v := v) σ δ₀ c b hb hbspan ⁻¹' A ∩ good (v := v) b) := by
  have h1 : ∫⁻ t in A, wt (v := v) σ δ₀ c t ∂(mm (v := v) σ δ₀ c b μ hb hbspan) =
      c₀ * ∫⁻ t in A, wt (v := v) σ δ₀ c t ∂τ := by
    rw [hmm, Measure.restrict_smul, lintegral_smul_measure, smul_eq_mul]
  have h2 : ∫⁻ t in A, wt (v := v) σ δ₀ c t ∂(mm (v := v) σ δ₀ c b μ hb hbspan) =
      μ (chart (v := v) σ δ₀ c b hb hbspan ⁻¹' A ∩ good (v := v) b) := by
    rw [← lintegral_indicator hA,
      lintegral_mm (v := v) σ δ₀ c b μ hb hbspan ((measurable_wt (v := v) σ δ₀ c).indicator hA)]
    have hpt : ∀ a ∈ good (v := v) b,
        A.indicator (wt (v := v) σ δ₀ c) (chart (v := v) σ δ₀ c b hb hbspan a) * Dinv (v := v) b a =
          (chart (v := v) σ δ₀ c b hb hbspan ⁻¹' A).indicator 1 a := by
      intro a ha
      by_cases hA' : chart (v := v) σ δ₀ c b hb hbspan a ∈ A
      · rw [Set.indicator_of_mem hA', Set.indicator_of_mem (show a ∈ _ ⁻¹' A from hA'), Pi.one_apply,
          wt_chart_mul_Dinv (v := v) σ δ₀ c b hb hbspan ha]
      · rw [Set.indicator_of_notMem hA', Set.indicator_of_notMem (show a ∉ _ ⁻¹' A from hA'), zero_mul]
    rw [setLIntegral_congr_fun (measurableSet_good (v := v) b) hpt,
      lintegral_indicator_one ((measurable_chart (v := v) σ δ₀ c b hb hbspan) hA),
      Measure.restrict_apply ((measurable_chart (v := v) σ δ₀ c b hb hbspan) hA)]
  rw [h2] at h1
  rw [h1, ← mul_assoc, ENNReal.inv_mul_cancel hc0 hct, one_mul]

theorem measurableSet_integralBox :
    MeasurableSet {a : ι → F | ∀ k, a k ∈ v.adicCompletionIntegers K} := by
  have hO : IsClosed ((v.adicCompletionIntegers K : Set F)) := by
    have h1 : ((v.adicCompletionIntegers K : Set F)) = ((Valued.v.integer : Subring F) : Set F) := by
      ext x
      rw [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 K) K v, SetLike.mem_coe,
        Valuation.mem_integer_iff]
    rw [h1]
    exact Valued.isClosed_integer (R := F)
  have : {a : ι → F | ∀ k, a k ∈ v.adicCompletionIntegers K} =
      ⋂ k, (fun a : ι → F => a k) ⁻¹' (v.adicCompletionIntegers K : Set F) := by
    ext a; simp
  rw [this]
  exact MeasurableSet.iInter fun k => (hO.preimage (continuous_apply k)).measurableSet

include hb hbspan in

theorem main
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
    (τ : Measure ↥(Tv (v := v) σ δ₀ c)) (hτ : τ.IsHaarMeasure)
    (hnull : μ (good (v := v) b)ᶜ = 0)
    (W : Set G) (hW : MeasurableSet[AutomorphicForm.glBorelOf (L ⊗[K] v.adicCompletion K)] W) :
    (∫⁻ t in {t : ↥(Tv (v := v) σ δ₀ c) | (t : G) ∈ W}, wt (v := v) σ δ₀ c t ∂τ) *
        μ {a : ι → F | ∀ k, a k ∈ v.adicCompletionIntegers K} =
      (∫⁻ t in {t : ↥(Tv (v := v) σ δ₀ c) | ∃ a : ι → F, (∀ k, a k ∈ v.adicCompletionIntegers K) ∧
          ((t : G) : M2) = mat (v := v) b a}, wt (v := v) σ δ₀ c t ∂τ) *
        μ {a : ι → F | ∃ t : ↥(Tv (v := v) σ δ₀ c), (t : G) ∈ W ∧ ((t : G) : M2) = mat (v := v) b a} := by
  haveI := hτ
  set O : Set (ι → F) := {a : ι → F | ∀ k, a k ∈ v.adicCompletionIntegers K} with hOdef
  have hOm : MeasurableSet O := measurableSet_integralBox (v := v)
  have hdet := fun t => det_Lam (v := v) σ δ₀ c b h2 hgen u hN hns hb hbspan t
  obtain ⟨c₀, hc0, hct, hmm⟩ := mm_eq_smul (v := v) σ δ₀ c b μ hb hbspan τ hdet

  have hSW : MeasurableSet {t : ↥(Tv (v := v) σ δ₀ c) | (t : G) ∈ W} := by
    letI : MeasurableSpace G := AutomorphicForm.glBorelOf (L ⊗[K] v.adicCompletion K)
    haveI : BorelSpace G := AutomorphicForm.borelSpace_glBorelOf _
    exact (continuous_subtype_val.measurable : Measurable fun t : ↥(Tv (v := v) σ δ₀ c) => (t : G)) hW
  have hSΛeq : {t : ↥(Tv (v := v) σ δ₀ c) | ∃ a : ι → F, (∀ k, a k ∈ v.adicCompletionIntegers K) ∧
      ((t : G) : M2) = mat (v := v) b a} = coord (v := v) σ δ₀ c b hb hbspan ⁻¹' O :=
    setOf_exists_eq_preimage_coord (v := v) σ δ₀ c b hb hbspan O
  have hSΛ : MeasurableSet (coord (v := v) σ δ₀ c b hb hbspan ⁻¹' O) :=
    measurable_coord (v := v) σ δ₀ c b hb hbspan hOm
  rw [hSΛeq, setLIntegral_wt_eq (v := v) σ δ₀ c b μ hb hbspan τ hc0 hct hmm hSW,
    setLIntegral_wt_eq (v := v) σ δ₀ c b μ hb hbspan τ hc0 hct hmm hSΛ,
    preimage_chart_inter_good, preimage_chart_preimage_coord_inter_good]

  have hμO : μ O = μ (O ∩ good (v := v) b) := by
    have h := measure_inter_add_diff O (measurableSet_good (v := v) b) (μ := μ)
    have h0 : μ (O \ good (v := v) b) = 0 :=
      measure_mono_null (fun a ha => ha.2) hnull
    rw [h0, add_zero] at h
    exact h.symm
  rw [hμO]
  ring

end Haar

end L1Main
p2m_reactivate "P2MW.S_AutomorphicForm_setLIntegral_twistedCentralizer_norm_det_mul_measure_pi_integers_eq_setLIntegral_lattice_mul_measure_preimage_of_isAddHaarMeasure.L1Main"

end
p2m_reactivate "P2MW.S_AutomorphicForm_setLIntegral_twistedCentralizer_norm_det_mul_measure_pi_integers_eq_setLIntegral_lattice_mul_measure_preimage_of_isAddHaarMeasure.L1Main"

open L1Main L1Toolkit in
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
    (ι : Type) [Fintype ι] [DecidableEq ι]
    (b : ι → Matrix (Fin 2) (Fin 2) L) (hb : LinearIndependent K b)
    (hbspan : ∀ X : Matrix (Fin 2) (Fin 2) L,
      X * (δ₀ : Matrix (Fin 2) (Fin 2) L) = (δ₀ : Matrix (Fin 2) (Fin 2) L) * X.map σ ↔
        X ∈ Submodule.span K (Set.range b))
    [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]
    (μ : Measure (ι → v.adicCompletion K)) [μ.IsAddHaarMeasure]
    (W : Set (GL (Fin 2) (L ⊗[K] v.adicCompletion K)))
    (hW : MeasurableSet[AutomorphicForm.glBorelOf (L ⊗[K] v.adicCompletion K)] W) :
    (∫⁻ t in {t : ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ
          (AutomorphicForm.tensorPlace K L v (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c))) |
          (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) ∈ W}, ENNReal.ofReal ‖Algebra.norm (v.adicCompletion K) (Matrix.det ((t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
            Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)))‖ ∂τ) *
        μ {a : ι → v.adicCompletion K | ∀ k, a k ∈ v.adicCompletionIntegers K} =
      (∫⁻ t in {t : ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ
          (AutomorphicForm.tensorPlace K L v (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c))) |
          ∃ a : ι → v.adicCompletion K, (∀ k, a k ∈ v.adicCompletionIntegers K) ∧
            ((t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) = (∑ k, (b k).map fun l : L => l ⊗ₜ[K] a k)}, ENNReal.ofReal ‖Algebra.norm (v.adicCompletion K) (Matrix.det ((t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
            Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)))‖ ∂τ) *
        μ {a : ι → v.adicCompletion K | ∃ t : ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ
          (AutomorphicForm.tensorPlace K L v (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c))),
          (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) ∈ W ∧
            ((t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) = (∑ k, (b k).map fun l : L => l ⊗ₜ[K] a k)} := by
  have hnull : μ (L1Main.good (v := v) b)ᶜ = 0 := by
    have h := AutomorphicForm.measure_setOf_algebraNorm_det_sum_map_tmul_eq_zero_eq_zero_of_isUnit K L v ι b
      (L1Main.coord (v := v) σ δ₀ c b hb hbspan 1) (L1Main.coord_mem_good (v := v) σ δ₀ c b hb hbspan 1) μ
    have hset : (L1Main.good (v := v) b)ᶜ = {a : ι → v.adicCompletion K |
        Algebra.norm (v.adicCompletion K) (Matrix.det (∑ i : ι, (b i).map fun l : L => l ⊗ₜ[K] a i :
          Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K))) = 0} := by
      ext a
      rw [Set.mem_compl_iff, Set.mem_setOf_eq]
      show ¬ IsUnit (L1Main.mat (v := v) b a).det ↔ _
      rw [L1Toolkit.isUnit_iff_norm_ne_zero, not_not]
      rfl
    rw [hset]; exact h
  exact L1Main.main (v := v) σ δ₀ c b μ hb hbspan h2 hgen u hN hns τ hτ hnull W hW

end S_AutomorphicForm_setLIntegral_twistedCentralizer_norm_det_mul_measure_pi_integers_eq_setLIntegral_lattice_mul_measure_preimage_of_isAddHaarMeasure
end P2MW
export P2MW.S_AutomorphicForm_setLIntegral_twistedCentralizer_norm_det_mul_measure_pi_integers_eq_setLIntegral_lattice_mul_measure_preimage_of_isAddHaarMeasure (solution)
