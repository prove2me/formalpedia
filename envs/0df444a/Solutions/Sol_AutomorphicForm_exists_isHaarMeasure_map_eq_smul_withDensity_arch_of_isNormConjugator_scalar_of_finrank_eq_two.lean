-- Prove2me | solution 1 for AutomorphicForm.exists_isHaarMeasure_map_eq_smul_withDensity_arch_of_isNormConjugator_scalar_of_finrank_eq_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/3de34daf-2836-5fc5-aa37-abd87cf6d99c

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Theorems.Thm_MeasureTheory_Measure_exists_isHaarMeasure_subgroup_units_map_val_eq_withDensity_of_abs_det_eq
import Theorems.Thm_NumberField_InfiniteAdeleRing_traceForm_nondegenerate_and_traceForm_tensorProduct_nondegenerate
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_isHaarMeasure_map_eq_smul_withDensity_arch_of_isNormConjugator_scalar_of_finrank_eq_two

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open IsDedekindDomain NumberField MeasureTheory MeasureTheory.Measure Topology TopologicalSpace Set
open TensorProduct Matrix
open scoped TensorProduct.RightActions NNReal ENNReal

noncomputable section

namespace AutomorphicForm
p2m_export "AutomorphicForm" "isTopologicalRing_tensor t2Space_tensor centralizerBorel toTensorGL sigmaTensor sigmaGL normString IsNormConjugator twistedCentralizer twistedCentralizerBorel mem_sigmaCentralizer_iff"
namespace ArchGramHaar
p2m_open "AutomorphicForm"

section Structures

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

abbrev F : Type := InfiniteAdeleRing K

abbrev E : Type := L ⊗[K] InfiniteAdeleRing K

abbrev MF : Type := Matrix (Fin 2) (Fin 2) (F K)

abbrev ME : Type := Matrix (Fin 2) (Fin 2) (E K L)

abbrev algRF : Algebra ℝ (F K) :=
  ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm.toRingHom.comp
    (algebraMap ℝ (mixedEmbedding.mixedSpace K))).toAlgebra

attribute [local instance] algRF

abbrev algRE : Algebra ℝ (E K L) :=
  ((Algebra.TensorProduct.includeRight : InfiniteAdeleRing K →ₐ[K] L ⊗[K] InfiniteAdeleRing K).toRingHom.comp
    (algebraMap ℝ (InfiniteAdeleRing K))).toAlgebra

attribute [local instance] algRE

def mixedAlgEquiv : F K ≃ₐ[ℝ] mixedEmbedding.mixedSpace K :=
  AlgEquiv.ofRingEquiv (f := InfiniteAdeleRing.ringEquiv_mixedSpace K) fun r => by
    show InfiniteAdeleRing.ringEquiv_mixedSpace K
        ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (algebraMap ℝ (mixedEmbedding.mixedSpace K) r)) = _
    exact RingEquiv.apply_symm_apply _ _

scoped instance moduleFree_F : Module.Free ℝ (F K) :=
  Module.Free.of_equiv (mixedAlgEquiv K).symm.toLinearEquiv

scoped instance moduleFinite_F : Module.Finite ℝ (F K) :=
  Module.Finite.equiv (mixedAlgEquiv K).symm.toLinearEquiv

theorem continuous_ringEquiv_mixedSpace_symm : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm := by
  apply continuous_pi
  intro v
  by_cases hv : InfinitePlace.IsReal v
  · have key : (fun y : mixedEmbedding.mixedSpace K => (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm y v)
        = fun y => (InfinitePlace.Completion.isometryEquivRealOfIsReal hv).symm (y.1 ⟨v, hv⟩) := by
      funext y
      apply (InfinitePlace.Completion.isometryEquivRealOfIsReal hv).injective
      rw [IsometryEquiv.apply_symm_apply]
      exact congrArg (fun z : mixedEmbedding.mixedSpace K => z.1 ⟨v, hv⟩)
        ((InfiniteAdeleRing.ringEquiv_mixedSpace K).apply_symm_apply y)
    rw [key]
    exact (InfinitePlace.Completion.isometryEquivRealOfIsReal hv).symm.continuous.comp
      ((continuous_apply _).comp continuous_fst)
  · have hc : InfinitePlace.IsComplex v := InfinitePlace.not_isReal_iff_isComplex.1 hv
    have key : (fun y : mixedEmbedding.mixedSpace K => (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm y v)
        = fun y => (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hc).symm (y.2 ⟨v, hc⟩) := by
      funext y
      apply (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hc).injective
      rw [IsometryEquiv.apply_symm_apply]
      exact congrArg (fun z : mixedEmbedding.mixedSpace K => z.2 ⟨v, hc⟩)
        ((InfiniteAdeleRing.ringEquiv_mixedSpace K).apply_symm_apply y)
    rw [key]
    exact (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hc).symm.continuous.comp
      ((continuous_apply _).comp continuous_snd)

theorem continuous_algebraMap_RF : Continuous (algebraMap ℝ (F K)) :=
  (continuous_ringEquiv_mixedSpace_symm K).comp (continuous_algebraMap ℝ (mixedEmbedding.mixedSpace K))

scoped instance continuousSMul_RF : ContinuousSMul ℝ (F K) :=
  ⟨((continuous_algebraMap_RF K).comp continuous_fst).mul continuous_snd⟩

theorem algebraMap_FE_apply (a : F K) : algebraMap (F K) (E K L) a = (1 : L) ⊗ₜ a := rfl

scoped instance isScalarTower_RFE : IsScalarTower ℝ (F K) (E K L) :=
  IsScalarTower.of_algebraMap_eq (R := ℝ) (S := F K) (A := E K L) fun _ => rfl

scoped instance moduleFree_FE : Module.Free (F K) (E K L) := inferInstance
scoped instance moduleFinite_FE : Module.Finite (F K) (E K L) := inferInstance

scoped instance moduleFinite_RE : Module.Finite ℝ (E K L) := Module.Finite.trans (F K) (E K L)

scoped instance moduleFree_RE : Module.Free ℝ (E K L) := by
  obtain ⟨⟨ι, bF⟩⟩ := (inferInstance : Module.Free ℝ (F K))
  obtain ⟨⟨κ, bE⟩⟩ := (inferInstance : Module.Free (F K) (E K L))
  exact Module.Free.of_basis (bF.smulTower bE)

theorem finrank_FE (h2 : Module.finrank K L = 2) : Module.finrank (F K) (E K L) = 2 := by
  have b := TensorProduct.RightActions.Algebra.TensorProduct.basis (F K) (Module.finBasis K L)
  rw [Module.finrank_eq_card_basis b, Fintype.card_fin, h2]

theorem norm_algebraMap_FE (h2 : Module.finrank K L = 2) (a : F K) :
    Algebra.norm ℝ (algebraMap (F K) (E K L) a) = (Algebra.norm ℝ a) ^ 2 := by
  rw [← Algebra.norm_norm (S := F K), Algebra.norm_algebraMap, finrank_FE K L h2, map_pow]

scoped instance instIsTopologicalRingE : IsTopologicalRing (E K L) := isTopologicalRing_tensor K L _
scoped instance instT2E : T2Space (E K L) := t2Space_tensor K L _

theorem continuous_algebraMap_FE : Continuous (algebraMap (F K) (E K L)) :=
  IsModuleTopology.continuous_of_linearMap (Algebra.linearMap (F K) (E K L))

theorem continuous_algebraMap_RE : Continuous (algebraMap ℝ (E K L)) :=
  (continuous_algebraMap_FE K L).comp (continuous_algebraMap_RF K)

scoped instance continuousSMul_RE : ContinuousSMul ℝ (E K L) :=
  ⟨((continuous_algebraMap_RE K L).comp continuous_fst).mul continuous_snd⟩

scoped instance instT2ME : T2Space (ME K L) := inferInstanceAs (T2Space (Fin 2 → Fin 2 → E K L))
scoped instance instT2MF : T2Space (MF K) := inferInstanceAs (T2Space (Fin 2 → Fin 2 → F K))
scoped instance instTAG_MF : IsTopologicalAddGroup (MF K) := inferInstance
scoped instance instCSM_MF : ContinuousSMul ℝ (MF K) := inferInstance
scoped instance instTAG_ME : IsTopologicalAddGroup (ME K L) := inferInstance
scoped instance instCSM_ME : ContinuousSMul ℝ (ME K L) := inferInstance
scoped instance instTR_ME : IsTopologicalRing (ME K L) := inferInstance
scoped instance instTR_MF : IsTopologicalRing (MF K) := inferInstance
scoped instance instFD_ME : FiniteDimensional ℝ (ME K L) := inferInstance
scoped instance instFD_MF : FiniteDimensional ℝ (MF K) := inferInstance

scoped instance instMeasurableSpaceMF : MeasurableSpace (MF K) := borel _
scoped instance instBorelSpaceMF : BorelSpace (MF K) := ⟨rfl⟩
scoped instance instMeasurableSpaceME : MeasurableSpace (ME K L) := borel _
scoped instance instBorelSpaceME : BorelSpace (ME K L) := ⟨rfl⟩

def halfTrace : L →ₗ[K] K := (2 : K)⁻¹ • Algebra.trace K L

theorem halfTrace_one (h2 : Module.finrank K L = 2) : halfTrace K L 1 = 1 := by
  simp only [halfTrace, LinearMap.smul_apply, smul_eq_mul]
  rw [show (1 : L) = algebraMap K L 1 from (map_one _).symm, Algebra.trace_algebraMap, h2]
  norm_num

def proj : E K L →ₗ[F K] F K where
  toFun := TensorProduct.lift ((LinearMap.lsmul K (F K)).comp (halfTrace K L))
  map_add' x y := map_add _ x y
  map_smul' f x := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul l a =>
        rw [TensorProduct.RightActions.smul_def, TensorProduct.comm_tmul, TensorProduct.smul_tmul',
          TensorProduct.comm_symm_tmul]
        simp only [TensorProduct.lift.tmul, LinearMap.comp_apply, LinearMap.lsmul_apply, RingHom.id_apply,
          smul_eq_mul]
        rw [Algebra.smul_def, Algebra.smul_def]
        ring
    | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]

theorem proj_tmul (l : L) (a : F K) : proj K L (l ⊗ₜ a) = halfTrace K L l • a := by
  show TensorProduct.lift _ (l ⊗ₜ a) = _
  simp [TensorProduct.lift.tmul]

theorem proj_algebraMap (h2 : Module.finrank K L = 2) (a : F K) : proj K L (algebraMap (F K) (E K L) a) = a := by
  rw [algebraMap_FE_apply, proj_tmul, halfTrace_one K L h2, one_smul]

theorem continuous_proj : Continuous (proj K L) := IsModuleTopology.continuous_of_linearMap (proj K L)

def iotaM : MF K →ₗ[ℝ] ME K L := ((Algebra.linearMap (F K) (E K L)).restrictScalars ℝ).mapMatrix

theorem iotaM_apply (Y : MF K) :
    iotaM K L Y = Y.map (Algebra.TensorProduct.includeRight : InfiniteAdeleRing K →ₐ[K] L ⊗[K] InfiniteAdeleRing K) :=
  rfl

theorem iotaM_apply' (Y : MF K) : iotaM K L Y = (algebraMap (F K) (E K L)).mapMatrix Y := rfl

def projM : ME K L → MF K := fun X => X.map (proj K L)

theorem projM_iotaM (h2 : Module.finrank K L = 2) (Y : MF K) : projM K L (iotaM K L Y) = Y := by
  ext i j
  exact proj_algebraMap K L h2 (Y i j)

theorem injective_iotaM (h2 : Module.finrank K L = 2) : Function.Injective (iotaM K L) :=
  Function.LeftInverse.injective (g := projM K L) fun Y => projM_iotaM K L h2 Y

theorem continuous_iotaM : Continuous (iotaM K L) := continuous_id.matrix_map (continuous_algebraMap_FE K L)

theorem continuous_projM : Continuous (projM K L) := continuous_id.matrix_map (continuous_proj K L)

theorem measurable_iotaM : Measurable (iotaM K L) := (continuous_iotaM K L).measurable

theorem isClosed_range_iotaM (h2 : Module.finrank K L = 2) : IsClosed (Set.range (iotaM K L)) := by
  have : Set.range (iotaM K L) = {X | iotaM K L (projM K L X) = X} := by
    ext X
    constructor
    · rintro ⟨Y, rfl⟩
      show iotaM K L (projM K L (iotaM K L Y)) = iotaM K L Y
      rw [projM_iotaM K L h2]
    · intro hX
      exact ⟨projM K L X, hX⟩
  rw [this]
  exact isClosed_eq ((continuous_iotaM K L).comp (continuous_projM K L)) continuous_id

theorem measurableEmbedding_iotaM (h2 : Module.finrank K L = 2) : MeasurableEmbedding (iotaM K L) :=
  MeasurableEmbedding.of_measurable_inverse (measurable_iotaM K L) (isClosed_range_iotaM K L h2).measurableSet
    (continuous_projM K L).measurable fun Y => projM_iotaM K L h2 Y

theorem withDensity_map_of_measurableEmbedding {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {f : α → β} (hf : MeasurableEmbedding f) (μ : Measure α) (g : β → ℝ≥0∞) :
    (Measure.map f μ).withDensity g = Measure.map f (μ.withDensity (g ∘ f)) := by
  ext s hs
  rw [withDensity_apply _ hs, hf.restrict_map, hf.lintegral_map, hf.map_apply,
    withDensity_apply _ (hf.measurable hs)]
  simp only [Function.comp_apply]

theorem iotaM_mul (X Y : MF K) : iotaM K L (X * Y) = iotaM K L X * iotaM K L Y := by
  rw [iotaM_apply', iotaM_apply', iotaM_apply', RingHom.map_mul]

theorem iotaM_one : iotaM K L 1 = 1 := by rw [iotaM_apply', RingHom.map_one]

theorem det_iotaM (Y : MF K) : (iotaM K L Y).det = algebraMap (F K) (E K L) Y.det := by
  rw [iotaM_apply', ← RingHom.map_det]

end Structures

section Galois

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)

include h2 in
theorem isGalois : IsGalois K L := by
  haveI : Algebra.IsQuadraticExtension K L := ⟨h2⟩
  infer_instance

include h2 in
theorem card_aut : Fintype.card (L ≃ₐ[K] L) = 2 := by
  haveI := isGalois K L h2
  rw [Fintype.card_eq_nat_card, IsGalois.card_aut_eq_finrank, h2]

include h2 hgen in

theorem sigma_ne_one : σ ≠ 1 := by
  intro hσ

  have hall : ∀ τ : L ≃ₐ[K] L, τ = 1 := by
    intro τ
    have := hgen τ
    rw [hσ, Subgroup.zpowers_one_eq_bot, Subgroup.mem_bot] at this
    exact this
  have hcard : Fintype.card (L ≃ₐ[K] L) = 1 := by
    rw [Fintype.card_eq_one_iff]
    exact ⟨1, hall⟩
  rw [card_aut K L h2] at hcard
  exact absurd hcard (by norm_num)

include h2 in

theorem sigma_sq (x : L) : σ (σ x) = x := by
  have h : σ ^ 2 = 1 := by rw [← card_aut K L h2]; exact pow_card_eq_one
  have := congrArg (fun τ : L ≃ₐ[K] L => τ x) h
  simpa [pow_two] using this

include h2 hgen in

theorem exists_theta : ∃ θ : L, σ θ = -θ ∧ θ ≠ 0 := by
  have hσ := sigma_ne_one K L h2 σ hgen
  obtain ⟨x, hx⟩ : ∃ x : L, σ x ≠ x := by
    by_contra h
    push Not at h
    exact hσ (AlgEquiv.ext h)
  refine ⟨x - σ x, ?_, sub_ne_zero.2 (Ne.symm hx)⟩
  rw [map_sub, sigma_sq K L h2, neg_sub]

end Galois

section Twist

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] (σ : L ≃ₐ[K] L)

attribute [local instance] algRF algRE

abbrev sE : E K L →+* E K L := sigmaTensor K L (F K) σ

theorem sE_tmul (l : L) (a : F K) : sE K L σ (l ⊗ₜ a) = σ l ⊗ₜ a := by
  simp [sE, sigmaTensor]

theorem sE_algebraMap (a : F K) : sE K L σ (algebraMap (F K) (E K L) a) = algebraMap (F K) (E K L) a := by
  rw [algebraMap_FE_apply, sE_tmul, map_one]

theorem sE_algebraMap_real (r : ℝ) : sE K L σ (algebraMap ℝ (E K L) r) = algebraMap ℝ (E K L) r :=
  sE_algebraMap K L σ _

def sEa : E K L →ₐ[ℝ] E K L :=
  { sE K L σ with commutes' := sE_algebraMap_real K L σ }

theorem sEa_apply (z : E K L) : sEa K L σ z = sE K L σ z := rfl

theorem sE_sE (h2 : Module.finrank K L = 2) (z : E K L) : sE K L σ (sE K L σ z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul l a => rw [sE_tmul, sE_tmul, sigma_sq K L h2]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

def sEe (h2 : Module.finrank K L = 2) : E K L ≃ₐ[ℝ] E K L :=
  AlgEquiv.ofAlgHom (sEa K L σ) (sEa K L σ) (by ext z; exact sE_sE K L σ h2 z) (by ext z; exact sE_sE K L σ h2 z)

theorem sEe_apply (h2 : Module.finrank K L = 2) (z : E K L) : sEe K L σ h2 z = sE K L σ z := rfl

theorem trace_mul_eq_zero_of_anti_of_fixed (h2 : Module.finrank K L = 2) {u t : E K L}
    (hu : sE K L σ u = -u) (ht : sE K L σ t = t) : Algebra.trace ℝ (E K L) (u * t) = 0 := by
  have h := Algebra.trace_eq_of_algEquiv (sEe K L σ h2) (u * t)
  rw [sEe_apply, map_mul, hu, ht] at h
  have h' : (-u) * t = -(u * t) := by ring
  rw [h', map_neg] at h
  linarith

def sM : ME K L →ₗ[ℝ] ME K L := (sEa K L σ).toLinearMap.mapMatrix

theorem sM_apply (X : ME K L) : sM K L σ X = X.map (sE K L σ) := rfl

theorem sM_apply' (X : ME K L) : sM K L σ X = (sE K L σ).mapMatrix X := rfl

theorem sM_mul (X Y : ME K L) : sM K L σ (X * Y) = sM K L σ X * sM K L σ Y := by
  rw [sM_apply', sM_apply', sM_apply', RingHom.map_mul]

theorem sM_one : sM K L σ 1 = 1 := by rw [sM_apply', RingHom.map_one]

theorem sM_sM (h2 : Module.finrank K L = 2) (X : ME K L) : sM K L σ (sM K L σ X) = X := by
  ext i j
  simp only [sM_apply, Matrix.map_apply]
  exact sE_sE K L σ h2 _

theorem trace_sM (X : ME K L) : (sM K L σ X).trace = sE K L σ X.trace := by
  rw [sM_apply', RingHom.mapMatrix_apply, ← AddMonoidHom.map_trace]

theorem sM_iotaM (Y : MF K) : sM K L σ (iotaM K L Y) = iotaM K L Y := by
  ext i j
  simp only [sM_apply, iotaM_apply', RingHom.mapMatrix_apply, Matrix.map_apply]
  exact sE_algebraMap K L σ _

theorem coe_sigmaGL (t : GL (Fin 2) (E K L)) :
    ((sigmaGL K L (F K) σ t : GL (Fin 2) (E K L)) : ME K L) = sM K L σ (t : ME K L) := rfl

theorem sM_smul (z : E K L) (X : ME K L) : sM K L σ (z • X) = sE K L σ z • sM K L σ X := by
  ext i j
  simp only [sM_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]

variable (δ : GL (Fin 2) (E K L))

def Adelta : Subalgebra ℝ (ME K L) where
  carrier := {X | X * (δ : ME K L) = (δ : ME K L) * X.map (sigmaTensor K L (InfiniteAdeleRing K) σ)}
  mul_mem' {X Y} hX hY := by
    simp only [Set.mem_setOf_eq] at hX hY ⊢
    change X * Y * (δ : ME K L) = (δ : ME K L) * sM K L σ (X * Y)
    change X * (δ : ME K L) = (δ : ME K L) * sM K L σ X at hX
    change Y * (δ : ME K L) = (δ : ME K L) * sM K L σ Y at hY
    rw [sM_mul, mul_assoc, hY, ← mul_assoc, hX, mul_assoc]
  one_mem' := by
    simp only [Set.mem_setOf_eq]
    change 1 * (δ : ME K L) = (δ : ME K L) * sM K L σ 1
    rw [sM_one, one_mul, mul_one]
  add_mem' {X Y} hX hY := by
    simp only [Set.mem_setOf_eq] at hX hY ⊢
    change (X + Y) * (δ : ME K L) = (δ : ME K L) * sM K L σ (X + Y)
    change X * (δ : ME K L) = (δ : ME K L) * sM K L σ X at hX
    change Y * (δ : ME K L) = (δ : ME K L) * sM K L σ Y at hY
    rw [map_add, add_mul, mul_add, hX, hY]
  zero_mem' := by
    simp only [Set.mem_setOf_eq]
    change 0 * (δ : ME K L) = (δ : ME K L) * sM K L σ 0
    rw [map_zero, zero_mul, mul_zero]
  algebraMap_mem' r := by
    simp only [Set.mem_setOf_eq]
    change algebraMap ℝ (ME K L) r * (δ : ME K L) = (δ : ME K L) * sM K L σ (algebraMap ℝ (ME K L) r)
    have h1 : sM K L σ (algebraMap ℝ (ME K L) r) = algebraMap ℝ (ME K L) r := by
      rw [Algebra.algebraMap_eq_smul_one, map_smul, sM_one]
    rw [h1]
    exact Algebra.commutes r _

theorem mem_Adelta {X : ME K L} : X ∈ Adelta K L σ δ ↔ X * (δ : ME K L) = (δ : ME K L) * sM K L σ X := Iff.rfl

theorem coe_Adelta :
    ((Adelta K L σ δ : Subalgebra ℝ (ME K L)) : Set (ME K L)) =
      {X | X * (δ : ME K L) = (δ : ME K L) * X.map (sigmaTensor K L (InfiniteAdeleRing K) σ)} := rfl

theorem mem_twistedCentralizer_iff (g : GL (Fin 2) (E K L)) :
    g ∈ twistedCentralizer K L (F K) σ δ ↔ (g : ME K L) ∈ Adelta K L σ δ := by
  rw [mem_sigmaCentralizer_iff, mem_Adelta, mul_inv_eq_iff_eq_mul]
  constructor
  · intro h
    have := congrArg (fun x : GL (Fin 2) (E K L) => (x : ME K L)) h
    simpa [coe_sigmaGL] using this
  · intro h
    apply Units.ext
    simpa [coe_sigmaGL] using h

end Twist

section MatrixDet

variable (S : Type*) [CommRing S]

def colEquiv : Matrix (Fin 2) (Fin 2) S ≃ₗ[S] (Fin 2 → S) × (Fin 2 → S) where
  toFun X := (fun i => X i 0, fun i => X i 1)
  map_add' X Y := rfl
  map_smul' r X := rfl
  invFun p := Matrix.of fun i j => if j = 0 then p.1 i else p.2 i
  left_inv X := by
    ext i j
    fin_cases j <;> simp
  right_inv p := by
    ext i <;> simp

def rowEquiv : Matrix (Fin 2) (Fin 2) S ≃ₗ[S] (Fin 2 → S) × (Fin 2 → S) where
  toFun X := (X 0, X 1)
  map_add' X Y := rfl
  map_smul' r X := rfl
  invFun p := Matrix.of fun i j => if i = 0 then p.1 j else p.2 j
  left_inv X := by
    ext i j
    fin_cases i <;> simp
  right_inv p := by
    ext j <;> simp

theorem colEquiv_mul (Y X : Matrix (Fin 2) (Fin 2) S) :
    colEquiv S (Y * X) = LinearMap.prodMap (Matrix.toLin' Y) (Matrix.toLin' Y) (colEquiv S X) := by
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;> fin_cases i <;>
    simp [colEquiv, Matrix.mul_apply, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem rowEquiv_mul (X Y : Matrix (Fin 2) (Fin 2) S) :
    rowEquiv S (X * Y) = LinearMap.prodMap (Matrix.toLin' Yᵀ) (Matrix.toLin' Yᵀ) (rowEquiv S X) := by
  refine Prod.ext (funext fun j => ?_) (funext fun j => ?_) <;> fin_cases j <;>
    simp [rowEquiv, Matrix.mul_apply, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      Matrix.transpose_apply, mul_comm]

theorem det_mulLeft_matrix (Y : Matrix (Fin 2) (Fin 2) S) :
    LinearMap.det (LinearMap.mulLeft S Y) = Y.det ^ 2 := by
  have h : LinearMap.mulLeft S Y =
      ((colEquiv S).symm : ((Fin 2 → S) × (Fin 2 → S)) →ₗ[S] Matrix (Fin 2) (Fin 2) S) ∘ₗ
        (LinearMap.prodMap (Matrix.toLin' Y) (Matrix.toLin' Y)) ∘ₗ
        (((colEquiv S).symm.symm : Matrix (Fin 2) (Fin 2) S ≃ₗ[S] (Fin 2 → S) × (Fin 2 → S)) :
          Matrix (Fin 2) (Fin 2) S →ₗ[S] (Fin 2 → S) × (Fin 2 → S)) := by
    apply LinearMap.ext
    intro X
    simp only [LinearMap.mulLeft_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_symm]
    rw [← colEquiv_mul, LinearEquiv.symm_apply_apply]
  rw [h, LinearMap.det_conj, LinearMap.det_prodMap, LinearMap.det_toLin', pow_two]

theorem det_mulRight_matrix (Y : Matrix (Fin 2) (Fin 2) S) :
    LinearMap.det (LinearMap.mulRight S Y) = Y.det ^ 2 := by
  have h : LinearMap.mulRight S Y =
      ((rowEquiv S).symm : ((Fin 2 → S) × (Fin 2 → S)) →ₗ[S] Matrix (Fin 2) (Fin 2) S) ∘ₗ
        (LinearMap.prodMap (Matrix.toLin' Yᵀ) (Matrix.toLin' Yᵀ)) ∘ₗ
        (((rowEquiv S).symm.symm : Matrix (Fin 2) (Fin 2) S ≃ₗ[S] (Fin 2 → S) × (Fin 2 → S)) :
          Matrix (Fin 2) (Fin 2) S →ₗ[S] (Fin 2 → S) × (Fin 2 → S)) := by
    apply LinearMap.ext
    intro X
    simp only [LinearMap.mulRight_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_symm]
    rw [← rowEquiv_mul, LinearEquiv.symm_apply_apply]
  rw [h, LinearMap.det_conj, LinearMap.det_prodMap, LinearMap.det_toLin', Matrix.det_transpose, pow_two]

end MatrixDet

section Decomposition

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L) (δ : GL (Fin 2) (E K L))

attribute [local instance] algRF algRE

scoped instance instSMulCommClassME : SMulCommClass ℝ (ME K L) (ME K L) := ⟨fun r X Y => (Matrix.mul_smul X r Y).symm⟩
scoped instance instIsScalarTowerME : IsScalarTower ℝ (ME K L) (ME K L) := ⟨fun r X Y => Matrix.smul_mul r X Y⟩
scoped instance instSMulCommClassMF : SMulCommClass ℝ (MF K) (MF K) := ⟨fun r X Y => (Matrix.mul_smul X r Y).symm⟩
scoped instance instIsScalarTowerMF : IsScalarTower ℝ (MF K) (MF K) := ⟨fun r X Y => Matrix.smul_mul r X Y⟩
scoped instance instSMulCommClassEME : SMulCommClass (E K L) (ME K L) (ME K L) :=
  ⟨fun r X Y => (Matrix.mul_smul X r Y).symm⟩
scoped instance instIsScalarTowerEME : IsScalarTower (E K L) (ME K L) (ME K L) := ⟨fun r X Y => Matrix.smul_mul r X Y⟩
scoped instance instSMulCommClassERME : SMulCommClass (E K L) ℝ (ME K L) :=
  ⟨fun z r X => by ext i j; simp only [Matrix.smul_apply, smul_eq_mul, mul_smul_comm]⟩
scoped instance instSMulCommClassREME : SMulCommClass ℝ (E K L) (ME K L) :=
  ⟨fun r z X => by ext i j; simp only [Matrix.smul_apply, smul_eq_mul, mul_smul_comm]⟩

abbrev Dinv : ME K L := ((δ⁻¹ : GL (Fin 2) (E K L)) : ME K L)

theorem D_mul_Dinv : (δ : ME K L) * Dinv K L δ = 1 := Units.mul_inv δ
theorem Dinv_mul_D : Dinv K L δ * (δ : ME K L) = 1 := Units.inv_mul δ

def Θ : ME K L →ₗ[ℝ] ME K L where
  toFun X := (δ : ME K L) * sM K L σ X * Dinv K L δ
  map_add' X Y := by rw [map_add, mul_add, add_mul]
  map_smul' r X := by
    rw [map_smul, mul_smul_comm, smul_mul_assoc]
    rfl

theorem Θ_apply (X : ME K L) : Θ K L σ δ X = (δ : ME K L) * sM K L σ X * Dinv K L δ := rfl

theorem mem_Adelta_iff_Θ (X : ME K L) : X ∈ Adelta K L σ δ ↔ Θ K L σ δ X = X := by
  rw [mem_Adelta, Θ_apply]
  constructor
  · intro h
    rw [← h, mul_assoc, D_mul_Dinv, mul_one]
  · intro h
    calc X * (δ : ME K L) = (δ : ME K L) * sM K L σ X * Dinv K L δ * (δ : ME K L) := by rw [h]
      _ = (δ : ME K L) * sM K L σ X := by rw [mul_assoc, Dinv_mul_D, mul_one]

variable (cδ : (E K L)ˣ) (hδc : (δ : ME K L) * sM K L σ (δ : ME K L) = (cδ : E K L) • (1 : ME K L))

include hδc in

theorem sM_Dinv_mul_Dinv : sM K L σ (Dinv K L δ) * Dinv K L δ = ((cδ⁻¹ : (E K L)ˣ) : E K L) • (1 : ME K L) := by
  set w : GL (Fin 2) (E K L) := δ * sigmaGL K L (F K) σ δ with hw
  have hwval : (w : ME K L) = (cδ : E K L) • (1 : ME K L) := by
    rw [hw, Units.val_mul, coe_sigmaGL]; exact hδc
  have hwinv : ((w⁻¹ : GL (Fin 2) (E K L)) : ME K L) = sM K L σ (Dinv K L δ) * Dinv K L δ := by
    rw [hw, _root_.mul_inv_rev, Units.val_mul, ← map_inv, coe_sigmaGL]
  rw [← hwinv, Matrix.coe_units_inv, hwval]
  refine Matrix.inv_eq_left_inv ?_
  rw [smul_mul_assoc, one_mul, smul_smul, Units.inv_mul, one_smul]

include h2 hδc in

theorem Θ_Θ (X : ME K L) : Θ K L σ δ (Θ K L σ δ X) = X := by
  rw [Θ_apply, Θ_apply, sM_mul, sM_mul, sM_sM K L σ h2]
  calc (δ : ME K L) * (sM K L σ (δ : ME K L) * X * sM K L σ (Dinv K L δ)) * Dinv K L δ
      = ((δ : ME K L) * sM K L σ (δ : ME K L)) * X * (sM K L σ (Dinv K L δ) * Dinv K L δ) := by
        simp only [mul_assoc]
    _ = ((cδ : E K L) • (1 : ME K L)) * X * (((cδ⁻¹ : (E K L)ˣ) : E K L) • (1 : ME K L)) := by
        rw [hδc, sM_Dinv_mul_Dinv K L σ δ cδ hδc]
    _ = X := by
        rw [smul_mul_assoc, one_mul, mul_smul_comm, mul_one, smul_smul, Units.inv_mul, one_smul]

variable {u : E K L} (hu : sE K L σ u = -u) (huu : IsUnit u)

include hu in

theorem Θ_smul (X : ME K L) : Θ K L σ δ (u • X) = -(u • Θ K L σ δ X) := by
  rw [Θ_apply, Θ_apply, sM_smul, hu, neg_smul, Matrix.mul_neg, Matrix.neg_mul, mul_smul_comm, smul_mul_assoc]

include hu huu in
theorem sE_unit_inv : sE K L σ ((huu.unit⁻¹ : (E K L)ˣ) : E K L) = -((huu.unit⁻¹ : (E K L)ˣ) : E K L) := by
  set ui : E K L := ((huu.unit⁻¹ : (E K L)ˣ) : E K L) with hui
  have hinv : u * ui = 1 := huu.unit.mul_inv
  have h1 : sE K L σ ui * sE K L σ u = 1 := by
    rw [← map_mul, mul_comm, hinv, map_one]
  rw [hu] at h1
  linear_combination (-ui) * h1 - (sE K L σ ui) * hinv

include h2 hδc hu huu in

theorem exists_decomp (X : ME K L) :
    ∃ P ∈ Adelta K L σ δ, ∃ Q ∈ Adelta K L σ δ, X = P + u • Q := by
  set P : ME K L := (1 / 2 : ℝ) • (X + Θ K L σ δ X) with hP
  set R : ME K L := (1 / 2 : ℝ) • (X - Θ K L σ δ X) with hR
  set ui : E K L := ((huu.unit⁻¹ : (E K L)ˣ) : E K L) with hui
  have hΘP : Θ K L σ δ P = P := by
    rw [hP, map_smul, map_add, Θ_Θ K L h2 σ δ cδ hδc, add_comm]
  have hΘR : Θ K L σ δ R = -R := by
    rw [hR, map_smul, map_sub, Θ_Θ K L h2 σ δ cδ hδc, ← neg_sub X (Θ K L σ δ X),
      smul_neg (1 / 2 : ℝ) (X - Θ K L σ δ X)]
  have hσui : sE K L σ ui = -ui := sE_unit_inv K L σ hu huu
  refine ⟨P, (mem_Adelta_iff_Θ K L σ δ P).2 hΘP, ui • R, (mem_Adelta_iff_Θ K L σ δ _).2 ?_, ?_⟩
  · rw [Θ_smul K L σ δ hσui, hΘR, smul_neg, neg_neg]
  · rw [smul_smul, hui, show u * ((huu.unit⁻¹ : (E K L)ˣ) : E K L) = 1 from huu.unit.mul_inv, one_smul, hP, hR,
      ← smul_add (1 / 2 : ℝ) (X + Θ K L σ δ X) (X - Θ K L σ δ X)]
    have : X + Θ K L σ δ X + (X - Θ K L σ δ X) = (2 : ℝ) • X := by rw [two_smul ℝ X]; abel
    rw [this, smul_smul]
    norm_num

include h2 hδc hu huu in

theorem eq_zero_of_decomp {P Q : ME K L} (hP : P ∈ Adelta K L σ δ) (hQ : Q ∈ Adelta K L σ δ)
    (h : P + u • Q = 0) : P = 0 ∧ Q = 0 := by
  have hΘP := (mem_Adelta_iff_Θ K L σ δ P).1 hP
  have hΘQ := (mem_Adelta_iff_Θ K L σ δ Q).1 hQ
  have h' : P - u • Q = 0 := by
    have := congrArg (Θ K L σ δ) h
    rw [map_add, Θ_smul K L σ δ hu, hΘP, hΘQ, map_zero, ← sub_eq_add_neg] at this
    exact this
  have hP0 : P = 0 := by
    have h2P : (2 : ℝ) • P = 0 := by
      rw [two_smul ℝ P]
      have := congrArg₂ (· + ·) h h'
      simp only [add_zero] at this
      rw [← this]; abel
    have : P = (1 / 2 : ℝ) • ((2 : ℝ) • P) := by rw [smul_smul]; norm_num
    rw [this, h2P]
    exact smul_zero (A := ME K L) (1 / 2 : ℝ)
  refine ⟨hP0, ?_⟩
  rw [hP0, zero_add] at h
  have := congrArg (fun Y => ((huu.unit⁻¹ : (E K L)ˣ) : E K L) • Y) h
  simp only [smul_smul, smul_zero] at this
  rwa [show ((huu.unit⁻¹ : (E K L)ˣ) : E K L) * u = 1 from huu.unit.inv_mul, one_smul] at this

variable {n : ℕ} (e : Fin n → ME K L) (hli : LinearIndependent ℝ e)
  (hsp : Submodule.span ℝ (Set.range e) = Subalgebra.toSubmodule (Adelta K L σ δ))

def ee (u : E K L) : Fin n ⊕ Fin n → ME K L := Sum.elim e fun i => u • e i

include hsp in
theorem mem_of_mem_span {X : ME K L} (hX : X ∈ Submodule.span ℝ (Set.range e)) : X ∈ Adelta K L σ δ := by
  rw [hsp] at hX; exact hX

include hsp in
theorem mem_span_of_mem {X : ME K L} (hX : X ∈ Adelta K L σ δ) : X ∈ Submodule.span ℝ (Set.range e) := by
  rw [hsp]; exact hX

include h2 hδc hu huu hli hsp in
theorem linearIndependent_ee : LinearIndependent ℝ (ee K L e u) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg
  set P : ME K L := ∑ a, g (Sum.inl a) • e a with hP
  set Q : ME K L := ∑ b, g (Sum.inr b) • e b with hQ
  have hPmem : P ∈ Adelta K L σ δ :=
    mem_of_mem_span K L σ δ e hsp (Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩))
  have hQmem : Q ∈ Adelta K L σ δ :=
    mem_of_mem_span K L σ δ e hsp (Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩))
  have hsum : P + u • Q = 0 := by
    rw [← hg, Fintype.sum_sum_type]
    simp only [ee, Sum.elim_inl, Sum.elim_inr]
    rw [hQ, Finset.smul_sum]
    congr 1
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [smul_comm]
  obtain ⟨hP0, hQ0⟩ := eq_zero_of_decomp K L h2 σ δ cδ hδc hu huu hPmem hQmem hsum
  have hli' := (Fintype.linearIndependent_iff.1 hli)
  have h1 := hli' (fun a => g (Sum.inl a)) hP0
  have h2'' := hli' (fun b => g (Sum.inr b)) hQ0
  rintro (a | b)
  · exact h1 a
  · exact h2'' b

include h2 hδc hu huu hsp in
theorem span_ee : ⊤ ≤ Submodule.span ℝ (Set.range (ee K L e u)) := by
  rintro X -
  obtain ⟨P, hP, Q, hQ, rfl⟩ := exists_decomp K L h2 σ δ cδ hδc hu huu X
  have hsub : Set.range e ⊆ Set.range (ee K L e u) := by
    rintro _ ⟨i, rfl⟩; exact ⟨Sum.inl i, rfl⟩
  refine Submodule.add_mem _ (Submodule.span_mono hsub (mem_span_of_mem K L σ δ e hsp hP)) ?_
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 (mem_span_of_mem K L σ δ e hsp hQ)
  rw [← hc, Finset.smul_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [smul_comm]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inr i, rfl⟩)

def B : Module.Basis (Fin n ⊕ Fin n) ℝ (ME K L) :=
  Module.Basis.mk (linearIndependent_ee K L h2 σ δ cδ hδc hu huu e hli hsp) (span_ee K L h2 σ δ cδ hδc hu huu e hsp)

theorem B_apply (k : Fin n ⊕ Fin n) : B K L h2 σ δ cδ hδc hu huu e hli hsp k = ee K L e u k :=
  Module.Basis.mk_apply _ _ k

theorem B_inl (i : Fin n) : B K L h2 σ δ cδ hδc hu huu e hli hsp (Sum.inl i) = e i := by
  rw [B_apply]; rfl
theorem B_inr (i : Fin n) : B K L h2 σ δ cδ hδc hu huu e hli hsp (Sum.inr i) = u • e i := by
  rw [B_apply]; rfl

def bA : Module.Basis (Fin n) ℝ (Adelta K L σ δ) :=
  Module.Basis.mk (v := fun i => (⟨e i, mem_of_mem_span K L σ δ e hsp (Submodule.subset_span ⟨i, rfl⟩)⟩ : Adelta K L σ δ))
    (by
      refine LinearIndependent.of_comp (Adelta K L σ δ).val.toLinearMap ?_
      exact hli)
    (by
      rintro ⟨x, hx⟩ -
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 (mem_span_of_mem K L σ δ e hsp hx)
      have : (⟨x, hx⟩ : Adelta K L σ δ) =
          ∑ i, c i • (⟨e i, mem_of_mem_span K L σ δ e hsp (Submodule.subset_span ⟨i, rfl⟩)⟩ : Adelta K L σ δ) := by
        apply Subtype.ext
        rw [AddSubmonoidClass.coe_finset_sum]
        simp only [Subalgebra.coe_smul]
        exact hc.symm
      rw [this]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))

theorem coe_bA (i : Fin n) : ((bA K L σ δ e hli hsp i : Adelta K L σ δ) : ME K L) = e i := by
  rw [bA, Module.Basis.mk_apply]

theorem repr_sum_smul {ι M : Type*} [Fintype ι] [AddCommGroup M] [Module ℝ M] (b : Module.Basis ι ℝ M)
    (c : ι → ℝ) (i : ι) : b.repr (∑ j, c j • b j) i = c i := by
  have h : b.equivFun (b.equivFun.symm c) = c := LinearEquiv.apply_symm_apply _ _
  rw [Module.Basis.equivFun_symm_apply] at h
  have := congrFun h i
  rwa [Module.Basis.equivFun_apply] at this

theorem mul_e_eq_sum (a : Adelta K L σ δ) (j : Fin n) :
    (a : ME K L) * e j =
      ∑ i, LinearMap.toMatrix (bA K L σ δ e hli hsp) (bA K L σ δ e hli hsp) (Algebra.lmul ℝ (Adelta K L σ δ) a) i j • e i := by
  have h := Matrix.toLin_self (v₁ := bA K L σ δ e hli hsp) (v₂ := bA K L σ δ e hli hsp)
    (LinearMap.toMatrix (bA K L σ δ e hli hsp) (bA K L σ δ e hli hsp) (Algebra.lmul ℝ (Adelta K L σ δ) a)) j
  rw [Matrix.toLin_toMatrix] at h
  have h' := congrArg (fun x : Adelta K L σ δ => (x : ME K L)) h
  rw [AddSubmonoidClass.coe_finset_sum] at h'
  simp only [Subalgebra.coe_smul, coe_bA] at h'
  rw [← h']
  show (a : ME K L) * e j = ((a * bA K L σ δ e hli hsp j : Adelta K L σ δ) : ME K L)
  rw [Subalgebra.coe_mul, coe_bA]

theorem e_mul_eq_sum (a : Adelta K L σ δ) (j : Fin n) :
    e j * (a : ME K L) =
      ∑ i, LinearMap.toMatrix (bA K L σ δ e hli hsp) (bA K L σ δ e hli hsp) (LinearMap.mulRight ℝ a) i j • e i := by
  have h := Matrix.toLin_self (v₁ := bA K L σ δ e hli hsp) (v₂ := bA K L σ δ e hli hsp)
    (LinearMap.toMatrix (bA K L σ δ e hli hsp) (bA K L σ δ e hli hsp) (LinearMap.mulRight ℝ a)) j
  rw [Matrix.toLin_toMatrix] at h
  have h' := congrArg (fun x : Adelta K L σ δ => (x : ME K L)) h
  rw [AddSubmonoidClass.coe_finset_sum] at h'
  simp only [Subalgebra.coe_smul, coe_bA] at h'
  rw [← h']
  show e j * (a : ME K L) = ((bA K L σ δ e hli hsp j * a : Adelta K L σ δ) : ME K L)
  rw [Subalgebra.coe_mul, coe_bA]

include h2 hδc hu huu in

theorem toMatrix_mulLeft (a : Adelta K L σ δ) :
    LinearMap.toMatrix (B K L h2 σ δ cδ hδc hu huu e hli hsp) (B K L h2 σ δ cδ hδc hu huu e hli hsp)
        (LinearMap.mulLeft ℝ (a : ME K L)) =
      Matrix.fromBlocks
        (LinearMap.toMatrix (bA K L σ δ e hli hsp) (bA K L σ δ e hli hsp) (Algebra.lmul ℝ (Adelta K L σ δ) a)) 0 0
        (LinearMap.toMatrix (bA K L σ δ e hli hsp) (bA K L σ δ e hli hsp) (Algebra.lmul ℝ (Adelta K L σ δ) a)) := by
  set Bb := B K L h2 σ δ cδ hδc hu huu e hli hsp with hBb
  set P := LinearMap.toMatrix (bA K L σ δ e hli hsp) (bA K L σ δ e hli hsp) (Algebra.lmul ℝ (Adelta K L σ δ) a) with hP

  have hcol : ∀ j : Fin n, (a : ME K L) * e j = ∑ k, (Sum.elim (fun i => P i j) (fun _ => (0 : ℝ)) k) • Bb k := by
    intro j
    rw [Fintype.sum_sum_type]
    have h0 : ∑ x : Fin n, (Sum.elim (fun i => P i j) (fun _ => (0 : ℝ)) (Sum.inr x)) • Bb (Sum.inr x) = 0 :=
      Finset.sum_eq_zero fun x _ => by rw [Sum.elim_inr]; exact zero_smul ℝ (Bb (Sum.inr x))
    rw [h0, add_zero]
    simp only [Sum.elim_inl, hBb, B_inl]
    exact mul_e_eq_sum K L σ δ e hli hsp a j
  have hcol' : ∀ j : Fin n, (a : ME K L) * (u • e j) = ∑ k, (Sum.elim (fun _ => (0 : ℝ)) (fun i => P i j) k) • Bb k := by
    intro j
    rw [Fintype.sum_sum_type]
    have h0 : ∑ x : Fin n, (Sum.elim (fun _ => (0 : ℝ)) (fun i => P i j) (Sum.inl x)) • Bb (Sum.inl x) = 0 :=
      Finset.sum_eq_zero fun x _ => by rw [Sum.elim_inl]; exact zero_smul ℝ (Bb (Sum.inl x))
    rw [h0, zero_add]
    simp only [Sum.elim_inr, hBb, B_inr]
    rw [mul_smul_comm, mul_e_eq_sum K L σ δ e hli hsp a j, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact smul_comm u _ (e i)
  ext k l
  rw [LinearMap.toMatrix_apply, LinearMap.mulLeft_apply]
  rcases l with j | j <;> rcases k with i | i
  · rw [hBb, B_inl, ← hBb, hcol j, repr_sum_smul, Matrix.fromBlocks_apply₁₁]; rfl
  · rw [hBb, B_inl, ← hBb, hcol j, repr_sum_smul, Matrix.fromBlocks_apply₂₁]; rfl
  · rw [hBb, B_inr, ← hBb, hcol' j, repr_sum_smul, Matrix.fromBlocks_apply₁₂]; rfl
  · rw [hBb, B_inr, ← hBb, hcol' j, repr_sum_smul, Matrix.fromBlocks_apply₂₂]; rfl

include h2 hδc hu huu in

theorem toMatrix_mulRight (a : Adelta K L σ δ) :
    LinearMap.toMatrix (B K L h2 σ δ cδ hδc hu huu e hli hsp) (B K L h2 σ δ cδ hδc hu huu e hli hsp)
        (LinearMap.mulRight ℝ (a : ME K L)) =
      Matrix.fromBlocks
        (LinearMap.toMatrix (bA K L σ δ e hli hsp) (bA K L σ δ e hli hsp) (LinearMap.mulRight ℝ a)) 0 0
        (LinearMap.toMatrix (bA K L σ δ e hli hsp) (bA K L σ δ e hli hsp) (LinearMap.mulRight ℝ a)) := by
  set Bb := B K L h2 σ δ cδ hδc hu huu e hli hsp with hBb
  set Q := LinearMap.toMatrix (bA K L σ δ e hli hsp) (bA K L σ δ e hli hsp) (LinearMap.mulRight ℝ a) with hQ
  have hcol : ∀ j : Fin n, e j * (a : ME K L) = ∑ k, (Sum.elim (fun i => Q i j) (fun _ => (0 : ℝ)) k) • Bb k := by
    intro j
    rw [Fintype.sum_sum_type]
    have h0 : ∑ x : Fin n, (Sum.elim (fun i => Q i j) (fun _ => (0 : ℝ)) (Sum.inr x)) • Bb (Sum.inr x) = 0 :=
      Finset.sum_eq_zero fun x _ => by rw [Sum.elim_inr]; exact zero_smul ℝ (Bb (Sum.inr x))
    rw [h0, add_zero]
    simp only [Sum.elim_inl, hBb, B_inl]
    exact e_mul_eq_sum K L σ δ e hli hsp a j
  have hcol' : ∀ j : Fin n, (u • e j) * (a : ME K L) = ∑ k, (Sum.elim (fun _ => (0 : ℝ)) (fun i => Q i j) k) • Bb k := by
    intro j
    rw [Fintype.sum_sum_type]
    have h0 : ∑ x : Fin n, (Sum.elim (fun _ => (0 : ℝ)) (fun i => Q i j) (Sum.inl x)) • Bb (Sum.inl x) = 0 :=
      Finset.sum_eq_zero fun x _ => by rw [Sum.elim_inl]; exact zero_smul ℝ (Bb (Sum.inl x))
    rw [h0, zero_add]
    simp only [Sum.elim_inr, hBb, B_inr]
    rw [smul_mul_assoc, e_mul_eq_sum K L σ δ e hli hsp a j, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact smul_comm u _ (e i)
  ext k l
  rw [LinearMap.toMatrix_apply, LinearMap.mulRight_apply]
  rcases l with j | j <;> rcases k with i | i
  · rw [hBb, B_inl, ← hBb, hcol j, repr_sum_smul, Matrix.fromBlocks_apply₁₁]; rfl
  · rw [hBb, B_inl, ← hBb, hcol j, repr_sum_smul, Matrix.fromBlocks_apply₂₁]; rfl
  · rw [hBb, B_inr, ← hBb, hcol' j, repr_sum_smul, Matrix.fromBlocks_apply₁₂]; rfl
  · rw [hBb, B_inr, ← hBb, hcol' j, repr_sum_smul, Matrix.fromBlocks_apply₂₂]; rfl

theorem det_mulLeft_real (Y : ME K L) :
    LinearMap.det (LinearMap.mulLeft ℝ Y) = (Algebra.norm ℝ Y.det) ^ 2 := by
  have h : LinearMap.mulLeft ℝ Y = (LinearMap.mulLeft (E K L) Y).restrictScalars ℝ := LinearMap.ext fun _ => rfl
  rw [h, LinearMap.det_restrictScalars, det_mulLeft_matrix, map_pow]

theorem det_mulRight_real (Y : ME K L) :
    LinearMap.det (LinearMap.mulRight ℝ Y) = (Algebra.norm ℝ Y.det) ^ 2 := by
  have h : LinearMap.mulRight ℝ Y = (LinearMap.mulRight (E K L) Y).restrictScalars ℝ := LinearMap.ext fun _ => rfl
  rw [h, LinearMap.det_restrictScalars, det_mulRight_matrix, map_pow]

include h2 hδc hu huu hli hsp in

theorem abs_det_left_Adelta (a : Adelta K L σ δ) :
    |(LinearMap.toMatrix (bA K L σ δ e hli hsp) (bA K L σ δ e hli hsp) (Algebra.lmul ℝ (Adelta K L σ δ) a)).det| =
      |Algebra.norm ℝ (a : ME K L).det| := by
  classical
  have hdet : LinearMap.det (LinearMap.mulLeft ℝ (a : ME K L)) =
      (LinearMap.toMatrix (bA K L σ δ e hli hsp) (bA K L σ δ e hli hsp) (Algebra.lmul ℝ (Adelta K L σ δ) a)).det ^ 2 := by
    rw [← LinearMap.det_toMatrix (B K L h2 σ δ cδ hδc hu huu e hli hsp), toMatrix_mulLeft K L h2 σ δ cδ hδc hu huu e hli hsp a,
      Matrix.det_fromBlocks_zero₂₁, pow_two]
  rw [det_mulLeft_real] at hdet
  exact ((sq_eq_sq_iff_abs_eq_abs _ _).1 hdet).symm

include h2 hδc hu huu hli hsp in

theorem abs_det_right_Adelta (a : Adelta K L σ δ) :
    |(LinearMap.toMatrix (bA K L σ δ e hli hsp) (bA K L σ δ e hli hsp) (LinearMap.mulRight ℝ a)).det| =
      |Algebra.norm ℝ (a : ME K L).det| := by
  classical
  have hdet : LinearMap.det (LinearMap.mulRight ℝ (a : ME K L)) =
      (LinearMap.toMatrix (bA K L σ δ e hli hsp) (bA K L σ δ e hli hsp) (LinearMap.mulRight ℝ a)).det ^ 2 := by
    rw [← LinearMap.det_toMatrix (B K L h2 σ δ cδ hδc hu huu e hli hsp), toMatrix_mulRight K L h2 σ δ cδ hδc hu huu e hli hsp a,
      Matrix.det_fromBlocks_zero₂₁, pow_two]
  rw [det_mulRight_real] at hdet
  exact ((sq_eq_sq_iff_abs_eq_abs _ _).1 hdet).symm

def bF : Module.Basis (Fin (Module.finrank ℝ (MF K))) ℝ (MF K) := Module.finBasis ℝ (MF K)

theorem det_toMatrix_mulLeft_MF (Y : MF K) :
    (LinearMap.toMatrix (bF K) (bF K) (LinearMap.mulLeft ℝ Y)).det = (Algebra.norm ℝ Y.det) ^ 2 := by
  have h : LinearMap.mulLeft ℝ Y = (LinearMap.mulLeft (F K) Y).restrictScalars ℝ := LinearMap.ext fun _ => rfl
  rw [LinearMap.det_toMatrix, h, LinearMap.det_restrictScalars, det_mulLeft_matrix, map_pow]

theorem det_toMatrix_mulRight_MF (Y : MF K) :
    (LinearMap.toMatrix (bF K) (bF K) (LinearMap.mulRight ℝ Y)).det = (Algebra.norm ℝ Y.det) ^ 2 := by
  have h : LinearMap.mulRight ℝ Y = (LinearMap.mulRight (F K) Y).restrictScalars ℝ := LinearMap.ext fun _ => rfl
  rw [LinearMap.det_toMatrix, h, LinearMap.det_restrictScalars, det_mulRight_matrix, map_pow]

theorem mul_bF_eq_sum (Y : MF K) (j : Fin (Module.finrank ℝ (MF K))) :
    Y * bF K j = ∑ i, LinearMap.toMatrix (bF K) (bF K) (LinearMap.mulLeft ℝ Y) i j • bF K i := by
  have h := Matrix.toLin_self (v₁ := bF K) (v₂ := bF K) (LinearMap.toMatrix (bF K) (bF K) (LinearMap.mulLeft ℝ Y)) j
  rw [Matrix.toLin_toMatrix, LinearMap.mulLeft_apply] at h
  exact h

theorem bF_mul_eq_sum (Y : MF K) (j : Fin (Module.finrank ℝ (MF K))) :
    bF K j * Y = ∑ i, LinearMap.toMatrix (bF K) (bF K) (LinearMap.mulRight ℝ Y) i j • bF K i := by
  have h := Matrix.toLin_self (v₁ := bF K) (v₂ := bF K) (LinearMap.toMatrix (bF K) (bF K) (LinearMap.mulRight ℝ Y)) j
  rw [Matrix.toLin_toMatrix, LinearMap.mulRight_apply] at h
  exact h

end Decomposition

section Gram

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

attribute [local instance] algRF algRE

def β : LinearMap.BilinForm ℝ (ME K L) :=
  LinearMap.mk₂ ℝ (fun X Y => Algebra.trace ℝ (E K L) (X * Y).trace)
    (fun X₁ X₂ Y => by simp only [add_mul, Matrix.trace_add, map_add])
    (fun r X Y => by rw [smul_mul_assoc, Matrix.trace_smul r (X * Y), map_smul, smul_eq_mul])
    (fun X Y₁ Y₂ => by simp only [mul_add, Matrix.trace_add, map_add])
    (fun r X Y => by rw [mul_smul_comm, Matrix.trace_smul r (X * Y), map_smul, smul_eq_mul])

theorem β_apply (X Y : ME K L) : β K L X Y = Algebra.trace ℝ (E K L) (X * Y).trace := rfl

theorem isRefl_β : (β K L).IsRefl := fun X Y h => by
  rw [β_apply] at h ⊢
  rwa [Matrix.trace_mul_comm]

theorem eq_zero_of_forall_β_eq_zero (hE : (Algebra.traceForm ℝ (E K L)).Nondegenerate) {X : ME K L}
    (h : ∀ Y, β K L X Y = 0) : X = 0 := by
  ext i j
  rw [Matrix.zero_apply]
  refine hE.1 (X i j) fun z => ?_
  rw [Algebra.traceForm_apply]
  have := h (Matrix.single j i z)
  rwa [β_apply, Matrix.trace_mul_single, op_smul_eq_mul] at this

variable (σ : L ≃ₐ[K] L) (h2 : Module.finrank K L = 2)

theorem sE_trace_of_mem (δ : GL (Fin 2) (E K L)) {X : ME K L} (hX : X ∈ Adelta K L σ δ) :
    sE K L σ X.trace = X.trace := by
  have h := (mem_Adelta_iff_Θ K L σ δ X).1 hX
  conv_rhs => rw [← h]
  rw [Θ_apply, Matrix.trace_mul_cycle, Dinv_mul_D, one_mul, trace_sM]

include h2 in

theorem eq_zero_of_mem_Adelta (hE : (Algebra.traceForm ℝ (E K L)).Nondegenerate) (δ : GL (Fin 2) (E K L))
    (cδ : (E K L)ˣ) (hδc : (δ : ME K L) * sM K L σ (δ : ME K L) = (cδ : E K L) • (1 : ME K L))
    {u : E K L} (hu : sE K L σ u = -u) (huu : IsUnit u)
    {m : ME K L} (hm : m ∈ Adelta K L σ δ) (h : ∀ Y ∈ Adelta K L σ δ, β K L m Y = 0) : m = 0 := by
  refine eq_zero_of_forall_β_eq_zero K L hE fun Y => ?_
  obtain ⟨P, hP, Q, hQ, rfl⟩ := exists_decomp K L h2 σ δ cδ hδc hu huu Y
  rw [map_add, h P hP, zero_add, β_apply, Matrix.mul_smul m u Q, Matrix.trace_smul u (m * Q), smul_eq_mul]
  exact trace_mul_eq_zero_of_anti_of_fixed K L σ h2 hu (sE_trace_of_mem K L σ δ ((Adelta K L σ δ).mul_mem hm hQ))

include h2 in

theorem exists_eq_add_theta_mul {θ : L} (hθ : σ θ = -θ) (hθ0 : θ ≠ 0) (z : E K L) :
    ∃ a b : F K, z = algebraMap (F K) (E K L) a + (θ ⊗ₜ (1 : F K)) * algebraMap (F K) (E K L) b := by

  have hliθ : LinearIndependent K ![(1 : L), θ] := by
    refine LinearIndependent.pair_iff.2 fun s t hst => ?_
    rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hst
    have hσ := congrArg σ hst
    rw [map_add, map_mul, AlgEquiv.commutes, AlgEquiv.commutes, hθ, map_zero] at hσ
    have ht : algebraMap K L t * θ = 0 := by
      have h3 : (2 : L) * (algebraMap K L t * θ) = 0 := by linear_combination hst - hσ
      exact (mul_eq_zero.1 h3).resolve_left two_ne_zero
    have ht0 : t = 0 := by
      rcases mul_eq_zero.1 ht with h | h
      · exact (map_eq_zero_iff (algebraMap K L) (algebraMap K L).injective).1 h
      · exact absurd h hθ0
    rw [ht0, map_zero, zero_mul, add_zero] at hst
    exact ⟨(map_eq_zero_iff (algebraMap K L) (algebraMap K L).injective).1 hst, ht0⟩
  set bθ := basisOfLinearIndependentOfCardEqFinrank hliθ (by rw [Fintype.card_fin, h2]) with hbθ
  have hdec : ∀ l : L, l = bθ.repr l 0 • (1 : L) + bθ.repr l 1 • θ := by
    intro l
    conv_lhs => rw [← bθ.sum_repr l]
    rw [Fin.sum_univ_two, hbθ, coe_basisOfLinearIndependentOfCardEqFinrank]
    rfl
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, by simp⟩
  | tmul l x =>
      refine ⟨bθ.repr l 0 • x, bθ.repr l 1 • x, ?_⟩
      rw [algebraMap_FE_apply, algebraMap_FE_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul,
        ← TensorProduct.smul_tmul, ← TensorProduct.smul_tmul, ← TensorProduct.add_tmul, ← hdec l]
  | add x y hx hy =>
      obtain ⟨a₁, b₁, rfl⟩ := hx
      obtain ⟨a₂, b₂, rfl⟩ := hy
      exact ⟨a₁ + a₂, b₁ + b₂, by rw [map_add, map_add, mul_add]; abel⟩

theorem trace_iotaM (Y : MF K) : (iotaM K L Y).trace = algebraMap (F K) (E K L) Y.trace := by
  rw [iotaM_apply', RingHom.mapMatrix_apply, ← AddMonoidHom.map_trace]

include h2 in

theorem eq_zero_of_range_iotaM (hE : (Algebra.traceForm ℝ (E K L)).Nondegenerate) {θ : L} (hθ : σ θ = -θ)
    (hθ0 : θ ≠ 0) {m₀ : MF K} (h : ∀ Y₀ : MF K, β K L (iotaM K L m₀) (iotaM K L Y₀) = 0) : iotaM K L m₀ = 0 := by
  refine eq_zero_of_forall_β_eq_zero K L hE fun Y => ?_
  choose fa fb hf using fun z : E K L => exists_eq_add_theta_mul K L σ h2 hθ hθ0 z
  set u : E K L := θ ⊗ₜ (1 : F K) with huθ
  have hu : sE K L σ u = -u := by rw [huθ, sE_tmul, hθ, TensorProduct.neg_tmul]
  have hY : Y = iotaM K L (Matrix.of fun i j => fa (Y i j)) + u • iotaM K L (Matrix.of fun i j => fb (Y i j)) := by
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, iotaM_apply', RingHom.mapMatrix_apply, Matrix.map_apply,
      Matrix.of_apply, smul_eq_mul]
    exact hf (Y i j)
  rw [hY, map_add, h, zero_add, β_apply, Matrix.mul_smul _ u _, Matrix.trace_smul u, smul_eq_mul, ← iotaM_mul,
    trace_iotaM]
  exact trace_mul_eq_zero_of_anti_of_fixed K L σ h2 hu (sE_algebraMap K L σ _)

theorem det_gram_ne_zero {n : ℕ} {e : Fin n → ME K L} (hli : LinearIndependent ℝ e)
    (hsep : ∀ m ∈ Submodule.span ℝ (Set.range e), (∀ n' ∈ Submodule.span ℝ (Set.range e), β K L m n' = 0) → m = 0) :
    (Matrix.of fun i j : Fin n => Algebra.trace ℝ (E K L) (Matrix.trace (e i * e j))).det ≠ 0 := by
  classical
  set W := Submodule.span ℝ (Set.range e) with hW
  set b : Module.Basis (Fin n) ℝ W := Module.Basis.span hli with hb
  have hrefl : ((β K L).restrict W).IsRefl := (isRefl_β K L).domRestrict W
  have hnd : ((β K L).restrict W).Nondegenerate := by
    show LinearMap.Nondegenerate _
    rw [hrefl.nondegenerate_iff_separatingLeft]
    rintro ⟨m, hm⟩ hm0
    have : m = 0 := hsep m hm fun n' hn' => by
      have := hm0 ⟨n', hn'⟩
      rwa [LinearMap.BilinForm.restrict_apply] at this
    exact Subtype.ext this
  have hdet := (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).1 hnd
  convert hdet using 2
  ext i j
  rw [LinearMap.BilinForm.toMatrix_apply, LinearMap.BilinForm.restrict_apply, Matrix.of_apply, hb,
    Module.Basis.span_apply, Module.Basis.span_apply]
  exact (β_apply K L (e i) (e j)).symm

end Gram

section Assembly

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

attribute [local instance] algRF algRE

theorem continuous_algebraNorm {M : Type*} [Ring M] [Algebra ℝ M] [FiniteDimensional ℝ M] [TopologicalSpace M]
    [IsTopologicalRing M] [ContinuousSMul ℝ M] [T2Space M] : Continuous (Algebra.norm ℝ : M → ℝ) := by
  classical
  set b := Module.finBasis ℝ M
  have h : (Algebra.norm ℝ : M → ℝ) = fun x => (Algebra.leftMulMatrix b x).det := by
    funext x; exact Algebra.norm_eq_matrix_det b x
  rw [h]
  have hc : Continuous fun x : M => Algebra.leftMulMatrix b x :=
    (Algebra.leftMulMatrix b).toLinearMap.continuous_of_finiteDimensional
  exact hc.matrix_det

abbrev sc {R : Type*} [CommRing R] (c : Rˣ) : GL (Fin 2) R := Matrix.GeneralLinearGroup.scalar (Fin 2) c

theorem scalar_mul_comm {R : Type*} [CommRing R] (c : Rˣ) (g : GL (Fin 2) R) : sc c * g = g * sc c := by
  refine Units.ext ?_
  show Matrix.scalar (Fin 2) (c : R) * (g : Matrix (Fin 2) (Fin 2) R) =
    (g : Matrix (Fin 2) (Fin 2) R) * Matrix.scalar (Fin 2) (c : R)
  exact (Matrix.scalar_commute (c : R) (fun r => Commute.all _ r) _).eq

theorem mem_centralizer_scalar {R : Type*} [CommRing R] (c : Rˣ) (g : GL (Fin 2) R) :
    g ∈ Subgroup.centralizer ({sc c} : Set (GL (Fin 2) R)) := by
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨rfl⟩
  exact scalar_mul_comm c g

theorem coe_sc {R : Type*} [CommRing R] (c : Rˣ) : ((sc c : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) = (c : R) • 1 := by
  show Matrix.scalar (Fin 2) (c : R) = _
  rw [Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]

theorem map_sc {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (c : Rˣ) :
    Matrix.GeneralLinearGroup.map f (sc c) = sc (Units.map (f : R →* S) c) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  show f ((Matrix.GeneralLinearGroup.scalar (Fin 2) c : Matrix (Fin 2) (Fin 2) R) i j) =
    (Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (f : R →* S) c) : Matrix (Fin 2) (Fin 2) S) i j
  rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.diagonal_apply]
  split_ifs <;> simp

variable (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L)

include h2 in

theorem exists_hδc (c : (F K)ˣ) (δ y : GL (Fin 2) (E K L)) (hδ : IsNormConjugator K L (F K) σ (sc c) δ y) :
    ∃ cδ : (E K L)ˣ, (δ : ME K L) * sM K L σ (δ : ME K L) = (cδ : E K L) • (1 : ME K L) := by
  set c' : (E K L)ˣ := Units.map ((Algebra.TensorProduct.includeRight : F K →ₐ[K] E K L).toRingHom : F K →* E K L) c
  have hT : toTensorGL K L (F K) (sc c) = sc c' := map_sc _ c
  have hN : normString K L (F K) σ δ = sc c' := by
    have h := hδ
    rw [IsNormConjugator, hT] at h

    calc normString K L (F K) σ δ = y * (y⁻¹ * normString K L (F K) σ δ * y) * y⁻¹ := by group
      _ = sc c' := by rw [← h, ← scalar_mul_comm, mul_assoc, mul_inv_cancel, mul_one]
  have hN2 : normString K L (F K) σ δ = δ * sigmaGL K L (F K) σ δ := by
    unfold normString
    rw [h2]
    simp [List.range_succ]
  refine ⟨c', ?_⟩
  rw [← coe_sigmaGL, ← Units.val_mul, ← hN2, hN, coe_sc]

def χF : MF K →* ℝ := (powMonoidHom 2).comp ((Algebra.norm ℝ (S := F K)).comp Matrix.detMonoidHom)

theorem χF_apply (Y : MF K) : χF K Y = (Algebra.norm ℝ Y.det) ^ 2 := rfl

theorem continuous_χF : Continuous (χF K) := by
  show Continuous fun Y : MF K => (Algebra.norm ℝ Y.det) ^ 2
  exact ((continuous_algebraNorm (M := F K)).comp
    (continuous_id.matrix_det : Continuous fun Y : MF K => Y.det)).pow 2

def χE : ME K L →* ℝ := (Algebra.norm ℝ (S := E K L)).comp Matrix.detMonoidHom

theorem χE_apply (X : ME K L) : χE K L X = Algebra.norm ℝ X.det := rfl

theorem continuous_χE : Continuous (χE K L) := by
  show Continuous fun X : ME K L => Algebra.norm ℝ X.det
  exact (continuous_algebraNorm (M := E K L)).comp (continuous_id.matrix_det : Continuous fun X : ME K L => X.det)

theorem measurable_ψ {V : Type*} [AddCommMonoid V] [Module ℝ V] [TopologicalSpace V] [ContinuousAdd V]
    [ContinuousSMul ℝ V] [MeasurableSpace V] [BorelSpace V] {n : ℕ} (e : Fin n → V) :
    Measurable fun c : Fin n → ℝ => ∑ i, c i • e i :=
  Continuous.measurable (continuous_finset_sum _ fun i _ => (continuous_apply i).smul continuous_const)

include h2 in

theorem arch_untwisted (hE : (Algebra.traceForm ℝ (E K L)).Nondegenerate) {θ : L} (hθ : σ θ = -θ) (hθ0 : θ ≠ 0)
    (c : (F K)ˣ) :
    letI : MeasurableSpace (Subgroup.centralizer ({sc c} : Set (GL (Fin 2) (F K)))) := borel _
    ∃ τ : Measure (Subgroup.centralizer ({sc c} : Set (GL (Fin 2) (F K)))),
      τ.IsHaarMeasure ∧ τ.IsMulRightInvariant ∧
      ∃ (n₁ : ℕ) (e₁ : Fin n₁ → ME K L), LinearIndependent ℝ e₁ ∧
        (Submodule.span ℝ (Set.range e₁) : Set (ME K L)) =
          Set.range (fun Y : MF K => Y.map (Algebra.TensorProduct.includeRight : F K →ₐ[K] E K L)) ∧
        Measure.map (fun t : Subgroup.centralizer ({sc c} : Set (GL (Fin 2) (F K))) =>
            ((t : GL (Fin 2) (F K)) : MF K).map (Algebra.TensorProduct.includeRight : F K →ₐ[K] E K L)) τ =
          (1 : ℝ≥0∞) • ((ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n₁ =>
              Algebra.trace ℝ (E K L) (Matrix.trace (e₁ i * e₁ j))).det|)) •
              Measure.map (fun c : Fin n₁ → ℝ => ∑ i, c i • e₁ i) volume).withDensity
            (fun X : ME K L => (ENNReal.ofReal |Algebra.norm ℝ (Matrix.det X)|)⁻¹) := by
  set Γ : Subgroup (GL (Fin 2) (F K)) := Subgroup.centralizer ({sc c} : Set (GL (Fin 2) (F K))) with hΓdef
  letI : MeasurableSpace Γ := borel _
  haveI : BorelSpace Γ := ⟨rfl⟩
  have hΓ : ∀ g : (MF K)ˣ, g ∈ Γ ↔ (g : MF K) ∈ (⊤ : Subalgebra ℝ (MF K)) :=
    fun g => ⟨fun _ => Algebra.mem_top, fun _ => mem_centralizer_scalar c g⟩
  have hsp : Submodule.span ℝ (Set.range (bF K)) = Subalgebra.toSubmodule (⊤ : Subalgebra ℝ (MF K)) := by
    rw [(bF K).span_eq, Algebra.top_toSubmodule]

  obtain ⟨τ₀, hH, hR, hmap⟩ :=
    MeasureTheory.Measure.exists_isHaarMeasure_subgroup_units_map_val_eq_withDensity_of_abs_det_eq
      (⊤ : Subalgebra ℝ (MF K)) Γ hΓ _ (bF K) (bF K).linearIndependent hsp (χF K) (continuous_χF K)
      (fun g hg => ⟨LinearMap.toMatrix (bF K) (bF K) (LinearMap.mulLeft ℝ (g : MF K)), mul_bF_eq_sum K (g : MF K), by
        rw [det_toMatrix_mulLeft_MF, χF_apply]⟩)
      (fun g hg => ⟨LinearMap.toMatrix (bF K) (bF K) (LinearMap.mulRight ℝ (g : MF K)), bF_mul_eq_sum K (g : MF K), by
        rw [det_toMatrix_mulRight_MF, χF_apply]⟩)

  set e₁ : Fin (Module.finrank ℝ (MF K)) → ME K L := ⇑(iotaM K L) ∘ ⇑(bF K) with he₁
  have hli₁ : LinearIndependent ℝ e₁ :=
    (bF K).linearIndependent.map' (iotaM K L) (LinearMap.ker_eq_bot.2 (injective_iotaM K L h2))
  have hrange : (Submodule.span ℝ (Set.range e₁) : Set (ME K L)) = Set.range (iotaM K L) := by
    rw [he₁, Set.range_comp, Submodule.span_image, (bF K).span_eq, Submodule.map_top, LinearMap.coe_range]

  set G : ℝ := (Matrix.of fun i j : Fin (Module.finrank ℝ (MF K)) =>
    Algebra.trace ℝ (E K L) (Matrix.trace (e₁ i * e₁ j))).det with hG
  have hG0 : G ≠ 0 := by
    refine det_gram_ne_zero K L hli₁ fun m hm hm0 => ?_
    have hm' : m ∈ (Submodule.span ℝ (Set.range e₁) : Set (ME K L)) := hm
    rw [hrange] at hm'
    obtain ⟨m₀, rfl⟩ := hm'
    refine eq_zero_of_range_iotaM K L σ h2 hE hθ hθ0 fun Y₀ => hm0 _ ?_
    show iotaM K L Y₀ ∈ (Submodule.span ℝ (Set.range e₁) : Set (ME K L))
    rw [hrange]; exact ⟨Y₀, rfl⟩
  set k : ℝ≥0∞ := ENNReal.ofReal (Real.sqrt |G|) with hk
  have hk0 : k ≠ 0 := by
    rw [hk, Ne, ENNReal.ofReal_eq_zero, not_le]
    exact Real.sqrt_pos.2 (abs_pos.2 hG0)
  have hktop : k ≠ ⊤ := ENNReal.ofReal_ne_top
  haveI := hH
  haveI := hR
  refine ⟨k • τ₀, IsHaarMeasure.smul τ₀ hk0 hktop, inferInstance, Module.finrank ℝ (MF K), e₁, hli₁, ?_, ?_⟩
  · rw [hrange]; rfl
  ·
    have hmeas_incl : Measurable fun t : Γ => ((t : GL (Fin 2) (F K)) : MF K) :=
      (Units.continuous_val.comp continuous_subtype_val).measurable
    have hcomp : (fun t : Γ => ((t : GL (Fin 2) (F K)) : MF K).map (Algebra.TensorProduct.includeRight : F K →ₐ[K] E K L)) =
        ⇑(iotaM K L) ∘ fun t : Γ => ((t : GL (Fin 2) (F K)) : MF K) := rfl
    have hψ : ⇑(iotaM K L) ∘ (fun c : Fin (Module.finrank ℝ (MF K)) → ℝ => ∑ i, c i • bF K i) =
        fun c => ∑ i, c i • e₁ i := by
      funext c
      simp only [Function.comp_apply, _root_.map_sum, _root_.map_smul, he₁]
    have hdens : (fun X : ME K L => (ENNReal.ofReal |Algebra.norm ℝ (Matrix.det X)|)⁻¹) ∘ ⇑(iotaM K L) =
        fun x => (ENNReal.ofReal |χF K x|)⁻¹ := by
      funext Y
      simp only [Function.comp_apply, det_iotaM, norm_algebraMap_FE K L h2, χF_apply]
    rw [hcomp, ← Measure.map_map (measurable_iotaM K L) hmeas_incl, Measure.map_smul, Measure.map_smul, hmap, ← hdens,
      ← withDensity_map_of_measurableEmbedding (measurableEmbedding_iotaM K L h2),
      Measure.map_map (measurable_iotaM K L) (measurable_ψ (bF K)), hψ, one_smul, withDensity_smul_measure]

include h2 in

theorem arch_twisted (hE : (Algebra.traceForm ℝ (E K L)).Nondegenerate) (δ : GL (Fin 2) (E K L)) (cδ : (E K L)ˣ)
    (hδc : (δ : ME K L) * sM K L σ (δ : ME K L) = (cδ : E K L) • (1 : ME K L))
    {u : E K L} (hu : sE K L σ u = -u) (huu : IsUnit u) :
    letI : MeasurableSpace (twistedCentralizer K L (F K) σ δ) := borel _
    ∃ τ' : Measure (twistedCentralizer K L (F K) σ δ),
      τ'.IsHaarMeasure ∧ τ'.IsMulRightInvariant ∧
      ∃ (n₂ : ℕ) (e₂ : Fin n₂ → ME K L), LinearIndependent ℝ e₂ ∧
        (Submodule.span ℝ (Set.range e₂) : Set (ME K L)) =
          {X | X * (δ : ME K L) = (δ : ME K L) * X.map (sigmaTensor K L (F K) σ)} ∧
        Measure.map (fun t : twistedCentralizer K L (F K) σ δ => ((t : GL (Fin 2) (E K L)) : ME K L)) τ' =
          (1 : ℝ≥0∞) • ((ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n₂ =>
              Algebra.trace ℝ (E K L) (Matrix.trace (e₂ i * e₂ j))).det|)) •
              Measure.map (fun c : Fin n₂ → ℝ => ∑ i, c i • e₂ i) volume).withDensity
            (fun X : ME K L => (ENNReal.ofReal |Algebra.norm ℝ (Matrix.det X)|)⁻¹) := by
  set Γ : Subgroup (GL (Fin 2) (E K L)) := twistedCentralizer K L (F K) σ δ with hΓdef
  letI : MeasurableSpace Γ := borel _
  haveI : BorelSpace Γ := ⟨rfl⟩
  have hΓ : ∀ g : (ME K L)ˣ, g ∈ Γ ↔ (g : ME K L) ∈ Adelta K L σ δ := mem_twistedCentralizer_iff K L σ δ
  set W : Submodule ℝ (ME K L) := Subalgebra.toSubmodule (Adelta K L σ δ) with hW
  set b2 := Module.finBasis ℝ W with hb2
  set e₂ : Fin (Module.finrank ℝ W) → ME K L := ⇑W.subtype ∘ ⇑b2 with he₂
  have hli₂ : LinearIndependent ℝ e₂ := b2.linearIndependent.map' W.subtype W.ker_subtype
  have hsp₂ : Submodule.span ℝ (Set.range e₂) = Subalgebra.toSubmodule (Adelta K L σ δ) := by
    rw [he₂, Set.range_comp, Submodule.span_image, b2.span_eq, Submodule.map_top, Submodule.range_subtype]

  obtain ⟨τ₀, hH, hR, hmap⟩ :=
    MeasureTheory.Measure.exists_isHaarMeasure_subgroup_units_map_val_eq_withDensity_of_abs_det_eq
      (Adelta K L σ δ) Γ hΓ _ e₂ hli₂ hsp₂ (χE K L) (continuous_χE K L)
      (fun g hg => ⟨LinearMap.toMatrix (bA K L σ δ e₂ hli₂ hsp₂) (bA K L σ δ e₂ hli₂ hsp₂)
          (Algebra.lmul ℝ (Adelta K L σ δ) ⟨(g : ME K L), (hΓ g).1 hg⟩),
        mul_e_eq_sum K L σ δ e₂ hli₂ hsp₂ ⟨(g : ME K L), (hΓ g).1 hg⟩,
        abs_det_left_Adelta K L h2 σ δ cδ hδc hu huu e₂ hli₂ hsp₂ ⟨(g : ME K L), (hΓ g).1 hg⟩⟩)
      (fun g hg => ⟨LinearMap.toMatrix (bA K L σ δ e₂ hli₂ hsp₂) (bA K L σ δ e₂ hli₂ hsp₂)
          (LinearMap.mulRight ℝ (⟨(g : ME K L), (hΓ g).1 hg⟩ : Adelta K L σ δ)),
        e_mul_eq_sum K L σ δ e₂ hli₂ hsp₂ ⟨(g : ME K L), (hΓ g).1 hg⟩,
        abs_det_right_Adelta K L h2 σ δ cδ hδc hu huu e₂ hli₂ hsp₂ ⟨(g : ME K L), (hΓ g).1 hg⟩⟩)

  set G : ℝ := (Matrix.of fun i j : Fin (Module.finrank ℝ W) =>
    Algebra.trace ℝ (E K L) (Matrix.trace (e₂ i * e₂ j))).det with hG
  have hG0 : G ≠ 0 := by
    refine det_gram_ne_zero K L hli₂ fun m hm hm0 => ?_
    rw [hsp₂] at hm
    exact eq_zero_of_mem_Adelta K L σ h2 hE δ cδ hδc hu huu hm fun Y hY => hm0 Y (by rw [hsp₂]; exact hY)
  set k : ℝ≥0∞ := ENNReal.ofReal (Real.sqrt |G|) with hk
  have hk0 : k ≠ 0 := by
    rw [hk, Ne, ENNReal.ofReal_eq_zero, not_le]
    exact Real.sqrt_pos.2 (abs_pos.2 hG0)
  have hktop : k ≠ ⊤ := ENNReal.ofReal_ne_top
  haveI := hH
  haveI := hR
  refine ⟨k • τ₀, IsHaarMeasure.smul τ₀ hk0 hktop, inferInstance, Module.finrank ℝ W, e₂, hli₂, ?_, ?_⟩
  · rw [hsp₂]; rfl
  · rw [Measure.map_smul, hmap, one_smul, withDensity_smul_measure]
    rfl

end Assembly

end AutomorphicForm.ArchGramHaar
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isHaarMeasure_map_eq_smul_withDensity_arch_of_isNormConjugator_scalar_of_finrank_eq_two.AutomorphicForm P2MW.S_AutomorphicForm_exists_isHaarMeasure_map_eq_smul_withDensity_arch_of_isNormConjugator_scalar_of_finrank_eq_two.AutomorphicForm.ArchGramHaar"
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isHaarMeasure_map_eq_smul_withDensity_arch_of_isNormConjugator_scalar_of_finrank_eq_two.AutomorphicForm"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isHaarMeasure_map_eq_smul_withDensity_arch_of_isNormConjugator_scalar_of_finrank_eq_two.AutomorphicForm P2MW.S_AutomorphicForm_exists_isHaarMeasure_map_eq_smul_withDensity_arch_of_isNormConjugator_scalar_of_finrank_eq_two.AutomorphicForm.ArchGramHaar"

open scoped TensorProduct.RightActions in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (γ : GL (Fin 2) (InfiniteAdeleRing K))
    (hγ : ∃ c : (InfiniteAdeleRing K)ˣ, γ = Matrix.GeneralLinearGroup.scalar (Fin 2) c)
    (δ y : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))
    (hδ : AutomorphicForm.IsNormConjugator K L (InfiniteAdeleRing K) σ γ δ y) :
    letI : Algebra ℝ (InfiniteAdeleRing K) :=
      ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm.toRingHom.comp
        (algebraMap ℝ (mixedEmbedding.mixedSpace K))).toAlgebra
    letI : Algebra ℝ (L ⊗[K] InfiniteAdeleRing K) :=
      ((Algebra.TensorProduct.includeRight : InfiniteAdeleRing K →ₐ[K] L ⊗[K] InfiniteAdeleRing K).toRingHom.comp
        (algebraMap ℝ (InfiniteAdeleRing K))).toAlgebra
    letI : MeasurableSpace (Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) := borel _
    letI := AutomorphicForm.centralizerBorel (InfiniteAdeleRing K) γ
    letI := AutomorphicForm.twistedCentralizerBorel K L (InfiniteAdeleRing K) σ δ
    ∃ (τ : Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (InfiniteAdeleRing K)))))
      (τ' : Measure (AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ δ)),
      τ.IsHaarMeasure ∧ τ'.IsHaarMeasure ∧ τ.IsMulRightInvariant ∧ τ'.IsMulRightInvariant ∧
      ∃ (n₁ n₂ : ℕ) (e₁ : Fin n₁ → Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K))
        (e₂ : Fin n₂ → Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) (s : ENNReal),
        s ≠ 0 ∧ s ≠ ⊤ ∧
        LinearIndependent ℝ e₁ ∧
          (Submodule.span ℝ (Set.range e₁) : Set (Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K))) =
            Set.range (fun Y : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K) =>
              Y.map (Algebra.TensorProduct.includeRight :
                InfiniteAdeleRing K →ₐ[K] L ⊗[K] InfiniteAdeleRing K)) ∧
        LinearIndependent ℝ e₂ ∧
          (Submodule.span ℝ (Set.range e₂) : Set (Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K))) =
            {X | X * (δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) =
              (δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) *
                X.map (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ)} ∧
        Measure.map (fun t : ↥(Subgroup.centralizer ({γ} : Set (GL (Fin 2) (InfiniteAdeleRing K)))) =>
            ((t : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)).map
              (Algebra.TensorProduct.includeRight :
                InfiniteAdeleRing K →ₐ[K] L ⊗[K] InfiniteAdeleRing K)) τ =
          s • ((ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n₁ =>
                  Algebra.trace ℝ (L ⊗[K] InfiniteAdeleRing K) (Matrix.trace (e₁ i * e₁ j))).det|)) •
                Measure.map (fun c : Fin n₁ → ℝ => ∑ i, c i • e₁ i) volume).withDensity
              (fun X : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K) =>
                (ENNReal.ofReal |Algebra.norm ℝ (Matrix.det X)|)⁻¹) ∧
        Measure.map (fun t : ↥(AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ δ) =>
            ((t : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K))) τ' =
          s • ((ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n₂ =>
                  Algebra.trace ℝ (L ⊗[K] InfiniteAdeleRing K) (Matrix.trace (e₂ i * e₂ j))).det|)) •
                Measure.map (fun c : Fin n₂ → ℝ => ∑ i, c i • e₂ i) volume).withDensity
              (fun X : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K) =>
                (ENNReal.ofReal |Algebra.norm ℝ (Matrix.det X)|)⁻¹) := by
  open _root_.AutomorphicForm _root_.P2MW.S_AutomorphicForm_exists_isHaarMeasure_map_eq_smul_withDensity_arch_of_isNormConjugator_scalar_of_finrank_eq_two.AutomorphicForm AutomorphicForm.ArchGramHaar in
  · obtain ⟨c, rfl⟩ := hγ
    obtain ⟨θ, hθ, hθ0⟩ := exists_theta K L h2 σ hgen
    have hE := (NumberField.InfiniteAdeleRing.traceForm_nondegenerate_and_traceForm_tensorProduct_nondegenerate K L).2
    obtain ⟨cδ, hδc⟩ := exists_hδc K L h2 σ c δ y hδ
    have hu : sE K L σ (θ ⊗ₜ (1 : F K)) = -(θ ⊗ₜ (1 : F K)) := by rw [sE_tmul, hθ, TensorProduct.neg_tmul]
    have huu : IsUnit (θ ⊗ₜ[K] (1 : F K) : E K L) :=
      IsUnit.of_mul_eq_one (θ⁻¹ ⊗ₜ (1 : F K))
        (by rw [Algebra.TensorProduct.tmul_mul_tmul, mul_inv_cancel₀ hθ0, mul_one]; rfl)
    obtain ⟨τ, hτH, hτR, n₁, e₁, hli₁, hsp₁, hτ⟩ := arch_untwisted K L h2 σ hE hθ hθ0 c
    obtain ⟨τ', hτ'H, hτ'R, n₂, e₂, hli₂, hsp₂, hτ'⟩ := arch_twisted K L h2 σ hE δ cδ hδc hu huu
    exact ⟨τ, τ', hτH, hτ'H, hτR, hτ'R, n₁, n₂, e₁, e₂, 1, one_ne_zero, ENNReal.one_ne_top, hli₁, hsp₁, hli₂, hsp₂,
      hτ, hτ'⟩

end S_AutomorphicForm_exists_isHaarMeasure_map_eq_smul_withDensity_arch_of_isNormConjugator_scalar_of_finrank_eq_two
end P2MW
export P2MW.S_AutomorphicForm_exists_isHaarMeasure_map_eq_smul_withDensity_arch_of_isNormConjugator_scalar_of_finrank_eq_two (solution)
