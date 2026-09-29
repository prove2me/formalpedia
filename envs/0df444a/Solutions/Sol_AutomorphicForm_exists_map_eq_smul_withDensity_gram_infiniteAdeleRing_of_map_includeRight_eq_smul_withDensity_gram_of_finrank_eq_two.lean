-- Prove2me | solution 1 for AutomorphicForm.exists_map_eq_smul_withDensity_gram_infiniteAdeleRing_of_map_includeRight_eq_smul_withDensity_gram_of_finrank_eq_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/46f74c46-f76c-5f63-92de-766f89010b88

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_map_eq_smul_withDensity_gram_infiniteAdeleRing_of_map_includeRight_eq_smul_withDensity_gram_of_finrank_eq_two

set_option autoImplicit false
set_option linter.unusedSectionVars false

open IsDedekindDomain NumberField MeasureTheory MeasureTheory.Measure Topology TopologicalSpace Set
open TensorProduct
open scoped TensorProduct.RightActions NNReal ENNReal

noncomputable section

namespace AutomorphicForm
p2m_export "AutomorphicForm" "t2Space_tensor glBorelOf"
namespace GramBaseChange
p2m_open "AutomorphicForm"

section Structures

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

abbrev F : Type := InfiniteAdeleRing K

abbrev E : Type := L ⊗[K] InfiniteAdeleRing K

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

theorem finrank_F : Module.finrank ℝ (F K) = Module.finrank ℚ K := by
  rw [(mixedAlgEquiv K).toLinearEquiv.finrank_eq, mixedEmbedding.finrank]

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

theorem algebraMap_FE_apply (a : F K) :
    algebraMap (F K) (E K L) a = (1 : L) ⊗ₜ a := rfl

theorem algebraMap_RE_eq :
    algebraMap ℝ (E K L) = (algebraMap (F K) (E K L)).comp (algebraMap ℝ (F K)) := rfl

scoped instance isScalarTower_RFE : IsScalarTower ℝ (F K) (E K L) :=
  IsScalarTower.of_algebraMap_eq (R := ℝ) (S := F K) (A := E K L) fun _ => rfl

scoped instance moduleFree_FE : Module.Free (F K) (E K L) := inferInstance

scoped instance moduleFinite_FE : Module.Finite (F K) (E K L) := inferInstance

theorem finrank_FE (h2 : Module.finrank K L = 2) : Module.finrank (F K) (E K L) = 2 := by
  have b := TensorProduct.RightActions.Algebra.TensorProduct.basis (F K) (Module.finBasis K L)
  rw [Module.finrank_eq_card_basis b, Fintype.card_fin, h2]

theorem trace_algebraMap_FE (h2 : Module.finrank K L = 2) (a : F K) :
    Algebra.trace ℝ (E K L) (algebraMap (F K) (E K L) a) = 2 * Algebra.trace ℝ (F K) a := by
  rw [← Algebra.trace_trace (S := F K), Algebra.trace_algebraMap, finrank_FE K L h2, map_nsmul, nsmul_eq_mul,
    Nat.cast_ofNat]

theorem norm_algebraMap_FE (h2 : Module.finrank K L = 2) (a : F K) :
    Algebra.norm ℝ (algebraMap (F K) (E K L) a) = (Algebra.norm ℝ a) ^ 2 := by
  rw [← Algebra.norm_norm (S := F K), Algebra.norm_algebraMap, finrank_FE K L h2, map_pow]

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

theorem proj_algebraMap (h2 : Module.finrank K L = 2) (a : F K) :
    proj K L (algebraMap (F K) (E K L) a) = a := by
  rw [algebraMap_FE_apply, proj_tmul, halfTrace_one K L h2, one_smul]

theorem continuous_algebraMap_FE : Continuous (algebraMap (F K) (E K L)) :=
  IsModuleTopology.continuous_of_linearMap (Algebra.linearMap (F K) (E K L))

theorem continuous_proj : Continuous (proj K L) :=
  IsModuleTopology.continuous_of_linearMap (proj K L)

theorem injective_algebraMap_FE (h2 : Module.finrank K L = 2) : Function.Injective (algebraMap (F K) (E K L)) :=
  Function.LeftInverse.injective (g := proj K L) fun a => proj_algebraMap K L h2 a

def iotaM : Matrix (Fin 2) (Fin 2) (F K) →ₗ[ℝ] Matrix (Fin 2) (Fin 2) (E K L) :=
  ((Algebra.linearMap (F K) (E K L)).restrictScalars ℝ).mapMatrix

theorem iotaM_apply (Y : Matrix (Fin 2) (Fin 2) (F K)) :
    iotaM K L Y = Y.map (Algebra.TensorProduct.includeRight :
      InfiniteAdeleRing K →ₐ[K] L ⊗[K] InfiniteAdeleRing K) := rfl

theorem iotaM_apply' (Y : Matrix (Fin 2) (Fin 2) (F K)) :
    iotaM K L Y = (algebraMap (F K) (E K L)).mapMatrix Y := rfl

def projM : Matrix (Fin 2) (Fin 2) (E K L) → Matrix (Fin 2) (Fin 2) (F K) := fun X => X.map (proj K L)

theorem projM_iotaM (h2 : Module.finrank K L = 2) (Y : Matrix (Fin 2) (Fin 2) (F K)) :
    projM K L (iotaM K L Y) = Y := by
  ext i j
  exact proj_algebraMap K L h2 (Y i j)

theorem injective_iotaM (h2 : Module.finrank K L = 2) : Function.Injective (iotaM K L) :=
  Function.LeftInverse.injective (g := projM K L) fun Y => projM_iotaM K L h2 Y

theorem continuous_iotaM : Continuous (iotaM K L) :=
  continuous_id.matrix_map (continuous_algebraMap_FE K L)

theorem continuous_projM : Continuous (projM K L) :=
  continuous_id.matrix_map (continuous_proj K L)

end Structures

section Measurable

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

attribute [local instance] algRF algRE

scoped instance instMeasurableSpaceMF : MeasurableSpace (Matrix (Fin 2) (Fin 2) (F K)) := borel _
scoped instance instBorelSpaceMF : BorelSpace (Matrix (Fin 2) (Fin 2) (F K)) := ⟨rfl⟩
scoped instance instMeasurableSpaceME : MeasurableSpace (Matrix (Fin 2) (Fin 2) (E K L)) := borel _
scoped instance instBorelSpaceME : BorelSpace (Matrix (Fin 2) (Fin 2) (E K L)) := ⟨rfl⟩
scoped instance instMeasurableSpaceG : MeasurableSpace (GL (Fin 2) (F K)) := borel _
scoped instance instBorelSpaceG : BorelSpace (GL (Fin 2) (F K)) := ⟨rfl⟩

scoped instance instT2E : T2Space (E K L) := t2Space_tensor K L _
scoped instance instT2ME : T2Space (Matrix (Fin 2) (Fin 2) (E K L)) :=
  inferInstanceAs (T2Space (Fin 2 → Fin 2 → E K L))
scoped instance instTAG_MF : IsTopologicalAddGroup (Matrix (Fin 2) (Fin 2) (F K)) := inferInstance
scoped instance instCSM_MF : ContinuousSMul ℝ (Matrix (Fin 2) (Fin 2) (F K)) := inferInstance

theorem measurable_iotaM : Measurable (iotaM K L) := (continuous_iotaM K L).measurable

theorem measurable_projM : Measurable (projM K L) := (continuous_projM K L).measurable

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
    (measurable_projM K L) fun Y => projM_iotaM K L h2 Y

theorem withDensity_map_of_measurableEmbedding {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {f : α → β} (hf : MeasurableEmbedding f) (μ : Measure α) (g : β → ℝ≥0∞) :
    (Measure.map f μ).withDensity g = Measure.map f (μ.withDensity (g ∘ f)) := by
  ext s hs
  rw [withDensity_apply _ hs, hf.restrict_map, hf.lintegral_map, hf.map_apply,
    withDensity_apply _ (hf.measurable hs)]
  simp only [Function.comp_apply]

theorem map_injective_of_measurableEmbedding {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {f : α → β} (hf : MeasurableEmbedding f) {μ ν : Measure α} (h : Measure.map f μ = Measure.map f ν) :
    μ = ν := by
  ext s hs
  have := congrArg (fun ρ : Measure β => ρ (f '' s)) h
  simp only [hf.map_apply, Set.preimage_image_eq _ hf.injective] at this
  exact this

end Measurable

section Gram

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

attribute [local instance] algRF algRE

theorem finrank_matrix_F : Module.finrank ℝ (Matrix (Fin 2) (Fin 2) (F K)) = 4 * Module.finrank ℚ K := by
  rw [Module.finrank_matrix, Fintype.card_fin, finrank_F]

theorem sqrt_two_pow_four_mul (m : ℕ) : Real.sqrt ((2 : ℝ) ^ (4 * m)) = 2 ^ (2 * m) := by
  rw [show (2 : ℝ) ^ (4 * m) = (2 ^ (2 * m)) ^ 2 by rw [← pow_mul]; ring_nf, Real.sqrt_sq (by positivity)]

theorem gram_iotaM (h2 : Module.finrank K L = 2) {n : ℕ} (e' : Fin n → Matrix (Fin 2) (Fin 2) (F K)) :
    (Matrix.of fun i j : Fin n =>
        Algebra.trace ℝ (E K L) (Matrix.trace (iotaM K L (e' i) * iotaM K L (e' j)))) =
      (2 : ℝ) • Matrix.of fun i j : Fin n => Algebra.trace ℝ (F K) (Matrix.trace (e' i * e' j)) := by
  ext i j
  simp only [Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
  rw [iotaM_apply', iotaM_apply', ← map_mul, RingHom.mapMatrix_apply, ← AddMonoidHom.map_trace]
  exact trace_algebraMap_FE K L h2 _

theorem density_iotaM (h2 : Module.finrank K L = 2) (Y : Matrix (Fin 2) (Fin 2) (F K)) :
    (ENNReal.ofReal |Algebra.norm ℝ (Matrix.det (iotaM K L Y))|)⁻¹ =
      (ENNReal.ofReal |Algebra.norm ℝ (Matrix.det Y)| ^ 2)⁻¹ := by
  rw [iotaM_apply', ← RingHom.map_det, norm_algebraMap_FE K L h2, abs_pow, ENNReal.ofReal_pow (abs_nonneg _)]

end Gram

end AutomorphicForm.GramBaseChange
p2m_reactivate "P2MW.S_AutomorphicForm_exists_map_eq_smul_withDensity_gram_infiniteAdeleRing_of_map_includeRight_eq_smul_withDensity_gram_of_finrank_eq_two.AutomorphicForm P2MW.S_AutomorphicForm_exists_map_eq_smul_withDensity_gram_infiniteAdeleRing_of_map_includeRight_eq_smul_withDensity_gram_of_finrank_eq_two.AutomorphicForm.GramBaseChange"
p2m_reactivate "P2MW.S_AutomorphicForm_exists_map_eq_smul_withDensity_gram_infiniteAdeleRing_of_map_includeRight_eq_smul_withDensity_gram_of_finrank_eq_two.AutomorphicForm"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_map_eq_smul_withDensity_gram_infiniteAdeleRing_of_map_includeRight_eq_smul_withDensity_gram_of_finrank_eq_two.AutomorphicForm P2MW.S_AutomorphicForm_exists_map_eq_smul_withDensity_gram_infiniteAdeleRing_of_map_includeRight_eq_smul_withDensity_gram_of_finrank_eq_two.AutomorphicForm.GramBaseChange"

open AutomorphicForm.GramBaseChange in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (h2 : Module.finrank K L = 2)
    (μ : @Measure (GL (Fin 2) (InfiniteAdeleRing K)) (AutomorphicForm.glBorelOf (InfiniteAdeleRing K)))
    (n : ℕ) (e : Fin n → Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) (s : ENNReal)
    (h :
      letI : Algebra ℝ (InfiniteAdeleRing K) :=
        ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm.toRingHom.comp
          (algebraMap ℝ (mixedEmbedding.mixedSpace K))).toAlgebra
      letI : Algebra ℝ (L ⊗[K] InfiniteAdeleRing K) :=
        ((Algebra.TensorProduct.includeRight : InfiniteAdeleRing K →ₐ[K] L ⊗[K] InfiniteAdeleRing K).toRingHom.comp
          (algebraMap ℝ (InfiniteAdeleRing K))).toAlgebra
      letI : MeasurableSpace (Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) := borel _
      letI := AutomorphicForm.glBorelOf (InfiniteAdeleRing K)
      LinearIndependent ℝ e ∧
        (Submodule.span ℝ (Set.range e) : Set (Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K))) =
          Set.range (fun Y : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K) =>
            Y.map (Algebra.TensorProduct.includeRight :
              InfiniteAdeleRing K →ₐ[K] L ⊗[K] InfiniteAdeleRing K)) ∧
        Measure.map (fun t : GL (Fin 2) (InfiniteAdeleRing K) =>
            (t : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)).map
              (Algebra.TensorProduct.includeRight :
                InfiniteAdeleRing K →ₐ[K] L ⊗[K] InfiniteAdeleRing K)) μ =
          s • ((ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n =>
                  Algebra.trace ℝ (L ⊗[K] InfiniteAdeleRing K) (Matrix.trace (e i * e j))).det|)) •
                Measure.map (fun c : Fin n → ℝ => ∑ i, c i • e i) volume).withDensity
              (fun X : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K) =>
                (ENNReal.ofReal |Algebra.norm ℝ (Matrix.det X)|)⁻¹)) :
    letI : Algebra ℝ (InfiniteAdeleRing K) :=
      ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm.toRingHom.comp
        (algebraMap ℝ (mixedEmbedding.mixedSpace K))).toAlgebra
    letI : MeasurableSpace (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) := borel _
    letI := AutomorphicForm.glBorelOf (InfiniteAdeleRing K)
    ∃ e' : Fin n → Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K),
      LinearIndependent ℝ e' ∧
        Submodule.span ℝ (Set.range e') = ⊤ ∧
        Measure.map (fun t : GL (Fin 2) (InfiniteAdeleRing K) =>
            (t : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K))) μ =
          (2 ^ (2 * Module.finrank ℚ K) * s) •
            ((ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n =>
                  Algebra.trace ℝ (InfiniteAdeleRing K) (Matrix.trace (e' i * e' j))).det|)) •
                Measure.map (fun c : Fin n → ℝ => ∑ i, c i • e' i) volume).withDensity
              (fun Y : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K) =>
                (ENNReal.ofReal |Algebra.norm ℝ (Matrix.det Y)| ^ 2)⁻¹) := by
  classical
  letI : Algebra ℝ (InfiniteAdeleRing K) := algRF K
  letI : Algebra ℝ (L ⊗[K] InfiniteAdeleRing K) := algRE K L
  obtain ⟨hli, hsp, hmap⟩ := h

  have hmem : ∀ i, e i ∈ Set.range (fun Y : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K) =>
      Y.map (Algebra.TensorProduct.includeRight : InfiniteAdeleRing K →ₐ[K] L ⊗[K] InfiniteAdeleRing K)) := by
    intro i
    rw [← hsp]
    exact Submodule.subset_span (Set.mem_range_self i)
  choose e' he' using hmem
  have he'ι : ∀ i, iotaM K L (e' i) = e i := he'
  have hcomp : (iotaM K L) ∘ e' = e := funext he'ι

  have hli' : LinearIndependent ℝ e' := by
    have : LinearIndependent ℝ (iotaM K L ∘ e') := by rw [hcomp]; exact hli
    exact LinearIndependent.of_comp _ this
  have hsp' : Submodule.span ℝ (Set.range e') = ⊤ := by
    refine Submodule.eq_top_iff'.2 fun Y => ?_
    have hY : iotaM K L Y ∈ (Submodule.span ℝ (Set.range e) : Set (Matrix (Fin 2) (Fin 2) (E K L))) := by
      rw [hsp]; exact ⟨Y, rfl⟩
    rw [← hcomp, Set.range_comp, Submodule.span_image] at hY
    obtain ⟨Z, hZ, hZY⟩ := (Submodule.mem_map).1 hY
    rw [← injective_iotaM K L h2 hZY]
    exact hZ
  refine ⟨e', hli', hsp', ?_⟩

  have hn : n = 4 * Module.finrank ℚ K := by
    have hb := Module.finrank_eq_card_basis (Module.Basis.mk hli' (by rw [hsp']))
    rw [Fintype.card_fin, finrank_matrix_F] at hb
    exact hb.symm

  set GK : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i j : Fin n =>
    Algebra.trace ℝ (F K) (Matrix.trace (e' i * e' j)) with hGK
  set AK : ℝ≥0∞ := ENNReal.ofReal (Real.sqrt |GK.det|) with hAK
  set fK : (Fin n → ℝ) → Matrix (Fin 2) (Fin 2) (F K) := fun c => ∑ i, c i • e' i with hfK
  set νK : Measure (Matrix (Fin 2) (Fin 2) (F K)) := Measure.map fK volume with hνK
  set ρK : Matrix (Fin 2) (Fin 2) (F K) → ℝ≥0∞ := fun Y =>
    (ENNReal.ofReal |Algebra.norm ℝ (Matrix.det Y)| ^ 2)⁻¹ with hρK
  set ρL : Matrix (Fin 2) (Fin 2) (E K L) → ℝ≥0∞ := fun X =>
    (ENNReal.ofReal |Algebra.norm ℝ (Matrix.det X)|)⁻¹ with hρL

  have hGram : (Matrix.of fun i j : Fin n =>
      Algebra.trace ℝ (E K L) (Matrix.trace (e i * e j))) = (2 : ℝ) • GK := by
    have := gram_iotaM K L h2 e'
    simp only [he'ι] at this
    exact this
  have hdet : (Matrix.of fun i j : Fin n =>
      Algebra.trace ℝ (E K L) (Matrix.trace (e i * e j))).det = 2 ^ n * GK.det := by
    rw [hGram, Matrix.det_smul, Fintype.card_fin]
  have hs2 : Real.sqrt ((2 : ℝ) ^ n) = 2 ^ (2 * Module.finrank ℚ K) := by
    rw [hn]; exact sqrt_two_pow_four_mul _
  have hA : ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n =>
      Algebra.trace ℝ (E K L) (Matrix.trace (e i * e j))).det|) = 2 ^ (2 * Module.finrank ℚ K) * AK := by
    rw [hdet, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ n), Real.sqrt_mul (by positivity), hs2,
      ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]

  have hfK_meas : Measurable fK := by
    refine Continuous.measurable ?_
    exact continuous_finsetSum _ fun i _ => (continuous_apply i).smul continuous_const
  have hfL : (fun c : Fin n → ℝ => ∑ i, c i • e i) = iotaM K L ∘ fK := by
    funext c
    simp only [Function.comp_apply, hfK, _root_.map_sum, map_smul, he'ι]
  have hνL : Measure.map (fun c : Fin n → ℝ => ∑ i, c i • e i) volume = Measure.map (iotaM K L) νK := by
    rw [hfL, hνK, Measure.map_map (measurable_iotaM K L) hfK_meas]

  have hρ : ρL ∘ iotaM K L = ρK := by
    funext Y
    exact density_iotaM K L h2 Y

  have hιemb := measurableEmbedding_iotaM K L h2
  have hval : Measurable (fun t : GL (Fin 2) (InfiniteAdeleRing K) =>
      (t : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K))) := Units.continuous_val.measurable
  have hLHS : Measure.map (fun t : GL (Fin 2) (InfiniteAdeleRing K) =>
        (t : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)).map
          (Algebra.TensorProduct.includeRight : InfiniteAdeleRing K →ₐ[K] L ⊗[K] InfiniteAdeleRing K)) μ =
      Measure.map (iotaM K L) (Measure.map (fun t : GL (Fin 2) (InfiniteAdeleRing K) =>
        (t : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K))) μ) := by
    rw [Measure.map_map (measurable_iotaM K L) hval]
    rfl
  have hRHS : s • ((ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n =>
        Algebra.trace ℝ (E K L) (Matrix.trace (e i * e j))).det|)) •
          Measure.map (fun c : Fin n → ℝ => ∑ i, c i • e i) volume).withDensity ρL =
      Measure.map (iotaM K L) ((2 ^ (2 * Module.finrank ℚ K) * s) • ((AK • νK).withDensity ρK)) := by
    rw [hA, hνL, ← Measure.map_smul, withDensity_map_of_measurableEmbedding hιemb, hρ, Measure.map_smul,
      ← smul_smul, withDensity_smul_measure, Measure.map_smul, smul_smul, mul_comm s]
  rw [hLHS, hRHS] at hmap
  exact map_injective_of_measurableEmbedding hιemb hmap

end S_AutomorphicForm_exists_map_eq_smul_withDensity_gram_infiniteAdeleRing_of_map_includeRight_eq_smul_withDensity_gram_of_finrank_eq_two
end P2MW
export P2MW.S_AutomorphicForm_exists_map_eq_smul_withDensity_gram_infiniteAdeleRing_of_map_includeRight_eq_smul_withDensity_gram_of_finrank_eq_two (solution)
