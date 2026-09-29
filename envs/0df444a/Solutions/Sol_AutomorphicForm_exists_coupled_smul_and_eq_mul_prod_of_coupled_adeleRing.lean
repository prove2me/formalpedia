-- Prove2me | solution 1 for AutomorphicForm.exists_coupled_smul_and_eq_mul_prod_of_coupled_adeleRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/15230768-c57b-56ca-b53d-98d67c9eac89

import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_NumberField_AdelicHaar
import Theorems.Thm_AutomorphicForm_exists_continuousMulEquiv_centralizer_twistedCentralizer_of_isNormConjugator
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_coupled_smul_and_eq_mul_prod_of_coupled_adeleRing
p2m_attr_erase "simp" "LT.TwistedNorm.sigmaPartialNorm_zero LT.TwistedNorm.GL2.traceDetCompanion_apply_10 LT.TwistedNorm.GL2.traceDetCompanion_apply_00 LT.TwistedNorm.GL2.traceDetCompanion_apply_01 LT.TwistedNorm.GL2.traceDetCompanion_apply_11"

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory MeasureTheory.Measure Topology TopologicalSpace Set Filter
open NumberField.AdelicLevel NumberField.AdelicHaar TensorProduct
open scoped TensorProduct.RightActions NNReal ENNReal Classical

noncomputable section

namespace AutomorphicForm
p2m_export "AutomorphicForm" "tensorArch tensorPlace semiLocalComponent_glFin_baseChangeGL tensorArch_toTensorGL tensorPlace_toTensorGL tensorArch_sigmaGL tensorPlace_sigmaGL baseChangeGLEquiv archIdentGLEquiv baseChangeGLEquiv_apply semiLocalEval_eq semiLocalHomeomorph_eq isTopologicalRing_tensor t2Space_tensor locallyCompactSpace_tensor isTopologicalGroup_tensorGL t2Space_tensorGL locallyCompactSpace_tensorGL centralizerBorel toTensorGL semiLocalHomeomorph piIntegers semiLocalIntegers semiLocalIntegers_eq_preimage semiLocalIntegralSet isOpen_semiLocalIntegralSet sigmaTensor sigmaGL normString IsNormConjugator twistedCentralizer twistedCentralizerBorel Coupled semiLocalEval semiLocalComponent integralUnitsSet mem_integralUnitsSet localIntegralSet mem_localIntegralSet locallyCompactSpace_localGL localCentralizer localCentralizerBorel IsRegularSemisimple mem_sigmaCentralizer_iff exists_continuousMulEquiv_centralizer_twistedCentralizer_of_isNormConjugator"
namespace CoupledTorusConstants
p2m_open "AutomorphicForm"

section Generic

variable {K L : Type} [Field K] [Field L] [Algebra K L]

theorem isRegularSemisimple_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    {g : GL (Fin 2) R} (hg : IsRegularSemisimple g) :
    IsRegularSemisimple (Matrix.GeneralLinearGroup.map f g) := by
  unfold IsRegularSemisimple at hg ⊢
  have hval : ((Matrix.GeneralLinearGroup.map f g : GL (Fin 2) S) : Matrix (Fin 2) (Fin 2) S) =
      f.mapMatrix (g : Matrix (Fin 2) (Fin 2) R) := rfl
  rw [hval, ← RingHom.map_det, RingHom.mapMatrix_apply, ← AddMonoidHom.map_trace]
  have := hg.map f
  simpa [map_ofNat] using this

theorem map_normString {A B : Type} [CommRing A] [Algebra K A] [CommRing B] [Algebra K B]
    (σ : L ≃ₐ[K] L) (F : GL (Fin 2) (L ⊗[K] A) →* GL (Fin 2) (L ⊗[K] B))
    (hF : ∀ x, F (sigmaGL K L A σ x) = sigmaGL K L B σ (F x)) (δ : GL (Fin 2) (L ⊗[K] A)) :
    F (normString K L A σ δ) = normString K L B σ (F δ) := by
  unfold normString
  rw [map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  show F ((sigmaGL K L A σ)^[i] δ) = (sigmaGL K L B σ)^[i] (F δ)
  exact (Function.Semiconj.iterate_right (f := F) (ga := sigmaGL K L A σ) (gb := sigmaGL K L B σ) hF i δ)

theorem isNormConjugator_map {A B : Type} [CommRing A] [Algebra K A] [CommRing B] [Algebra K B]
    (σ : L ≃ₐ[K] L) (F : GL (Fin 2) (L ⊗[K] A) →* GL (Fin 2) (L ⊗[K] B)) (Fb : GL (Fin 2) A →* GL (Fin 2) B)
    (hF : ∀ x, F (sigmaGL K L A σ x) = sigmaGL K L B σ (F x))
    (hFt : ∀ g, F (toTensorGL K L A g) = toTensorGL K L B (Fb g))
    {γ : GL (Fin 2) A} {δ y : GL (Fin 2) (L ⊗[K] A)} (hy : IsNormConjugator K L A σ γ δ y) :
    IsNormConjugator K L B σ (Fb γ) (F δ) (F y) := by
  unfold IsNormConjugator at hy ⊢
  rw [← hFt, hy, map_mul, map_mul, map_inv, map_normString σ F hF]

theorem mul_mem_integralUnitsSet {A : Type*} [CommRing A] (U : Subring A) {g h : GL (Fin 2) A}
    (hg : g ∈ integralUnitsSet (U : Set A)) (hh : h ∈ integralUnitsSet (U : Set A)) :
    g * h ∈ integralUnitsSet (U : Set A) := by
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [Units.val_mul, Matrix.mul_apply]
    exact U.sum_mem fun k _ => U.mul_mem (hg.1 i k) (hh.1 k j)
  · rw [mul_inv_rev, Units.val_mul, Matrix.mul_apply]
    exact U.sum_mem fun k _ => U.mul_mem (hh.2 i k) (hg.2 k j)

theorem inv_mem_integralUnitsSet {A : Type*} [CommRing A] (U : Set A) {g : GL (Fin 2) A}
    (hg : g ∈ integralUnitsSet U) : g⁻¹ ∈ integralUnitsSet U :=
  ⟨hg.2, by rw [inv_inv]; exact hg.1⟩

end Generic

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

abbrev Garch (K : Type) [Field K] [NumberField K] : Type := GL (Fin 2) (InfiniteAdeleRing K)
abbrev Gad (K : Type) [Field K] [NumberField K] : Type := GL (Fin 2) (AdeleRing (𝓞 K) K)
abbrev Gv (v : HeightOneSpectrum (𝓞 K)) : Type := GL (Fin 2) (v.adicCompletion K)
abbrev SL (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) : Type := L ⊗[K] v.adicCompletion K
abbrev Gsl (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) : Type := GL (Fin 2) (SL K L v)
abbrev Gt (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] : Type :=
  GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)
abbrev Ht (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] : Type :=
  GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)

section Instances

scoped instance instSecondCountableCompletion (w : InfinitePlace K) : SecondCountableTopology w.Completion :=
  (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology

scoped instance instSecondCountableInfiniteAdeleRing : SecondCountableTopology (InfiniteAdeleRing K) :=
  show SecondCountableTopology ((w : InfinitePlace K) → w.Completion) from inferInstance

scoped instance instSecondCountableMulOpposite (X : Type*) [TopologicalSpace X] [Mul X]
    [SecondCountableTopology X] : SecondCountableTopology Xᵐᵒᵖ :=
  MulOpposite.opHomeomorph.symm.secondCountableTopology

theorem secondCountable_gl (A : Type*) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [SecondCountableTopology A] : SecondCountableTopology (GL (Fin 2) A) := by
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) A) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → A))
  exact Units.isEmbedding_embedProduct.secondCountableTopology

scoped instance instSecondCountableGarch : SecondCountableTopology (Garch K) := secondCountable_gl _
scoped instance instSecondCountableGv (v : HeightOneSpectrum (𝓞 K)) : SecondCountableTopology (Gv (K := K) v) :=
  secondCountable_gl _

scoped instance instLocallyCompactGarch : LocallyCompactSpace (Garch K) := by
  haveI : T2Space (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) :=
    inferInstanceAs (T2Space (Fin 2 → Fin 2 → InfiniteAdeleRing K))
  haveI : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) :=
    inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → InfiniteAdeleRing K))
  exact Units.isClosedEmbedding_embedProduct.locallyCompactSpace
scoped instance instLocallyCompactGv (v : HeightOneSpectrum (𝓞 K)) : LocallyCompactSpace (Gv (K := K) v) :=
  locallyCompactSpace_localGL K v
scoped instance instT2Garch : T2Space (Garch K) := by
  haveI : T2Space (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) :=
    inferInstanceAs (T2Space (Fin 2 → Fin 2 → InfiniteAdeleRing K))
  exact Units.isEmbedding_embedProduct.t2Space
scoped instance instT2Gv (v : HeightOneSpectrum (𝓞 K)) : T2Space (Gv (K := K) v) := by
  haveI : T2Space (Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) :=
    inferInstanceAs (T2Space (Fin 2 → Fin 2 → v.adicCompletion K))
  exact Units.isEmbedding_embedProduct.t2Space
scoped instance instT2Gad : T2Space (Gad K) := by
  haveI : T2Space (Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) :=
    inferInstanceAs (T2Space (Fin 2 → Fin 2 → AdeleRing (𝓞 K) K))
  exact Units.isEmbedding_embedProduct.t2Space

scoped instance instIsTopologicalRingSL (v : HeightOneSpectrum (𝓞 K)) : IsTopologicalRing (SL K L v) :=
  isTopologicalRing_tensor K L _
scoped instance instT2SL (v : HeightOneSpectrum (𝓞 K)) : T2Space (SL K L v) := t2Space_tensor K L _
scoped instance instLocallyCompactSL (v : HeightOneSpectrum (𝓞 K)) : LocallyCompactSpace (SL K L v) :=
  locallyCompactSpace_tensor K L _
scoped instance instFiniteExtension (v : HeightOneSpectrum (𝓞 K)) : Finite (v.Extension (𝓞 L)) :=
  HeightOneSpectrum.Extension.finite (𝓞 K) K L (𝓞 L) v
scoped instance instSecondCountableSL (v : HeightOneSpectrum (𝓞 K)) : SecondCountableTopology (SL K L v) :=
  (semiLocalHomeomorph K L v).secondCountableTopology
scoped instance instSecondCountableGsl (v : HeightOneSpectrum (𝓞 K)) : SecondCountableTopology (Gsl K L v) :=
  secondCountable_gl _
scoped instance instLocallyCompactGsl (v : HeightOneSpectrum (𝓞 K)) : LocallyCompactSpace (Gsl K L v) :=
  locallyCompactSpace_tensorGL K L _
scoped instance instIsTopologicalGroupGsl (v : HeightOneSpectrum (𝓞 K)) : IsTopologicalGroup (Gsl K L v) :=
  isTopologicalGroup_tensorGL K L _
scoped instance instT2Gsl (v : HeightOneSpectrum (𝓞 K)) : T2Space (Gsl K L v) := t2Space_tensorGL K L _
scoped instance instIsTopologicalRingTA : IsTopologicalRing (L ⊗[K] AdeleRing (𝓞 K) K) :=
  isTopologicalRing_tensor K L _
scoped instance instT2TA : T2Space (L ⊗[K] AdeleRing (𝓞 K) K) := t2Space_tensor K L _
scoped instance instIsTopologicalGroupGt : IsTopologicalGroup (Gt K L) := isTopologicalGroup_tensorGL K L _
scoped instance instT2Gt : T2Space (Gt K L) := t2Space_tensorGL K L _
scoped instance instIsTopologicalRingTI : IsTopologicalRing (L ⊗[K] InfiniteAdeleRing K) :=
  isTopologicalRing_tensor K L _
scoped instance instT2TI : T2Space (L ⊗[K] InfiniteAdeleRing K) := t2Space_tensor K L _
scoped instance instIsTopologicalGroupHt : IsTopologicalGroup (Ht K L) := isTopologicalGroup_tensorGL K L _
scoped instance instLocallyCompactHt : LocallyCompactSpace (Ht K L) := locallyCompactSpace_tensorGL K L _
scoped instance instT2Ht : T2Space (Ht K L) := t2Space_tensorGL K L _
scoped instance instSecondCountableHt : SecondCountableTopology (Ht K L) :=
  (archIdentGLEquiv K L).toHomeomorph.secondCountableTopology

scoped instance instMeasurableSpaceGarch : MeasurableSpace (Garch K) := borel _
scoped instance instBorelSpaceGarch : BorelSpace (Garch K) := ⟨rfl⟩
scoped instance instMeasurableSpaceGv (v : HeightOneSpectrum (𝓞 K)) : MeasurableSpace (Gv (K := K) v) := borel _
scoped instance instBorelSpaceGv (v : HeightOneSpectrum (𝓞 K)) : BorelSpace (Gv (K := K) v) := ⟨rfl⟩
scoped instance instMeasurableSpaceGad : MeasurableSpace (Gad K) := borel _
scoped instance instBorelSpaceGad : BorelSpace (Gad K) := ⟨rfl⟩
scoped instance instMeasurableSpaceHt : MeasurableSpace (Ht K L) := borel _
scoped instance instBorelSpaceHt : BorelSpace (Ht K L) := ⟨rfl⟩
scoped instance instMeasurableSpaceGsl (v : HeightOneSpectrum (𝓞 K)) : MeasurableSpace (Gsl K L v) := borel _
scoped instance instBorelSpaceGsl (v : HeightOneSpectrum (𝓞 K)) : BorelSpace (Gsl K L v) := ⟨rfl⟩
scoped instance instMeasurableSpaceGt : MeasurableSpace (Gt K L) := borel _
scoped instance instBorelSpaceGt : BorelSpace (Gt K L) := ⟨rfl⟩

scoped instance (priority := 10000) instMeasurableSpaceSubgroupGad (H : Subgroup (Gad K)) : MeasurableSpace H :=
  borel _
scoped instance instBorelSpaceSubgroupGad (H : Subgroup (Gad K)) : BorelSpace H := ⟨rfl⟩
scoped instance (priority := 10000) instMeasurableSpaceSubgroupGarch (H : Subgroup (Garch K)) :
    MeasurableSpace H := borel _
scoped instance instBorelSpaceSubgroupGarch (H : Subgroup (Garch K)) : BorelSpace H := ⟨rfl⟩
scoped instance (priority := 10000) instMeasurableSpaceSubgroupGv (v : HeightOneSpectrum (𝓞 K))
    (H : Subgroup (Gv (K := K) v)) : MeasurableSpace H := borel _
scoped instance instBorelSpaceSubgroupGv (v : HeightOneSpectrum (𝓞 K)) (H : Subgroup (Gv (K := K) v)) :
    BorelSpace H := ⟨rfl⟩
scoped instance (priority := 10000) instMeasurableSpaceSubgroupGt (H : Subgroup (Gt K L)) : MeasurableSpace H :=
  borel _
scoped instance instBorelSpaceSubgroupGt (H : Subgroup (Gt K L)) : BorelSpace H := ⟨rfl⟩
scoped instance (priority := 10000) instMeasurableSpaceSubgroupHt (H : Subgroup (Ht K L)) : MeasurableSpace H :=
  borel _
scoped instance instBorelSpaceSubgroupHt (H : Subgroup (Ht K L)) : BorelSpace H := ⟨rfl⟩
scoped instance (priority := 10000) instMeasurableSpaceSubgroupGsl (v : HeightOneSpectrum (𝓞 K))
    (H : Subgroup (Gsl K L v)) : MeasurableSpace H := borel _
scoped instance instBorelSpaceSubgroupGsl (v : HeightOneSpectrum (𝓞 K)) (H : Subgroup (Gsl K L v)) :
    BorelSpace H := ⟨rfl⟩

end Instances

variable (K L) in
theorem continuous_sigmaTensor (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A]
    (σ : L ≃ₐ[K] L) : Continuous (sigmaTensor K L A σ) := by
  haveI := isTopologicalRing_tensor K L A
  exact IsModuleTopology.continuous_of_linearMap
    (TensorProduct.RightActions.AlgebraMap.baseChange K L L A σ.toAlgHom).toLinearMap

variable (K L) in
theorem continuous_sigmaGL (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A]
    (σ : L ≃ₐ[K] L) : Continuous (sigmaGL K L A σ) := by
  haveI := isTopologicalRing_tensor K L A
  refine Continuous.units_map _ ?_
  exact continuous_id.matrix_map (continuous_sigmaTensor K L A σ)

variable (K L) in
theorem isClosed_twistedCentralizer (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A]
    [IsTopologicalRing A] [T2Space A] (σ : L ≃ₐ[K] L) (δ : GL (Fin 2) (L ⊗[K] A)) :
    IsClosed ((twistedCentralizer K L A σ δ : Subgroup (GL (Fin 2) (L ⊗[K] A))) : Set (GL (Fin 2) (L ⊗[K] A))) := by
  haveI := isTopologicalGroup_tensorGL K L A
  haveI := t2Space_tensorGL K L A
  have hc : Continuous fun t : GL (Fin 2) (L ⊗[K] A) => t * δ * (sigmaGL K L A σ t)⁻¹ :=
    (continuous_id.mul continuous_const).mul (continuous_sigmaGL K L A σ).inv
  have : ((twistedCentralizer K L A σ δ : Subgroup (GL (Fin 2) (L ⊗[K] A))) : Set (GL (Fin 2) (L ⊗[K] A))) =
      (fun t : GL (Fin 2) (L ⊗[K] A) => t * δ * (sigmaGL K L A σ t)⁻¹) ⁻¹' {δ} := by
    ext t
    exact mem_sigmaCentralizer_iff
  rw [this]
  exact (isClosed_singleton).preimage hc

variable (K L) in

theorem continuous_includeRight (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A] :
    Continuous (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A) := by
  have h : Continuous fun a : A => a • (1 : L ⊗[K] A) := continuous_id.fun_smul continuous_const
  refine h.congr fun a => ?_
  rw [← Algebra.algebraMap_eq_smul_one]
  rfl

variable (K L) in

theorem continuous_toTensorGL (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A] :
    Continuous (toTensorGL K L A) := by
  haveI := isTopologicalRing_tensor K L A
  refine Continuous.units_map _ ?_
  change Continuous fun M : Matrix (Fin 2) (Fin 2) A =>
    M.map ((Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A).toRingHom)
  exact continuous_id.matrix_map (continuous_includeRight K L A)

private theorem _root_.AutomorphicForm.CoupledTorusConstants.isClosed_centralizer {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    (g : G) : IsClosed ((Subgroup.centralizer ({g} : Set G) : Subgroup G) : Set G) := by
  show IsClosed (Set.centralizer ({g} : Set G))
  exact Set.isClosed_centralizer _

p2m_export "AutomorphicForm.CoupledTorusConstants" "isClosed_centralizer"

section UnitDictionary

variable (v : HeightOneSpectrum (𝓞 K))

theorem mem_semiLocalIntegers_iff (x : SL K L v) :
    x ∈ semiLocalIntegers K L v ↔
      ∀ w : v.Extension (𝓞 L), semiLocalHomeomorph K L v x w ∈ w.1.adicCompletionIntegers L := by
  rw [semiLocalIntegers_eq_preimage, Set.mem_preimage, piIntegers, Set.mem_univ_pi]
  rfl

theorem semiLocalHomeomorph_one_tmul (z : v.adicCompletion K) (w : v.Extension (𝓞 L)) :
    semiLocalHomeomorph K L v ((1 : L) ⊗ₜ z) w = w.adicCompletionSemialgHom K L z := by
  rw [semiLocalHomeomorph_eq]
  show HeightOneSpectrum.adicCompletion.baseChange K L (𝓞 L) v ((1 : L) ⊗ₜ z) w = _
  rw [HeightOneSpectrum.adicCompletion.baseChange_tmul_apply, map_one, one_mul]
  rfl

theorem semialgHom_mem_iff (w : v.Extension (𝓞 L)) (z : v.adicCompletion K) :
    w.adicCompletionSemialgHom K L z ∈ w.1.adicCompletionIntegers L ↔ z ∈ v.adicCompletionIntegers K := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, HeightOneSpectrum.mem_adicCompletionIntegers,
    HeightOneSpectrum.Extension.valued_adicCompletionSemialgHom K L w z, pow_le_one_iff]
  exact HeightOneSpectrum.ramificationIdx_ne_zero (𝓞 K) (𝓞 L)
    (algebraMap_injective_of_field_isFractionRing (R := 𝓞 K) (S := 𝓞 L) K L) w.1

theorem nonempty_extension : Nonempty (v.Extension (𝓞 L)) := by
  haveI := v.isMaximal
  obtain ⟨Q, hQmax, hQover⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 L) v.asIdeal
  have hQ : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q
  refine ⟨⟨⟨Q, hQmax.isPrime, hQ⟩, ?_⟩⟩
  apply HeightOneSpectrum.ext
  simp only [HeightOneSpectrum.under_asIdeal]
  exact hQover.over.symm

theorem one_tmul_mem_semiLocalIntegers_iff (z : v.adicCompletion K) :
    ((1 : L) ⊗ₜ[K] z) ∈ semiLocalIntegers K L v ↔ z ∈ v.adicCompletionIntegers K := by
  rw [mem_semiLocalIntegers_iff]
  simp only [semiLocalHomeomorph_one_tmul, semialgHom_mem_iff]
  obtain ⟨w⟩ := nonempty_extension (K := K) (L := L) v
  exact ⟨fun h => h w, fun h _ => h⟩

theorem toTensorGL_mem_semiLocalIntegralSet_iff (g : Gv (K := K) v) :
    toTensorGL K L (v.adicCompletion K) g ∈ semiLocalIntegralSet K L v ↔ g ∈ localIntegralSet K v := by
  have hval : ∀ (h : Gv (K := K) v) (i j : Fin 2),
      ((toTensorGL K L (v.adicCompletion K) h : Gsl K L v) : Matrix (Fin 2) (Fin 2) (SL K L v)) i j =
        (1 : L) ⊗ₜ[K] ((h : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j) := fun _ _ _ => rfl
  simp only [semiLocalIntegralSet, mem_integralUnitsSet, ← map_inv, hval, one_tmul_mem_semiLocalIntegers_iff,
    mem_localIntegralSet]

end UnitDictionary

section Cofinite

variable (v : HeightOneSpectrum (𝓞 K))

theorem semiLocalEval_mem_semiLocalIntegers_iff (a : FiniteAdeleRing (𝓞 L) L) :
    semiLocalEval K L v a ∈ semiLocalIntegers K L v ↔
      ∀ w : v.Extension (𝓞 L), a w.1 ∈ w.1.adicCompletionIntegers L := by
  rw [semiLocalIntegers_eq_preimage, Set.mem_preimage, semiLocalHomeomorph_eq, semiLocalEval_eq,
    AlgEquiv.apply_symm_apply, piIntegers, Set.mem_univ_pi]
  rfl

theorem semiLocalComponent_apply (h : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) (i j : Fin 2) :
    (semiLocalComponent K L v h : Matrix (Fin 2) (Fin 2) (SL K L v)) i j =
      semiLocalEval K L v ((h : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 L) L)) i j) := rfl

theorem semiLocalComponent_mem_iff (h : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) :
    semiLocalComponent K L v h ∈ semiLocalIntegralSet K L v ↔
      ∀ w : v.Extension (𝓞 L), finComponent (𝓞 L) L w.1 h ∈ localIntegralSet L w.1 := by
  simp only [semiLocalIntegralSet, mem_integralUnitsSet, ← map_inv, semiLocalComponent_apply,
    semiLocalEval_mem_semiLocalIntegers_iff, mem_localIntegralSet, finComponent_apply]
  constructor
  · rintro ⟨h1, h2⟩ w
    exact ⟨fun i j => h1 i j w, fun i j => h2 i j w⟩
  · intro hw
    exact ⟨fun i j w => (hw w).1 i j, fun i j w => (hw w).2 i j⟩

omit v in
theorem eventually_finComponent_mem (h : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) :
    ∀ᶠ w in cofinite, finComponent (𝓞 L) L w h ∈ localIntegralSet L w := by
  have h1 : ∀ i j : Fin 2, ∀ᶠ w : HeightOneSpectrum (𝓞 L) in cofinite,
      ((h : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 L) L)) i j) w ∈ w.adicCompletionIntegers L :=
    fun i j => ((h : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 L) L)) i j).2
  have h2 : ∀ i j : Fin 2, ∀ᶠ w : HeightOneSpectrum (𝓞 L) in cofinite,
      (((h⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 L) L)) i j) w ∈
        w.adicCompletionIntegers L :=
    fun i j => (((h⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 L) L)) i j).2
  have h1' : ∀ᶠ w : HeightOneSpectrum (𝓞 L) in cofinite, ∀ i j : Fin 2,
      ((h : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 L) L)) i j) w ∈ w.adicCompletionIntegers L :=
    eventually_all.2 fun i => eventually_all.2 fun j => h1 i j
  have h2' : ∀ᶠ w : HeightOneSpectrum (𝓞 L) in cofinite, ∀ i j : Fin 2,
      (((h⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 L) L)) i j) w ∈
        w.adicCompletionIntegers L :=
    eventually_all.2 fun i => eventually_all.2 fun j => h2 i j
  filter_upwards [h1', h2'] with w hw1 hw2
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [finComponent_apply]
    exact hw1 i j
  · rw [← map_inv, finComponent_apply]
    exact hw2 i j

omit v in
theorem finite_setOf_tensorPlace_not_mem (x : Gt K L) :
    {v | tensorPlace K L v x ∉ semiLocalIntegralSet K L v}.Finite := by
  have hfin := Filter.eventually_cofinite.1
    (eventually_finComponent_mem (glFin (𝓞 L) L (baseChangeGLEquiv K L x)))
  refine (hfin.image (HeightOneSpectrum.under (𝓞 K))).subset fun v hv => ?_
  rw [Set.mem_setOf_eq, ← semiLocalComponent_glFin_baseChangeGL, ← baseChangeGLEquiv_apply,
    semiLocalComponent_mem_iff, not_forall] at hv
  obtain ⟨w, hw⟩ := hv
  exact ⟨w.1, hw, w.2⟩

end Cofinite

def semiLocalSubring (v : HeightOneSpectrum (𝓞 K)) : Subring (SL K L v) :=
  (HeightOneSpectrum.tensorAdicCompletionIntegersTo K L (𝓞 L) v).toRingHom.range

theorem coe_semiLocalSubring (v : HeightOneSpectrum (𝓞 K)) :
    (semiLocalSubring (K := K) (L := L) v : Set (SL K L v)) = semiLocalIntegers K L v := by
  ext x
  simp only [semiLocalSubring, RingHom.coe_range, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    semiLocalIntegers, Set.mem_range]

theorem mul_mem_semiLocalIntegralSet (v : HeightOneSpectrum (𝓞 K)) {g h : Gsl K L v}
    (hg : g ∈ semiLocalIntegralSet K L v) (hh : h ∈ semiLocalIntegralSet K L v) :
    g * h ∈ semiLocalIntegralSet K L v := by
  have h' := mul_mem_integralUnitsSet (semiLocalSubring (K := K) (L := L) v)
    (by rw [coe_semiLocalSubring]; exact hg) (by rw [coe_semiLocalSubring]; exact hh)
  rwa [coe_semiLocalSubring] at h'

theorem inv_mem_semiLocalIntegralSet (v : HeightOneSpectrum (𝓞 K)) {g : Gsl K L v}
    (hg : g ∈ semiLocalIntegralSet K L v) : g⁻¹ ∈ semiLocalIntegralSet K L v :=
  inv_mem_integralUnitsSet _ hg

theorem conj_mem_semiLocalIntegralSet_iff (v : HeightOneSpectrum (𝓞 K)) {yv t : Gsl K L v}
    (hy : yv ∈ semiLocalIntegralSet K L v) :
    yv * t * yv⁻¹ ∈ semiLocalIntegralSet K L v ↔ t ∈ semiLocalIntegralSet K L v := by
  constructor
  · intro h
    have h' := mul_mem_semiLocalIntegralSet v (mul_mem_semiLocalIntegralSet v (inv_mem_semiLocalIntegralSet v hy) h) hy
    simpa [mul_assoc] using h'
  · intro h
    exact mul_mem_semiLocalIntegralSet v (mul_mem_semiLocalIntegralSet v hy h) (inv_mem_semiLocalIntegralSet v hy)

section GlobalTransport

variable (σ : L ≃ₐ[K] L) (γ : Gad K) (δ y : Gt K L)

abbrev Tad : Subgroup (Gad K) := Subgroup.centralizer ({γ} : Set (Gad K))
abbrev Ttw : Subgroup (Gt K L) := twistedCentralizer K L (AdeleRing (𝓞 K) K) σ δ

theorem eq_map_of_coupled (e : Tad γ ≃ₜ* Ttw σ δ)
    (he : ∀ s : Tad γ, ((e s : Ttw σ δ) : Gt K L) = y * toTensorGL K L _ (s : Gad K) * y⁻¹)
    (τ : Measure (Tad γ)) (τ' : Measure (Ttw σ δ)) (hC : Coupled K L (AdeleRing (𝓞 K) K) σ γ δ y τ τ') :
    τ' = Measure.map e τ := by
  set j : Ttw σ δ → Gt K L := fun t => y⁻¹ * (t : Gt K L) * y with hj_def
  have hCj : Measure.map j τ' = Measure.map (fun s : Tad γ => toTensorGL K L _ (s : Gad K)) τ := hC
  have hcomp : (fun s : Tad γ => toTensorGL K L _ (s : Gad K)) = j ∘ e := by
    funext s
    simp only [Function.comp_apply, hj_def, he]
    group

  have hhomeo := Homeomorph.isClosedEmbedding ((Homeomorph.mulLeft y⁻¹).trans (Homeomorph.mulRight y))
  have hjce' := hhomeo.comp (IsClosedEmbedding.subtypeVal (isClosed_twistedCentralizer K L _ σ δ))
  have hjeq : j = ((Homeomorph.mulLeft y⁻¹).trans (Homeomorph.mulRight y)) ∘ (Subtype.val : Ttw σ δ → Gt K L) := by
    funext t
    rfl
  have hjce : IsClosedEmbedding j := hjeq ▸ hjce'
  have hjm : MeasurableEmbedding j := hjce.measurableEmbedding
  have hem : Measurable e := e.continuous.measurable
  rw [hcomp, ← Measure.map_map hjm.measurable hem] at hCj
  ext A hA
  rw [← Set.preimage_image_eq A hjm.injective, ← hjm.map_apply, hCj, hjm.map_apply]

end GlobalTransport

section LocalFactors

theorem exists_map_eq_smul {T T' : Type*} [Group T] [TopologicalSpace T] [IsTopologicalGroup T]
    [MeasurableSpace T] [BorelSpace T] [Group T'] [TopologicalSpace T'] [IsTopologicalGroup T']
    [MeasurableSpace T'] [BorelSpace T'] [LocallyCompactSpace T'] [SecondCountableTopology T']
    (e : T ≃ₜ* T') (μ : Measure T) [IsHaarMeasure μ] (μ' : Measure T') [IsHaarMeasure μ'] :
    ∃ a : ℝ≥0, a ≠ 0 ∧ Measure.map e μ = a • μ' := by
  haveI : IsHaarMeasure (Measure.map e μ) := e.isHaarMeasure_map μ
  refine ⟨haarScalarFactor (Measure.map e μ) μ', (haarScalarFactor_pos_of_isHaarMeasure _ _).ne', ?_⟩
  exact isMulLeftInvariant_eq_smul (Measure.map e μ) μ'

end LocalFactors

theorem prod_indicator_eq {ι : Type*} (S : Finset ι) (P : ι → Prop) :
    (∏ i ∈ S, (if P i then (1 : ℂ) else 0)) = if ∀ i ∈ S, P i then 1 else 0 := by
  classical
  split_ifs with h
  · exact Finset.prod_eq_one fun i hi => if_pos (h i hi)
  · push Not at h
    obtain ⟨i, hi, hPi⟩ := h
    exact Finset.prod_eq_zero hi (if_neg hPi)

section Main

variable [IsGalois K L] (σ : L ≃ₐ[K] L) (hσ : ∀ θ : L ≃ₐ[K] L, θ ∈ Subgroup.zpowers σ)
  (γ : Gad K) (hγ : IsRegularSemisimple γ) (δ y : Gt K L)
  (hy : IsNormConjugator K L (AdeleRing (𝓞 K) K) σ γ δ y)

abbrev cpt (v : HeightOneSpectrum (𝓞 K)) (g : Gad K) : Gv (K := K) v := finComponent (𝓞 K) K v (glFin (𝓞 K) K g)

abbrev Tv (v : HeightOneSpectrum (𝓞 K)) : Subgroup (Gv (K := K) v) := localCentralizer K v (cpt v γ)
abbrev Ta : Subgroup (Garch K) := Subgroup.centralizer ({glArch (𝓞 K) K γ} : Set (Garch K))
abbrev Tv' (v : HeightOneSpectrum (𝓞 K)) : Subgroup (Gsl K L v) :=
  twistedCentralizer K L (v.adicCompletion K) σ (tensorPlace K L v δ)
abbrev Ta' : Subgroup (Ht K L) := twistedCentralizer K L (InfiniteAdeleRing K) σ (tensorArch K L δ)

scoped instance instLocallyCompactTv' (v : HeightOneSpectrum (𝓞 K)) : LocallyCompactSpace (Tv' σ δ v) :=
  (isClosed_twistedCentralizer K L _ σ _).locallyCompactSpace
scoped instance instLocallyCompactTa' : LocallyCompactSpace (Ta' σ δ) :=
  (isClosed_twistedCentralizer K L _ σ _).locallyCompactSpace
scoped instance instSecondCountableTv' (v : HeightOneSpectrum (𝓞 K)) : SecondCountableTopology (Tv' σ δ v) :=
  TopologicalSpace.Subtype.secondCountableTopology _
scoped instance instSecondCountableTa' : SecondCountableTopology (Ta' σ δ) :=
  TopologicalSpace.Subtype.secondCountableTopology _

include hσ hγ hy in
theorem exists_iso_v (v : HeightOneSpectrum (𝓞 K)) :
    ∃ e : Tv γ v ≃ₜ* Tv' σ δ v, ∀ s : Tv γ v,
      ((e s : Tv' σ δ v) : Gsl K L v) = tensorPlace K L v y * toTensorGL K L _ (s : Gv v) * (tensorPlace K L v y)⁻¹ :=
  AutomorphicForm.exists_continuousMulEquiv_centralizer_twistedCentralizer_of_isNormConjugator K L σ hσ
    (v.adicCompletion K) (cpt v γ) (isRegularSemisimple_map _ (isRegularSemisimple_map _ hγ)) _ _
    (isNormConjugator_map σ (tensorPlace K L v) ((finComponent (𝓞 K) K v).comp (glFin (𝓞 K) K))
      (tensorPlace_sigmaGL K L σ v) (tensorPlace_toTensorGL K L v) hy)

include hσ hγ hy in
theorem exists_iso_a :
    ∃ e : Ta γ ≃ₜ* Ta' σ δ, ∀ s : Ta γ,
      ((e s : Ta' σ δ) : Ht K L) = tensorArch K L y * toTensorGL K L _ (s : Garch K) * (tensorArch K L y)⁻¹ :=
  AutomorphicForm.exists_continuousMulEquiv_centralizer_twistedCentralizer_of_isNormConjugator K L σ hσ
    (InfiniteAdeleRing K) (glArch (𝓞 K) K γ) (isRegularSemisimple_map _ hγ) _ _
    (isNormConjugator_map σ (tensorArch K L) (glArch (𝓞 K) K) (tensorArch_sigmaGL K L σ) (tensorArch_toTensorGL K L) hy)

include hσ hγ hy in
theorem exists_iso :
    ∃ e : Tad γ ≃ₜ* Ttw σ δ, ∀ s : Tad γ,
      ((e s : Ttw σ δ) : Gt K L) = y * toTensorGL K L _ (s : Gad K) * y⁻¹ :=
  AutomorphicForm.exists_continuousMulEquiv_centralizer_twistedCentralizer_of_isNormConjugator K L σ hσ
    (AdeleRing (𝓞 K) K) γ hγ δ y hy

omit [IsGalois K L] in

theorem coupled_v (v : HeightOneSpectrum (𝓞 K)) (e : Tv γ v ≃ₜ* Tv' σ δ v)
    (he : ∀ s : Tv γ v,
      ((e s : Tv' σ δ v) : Gsl K L v) = tensorPlace K L v y * toTensorGL K L _ (s : Gv v) * (tensorPlace K L v y)⁻¹)
    (τv : Measure (Tv γ v)) (τ'' : Measure (Tv' σ δ v)) (h : Measure.map e τv = τ'') :
    Coupled K L (v.adicCompletion K) σ (cpt v γ) (tensorPlace K L v δ) (tensorPlace K L v y) τv τ'' := by
  have hjm : Measurable (fun t : Tv' σ δ v => (tensorPlace K L v y)⁻¹ * (t : Gsl K L v) * tensorPlace K L v y) :=
    ((continuous_const.mul continuous_subtype_val).mul continuous_const).measurable
  show Measure.map (fun t : Tv' σ δ v => (tensorPlace K L v y)⁻¹ * (t : Gsl K L v) * tensorPlace K L v y) τ'' =
    Measure.map (fun s : Tv γ v => toTensorGL K L _ (s : Gv v)) τv
  have hem : Measurable (e : Tv γ v → Tv' σ δ v) := e.continuous.measurable
  rw [← h, Measure.map_map hjm hem]
  congr 1
  funext s
  simp only [Function.comp_apply, he]
  group

omit [IsGalois K L] in

theorem coupled_a (e : Ta γ ≃ₜ* Ta' σ δ)
    (he : ∀ s : Ta γ,
      ((e s : Ta' σ δ) : Ht K L) = tensorArch K L y * toTensorGL K L _ (s : Garch K) * (tensorArch K L y)⁻¹)
    (τv : Measure (Ta γ)) (τ'' : Measure (Ta' σ δ)) (h : Measure.map e τv = τ'') :
    Coupled K L (InfiniteAdeleRing K) σ (glArch (𝓞 K) K γ) (tensorArch K L δ) (tensorArch K L y) τv τ'' := by
  have hjm : Measurable (fun t : Ta' σ δ => (tensorArch K L y)⁻¹ * (t : Ht K L) * tensorArch K L y) :=
    ((continuous_const.mul continuous_subtype_val).mul continuous_const).measurable
  show Measure.map (fun t : Ta' σ δ => (tensorArch K L y)⁻¹ * (t : Ht K L) * tensorArch K L y) τ'' =
    Measure.map (fun s : Ta γ => toTensorGL K L _ (s : Garch K)) τv
  have hem : Measurable (e : Ta γ → Ta' σ δ) := e.continuous.measurable
  rw [← h, Measure.map_map hjm hem]
  congr 1
  funext s
  simp only [Function.comp_apply, he]
  group

def boxL (Ca' : Set (Ht K L)) : Set (Gt K L) :=
  {x | tensorArch K L x ∈ Ca' ∧ ∀ v : HeightOneSpectrum (𝓞 K), tensorPlace K L v x ∈ semiLocalIntegralSet K L v}

def W' (Ca' : Set (Ht K L)) : Gt K L → ℂ := fun x => if x ∈ boxL (K := K) (L := L) Ca' then 1 else 0

def W (Ca' : Set (Ht K L)) : Gad K → ℂ := fun g => W' Ca' (y * toTensorGL K L _ g * y⁻¹)

def Wa (Ca' : Set (Ht K L)) : Garch K → ℂ := fun g =>
  if tensorArch K L y * toTensorGL K L _ g * (tensorArch K L y)⁻¹ ∈ Ca' then 1 else 0

def WS (v : HeightOneSpectrum (𝓞 K)) : Gv (K := K) v → ℂ := fun g =>
  if tensorPlace K L v y * toTensorGL K L _ g * (tensorPlace K L v y)⁻¹ ∈ semiLocalIntegralSet K L v then 1 else 0

omit [IsGalois K L] in
theorem tensorPlace_conj (v : HeightOneSpectrum (𝓞 K)) (g : Gad K) :
    tensorPlace K L v (y * toTensorGL K L _ g * y⁻¹) =
      tensorPlace K L v y * toTensorGL K L _ (cpt v g) * (tensorPlace K L v y)⁻¹ := by
  rw [map_mul, map_mul, map_inv, tensorPlace_toTensorGL]

omit [IsGalois K L] in
theorem tensorArch_conj (g : Gad K) :
    tensorArch K L (y * toTensorGL K L _ g * y⁻¹) =
      tensorArch K L y * toTensorGL K L _ (glArch (𝓞 K) K g) * (tensorArch K L y)⁻¹ := by
  rw [map_mul, map_mul, map_inv, tensorArch_toTensorGL]

def S₀ : Finset (HeightOneSpectrum (𝓞 K)) := (finite_setOf_tensorPlace_not_mem (K := K) (L := L) y).toFinset

omit [IsGalois K L] in
theorem mem_of_not_mem_S₀ {v : HeightOneSpectrum (𝓞 K)} (hv : v ∉ S₀ y) :
    tensorPlace K L v y ∈ semiLocalIntegralSet K L v := by
  by_contra h
  exact hv ((Set.Finite.mem_toFinset _).2 h)

omit [IsGalois K L] in

theorem WS_cond_iff {v : HeightOneSpectrum (𝓞 K)} (hv : v ∉ S₀ y) (g : Gv (K := K) v) :
    tensorPlace K L v y * toTensorGL K L _ g * (tensorPlace K L v y)⁻¹ ∈ semiLocalIntegralSet K L v ↔
      g ∈ localIntegralSet K v := by
  rw [conj_mem_semiLocalIntegralSet_iff v (mem_of_not_mem_S₀ y hv), toTensorGL_mem_semiLocalIntegralSet_iff]

omit [IsGalois K L] in

theorem W_shape (Ca' : Set (Ht K L)) {S : Finset (HeightOneSpectrum (𝓞 K))} (hS : S₀ y ⊆ S) (g : Gad K)
    (hg : ∀ v ∉ S, cpt v g ∈ localIntegralSet K v) :
    W y Ca' g = Wa y Ca' (glArch (𝓞 K) K g) * ∏ v ∈ S, WS y v (cpt v g) := by
  simp only [W, W', Wa, WS, boxL, Set.mem_setOf_eq, tensorArch_conj, tensorPlace_conj]
  rw [prod_indicator_eq S]
  by_cases ha : tensorArch K L y * toTensorGL K L _ (glArch (𝓞 K) K g) * (tensorArch K L y)⁻¹ ∈ Ca'
  · simp only [ha, true_and, if_true, one_mul]
    congr 1
    apply propext
    constructor
    · exact fun h v _ => h v
    · intro h v
      by_cases hv : v ∈ S
      · exact h v hv
      · exact (WS_cond_iff y (fun h0 => hv (hS h0)) _).2 (hg v hv)
  · simp only [ha, false_and, if_false, zero_mul]

omit [IsGalois K L] in

theorem W_vanish (Ca' : Set (Ht K L)) {S : Finset (HeightOneSpectrum (𝓞 K))} (hS : S₀ y ⊆ S) (g : Gad K)
    (hg : ∃ v ∉ S, cpt v g ∉ localIntegralSet K v) : W y Ca' g = 0 := by
  obtain ⟨v, hv, hgv⟩ := hg
  simp only [W, W', boxL, Set.mem_setOf_eq, tensorPlace_conj]
  rw [if_neg]
  rintro ⟨-, h⟩
  exact hgv ((WS_cond_iff y (fun h0 => hv (hS h0)) _).1 (h v))

omit [IsGalois K L] in

theorem W'_shape (Ca' : Set (Ht K L)) (S : Finset (HeightOneSpectrum (𝓞 K))) (x : Gt K L)
    (hx : ∀ v ∉ S, tensorPlace K L v x ∈ semiLocalIntegralSet K L v) :
    W' Ca' x = (if tensorArch K L x ∈ Ca' then (1 : ℂ) else 0) *
      ∏ v ∈ S, (if tensorPlace K L v x ∈ semiLocalIntegralSet K L v then (1 : ℂ) else 0) := by
  simp only [W', boxL, Set.mem_setOf_eq]
  rw [prod_indicator_eq S]
  by_cases ha : tensorArch K L x ∈ Ca'
  · simp only [ha, true_and, if_true, one_mul]
    congr 1
    apply propext
    constructor
    · exact fun h v _ => h v
    · intro h v
      by_cases hv : v ∈ S
      · exact h v hv
      · exact hx v hv
  · simp only [ha, false_and, if_false, zero_mul]

omit [IsGalois K L] in
theorem W'_vanish (Ca' : Set (Ht K L)) (S : Finset (HeightOneSpectrum (𝓞 K))) (x : Gt K L)
    (hx : ∃ v ∉ S, tensorPlace K L v x ∉ semiLocalIntegralSet K L v) : W' Ca' x = 0 := by
  obtain ⟨v, -, hxv⟩ := hx
  simp only [W', boxL, Set.mem_setOf_eq]
  rw [if_neg]
  rintro ⟨-, h⟩
  exact hxv (h v)

theorem aestronglyMeasurable_ite {X : Type*} [MeasurableSpace X] {P : X → Prop} (hP : MeasurableSet {x | P x})
    (μ : Measure X) : AEStronglyMeasurable (fun x => if P x then (1 : ℂ) else 0) μ := by
  have : (fun x => if P x then (1 : ℂ) else 0) = {x | P x}.indicator fun _ => (1 : ℂ) := by
    funext x; simp only [Set.indicator_apply, Set.mem_setOf_eq]
  rw [this]
  exact (aestronglyMeasurable_const.indicator hP)

theorem integral_ite {X : Type*} [MeasurableSpace X] {P : X → Prop} (hP : MeasurableSet {x | P x})
    (μ : Measure X) : ∫ x, (if P x then (1 : ℂ) else 0) ∂μ = (μ.real {x | P x} : ℂ) := by
  have : (fun x => if P x then (1 : ℂ) else 0) = {x | P x}.indicator fun _ => (1 : ℂ) := by
    funext x; simp only [Set.indicator_apply, Set.mem_setOf_eq]
  rw [this, integral_indicator_const _ hP, Complex.real_smul, mul_one]

omit [IsGalois K L] in

theorem eval_L (τ' : Measure (Ttw σ δ)) (τa' : Measure (Ta' σ δ))
    (τf' : ∀ v : HeightOneSpectrum (𝓞 K), Measure (Tv' σ δ v))
    (hτf1' : ∀ v, τf' v (Subtype.val ⁻¹' semiLocalIntegralSet K L v) = 1)
    (cT' : ℝ)
    (hT' : ∀ (S : Finset (HeightOneSpectrum (𝓞 K))) (W : Gt K L → ℂ) (Wa : Ht K L → ℂ)
        (WS : ∀ v : HeightOneSpectrum (𝓞 K), Gsl K L v → ℂ),
        AEStronglyMeasurable (fun t : Ta' σ δ => Wa t) τa' →
        (∀ v ∈ S, AEStronglyMeasurable (fun t : Tv' σ δ v => WS v t) (τf' v)) →
        (∀ t : Ttw σ δ, (∀ v ∉ S, tensorPlace K L v (t : Gt K L) ∈ semiLocalIntegralSet K L v) →
            W t = Wa (tensorArch K L (t : Gt K L)) * ∏ v ∈ S, WS v (tensorPlace K L v (t : Gt K L))) →
        (∀ t : Ttw σ δ, (∃ v ∉ S, tensorPlace K L v (t : Gt K L) ∉ semiLocalIntegralSet K L v) → W t = 0) →
          ∫ t, W t ∂τ' = cT' * (∫ t, Wa t ∂τa') * ∏ v ∈ S, ∫ t, WS v t ∂(τf' v))
    (S : Finset (HeightOneSpectrum (𝓞 K))) (k : Set (Ta' σ δ)) (hk : IsCompact k) :
    ∫ t : Ttw σ δ, W' (Subtype.val '' k) t ∂τ' = cT' * (τa'.real k : ℂ) := by
  have hCa'cl : IsClosed (Subtype.val '' k : Set (Ht K L)) := (hk.image continuous_subtype_val).isClosed
  have hpre : Subtype.val ⁻¹' (Subtype.val '' k : Set (Ht K L)) = k := Set.preimage_image_eq _ Subtype.val_injective
  have hL := hT' S (W' (Subtype.val '' k)) (fun g => if g ∈ (Subtype.val '' k : Set (Ht K L)) then (1 : ℂ) else 0)
    (fun v g => if g ∈ semiLocalIntegralSet K L v then (1 : ℂ) else 0)
    (aestronglyMeasurable_ite (hCa'cl.measurableSet.preimage continuous_subtype_val.measurable) _)
    (fun v _ => aestronglyMeasurable_ite
      ((isOpen_semiLocalIntegralSet K L v).measurableSet.preimage continuous_subtype_val.measurable) _)
    (fun t ht => W'_shape _ S _ ht) (fun t ht => W'_vanish _ S _ ht)
  have hLa : ∫ t : Ta' σ δ, (fun g : Ht K L => if g ∈ (Subtype.val '' k : Set (Ht K L)) then (1 : ℂ) else 0) t ∂τa' =
      (τa'.real k : ℂ) := by
    rw [integral_ite (hCa'cl.measurableSet.preimage continuous_subtype_val.measurable)]
    congr 2
  have hLv : ∀ v ∈ S, ∫ t : Tv' σ δ v,
      (fun g : Gsl K L v => if g ∈ semiLocalIntegralSet K L v then (1 : ℂ) else 0) t ∂(τf' v) = 1 := by
    intro v _
    rw [integral_ite ((isOpen_semiLocalIntegralSet K L v).measurableSet.preimage continuous_subtype_val.measurable)]
    have : (τf' v).real {t : Tv' σ δ v | (t : Gsl K L v) ∈ semiLocalIntegralSet K L v} = 1 := by
      rw [Measure.real, show {t : Tv' σ δ v | (t : Gsl K L v) ∈ semiLocalIntegralSet K L v} =
        Subtype.val ⁻¹' semiLocalIntegralSet K L v from rfl, hτf1' v, ENNReal.toReal_one]
    rw [this, Complex.ofReal_one]
  rw [hLa, Finset.prod_eq_one hLv, mul_one] at hL
  exact hL

omit [IsGalois K L] in

theorem eval_K (τ : Measure (Tad γ)) (τa : Measure (Ta γ))
    (τf : ∀ v : HeightOneSpectrum (𝓞 K), Measure (Tv γ v))
    (cT : ℝ)
    (hT : ∀ (S : Finset (HeightOneSpectrum (𝓞 K))) (W : Gad K → ℂ) (Wa : Garch K → ℂ)
        (WS : ∀ v : HeightOneSpectrum (𝓞 K), Gv (K := K) v → ℂ),
        AEStronglyMeasurable (fun t : Ta γ => Wa t) τa →
        (∀ v ∈ S, AEStronglyMeasurable (fun t : Tv γ v => WS v t) (τf v)) →
        (∀ t : Tad γ, (∀ v ∉ S, cpt v (t : Gad K) ∈ localIntegralSet K v) →
            W t = Wa (glArch (𝓞 K) K (t : Gad K)) * ∏ v ∈ S, WS v (cpt v (t : Gad K))) →
        (∀ t : Tad γ, (∃ v ∉ S, cpt v (t : Gad K) ∉ localIntegralSet K v) → W t = 0) →
          ∫ t, W t ∂τ = cT * (∫ t, Wa t ∂τa) * ∏ v ∈ S, ∫ t, WS v t ∂(τf v))
    (τa' : Measure (Ta' σ δ)) (τf' : ∀ v : HeightOneSpectrum (𝓞 K), Measure (Tv' σ δ v))
    (hτf1' : ∀ v, τf' v (Subtype.val ⁻¹' semiLocalIntegralSet K L v) = 1)
    (ev : ∀ v : HeightOneSpectrum (𝓞 K), Tv γ v ≃ₜ* Tv' σ δ v)
    (hev : ∀ v (s : Tv γ v), ((ev v s : Tv' σ δ v) : Gsl K L v) =
      tensorPlace K L v y * toTensorGL K L _ (s : Gv v) * (tensorPlace K L v y)⁻¹)
    (ea : Ta γ ≃ₜ* Ta' σ δ)
    (hea : ∀ s : Ta γ, ((ea s : Ta' σ δ) : Ht K L) = tensorArch K L y * toTensorGL K L _ (s : Garch K) * (tensorArch K L y)⁻¹)
    (a : HeightOneSpectrum (𝓞 K) → ℝ≥0) (hmapv : ∀ v, Measure.map (ev v) (τf v) = a v • τf' v)
    (b : ℝ≥0) (hmapa : Measure.map ea τa = b • τa')
    (S : Finset (HeightOneSpectrum (𝓞 K))) (hS : S₀ y ⊆ S) (k : Set (Ta' σ δ)) (hk : IsCompact k) :
    ∫ t : Tad γ, W y (Subtype.val '' k) t ∂τ = cT * (b * (τa'.real k : ℂ)) * ∏ v ∈ S, ((a v : ℝ) : ℂ) := by
  have hCa'cl : IsClosed (Subtype.val '' k : Set (Ht K L)) := (hk.image continuous_subtype_val).isClosed
  have hpre : Subtype.val ⁻¹' (Subtype.val '' k : Set (Ht K L)) = k := Set.preimage_image_eq _ Subtype.val_injective
  have hca : Continuous fun g : Garch K => tensorArch K L y * toTensorGL K L _ g * (tensorArch K L y)⁻¹ :=
    (continuous_const.mul (continuous_toTensorGL K L _)).mul continuous_const
  have hcv : ∀ v : HeightOneSpectrum (𝓞 K), Continuous fun g : Gv (K := K) v =>
      tensorPlace K L v y * toTensorGL K L _ g * (tensorPlace K L v y)⁻¹ := fun v =>
    (continuous_const.mul (continuous_toTensorGL K L _)).mul continuous_const
  have hmeasa : MeasurableSet {t : Ta γ | tensorArch K L y * toTensorGL K L _ (t : Garch K) * (tensorArch K L y)⁻¹ ∈
      (Subtype.val '' k : Set (Ht K L))} :=
    (hCa'cl.preimage hca).measurableSet.preimage continuous_subtype_val.measurable
  have hmeasv : ∀ v : HeightOneSpectrum (𝓞 K), MeasurableSet {t : Tv γ v |
      tensorPlace K L v y * toTensorGL K L _ (t : Gv v) * (tensorPlace K L v y)⁻¹ ∈ semiLocalIntegralSet K L v} :=
    fun v => ((isOpen_semiLocalIntegralSet K L v).preimage (hcv v)).measurableSet.preimage continuous_subtype_val.measurable
  have hK := hT S (W y (Subtype.val '' k)) (Wa y (Subtype.val '' k)) (WS y)
    (aestronglyMeasurable_ite hmeasa _) (fun v _ => aestronglyMeasurable_ite (hmeasv v) _)
    (fun t ht => W_shape y _ hS _ ht) (fun t ht => W_vanish y _ hS _ ht)

  have hKa : ∫ t : Ta γ, Wa y (Subtype.val '' k) t ∂τa = b * (τa'.real k : ℂ) := by
    show ∫ t : Ta γ, (if tensorArch K L y * toTensorGL K L _ (t : Garch K) * (tensorArch K L y)⁻¹ ∈
      (Subtype.val '' k : Set (Ht K L)) then (1 : ℂ) else 0) ∂τa = _
    rw [integral_ite hmeasa]
    have hset : {t : Ta γ | tensorArch K L y * toTensorGL K L _ (t : Garch K) * (tensorArch K L y)⁻¹ ∈
        (Subtype.val '' k : Set (Ht K L))} = ea ⁻¹' (Subtype.val ⁻¹' (Subtype.val '' k : Set (Ht K L))) := by
      ext t
      simp only [Set.mem_setOf_eq, Set.mem_preimage, hea]
    have hema : Measurable (ea : Ta γ → Ta' σ δ) := ea.continuous.measurable
    rw [hset, Measure.real, ← Measure.map_apply hema
      (hCa'cl.measurableSet.preimage continuous_subtype_val.measurable), hmapa, hpre, Measure.smul_apply,
      ENNReal.toReal_smul, NNReal.smul_def, smul_eq_mul, Complex.ofReal_mul, Measure.real]

  have hKv : ∀ v ∈ S, ∫ t : Tv γ v, WS y v t ∂(τf v) = ((a v : ℝ) : ℂ) := by
    intro v _
    show ∫ t : Tv γ v, (if tensorPlace K L v y * toTensorGL K L _ (t : Gv v) * (tensorPlace K L v y)⁻¹ ∈
      semiLocalIntegralSet K L v then (1 : ℂ) else 0) ∂(τf v) = _
    rw [integral_ite (hmeasv v)]
    have hset : {t : Tv γ v | tensorPlace K L v y * toTensorGL K L _ (t : Gv v) * (tensorPlace K L v y)⁻¹ ∈
        semiLocalIntegralSet K L v} = ev v ⁻¹' (Subtype.val ⁻¹' semiLocalIntegralSet K L v) := by
      ext t
      simp only [Set.mem_setOf_eq, Set.mem_preimage, hev]
    have hemv : Measurable (ev v : Tv γ v → Tv' σ δ v) := (ev v).continuous.measurable
    rw [hset, Measure.real, ← Measure.map_apply hemv
      ((isOpen_semiLocalIntegralSet K L v).measurableSet.preimage continuous_subtype_val.measurable), hmapv v,
      Measure.smul_apply, hτf1' v]
    simp
  rw [hKa, Finset.prod_congr rfl hKv] at hK
  exact hK

include hσ hγ hy in
theorem main
    (τ : Measure (Tad γ)) (τa : Measure (Ta γ)) [IsHaarMeasure τa]
    (τf : ∀ v : HeightOneSpectrum (𝓞 K), Measure (Tv γ v)) (hτf : ∀ v, IsHaarMeasure (τf v))
    (cT : ℝ)
    (hT : ∀ (S : Finset (HeightOneSpectrum (𝓞 K))) (W : Gad K → ℂ) (Wa : Garch K → ℂ)
        (WS : ∀ v : HeightOneSpectrum (𝓞 K), Gv (K := K) v → ℂ),
        AEStronglyMeasurable (fun t : Ta γ => Wa t) τa →
        (∀ v ∈ S, AEStronglyMeasurable (fun t : Tv γ v => WS v t) (τf v)) →
        (∀ t : Tad γ, (∀ v ∉ S, cpt v (t : Gad K) ∈ localIntegralSet K v) →
            W t = Wa (glArch (𝓞 K) K (t : Gad K)) * ∏ v ∈ S, WS v (cpt v (t : Gad K))) →
        (∀ t : Tad γ, (∃ v ∉ S, cpt v (t : Gad K) ∉ localIntegralSet K v) → W t = 0) →
          ∫ t, W t ∂τ = cT * (∫ t, Wa t ∂τa) * ∏ v ∈ S, ∫ t, WS v t ∂(τf v))
    (τ' : Measure (Ttw σ δ)) (τa' : Measure (Ta' σ δ)) [IsHaarMeasure τa']
    (τf' : ∀ v : HeightOneSpectrum (𝓞 K), Measure (Tv' σ δ v)) (hτf' : ∀ v, IsHaarMeasure (τf' v))
    (hτf1' : ∀ v, τf' v (Subtype.val ⁻¹' semiLocalIntegralSet K L v) = 1)
    (cT' : ℝ)
    (hT' : ∀ (S : Finset (HeightOneSpectrum (𝓞 K))) (W : Gt K L → ℂ) (Wa : Ht K L → ℂ)
        (WS : ∀ v : HeightOneSpectrum (𝓞 K), Gsl K L v → ℂ),
        AEStronglyMeasurable (fun t : Ta' σ δ => Wa t) τa' →
        (∀ v ∈ S, AEStronglyMeasurable (fun t : Tv' σ δ v => WS v t) (τf' v)) →
        (∀ t : Ttw σ δ, (∀ v ∉ S, tensorPlace K L v (t : Gt K L) ∈ semiLocalIntegralSet K L v) →
            W t = Wa (tensorArch K L (t : Gt K L)) * ∏ v ∈ S, WS v (tensorPlace K L v (t : Gt K L))) →
        (∀ t : Ttw σ δ, (∃ v ∉ S, tensorPlace K L v (t : Gt K L) ∉ semiLocalIntegralSet K L v) → W t = 0) →
          ∫ t, W t ∂τ' = cT' * (∫ t, Wa t ∂τa') * ∏ v ∈ S, ∫ t, WS v t ∂(τf' v))
    (hC : Coupled K L (AdeleRing (𝓞 K) K) σ γ δ y τ τ') :
    ∃ (a : HeightOneSpectrum (𝓞 K) → ℝ≥0) (b : ℝ≥0), (∀ v, a v ≠ 0) ∧ b ≠ 0 ∧
      (∀ v : HeightOneSpectrum (𝓞 K), Coupled K L (v.adicCompletion K) σ (cpt v γ)
        (tensorPlace K L v δ) (tensorPlace K L v y) (τf v) (a v • τf' v)) ∧
      Coupled K L (InfiniteAdeleRing K) σ (glArch (𝓞 K) K γ) (tensorArch K L δ) (tensorArch K L y) τa (b • τa') ∧
      ∃ S₀ : Finset (HeightOneSpectrum (𝓞 K)), ∀ S : Finset (HeightOneSpectrum (𝓞 K)), S₀ ⊆ S →
        cT' = cT * b * ∏ v ∈ S, (a v : ℝ) := by
  haveI := hτf
  haveI := hτf'

  have hev := exists_iso_v σ hσ γ hγ δ y hy
  choose ev hev using hev
  obtain ⟨ea, hea⟩ := exists_iso_a σ hσ γ hγ δ y hy
  obtain ⟨e, he⟩ := exists_iso σ hσ γ hγ δ y hy

  have hav : ∀ v, ∃ a : ℝ≥0, a ≠ 0 ∧ Measure.map (ev v) (τf v) = a • τf' v :=
    fun v => exists_map_eq_smul (ev v) (τf v) (τf' v)
  choose a ha hmapv using hav
  obtain ⟨b, hb, hmapa⟩ := exists_map_eq_smul ea τa τa'
  refine ⟨a, b, ha, hb, fun v => coupled_v σ γ δ y v (ev v) (hev v) (τf v) _ (hmapv v),
    coupled_a σ γ δ y ea hea τa _ hmapa, S₀ y, fun S hS => ?_⟩

  have hτ'e : τ' = Measure.map e τ := eq_map_of_coupled σ γ δ y e he τ τ' hC

  obtain ⟨k⟩ : Nonempty (PositiveCompacts (Ta' σ δ)) := inferInstance
  have hkpos : τa'.real (k : Set (Ta' σ δ)) ≠ 0 := by
    rw [Measure.real, ENNReal.toReal_ne_zero]
    exact ⟨(measure_pos_of_nonempty_interior τa' k.interior_nonempty).ne', k.isCompact.measure_lt_top.ne⟩
  have hL := eval_L σ δ τ' τa' τf' hτf1' cT' hT' S (k : Set (Ta' σ δ)) k.isCompact
  have hK := eval_K σ γ δ y τ τa τf cT hT τa' τf' hτf1' ev hev ea hea a hmapv b hmapa S hS (k : Set (Ta' σ δ)) k.isCompact

  have hKL : ∫ t : Tad γ, W y (Subtype.val '' (k : Set (Ta' σ δ))) t ∂τ =
      ∫ t : Ttw σ δ, W' (Subtype.val '' (k : Set (Ta' σ δ))) t ∂τ' := by
    rw [hτ'e]
    have hme : MeasurableEmbedding (e : Tad γ → Ttw σ δ) := e.toHomeomorph.measurableEmbedding
    rw [hme.integral_map]
    congr 1
    funext s
    simp only [W, he]
  rw [hKL, hL] at hK

  have hm : ((τa'.real (k : Set (Ta' σ δ)) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hkpos
  have hK' : (cT' : ℂ) = cT * b * ∏ v ∈ S, ((a v : ℝ) : ℂ) := by
    have h2 : (cT' : ℂ) * (τa'.real (k : Set (Ta' σ δ)) : ℂ) =
        (cT * b * ∏ v ∈ S, ((a v : ℝ) : ℂ)) * (τa'.real (k : Set (Ta' σ δ)) : ℂ) := by
      rw [hK]; ring
    exact mul_right_cancel₀ hm h2
  exact_mod_cast hK'

end Main

end AutomorphicForm.CoupledTorusConstants
p2m_reactivate "P2MW.S_AutomorphicForm_exists_coupled_smul_and_eq_mul_prod_of_coupled_adeleRing.AutomorphicForm P2MW.S_AutomorphicForm_exists_coupled_smul_and_eq_mul_prod_of_coupled_adeleRing.AutomorphicForm.CoupledTorusConstants"
p2m_reactivate "P2MW.S_AutomorphicForm_exists_coupled_smul_and_eq_mul_prod_of_coupled_adeleRing.AutomorphicForm"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_coupled_smul_and_eq_mul_prod_of_coupled_adeleRing.AutomorphicForm P2MW.S_AutomorphicForm_exists_coupled_smul_and_eq_mul_prod_of_coupled_adeleRing.AutomorphicForm.CoupledTorusConstants"

open _root_.AutomorphicForm _root_.P2MW.S_AutomorphicForm_exists_coupled_smul_and_eq_mul_prod_of_coupled_adeleRing.AutomorphicForm AutomorphicForm.CoupledTorusConstants in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hσ : ∀ θ : L ≃ₐ[K] L, θ ∈ Subgroup.zpowers σ)
    (γ : GL (Fin 2) (AdeleRing (𝓞 K) K)) (hγ : AutomorphicForm.IsRegularSemisimple γ)
    (δ y : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))
    (hy : AutomorphicForm.IsNormConjugator K L (AdeleRing (𝓞 K) K) σ γ δ y)
    (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))))
      (AutomorphicForm.centralizerBorel (AdeleRing (𝓞 K) K) γ))
    (τa : @Measure (Subgroup.centralizer
        ({AdelicLevel.glArch (𝓞 K) K γ} : Set (GL (Fin 2) (InfiniteAdeleRing K))))
      (AutomorphicForm.centralizerBorel (InfiniteAdeleRing K) (AdelicLevel.glArch (𝓞 K) K γ)))
    (hτa : @Measure.IsHaarMeasure _ _ _
      (AutomorphicForm.centralizerBorel (InfiniteAdeleRing K) (AdelicLevel.glArch (𝓞 K) K γ)) τa)
    (τf : ∀ v : HeightOneSpectrum (𝓞 K),
      @Measure (AutomorphicForm.localCentralizer K v
          (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K γ)))
        (AutomorphicForm.localCentralizerBorel K v
          (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K γ))))
    (hτf : ∀ v : HeightOneSpectrum (𝓞 K), @Measure.IsHaarMeasure _ _ _
      (AutomorphicForm.localCentralizerBorel K v
        (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K γ))) (τf v))
    (cT : ℝ)
    (hT : ∀ (S : Finset (HeightOneSpectrum (𝓞 K)))
        (W : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) (Wa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)
        (WS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ),
        AEStronglyMeasurable[AutomorphicForm.centralizerBorel (InfiniteAdeleRing K)
          (AdelicLevel.glArch (𝓞 K) K γ)] (fun t => Wa t) τa →
        (∀ v ∈ S, AEStronglyMeasurable[AutomorphicForm.localCentralizerBorel K v
          (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K γ))] (fun t => WS v t) (τf v)) →
        (∀ t : Subgroup.centralizer ({γ} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))),
          (∀ v ∉ S, AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K t) ∈
              AutomorphicForm.localIntegralSet K v) →
            W t = Wa (AdelicLevel.glArch (𝓞 K) K t) *
              ∏ v ∈ S, WS v (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K t))) →
        (∀ t : Subgroup.centralizer ({γ} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))),
          (∃ v ∉ S, AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K t) ∉
              AutomorphicForm.localIntegralSet K v) → W t = 0) →
          ∫ t, W t ∂τ = cT * (∫ t, Wa t ∂τa) * ∏ v ∈ S, ∫ t, WS v t ∂(τf v))
    (τ' : @Measure (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ δ)
      (AutomorphicForm.twistedCentralizerBorel K L (AdeleRing (𝓞 K) K) σ δ))
    (τa' : @Measure (AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ
        (AutomorphicForm.tensorArch K L δ))
      (AutomorphicForm.twistedCentralizerBorel K L (InfiniteAdeleRing K) σ
        (AutomorphicForm.tensorArch K L δ)))
    (hτa' : @Measure.IsHaarMeasure _ _ _
      (AutomorphicForm.twistedCentralizerBorel K L (InfiniteAdeleRing K) σ
        (AutomorphicForm.tensorArch K L δ)) τa')
    (τf' : ∀ v : HeightOneSpectrum (𝓞 K),
      @Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ
          (AutomorphicForm.tensorPlace K L v δ))
        (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ
          (AutomorphicForm.tensorPlace K L v δ)))
    (hτf' : ∀ v : HeightOneSpectrum (𝓞 K), @Measure.IsHaarMeasure _ _ _
      (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ
        (AutomorphicForm.tensorPlace K L v δ)) (τf' v))
    (hτf1' : ∀ v : HeightOneSpectrum (𝓞 K),
      τf' v (Subtype.val ⁻¹' AutomorphicForm.semiLocalIntegralSet K L v) = 1)
    (cT' : ℝ)
    (hT' : ∀ (S : Finset (HeightOneSpectrum (𝓞 K)))
        (W : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) → ℂ)
        (Wa : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) → ℂ)
        (WS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ),
        AEStronglyMeasurable[AutomorphicForm.twistedCentralizerBorel K L (InfiniteAdeleRing K) σ
          (AutomorphicForm.tensorArch K L δ)] (fun t => Wa t) τa' →
        (∀ v ∈ S, AEStronglyMeasurable[AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ
          (AutomorphicForm.tensorPlace K L v δ)] (fun t => WS v t) (τf' v)) →
        (∀ t : AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ δ,
          (∀ v ∉ S, AutomorphicForm.tensorPlace K L v t ∈ AutomorphicForm.semiLocalIntegralSet K L v) →
            W t = Wa (AutomorphicForm.tensorArch K L t) *
              ∏ v ∈ S, WS v (AutomorphicForm.tensorPlace K L v t)) →
        (∀ t : AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ δ,
          (∃ v ∉ S, AutomorphicForm.tensorPlace K L v t ∉ AutomorphicForm.semiLocalIntegralSet K L v) →
            W t = 0) →
          ∫ t, W t ∂τ' = cT' * (∫ t, Wa t ∂τa') * ∏ v ∈ S, ∫ t, WS v t ∂(τf' v))
    (hC : AutomorphicForm.Coupled K L (AdeleRing (𝓞 K) K) σ γ δ y τ τ') :
    ∃ (a : HeightOneSpectrum (𝓞 K) → ℝ≥0) (b : ℝ≥0), (∀ v, a v ≠ 0) ∧ b ≠ 0 ∧
      (∀ v : HeightOneSpectrum (𝓞 K), AutomorphicForm.Coupled K L (v.adicCompletion K) σ
        (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K γ))
        (AutomorphicForm.tensorPlace K L v δ) (AutomorphicForm.tensorPlace K L v y)
        (τf v) (a v • τf' v)) ∧
      AutomorphicForm.Coupled K L (InfiniteAdeleRing K) σ (AdelicLevel.glArch (𝓞 K) K γ)
        (AutomorphicForm.tensorArch K L δ) (AutomorphicForm.tensorArch K L y) τa (b • τa') ∧
      ∃ S₀ : Finset (HeightOneSpectrum (𝓞 K)), ∀ S : Finset (HeightOneSpectrum (𝓞 K)), S₀ ⊆ S →
        cT' = cT * b * ∏ v ∈ S, (a v : ℝ) := by
  haveI := hτa; haveI := hτa'
  exact main σ hσ γ hγ δ y hy τ τa τf hτf cT hT τ' τa' τf' hτf' hτf1' cT' hT' hC

end S_AutomorphicForm_exists_coupled_smul_and_eq_mul_prod_of_coupled_adeleRing
end P2MW
export P2MW.S_AutomorphicForm_exists_coupled_smul_and_eq_mul_prod_of_coupled_adeleRing (solution)
