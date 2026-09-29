-- Prove2me | solution 1 for AutomorphicForm.isMulRightInvariant_twistedCentralizer_adeleRing_of_normString_eq_toTensorGL_centralScalar_of_finrank_eq_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/30ef1aed-7371-5aaa-a8e1-15705f58d45a

import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Theorems.Thm_AutomorphicForm_exists_integral_twistedCentralizer_eq_mul_integral_mul_prod_integral_of_isHaarMeasure
import Theorems.Thm_AutomorphicForm_exists_finset_mem_nhds_forall_tensorPlace_mem_semiLocalIntegralSet
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology_generalLinearGroup_finTwo
import Theorems.Thm_AutomorphicForm_exists_continuousMulEquiv_centralizer_twistedCentralizer_of_eq_scalar
import Theorems.Thm_Matrix_GeneralLinearGroup_isMulRightInvariant_and_isInvInvariant_of_isHaarMeasure_fin_two
import Theorems.Thm_AutomorphicForm_exists_isCompact_forall_twistedCentralizer_eq_scalar_mul_of_not_isSigmaConjugate_scalar_of_finrank_eq_two
import Theorems.Thm_MeasureTheory_Measure_isMulRightInvariant_of_forall_exists_eq_mul_of_isCompact
import Theorems.Thm_AutomorphicForm_exists_isHaarMeasure_map_eq_smul_withDensity_arch_of_isNormConjugator_scalar_of_finrank_eq_two
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_isMulRightInvariant_twistedCentralizer_adeleRing_of_normString_eq_toTensorGL_centralScalar_of_finrank_eq_two
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply LT.TwistedNorm.sigmaPartialNorm_zero LT.TwistedNorm.GL2.traceDetCompanion_apply_10 LT.TwistedNorm.GL2.traceDetCompanion_apply_00 LT.TwistedNorm.GL2.traceDetCompanion_apply_01 LT.TwistedNorm.GL2.traceDetCompanion_apply_11"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open IsDedekindDomain NumberField MeasureTheory MeasureTheory.Measure Topology TopologicalSpace Set Filter
open NumberField.AdelicLevel TensorProduct
open scoped TensorProduct.RightActions NNReal ENNReal

noncomputable section

namespace AutomorphicForm
p2m_export "AutomorphicForm" "tensorArchHom tensorPlaceHom tensorArch tensorPlace tensorArch_toTensorGL tensorPlace_toTensorGL tensorArchHom_sigmaTensor tensorPlaceHom_sigmaTensor tensorArch_sigmaGL tensorPlace_sigmaGL baseChangeGLEquiv archIdentGLEquiv isTopologicalRing_tensor t2Space_tensor locallyCompactSpace_tensor isTopologicalGroup_tensorGL t2Space_tensorGL locallyCompactSpace_tensorGL glBorelOf centralizerBorel toTensorGL semiLocalHomeomorph semiLocalIntegers semiLocalIntegralSet one_mem_semiLocalIntegralSet isCompact_semiLocalIntegralSet isOpen_semiLocalIntegralSet sigmaTensor sigmaGL normString IsSigmaConjugate IsNormConjugator IsNormOf twistedCentralizer twistedCentralizerBorel integralUnitsSet centralScalar mem_sigmaCentralizer_iff exists_integral_twistedCentralizer_eq_mul_integral_mul_prod_integral_of_isHaarMeasure exists_finset_mem_nhds_forall_tensorPlace_mem_semiLocalIntegralSet exists_continuousMulEquiv_centralizer_twistedCentralizer_of_eq_scalar exists_isCompact_forall_twistedCentralizer_eq_scalar_mul_of_not_isSigmaConjugate_scalar_of_finrank_eq_two exists_isHaarMeasure_map_eq_smul_withDensity_arch_of_isNormConjugator_scalar_of_finrank_eq_two"
namespace TwistedUnimodular
p2m_open "AutomorphicForm"

section LinearAlgebra

variable {R S : Type*} [CommRing R] [CommRing S]

abbrev sc (c : Rˣ) : GL (Fin 2) R := Matrix.GeneralLinearGroup.scalar (Fin 2) c

theorem scalar_mul_comm (c : Rˣ) (g : GL (Fin 2) R) : sc c * g = g * sc c := by
  refine Units.ext ?_
  show Matrix.scalar (Fin 2) (c : R) * (g : Matrix (Fin 2) (Fin 2) R) =
    (g : Matrix (Fin 2) (Fin 2) R) * Matrix.scalar (Fin 2) (c : R)
  exact (Matrix.scalar_commute (c : R) (fun r => Commute.all _ r) _).eq

theorem centralizer_scalar_eq_top (c : Rˣ) :
    Subgroup.centralizer ({sc c} : Set (GL (Fin 2) R)) = ⊤ := by
  rw [Subgroup.centralizer_eq_top_iff_subset, Set.singleton_subset_iff, SetLike.mem_coe, Subgroup.mem_center_iff]
  intro g
  exact (scalar_mul_comm c g).symm

theorem map_scalar (f : R →+* S) (c : Rˣ) :
    Matrix.GeneralLinearGroup.map f (sc c) = sc (Units.map (f : R →* S) c) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  show f ((Matrix.GeneralLinearGroup.scalar (Fin 2) c : Matrix (Fin 2) (Fin 2) R) i j) = _
  simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply]
  split_ifs <;> simp

def centralizerScalarEquiv [TopologicalSpace R] (c : Rˣ) :
    Subgroup.centralizer ({sc c} : Set (GL (Fin 2) R)) ≃ₜ* GL (Fin 2) R :=
  { (MulEquiv.subgroupCongr (centralizer_scalar_eq_top c)).trans Subgroup.topEquiv with
    continuous_toFun := continuous_subtype_val
    continuous_invFun := by
      apply Continuous.subtype_mk continuous_id }

end LinearAlgebra

section Tensor

variable (K L : Type) [Field K] [Field L] [Algebra K L]
  (σ : L ≃ₐ[K] L) (A : Type) [CommRing A] [Algebra K A]

theorem sigmaTensor_includeRight (a : A) :
    sigmaTensor K L A σ ((Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A) a) =
      (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A) a := by
  simp [sigmaTensor]

theorem sigmaGL_toTensorGL (g : GL (Fin 2) A) : sigmaGL K L A σ (toTensorGL K L A g) = toTensorGL K L A g := by
  ext i j
  change sigmaTensor K L A σ ((Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A).toRingHom ((g : Matrix (Fin 2) (Fin 2) A) i j)) =
    (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A).toRingHom ((g : Matrix (Fin 2) (Fin 2) A) i j)
  exact sigmaTensor_includeRight K L σ A _

theorem toTensorGL_scalar (c : Aˣ) :
    toTensorGL K L A (sc c) =
      sc (Units.map ((Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A).toRingHom : A →* L ⊗[K] A) c) :=
  map_scalar _ c

theorem map_normString {B : Type} [CommRing B] [Algebra K B] (f : L ⊗[K] A →+* L ⊗[K] B)
    (hf : ∀ z, f (sigmaTensor K L A σ z) = sigmaTensor K L B σ (f z)) (δ : GL (Fin 2) (L ⊗[K] A)) :
    Matrix.GeneralLinearGroup.map f (normString K L A σ δ) =
      normString K L B σ (Matrix.GeneralLinearGroup.map f δ) := by
  have hcomm : ∀ x : GL (Fin 2) (L ⊗[K] A), Matrix.GeneralLinearGroup.map f (sigmaGL K L A σ x) =
      sigmaGL K L B σ (Matrix.GeneralLinearGroup.map f x) := fun x =>
    Matrix.GeneralLinearGroup.ext fun i j => hf _
  have hiter : ∀ (i : ℕ) (x : GL (Fin 2) (L ⊗[K] A)),
      Matrix.GeneralLinearGroup.map f ((⇑(sigmaGL K L A σ))^[i] x) =
        (⇑(sigmaGL K L B σ))^[i] (Matrix.GeneralLinearGroup.map f x) := by
    intro i
    induction i with
    | zero => intro x; rfl
    | succ i ih => intro x; rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hcomm, ih]
  unfold normString
  rw [map_list_prod, List.map_map]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  exact hiter i δ

end Tensor

section Carriers

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

abbrev Gad (L : Type) [Field L] [NumberField L] : Type := GL (Fin 2) (AdeleRing (𝓞 L) L)

abbrev Gv (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) : Type := GL (Fin 2) (v.adicCompletion K)

abbrev SL (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) : Type :=
  L ⊗[K] v.adicCompletion K

abbrev Gsl (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) : Type :=
  GL (Fin 2) (SL K L v)

abbrev Gt (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] : Type :=
  GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)

abbrev Ht (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] : Type :=
  GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)

section Instances

scoped instance instSecondCountableCompletion (w : InfinitePlace L) : SecondCountableTopology w.Completion :=
  (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology

scoped instance instSecondCountableInfiniteAdeleRing : SecondCountableTopology (InfiniteAdeleRing L) :=
  show SecondCountableTopology ((w : InfinitePlace L) → w.Completion) from inferInstance

scoped instance instSecondCountableMulOpposite (X : Type*) [TopologicalSpace X] [Mul X]
    [SecondCountableTopology X] : SecondCountableTopology Xᵐᵒᵖ :=
  MulOpposite.opHomeomorph.symm.secondCountableTopology

theorem secondCountable_gl (A : Type*) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [SecondCountableTopology A] : SecondCountableTopology (GL (Fin 2) A) := by
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) A) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → A))
  exact Units.isEmbedding_embedProduct.secondCountableTopology

scoped instance instSecondCountableGarchL : SecondCountableTopology (GL (Fin 2) (InfiniteAdeleRing L)) := secondCountable_gl _

scoped instance instSecondCountableGv (v : HeightOneSpectrum (𝓞 K)) : SecondCountableTopology (Gv K v) :=
  secondCountable_gl _
scoped instance instLocallyCompactGv (v : HeightOneSpectrum (𝓞 K)) : LocallyCompactSpace (Gv K v) := by
  haveI : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) :=
    inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → v.adicCompletion K))
  exact Units.isClosedEmbedding_embedProduct.locallyCompactSpace
scoped instance instT2Gv (v : HeightOneSpectrum (𝓞 K)) : T2Space (Gv K v) := by
  haveI : T2Space (Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) := inferInstanceAs (T2Space (Fin 2 → Fin 2 → v.adicCompletion K))
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
scoped instance instLocallyCompactTA : LocallyCompactSpace (L ⊗[K] AdeleRing (𝓞 K) K) := locallyCompactSpace_tensor K L _
scoped instance instIsTopologicalGroupGt : IsTopologicalGroup (Gt K L) := isTopologicalGroup_tensorGL K L _
scoped instance instT2Gt : T2Space (Gt K L) := t2Space_tensorGL K L _
scoped instance instLocallyCompactGt : LocallyCompactSpace (Gt K L) := locallyCompactSpace_tensorGL K L _

scoped instance instSecondCountableGt : SecondCountableTopology (Gt K L) := by
  haveI : SecondCountableTopology (Gad L) := NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo L
  exact (baseChangeGLEquiv K L).toHomeomorph.secondCountableTopology

scoped instance instIsTopologicalRingTI : IsTopologicalRing (L ⊗[K] InfiniteAdeleRing K) :=
  isTopologicalRing_tensor K L _
scoped instance instT2TI : T2Space (L ⊗[K] InfiniteAdeleRing K) := t2Space_tensor K L _
scoped instance instLocallyCompactTI : LocallyCompactSpace (L ⊗[K] InfiniteAdeleRing K) :=
  locallyCompactSpace_tensor K L _
scoped instance instIsTopologicalGroupHt : IsTopologicalGroup (Ht K L) := isTopologicalGroup_tensorGL K L _
scoped instance instLocallyCompactHt : LocallyCompactSpace (Ht K L) := locallyCompactSpace_tensorGL K L _
scoped instance instT2Ht : T2Space (Ht K L) := t2Space_tensorGL K L _
scoped instance instSecondCountableHt : SecondCountableTopology (Ht K L) :=
  (archIdentGLEquiv K L).toHomeomorph.secondCountableTopology

scoped instance instMeasurableSpaceGv (v : HeightOneSpectrum (𝓞 K)) : MeasurableSpace (Gv K v) := borel _
scoped instance instBorelSpaceGv (v : HeightOneSpectrum (𝓞 K)) : BorelSpace (Gv K v) := ⟨rfl⟩
scoped instance instMeasurableSpaceHt : MeasurableSpace (Ht K L) := borel _
scoped instance instBorelSpaceHt : BorelSpace (Ht K L) := ⟨rfl⟩
scoped instance instMeasurableSpaceGsl (v : HeightOneSpectrum (𝓞 K)) : MeasurableSpace (Gsl K L v) := borel _
scoped instance instBorelSpaceGsl (v : HeightOneSpectrum (𝓞 K)) : BorelSpace (Gsl K L v) := ⟨rfl⟩
scoped instance instMeasurableSpaceGt : MeasurableSpace (Gt K L) := borel _
scoped instance instBorelSpaceGt : BorelSpace (Gt K L) := ⟨rfl⟩

scoped instance (priority := 10000) instMeasurableSpaceSubgroupGv (v : HeightOneSpectrum (𝓞 K))
    (H : Subgroup (Gv K v)) : MeasurableSpace H := borel _
scoped instance instBorelSpaceSubgroupGv (v : HeightOneSpectrum (𝓞 K)) (H : Subgroup (Gv K v)) :
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

theorem isClosed_twistedCentralizer (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A]
    [IsTopologicalRing A] [T2Space A] (σ : L ≃ₐ[K] L) (δ : GL (Fin 2) (L ⊗[K] A)) :
    IsClosed ((twistedCentralizer K L A σ δ : Subgroup (GL (Fin 2) (L ⊗[K] A))) : Set (GL (Fin 2) (L ⊗[K] A))) := by
  haveI := isTopologicalRing_tensor K L A
  haveI := isTopologicalGroup_tensorGL K L A
  haveI := t2Space_tensorGL K L A
  have hcs : Continuous (sigmaGL K L A σ) := by
    refine Continuous.units_map _ ?_
    exact continuous_id.matrix_map (IsModuleTopology.continuous_of_linearMap
      (TensorProduct.RightActions.AlgebraMap.baseChange K L L A σ.toAlgHom).toLinearMap)
  have hc : Continuous fun t : GL (Fin 2) (L ⊗[K] A) => t * δ * (sigmaGL K L A σ t)⁻¹ :=
    (continuous_id.mul continuous_const).mul hcs.inv
  have : ((twistedCentralizer K L A σ δ : Subgroup (GL (Fin 2) (L ⊗[K] A))) : Set (GL (Fin 2) (L ⊗[K] A))) =
      (fun t : GL (Fin 2) (L ⊗[K] A) => t * δ * (sigmaGL K L A σ t)⁻¹) ⁻¹' {δ} := by
    ext t
    exact mem_sigmaCentralizer_iff
  rw [this]
  exact (isClosed_singleton).preimage hc

variable (K) in

def uArch (u : (AdeleRing (𝓞 K) K)ˣ) : (InfiniteAdeleRing K)ˣ :=
  Units.map (adeleArch (𝓞 K) K : AdeleRing (𝓞 K) K →* InfiniteAdeleRing K) u

variable (K) in

def uAt (v : HeightOneSpectrum (𝓞 K)) (u : (AdeleRing (𝓞 K) K)ˣ) : (v.adicCompletion K)ˣ :=
  Units.map (((finAdeleEval (𝓞 K) K v).comp (adeleFin (𝓞 K) K)) : AdeleRing (𝓞 K) K →* v.adicCompletion K) u

theorem glArch_centralScalar (u : (AdeleRing (𝓞 K) K)ˣ) :
    glArch (𝓞 K) K (centralScalar (𝓞 K) K u) = sc (uArch K u) :=
  map_scalar _ u

theorem cpt_centralScalar (v : HeightOneSpectrum (𝓞 K)) (u : (AdeleRing (𝓞 K) K)ˣ) :
    finComponent (𝓞 K) K v (glFin (𝓞 K) K (centralScalar (𝓞 K) K u)) = sc (uAt K v u) := by
  rw [show finComponent (𝓞 K) K v (glFin (𝓞 K) K (centralScalar (𝓞 K) K u)) =
      Matrix.GeneralLinearGroup.map ((finAdeleEval (𝓞 K) K v).comp (adeleFin (𝓞 K) K)) (centralScalar (𝓞 K) K u)
    from rfl]
  exact map_scalar _ u

variable (K L) in
theorem tensorArch_normString (σ : L ≃ₐ[K] L) (δ : Gt K L) :
    tensorArch K L (normString K L (AdeleRing (𝓞 K) K) σ δ) =
      normString K L (InfiniteAdeleRing K) σ (tensorArch K L δ) :=
  map_normString K L σ (AdeleRing (𝓞 K) K) (tensorArchHom K L).toRingHom (tensorArchHom_sigmaTensor K L σ) δ

variable (K L) in
theorem tensorPlace_normString (σ : L ≃ₐ[K] L) (v : HeightOneSpectrum (𝓞 K)) (δ : Gt K L) :
    tensorPlace K L v (normString K L (AdeleRing (𝓞 K) K) σ δ) =
      normString K L (v.adicCompletion K) σ (tensorPlace K L v δ) :=
  map_normString K L σ (AdeleRing (𝓞 K) K) (tensorPlaceHom K L v).toRingHom (tensorPlaceHom_sigmaTensor K L σ v) δ

end Carriers

section TransportEquiv

variable {G H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [MeasurableSpace H] [BorelSpace H]

theorem isMulRightInvariant_of_map_equiv (e : G ≃ₜ* H) (μ : Measure G)
    (h : (Measure.map e μ).IsMulRightInvariant) : μ.IsMulRightInvariant := by
  have hem : Measurable (e : G → H) := e.continuous.measurable
  have hesm : Measurable (e.symm : H → G) := e.symm.continuous.measurable
  refine ⟨fun g => ?_⟩
  have h1 : Measure.map (· * e g) (Measure.map e μ) = Measure.map e μ := map_mul_right_eq_self _ (e g)
  rw [Measure.map_map (measurable_mul_const (e g)) hem] at h1
  have h2 : (fun x : H => x * e g) ∘ (e : G → H) = (e : G → H) ∘ fun x : G => x * g := by
    funext x
    simp only [Function.comp_apply, map_mul]
  rw [h2, ← Measure.map_map hem (measurable_mul_const g)] at h1
  have h3 := congrArg (Measure.map (e.symm : H → G)) h1
  simp only [Measure.map_map hesm hem] at h3
  have hid : (e.symm : H → G) ∘ (e : G → H) = id := by
    funext x; simp
  rw [hid, Measure.map_id, Measure.map_id] at h3
  exact h3

theorem forall_isMulRightInvariant_of_equiv (e : G ≃ₜ* H)
    (hH : ∀ ν : Measure H, ν.IsHaarMeasure → ν.IsMulRightInvariant)
    (μ : Measure G) [μ.IsHaarMeasure] : μ.IsMulRightInvariant :=
  isMulRightInvariant_of_map_equiv e μ (hH _ (e.isHaarMeasure_map μ))

end TransportEquiv

section Local

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

theorem isMulRightInvariant_gv (v : HeightOneSpectrum (𝓞 K)) (ν : Measure (Gv K v)) [ν.IsHaarMeasure] :
    ν.IsMulRightInvariant :=
  (Matrix.GeneralLinearGroup.isMulRightInvariant_and_isInvInvariant_of_isHaarMeasure_fin_two ν).1

theorem isMulRightInvariant_centralizer_gv (v : HeightOneSpectrum (𝓞 K)) (c : (v.adicCompletion K)ˣ)
    (ν : Measure (Subgroup.centralizer ({sc c} : Set (Gv K v)))) [ν.IsHaarMeasure] :
    ν.IsMulRightInvariant := by
  haveI : IsTopologicalGroup (Subgroup.centralizer ({sc c} : Set (Gv K v))) := inferInstance
  exact forall_isMulRightInvariant_of_equiv (centralizerScalarEquiv c)
    (fun ν' hν' => by haveI := hν'; exact isMulRightInvariant_gv v ν') ν

variable (σ : L ≃ₐ[K] L)

scoped instance instLocallyCompactTwistedGsl (v : HeightOneSpectrum (𝓞 K)) (δv : Gsl K L v) :
    LocallyCompactSpace (twistedCentralizer K L (v.adicCompletion K) σ δv) :=
  (isClosed_twistedCentralizer (K := K) (L := L) _ σ δv).isClosedEmbedding_subtypeVal.locallyCompactSpace

scoped instance instSecondCountableTwistedGsl (v : HeightOneSpectrum (𝓞 K)) (δv : Gsl K L v) :
    SecondCountableTopology (twistedCentralizer K L (v.adicCompletion K) σ δv) :=
  (Topology.IsInducing.subtypeVal).secondCountableTopology

theorem isMulRightInvariant_twisted_place (h2 : Module.finrank K L = 2)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (v : HeightOneSpectrum (𝓞 K)) (c : (v.adicCompletion K)ˣ) (δv : Gsl K L v)
    (hδv : normString K L (v.adicCompletion K) σ δv = toTensorGL K L (v.adicCompletion K) (sc c))
    (ν : Measure (twistedCentralizer K L (v.adicCompletion K) σ δv)) [ν.IsHaarMeasure] :
    ν.IsMulRightInvariant := by
  classical
  haveI : Algebra.IsQuadraticExtension K L := ⟨h2⟩
  haveI : IsGalois K L := inferInstance
  by_cases hkind : ∃ z : (SL K L v)ˣ, IsSigmaConjugate K L (v.adicCompletion K) σ δv (sc z)
  ·
    obtain ⟨z, x, hx⟩ := hkind
    obtain ⟨e, -⟩ := AutomorphicForm.exists_continuousMulEquiv_centralizer_twistedCentralizer_of_eq_scalar K L σ hgen
      (v.adicCompletion K) (sc c) ⟨c, rfl⟩ δv x z hx.symm
    haveI : IsTopologicalGroup (Subgroup.centralizer ({sc c} : Set (Gv K v))) := inferInstance
    exact forall_isMulRightInvariant_of_equiv e.symm
      (fun ν' hν' => by haveI := hν'; exact isMulRightInvariant_centralizer_gv v c ν') ν
  ·
    push Not at hkind
    have hδ : IsNormOf K L (v.adicCompletion K) σ (sc c) δv := by
      refine ⟨1, ?_⟩
      unfold IsNormConjugator
      rw [inv_one, one_mul, mul_one]
      exact hδv.symm
    obtain ⟨C, hC, hCsub, hcov⟩ :=
      AutomorphicForm.exists_isCompact_forall_twistedCentralizer_eq_scalar_mul_of_not_isSigmaConjugate_scalar_of_finrank_eq_two
        K L h2 σ hgen v c δv hδ hkind

    have hmem : ∀ e : (v.adicCompletion K)ˣ, toTensorGL K L (v.adicCompletion K) (sc e) ∈
        twistedCentralizer K L (v.adicCompletion K) σ δv := by
      intro e
      rw [mem_sigmaCentralizer_iff, sigmaGL_toTensorGL, toTensorGL_scalar, scalar_mul_comm, mul_assoc, mul_inv_cancel,
        mul_one]
    set Z : Set (twistedCentralizer K L (v.adicCompletion K) σ δv) :=
      Set.range fun e : (v.adicCompletion K)ˣ => (⟨toTensorGL K L (v.adicCompletion K) (sc e), hmem e⟩ :
        twistedCentralizer K L (v.adicCompletion K) σ δv) with hZ
    set C' : Set (twistedCentralizer K L (v.adicCompletion K) σ δv) := Subtype.val ⁻¹' C with hC'
    have hC'c : IsCompact C' :=
      (IsClosedEmbedding.subtypeVal (isClosed_twistedCentralizer (K := K) (L := L) _ σ δv)).isCompact_preimage hC
    have hZc : ∀ z ∈ Z, ∀ g : twistedCentralizer K L (v.adicCompletion K) σ δv, g * z = z * g := by
      rintro z ⟨e, rfl⟩ g
      refine Subtype.ext ?_
      show (g : Gsl K L v) * toTensorGL K L (v.adicCompletion K) (sc e) = toTensorGL K L (v.adicCompletion K) (sc e) * g
      rw [toTensorGL_scalar]
      exact (scalar_mul_comm _ _).symm
    have hcov' : ∀ g : twistedCentralizer K L (v.adicCompletion K) σ δv, ∃ z ∈ Z, ∃ k ∈ C', g = z * k := by
      intro g
      obtain ⟨e, k, hk, hgk⟩ := hcov g g.2
      have hkT : k ∈ twistedCentralizer K L (v.adicCompletion K) σ δv := hCsub hk
      refine ⟨⟨toTensorGL K L (v.adicCompletion K) (sc e), hmem e⟩, ⟨e, rfl⟩, ⟨k, hkT⟩, hk, ?_⟩
      exact Subtype.ext hgk
    exact MeasureTheory.Measure.isMulRightInvariant_of_forall_exists_eq_mul_of_isCompact Z C' hZc hC'c hcov' ν

variable (v : HeightOneSpectrum (𝓞 K)) (δv : Gsl K L v)

def unitTwistedCompacts : PositiveCompacts (twistedCentralizer K L (v.adicCompletion K) σ δv) where
  carrier := Subtype.val ⁻¹' semiLocalIntegralSet K L v
  isCompact' := (IsClosedEmbedding.subtypeVal (isClosed_twistedCentralizer (K := K) (L := L) _ σ δv)).isCompact_preimage
    (isCompact_semiLocalIntegralSet K L v)
  interior_nonempty' := by
    rw [((isOpen_semiLocalIntegralSet K L v).preimage continuous_subtype_val).interior_eq]
    exact ⟨1, one_mem_semiLocalIntegralSet K L v⟩

def unitTwistedHaar : Measure (twistedCentralizer K L (v.adicCompletion K) σ δv) :=
  Measure.haarMeasure (unitTwistedCompacts σ v δv)

scoped instance isHaarMeasure_unitTwistedHaar : (unitTwistedHaar σ v δv).IsHaarMeasure :=
  Measure.isHaarMeasure_haarMeasure _

theorem unitTwistedHaar_self : unitTwistedHaar σ v δv (Subtype.val ⁻¹' semiLocalIntegralSet K L v) = 1 :=
  Measure.haarMeasure_self

end Local

section Global

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable (σ : L ≃ₐ[K] L) (δ : Gt K L)

abbrev Tad : Subgroup (Gt K L) := twistedCentralizer K L (AdeleRing (𝓞 K) K) σ δ

abbrev Tarch : Subgroup (Ht K L) := twistedCentralizer K L (InfiniteAdeleRing K) σ (tensorArch K L δ)

abbrev Tv (v : HeightOneSpectrum (𝓞 K)) : Subgroup (Gsl K L v) :=
  twistedCentralizer K L (v.adicCompletion K) σ (tensorPlace K L v δ)

scoped instance instLocallyCompactTad : LocallyCompactSpace (Tad σ δ) :=
  (isClosed_twistedCentralizer (K := K) (L := L) _ σ δ).isClosedEmbedding_subtypeVal.locallyCompactSpace

scoped instance instSecondCountableTad : SecondCountableTopology (Tad σ δ) :=
  (Topology.IsInducing.subtypeVal).secondCountableTopology

scoped instance instLocallyCompactTarch : LocallyCompactSpace (Tarch σ δ) :=
  (isClosed_twistedCentralizer (K := K) (L := L) _ σ _).isClosedEmbedding_subtypeVal.locallyCompactSpace

scoped instance instSecondCountableTarch : SecondCountableTopology (Tarch σ δ) :=
  (Topology.IsInducing.subtypeVal).secondCountableTopology

variable {σ δ}

theorem tensorArch_mem (s : Tad σ δ) : tensorArch K L (s : Gt K L) ∈ Tarch σ δ := by
  have h := (AutomorphicForm.mem_sigmaCentralizer_iff).1 s.2
  rw [AutomorphicForm.mem_sigmaCentralizer_iff, ← tensorArch_sigmaGL, ← map_inv, ← map_mul, ← map_mul, h]

theorem tensorPlace_mem (v : HeightOneSpectrum (𝓞 K)) (s : Tad σ δ) : tensorPlace K L v (s : Gt K L) ∈ Tv σ δ v := by
  have h := (AutomorphicForm.mem_sigmaCentralizer_iff).1 s.2
  rw [AutomorphicForm.mem_sigmaCentralizer_iff, ← tensorPlace_sigmaGL, ← map_inv, ← map_mul, ← map_mul, h]

def indC {G : Type*} [Group G] (H : Subgroup G) (C : Set H) : G → ℂ :=
  (Subtype.val '' C).indicator fun _ => (1 : ℂ)

theorem indC_coe {G : Type*} [Group G] (H : Subgroup G) (C : Set H) (t : H) :
    indC H C t = C.indicator (fun _ => (1 : ℂ)) t := by
  unfold indC
  by_cases ht : t ∈ C
  · rw [Set.indicator_of_mem ht, Set.indicator_of_mem (Set.mem_image_of_mem Subtype.val ht)]
  · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem]
    rintro ⟨u, hu, hut⟩
    exact ht (Subtype.val_injective hut ▸ hu)

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

variable (σ δ)

set_option maxHeartbeats 4000000 in

theorem global (τa : Measure (Tarch σ δ)) [τa.IsHaarMeasure] [τa.IsMulRightInvariant]
    (τf : ∀ v : HeightOneSpectrum (𝓞 K), Measure (Tv σ δ v)) [hτf : ∀ v, (τf v).IsHaarMeasure]
    (hτfr : ∀ v, (τf v).IsMulRightInvariant)
    (hτf1 : ∀ v : HeightOneSpectrum (𝓞 K), τf v (Subtype.val ⁻¹' semiLocalIntegralSet K L v) = 1)
    (τ : Measure (Tad σ δ)) [τ.IsHaarMeasure] : τ.IsMulRightInvariant := by
  classical

  obtain ⟨cT, hcT, hT⟩ :=
    AutomorphicForm.exists_integral_twistedCentralizer_eq_mul_integral_mul_prod_integral_of_isHaarMeasure
      K L σ δ τ inferInstance τa inferInstance τf hτf hτf1
  refine ⟨fun s => ?_⟩
  set ρ' : Measure (Tad σ δ) := Measure.map (· * s) τ with hρ'
  haveI : ρ'.IsHaarMeasure := isHaarMeasure_map_mul_right τ s
  have huniq : ρ' = haarScalarFactor ρ' τ • τ := isMulLeftInvariant_eq_smul ρ' τ
  set k : ℝ≥0 := haarScalarFactor ρ' τ with hk_def
  clear_value k

  obtain ⟨Ca⟩ : Nonempty (PositiveCompacts (Tarch σ δ)) := inferInstance
  have hCa : IsCompact (Ca : Set (Tarch σ δ)) := Ca.isCompact
  have hCapos : τa (Ca : Set (Tarch σ δ)) ≠ 0 :=
    (measure_pos_of_nonempty_interior τa Ca.interior_nonempty).ne'
  have hCatop : τa (Ca : Set (Tarch σ δ)) ≠ ⊤ := hCa.measure_lt_top.ne

  obtain ⟨S, U, hU, hSU⟩ := AutomorphicForm.exists_finset_mem_nhds_forall_tensorPlace_mem_semiLocalIntegralSet K L (s : Gt K L)
  have hsS : ∀ v ∉ S, tensorPlace K L v (s : Gt K L) ∈ semiLocalIntegralSet K L v :=
    fun v hv => hSU _ (mem_of_mem_nhds hU) v hv

  set sA : Tarch σ δ := ⟨tensorArch K L (s : Gt K L), tensorArch_mem s⟩ with hsA
  set sV : ∀ v : HeightOneSpectrum (𝓞 K), Tv σ δ v := fun v => ⟨tensorPlace K L v (s : Gt K L), tensorPlace_mem v s⟩
    with hsV

  set Wa : Ht K L → ℂ := indC (Tarch σ δ) (Ca : Set (Tarch σ δ)) with hWa
  set Wa' : Ht K L → ℂ := fun y => Wa (y * tensorArch K L (s : Gt K L)) with hWa'
  set WS : ∀ v : HeightOneSpectrum (𝓞 K), Gsl K L v → ℂ := fun v =>
    (semiLocalIntegralSet K L v).indicator fun _ => (1 : ℂ) with hWS
  set WS' : ∀ v : HeightOneSpectrum (𝓞 K), Gsl K L v → ℂ := fun v y => WS v (y * tensorPlace K L v (s : Gt K L)) with hWS'
  set W : Gt K L → ℂ := fun x =>
    if ∀ v ∉ S, tensorPlace K L v x ∈ semiLocalIntegralSet K L v then
      Wa (tensorArch K L x) * ∏ v ∈ S, WS v (tensorPlace K L v x) else 0 with hW
  set W' : Gt K L → ℂ := fun x => W (x * (s : Gt K L)) with hW'

  have hWa₀ : ∀ t : Tarch σ δ, Wa t = (Ca : Set (Tarch σ δ)).indicator (fun _ => (1 : ℂ)) t := fun t => by
    rw [hWa]; exact indC_coe _ _ t
  have hWa₀' : ∀ t : Tarch σ δ, Wa' t = ((fun y : Tarch σ δ => y * sA) ⁻¹' (Ca : Set (Tarch σ δ))).indicator (fun _ => (1 : ℂ)) t := by
    intro t
    rw [hWa']
    dsimp only
    have := hWa₀ (t * sA)
    rw [Subgroup.coe_mul] at this
    rw [this]
    rfl
  have hWS₀ : ∀ (v : HeightOneSpectrum (𝓞 K)) (t : Tv σ δ v),
      WS v t = (Subtype.val ⁻¹' semiLocalIntegralSet K L v : Set (Tv σ δ v)).indicator (fun _ => (1 : ℂ)) t := by
    intro v t
    rw [hWS]
    dsimp only
    by_cases ht : (t : Gsl K L v) ∈ semiLocalIntegralSet K L v
    · rw [Set.indicator_of_mem ht, Set.indicator_of_mem (show t ∈ Subtype.val ⁻¹' semiLocalIntegralSet K L v from ht)]
    · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem (show t ∉ Subtype.val ⁻¹' semiLocalIntegralSet K L v from ht)]
  have hWS₀' : ∀ (v : HeightOneSpectrum (𝓞 K)) (t : Tv σ δ v),
      WS' v t = ((fun y : Tv σ δ v => y * sV v) ⁻¹' (Subtype.val ⁻¹' semiLocalIntegralSet K L v : Set (Tv σ δ v))).indicator
        (fun _ => (1 : ℂ)) t := by
    intro v t
    rw [hWS']
    dsimp only
    have := hWS₀ v (t * sV v)
    rw [Subgroup.coe_mul] at this
    rw [this]
    rfl

  have hpreCa : IsCompact ((fun y : Tarch σ δ => y * sA) ⁻¹' (Ca : Set (Tarch σ δ))) := by
    have : (fun y : Tarch σ δ => y * sA) ⁻¹' (Ca : Set (Tarch σ δ)) = (fun y => y * sA⁻¹) '' (Ca : Set (Tarch σ δ)) := by
      ext y
      simp only [Set.mem_preimage, Set.mem_image]
      constructor
      · intro hy; exact ⟨y * sA, hy, by group⟩
      · rintro ⟨y', hy', rfl⟩; simpa using hy'
    rw [this]
    exact hCa.image (continuous_id.mul continuous_const)
  have hIntMeas : ∀ v : HeightOneSpectrum (𝓞 K),
      MeasurableSet (Subtype.val ⁻¹' semiLocalIntegralSet K L v : Set (Tv σ δ v)) := fun v =>
    ((isOpen_semiLocalIntegralSet K L v).preimage continuous_subtype_val).measurableSet
  have hWa_meas : AEStronglyMeasurable (fun t : Tarch σ δ => Wa t) τa := by
    have : (fun t : Tarch σ δ => Wa t) = (Ca : Set (Tarch σ δ)).indicator fun _ => (1 : ℂ) := funext hWa₀
    rw [this]
    exact (measurable_const.indicator hCa.measurableSet).aestronglyMeasurable
  have hWa'_meas : AEStronglyMeasurable (fun t : Tarch σ δ => Wa' t) τa := by
    have : (fun t : Tarch σ δ => Wa' t) =
        ((fun y : Tarch σ δ => y * sA) ⁻¹' (Ca : Set (Tarch σ δ))).indicator fun _ => (1 : ℂ) := funext hWa₀'
    rw [this]
    exact (measurable_const.indicator hpreCa.measurableSet).aestronglyMeasurable
  have hWS_meas : ∀ v ∈ S, AEStronglyMeasurable (fun t : Tv σ δ v => WS v t) (τf v) := by
    intro v _
    have : (fun t : Tv σ δ v => WS v t) =
        (Subtype.val ⁻¹' semiLocalIntegralSet K L v : Set (Tv σ δ v)).indicator fun _ => (1 : ℂ) := funext (hWS₀ v)
    rw [this]
    exact (measurable_const.indicator (hIntMeas v)).aestronglyMeasurable
  have hWS'_meas : ∀ v ∈ S, AEStronglyMeasurable (fun t : Tv σ δ v => WS' v t) (τf v) := by
    intro v _
    have : (fun t : Tv σ δ v => WS' v t) =
        ((fun y : Tv σ δ v => y * sV v) ⁻¹' (Subtype.val ⁻¹' semiLocalIntegralSet K L v : Set (Tv σ δ v))).indicator
          fun _ => (1 : ℂ) := funext (hWS₀' v)
    rw [this]
    exact (measurable_const.indicator ((hIntMeas v).preimage (measurable_mul_const _))).aestronglyMeasurable

  have hWshape : ∀ t : Tad σ δ, (∀ v ∉ S, tensorPlace K L v (t : Gt K L) ∈ semiLocalIntegralSet K L v) →
      W t = Wa (tensorArch K L (t : Gt K L)) * ∏ v ∈ S, WS v (tensorPlace K L v (t : Gt K L)) := by
    intro t ht; rw [hW]; dsimp only; rw [if_pos ht]
  have hWvan : ∀ t : Tad σ δ, (∃ v ∉ S, tensorPlace K L v (t : Gt K L) ∉ semiLocalIntegralSet K L v) → W t = 0 := by
    intro t ht
    rw [hW]; dsimp only
    rw [if_neg]
    push Not
    exact ht
  have hiff : ∀ (v : HeightOneSpectrum (𝓞 K)) (x : Gt K L), v ∉ S →
      (tensorPlace K L v (x * (s : Gt K L)) ∈ semiLocalIntegralSet K L v ↔
        tensorPlace K L v x ∈ semiLocalIntegralSet K L v) := by
    intro v x hv
    rw [map_mul]
    constructor
    · intro h
      have := mul_mem_semiLocalIntegralSet v h (inv_mem_semiLocalIntegralSet v (hsS v hv))
      rwa [mul_inv_cancel_right] at this
    · intro h
      exact mul_mem_semiLocalIntegralSet v h (hsS v hv)
  have hW'shape : ∀ t : Tad σ δ, (∀ v ∉ S, tensorPlace K L v (t : Gt K L) ∈ semiLocalIntegralSet K L v) →
      W' t = Wa' (tensorArch K L (t : Gt K L)) * ∏ v ∈ S, WS' v (tensorPlace K L v (t : Gt K L)) := by
    intro t ht
    have ht' : ∀ v ∉ S, tensorPlace K L v ((t : Gt K L) * (s : Gt K L)) ∈ semiLocalIntegralSet K L v :=
      fun v hv => (hiff v _ hv).2 (ht v hv)
    rw [hW', hW]; dsimp only
    rw [if_pos ht']
    simp only [map_mul, hWa', hWS']
  have hW'van : ∀ t : Tad σ δ, (∃ v ∉ S, tensorPlace K L v (t : Gt K L) ∉ semiLocalIntegralSet K L v) → W' t = 0 := by
    intro t ht
    obtain ⟨v, hv, hvt⟩ := ht
    rw [hW', hW]; dsimp only
    rw [if_neg]
    push Not
    exact ⟨v, hv, fun h => hvt ((hiff v _ hv).1 h)⟩

  have h1 := hT S W Wa WS hWa_meas hWS_meas hWshape hWvan
  have h2 := hT S W' Wa' WS' hWa'_meas hWS'_meas hW'shape hW'van

  have hIa : ∫ t : Tarch σ δ, Wa' (t : Ht K L) ∂τa = ∫ t : Tarch σ δ, Wa (t : Ht K L) ∂τa := by
    have : (fun t : Tarch σ δ => Wa' t) = fun t : Tarch σ δ => (fun y : Tarch σ δ => Wa y) (t * sA) := by
      funext t; rfl
    rw [this]
    exact integral_mul_right_eq_self (fun y : Tarch σ δ => Wa y) sA
  have hIv : ∀ v, ∫ t : Tv σ δ v, WS' v (t : Gsl K L v) ∂(τf v) = ∫ t : Tv σ δ v, WS v (t : Gsl K L v) ∂(τf v) := by
    intro v
    haveI := hτfr v
    have : (fun t : Tv σ δ v => WS' v t) = fun t : Tv σ δ v => (fun y : Tv σ δ v => WS v y) (t * sV v) := by
      funext t; rfl
    rw [this]
    exact integral_mul_right_eq_self (fun y : Tv σ δ v => WS v y) (sV v)
  have h12 : ∫ t : Tad σ δ, W' (t : Gt K L) ∂τ = ∫ t : Tad σ δ, W (t : Gt K L) ∂τ := by
    rw [h1, h2, hIa]
    congr 1
    exact Finset.prod_congr rfl fun v _ => hIv v

  have hIa1 : ∫ t : Tarch σ δ, Wa (t : Ht K L) ∂τa = ((τa (Ca : Set (Tarch σ δ))).toReal : ℂ) := by
    simp_rw [hWa₀]
    rw [integral_indicator_const _ hCa.measurableSet, Measure.real, Complex.real_smul, mul_one]
  have hIv1 : ∀ v ∈ S, ∫ t : Tv σ δ v, WS v (t : Gsl K L v) ∂(τf v) = 1 := by
    intro v _
    simp_rw [hWS₀ v]
    rw [integral_indicator_const _ (hIntMeas v), Measure.real, hτf1 v, Complex.real_smul, mul_one]
    simp
  have hval : ∫ t : Tad σ δ, W (t : Gt K L) ∂τ = (cT : ℂ) * ((τa (Ca : Set (Tarch σ δ))).toReal : ℂ) := by
    rw [h1, hIa1, Finset.prod_eq_one hIv1, mul_one]
  have hI0 : ∫ t : Tad σ δ, W (t : Gt K L) ∂τ ≠ 0 := by
    rw [hval]
    exact mul_ne_zero (Complex.ofReal_ne_zero.2 hcT.ne')
      (Complex.ofReal_ne_zero.2 (ENNReal.toReal_ne_zero.2 ⟨hCapos, hCatop⟩))

  have h3 : ∫ t : Tad σ δ, W' (t : Gt K L) ∂τ = ∫ t : Tad σ δ, W (t : Gt K L) ∂ρ' := by
    rw [hρ', show (fun x : Tad σ δ => x * s) = ⇑(MeasurableEquiv.mulRight s) from rfl,
      MeasureTheory.integral_map_equiv (MeasurableEquiv.mulRight s) (fun t : Tad σ δ => W t)]
    rfl
  rw [huniq, integral_smul_nnreal_measure, h12, NNReal.smul_def, Complex.real_smul] at h3

  have hk : k = 1 := by
    have h4 : ((k : ℝ) : ℂ) = 1 := (mul_eq_right₀ hI0).1 h3.symm
    exact NNReal.coe_eq_one.1 (Complex.ofReal_eq_one.1 h4)
  rw [huniq, hk, one_smul]

end Global

section Assembly

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

theorem main (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (δ : Gt K L) (u : (AdeleRing (𝓞 K) K)ˣ)
    (hN : normString K L (AdeleRing (𝓞 K) K) σ δ = toTensorGL K L (AdeleRing (𝓞 K) K) (centralScalar (𝓞 K) K u))
    (τ' : Measure (Tad σ δ)) [τ'.IsHaarMeasure] : τ'.IsMulRightInvariant := by
  classical

  have hya : IsNormConjugator K L (InfiniteAdeleRing K) σ (sc (uArch K u)) (tensorArch K L δ) 1 := by
    unfold IsNormConjugator
    rw [inv_one, one_mul, mul_one, ← tensorArch_normString, hN, tensorArch_toTensorGL, glArch_centralScalar]
  have hNv : ∀ v : HeightOneSpectrum (𝓞 K), normString K L (v.adicCompletion K) σ (tensorPlace K L v δ) =
      toTensorGL K L (v.adicCompletion K) (sc (uAt K v u)) := by
    intro v
    rw [← tensorPlace_normString, hN, tensorPlace_toTensorGL]
    exact congrArg _ (cpt_centralScalar v u)

  letI mM : MeasurableSpace (Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) := borel _
  haveI : BorelSpace (Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) := ⟨rfl⟩
  obtain ⟨τc, τa, hτcH, hτaH, hτcR, hτaR, -⟩ :=
    AutomorphicForm.exists_isHaarMeasure_map_eq_smul_withDensity_arch_of_isNormConjugator_scalar_of_finrank_eq_two
      K L h2 σ hgen (sc (uArch K u)) ⟨_, rfl⟩ (tensorArch K L δ) 1 hya
  haveI := hτaH
  haveI := hτaR

  set τu : ∀ v : HeightOneSpectrum (𝓞 K), Measure (Tv σ δ v) := fun v => unitTwistedHaar σ v (tensorPlace K L v δ)
    with hτu_def
  haveI hτuH : ∀ v, (τu v).IsHaarMeasure := fun v => isHaarMeasure_unitTwistedHaar σ v _
  have hτu1 : ∀ v : HeightOneSpectrum (𝓞 K), τu v (Subtype.val ⁻¹' semiLocalIntegralSet K L v) = 1 := fun v =>
    unitTwistedHaar_self σ v _
  have hτur : ∀ v, (τu v).IsMulRightInvariant := fun v =>
    isMulRightInvariant_twisted_place σ h2 hgen v (uAt K v u) (tensorPlace K L v δ) (hNv v) (τu v)
  exact global σ δ τa τu hτur hτu1 τ'

end Assembly

end AutomorphicForm.TwistedUnimodular
p2m_reactivate "P2MW.S_AutomorphicForm_isMulRightInvariant_twistedCentralizer_adeleRing_of_normString_eq_toTensorGL_centralScalar_of_finrank_eq_two.AutomorphicForm P2MW.S_AutomorphicForm_isMulRightInvariant_twistedCentralizer_adeleRing_of_normString_eq_toTensorGL_centralScalar_of_finrank_eq_two.AutomorphicForm.TwistedUnimodular"
p2m_reactivate "P2MW.S_AutomorphicForm_isMulRightInvariant_twistedCentralizer_adeleRing_of_normString_eq_toTensorGL_centralScalar_of_finrank_eq_two.AutomorphicForm"

end
p2m_reactivate "P2MW.S_AutomorphicForm_isMulRightInvariant_twistedCentralizer_adeleRing_of_normString_eq_toTensorGL_centralScalar_of_finrank_eq_two.AutomorphicForm P2MW.S_AutomorphicForm_isMulRightInvariant_twistedCentralizer_adeleRing_of_normString_eq_toTensorGL_centralScalar_of_finrank_eq_two.AutomorphicForm.TwistedUnimodular"

section Solution

open MeasureTheory NumberField IsDedekindDomain
open AutomorphicForm.TwistedUnimodular
open scoped TensorProduct TensorProduct.RightActions

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (δ : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) (u : (AdeleRing (𝓞 K) K)ˣ)
    (hN : AutomorphicForm.normString K L (AdeleRing (𝓞 K) K) σ δ =
      AutomorphicForm.toTensorGL K L (AdeleRing (𝓞 K) K) (AutomorphicForm.centralScalar (𝓞 K) K u))
    (τ' : @Measure (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ δ)
      (AutomorphicForm.twistedCentralizerBorel K L (AdeleRing (𝓞 K) K) σ δ))
    (hτ' : @Measure.IsHaarMeasure _ _ _
      (AutomorphicForm.twistedCentralizerBorel K L (AdeleRing (𝓞 K) K) σ δ) τ') :
    @Measure.IsMulRightInvariant _
      (AutomorphicForm.twistedCentralizerBorel K L (AdeleRing (𝓞 K) K) σ δ) _ τ' := by
  haveI := hτ'
  exact main h2 σ hgen δ u hN τ'

end Solution
p2m_reactivate "P2MW.S_AutomorphicForm_isMulRightInvariant_twistedCentralizer_adeleRing_of_normString_eq_toTensorGL_centralScalar_of_finrank_eq_two.AutomorphicForm P2MW.S_AutomorphicForm_isMulRightInvariant_twistedCentralizer_adeleRing_of_normString_eq_toTensorGL_centralScalar_of_finrank_eq_two.AutomorphicForm.TwistedUnimodular"

end S_AutomorphicForm_isMulRightInvariant_twistedCentralizer_adeleRing_of_normString_eq_toTensorGL_centralScalar_of_finrank_eq_two
end P2MW
export P2MW.S_AutomorphicForm_isMulRightInvariant_twistedCentralizer_adeleRing_of_normString_eq_toTensorGL_centralScalar_of_finrank_eq_two (solution)
