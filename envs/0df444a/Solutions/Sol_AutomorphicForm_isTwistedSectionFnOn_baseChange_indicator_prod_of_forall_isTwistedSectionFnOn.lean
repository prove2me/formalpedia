-- Prove2me | solution 1 for AutomorphicForm.isTwistedSectionFnOn_baseChange_indicator_prod_of_forall_isTwistedSectionFnOn
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/217301d6-37ec-5010-be55-c74df2f46522

import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_isTwistedSectionFnOn_baseChange_indicator_prod_of_forall_isTwistedSectionFnOn

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory MeasureTheory.Measure Topology TopologicalSpace Set Filter
open NumberField.AdelicLevel TensorProduct
open scoped TensorProduct.RightActions NNReal ENNReal

noncomputable section

namespace AutomorphicForm
p2m_export "AutomorphicForm" "tensorArch tensorPlace glArch_baseChangeGL semiLocalComponent_glFin_baseChangeGL tensorArch_sigmaGL tensorPlace_sigmaGL baseChangeGLEquiv archIdentGLEquiv semiLocalEval_eq semiLocalHomeomorph_eq continuous_tensorArch continuous_tensorPlace matrix_eq_of_forall_semiLocalEval_mapMatrix_eq isTopologicalRing_tensor t2Space_tensor locallyCompactSpace_tensor isTopologicalGroup_tensorGL locallyCompactSpace_tensorGL glBorelOf semiLocalHomeomorph piIntegers semiLocalIntegers semiLocalIntegers_eq_preimage semiLocalIntegralSet one_mem_semiLocalIntegralSet isCompact_semiLocalIntegralSet isOpen_semiLocalIntegralSet sigmaGL twistedCentralizer twistedCentralizerBorel IsTwistedSectionFnOn semiLocalEval semiLocalComponent integralUnitsSet mem_integralUnitsSet localIntegralSet mem_localIntegralSet unitFinSet one_mem_unitFinSet isCompact_unitFinSet isOpen_unitFinSet"
namespace BaseChangeProductSectionFn
p2m_open "AutomorphicForm"

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

abbrev Garch (L : Type) [Field L] [NumberField L] : Type := GL (Fin 2) (InfiniteAdeleRing L)

abbrev Gfin (L : Type) [Field L] [NumberField L] : Type := GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)

abbrev Gad (L : Type) [Field L] [NumberField L] : Type := GL (Fin 2) (AdeleRing (𝓞 L) L)

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

abbrev SProd (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (S : Finset (HeightOneSpectrum (𝓞 K))) : Type :=
  (v : S) → Gsl K L v.1

abbrev LocProd (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (S : Finset (HeightOneSpectrum (𝓞 K))) : Type :=
  Ht K L × SProd K L S

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

scoped instance instSecondCountableGarch : SecondCountableTopology (Garch L) := secondCountable_gl _

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

scoped instance instIsTopologicalRingTA : IsTopologicalRing (L ⊗[K] AdeleRing (𝓞 K) K) :=
  isTopologicalRing_tensor K L _
scoped instance instT2TA : T2Space (L ⊗[K] AdeleRing (𝓞 K) K) := t2Space_tensor K L _
scoped instance instIsTopologicalGroupGt : IsTopologicalGroup (Gt K L) := isTopologicalGroup_tensorGL K L _

scoped instance instIsTopologicalRingTI : IsTopologicalRing (L ⊗[K] InfiniteAdeleRing K) :=
  isTopologicalRing_tensor K L _
scoped instance instT2TI : T2Space (L ⊗[K] InfiniteAdeleRing K) := t2Space_tensor K L _
scoped instance instLocallyCompactTI : LocallyCompactSpace (L ⊗[K] InfiniteAdeleRing K) :=
  locallyCompactSpace_tensor K L _
scoped instance instIsTopologicalGroupHt : IsTopologicalGroup (Ht K L) := isTopologicalGroup_tensorGL K L _
scoped instance instLocallyCompactHt : LocallyCompactSpace (Ht K L) := locallyCompactSpace_tensorGL K L _
scoped instance instSecondCountableHt : SecondCountableTopology (Ht K L) :=
  (archIdentGLEquiv K L).toHomeomorph.secondCountableTopology

scoped instance instMeasurableSpaceHt : MeasurableSpace (Ht K L) := borel _
scoped instance instBorelSpaceHt : BorelSpace (Ht K L) := ⟨rfl⟩
scoped instance instMeasurableSpaceGsl (v : HeightOneSpectrum (𝓞 K)) : MeasurableSpace (Gsl K L v) := borel _
scoped instance instBorelSpaceGsl (v : HeightOneSpectrum (𝓞 K)) : BorelSpace (Gsl K L v) := ⟨rfl⟩
scoped instance instMeasurableSpaceGt : MeasurableSpace (Gt K L) := borel _
scoped instance instBorelSpaceGt : BorelSpace (Gt K L) := ⟨rfl⟩

scoped instance instSigmaCompactGsl (v : HeightOneSpectrum (𝓞 K)) : SigmaCompactSpace (Gsl K L v) :=
  sigmaCompactSpace_of_locallyCompact_secondCountable
scoped instance instSigmaCompactHt : SigmaCompactSpace (Ht K L) :=
  sigmaCompactSpace_of_locallyCompact_secondCountable

end Instances

section IntegralSubgroup

variable {A : Type*} [CommRing A]

theorem mul_mem_integralUnitsSet (U : Subring A) {g h : GL (Fin 2) A}
    (hg : g ∈ integralUnitsSet (U : Set A)) (hh : h ∈ integralUnitsSet (U : Set A)) :
    g * h ∈ integralUnitsSet (U : Set A) := by
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [Units.val_mul, Matrix.mul_apply]
    exact U.sum_mem fun k _ => U.mul_mem (hg.1 i k) (hh.1 k j)
  · rw [mul_inv_rev, Units.val_mul, Matrix.mul_apply]
    exact U.sum_mem fun k _ => U.mul_mem (hh.2 i k) (hg.2 k j)

theorem inv_mem_integralUnitsSet (U : Set A) {g : GL (Fin 2) A} (hg : g ∈ integralUnitsSet U) :
    g⁻¹ ∈ integralUnitsSet U :=
  ⟨hg.2, by rw [inv_inv]; exact hg.1⟩

end IntegralSubgroup

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

section Dictionary

variable (v : HeightOneSpectrum (𝓞 K))

theorem semiLocalEval_mem_semiLocalIntegers_iff (a : FiniteAdeleRing (𝓞 L) L) :
    semiLocalEval K L v a ∈ semiLocalIntegers K L v ↔
      ∀ w : v.Extension (𝓞 L), a w.1 ∈ w.1.adicCompletionIntegers L := by
  rw [semiLocalIntegers_eq_preimage, Set.mem_preimage, semiLocalHomeomorph_eq, semiLocalEval_eq,
    AlgEquiv.apply_symm_apply, piIntegers, Set.mem_univ_pi]
  rfl

theorem semiLocalComponent_apply (h : Gfin L) (i j : Fin 2) :
    (semiLocalComponent K L v h : Matrix (Fin 2) (Fin 2) (SL K L v)) i j =
      semiLocalEval K L v ((h : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 L) L)) i j) := rfl

theorem semiLocalComponent_mem_iff (h : Gfin L) :
    semiLocalComponent K L v h ∈ semiLocalIntegralSet K L v ↔
      ∀ w : v.Extension (𝓞 L), finComponent (𝓞 L) L w.1 h ∈ localIntegralSet L w.1 := by
  simp only [semiLocalIntegralSet, mem_integralUnitsSet, ← map_inv, semiLocalComponent_apply,
    semiLocalEval_mem_semiLocalIntegers_iff, mem_localIntegralSet, finComponent_apply]
  constructor
  · rintro ⟨h1, h2⟩ w
    exact ⟨fun i j => h1 i j w, fun i j => h2 i j w⟩
  · intro hw
    exact ⟨fun i j w => (hw w).1 i j, fun i j w => (hw w).2 i j⟩

theorem forall_semiLocalComponent_mem_iff (h : Gfin L) :
    (∀ v : HeightOneSpectrum (𝓞 K), semiLocalComponent K L v h ∈ semiLocalIntegralSet K L v) ↔
      h ∈ unitFinSet L := by
  constructor
  · intro hh w
    exact (semiLocalComponent_mem_iff (HeightOneSpectrum.under (𝓞 K) w) h).1 (hh _) ⟨w, rfl⟩
  · intro hh v
    exact (semiLocalComponent_mem_iff v h).2 fun w => hh w.1

end Dictionary

variable (S : Finset (HeightOneSpectrum (𝓞 K)))

section Embedding

variable (L) in

def above : Set (HeightOneSpectrum (𝓞 L)) :=
  (HeightOneSpectrum.under (𝓞 K) : HeightOneSpectrum (𝓞 L) → HeightOneSpectrum (𝓞 K)) ⁻¹' (↑S)

theorem finite_above : (above L S).Finite :=
  HeightOneSpectrum.preimage_comap_finite (𝓞 K) K L (𝓞 L) (↑S) S.finite_toSet

theorem cofinite_le_principal_compl :
    (cofinite : Filter (HeightOneSpectrum (𝓞 L))) ≤ 𝓟 ((above L S)ᶜ) :=
  Filter.le_principal_iff.mpr (finite_above S).compl_mem_cofinite

open scoped Classical in

def entryFun (i j : Fin 2) (t : (v : S) → Matrix (Fin 2) (Fin 2) (SL K L v.1))
    (w : HeightOneSpectrum (𝓞 L)) : w.adicCompletion L :=
  if h : HeightOneSpectrum.under (𝓞 K) w ∈ S then
    semiLocalHomeomorph K L (HeightOneSpectrum.under (𝓞 K) w) (t ⟨_, h⟩ i j) ⟨w, rfl⟩
  else (1 : Matrix (Fin 2) (Fin 2) (w.adicCompletion L)) i j

theorem one_apply_mem (w : HeightOneSpectrum (𝓞 L)) (i j : Fin 2) :
    (1 : Matrix (Fin 2) (Fin 2) (w.adicCompletion L)) i j ∈ w.adicCompletionIntegers L := by
  rw [Matrix.one_apply]
  split_ifs
  · exact one_mem _
  · exact zero_mem _

open scoped Classical in
theorem entryFun_of_not_mem (i j : Fin 2) (t : (v : S) → Matrix (Fin 2) (Fin 2) (SL K L v.1))
    {w : HeightOneSpectrum (𝓞 L)} (hw : HeightOneSpectrum.under (𝓞 K) w ∉ S) :
    entryFun S i j t w = (1 : Matrix (Fin 2) (Fin 2) (w.adicCompletion L)) i j := by
  simp only [entryFun, dif_neg hw]

open scoped Classical in

def entryPrincipal (i j : Fin 2) (t : (v : S) → Matrix (Fin 2) (Fin 2) (SL K L v.1)) :
    RestrictedProduct (fun w : HeightOneSpectrum (𝓞 L) => w.adicCompletion L)
      (fun w : HeightOneSpectrum (𝓞 L) => (w.adicCompletionIntegers L : Set (w.adicCompletion L)))
      (𝓟 ((above L S)ᶜ)) :=
  ⟨entryFun S i j t, Filter.eventually_principal.mpr fun w hw => by
      have hwS : HeightOneSpectrum.under (𝓞 K) w ∉ S := hw
      show entryFun S i j t w ∈ _
      rw [entryFun_of_not_mem S i j t hwS]
      exact one_apply_mem w i j⟩

def entryAdele (i j : Fin 2) (t : (v : S) → Matrix (Fin 2) (Fin 2) (SL K L v.1)) :
    FiniteAdeleRing (𝓞 L) L :=
  RestrictedProduct.inclusion (fun w : HeightOneSpectrum (𝓞 L) => w.adicCompletion L)
    (fun w : HeightOneSpectrum (𝓞 L) => (w.adicCompletionIntegers L : Set (w.adicCompletion L)))
    (cofinite_le_principal_compl S) (entryPrincipal S i j t)

open scoped Classical in
theorem continuous_entryAdele (i j : Fin 2) : Continuous (entryAdele (K := K) (L := L) S i j) := by
  refine (RestrictedProduct.continuous_inclusion _).comp ?_
  refine RestrictedProduct.continuous_rng_of_principal_iff_forall.mpr fun w => ?_
  show Continuous fun t : (v : S) → Matrix (Fin 2) (Fin 2) (SL K L v.1) => entryFun S i j t w
  by_cases hw : HeightOneSpectrum.under (𝓞 K) w ∈ S
  · simp only [entryFun, dif_pos hw]
    exact (continuous_apply _).comp
      ((semiLocalHomeomorph K L (HeightOneSpectrum.under (𝓞 K) w)).continuous.comp
        ((continuous_apply _).matrix_elem i j))
  · simp only [entryFun, dif_neg hw]; exact continuous_const

def sMat (t : (v : S) → Matrix (Fin 2) (Fin 2) (SL K L v.1)) :
    Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 L) L) :=
  Matrix.of fun i j => entryAdele S i j t

theorem sMat_apply (t : (v : S) → Matrix (Fin 2) (Fin 2) (SL K L v.1)) (i j : Fin 2)
    (w : HeightOneSpectrum (𝓞 L)) : sMat S t i j w = entryFun S i j t w := rfl

theorem mapMatrix_sMat_of_mem (t : (v : S) → Matrix (Fin 2) (Fin 2) (SL K L v.1))
    {v : HeightOneSpectrum (𝓞 K)} (hv : v ∈ S) :
    (semiLocalEval K L v).mapMatrix (sMat S t) = t ⟨v, hv⟩ := by
  classical
  ext i j
  rw [RingHom.mapMatrix_apply, Matrix.map_apply, semiLocalEval_eq, AlgEquiv.symm_apply_eq]
  funext w
  obtain ⟨w, rfl⟩ := w
  rw [sMat_apply]
  simp only [entryFun, dif_pos hv]
  rfl

theorem mapMatrix_sMat_of_not_mem (t : (v : S) → Matrix (Fin 2) (Fin 2) (SL K L v.1))
    {v : HeightOneSpectrum (𝓞 K)} (hv : v ∉ S) :
    (semiLocalEval K L v).mapMatrix (sMat S t) = 1 := by
  classical
  ext i j
  rw [RingHom.mapMatrix_apply, Matrix.map_apply, semiLocalEval_eq, AlgEquiv.symm_apply_eq]
  funext w
  obtain ⟨w, rfl⟩ := w
  rw [sMat_apply, entryFun_of_not_mem S i j t hv]
  by_cases hij : i = j
  · subst hij
    rw [Matrix.one_apply_eq, Matrix.one_apply_eq, map_one]
    rfl
  · rw [Matrix.one_apply_ne hij, Matrix.one_apply_ne hij, map_zero]
    rfl

theorem sMat_one : sMat (K := K) (L := L) S (fun _ => (1 : Matrix (Fin 2) (Fin 2) _)) = 1 := by
  refine matrix_eq_of_forall_semiLocalEval_mapMatrix_eq K L fun v => ?_
  by_cases hv : v ∈ S
  · rw [mapMatrix_sMat_of_mem S _ hv, map_one]
  · rw [mapMatrix_sMat_of_not_mem S _ hv, map_one]

theorem sMat_mul (t t' : (v : S) → Matrix (Fin 2) (Fin 2) (SL K L v.1)) :
    sMat S (fun v => t v * t' v) = sMat S t * sMat S t' := by
  refine matrix_eq_of_forall_semiLocalEval_mapMatrix_eq K L fun v => ?_
  by_cases hv : v ∈ S
  · rw [map_mul, mapMatrix_sMat_of_mem S _ hv, mapMatrix_sMat_of_mem S _ hv, mapMatrix_sMat_of_mem S _ hv]
  · rw [map_mul, mapMatrix_sMat_of_not_mem S _ hv, mapMatrix_sMat_of_not_mem S _ hv,
      mapMatrix_sMat_of_not_mem S _ hv, mul_one]

def sEmbedFin : SProd K L S →* Gfin L where
  toFun t :=
    { val := sMat S fun v => (t v).val
      inv := sMat S fun v => ((t v)⁻¹).val
      val_inv := by
        rw [← sMat_mul]
        simp only [Units.mul_inv]
        exact sMat_one S
      inv_val := by
        rw [← sMat_mul]
        simp only [Units.inv_mul]
        exact sMat_one S }
  map_one' := Units.ext (by simp only [Units.val_one, Pi.one_apply]; exact sMat_one S)
  map_mul' t t' := Units.ext (by
    simp only [Units.val_mul, Pi.mul_apply]
    exact sMat_mul S _ _)

theorem coe_sEmbedFin (t : SProd K L S) :
    (sEmbedFin S t).val = sMat S fun v => (t v).val :=
  rfl

theorem semiLocalComponent_sEmbedFin_of_mem (t : SProd K L S) {v : HeightOneSpectrum (𝓞 K)} (hv : v ∈ S) :
    semiLocalComponent K L v (sEmbedFin S t) = t ⟨v, hv⟩ := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  have h := congrFun (congrFun (mapMatrix_sMat_of_mem S (fun v => (t v).val) hv) i) j
  rw [RingHom.mapMatrix_apply, Matrix.map_apply] at h
  rw [semiLocalComponent_apply, coe_sEmbedFin]
  exact h

theorem semiLocalComponent_sEmbedFin_of_not_mem (t : SProd K L S) {v : HeightOneSpectrum (𝓞 K)}
    (hv : v ∉ S) : semiLocalComponent K L v (sEmbedFin S t) = 1 := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  have h := congrFun (congrFun (mapMatrix_sMat_of_not_mem S (fun v => (t v).val) hv) i) j
  rw [RingHom.mapMatrix_apply, Matrix.map_apply] at h
  rw [semiLocalComponent_apply, coe_sEmbedFin, Units.val_one]
  exact h

theorem continuous_sEmbedFin : Continuous (sEmbedFin (K := K) (L := L) S) := by
  have hval : Continuous fun t : SProd K L S => (sEmbedFin S t).val := by
    refine continuous_matrix fun i j => ?_
    show Continuous fun t : SProd K L S => entryAdele S i j (fun v => (t v).val)
    refine (continuous_entryAdele S i j).comp (continuous_pi fun v => ?_)
    exact Units.continuous_val.comp (continuous_apply v)
  refine Units.continuous_iff.mpr ⟨hval, ?_⟩
  have h : (fun t : SProd K L S => ((sEmbedFin S t)⁻¹).val) =
      (fun t : SProd K L S => (sEmbedFin S t).val) ∘ fun t => t⁻¹ := by
    funext t; simp only [Function.comp_apply, map_inv]
  rw [h]
  exact hval.comp continuous_inv

theorem matrix_eq_of_arch_fin_eq {M N : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)}
    (h₁ : (adeleArch (𝓞 L) L).mapMatrix M = (adeleArch (𝓞 L) L).mapMatrix N)
    (h₂ : (adeleFin (𝓞 L) L).mapMatrix M = (adeleFin (𝓞 L) L).mapMatrix N) : M = N := by
  ext i j
  have hw₁ := congrFun (congrFun h₁ i) j
  have hw₂ := congrFun (congrFun h₂ i) j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, adeleArch_apply, adeleFin_apply] at hw₁ hw₂
  exact Prod.ext hw₁ hw₂

def pairMat (a : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing L)) (b : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 L) L)) :
    Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L) :=
  Matrix.of fun i j => ((a i j, b i j) : AdeleRing (𝓞 L) L)

theorem mapMatrix_arch_pairMat (a : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing L))
    (b : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 L) L)) :
    (adeleArch (𝓞 L) L).mapMatrix (pairMat a b) = a := by
  ext i j; rfl

theorem mapMatrix_fin_pairMat (a : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing L))
    (b : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 L) L)) :
    (adeleFin (𝓞 L) L).mapMatrix (pairMat a b) = b := by
  ext i j; rfl

theorem pairMat_one : pairMat (L := L) 1 1 = 1 :=
  matrix_eq_of_arch_fin_eq (by rw [mapMatrix_arch_pairMat, map_one])
    (by rw [mapMatrix_fin_pairMat, map_one])

theorem pairMat_mul (a a' : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing L))
    (b b' : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 L) L)) :
    pairMat (a * a') (b * b') = pairMat a b * pairMat a' b' :=
  matrix_eq_of_arch_fin_eq
    (by rw [map_mul, mapMatrix_arch_pairMat, mapMatrix_arch_pairMat, mapMatrix_arch_pairMat])
    (by rw [map_mul, mapMatrix_fin_pairMat, mapMatrix_fin_pairMat, mapMatrix_fin_pairMat])

def pairGL : Garch L × Gfin L →* Gad L where
  toFun x :=
    { val := pairMat (x.1 : Matrix (Fin 2) (Fin 2) _) (x.2 : Matrix (Fin 2) (Fin 2) _)
      inv := pairMat ((x.1⁻¹ : Garch L) : Matrix (Fin 2) (Fin 2) _) ((x.2⁻¹ : Gfin L) : Matrix (Fin 2) (Fin 2) _)
      val_inv := by rw [← pairMat_mul]; simp only [Units.mul_inv]; exact pairMat_one
      inv_val := by rw [← pairMat_mul]; simp only [Units.inv_mul]; exact pairMat_one }
  map_one' := Units.ext (by simp only [Units.val_one, Prod.fst_one, Prod.snd_one]; exact pairMat_one)
  map_mul' x y := Units.ext (by
    simp only [Units.val_mul, Prod.fst_mul, Prod.snd_mul]
    exact pairMat_mul _ _ _ _)

theorem glArch_pairGL (x : Garch L × Gfin L) : glArch (𝓞 L) L (pairGL x) = x.1 :=
  Matrix.GeneralLinearGroup.ext fun _ _ => rfl

theorem glFin_pairGL (x : Garch L × Gfin L) : glFin (𝓞 L) L (pairGL x) = x.2 :=
  Matrix.GeneralLinearGroup.ext fun _ _ => rfl

theorem pairGL_glArch_glFin (g : Gad L) : pairGL (glArch (𝓞 L) L g, glFin (𝓞 L) L g) = g :=
  Matrix.GeneralLinearGroup.ext fun _ _ => rfl

theorem continuous_pairGL : Continuous (pairGL (L := L)) := by
  have hval : ∀ (φ : Garch L × Gfin L → Garch L × Gfin L), Continuous φ →
      Continuous fun x => (pairGL (φ x)).val := by
    intro φ hφ
    refine continuous_matrix fun i j => ?_
    show Continuous fun x => (((φ x).1.val i j, (φ x).2.val i j) : AdeleRing (𝓞 L) L)
    exact ((Units.continuous_val.comp (continuous_fst.comp hφ)).matrix_elem i j).prodMk
      ((Units.continuous_val.comp (continuous_snd.comp hφ)).matrix_elem i j)
  refine Units.continuous_iff.mpr ⟨hval id continuous_id, ?_⟩
  have h : (fun x : Garch L × Gfin L => ((pairGL x)⁻¹).val) =
      fun x => (pairGL (x⁻¹)).val := by
    funext x; simp only [map_inv]
  rw [h]
  exact hval _ continuous_inv

abbrev bcG : Gt K L ≃ₜ* Gad L := baseChangeGLEquiv K L

abbrev bcH : Ht K L ≃ₜ* Garch L := archIdentGLEquiv K L

theorem glArch_bcG (x : Gt K L) : glArch (𝓞 L) L (bcG x) = bcH (tensorArch K L x) :=
  glArch_baseChangeGL K L x

theorem semiLocalComponent_glFin_bcG (v : HeightOneSpectrum (𝓞 K)) (x : Gt K L) :
    semiLocalComponent K L v (glFin (𝓞 L) L (bcG x)) = tensorPlace K L v x :=
  semiLocalComponent_glFin_baseChangeGL K L v x

theorem tensorArch_eq (x : Gt K L) : tensorArch K L x = (bcH (K := K) (L := L)).symm (glArch (𝓞 L) L (bcG x)) := by
  rw [eq_comm, ContinuousMulEquiv.symm_apply_eq, glArch_bcG]

theorem tensorPlace_eq (v : HeightOneSpectrum (𝓞 K)) (x : Gt K L) :
    tensorPlace K L v x = semiLocalComponent K L v (glFin (𝓞 L) L (bcG x)) :=
  (semiLocalComponent_glFin_bcG v x).symm

def fromLocL : LocProd K L S →* Gad L :=
  pairGL.comp ((bcH (K := K) (L := L)).toMulEquiv.toMonoidHom.prodMap (sEmbedFin S))

theorem glArch_fromLocL (x : LocProd K L S) : glArch (𝓞 L) L (fromLocL S x) = bcH x.1 :=
  glArch_pairGL _

theorem glFin_fromLocL (x : LocProd K L S) : glFin (𝓞 L) L (fromLocL S x) = sEmbedFin S x.2 :=
  glFin_pairGL _

def fromLoc : LocProd K L S →* Gt K L :=
  (bcG (K := K) (L := L)).symm.toMulEquiv.toMonoidHom.comp (fromLocL S)

theorem fromLoc_apply (x : LocProd K L S) : fromLoc S x = (bcG (K := K) (L := L)).symm (fromLocL S x) := rfl

theorem bcG_fromLoc (x : LocProd K L S) : bcG (fromLoc S x) = fromLocL S x := by
  rw [fromLoc_apply, ContinuousMulEquiv.apply_symm_apply]

theorem tensorArch_fromLoc (x : LocProd K L S) : tensorArch K L (fromLoc S x) = x.1 := by
  rw [tensorArch_eq, bcG_fromLoc, glArch_fromLocL, ContinuousMulEquiv.symm_apply_apply]

theorem tensorPlace_fromLoc_of_mem (x : LocProd K L S) {v : HeightOneSpectrum (𝓞 K)} (hv : v ∈ S) :
    tensorPlace K L v (fromLoc S x) = x.2 ⟨v, hv⟩ := by
  rw [tensorPlace_eq, bcG_fromLoc, glFin_fromLocL, semiLocalComponent_sEmbedFin_of_mem S _ hv]

theorem tensorPlace_fromLoc_of_not_mem (x : LocProd K L S) {v : HeightOneSpectrum (𝓞 K)} (hv : v ∉ S) :
    tensorPlace K L v (fromLoc S x) = 1 := by
  rw [tensorPlace_eq, bcG_fromLoc, glFin_fromLocL, semiLocalComponent_sEmbedFin_of_not_mem S _ hv]

theorem continuous_fromLoc : Continuous (fromLoc (K := K) (L := L) S) := by
  have h1 : Continuous (fromLocL (K := K) (L := L) S) :=
    continuous_pairGL.comp ((bcH (K := K) (L := L)).continuous.prodMap (continuous_sEmbedFin S))
  exact (bcG (K := K) (L := L)).symm.continuous.comp h1

def toLoc : Gt K L →* LocProd K L S :=
  MonoidHom.prod (tensorArch K L) (MonoidHom.pi fun v : S => tensorPlace K L v.1)

theorem toLoc_apply_fst (x : Gt K L) : (toLoc S x).1 = tensorArch K L x := rfl

theorem toLoc_apply_snd (x : Gt K L) (v : S) : (toLoc S x).2 v = tensorPlace K L v.1 x := rfl

theorem toLoc_fromLoc (x : LocProd K L S) : toLoc S (fromLoc S x) = x := by
  refine Prod.ext ?_ (funext fun v => ?_)
  · rw [toLoc_apply_fst, tensorArch_fromLoc]
  · rw [toLoc_apply_snd, tensorPlace_fromLoc_of_mem S x v.2]

theorem continuous_toLoc : Continuous (toLoc (K := K) (L := L) S) :=
  (continuous_tensorArch K L).prodMk (continuous_pi fun v => continuous_tensorPlace K L v.1)

end Embedding

section OpenKernel

variable (K L) in

def unitsAway : Subgroup (Gt K L) where
  carrier := {x | ∀ v ∉ S, tensorPlace K L v x ∈ semiLocalIntegralSet K L v}
  mul_mem' {g h} hg hh v hv := by
    rw [map_mul]
    exact mul_mem_semiLocalIntegralSet v (hg v hv) (hh v hv)
  one_mem' v _ := by rw [map_one]; exact one_mem_semiLocalIntegralSet K L v
  inv_mem' {g} hg v hv := by
    rw [map_inv]
    exact inv_mem_semiLocalIntegralSet v (hg v hv)

theorem mem_unitsAway_iff (x : Gt K L) :
    x ∈ unitsAway K L S ↔ ∀ v ∉ S, tensorPlace K L v x ∈ semiLocalIntegralSet K L v :=
  Iff.rfl

theorem fromLoc_mem_unitsAway (x : LocProd K L S) : fromLoc S x ∈ unitsAway K L S := fun v hv => by
  rw [tensorPlace_fromLoc_of_not_mem S x hv]
  exact one_mem_semiLocalIntegralSet K L v

theorem isOpen_unitsAway : IsOpen (unitsAway K L S : Set (Gt K L)) := by
  refine Subgroup.isOpen_of_mem_nhds (unitsAway K L S) (g := 1) ?_
  have h1 : (fun x : Gt K L => glFin (𝓞 L) L (bcG x)) ⁻¹' unitFinSet L ⊆ (unitsAway K L S : Set (Gt K L)) := by
    intro x hx v _
    rw [tensorPlace_eq]
    exact (forall_semiLocalComponent_mem_iff (K := K) _).2 hx v
  refine Filter.mem_of_superset ?_ h1
  refine ((isOpen_unitFinSet L).preimage
    ((continuous_glFin (𝓞 L) L).comp (bcG (K := K) (L := L)).continuous)).mem_nhds ?_
  show glFin (𝓞 L) L (bcG (K := K) (L := L) 1) ∈ unitFinSet L
  rw [map_one, map_one]
  exact one_mem_unitFinSet L

theorem measurableSet_unitsAway : MeasurableSet (unitsAway K L S : Set (Gt K L)) :=
  (isOpen_unitsAway S).measurableSet

variable (K L) in

def kerSet : Set (Gt K L) :=
  {k | tensorArch K L k = 1 ∧ (∀ v ∈ S, tensorPlace K L v k = 1) ∧
    ∀ v, tensorPlace K L v k ∈ semiLocalIntegralSet K L v}

theorem kerSet_subset_preimage :
    kerSet K L S ⊆ (bcG (K := K) (L := L)) ⁻¹' (pairGL '' (({1} : Set (Garch L)) ×ˢ unitFinSet L)) := by
  intro k hk
  obtain ⟨h1, -, h3⟩ := hk
  refine ⟨(glArch (𝓞 L) L (bcG k), glFin (𝓞 L) L (bcG k)), ⟨?_, ?_⟩, pairGL_glArch_glFin _⟩
  · show glArch (𝓞 L) L (bcG k) ∈ ({1} : Set (Garch L))
    rw [glArch_bcG, h1, map_one]
    exact Set.mem_singleton 1
  · show glFin (𝓞 L) L (bcG k) ∈ unitFinSet L
    refine (forall_semiLocalComponent_mem_iff (K := K) _).1 fun v => ?_
    rw [← tensorPlace_eq]
    exact h3 v

theorem isClosed_kerSet : IsClosed (kerSet K L S) := by
  have h1 : IsClosed {k : Gt K L | tensorArch K L k = 1} :=
    isClosed_eq (continuous_tensorArch K L) continuous_const
  have h2 : IsClosed {k : Gt K L | ∀ v ∈ S, tensorPlace K L v k = 1} := by
    have : {k : Gt K L | ∀ v ∈ S, tensorPlace K L v k = 1} = ⋂ v ∈ S, {k | tensorPlace K L v k = 1} := by
      ext k; simp only [Set.mem_setOf_eq, Set.mem_iInter]
    rw [this]
    exact isClosed_biInter fun v _ => isClosed_eq (continuous_tensorPlace K L v) continuous_const
  have h3 : IsClosed {k : Gt K L | ∀ v, tensorPlace K L v k ∈ semiLocalIntegralSet K L v} := by
    have : {k : Gt K L | ∀ v, tensorPlace K L v k ∈ semiLocalIntegralSet K L v} =
        ⋂ v, tensorPlace K L v ⁻¹' semiLocalIntegralSet K L v := by
      ext k; simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage]
    rw [this]
    exact isClosed_iInter fun v =>
      (isCompact_semiLocalIntegralSet K L v).isClosed.preimage (continuous_tensorPlace K L v)
  have hK : kerSet K L S =
      ({k : Gt K L | tensorArch K L k = 1} ∩ {k : Gt K L | ∀ v ∈ S, tensorPlace K L v k = 1}) ∩
      {k : Gt K L | ∀ v, tensorPlace K L v k ∈ semiLocalIntegralSet K L v} := by
    ext k; simp only [kerSet, Set.mem_inter_iff, Set.mem_setOf_eq, and_assoc]
  rw [hK]
  exact (h1.inter h2).inter h3

theorem isCompact_kerSet : IsCompact (kerSet K L S) := by
  have hc : IsCompact (pairGL '' (({1} : Set (Garch L)) ×ˢ unitFinSet L)) :=
    (isCompact_singleton.prod (isCompact_unitFinSet L)).image continuous_pairGL
  exact ((bcG (K := K) (L := L)).toHomeomorph.isCompact_preimage.2 hc).of_isClosed_subset
    (isClosed_kerSet S) (kerSet_subset_preimage S)

end OpenKernel

section More

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

theorem mul_mem_semiLocalIntegralSet_iff_right (v : HeightOneSpectrum (𝓞 K)) {g h : Gsl K L v}
    (hh : h ∈ semiLocalIntegralSet K L v) : g * h ∈ semiLocalIntegralSet K L v ↔ g ∈ semiLocalIntegralSet K L v := by
  refine ⟨fun hgh => ?_, fun hg => mul_mem_semiLocalIntegralSet v hg hh⟩
  have := mul_mem_semiLocalIntegralSet v hgh (inv_mem_semiLocalIntegralSet v hh)
  rwa [mul_inv_cancel_right] at this

theorem isClosed_unitsAway : IsClosed (unitsAway K L S : Set (Gt K L)) := by
  have : (unitsAway K L S : Set (Gt K L)) = ⋂ v ∈ (↑S : Set (HeightOneSpectrum (𝓞 K)))ᶜ,
      tensorPlace K L v ⁻¹' semiLocalIntegralSet K L v := by
    ext g
    simp only [SetLike.mem_coe, mem_unitsAway_iff, Set.mem_iInter, Set.mem_preimage, Set.mem_compl_iff]
  rw [this]
  exact isClosed_biInter fun v _ =>
    (isCompact_semiLocalIntegralSet K L v).isClosed.preimage (continuous_tensorPlace K L v)

theorem eventually_finComponent_mem (h : Gfin L) :
    ∀ᶠ w in cofinite, finComponent (𝓞 L) L w h ∈ localIntegralSet L w := by
  have h1 : ∀ i j : Fin 2, ∀ᶠ w : HeightOneSpectrum (𝓞 L) in cofinite,
      ((h : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 L) L)) i j) w ∈ w.adicCompletionIntegers L :=
    fun i j => ((h : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 L) L)) i j).2
  have h2 : ∀ i j : Fin 2, ∀ᶠ w : HeightOneSpectrum (𝓞 L) in cofinite,
      (((h⁻¹ : Gfin L) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 L) L)) i j) w ∈ w.adicCompletionIntegers L :=
    fun i j => (((h⁻¹ : Gfin L) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 L) L)) i j).2
  have h1' : ∀ᶠ w : HeightOneSpectrum (𝓞 L) in cofinite, ∀ i j : Fin 2,
      ((h : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 L) L)) i j) w ∈ w.adicCompletionIntegers L :=
    eventually_all.2 fun i => eventually_all.2 fun j => h1 i j
  have h2' : ∀ᶠ w : HeightOneSpectrum (𝓞 L) in cofinite, ∀ i j : Fin 2,
      (((h⁻¹ : Gfin L) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 L) L)) i j) w ∈ w.adicCompletionIntegers L :=
    eventually_all.2 fun i => eventually_all.2 fun j => h2 i j
  filter_upwards [h1', h2'] with w hw1 hw2
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [finComponent_apply]
    exact hw1 i j
  · rw [← map_inv, finComponent_apply]
    exact hw2 i j

theorem finite_setOf_tensorPlace_not_mem (x : Gt K L) :
    {v | tensorPlace K L v x ∉ semiLocalIntegralSet K L v}.Finite := by
  have hfin := Filter.eventually_cofinite.1 (eventually_finComponent_mem (glFin (𝓞 L) L (bcG (K := K) x)))
  refine (hfin.image (HeightOneSpectrum.under (𝓞 K))).subset fun v hv => ?_
  rw [Set.mem_setOf_eq, tensorPlace_eq, semiLocalComponent_mem_iff, not_forall] at hv
  obtain ⟨w, hw⟩ := hv
  exact ⟨w.1, hw, w.2⟩

theorem mem_image_mul_of_mem (C : Set (LocProd K L S)) {a : Gt K L}
    (haU : a ∈ unitsAway K L S) (haC : toLoc S a ∈ C) :
    a ∈ (fun p : Gt K L × Gt K L => p.1 * p.2) '' ((fromLoc S '' C) ×ˢ kerSet K L S) := by
  set b := fromLoc S (toLoc S a) with hb
  refine ⟨(b, b⁻¹ * a), ⟨⟨toLoc S a, haC, rfl⟩, ?_⟩, mul_inv_cancel_left b a⟩
  have hinf : tensorArch K L (b⁻¹ * a) = 1 := by
    rw [map_mul, map_inv, hb, tensorArch_fromLoc, toLoc_apply_fst, inv_mul_cancel]
  have hfinS : ∀ v ∈ S, tensorPlace K L v (b⁻¹ * a) = 1 := by
    intro v hv
    rw [map_mul, map_inv, hb, tensorPlace_fromLoc_of_mem S _ hv, toLoc_apply_snd, inv_mul_cancel]
  have hfin : ∀ v, v ∉ S → tensorPlace K L v (b⁻¹ * a) = tensorPlace K L v a := by
    intro v hv
    rw [map_mul, map_inv, hb, tensorPlace_fromLoc_of_not_mem S _ hv, inv_one, one_mul]
  refine ⟨hinf, hfinS, fun v => ?_⟩
  by_cases hv : v ∈ S
  · rw [hfinS v hv]; exact one_mem_semiLocalIntegralSet K L v
  · rw [hfin v hv]; exact haU v hv

def box (Ca : Set (Ht K L)) (Cv : ∀ v : S, Set (Gsl K L v.1)) : Set (Gt K L) :=
  {x : Gt K L | tensorArch K L x ∈ Ca ∧ (∀ v : S, tensorPlace K L v.1 x ∈ Cv v) ∧
    ∀ v ∉ S, tensorPlace K L v x ∈ semiLocalIntegralSet K L v}

theorem box_eq (Ca : Set (Ht K L)) (Cv : ∀ v : S, Set (Gsl K L v.1)) :
    box S Ca Cv = (tensorArch K L ⁻¹' Ca ∩ ⋂ v : S, tensorPlace K L v.1 ⁻¹' Cv v) ∩ (unitsAway K L S : Set (Gt K L)) := by
  ext x
  simp only [box, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage, Set.mem_iInter, SetLike.mem_coe,
    mem_unitsAway_iff, and_assoc]

theorem isClosed_box {Ca : Set (Ht K L)} (hCa : IsClosed Ca) {Cv : ∀ v : S, Set (Gsl K L v.1)}
    (hCv : ∀ v, IsClosed (Cv v)) : IsClosed (box S Ca Cv) := by
  rw [box_eq]
  exact ((hCa.preimage (continuous_tensorArch K L)).inter
    (isClosed_iInter fun v => (hCv v).preimage (continuous_tensorPlace K L v.1))).inter (isClosed_unitsAway S)

theorem isCompact_box {Ca : Set (Ht K L)} (hCa : IsCompact Ca) {Cv : ∀ v : S, Set (Gsl K L v.1)}
    (hCv : ∀ v, IsCompact (Cv v)) : IsCompact (box S Ca Cv) := by
  have hCc : IsCompact (Ca ×ˢ Set.pi Set.univ Cv) := hCa.prod (isCompact_univ_pi hCv)
  have hbig : IsCompact ((fun p : Gt K L × Gt K L => p.1 * p.2) ''
      ((fromLoc S '' (Ca ×ˢ Set.pi Set.univ Cv)) ×ˢ kerSet K L S)) :=
    ((hCc.image (continuous_fromLoc S)).prod (isCompact_kerSet S)).image continuous_mul
  refine hbig.of_isClosed_subset (isClosed_box S hCa.isClosed fun v => (hCv v).isClosed) fun x hx => ?_
  refine mem_image_mul_of_mem S _ (fun v hv => hx.2.2 v hv) ?_
  rw [Set.mem_prod, toLoc_apply_fst, Set.mem_univ_pi]
  exact ⟨hx.1, fun v => hx.2.1 v⟩

end More

section Main

variable (σ : L ≃ₐ[K] L) (δ : Gt K L)

abbrev Tad : Subgroup (Gt K L) := twistedCentralizer K L (AdeleRing (𝓞 K) K) σ δ

abbrev Tarch : Subgroup (Ht K L) := twistedCentralizer K L (InfiniteAdeleRing K) σ (tensorArch K L δ)

abbrev Tv (v : HeightOneSpectrum (𝓞 K)) : Subgroup (Gsl K L v) :=
  twistedCentralizer K L (v.adicCompletion K) σ (tensorPlace K L v δ)

variable {σ δ}

theorem tensorArch_tconj (x : Gt K L) :
    tensorArch K L (x⁻¹ * δ * sigmaGL K L (AdeleRing (𝓞 K) K) σ x) =
      (tensorArch K L x)⁻¹ * tensorArch K L δ * sigmaGL K L (InfiniteAdeleRing K) σ (tensorArch K L x) := by
  rw [map_mul, map_mul, map_inv, tensorArch_sigmaGL]

theorem tensorPlace_tconj (v : HeightOneSpectrum (𝓞 K)) (x : Gt K L) :
    tensorPlace K L v (x⁻¹ * δ * sigmaGL K L (AdeleRing (𝓞 K) K) σ x) =
      (tensorPlace K L v x)⁻¹ * tensorPlace K L v δ *
        sigmaGL K L (v.adicCompletion K) σ (tensorPlace K L v x) := by
  rw [map_mul, map_mul, map_inv, tensorPlace_sigmaGL]

variable (σ δ)
variable (τ : Measure (Tad σ δ)) (τa : Measure (Tarch σ δ)) (τf : ∀ v : HeightOneSpectrum (𝓞 K), Measure (Tv σ δ v))
  (c : ℝ)
  (φ : Gt K L → ℂ) (φa : Ht K L → ℂ) (φS : ∀ v : HeightOneSpectrum (𝓞 K), Gsl K L v → ℂ)
  (wa : Ht K L → ℝ) (wf : ∀ v : HeightOneSpectrum (𝓞 K), Gsl K L v → ℝ)

def prodFn : Gt K L → ℝ :=
  (unitsAway K L S : Set (Gt K L)).indicator fun x =>
    c⁻¹ * (wa (tensorArch K L x) * ∏ v ∈ S, wf v (tensorPlace K L v x))

theorem prodFn_of_mem {x : Gt K L} (hx : x ∈ unitsAway K L S) :
    prodFn S c wa wf x = c⁻¹ * (wa (tensorArch K L x) * ∏ v ∈ S, wf v (tensorPlace K L v x)) :=
  Set.indicator_of_mem hx _

theorem prodFn_of_not_mem {x : Gt K L} (hx : x ∉ unitsAway K L S) : prodFn S c wa wf x = 0 :=
  Set.indicator_of_notMem hx _

theorem prodFn_nonneg (hc : 0 < c) (hwa : ∀ y, 0 ≤ wa y) (hwf : ∀ v ∈ S, ∀ y, 0 ≤ wf v y) (x : Gt K L) :
    0 ≤ prodFn S c wa wf x := by
  by_cases hx : x ∈ unitsAway K L S
  · rw [prodFn_of_mem S c wa wf hx]
    exact mul_nonneg (inv_nonneg.2 hc.le)
      (mul_nonneg (hwa _) (Finset.prod_nonneg fun v hv => hwf v hv _))
  · rw [prodFn_of_not_mem S c wa wf hx]

theorem measurable_prodFn (hwa : Measurable wa) (hwf : ∀ v ∈ S, Measurable (wf v)) :
    Measurable (prodFn S c wa wf) := by
  refine Measurable.indicator ?_ (measurableSet_unitsAway S)
  refine measurable_const.mul ((hwa.comp (continuous_tensorArch K L).measurable).mul ?_)
  exact Finset.measurable_prod S fun v hv => (hwf v hv).comp (continuous_tensorPlace K L v).measurable

theorem hasCompactSupport_prodFn (hwa : HasCompactSupport wa) (hwf : ∀ v ∈ S, HasCompactSupport (wf v)) :
    HasCompactSupport (prodFn S c wa wf) := by
  have hBc : IsCompact (box S (tsupport wa) fun v : S => tsupport (wf v.1)) :=
    isCompact_box S hwa fun v => hwf v.1 v.2
  have hBcl : IsClosed (box S (tsupport wa) fun v : S => tsupport (wf v.1)) :=
    isClosed_box S (isClosed_tsupport wa) fun v => isClosed_tsupport _
  refine HasCompactSupport.intro' hBc hBcl fun x hx => ?_
  by_cases hxU : x ∈ unitsAway K L S
  · rw [prodFn_of_mem S c wa wf hxU]
    have : ¬ (tensorArch K L x ∈ tsupport wa ∧ ∀ v : S, tensorPlace K L v.1 x ∈ tsupport (wf v.1)) := by
      intro h
      exact hx ⟨h.1, h.2, hxU⟩
    rw [not_and_or, not_forall] at this
    rcases this with h | ⟨v, hv⟩
    · rw [image_eq_zero_of_notMem_tsupport h, zero_mul, mul_zero]
    · have h0 : wf v.1 (tensorPlace K L v.1 x) = 0 := image_eq_zero_of_notMem_tsupport hv
      rw [Finset.prod_eq_zero (Finset.coe_mem v) h0, mul_zero, mul_zero]
  · exact prodFn_of_not_mem S c wa wf hxU

theorem integral_prodFn_translate_eq_one (hc : 0 < c)
    (hτ : ∀ (S' : Finset (HeightOneSpectrum (𝓞 K)))
        (W : Gt K L → ℂ) (Wa : Ht K L → ℂ) (WS : ∀ v : HeightOneSpectrum (𝓞 K), Gsl K L v → ℂ),
        AEStronglyMeasurable (fun t : Tarch σ δ => Wa t) τa →
        (∀ v ∈ S', AEStronglyMeasurable (fun t : Tv σ δ v => WS v t) (τf v)) →
        (∀ t : Tad σ δ, (∀ v ∉ S', tensorPlace K L v (t : Gt K L) ∈ semiLocalIntegralSet K L v) →
            W t = Wa (tensorArch K L (t : Gt K L)) * ∏ v ∈ S', WS v (tensorPlace K L v (t : Gt K L))) →
        (∀ t : Tad σ δ, (∃ v ∉ S', tensorPlace K L v (t : Gt K L) ∉ semiLocalIntegralSet K L v) → W t = 0) →
          ∫ t, W t ∂τ = c * (∫ t, Wa t ∂τa) * ∏ v ∈ S', ∫ t, WS v t ∂(τf v))
    (hφ : ∀ g : Gt K L, (∀ v ∉ S, tensorPlace K L v g ∈ semiLocalIntegralSet K L v) →
        φ g = φa (tensorArch K L g) * ∏ v ∈ S, φS v (tensorPlace K L v g))
    (hφ0 : ∀ g : Gt K L, (∃ v ∉ S, tensorPlace K L v g ∉ semiLocalIntegralSet K L v) → φ g = 0)
    (hwam : Measurable wa)
    (hwa1 : ∀ y : Ht K L, φa (y⁻¹ * tensorArch K L δ * sigmaGL K L (InfiniteAdeleRing K) σ y) ≠ 0 →
      ∫ t : Tarch σ δ, wa ((t : Ht K L) * y) ∂τa = 1)
    (hwfm : ∀ v ∈ S, Measurable (wf v))
    (hwf1 : ∀ v ∈ S, ∀ y : Gsl K L v,
      φS v (y⁻¹ * tensorPlace K L v δ * sigmaGL K L (v.adicCompletion K) σ y) ≠ 0 →
      ∫ t : Tv σ δ v, wf v ((t : Gsl K L v) * y) ∂(τf v) = 1)
    (hunit : ∀ v ∉ S, ∀ y : Gsl K L v,
      y⁻¹ * tensorPlace K L v δ * sigmaGL K L (v.adicCompletion K) σ y ∈ semiLocalIntegralSet K L v →
      ∫ t : Tv σ δ v, (semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℝ)) ((t : Gsl K L v) * y) ∂(τf v) = 1)
    (x : Gt K L) (hx : φ (x⁻¹ * δ * sigmaGL K L (AdeleRing (𝓞 K) K) σ x) ≠ 0) :
    ∫ t : Tad σ δ, prodFn S c wa wf ((t : Gt K L) * x) ∂τ = 1 := by
  classical
  set ξ : Gt K L := x⁻¹ * δ * sigmaGL K L (AdeleRing (𝓞 K) K) σ x with hξ

  have hint : ∀ v ∉ S, tensorPlace K L v ξ ∈ semiLocalIntegralSet K L v := by
    by_contra h
    push Not at h
    obtain ⟨v, hv, hv'⟩ := h
    exact hx (hφ0 _ ⟨v, hv, hv'⟩)
  have hφx : φ ξ = φa (tensorArch K L ξ) * ∏ v ∈ S, φS v (tensorPlace K L v ξ) := hφ _ hint
  have hφa : φa ((tensorArch K L x)⁻¹ * tensorArch K L δ *
      sigmaGL K L (InfiniteAdeleRing K) σ (tensorArch K L x)) ≠ 0 := by
    rw [← tensorArch_tconj]
    intro h
    rw [hφx, h, zero_mul] at hx
    exact hx rfl
  have hφS : ∀ v ∈ S, φS v ((tensorPlace K L v x)⁻¹ * tensorPlace K L v δ *
      sigmaGL K L (v.adicCompletion K) σ (tensorPlace K L v x)) ≠ 0 := by
    intro v hv h
    rw [← tensorPlace_tconj] at h
    rw [hφx, Finset.prod_eq_zero hv h, mul_zero] at hx
    exact hx rfl

  set B : Finset (HeightOneSpectrum (𝓞 K)) := (finite_setOf_tensorPlace_not_mem x).toFinset \ S with hB
  have hBS : Disjoint S B := Finset.disjoint_sdiff
  have hmemB : ∀ v, v ∈ B ↔ tensorPlace K L v x ∉ semiLocalIntegralSet K L v ∧ v ∉ S := fun v => by
    rw [hB, Finset.mem_sdiff, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  set Sx : Finset (HeightOneSpectrum (𝓞 K)) := S ∪ B with hSx
  have hSSx : S ⊆ Sx := Finset.subset_union_left
  have hxint : ∀ v ∉ Sx, tensorPlace K L v x ∈ semiLocalIntegralSet K L v := by
    intro v hv
    by_contra h
    have hvS : v ∉ S := fun h' => hv (hSSx h')
    exact hv (Finset.mem_union_right _ ((hmemB v).2 ⟨h, hvS⟩))

  let Wa : Ht K L → ℂ := fun y => ((c⁻¹ * wa (y * tensorArch K L x) : ℝ) : ℂ)
  let WS : ∀ v : HeightOneSpectrum (𝓞 K), Gsl K L v → ℂ := fun v y =>
    if v ∈ S then ((wf v (y * tensorPlace K L v x) : ℝ) : ℂ)
    else (((semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℝ)) (y * tensorPlace K L v x) : ℝ) : ℂ)
  let W : Gt K L → ℂ := fun g => ((prodFn S c wa wf (g * x) : ℝ) : ℂ)

  have hWa : AEStronglyMeasurable (fun t : Tarch σ δ => Wa t) τa := by
    refine (Complex.measurable_ofReal.comp ?_).aestronglyMeasurable
    refine measurable_const.mul (hwam.comp ?_)
    exact (continuous_subtype_val.mul continuous_const).measurable
  have hWS : ∀ v ∈ Sx, AEStronglyMeasurable (fun t : Tv σ δ v => WS v t) (τf v) := by
    intro v _
    by_cases hv : v ∈ S
    · have : (fun t : Tv σ δ v => WS v t) = fun t : Tv σ δ v =>
          ((wf v ((t : Gsl K L v) * tensorPlace K L v x) : ℝ) : ℂ) := by
        funext t; simp only [WS, if_pos hv]
      rw [this]
      refine (Complex.measurable_ofReal.comp ((hwfm v hv).comp ?_)).aestronglyMeasurable
      exact (continuous_subtype_val.mul continuous_const).measurable
    · have : (fun t : Tv σ δ v => WS v t) = fun t : Tv σ δ v =>
          (((semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℝ))
            ((t : Gsl K L v) * tensorPlace K L v x) : ℝ) : ℂ) := by
        funext t; simp only [WS, if_neg hv]
      rw [this]
      refine (Complex.measurable_ofReal.comp ((measurable_const.indicator
        (isOpen_semiLocalIntegralSet K L v).measurableSet).comp ?_)).aestronglyMeasurable
      exact (continuous_subtype_val.mul continuous_const).measurable

  have hshape : ∀ t : Tad σ δ, (∀ v ∉ Sx, tensorPlace K L v (t : Gt K L) ∈ semiLocalIntegralSet K L v) →
      W t = Wa (tensorArch K L (t : Gt K L)) * ∏ v ∈ Sx, WS v (tensorPlace K L v (t : Gt K L)) := by
    intro t ht
    have hprodSx : ∏ v ∈ Sx, WS v (tensorPlace K L v (t : Gt K L)) =
        (∏ v ∈ S, ((wf v (tensorPlace K L v (t : Gt K L) * tensorPlace K L v x) : ℝ) : ℂ)) *
          ∏ v ∈ B, (((semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℝ))
            (tensorPlace K L v (t : Gt K L) * tensorPlace K L v x) : ℝ) : ℂ) := by
      rw [hSx, Finset.prod_union hBS]
      congr 1
      · exact Finset.prod_congr rfl fun v hv => by simp only [WS, if_pos hv]
      · exact Finset.prod_congr rfl fun v hv => by simp only [WS, if_neg ((hmemB v).1 hv).2]
    by_cases htx : (t : Gt K L) * x ∈ unitsAway K L S
    · have hB1 : ∏ v ∈ B, (((semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℝ))
          (tensorPlace K L v (t : Gt K L) * tensorPlace K L v x) : ℝ) : ℂ) = 1 := by
        refine Finset.prod_eq_one fun v hv => ?_
        have hvS : v ∉ S := ((hmemB v).1 hv).2
        have : tensorPlace K L v (t : Gt K L) * tensorPlace K L v x ∈ semiLocalIntegralSet K L v := by
          rw [← map_mul]; exact htx v hvS
        rw [Set.indicator_of_mem this, Complex.ofReal_one]
      simp only [W]
      rw [prodFn_of_mem S c wa wf htx, hprodSx, hB1, mul_one, map_mul, Complex.ofReal_mul,
        Complex.ofReal_mul, Complex.ofReal_prod]
      simp only [Wa, map_mul, Complex.ofReal_mul]
      ring
    · obtain ⟨v, hvS, hv⟩ : ∃ v ∉ S, tensorPlace K L v ((t : Gt K L) * x) ∉ semiLocalIntegralSet K L v := by
        by_contra h
        push Not at h
        exact htx h
      have hvSx : v ∈ Sx := by
        by_contra h'
        rw [map_mul] at hv
        exact hv (mul_mem_semiLocalIntegralSet v (ht v h') (hxint v h'))
      have hvB : v ∈ B := by
        rcases Finset.mem_union.1 hvSx with h | h
        · exact absurd h hvS
        · exact h
      have hB0 : ∏ v ∈ B, (((semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℝ))
          (tensorPlace K L v (t : Gt K L) * tensorPlace K L v x) : ℝ) : ℂ) = 0 := by
        refine Finset.prod_eq_zero hvB ?_
        rw [← map_mul, Set.indicator_of_notMem hv, Complex.ofReal_zero]
      simp only [W]
      rw [prodFn_of_not_mem S c wa wf htx, hprodSx, hB0, mul_zero, mul_zero, Complex.ofReal_zero]
  have hvanish : ∀ t : Tad σ δ, (∃ v ∉ Sx, tensorPlace K L v (t : Gt K L) ∉ semiLocalIntegralSet K L v) →
      W t = 0 := by
    rintro t ⟨v, hv, hvt⟩
    have hvS : v ∉ S := fun h => hv (hSSx h)
    have htx : (t : Gt K L) * x ∉ unitsAway K L S := by
      intro h
      have := h v hvS
      rw [map_mul, mul_mem_semiLocalIntegralSet_iff_right v (hxint v hv)] at this
      exact hvt this
    simp only [W]
    rw [prodFn_of_not_mem S c wa wf htx, Complex.ofReal_zero]

  have key := hτ Sx W Wa WS hWa hWS hshape hvanish
  have hIa : ∫ t : Tarch σ δ, Wa t ∂τa = ((c⁻¹ : ℝ) : ℂ) := by
    simp only [Wa]
    rw [integral_complex_ofReal, integral_const_mul, hwa1 _ hφa, mul_one]
  have hIS : ∏ v ∈ Sx, ∫ t : Tv σ δ v, WS v t ∂(τf v) = 1 := by
    refine Finset.prod_eq_one fun v _ => ?_
    by_cases hv : v ∈ S
    · simp only [WS, if_pos hv]
      rw [integral_complex_ofReal, hwf1 v hv _ (hφS v hv), Complex.ofReal_one]
    · simp only [WS, if_neg hv]
      rw [integral_complex_ofReal, hunit v hv _ (by rw [← tensorPlace_tconj]; exact hint v hv),
        Complex.ofReal_one]
  rw [hIa, hIS, mul_one, ← Complex.ofReal_mul, mul_inv_cancel₀ hc.ne'] at key
  have hW : ∫ t : Tad σ δ, W t ∂τ = ((∫ t : Tad σ δ, prodFn S c wa wf ((t : Gt K L) * x) ∂τ : ℝ) : ℂ) := by
    simp only [W]
    exact integral_complex_ofReal
  rw [hW, Complex.ofReal_one] at key
  exact_mod_cast key

end Main

end AutomorphicForm.BaseChangeProductSectionFn
p2m_reactivate "P2MW.S_AutomorphicForm_isTwistedSectionFnOn_baseChange_indicator_prod_of_forall_isTwistedSectionFnOn.AutomorphicForm P2MW.S_AutomorphicForm_isTwistedSectionFnOn_baseChange_indicator_prod_of_forall_isTwistedSectionFnOn.AutomorphicForm.BaseChangeProductSectionFn"
p2m_reactivate "P2MW.S_AutomorphicForm_isTwistedSectionFnOn_baseChange_indicator_prod_of_forall_isTwistedSectionFnOn.AutomorphicForm"

end
p2m_reactivate "P2MW.S_AutomorphicForm_isTwistedSectionFnOn_baseChange_indicator_prod_of_forall_isTwistedSectionFnOn.AutomorphicForm P2MW.S_AutomorphicForm_isTwistedSectionFnOn_baseChange_indicator_prod_of_forall_isTwistedSectionFnOn.AutomorphicForm.BaseChangeProductSectionFn"

section Solution

open MeasureTheory NumberField IsDedekindDomain
open AutomorphicForm.BaseChangeProductSectionFn
open scoped TensorProduct TensorProduct.RightActions

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (σ : L ≃ₐ[K] L) (δ : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))
    (τ : @Measure (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ δ)
      (AutomorphicForm.twistedCentralizerBorel K L (AdeleRing (𝓞 K) K) σ δ))
    (τa : @Measure (AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ
        (AutomorphicForm.tensorArch K L δ))
      (AutomorphicForm.twistedCentralizerBorel K L (InfiniteAdeleRing K) σ
        (AutomorphicForm.tensorArch K L δ)))
    (τf : ∀ v : HeightOneSpectrum (𝓞 K),
      @Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ
          (AutomorphicForm.tensorPlace K L v δ))
        (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ
          (AutomorphicForm.tensorPlace K L v δ)))
    (c : ℝ) (hc : 0 < c)
    (hτ : ∀ (S : Finset (HeightOneSpectrum (𝓞 K)))
        (W : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) → ℂ)
        (Wa : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) → ℂ)
        (WS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ),
        AEStronglyMeasurable[AutomorphicForm.twistedCentralizerBorel K L (InfiniteAdeleRing K) σ
          (AutomorphicForm.tensorArch K L δ)] (fun t => Wa t) τa →
        (∀ v ∈ S, AEStronglyMeasurable[AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ
          (AutomorphicForm.tensorPlace K L v δ)] (fun t => WS v t) (τf v)) →
        (∀ t : AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ δ,
          (∀ v ∉ S, AutomorphicForm.tensorPlace K L v t ∈ AutomorphicForm.semiLocalIntegralSet K L v) →
            W t = Wa (AutomorphicForm.tensorArch K L t) *
              ∏ v ∈ S, WS v (AutomorphicForm.tensorPlace K L v t)) →
        (∀ t : AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ δ,
          (∃ v ∉ S, AutomorphicForm.tensorPlace K L v t ∉ AutomorphicForm.semiLocalIntegralSet K L v) →
            W t = 0) →
          ∫ t, W t ∂τ = c * (∫ t, Wa t ∂τa) * ∏ v ∈ S, ∫ t, WS v t ∂(τf v))
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (φ : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) → ℂ) (φa : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) → ℂ)
    (φS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ)
    (hφ : ∀ x : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K),
      (∀ v ∉ S, AutomorphicForm.tensorPlace K L v x ∈ AutomorphicForm.semiLocalIntegralSet K L v) →
        φ x = φa (AutomorphicForm.tensorArch K L x) *
          ∏ v ∈ S, φS v (AutomorphicForm.tensorPlace K L v x))
    (hφ0 : ∀ x : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K),
      (∃ v ∉ S, AutomorphicForm.tensorPlace K L v x ∉ AutomorphicForm.semiLocalIntegralSet K L v) →
        φ x = 0)
    (wa : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) → ℝ)
    (hwa : AutomorphicForm.IsTwistedSectionFnOn K L (InfiniteAdeleRing K) σ
      (AutomorphicForm.tensorArch K L δ) τa φa wa)
    (wf : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℝ)
    (hwf : ∀ v ∈ S, AutomorphicForm.IsTwistedSectionFnOn K L (v.adicCompletion K) σ
      (AutomorphicForm.tensorPlace K L v δ) (τf v) (φS v) (wf v))
    (hunit : ∀ v ∉ S, AutomorphicForm.IsTwistedSectionFnOn K L (v.adicCompletion K) σ
      (AutomorphicForm.tensorPlace K L v δ) (τf v)
      ((AutomorphicForm.semiLocalIntegralSet K L v).indicator fun _ => (1 : ℂ))
      ((AutomorphicForm.semiLocalIntegralSet K L v).indicator fun _ => (1 : ℝ))) :
    AutomorphicForm.IsTwistedSectionFnOn K L (AdeleRing (𝓞 K) K) σ δ τ φ
      ({x : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) |
          ∀ v ∉ S, AutomorphicForm.tensorPlace K L v x ∈ AutomorphicForm.semiLocalIntegralSet K L v}.indicator
        fun x => c⁻¹ * (wa (AutomorphicForm.tensorArch K L x) *
          ∏ v ∈ S, wf v (AutomorphicForm.tensorPlace K L v x))) := by
  obtain ⟨hwa0, hwam, hwac, hwa1⟩ := hwa
  have hwf0 : ∀ v ∈ S, ∀ y, 0 ≤ wf v y := fun v hv => (hwf v hv).1
  have hwfm : ∀ v ∈ S, Measurable (wf v) := fun v hv => (hwf v hv).2.1
  have hwfc : ∀ v ∈ S, HasCompactSupport (wf v) := fun v hv => (hwf v hv).2.2.1
  have hwf1 : ∀ v ∈ S, ∀ y : Gsl K L v,
      φS v (y⁻¹ * AutomorphicForm.tensorPlace K L v δ * AutomorphicForm.sigmaGL K L (v.adicCompletion K) σ y) ≠ 0 →
      ∫ t : Tv σ δ v, wf v ((t : Gsl K L v) * y) ∂(τf v) = 1 := fun v hv => (hwf v hv).2.2.2
  have hunit' : ∀ v ∉ S, ∀ y : Gsl K L v,
      y⁻¹ * AutomorphicForm.tensorPlace K L v δ * AutomorphicForm.sigmaGL K L (v.adicCompletion K) σ y ∈
        AutomorphicForm.semiLocalIntegralSet K L v →
      ∫ t : Tv σ δ v, (AutomorphicForm.semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℝ))
        ((t : Gsl K L v) * y) ∂(τf v) = 1 := by
    intro v hv y hy
    refine (hunit v hv).2.2.2 y ?_
    rw [Set.indicator_of_mem hy]
    exact one_ne_zero
  show (∀ x, 0 ≤ prodFn S c wa wf x) ∧ Measurable (prodFn S c wa wf) ∧ HasCompactSupport (prodFn S c wa wf) ∧
    ∀ x, φ (x⁻¹ * δ * AutomorphicForm.sigmaGL K L (AdeleRing (𝓞 K) K) σ x) ≠ 0 →
      ∫ t : Tad σ δ, prodFn S c wa wf ((t : Gt K L) * x) ∂τ = 1
  exact ⟨prodFn_nonneg S c wa wf hc hwa0 hwf0, measurable_prodFn S c wa wf hwam hwfm,
    hasCompactSupport_prodFn S c wa wf hwac hwfc,
    fun x hx => integral_prodFn_translate_eq_one S σ δ τ τa τf c φ φa φS wa wf hc hτ hφ hφ0 hwam hwa1 hwfm
      hwf1 hunit' x hx⟩

end Solution
p2m_reactivate "P2MW.S_AutomorphicForm_isTwistedSectionFnOn_baseChange_indicator_prod_of_forall_isTwistedSectionFnOn.AutomorphicForm P2MW.S_AutomorphicForm_isTwistedSectionFnOn_baseChange_indicator_prod_of_forall_isTwistedSectionFnOn.AutomorphicForm.BaseChangeProductSectionFn"

end S_AutomorphicForm_isTwistedSectionFnOn_baseChange_indicator_prod_of_forall_isTwistedSectionFnOn
end P2MW
export P2MW.S_AutomorphicForm_isTwistedSectionFnOn_baseChange_indicator_prod_of_forall_isTwistedSectionFnOn (solution)
