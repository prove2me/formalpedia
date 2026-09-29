-- Prove2me | solution 1 for AutomorphicForm.exists_isCompact_setOf_mem_centralizer_normString_twistedConj_mem_subset_twistedCentralizer_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/053213b5-1ec6-5443-ac3a-4341b3d28fea

import Theorems.Thm_AutomorphicForm_exists_isCompact_setOf_mem_centralizer_normString_twistedConj_mem_subset_twistedCentralizer_mul_of_isArtinianRing
import Theorems.Thm_AutomorphicForm_setOf_mem_centralizer_normString_twistedConj_mem_semiLocalIntegralSet_subset_twistedCentralizer_mul_of_ramificationIdx_eq_one
import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_isCompact_setOf_mem_centralizer_normString_twistedConj_mem_subset_twistedCentralizer_mul

set_option autoImplicit false

open IsDedekindDomain NumberField Topology TopologicalSpace Set Filter
open NumberField.AdelicLevel TensorProduct
open scoped TensorProduct.RightActions Pointwise

noncomputable section

namespace AutomorphicForm
p2m_export "AutomorphicForm" "exists_isCompact_setOf_mem_centralizer_normString_twistedConj_mem_subset_twistedCentralizer_mul_of_isArtinianRing isTopologicalRing_tensor t2Space_tensor locallyCompactSpace_tensor isTopologicalGroup_tensorGL locallyCompactSpace_tensorGL semiLocalHomeomorph piIntegers semiLocalIntegers semiLocalIntegers_eq_preimage semiLocalIntegralSet one_mem_semiLocalIntegralSet isCompact_semiLocalIntegralSet sigmaGL normString twistedCentralizer semiLocalEval semiLocalComponent integralUnitsSet mem_integralUnitsSet localIntegralSet mem_localIntegralSet unitFinSet one_mem_unitFinSet isCompact_unitFinSet isOpen_unitFinSet IsRegularSemisimple mem_sigmaCentralizer_iff setOf_mem_centralizer_normString_twistedConj_mem_semiLocalIntegralSet_subset_twistedCentralizer_mul_of_ramificationIdx_eq_one tensorArchHom tensorPlaceHom tensorArch tensorPlace tensorPlace_apply glArch_baseChangeGL semiLocalComponent_glFin_baseChangeGL tensorArch_sigmaGL tensorPlace_sigmaGL archIdentEquiv baseChangeGLEquiv archIdentGLEquiv semiLocalEval_eq semiLocalHomeomorph_eq continuous_tensorArch continuous_tensorPlace matrix_eq_of_forall_semiLocalEval_mapMatrix_eq eq_of_tensorArch_eq_of_forall_tensorPlace_eq"
namespace TwistedTorusProper
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

theorem mul_mem_semiLocalIntegralSet_iff_right (v : HeightOneSpectrum (𝓞 K)) {g h : Gsl K L v}
    (hh : h ∈ semiLocalIntegralSet K L v) : g * h ∈ semiLocalIntegralSet K L v ↔ g ∈ semiLocalIntegralSet K L v := by
  refine ⟨fun hgh => ?_, fun hg => mul_mem_semiLocalIntegralSet v hg hh⟩
  have := mul_mem_semiLocalIntegralSet v hgh (inv_mem_semiLocalIntegralSet v hh)
  rwa [mul_inv_cancel_right] at this

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

theorem unitsAway_mono {S S' : Finset (HeightOneSpectrum (𝓞 K))} (h : S ⊆ S') :
    unitsAway K L S ≤ unitsAway K L S' :=
  fun _ hg v hv => hg v fun h' => hv (h h')

theorem exists_finset_subset_unitsAway {C : Set (Gt K L)} (hC : IsCompact C) :
    ∃ S₀ : Finset (HeightOneSpectrum (𝓞 K)), C ⊆ (unitsAway K L S₀ : Set (Gt K L)) := by
  classical
  obtain ⟨t, ht⟩ := hC.elim_finite_subcover
    (fun S : Finset (HeightOneSpectrum (𝓞 K)) => (unitsAway K L S : Set (Gt K L)))
    (fun S => isOpen_unitsAway S)
    (fun g _ => Set.mem_iUnion.2 ⟨(finite_setOf_tensorPlace_not_mem g).toFinset, fun v hv => by
      by_contra h
      exact hv ((Set.Finite.mem_toFinset _).2 h)⟩)
  refine ⟨t.biUnion id, fun g hg => ?_⟩
  obtain ⟨S, hS, hgS⟩ := Set.mem_iUnion₂.1 (ht hg)
  exact unitsAway_mono (fun v hv => Finset.mem_biUnion.2 ⟨S, hS, hv⟩) hgS

end More

theorem tensorPlace_normString (σ : L ≃ₐ[K] L) (v : HeightOneSpectrum (𝓞 K)) (δ : Gt K L) :
    tensorPlace K L v (normString K L (AdeleRing (𝓞 K) K) σ δ) =
      normString K L (v.adicCompletion K) σ (tensorPlace K L v δ) := by
  unfold normString
  rw [map_list_prod, List.map_map]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  show tensorPlace K L v ((⇑(sigmaGL K L (AdeleRing (𝓞 K) K) σ))^[i] δ) = _
  exact (Function.Semiconj.iterate_right (f := tensorPlace K L v)
    (ga := ⇑(sigmaGL K L (AdeleRing (𝓞 K) K) σ)) (gb := ⇑(sigmaGL K L (v.adicCompletion K) σ))
    (fun x => tensorPlace_sigmaGL K L σ v x) i).eq δ

theorem isRegularSemisimple_tensorPlace {g : Gt K L} (hg : IsRegularSemisimple g) (v : HeightOneSpectrum (𝓞 K)) :
    IsRegularSemisimple (tensorPlace K L v g) := by
  let φ : L ⊗[K] AdeleRing (𝓞 K) K →+* SL K L v := (tensorPlaceHom K L v).toRingHom
  have hval : ((tensorPlace K L v g : Gsl K L v) : Matrix (Fin 2) (Fin 2) (SL K L v)) =
      φ.mapMatrix (g : Matrix (Fin 2) (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) := by
    ext i j; rfl
  unfold IsRegularSemisimple
  rw [hval]
  have e : (φ.mapMatrix (g : Matrix (Fin 2) (Fin 2) _)).trace ^ 2 - 4 * (φ.mapMatrix (g : Matrix (Fin 2) (Fin 2) _)).det =
      φ ((g : Matrix (Fin 2) (Fin 2) _).trace ^ 2 - 4 * (g : Matrix (Fin 2) (Fin 2) _).det) := by
    rw [map_sub, map_pow, map_mul, map_ofNat, RingHom.map_det, AddMonoidHom.map_trace φ]
    rfl
  rw [e]
  exact hg.map φ

section Main

variable (σ : L ≃ₐ[K] L) (δ : Gt K L)

abbrev Tad : Subgroup (Gt K L) := twistedCentralizer K L (AdeleRing (𝓞 K) K) σ δ

abbrev Tarch : Subgroup (Ht K L) := twistedCentralizer K L (InfiniteAdeleRing K) σ (tensorArch K L δ)

abbrev Tv (v : HeightOneSpectrum (𝓞 K)) : Subgroup (Gsl K L v) :=
  twistedCentralizer K L (v.adicCompletion K) σ (tensorPlace K L v δ)

abbrev tconj (x : Gt K L) : Gt K L := x⁻¹ * δ * sigmaGL K L (AdeleRing (𝓞 K) K) σ x

variable {σ δ}

theorem tensorArch_tconj (x : Gt K L) :
    tensorArch K L (tconj σ δ x) =
      (tensorArch K L x)⁻¹ * tensorArch K L δ * sigmaGL K L (InfiniteAdeleRing K) σ (tensorArch K L x) := by
  rw [tconj, map_mul, map_mul, map_inv, tensorArch_sigmaGL]

theorem tensorPlace_tconj (v : HeightOneSpectrum (𝓞 K)) (x : Gt K L) :
    tensorPlace K L v (tconj σ δ x) =
      (tensorPlace K L v x)⁻¹ * tensorPlace K L v δ *
        sigmaGL K L (v.adicCompletion K) σ (tensorPlace K L v x) := by
  rw [tconj, map_mul, map_mul, map_inv, tensorPlace_sigmaGL]

theorem tensorPlace_mem_Tv (t : Tad σ δ) (v : HeightOneSpectrum (𝓞 K)) : tensorPlace K L v (t : Gt K L) ∈ Tv σ δ v := by
  have ht := (AutomorphicForm.mem_sigmaCentralizer_iff).1 t.2
  rw [AutomorphicForm.mem_sigmaCentralizer_iff, ← tensorPlace_sigmaGL, ← map_inv, ← map_mul, ← map_mul, ht]

theorem tensorArch_mem_Tarch (t : Tad σ δ) : tensorArch K L (t : Gt K L) ∈ Tarch σ δ := by
  have ht := (AutomorphicForm.mem_sigmaCentralizer_iff).1 t.2
  rw [AutomorphicForm.mem_sigmaCentralizer_iff, ← tensorArch_sigmaGL, ← map_inv, ← map_mul, ← map_mul, ht]

theorem tensorArch_normString (σ : L ≃ₐ[K] L) (δ : Gt K L) :
    tensorArch K L (normString K L (AdeleRing (𝓞 K) K) σ δ) =
      normString K L (InfiniteAdeleRing K) σ (tensorArch K L δ) := by
  unfold normString
  rw [map_list_prod, List.map_map]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  show tensorArch K L ((⇑(sigmaGL K L (AdeleRing (𝓞 K) K) σ))^[i] δ) = _
  exact (Function.Semiconj.iterate_right (f := tensorArch K L)
    (ga := ⇑(sigmaGL K L (AdeleRing (𝓞 K) K) σ)) (gb := ⇑(sigmaGL K L (InfiniteAdeleRing K) σ))
    (fun x => tensorArch_sigmaGL K L σ x) i).eq δ

theorem isRegularSemisimple_tensorArch {g : Gt K L} (hg : IsRegularSemisimple g) :
    IsRegularSemisimple (tensorArch K L g) := by
  let φ : L ⊗[K] AdeleRing (𝓞 K) K →+* L ⊗[K] InfiniteAdeleRing K := (tensorArchHom K L).toRingHom
  have hval : ((tensorArch K L g : Ht K L) : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) =
      φ.mapMatrix (g : Matrix (Fin 2) (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) := by
    ext i j; rfl
  unfold IsRegularSemisimple
  rw [hval]
  have e : (φ.mapMatrix (g : Matrix (Fin 2) (Fin 2) _)).trace ^ 2 - 4 * (φ.mapMatrix (g : Matrix (Fin 2) (Fin 2) _)).det =
      φ ((g : Matrix (Fin 2) (Fin 2) _).trace ^ 2 - 4 * (g : Matrix (Fin 2) (Fin 2) _).det) := by
    rw [map_sub, map_pow, map_mul, map_ofNat, RingHom.map_det, AddMonoidHom.map_trace φ]
    rfl
  rw [e]
  exact hg.map φ

theorem map_mem_centralizer {G H : Type*} [Group G] [Group H] (f : G →* H) {γ z : G}
    (hz : z ∈ Subgroup.centralizer ({γ} : Set G)) : f z ∈ Subgroup.centralizer ({f γ} : Set H) := by
  rw [Subgroup.mem_centralizer_singleton_iff] at hz ⊢
  rw [← map_mul, hz, map_mul]

theorem mem_Tad_of_components {t : Gt K L} (ha : tensorArch K L t ∈ Tarch σ δ)
    (hv : ∀ v : HeightOneSpectrum (𝓞 K), tensorPlace K L v t ∈ Tv σ δ v) : t ∈ Tad σ δ := by
  rw [AutomorphicForm.mem_sigmaCentralizer_iff]
  refine eq_of_tensorArch_eq_of_forall_tensorPlace_eq K L ?_ fun v => ?_
  · have h := (AutomorphicForm.mem_sigmaCentralizer_iff).1 ha
    rwa [map_mul, map_mul, map_inv, tensorArch_sigmaGL]
  · have h := (AutomorphicForm.mem_sigmaCentralizer_iff).1 (hv v)
    rwa [map_mul, map_mul, map_inv, tensorPlace_sigmaGL]

scoped instance instIsReducedSL (v : HeightOneSpectrum (𝓞 K)) : IsReduced (SL K L v) :=
  isReduced_of_injective (HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v)
    (HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v).injective

scoped instance instIsReducedInfiniteAdeleRing : IsReduced (InfiniteAdeleRing L) :=
  inferInstanceAs (IsReduced ((w : InfinitePlace L) → w.Completion))

scoped instance instIsReducedTI : IsReduced (L ⊗[K] InfiniteAdeleRing K) :=
  isReduced_of_injective (archIdentEquiv K L) (archIdentEquiv K L).injective

scoped instance instIsArtinianRingInfiniteAdeleRing : IsArtinianRing (InfiniteAdeleRing L) :=
  inferInstanceAs (IsArtinianRing ((w : InfinitePlace L) → w.Completion))

scoped instance instIsTopologicalRingInfiniteAdeleRing : IsTopologicalRing (InfiniteAdeleRing L) :=
  inferInstanceAs (IsTopologicalRing ((w : InfinitePlace L) → w.Completion))

theorem dvd_differentIdeal_of_ramificationIdx_ne_one (w : HeightOneSpectrum (𝓞 L))
    (hw : Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w).asIdeal w.asIdeal ≠ 1) :
    w.asIdeal ∣ differentIdeal (𝓞 K) (𝓞 L) := by
  set p : Ideal (𝓞 K) := (HeightOneSpectrum.under (𝓞 K) w).asIdeal with hp_def
  set e : ℕ := Ideal.ramificationIdx' p w.asIdeal with he_def
  have hp : p ≠ ⊥ := (HeightOneSpectrum.under (𝓞 K) w).ne_bot
  have hle : Ideal.map (algebraMap (𝓞 K) (𝓞 L)) p ≤ w.asIdeal := by
    rw [Ideal.map_le_iff_le_comap]
    exact le_rfl
  have hmap : Ideal.map (algebraMap (𝓞 K) (𝓞 L)) p ≠ ⊥ :=
    (Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective (𝓞 K) (𝓞 L))).not.2 hp
  have he0 : e ≠ 0 := Ideal.IsDedekindDomain.ramificationIdx_ne_zero hmap w.isPrime hle
  have hP : w.asIdeal ^ e ∣ Ideal.map (algebraMap (𝓞 K) (𝓞 L)) p :=
    Ideal.dvd_iff_le.2 Ideal.le_pow_ramificationIdx
  have h := pow_sub_one_dvd_differentIdeal_aux (𝓞 K) K L w.asIdeal he0 hp hP
  have he2 : e - 1 ≠ 0 := by
    intro h0
    apply hw
    omega
  exact (dvd_pow_self w.asIdeal he2).trans h

theorem finite_setOf_ramified :
    {v : HeightOneSpectrum (𝓞 K) | ¬ ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v →
      Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w).asIdeal w.asIdeal = 1}.Finite := by
  have hfin : {w : HeightOneSpectrum (𝓞 L) | w.asIdeal ∣ differentIdeal (𝓞 K) (𝓞 L)}.Finite :=
    Ideal.finite_factors differentIdeal_ne_bot
  refine (hfin.image (HeightOneSpectrum.under (𝓞 K))).subset fun v hv => ?_
  simp only [Set.mem_setOf_eq, not_forall, exists_prop] at hv
  obtain ⟨w, hwv, hw⟩ := hv
  exact ⟨w, dvd_differentIdeal_of_ramificationIdx_ne_one w hw, hwv⟩

def scalarGL {R : Type*} [CommRing R] (a : Rˣ) : GL (Fin 2) R :=
  Units.map (Matrix.scalar (Fin 2) : R →+* Matrix (Fin 2) (Fin 2) R).toMonoidHom a

theorem scalarGL_inv_apply {R : Type*} [CommRing R] (a : Rˣ) :
    (((scalarGL a)⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) 0 0 = ((a⁻¹ : Rˣ) : R) := by
  rw [scalarGL, ← map_inv, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe,
    Matrix.scalar_apply, Matrix.diagonal_apply_eq]

theorem exists_finset_disc_unit (σ : L ≃ₐ[K] L) (δ : Gt K L)
    (hδ : IsRegularSemisimple (normString K L (AdeleRing (𝓞 K) K) σ δ)) :
    ∃ Sd : Finset (HeightOneSpectrum (𝓞 K)), ∀ v ∉ Sd, ∃ u ∈ semiLocalIntegers K L v,
      u * (Matrix.trace ((normString K L (v.adicCompletion K) σ (tensorPlace K L v δ) : Gsl K L v) :
              Matrix (Fin 2) (Fin 2) (SL K L v)) ^ 2 -
            4 * Matrix.det ((normString K L (v.adicCompletion K) σ (tensorPlace K L v δ) : Gsl K L v) :
              Matrix (Fin 2) (Fin 2) (SL K L v))) = 1 := by
  obtain ⟨a, ha⟩ := hδ
  set g : Gt K L := scalarGL a with hg
  refine ⟨(finite_setOf_tensorPlace_not_mem g).toFinset, fun v hv => ?_⟩
  have hgv : tensorPlace K L v g ∈ semiLocalIntegralSet K L v := by
    by_contra h
    exact hv ((Set.Finite.mem_toFinset _).2 h)
  let φ : L ⊗[K] AdeleRing (𝓞 K) K →+* SL K L v := (tensorPlaceHom K L v).toRingHom
  refine ⟨φ ((a⁻¹ : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ) : L ⊗[K] AdeleRing (𝓞 K) K), ?_, ?_⟩
  · have h := hgv.2 0 0
    rw [← map_inv, tensorPlace_apply, scalarGL_inv_apply] at h
    exact h
  · rw [← tensorPlace_normString]
    have hval : ((tensorPlace K L v (normString K L (AdeleRing (𝓞 K) K) σ δ) : Gsl K L v) :
        Matrix (Fin 2) (Fin 2) (SL K L v)) =
        φ.mapMatrix ((normString K L (AdeleRing (𝓞 K) K) σ δ : Gt K L) : Matrix (Fin 2) (Fin 2) _) := by
      ext i j; rfl
    have e : (φ.mapMatrix ((normString K L (AdeleRing (𝓞 K) K) σ δ : Gt K L) : Matrix (Fin 2) (Fin 2) _)).trace ^ 2 -
        4 * (φ.mapMatrix ((normString K L (AdeleRing (𝓞 K) K) σ δ : Gt K L) : Matrix (Fin 2) (Fin 2) _)).det =
        φ (((normString K L (AdeleRing (𝓞 K) K) σ δ : Gt K L) : Matrix (Fin 2) (Fin 2) _).trace ^ 2 -
          4 * ((normString K L (AdeleRing (𝓞 K) K) σ δ : Gt K L) : Matrix (Fin 2) (Fin 2) _).det) := by
      rw [map_sub, map_pow, map_mul, map_ofNat, RingHom.map_det, AddMonoidHom.map_trace φ]
      rfl
    rw [hval, e, ← ha, ← map_mul, Units.inv_mul, map_one]

theorem main (hσ : σ ^ Module.finrank K L = 1)
    (hδ : IsRegularSemisimple (normString K L (AdeleRing (𝓞 K) K) σ δ))
    {C : Set (Gt K L)} (hC : IsCompact C) :
    ∃ D : Set (Gt K L), IsCompact D ∧
      {z : Gt K L | z ∈ Subgroup.centralizer ({normString K L (AdeleRing (𝓞 K) K) σ δ} : Set (Gt K L)) ∧
          tconj σ δ z ∈ C} ⊆ (Tad σ δ : Set (Gt K L)) * D := by
  classical
  set N : Gt K L := normString K L (AdeleRing (𝓞 K) K) σ δ with hN

  obtain ⟨S₀, hS₀⟩ := exists_finset_subset_unitsAway hC
  obtain ⟨Sd, hSd⟩ := exists_finset_disc_unit σ δ hδ
  set Sδ : Finset (HeightOneSpectrum (𝓞 K)) := (finite_setOf_tensorPlace_not_mem δ).toFinset with hSδ
  set Sr : Finset (HeightOneSpectrum (𝓞 K)) := (finite_setOf_ramified (K := K) (L := L)).toFinset with hSr
  set S : Finset (HeightOneSpectrum (𝓞 K)) := S₀ ∪ Sd ∪ Sδ ∪ Sr with hS
  have hS₀S : S₀ ⊆ S := by
    intro v hv; simp only [hS, Finset.mem_union]; exact Or.inl (Or.inl (Or.inl hv))
  have hδint : ∀ v ∉ S, tensorPlace K L v δ ∈ semiLocalIntegralSet K L v := by
    intro v hv
    by_contra h
    apply hv
    simp only [hS, Finset.mem_union]
    exact Or.inl (Or.inr ((Set.Finite.mem_toFinset _).2 h))
  have hram : ∀ v ∉ S, ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v →
      Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w).asIdeal w.asIdeal = 1 := by
    intro v hv
    by_contra h
    apply hv
    simp only [hS, Finset.mem_union]
    exact Or.inr ((Set.Finite.mem_toFinset _).2 h)
  have hdisc : ∀ v ∉ S, ∃ u ∈ semiLocalIntegers K L v,
      u * (Matrix.trace ((normString K L (v.adicCompletion K) σ (tensorPlace K L v δ) : Gsl K L v) :
              Matrix (Fin 2) (Fin 2) (SL K L v)) ^ 2 -
            4 * Matrix.det ((normString K L (v.adicCompletion K) σ (tensorPlace K L v δ) : Gsl K L v) :
              Matrix (Fin 2) (Fin 2) (SL K L v))) = 1 := by
    intro v hv
    refine hSd v fun h => hv ?_
    simp only [hS, Finset.mem_union]
    exact Or.inl (Or.inl (Or.inr h))

  have hregA : IsRegularSemisimple (normString K L (InfiniteAdeleRing K) σ (tensorArch K L δ)) := by
    rw [← tensorArch_normString]; exact isRegularSemisimple_tensorArch hδ
  have hregv : ∀ v : HeightOneSpectrum (𝓞 K),
      IsRegularSemisimple (normString K L (v.adicCompletion K) σ (tensorPlace K L v δ)) := fun v => by
    rw [← tensorPlace_normString]; exact isRegularSemisimple_tensorPlace hδ v
  obtain ⟨Da, hDac, hDa⟩ :=
    AutomorphicForm.exists_isCompact_setOf_mem_centralizer_normString_twistedConj_mem_subset_twistedCentralizer_mul_of_isArtinianRing
      K L (InfiniteAdeleRing K) σ hσ (tensorArch K L δ) hregA (tensorArch K L '' C)
      (hC.image (continuous_tensorArch K L))
  have hloc : ∀ v : HeightOneSpectrum (𝓞 K), ∃ Dv : Set (Gsl K L v), IsCompact Dv ∧
      {z : Gsl K L v | z ∈ Subgroup.centralizer
          ({normString K L (v.adicCompletion K) σ (tensorPlace K L v δ)} : Set (Gsl K L v)) ∧
        z⁻¹ * tensorPlace K L v δ * sigmaGL K L (v.adicCompletion K) σ z ∈ tensorPlace K L v '' C} ⊆
        (Tv σ δ v : Set (Gsl K L v)) * Dv := fun v =>
    AutomorphicForm.exists_isCompact_setOf_mem_centralizer_normString_twistedConj_mem_subset_twistedCentralizer_mul_of_isArtinianRing
      K L (v.adicCompletion K) σ hσ (tensorPlace K L v δ) (hregv v) (tensorPlace K L v '' C)
      (hC.image (continuous_tensorPlace K L v))
  choose Dv hDvc hDv using hloc

  set B : Set (LocProd K L S) := Da ×ˢ Set.univ.pi fun v : S => Dv v.1 with hB
  have hBc : IsCompact B := hDac.prod (isCompact_univ_pi fun v => hDvc v.1)
  refine ⟨(fromLoc S '' B) * kerSet K L S, (hBc.image (continuous_fromLoc S)).mul (isCompact_kerSet S), ?_⟩

  rintro z ⟨hzZ, hzC⟩
  have hyU : tconj σ δ z ∈ unitsAway K L S₀ := hS₀ hzC

  have ha : tensorArch K L z ∈ (Tarch σ δ : Set (Ht K L)) * Da := by
    refine hDa ⟨?_, ?_⟩
    · rw [← tensorArch_normString]
      exact map_mem_centralizer (tensorArch K L) hzZ
    · rw [← tensorArch_tconj]
      exact Set.mem_image_of_mem _ hzC
  obtain ⟨ta, hta, da, hda, hzad⟩ := Set.mem_mul.1 ha

  set Sz : Finset (HeightOneSpectrum (𝓞 K)) := S ∪ (finite_setOf_tensorPlace_not_mem z).toFinset with hSz
  have hzint : ∀ v ∉ Sz, tensorPlace K L v z ∈ semiLocalIntegralSet K L v := by
    intro v hv
    by_contra h
    apply hv
    simp only [hSz, Finset.mem_union]
    exact Or.inr ((Set.Finite.mem_toFinset _).2 h)
  have hSSz : S ⊆ Sz := Finset.subset_union_left
  have hloc : ∀ v : HeightOneSpectrum (𝓞 K), ∃ tv : Gsl K L v, tv ∈ Tv σ δ v ∧
      (v ∈ S → tv⁻¹ * tensorPlace K L v z ∈ Dv v) ∧
      (v ∉ S → tv⁻¹ * tensorPlace K L v z ∈ semiLocalIntegralSet K L v) ∧ (v ∉ Sz → tv = 1) := by
    intro v
    have hzZv : tensorPlace K L v z ∈ Subgroup.centralizer
        ({normString K L (v.adicCompletion K) σ (tensorPlace K L v δ)} : Set (Gsl K L v)) := by
      rw [← tensorPlace_normString]
      exact map_mem_centralizer (tensorPlace K L v) hzZ
    by_cases hvS : v ∈ S
    · have hmem : tensorPlace K L v z ∈ (Tv σ δ v : Set (Gsl K L v)) * Dv v := by
        refine hDv v ⟨hzZv, ?_⟩
        rw [← tensorPlace_tconj]
        exact Set.mem_image_of_mem _ hzC
      obtain ⟨tv, htv, dv, hdv, he⟩ := Set.mem_mul.1 hmem
      refine ⟨tv, htv, fun _ => ?_, fun h => (h hvS).elim, fun h => (h (hSSz hvS)).elim⟩
      rw [← he, inv_mul_cancel_left]
      exact hdv
    · by_cases hvz : v ∈ Sz
      · have hy : (tensorPlace K L v z)⁻¹ * tensorPlace K L v δ *
            sigmaGL K L (v.adicCompletion K) σ (tensorPlace K L v z) ∈ semiLocalIntegralSet K L v := by
          rw [← tensorPlace_tconj]
          exact hyU v fun h => hvS (hS₀S h)
        have hmem : tensorPlace K L v z ∈ (Tv σ δ v : Set (Gsl K L v)) * semiLocalIntegralSet K L v :=
          AutomorphicForm.setOf_mem_centralizer_normString_twistedConj_mem_semiLocalIntegralSet_subset_twistedCentralizer_mul_of_ramificationIdx_eq_one
            K L σ hσ v (hram v hvS) (tensorPlace K L v δ) (hδint v hvS) (hdisc v hvS) ⟨hzZv, hy⟩
        obtain ⟨tv, htv, dv, hdv, he⟩ := Set.mem_mul.1 hmem
        refine ⟨tv, htv, fun h => (hvS h).elim, fun _ => ?_, fun h => (h hvz).elim⟩
        rw [← he, inv_mul_cancel_left]
        exact hdv
      · refine ⟨1, (Tv σ δ v).one_mem, fun h => (hvS h).elim, fun _ => ?_, fun _ => rfl⟩
        rw [inv_one, one_mul]
        exact hzint v hvz
  choose tv htvT htvS htvS' htv1 using hloc

  set t : Gt K L := fromLoc Sz (ta, fun v : Sz => tv v.1) with ht_def
  have hta_eq : tensorArch K L t = ta := tensorArch_fromLoc Sz _
  have htv_eq : ∀ v : HeightOneSpectrum (𝓞 K), tensorPlace K L v t = tv v := by
    intro v
    by_cases hv : v ∈ Sz
    · exact tensorPlace_fromLoc_of_mem Sz _ hv
    · rw [tensorPlace_fromLoc_of_not_mem Sz _ hv, htv1 v hv]
  have htT : t ∈ Tad σ δ :=
    mem_Tad_of_components (by rw [hta_eq]; exact hta) fun v => by rw [htv_eq]; exact htvT v
  refine Set.mem_mul.2 ⟨t, htT, t⁻¹ * z, ?_, mul_inv_cancel_left t z⟩

  set d : Gt K L := t⁻¹ * z with hd_def
  have hda_eq : tensorArch K L d = da := by
    rw [hd_def, map_mul, map_inv, hta_eq, ← hzad, inv_mul_cancel_left]
  have hdv_eq : ∀ v : HeightOneSpectrum (𝓞 K), tensorPlace K L v d = (tv v)⁻¹ * tensorPlace K L v z := by
    intro v
    rw [hd_def, map_mul, map_inv, htv_eq]
  set e : Gt K L := fromLoc S (tensorArch K L d, fun v : S => tensorPlace K L v.1 d) with he_def
  refine Set.mem_mul.2 ⟨e, Set.mem_image_of_mem _ ⟨?_, ?_⟩, e⁻¹ * d, ⟨?_, ?_, ?_⟩, mul_inv_cancel_left e d⟩
  · show tensorArch K L d ∈ Da
    rw [hda_eq]; exact hda
  · show (fun v : S => tensorPlace K L v.1 d) ∈ Set.univ.pi fun v : S => Dv v.1
    refine Set.mem_univ_pi.2 fun v => ?_
    show tensorPlace K L v.1 d ∈ Dv v.1
    rw [hdv_eq]
    exact htvS v.1 v.2
  · rw [map_mul, map_inv, he_def, tensorArch_fromLoc, inv_mul_cancel]
  · intro v hv
    rw [map_mul, map_inv, he_def, tensorPlace_fromLoc_of_mem S _ hv, inv_mul_cancel]
  · intro v
    by_cases hv : v ∈ S
    · rw [map_mul, map_inv, he_def, tensorPlace_fromLoc_of_mem S _ hv, inv_mul_cancel]
      exact one_mem_semiLocalIntegralSet K L v
    · rw [map_mul, map_inv, he_def, tensorPlace_fromLoc_of_not_mem S _ hv, inv_one, one_mul, hdv_eq]
      exact htvS' v hv

end Main

end AutomorphicForm.TwistedTorusProper
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isCompact_setOf_mem_centralizer_normString_twistedConj_mem_subset_twistedCentralizer_mul.AutomorphicForm P2MW.S_AutomorphicForm_exists_isCompact_setOf_mem_centralizer_normString_twistedConj_mem_subset_twistedCentralizer_mul.AutomorphicForm.TwistedTorusProper"
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isCompact_setOf_mem_centralizer_normString_twistedConj_mem_subset_twistedCentralizer_mul.AutomorphicForm"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isCompact_setOf_mem_centralizer_normString_twistedConj_mem_subset_twistedCentralizer_mul.AutomorphicForm P2MW.S_AutomorphicForm_exists_isCompact_setOf_mem_centralizer_normString_twistedConj_mem_subset_twistedCentralizer_mul.AutomorphicForm.TwistedTorusProper"

open NumberField in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]
    (σ : L ≃ₐ[K] L) (hσ : σ ^ Module.finrank K L = 1)
    (δ : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))
    (hδ : AutomorphicForm.IsRegularSemisimple (AutomorphicForm.normString K L (AdeleRing (𝓞 K) K) σ δ))
    (C : Set (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))) (hC : IsCompact C) :
    ∃ D : Set (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)), IsCompact D ∧
      {z : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) |
          z ∈ Subgroup.centralizer
              ({AutomorphicForm.normString K L (AdeleRing (𝓞 K) K) σ δ} :
                Set (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))) ∧
            z⁻¹ * δ * AutomorphicForm.sigmaGL K L (AdeleRing (𝓞 K) K) σ z ∈ C} ⊆
        (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ δ :
            Set (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))) * D :=
  AutomorphicForm.TwistedTorusProper.main (σ := σ) (δ := δ) hσ hδ hC

end S_AutomorphicForm_exists_isCompact_setOf_mem_centralizer_normString_twistedConj_mem_subset_twistedCentralizer_mul
end P2MW
export P2MW.S_AutomorphicForm_exists_isCompact_setOf_mem_centralizer_normString_twistedConj_mem_subset_twistedCentralizer_mul (solution)
