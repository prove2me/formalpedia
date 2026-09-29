-- Prove2me | solution 1 for AutomorphicForm.exists_isTwistedOrbitalIntegralOn_baseChange_eq_mul_prod_of_isSemiLocalFactorization
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/63cc5b04-d39e-5bb3-84d3-ab345ab02c30

import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_NumberField_AdelicHaar
import Theorems.Thm_AutomorphicForm_exists_finset_forall_isTwistedSectionFnOn_indicator_semiLocalIntegralSet_of_isTwistedSectionFnOn_baseChange
import Theorems.Thm_AutomorphicForm_isTwistedSectionFnOn_baseChange_indicator_prod_of_forall_isTwistedSectionFnOn
import Theorems.Thm_AutomorphicForm_IsTwistedOrbitalIntegralOn_unique_of_isRegularSemisimple_normString
import Theorems.Thm_MeasureTheory_exists_hasCompactSupport_integral_subgroup_translate_eq_one_of_subset_mul
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_isTwistedOrbitalIntegralOn_baseChange_eq_mul_prod_of_isSemiLocalFactorization
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply"

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory MeasureTheory.Measure Topology TopologicalSpace Set Filter
open NumberField.AdelicLevel NumberField.AdelicHaar TensorProduct
open scoped TensorProduct.RightActions NNReal ENNReal Pointwise Classical

noncomputable section

namespace AutomorphicForm
p2m_export "AutomorphicForm" "tensorArch tensorPlace baseChangeGL glArch_baseChangeGL semiLocalComponent_glFin_baseChangeGL tensorArch_sigmaGL tensorPlace_sigmaGL baseChangeGLEquiv archIdentGLEquiv semiLocalEval_eq semiLocalHomeomorph_eq matrix_eq_of_forall_semiLocalEval_mapMatrix_eq isTopologicalRing_tensor t2Space_tensor locallyCompactSpace_tensor isTopologicalGroup_tensorGL t2Space_tensorGL locallyCompactSpace_tensorGL glBorelOf semiLocalHomeomorph piIntegers semiLocalIntegers semiLocalIntegers_eq_preimage zero_mem_semiLocalIntegers semiLocalIntegralSet isOpen_semiLocalIntegralSet semiLocalHaar semiLocalHaar_semiLocalIntegralSet sigmaTensor sigmaGL normString twistedCentralizer twistedCentralizerBorel IsTwistedSectionFnOn IsTwistedOrbitalIntegralOn IsTwistedOrbitalIntegral archIdentGL semiLocalEval semiLocalComponent IsSemiLocalFactorization integralUnitsSet mem_integralUnitsSet localIntegralSet mem_localIntegralSet unitFinSet IsRegularSemisimple archEntries IsArchTestFactor mem_sigmaCentralizer_iff exists_finset_forall_isTwistedSectionFnOn_indicator_semiLocalIntegralSet_of_isTwistedSectionFnOn_baseChange isTwistedSectionFnOn_baseChange_indicator_prod_of_forall_isTwistedSectionFnOn IsTwistedOrbitalIntegralOn.unique_of_isRegularSemisimple_normString"
namespace TwistedOrbitalEuler
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

scoped instance instT2Ht : T2Space (Ht K L) := t2Space_tensorGL K L _
scoped instance instT2Gsl (v : HeightOneSpectrum (𝓞 K)) : T2Space (Gsl K L v) := t2Space_tensorGL K L _
scoped instance instT2Gt : T2Space (Gt K L) := t2Space_tensorGL K L _
scoped instance instLocallyCompactTA : LocallyCompactSpace (L ⊗[K] AdeleRing (𝓞 K) K) := locallyCompactSpace_tensor K L _

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

end Embedding

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

end More

section Regular

variable {A : Type*} [CommRing A]

theorem entries_of_commute (g X : Matrix (Fin 2) (Fin 2) A) (h : X * g = g * X) (u : A)
    (hu : u * (Matrix.trace g ^ 2 - 4 * Matrix.det g) = 1) :
    ∃ α β : A, X = α • (1 : Matrix (Fin 2) (Fin 2) A) + β • g := by
  rw [Matrix.trace_fin_two, Matrix.det_fin_two] at hu
  have e00 := congrFun (congrFun h 0) 0
  have e01 := congrFun (congrFun h 0) 1
  have e10 := congrFun (congrFun h 1) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10
  let B : A := u * (2 * g 1 0 * X 0 1 + 2 * g 0 1 * X 1 0 + (g 0 0 - g 1 1) * (X 0 0 - X 1 1))
  refine ⟨X 0 0 - B * g 0 0, B, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, B, Fin.zero_eta,
      Fin.mk_one, Fin.isValue, if_true, one_ne_zero, zero_ne_one, if_false, mul_one, mul_zero, zero_add]
  · ring
  · linear_combination (-(X 0 1)) * hu - (u * (g 0 0 - g 1 1)) * e01 + (2 * u * g 0 1) * e00
  · linear_combination (-(X 1 0)) * hu + (u * (g 0 0 - g 1 1)) * e10 - (2 * u * g 1 0) * e00
  · linear_combination (X 0 0 - X 1 1) * hu - (2 * u * g 1 0) * e01 + (2 * u * g 0 1) * e10

theorem mul_comm_of_mem_centralizer {g : GL (Fin 2) A} (hg : IsRegularSemisimple g) {s z : GL (Fin 2) A}
    (hs : s ∈ Subgroup.centralizer ({g} : Set (GL (Fin 2) A)))
    (hz : z ∈ Subgroup.centralizer ({g} : Set (GL (Fin 2) A))) : s * z = z * s := by
  obtain ⟨u, hu⟩ := hg.exists_left_inv
  rw [Subgroup.mem_centralizer_singleton_iff] at hs hz
  have hs' : (s : Matrix (Fin 2) (Fin 2) A) * g = g * s := by rw [← Units.val_mul, hs, Units.val_mul]
  have hz' : (z : Matrix (Fin 2) (Fin 2) A) * g = g * z := by rw [← Units.val_mul, hz, Units.val_mul]
  obtain ⟨α, β, hS⟩ := entries_of_commute _ _ hs' u hu
  obtain ⟨α', β', hZ⟩ := entries_of_commute _ _ hz' u hu
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, hS, hZ]
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_add, smul_smul]
  rw [mul_comm α' α, mul_comm α' β, mul_comm β' α, mul_comm β' β]
  abel

theorem isRegularSemisimple_map {R T : Type*} [CommRing R] [CommRing T] (f : R →+* T)
    {g : GL (Fin 2) R} (hg : IsRegularSemisimple g) :
    IsRegularSemisimple (Matrix.GeneralLinearGroup.map f g) := by
  unfold IsRegularSemisimple at hg ⊢
  have hval : ((Matrix.GeneralLinearGroup.map f g : GL (Fin 2) T) : Matrix (Fin 2) (Fin 2) T) =
      f.mapMatrix (g : Matrix (Fin 2) (Fin 2) R) := rfl
  rw [hval, ← RingHom.map_det, RingHom.mapMatrix_apply, ← AddMonoidHom.map_trace]
  have := hg.map f
  simpa [map_ofNat] using this

theorem isMulRightInvariant_of_comm {G : Type*} [Group G] (T : Subgroup G) (hcomm : ∀ s t : T, s * t = t * s)
    [MeasurableSpace T] (τ : Measure T) [τ.IsMulLeftInvariant] : τ.IsMulRightInvariant := by
  refine ⟨fun g => ?_⟩
  have : (fun t : T => t * g) = fun t : T => g * t := funext fun t => hcomm t g
  rw [this]
  exact map_mul_left_eq_self τ g

theorem continuous_twistedConj {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (g : G)
    (s : G →* G) (hs : Continuous s) : Continuous fun x : G => x⁻¹ * g * s x :=
  (continuous_id.inv.mul continuous_const).mul hs

end Regular

section Twist

variable (K L) (A : Type) [CommRing A] [Algebra K A] (σ : L ≃ₐ[K] L)

omit [NumberField K] [NumberField L] in
theorem map_normString {B : Type} [CommRing B] [Algebra K B] (F : GL (Fin 2) (L ⊗[K] A) →* GL (Fin 2) (L ⊗[K] B))
    (hF : ∀ x, F (sigmaGL K L A σ x) = sigmaGL K L B σ (F x)) (δ : GL (Fin 2) (L ⊗[K] A)) :
    F (normString K L A σ δ) = normString K L B σ (F δ) := by
  unfold normString
  rw [map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  show F ((sigmaGL K L A σ)^[i] δ) = (sigmaGL K L B σ)^[i] (F δ)
  exact (Function.Semiconj.iterate_right (f := F) (ga := sigmaGL K L A σ) (gb := sigmaGL K L B σ) hF i δ)

omit [NumberField K] [NumberField L] in
theorem sigmaTensor_iterate (k : ℕ) (y : L ⊗[K] A) :
    (sigmaTensor K L A σ)^[k] y = Algebra.TensorProduct.map (σ ^ k).toAlgHom (AlgHom.id K A) y := by
  induction k generalizing y with
  | zero =>
      simp only [Function.iterate_zero, id_eq, pow_zero]
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul a b => simp [Algebra.TensorProduct.map_tmul]
      | add x y hx hy => rw [map_add, ← hx, ← hy]
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih]
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul a b =>
          simp [sigmaTensor, Algebra.TensorProduct.map_tmul, pow_succ', AlgEquiv.mul_apply]
      | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]

omit [NumberField K] [NumberField L] in
theorem sigmaGL_iterate_finrank (hσ : σ ^ Module.finrank K L = 1) (x : GL (Fin 2) (L ⊗[K] A)) :
    (sigmaGL K L A σ)^[Module.finrank K L] x = x := by
  have hentry : ∀ (k : ℕ) (x : GL (Fin 2) (L ⊗[K] A)) (i j : Fin 2),
      ((sigmaGL K L A σ)^[k] x) i j = (sigmaTensor K L A σ)^[k] (x i j) := by
    intro k
    induction k with
    | zero => intro x i j; rfl
    | succ k ih =>
        intro x i j
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply', sigmaGL,
          Matrix.GeneralLinearGroup.map_apply, ← sigmaGL, ih]
  apply Units.ext
  ext i j
  rw [hentry, sigmaTensor_iterate, hσ]
  induction (x i j) using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [Algebra.TensorProduct.map_tmul]
  | add x y hx hy => rw [map_add, hx, hy]

omit [NumberField K] [NumberField L] in

theorem twistedCentralizer_le_centralizer_normString (hσ : σ ^ Module.finrank K L = 1)
    (δ : GL (Fin 2) (L ⊗[K] A)) :
    twistedCentralizer K L A σ δ ≤ Subgroup.centralizer ({normString K L A σ δ} : Set (GL (Fin 2) (L ⊗[K] A))) := by
  intro t ht
  set s := sigmaGL K L A σ with hs
  have htδ : t * δ = δ * s t := by
    have h := (mem_sigmaCentralizer_iff).1 ht
    rw [← hs] at h
    exact mul_inv_eq_iff_eq_mul.1 h
  have hmul : ∀ (k : ℕ) (x y : GL (Fin 2) (L ⊗[K] A)), s^[k] (x * y) = s^[k] x * s^[k] y := by
    intro k
    induction k with
    | zero => intro x y; rfl
    | succ k ih => intro x y; simp only [Function.iterate_succ_apply', ih, map_mul]
  have hP : ∀ k : ℕ, t * ((List.range k).map fun i => s^[i] δ).prod =
      ((List.range k).map fun i => s^[i] δ).prod * s^[k] t := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        rw [List.range_succ, List.map_append, List.prod_append, List.map_singleton,
          List.prod_singleton, ← mul_assoc, ih, mul_assoc, mul_assoc]
        congr 1
        have h1 : s^[k] t * s^[k] δ = s^[k] (t * δ) := (hmul k t δ).symm
        rw [h1, htδ, hmul, ← Function.iterate_succ_apply s k t]
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h := hP (Module.finrank K L)
  rw [sigmaGL_iterate_finrank K L A σ hσ] at h
  exact h

omit [NumberField K] [NumberField L] in

theorem twistedCentralizer_comm (hσ : σ ^ Module.finrank K L = 1) {δ : GL (Fin 2) (L ⊗[K] A)}
    (hδ : IsRegularSemisimple (normString K L A σ δ)) (s t : twistedCentralizer K L A σ δ) : s * t = t * s :=
  Subtype.ext (mul_comm_of_mem_centralizer hδ
    (twistedCentralizer_le_centralizer_normString K L A σ hσ δ s.2)
    (twistedCentralizer_le_centralizer_normString K L A σ hσ δ t.2))

variable [TopologicalSpace A] [IsTopologicalRing A]

theorem continuous_sigmaTensor : Continuous (sigmaTensor K L A σ) := by
  haveI := isTopologicalRing_tensor K L A
  exact IsModuleTopology.continuous_of_linearMap
    (TensorProduct.RightActions.AlgebraMap.baseChange K L L A σ.toAlgHom).toLinearMap

theorem continuous_sigmaGL : Continuous (sigmaGL K L A σ) := by
  haveI := isTopologicalRing_tensor K L A
  refine Continuous.units_map _ ?_
  exact continuous_id.matrix_map (continuous_sigmaTensor K L A σ)

theorem isClosed_twistedCentralizer [T2Space A] (δ : GL (Fin 2) (L ⊗[K] A)) :
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

end Twist

section SigmaStable

variable (v : HeightOneSpectrum (𝓞 K)) (σ : L ≃ₐ[K] L)

theorem sigmaTensor_mem_semiLocalIntegers {x : SL K L v} (hx : x ∈ semiLocalIntegers K L v) :
    sigmaTensor K L (v.adicCompletion K) σ x ∈ semiLocalIntegers K L v := by
  obtain ⟨z, rfl⟩ := hx
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]; exact zero_mem_semiLocalIntegers K L v
  | tmul b y =>
      refine ⟨(galRestrict (𝓞 K) K L (𝓞 L) σ b) ⊗ₜ y, ?_⟩
      rw [HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul, HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul,
        algebraMap_galRestrict_apply]
      simp [sigmaTensor]
  | add x y hx hy =>
      rw [map_add, map_add]
      obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := hy
      exact ⟨a + b, by rw [map_add, ha, hb]⟩

theorem sigmaGL_mem_semiLocalIntegralSet {g : Gsl K L v} (hg : g ∈ semiLocalIntegralSet K L v) :
    sigmaGL K L (v.adicCompletion K) σ g ∈ semiLocalIntegralSet K L v := by
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · exact sigmaTensor_mem_semiLocalIntegers v σ (hg.1 i j)
  · rw [← map_inv]
    exact sigmaTensor_mem_semiLocalIntegers v σ (hg.2 i j)

end SigmaStable

section TestFn

open NumberField.InfinitePlace NumberField.InfinitePlace.Completion

omit [NumberField L] in
theorem continuous_ringEquiv_mixedSpace : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace L) := by
  refine continuous_prodMk.2 ⟨continuous_pi fun v => ?_, continuous_pi fun v => ?_⟩
  · exact (isometry_extensionEmbeddingOfIsReal v.2).continuous.comp (continuous_apply _)
  · exact (isometry_extensionEmbedding v.1).continuous.comp (continuous_apply _)

omit [NumberField L] in
theorem continuous_archEntries : Continuous (archEntries L : Garch L → _) :=
  continuous_pi fun i => continuous_pi fun j =>
    (continuous_ringEquiv_mixedSpace (L := L)).comp (Units.continuous_val.matrix_elem i j)

namespace IsArchTestFactor
private theorem _root_.AutomorphicForm.TwistedOrbitalEuler.IsArchTestFactor.continuous {φa : Garch L → ℂ} (h : IsArchTestFactor L φa) : Continuous φa := by
  obtain ⟨⟨Φ, hΦ, hφa⟩, -⟩ := h
  have : φa = Φ ∘ archEntries L := funext hφa
  rw [this]
  exact hΦ.continuous.comp continuous_archEntries

end IsArchTestFactor
p2m_export "AutomorphicForm.TwistedOrbitalEuler" "IsArchTestFactor.continuous"
variable {S : Finset (HeightOneSpectrum (𝓞 K))} {φ : Gad L → ℂ} {φa : Garch L → ℂ} {φf : Gfin L → ℂ}
  {φS : ∀ v : HeightOneSpectrum (𝓞 K), Gsl K L v → ℂ}

theorem continuous_of_isSemiLocalFactorization (hφ : IsSemiLocalFactorization K L S φ φa φf φS) : Continuous φ := by
  have h : φ = fun g => φa (glArch (𝓞 L) L g) * φf (glFin (𝓞 L) L g) := funext hφ.2.2.2.2.2
  rw [h]
  exact ((IsArchTestFactor.continuous hφ.1).comp (continuous_glArch (𝓞 L) L)).mul
    (hφ.2.1.1.continuous.comp (continuous_glFin (𝓞 L) L))

theorem bounded_of_isSemiLocalFactorization (hφ : IsSemiLocalFactorization K L S φ φa φf φS) :
    ∃ C : ℝ, ∀ g, ‖φ g‖ ≤ C := by
  obtain ⟨Ca, hCa⟩ := ((IsArchTestFactor.continuous hφ.1).norm).bddAbove_range_of_hasCompactSupport hφ.1.2.norm
  obtain ⟨Cf, hCf⟩ := (hφ.2.1.1.continuous.norm).bddAbove_range_of_hasCompactSupport hφ.2.1.2.norm
  refine ⟨Ca * Cf, fun g => ?_⟩
  rw [hφ.2.2.2.2.2 g, norm_mul]
  have ha : ‖φa (glArch (𝓞 L) L g)‖ ≤ Ca := hCa ⟨_, rfl⟩
  have hb : ‖φf (glFin (𝓞 L) L g)‖ ≤ Cf := hCf ⟨_, rfl⟩
  have hCa0 : 0 ≤ Ca := (norm_nonneg _).trans ha
  exact mul_le_mul ha hb (norm_nonneg _) hCa0

end TestFn

section Shape

variable (S : Finset (HeightOneSpectrum (𝓞 K))) (φ : Gad L → ℂ) (φa : Garch L → ℂ) (φf : Gfin L → ℂ)
  (φS : ∀ v : HeightOneSpectrum (𝓞 K), Gsl K L v → ℂ)

def φSp (v : HeightOneSpectrum (𝓞 K)) : Gsl K L v → ℂ :=
  if v ∈ S then φS v else (semiLocalIntegralSet K L v).indicator fun _ => (1 : ℂ)

theorem φSp_of_mem {v : HeightOneSpectrum (𝓞 K)} (hv : v ∈ S) : φSp S φS v = φS v := by
  simp only [φSp, hv, if_true]

theorem φSp_of_not_mem {v : HeightOneSpectrum (𝓞 K)} (hv : v ∉ S) :
    φSp S φS v = (semiLocalIntegralSet K L v).indicator fun _ => (1 : ℂ) := by
  simp only [φSp, hv, if_false]

abbrev φat : Ht K L → ℂ := φa ∘ archIdentGL K L

abbrev φt : Gt K L → ℂ := φ ∘ baseChangeGL K L

variable {S φ φa φf φS}

theorem shape_of_subset (hφ : IsSemiLocalFactorization K L S φ φa φf φS) {S' : Finset (HeightOneSpectrum (𝓞 K))}
    (hSS' : S ⊆ S') (x : Gt K L) (hx : ∀ v ∉ S', tensorPlace K L v x ∈ semiLocalIntegralSet K L v) :
    φt φ x = φat φa (tensorArch K L x) * ∏ v ∈ S', φSp S φS v (tensorPlace K L v x) := by
  show φ (baseChangeGL K L x) = φa (archIdentGL K L (tensorArch K L x)) * _
  rw [hφ.2.2.2.2.2, glArch_baseChangeGL]
  by_cases hall : ∀ v ∈ S', v ∉ S → tensorPlace K L v x ∈ semiLocalIntegralSet K L v
  · have hint : ∀ v ∉ S, semiLocalComponent K L v (glFin (𝓞 L) L (baseChangeGL K L x)) ∈ semiLocalIntegralSet K L v := by
      intro v hv
      rw [semiLocalComponent_glFin_baseChangeGL]
      by_cases hv' : v ∈ S'
      · exact hall v hv' hv
      · exact hx v hv'
    rw [hφ.2.2.2.1 _ hint]
    congr 1
    rw [← Finset.prod_subset hSS' (fun v hv' hv => ?_)]
    · exact Finset.prod_congr rfl fun v hv => by rw [φSp_of_mem S φS hv, semiLocalComponent_glFin_baseChangeGL]
    · rw [φSp_of_not_mem S φS hv, Set.indicator_of_mem (hall v hv' hv)]
  · push Not at hall
    obtain ⟨v, hv', hv, hgv⟩ := hall
    rw [hφ.2.2.2.2.1 _ ⟨v, hv, by rwa [semiLocalComponent_glFin_baseChangeGL]⟩, mul_zero]
    symm
    apply mul_eq_zero_of_right
    exact Finset.prod_eq_zero hv' (by rw [φSp_of_not_mem S φS hv, Set.indicator_of_notMem hgv])

theorem vanish_of_subset (hφ : IsSemiLocalFactorization K L S φ φa φf φS) {S' : Finset (HeightOneSpectrum (𝓞 K))}
    (hSS' : S ⊆ S') (x : Gt K L) (hx : ∃ v ∉ S', tensorPlace K L v x ∉ semiLocalIntegralSet K L v) : φt φ x = 0 := by
  obtain ⟨v, hv', hgv⟩ := hx
  show φ (baseChangeGL K L x) = 0
  rw [hφ.2.2.2.2.2, hφ.2.2.2.2.1 _ ⟨v, fun hv => hv' (hSS' hv), by rwa [semiLocalComponent_glFin_baseChangeGL]⟩,
    mul_zero]

theorem measurable_φSp (hφ : IsSemiLocalFactorization K L S φ φa φf φS) (v : HeightOneSpectrum (𝓞 K)) :
    Measurable (φSp S φS v) := by
  by_cases hv : v ∈ S
  · rw [φSp_of_mem S φS hv]
    exact (hφ.2.2.1 v hv).1.continuous.measurable
  · rw [φSp_of_not_mem S φS hv]
    exact measurable_const.indicator (isOpen_semiLocalIntegralSet K L v).measurableSet

theorem continuous_φat (hφ : IsSemiLocalFactorization K L S φ φa φf φS) : Continuous (φat φa : Ht K L → ℂ) :=
  (IsArchTestFactor.continuous hφ.1).comp (archIdentGLEquiv K L).continuous

theorem continuous_φt (hφ : IsSemiLocalFactorization K L S φ φa φf φS) : Continuous (φt φ : Gt K L → ℂ) :=
  (continuous_of_isSemiLocalFactorization hφ).comp (baseChangeGLEquiv K L).continuous

theorem bounded_φt (hφ : IsSemiLocalFactorization K L S φ φa φf φS) : ∃ C : ℝ, ∀ x : Gt K L, ‖φt φ x‖ ≤ C := by
  obtain ⟨C, hC⟩ := bounded_of_isSemiLocalFactorization hφ
  exact ⟨C, fun x => hC _⟩

end Shape

section Dichotomy

variable {S : Finset (HeightOneSpectrum (𝓞 K))} {φ : Gad L → ℂ} {φa : Garch L → ℂ} {φf : Gfin L → ℂ}
  {φS : ∀ v : HeightOneSpectrum (𝓞 K), Gsl K L v → ℂ} (σ : L ≃ₐ[K] L)

theorem tensorArch_tconj (δ x : Gt K L) :
    tensorArch K L (x⁻¹ * δ * sigmaGL K L _ σ x) =
      (tensorArch K L x)⁻¹ * tensorArch K L δ * sigmaGL K L _ σ (tensorArch K L x) := by
  rw [map_mul, map_mul, map_inv, tensorArch_sigmaGL]

theorem tensorPlace_tconj (v : HeightOneSpectrum (𝓞 K)) (δ x : Gt K L) :
    tensorPlace K L v (x⁻¹ * δ * sigmaGL K L _ σ x) =
      (tensorPlace K L v x)⁻¹ * tensorPlace K L v δ * sigmaGL K L _ σ (tensorPlace K L v x) := by
  rw [map_mul, map_mul, map_inv, tensorPlace_sigmaGL]

theorem exists_ne_zero_of_local (hφ : IsSemiLocalFactorization K L S φ φa φf φS) (δ : Gt K L)
    (ha : ∃ x : Ht K L, φat φa (x⁻¹ * tensorArch K L δ * sigmaGL K L _ σ x) ≠ 0)
    (hS : ∀ v ∈ S, ∃ x : Gsl K L v, φS v (x⁻¹ * tensorPlace K L v δ * sigmaGL K L _ σ x) ≠ 0)
    (hnS : ∀ v ∉ S, ∃ x : Gsl K L v, x⁻¹ * tensorPlace K L v δ * sigmaGL K L _ σ x ∈ semiLocalIntegralSet K L v) :
    ∃ x : Gt K L, φt φ (x⁻¹ * δ * sigmaGL K L _ σ x) ≠ 0 := by
  obtain ⟨xa, hxa⟩ := ha
  have hloc : ∀ v : HeightOneSpectrum (𝓞 K), ∃ x : Gsl K L v,
      (v ∈ S → φS v (x⁻¹ * tensorPlace K L v δ * sigmaGL K L _ σ x) ≠ 0) ∧
      (v ∉ S → x⁻¹ * tensorPlace K L v δ * sigmaGL K L _ σ x ∈ semiLocalIntegralSet K L v) := by
    intro v
    by_cases hv : v ∈ S
    · obtain ⟨x, hx⟩ := hS v hv
      exact ⟨x, fun _ => hx, fun h => absurd hv h⟩
    · obtain ⟨x, hx⟩ := hnS v hv
      exact ⟨x, fun h => absurd h hv, fun _ => hx⟩
  choose xv hxvS hxvnS using hloc
  obtain ⟨B, hB⟩ : ∃ B : Finset (HeightOneSpectrum (𝓞 K)), B = S ∪ (finite_setOf_tensorPlace_not_mem δ).toFinset :=
    ⟨_, rfl⟩
  obtain ⟨x, hx⟩ : ∃ x : Gt K L, x = fromLoc B (xa, fun v => xv v.1) := ⟨_, rfl⟩
  have hxa' : tensorArch K L x = xa := by rw [hx]; exact tensorArch_fromLoc B _
  have hxB : ∀ v ∈ B, tensorPlace K L v x = xv v := fun v hv => by rw [hx]; exact tensorPlace_fromLoc_of_mem B _ hv
  have hxnB : ∀ v ∉ B, tensorPlace K L v x = 1 := fun v hv => by rw [hx]; exact tensorPlace_fromLoc_of_not_mem B _ hv
  have hδint : ∀ v ∉ B, tensorPlace K L v δ ∈ semiLocalIntegralSet K L v := by
    intro v hv
    by_contra h
    exact hv (by rw [hB]; exact Finset.mem_union_right _ ((Set.Finite.mem_toFinset _).2 h))
  have hSB : S ⊆ B := by rw [hB]; exact Finset.subset_union_left
  refine ⟨x, ?_⟩
  have hint : ∀ v ∉ S, tensorPlace K L v (x⁻¹ * δ * sigmaGL K L _ σ x) ∈ semiLocalIntegralSet K L v := by
    intro v hv
    rw [tensorPlace_tconj]
    by_cases hvB : v ∈ B
    · rw [hxB v hvB]; exact hxvnS v hv
    · rw [hxnB v hvB, inv_one, one_mul, map_one, mul_one]; exact hδint v hvB
  rw [shape_of_subset hφ (Finset.Subset.refl S) _ hint, tensorArch_tconj, hxa']
  refine mul_ne_zero hxa (Finset.prod_ne_zero_iff.2 fun v hv => ?_)
  rw [φSp_of_mem S φS hv, tensorPlace_tconj, hxB v (hSB hv)]
  exact hxvS v hv

end Dichotomy

section Euler

variable (σ : L ≃ₐ[K] L) (hσ : σ ^ Module.finrank K L = 1)
  (μ : Measure (Gt K L)) [IsHaarMeasure μ] (ν : Measure (Ht K L)) (cG : ℝ)
  (hG : ∀ (S : Finset (HeightOneSpectrum (𝓞 K))) (F : Gt K L → ℂ) (Fa : Ht K L → ℂ)
      (FS : ∀ v : HeightOneSpectrum (𝓞 K), Gsl K L v → ℂ),
      AEStronglyMeasurable Fa ν → (∀ v ∈ S, AEStronglyMeasurable (FS v) (semiLocalHaar K L v)) →
      (∀ x : Gt K L, (∀ v ∉ S, tensorPlace K L v x ∈ semiLocalIntegralSet K L v) →
          F x = Fa (tensorArch K L x) * ∏ v ∈ S, FS v (tensorPlace K L v x)) →
      (∀ x : Gt K L, (∃ v ∉ S, tensorPlace K L v x ∉ semiLocalIntegralSet K L v) → F x = 0) →
        ∫ x, F x ∂μ = cG * (∫ y, Fa y ∂ν) * ∏ v ∈ S, ∫ y, FS v y ∂(semiLocalHaar K L v))
  (δ : Gt K L) (hδ : IsRegularSemisimple (normString K L (AdeleRing (𝓞 K) K) σ δ))

abbrev Ttw : Subgroup (Gt K L) := twistedCentralizer K L (AdeleRing (𝓞 K) K) σ δ
abbrev Ta' : Subgroup (Ht K L) := twistedCentralizer K L (InfiniteAdeleRing K) σ (tensorArch K L δ)
abbrev Tv' (v : HeightOneSpectrum (𝓞 K)) : Subgroup (Gsl K L v) :=
  twistedCentralizer K L (v.adicCompletion K) σ (tensorPlace K L v δ)

variable (τ : Measure (Ttw σ δ)) [IsHaarMeasure τ] (τa : Measure (Ta' σ δ)) [IsHaarMeasure τa]
  (τf : ∀ v : HeightOneSpectrum (𝓞 K), Measure (Tv' σ δ v)) (hτf : ∀ v, IsHaarMeasure (τf v))
  (hτf1 : ∀ v, τf v (Subtype.val ⁻¹' semiLocalIntegralSet K L v) = 1)
  (cT : ℝ) (hcT : 0 < cT)
  (hT : ∀ (S : Finset (HeightOneSpectrum (𝓞 K))) (W : Gt K L → ℂ) (Wa : Ht K L → ℂ)
      (WS : ∀ v : HeightOneSpectrum (𝓞 K), Gsl K L v → ℂ),
      AEStronglyMeasurable (fun t : Ta' σ δ => Wa t) τa →
      (∀ v ∈ S, AEStronglyMeasurable (fun t : Tv' σ δ v => WS v t) (τf v)) →
      (∀ t : Ttw σ δ, (∀ v ∉ S, tensorPlace K L v (t : Gt K L) ∈ semiLocalIntegralSet K L v) →
          W t = Wa (tensorArch K L (t : Gt K L)) * ∏ v ∈ S, WS v (tensorPlace K L v (t : Gt K L))) →
      (∀ t : Ttw σ δ, (∃ v ∉ S, tensorPlace K L v (t : Gt K L) ∉ semiLocalIntegralSet K L v) → W t = 0) →
        ∫ t, W t ∂τ = cT * (∫ t, Wa t ∂τa) * ∏ v ∈ S, ∫ t, WS v t ∂(τf v))
  (S : Finset (HeightOneSpectrum (𝓞 K))) (φ : Gad L → ℂ) (φa : Garch L → ℂ) (φf : Gfin L → ℂ)
  (φS : ∀ v : HeightOneSpectrum (𝓞 K), Gsl K L v → ℂ) (hφ : IsSemiLocalFactorization K L S φ φa φf φS)

include hσ hδ in

theorem exists_local_sectionFn (v : HeightOneSpectrum (𝓞 K)) [IsHaarMeasure (τf v)]
    (g : Gsl K L v → ℂ) (C : Set (Gsl K L v)) (hC : IsCompact C)
    (hE : {y : Gsl K L v | g (y⁻¹ * tensorPlace K L v δ * sigmaGL K L _ σ y) ≠ 0} ⊆ (Tv' σ δ v : Set (Gsl K L v)) * C) :
    ∃ w : Gsl K L v → ℝ, IsTwistedSectionFnOn K L (v.adicCompletion K) σ (tensorPlace K L v δ) (τf v) g w := by
  have hδv : IsRegularSemisimple (normString K L (v.adicCompletion K) σ (tensorPlace K L v δ)) := by
    rw [← map_normString K L _ σ (tensorPlace K L v) (tensorPlace_sigmaGL K L σ v) δ]
    exact isRegularSemisimple_map _ hδ
  haveI : (τf v).IsMulRightInvariant := isMulRightInvariant_of_comm _ (twistedCentralizer_comm K L _ σ hσ hδv) (τf v)
  obtain ⟨w, hw0, hwm, hws, hw1⟩ :=
    MeasureTheory.exists_hasCompactSupport_integral_subgroup_translate_eq_one_of_subset_mul
      (Tv' σ δ v) (isClosed_twistedCentralizer K L _ σ _) (τf v) hC hE
  exact ⟨w, hw0, hwm, hws, fun x hx => hw1 x hx⟩

include hσ hδ in
theorem exists_arch_sectionFn (g : Ht K L → ℂ) (C : Set (Ht K L)) (hC : IsCompact C)
    (hE : {y : Ht K L | g (y⁻¹ * tensorArch K L δ * sigmaGL K L _ σ y) ≠ 0} ⊆ (Ta' σ δ : Set (Ht K L)) * C) :
    ∃ w : Ht K L → ℝ, IsTwistedSectionFnOn K L (InfiniteAdeleRing K) σ (tensorArch K L δ) τa g w := by
  have hδa : IsRegularSemisimple (normString K L (InfiniteAdeleRing K) σ (tensorArch K L δ)) := by
    rw [← map_normString K L _ σ (tensorArch K L) (tensorArch_sigmaGL K L σ) δ]
    exact isRegularSemisimple_map _ hδ
  haveI : τa.IsMulRightInvariant := isMulRightInvariant_of_comm _ (twistedCentralizer_comm K L _ σ hσ hδa) τa
  obtain ⟨w, hw0, hwm, hws, hw1⟩ :=
    MeasureTheory.exists_hasCompactSupport_integral_subgroup_translate_eq_one_of_subset_mul
      (Ta' σ δ) (isClosed_twistedCentralizer K L _ σ _) τa hC hE
  exact ⟨w, hw0, hwm, hws, fun x hx => hw1 x hx⟩

theorem unit_orbitalIntegral (v : HeightOneSpectrum (𝓞 K)) (hδv : tensorPlace K L v δ ∈ semiLocalIntegralSet K L v)
    (hunit : IsTwistedSectionFnOn K L (v.adicCompletion K) σ (tensorPlace K L v δ) (τf v)
      ((semiLocalIntegralSet K L v).indicator fun _ => (1 : ℂ)) ((semiLocalIntegralSet K L v).indicator fun _ => (1 : ℝ))) :
    IsTwistedOrbitalIntegral K L v σ (tensorPlace K L v δ) (τf v) ((semiLocalIntegralSet K L v).indicator fun _ => (1 : ℂ)) 1 := by
  refine ⟨(semiLocalIntegralSet K L v).indicator fun _ => (1 : ℝ), hunit, ?_⟩
  have h : (fun x : Gsl K L v => (semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ))
      (x⁻¹ * tensorPlace K L v δ * sigmaGL K L _ σ x) *
      (((semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℝ)) x : ℝ) : ℂ)) =
      (semiLocalIntegralSet K L v).indicator fun _ => (1 : ℂ) := by
    funext x
    by_cases hx : x ∈ semiLocalIntegralSet K L v
    · have hc : x⁻¹ * tensorPlace K L v δ * sigmaGL K L _ σ x ∈ semiLocalIntegralSet K L v :=
        mul_mem_semiLocalIntegralSet v (mul_mem_semiLocalIntegralSet v (inv_mem_semiLocalIntegralSet v hx) hδv)
          (sigmaGL_mem_semiLocalIntegralSet v σ hx)
      simp only [Set.indicator_of_mem hx, Set.indicator_of_mem hc, Complex.ofReal_one, mul_one]
    · simp only [Set.indicator_of_notMem hx, Complex.ofReal_zero, mul_zero]
  show (1 : ℂ) = ∫ x, (semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ))
      (x⁻¹ * tensorPlace K L v δ * sigmaGL K L _ σ x) *
      (((semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℝ)) x : ℝ) : ℂ) ∂(semiLocalHaar K L v)
  rw [h, integral_indicator_const _ (isOpen_semiLocalIntegralSet K L v).measurableSet, Measure.real,
    semiLocalHaar_semiLocalIntegralSet]
  simp

omit [IsHaarMeasure μ] [IsHaarMeasure τa] in
include hG hφ in

theorem euler_core (S₁ : Finset (HeightOneSpectrum (𝓞 K))) (hSS₁ : S ⊆ S₁)
    (hδint₁ : ∀ v ∉ S₁, tensorPlace K L v δ ∈ semiLocalIntegralSet K L v)
    (wa : Ht K L → ℝ) (hwa : IsTwistedSectionFnOn K L (InfiniteAdeleRing K) σ (tensorArch K L δ) τa (φat φa) wa)
    (wf : ∀ v : HeightOneSpectrum (𝓞 K), Gsl K L v → ℝ)
    (hwf : ∀ v ∈ S₁, IsTwistedSectionFnOn K L (v.adicCompletion K) σ (tensorPlace K L v δ) (τf v) (φSp S φS v) (wf v))
    (hunit : ∀ v ∉ S₁, IsTwistedSectionFnOn K L (v.adicCompletion K) σ (tensorPlace K L v δ) (τf v)
      ((semiLocalIntegralSet K L v).indicator fun _ => (1 : ℂ)) ((semiLocalIntegralSet K L v).indicator fun _ => (1 : ℝ)))
    (wt : Gt K L → ℝ)
    (hwt : wt = {x : Gt K L | ∀ v ∉ S₁, tensorPlace K L v x ∈ semiLocalIntegralSet K L v}.indicator
      fun x => cT⁻¹ * (wa (tensorArch K L x) * ∏ v ∈ S₁, wf v (tensorPlace K L v x)))
    (I : ℂ) (hIt : I = ∫ x, φt φ (x⁻¹ * δ * sigmaGL K L _ σ x) * (wt x : ℂ) ∂μ) :
    ∃ (Ia : ℂ) (Iv : HeightOneSpectrum (𝓞 K) → ℂ),
      IsTwistedOrbitalIntegralOn K L (InfiniteAdeleRing K) σ ν (tensorArch K L δ) τa (φat φa) Ia ∧
      (∀ v, IsTwistedOrbitalIntegral K L v σ (tensorPlace K L v δ) (τf v) (φSp S φS v) (Iv v)) ∧
      ∀ T : Finset (HeightOneSpectrum (𝓞 K)), S₁ ⊆ T → I = cG * cT⁻¹ * Ia * ∏ v ∈ T, Iv v := by
  obtain ⟨F, hF⟩ : ∃ F : Gt K L → ℂ, F = fun x => φt φ (x⁻¹ * δ * sigmaGL K L _ σ x) * (wt x : ℂ) := ⟨_, rfl⟩
  obtain ⟨Fa, hFa⟩ : ∃ Fa : Ht K L → ℂ,
      Fa = fun x => ((cT⁻¹ : ℝ) : ℂ) * (φat φa (x⁻¹ * tensorArch K L δ * sigmaGL K L _ σ x) * (wa x : ℂ)) := ⟨_, rfl⟩
  obtain ⟨Fv, hFv⟩ : ∃ Fv : ∀ v : HeightOneSpectrum (𝓞 K), Gsl K L v → ℂ,
      Fv = fun v x => φSp S φS v (x⁻¹ * tensorPlace K L v δ * sigmaGL K L _ σ x) * (wf v x : ℂ) := ⟨_, rfl⟩
  have hFshape : ∀ x : Gt K L, (∀ v ∉ S₁, tensorPlace K L v x ∈ semiLocalIntegralSet K L v) →
      F x = Fa (tensorArch K L x) * ∏ v ∈ S₁, Fv v (tensorPlace K L v x) := by
    intro x hx
    have hcx : ∀ v ∉ S₁, tensorPlace K L v (x⁻¹ * δ * sigmaGL K L _ σ x) ∈ semiLocalIntegralSet K L v := by
      intro v hv
      rw [tensorPlace_tconj]
      exact mul_mem_semiLocalIntegralSet v (mul_mem_semiLocalIntegralSet v (inv_mem_semiLocalIntegralSet v (hx v hv))
        (hδint₁ v hv)) (sigmaGL_mem_semiLocalIntegralSet v σ (hx v hv))
    have hwtx : wt x = cT⁻¹ * (wa (tensorArch K L x) * ∏ v ∈ S₁, wf v (tensorPlace K L v x)) := by
      rw [hwt, Set.indicator_of_mem (show x ∈ {x : Gt K L | ∀ v ∉ S₁, tensorPlace K L v x ∈ semiLocalIntegralSet K L v}
        from hx)]
    rw [hF, hFa, hFv]
    dsimp only
    rw [shape_of_subset hφ hSS₁ _ hcx, hwtx, tensorArch_tconj]
    simp only [tensorPlace_tconj]
    push_cast
    rw [Finset.prod_mul_distrib]
    ring
  have hFvanish : ∀ x : Gt K L, (∃ v ∉ S₁, tensorPlace K L v x ∉ semiLocalIntegralSet K L v) → F x = 0 := by
    intro x hx
    have hwtx : wt x = 0 := by
      rw [hwt, Set.indicator_of_notMem]
      obtain ⟨v, hv, hxv⟩ := hx
      exact fun h => hxv (h v hv)
    rw [hF]
    dsimp only
    rw [hwtx, Complex.ofReal_zero, mul_zero]
  have hFa_meas : AEStronglyMeasurable Fa ν := by
    rw [hFa]
    refine (Measurable.aestronglyMeasurable ?_)
    exact measurable_const.mul ((((continuous_φat hφ).comp
      (continuous_twistedConj _ _ (continuous_sigmaGL K L _ σ))).measurable).mul (Complex.measurable_ofReal.comp hwa.2.1))
  have hFv_meas : ∀ v ∈ S₁, AEStronglyMeasurable (Fv v) (semiLocalHaar K L v) := by
    intro v hv
    rw [hFv]
    refine (Measurable.aestronglyMeasurable ?_)
    exact ((measurable_φSp hφ v).comp (continuous_twistedConj _ _ (continuous_sigmaGL K L _ σ)).measurable).mul
      (Complex.measurable_ofReal.comp (hwf v hv).2.1)
  have hEuler := hG S₁ F Fa Fv hFa_meas hFv_meas hFshape hFvanish
  obtain ⟨Ia, hIa⟩ : ∃ Ia : ℂ, Ia = ∫ x, φat φa (x⁻¹ * tensorArch K L δ * sigmaGL K L _ σ x) * (wa x : ℂ) ∂ν := ⟨_, rfl⟩
  obtain ⟨Iv, hIv⟩ : ∃ Iv : HeightOneSpectrum (𝓞 K) → ℂ,
      Iv = fun v => if v ∈ S₁ then ∫ y, Fv v y ∂(semiLocalHaar K L v) else 1 := ⟨_, rfl⟩
  have hIa' : ∫ x, Fa x ∂ν = ((cT⁻¹ : ℝ) : ℂ) * Ia := by
    rw [hFa, hIa]
    exact integral_const_mul _ _
  refine ⟨Ia, Iv, ⟨wa, hwa, hIa⟩, fun v => ?_, fun T hT₁ => ?_⟩
  · by_cases hv : v ∈ S₁
    · refine ⟨wf v, hwf v hv, ?_⟩
      rw [hIv]
      dsimp only
      rw [if_pos hv, hFv]
    · rw [hIv]
      dsimp only
      rw [if_neg hv, φSp_of_not_mem S φS (fun h => hv (hSS₁ h))]
      exact unit_orbitalIntegral σ δ τf v (hδint₁ v hv) (hunit v hv)
  · have hprod : ∏ v ∈ T, Iv v = ∏ v ∈ S₁, ∫ y, Fv v y ∂(semiLocalHaar K L v) := by
      rw [← Finset.prod_subset hT₁ (fun v _ hv => by rw [hIv]; dsimp only; rw [if_neg hv])]
      exact Finset.prod_congr rfl fun v hv => by rw [hIv]; dsimp only; rw [if_pos hv]
    have hIF : I = ∫ x, F x ∂μ := by rw [hIt, hF]
    rw [hprod, hIF, hEuler, hIa']
    push_cast
    ring

include hσ hG hδ hτf hτf1 hcT hT hφ in

theorem euler (I : ℂ) (hI : IsTwistedOrbitalIntegralOn K L (AdeleRing (𝓞 K) K) σ μ δ τ (φt φ) I)
    (hne : ∃ x : Gt K L, φt φ (x⁻¹ * δ * sigmaGL K L _ σ x) ≠ 0) :
    ∃ S₁ : Finset (HeightOneSpectrum (𝓞 K)), S ⊆ S₁ ∧
      ∃ (Ia : ℂ) (Iv : HeightOneSpectrum (𝓞 K) → ℂ),
        IsTwistedOrbitalIntegralOn K L (InfiniteAdeleRing K) σ ν (tensorArch K L δ) τa (φat φa) Ia ∧
        (∀ v, IsTwistedOrbitalIntegral K L v σ (tensorPlace K L v δ) (τf v) (φSp S φS v) (Iv v)) ∧
        ∀ T : Finset (HeightOneSpectrum (𝓞 K)), S₁ ⊆ T → I = cG * cT⁻¹ * Ia * ∏ v ∈ T, Iv v := by
  haveI := hτf
  haveI : SecondCountableTopology (AdeleRing (𝓞 K) K) := NumberField.AdeleRing.secondCountableTopology K
  obtain ⟨S₀, hS₀⟩ : ∃ S₀ : Finset (HeightOneSpectrum (𝓞 K)), S₀ = S ∪ (finite_setOf_tensorPlace_not_mem δ).toFinset :=
    ⟨_, rfl⟩
  have hSS₀ : S ⊆ S₀ := by rw [hS₀]; exact Finset.subset_union_left
  have hδint : ∀ v ∉ S₀, tensorPlace K L v δ ∈ semiLocalIntegralSet K L v := by
    intro v hv
    by_contra h
    exact hv (by rw [hS₀]; exact Finset.mem_union_right _ ((Set.Finite.mem_toFinset _).2 h))
  obtain ⟨w, hw, hIw⟩ := hI
  obtain ⟨⟨S₁, hS₀S₁, hunit⟩, hcpS, hcpnS, hcpa⟩ :=
    AutomorphicForm.exists_finset_forall_isTwistedSectionFnOn_indicator_semiLocalIntegralSet_of_isTwistedSectionFnOn_baseChange
      K L σ hσ δ hδ τ τf (fun v => inferInstance) hτf1 S₀ (φt φ) (φat φa) (φSp S φS)
      (fun x hx => shape_of_subset hφ hSS₀ x hx) (fun x hx => vanish_of_subset hφ hSS₀ x hx) ⟨w, hw⟩ hne
  have hSS₁ : S ⊆ S₁ := hSS₀.trans hS₀S₁
  have hδint₁ : ∀ v ∉ S₁, tensorPlace K L v δ ∈ semiLocalIntegralSet K L v := fun v hv => hδint v fun h => hv (hS₀S₁ h)
  have hloc : ∀ v : HeightOneSpectrum (𝓞 K), ∃ wv : Gsl K L v → ℝ,
      v ∈ S₁ → IsTwistedSectionFnOn K L (v.adicCompletion K) σ (tensorPlace K L v δ) (τf v) (φSp S φS v) wv := by
    intro v
    by_cases hv : v ∈ S₁
    · by_cases hv₀ : v ∈ S₀
      · obtain ⟨C, hC, hE⟩ := hcpS v hv₀
        obtain ⟨wv, hwv⟩ := exists_local_sectionFn σ hσ δ hδ τf v (φSp S φS v) C hC hE
        exact ⟨wv, fun _ => hwv⟩
      · obtain ⟨C, hC, hE⟩ := hcpnS v hv₀
        have hE' : {y : Gsl K L v | φSp S φS v (y⁻¹ * tensorPlace K L v δ * sigmaGL K L _ σ y) ≠ 0} ⊆
            (Tv' σ δ v : Set (Gsl K L v)) * C := by
          intro y hy
          apply hE
          rw [Set.mem_setOf_eq, φSp_of_not_mem S φS (fun h => hv₀ (hSS₀ h))] at hy
          simpa [Set.indicator_apply_ne_zero] using hy
        obtain ⟨wv, hwv⟩ := exists_local_sectionFn σ hσ δ hδ τf v (φSp S φS v) C hC hE'
        exact ⟨wv, fun _ => hwv⟩
    · exact ⟨fun _ => 0, fun h => absurd h hv⟩
  choose wf hwf using hloc
  obtain ⟨Ca, hCa, hEa⟩ := hcpa
  obtain ⟨wa, hwa⟩ := exists_arch_sectionFn σ hσ δ hδ τa (φat φa) Ca hCa hEa
  have hsec := AutomorphicForm.isTwistedSectionFnOn_baseChange_indicator_prod_of_forall_isTwistedSectionFnOn K L σ δ τ τa τf
    cT hcT hT S₁ (φt φ) (φat φa) (φSp S φS) (fun x hx => shape_of_subset hφ hSS₁ x hx)
    (fun x hx => vanish_of_subset hφ hSS₁ x hx) wa hwa wf (fun v hv => hwf v hv) (fun v hv => hunit v hv)
  obtain ⟨wt, hwt⟩ : ∃ wt : Gt K L → ℝ, wt = {x : Gt K L | ∀ v ∉ S₁, tensorPlace K L v x ∈ semiLocalIntegralSet K L v}.indicator
    fun x => cT⁻¹ * (wa (tensorArch K L x) * ∏ v ∈ S₁, wf v (tensorPlace K L v x)) := ⟨_, rfl⟩
  rw [← hwt] at hsec
  have hIt : I = ∫ x, φt φ (x⁻¹ * δ * sigmaGL K L _ σ x) * (wt x : ℂ) ∂μ :=
    AutomorphicForm.IsTwistedOrbitalIntegralOn.unique_of_isRegularSemisimple_normString K L (AdeleRing (𝓞 K) K) σ hσ μ
      inferInstance δ hδ τ inferInstance (φt φ) (continuous_φt hφ).measurable (bounded_φt hφ) ⟨w, hw, hIw⟩ ⟨wt, hsec, rfl⟩
  obtain ⟨Ia, Iv, h1, h2, h3⟩ := euler_core σ μ ν cG hG δ τa τf cT S φ φa φf φS hφ S₁ hSS₁ hδint₁ wa hwa wf hwf hunit
    wt hwt I hIt
  exact ⟨S₁, hSS₁, Ia, Iv, h1, h2, h3⟩

end Euler

end AutomorphicForm.TwistedOrbitalEuler
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isTwistedOrbitalIntegralOn_baseChange_eq_mul_prod_of_isSemiLocalFactorization.AutomorphicForm P2MW.S_AutomorphicForm_exists_isTwistedOrbitalIntegralOn_baseChange_eq_mul_prod_of_isSemiLocalFactorization.AutomorphicForm.TwistedOrbitalEuler"
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isTwistedOrbitalIntegralOn_baseChange_eq_mul_prod_of_isSemiLocalFactorization.AutomorphicForm"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isTwistedOrbitalIntegralOn_baseChange_eq_mul_prod_of_isSemiLocalFactorization.AutomorphicForm P2MW.S_AutomorphicForm_exists_isTwistedOrbitalIntegralOn_baseChange_eq_mul_prod_of_isSemiLocalFactorization.AutomorphicForm.TwistedOrbitalEuler"

open _root_.AutomorphicForm _root_.P2MW.S_AutomorphicForm_exists_isTwistedOrbitalIntegralOn_baseChange_eq_mul_prod_of_isSemiLocalFactorization.AutomorphicForm AutomorphicForm.TwistedOrbitalEuler in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (σ : L ≃ₐ[K] L) (hσ : σ ^ Module.finrank K L = 1)
    (μ : @Measure (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))
      (AutomorphicForm.glBorelOf (L ⊗[K] AdeleRing (𝓞 K) K)))
    (hμ : @Measure.IsHaarMeasure (GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) _ _
      (AutomorphicForm.glBorelOf (L ⊗[K] AdeleRing (𝓞 K) K)) μ)
    (ν : @Measure (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))
      (AutomorphicForm.glBorelOf (L ⊗[K] InfiniteAdeleRing K)))
    (cG : ℝ)
    (hG : ∀ (S : Finset (HeightOneSpectrum (𝓞 K)))
        (F : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) → ℂ) (Fa : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) → ℂ)
        (FS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ),
        AEStronglyMeasurable[AutomorphicForm.glBorelOf (L ⊗[K] InfiniteAdeleRing K)] Fa ν →
        (∀ v ∈ S, AEStronglyMeasurable[AutomorphicForm.glBorelOf (L ⊗[K] v.adicCompletion K)] (FS v)
          (AutomorphicForm.semiLocalHaar K L v)) →
        (∀ x : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K),
          (∀ v ∉ S, AutomorphicForm.tensorPlace K L v x ∈ AutomorphicForm.semiLocalIntegralSet K L v) →
            F x = Fa (AutomorphicForm.tensorArch K L x) *
              ∏ v ∈ S, FS v (AutomorphicForm.tensorPlace K L v x)) →
        (∀ x : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K),
          (∃ v ∉ S, AutomorphicForm.tensorPlace K L v x ∉ AutomorphicForm.semiLocalIntegralSet K L v) →
            F x = 0) →
          ∫ x, F x ∂μ = cG * (∫ y, Fa y ∂ν) * ∏ v ∈ S, ∫ y, FS v y ∂(AutomorphicForm.semiLocalHaar K L v))
    (δ : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))
    (hδ : AutomorphicForm.IsRegularSemisimple (AutomorphicForm.normString K L (AdeleRing (𝓞 K) K) σ δ))
    (τ : @Measure (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ δ)
      (AutomorphicForm.twistedCentralizerBorel K L (AdeleRing (𝓞 K) K) σ δ))
    (hτ : @Measure.IsHaarMeasure _ _ _
      (AutomorphicForm.twistedCentralizerBorel K L (AdeleRing (𝓞 K) K) σ δ) τ)
    (τa : @Measure (AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ
        (AutomorphicForm.tensorArch K L δ))
      (AutomorphicForm.twistedCentralizerBorel K L (InfiniteAdeleRing K) σ
        (AutomorphicForm.tensorArch K L δ)))
    (hτa : @Measure.IsHaarMeasure _ _ _
      (AutomorphicForm.twistedCentralizerBorel K L (InfiniteAdeleRing K) σ
        (AutomorphicForm.tensorArch K L δ)) τa)
    (τf : ∀ v : HeightOneSpectrum (𝓞 K),
      @Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ
          (AutomorphicForm.tensorPlace K L v δ))
        (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ
          (AutomorphicForm.tensorPlace K L v δ)))
    (hτf : ∀ v : HeightOneSpectrum (𝓞 K), @Measure.IsHaarMeasure _ _ _
      (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ
        (AutomorphicForm.tensorPlace K L v δ)) (τf v))
    (hτf1 : ∀ v : HeightOneSpectrum (𝓞 K),
      τf v (Subtype.val ⁻¹' AutomorphicForm.semiLocalIntegralSet K L v) = 1)
    (cT : ℝ) (hcT : 0 < cT)
    (hT : ∀ (S : Finset (HeightOneSpectrum (𝓞 K)))
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
          ∫ t, W t ∂τ = cT * (∫ t, Wa t ∂τa) * ∏ v ∈ S, ∫ t, WS v t ∂(τf v))
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (φ : GL (Fin 2) (AdeleRing (𝓞 L) L) → ℂ) (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ)
    (φf : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ)
    (φS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ)
    (hφ : AutomorphicForm.IsSemiLocalFactorization K L S φ φa φf φS)
    (I : ℂ)
    (hI : AutomorphicForm.IsTwistedOrbitalIntegralOn K L (AdeleRing (𝓞 K) K) σ μ δ τ
      (φ ∘ AutomorphicForm.baseChangeGL K L) I) :
    (I = 0 ∧
      ((∀ x : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K),
          φa (AutomorphicForm.archIdentGL K L (x⁻¹ * AutomorphicForm.tensorArch K L δ *
            AutomorphicForm.sigmaGL K L (InfiniteAdeleRing K) σ x)) = 0) ∨
        (∃ v ∈ S, ∀ x : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
          φS v (x⁻¹ * AutomorphicForm.tensorPlace K L v δ *
            AutomorphicForm.sigmaGL K L (v.adicCompletion K) σ x) = 0) ∨
        (∃ v ∉ S, ∀ x : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
          x⁻¹ * AutomorphicForm.tensorPlace K L v δ * AutomorphicForm.sigmaGL K L (v.adicCompletion K) σ x ∉
            AutomorphicForm.semiLocalIntegralSet K L v))) ∨
    ∃ S₁ : Finset (HeightOneSpectrum (𝓞 K)), S ⊆ S₁ ∧
      ∃ (Ia : ℂ) (Iv : HeightOneSpectrum (𝓞 K) → ℂ),
        AutomorphicForm.IsTwistedOrbitalIntegralOn K L (InfiniteAdeleRing K) σ ν
          (AutomorphicForm.tensorArch K L δ) τa (φa ∘ AutomorphicForm.archIdentGL K L) Ia ∧
        (∀ v ∈ S, AutomorphicForm.IsTwistedOrbitalIntegral K L v σ
          (AutomorphicForm.tensorPlace K L v δ) (τf v) (φS v) (Iv v)) ∧
        (∀ v ∉ S, AutomorphicForm.IsTwistedOrbitalIntegral K L v σ
          (AutomorphicForm.tensorPlace K L v δ) (τf v)
          ((AutomorphicForm.semiLocalIntegralSet K L v).indicator fun _ => (1 : ℂ)) (Iv v)) ∧
        ∀ T : Finset (HeightOneSpectrum (𝓞 K)), S₁ ⊆ T →
          I = cG * cT⁻¹ * Ia * ∏ v ∈ T, Iv v := by
  haveI := hμ; haveI := hτ; haveI := hτa
  by_cases hne : ∃ x : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K),
      φt φ (x⁻¹ * δ * AutomorphicForm.sigmaGL K L (AdeleRing (𝓞 K) K) σ x) ≠ 0
  · right
    obtain ⟨S₁, hSS₁, Ia, Iv, hIa, hIv, hIeq⟩ :=
      euler σ hσ μ ν cG hG δ hδ τ τa τf hτf hτf1 cT hcT hT S φ φa φf φS hφ I hI hne
    refine ⟨S₁, hSS₁, Ia, Iv, hIa, fun v hv => ?_, fun v hv => ?_, hIeq⟩
    · have h := hIv v
      rwa [φSp_of_mem S φS hv] at h
    · have h := hIv v
      rwa [φSp_of_not_mem S φS hv] at h
  · left
    refine ⟨?_, ?_⟩
    · obtain ⟨w, -, rfl⟩ := hI
      push Not at hne
      have h0 : ∀ x : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K),
          φ (AutomorphicForm.baseChangeGL K L (x⁻¹ * δ * AutomorphicForm.sigmaGL K L (AdeleRing (𝓞 K) K) σ x)) = 0 := hne
      simp only [Function.comp_apply, h0, zero_mul, integral_zero]
    · by_contra hcon
      push Not at hcon
      obtain ⟨ha, hS, hnS⟩ := hcon
      exact hne (exists_ne_zero_of_local σ hφ δ ha hS hnS)

end S_AutomorphicForm_exists_isTwistedOrbitalIntegralOn_baseChange_eq_mul_prod_of_isSemiLocalFactorization
end P2MW
export P2MW.S_AutomorphicForm_exists_isTwistedOrbitalIntegralOn_baseChange_eq_mul_prod_of_isSemiLocalFactorization (solution)
