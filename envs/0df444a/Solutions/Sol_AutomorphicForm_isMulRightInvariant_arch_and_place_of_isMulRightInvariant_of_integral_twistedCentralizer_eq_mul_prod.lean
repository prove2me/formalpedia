-- Prove2me | solution 1 for AutomorphicForm.isMulRightInvariant_arch_and_place_of_isMulRightInvariant_of_integral_twistedCentralizer_eq_mul_prod
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/cfa54e05-04c6-585b-a679-28b2d970034c

import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_isMulRightInvariant_arch_and_place_of_isMulRightInvariant_of_integral_twistedCentralizer_eq_mul_prod

set_option autoImplicit false
set_option linter.unusedSectionVars false

open IsDedekindDomain NumberField MeasureTheory MeasureTheory.Measure Topology TopologicalSpace Set Filter
open NumberField.AdelicLevel TensorProduct
open scoped TensorProduct.RightActions NNReal ENNReal Pointwise

noncomputable section

namespace AutomorphicForm
p2m_export "AutomorphicForm" "tensorArch tensorPlace glArch_baseChangeGL semiLocalComponent_glFin_baseChangeGL tensorArch_sigmaGL tensorPlace_sigmaGL baseChangeGLEquiv archIdentGLEquiv semiLocalEval_eq semiLocalHomeomorph_eq continuous_tensorArch continuous_tensorPlace matrix_eq_of_forall_semiLocalEval_mapMatrix_eq eq_of_tensorArch_eq_of_forall_tensorPlace_eq isTopologicalRing_tensor t2Space_tensor locallyCompactSpace_tensor isTopologicalGroup_tensorGL t2Space_tensorGL locallyCompactSpace_tensorGL glBorelOf semiLocalHomeomorph piIntegers semiLocalIntegers semiLocalIntegers_eq_preimage semiLocalIntegralSet sigmaTensor sigmaGL twistedCentralizer twistedCentralizerBorel semiLocalEval semiLocalComponent integralUnitsSet mem_integralUnitsSet localIntegralSet mem_localIntegralSet unitFinSet mem_sigmaCentralizer_iff"
namespace TwistedRightInv
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

open scoped Classical in

def atPlace (v : HeightOneSpectrum (𝓞 K)) (y : Gsl K L v) : Gt K L :=
  fromLoc ({v} : Finset (HeightOneSpectrum (𝓞 K)))
    (1, Function.update (1 : SProd K L ({v} : Finset (HeightOneSpectrum (𝓞 K)))) ⟨v, Finset.mem_singleton_self v⟩ y)

theorem tensorArch_atPlace (v : HeightOneSpectrum (𝓞 K)) (y : Gsl K L v) : tensorArch K L (atPlace v y) = 1 :=
  tensorArch_fromLoc _ _

theorem tensorPlace_atPlace_self (v : HeightOneSpectrum (𝓞 K)) (y : Gsl K L v) :
    tensorPlace K L v (atPlace v y) = y := by
  classical
  rw [atPlace, tensorPlace_fromLoc_of_mem _ _ (Finset.mem_singleton_self v)]
  exact Function.update_self _ _ _

theorem tensorPlace_atPlace_of_ne (v : HeightOneSpectrum (𝓞 K)) (y : Gsl K L v) {w : HeightOneSpectrum (𝓞 K)}
    (hw : w ≠ v) : tensorPlace K L w (atPlace v y) = 1 :=
  tensorPlace_fromLoc_of_not_mem _ _ (fun h => hw (Finset.mem_singleton.1 h))

def atArch (y : Ht K L) : Gt K L :=
  fromLoc (∅ : Finset (HeightOneSpectrum (𝓞 K))) (y, 1)

theorem tensorArch_atArch (y : Ht K L) : tensorArch K L (atArch y) = y :=
  tensorArch_fromLoc _ _

theorem tensorPlace_atArch (y : Ht K L) (w : HeightOneSpectrum (𝓞 K)) : tensorPlace K L w (atArch y) = 1 :=
  tensorPlace_fromLoc_of_not_mem _ _ (Finset.notMem_empty w)

end More

section Twist

variable (K L) (A : Type) [CommRing A] [Algebra K A] (σ : L ≃ₐ[K] L) [TopologicalSpace A] [IsTopologicalRing A]

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

section HaarRight

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

theorem isMulRightInvariant_of_forall_toReal_eq (ρ : Measure G) [ρ.IsHaarMeasure]
    (h : ∀ (s : G) (C : Set G), IsCompact C → (ρ ((fun t => t * s) ⁻¹' C)).toReal = (ρ C).toReal) :
    ρ.IsMulRightInvariant := by
  refine ⟨fun s => ?_⟩
  set ρ' : Measure G := Measure.map (· * s) ρ with hρ'
  haveI : ρ'.IsHaarMeasure := isHaarMeasure_map_mul_right ρ s
  have huniq : ρ' = haarScalarFactor ρ' ρ • ρ := isMulLeftInvariant_eq_smul ρ' ρ
  obtain ⟨C₀⟩ : Nonempty (PositiveCompacts G) := inferInstance
  have hC : IsCompact (C₀ : Set G) := C₀.isCompact
  have hpos : ρ (C₀ : Set G) ≠ 0 := (measure_pos_of_nonempty_interior ρ C₀.interior_nonempty).ne'
  have htop : ρ (C₀ : Set G) ≠ ⊤ := hC.measure_lt_top.ne
  have hpre : IsCompact ((fun t => t * s) ⁻¹' (C₀ : Set G)) := by
    have : (fun t => t * s) ⁻¹' (C₀ : Set G) = (fun t => t * s⁻¹) '' (C₀ : Set G) := by
      ext t
      simp only [Set.mem_preimage, Set.mem_image]
      constructor
      · intro ht; exact ⟨t * s, ht, by group⟩
      · rintro ⟨u, hu, rfl⟩; simpa using hu
    rw [this]
    exact hC.image (continuous_id.mul continuous_const)
  have hval : ρ' (C₀ : Set G) = ρ (C₀ : Set G) := by
    rw [hρ', Measure.map_apply (measurable_mul_const s) hC.measurableSet]
    have h1 := h s (C₀ : Set G) hC
    exact (ENNReal.toReal_eq_toReal_iff' hpre.measure_lt_top.ne htop).1 h1
  have hc : (haarScalarFactor ρ' ρ : ℝ≥0∞) = 1 := by
    have h2 : (haarScalarFactor ρ' ρ : ℝ≥0∞) * ρ (C₀ : Set G) = 1 * ρ (C₀ : Set G) := by
      rw [one_mul]
      conv_rhs => rw [← hval, huniq]
      rfl
    exact (ENNReal.mul_left_inj hpos htop).1 h2
  have : (haarScalarFactor ρ' ρ) = 1 := by exact_mod_cast hc
  rw [huniq, this, one_smul]

end HaarRight

section Main

variable (σ : L ≃ₐ[K] L) (δ : Gt K L)

abbrev Tad : Subgroup (Gt K L) := twistedCentralizer K L (AdeleRing (𝓞 K) K) σ δ

abbrev Tarch : Subgroup (Ht K L) := twistedCentralizer K L (InfiniteAdeleRing K) σ (tensorArch K L δ)

abbrev Tv (v : HeightOneSpectrum (𝓞 K)) : Subgroup (Gsl K L v) :=
  twistedCentralizer K L (v.adicCompletion K) σ (tensorPlace K L v δ)

scoped instance instLocallyCompactTarch : LocallyCompactSpace (Tarch σ δ) :=
  (isClosed_twistedCentralizer K L _ σ _).isClosedEmbedding_subtypeVal.locallyCompactSpace

scoped instance instLocallyCompactTv (v : HeightOneSpectrum (𝓞 K)) : LocallyCompactSpace (Tv σ δ v) :=
  (isClosed_twistedCentralizer K L _ σ _).isClosedEmbedding_subtypeVal.locallyCompactSpace

scoped instance instSecondCountableTarch : SecondCountableTopology (Tarch σ δ) :=
  (Topology.IsInducing.subtypeVal).secondCountableTopology

scoped instance instSecondCountableTv (v : HeightOneSpectrum (𝓞 K)) : SecondCountableTopology (Tv σ δ v) :=
  (Topology.IsInducing.subtypeVal).secondCountableTopology

variable {σ δ}

theorem mem_Tad_of_components {g : Gt K L} (ha : tensorArch K L g ∈ Tarch σ δ)
    (hv : ∀ v, tensorPlace K L v g ∈ Tv σ δ v) : g ∈ Tad σ δ := by
  rw [AutomorphicForm.mem_sigmaCentralizer_iff]
  refine eq_of_tensorArch_eq_of_forall_tensorPlace_eq K L ?_ fun v => ?_
  · rw [map_mul, map_mul, map_inv, tensorArch_sigmaGL]
    exact (AutomorphicForm.mem_sigmaCentralizer_iff).1 ha
  · rw [map_mul, map_mul, map_inv, tensorPlace_sigmaGL]
    exact (AutomorphicForm.mem_sigmaCentralizer_iff).1 (hv v)

theorem atPlace_mem (v : HeightOneSpectrum (𝓞 K)) (s : Tv σ δ v) : atPlace v (s : Gsl K L v) ∈ Tad σ δ := by
  refine mem_Tad_of_components ?_ fun w => ?_
  · rw [tensorArch_atPlace]; exact one_mem _
  · by_cases hw : w = v
    · subst hw; rw [tensorPlace_atPlace_self]; exact s.2
    · rw [tensorPlace_atPlace_of_ne v _ hw]; exact one_mem _

theorem atArch_mem (s : Tarch σ δ) : atArch (s : Ht K L) ∈ Tad σ δ := by
  refine mem_Tad_of_components ?_ fun w => ?_
  · rw [tensorArch_atArch]; exact s.2
  · rw [tensorPlace_atArch]; exact one_mem _

variable (σ δ)
variable (τ : Measure (Tad σ δ)) [τ.IsMulRightInvariant]
  (τa : Measure (Tarch σ δ)) [τa.IsHaarMeasure]
  (τf : ∀ v : HeightOneSpectrum (𝓞 K), Measure (Tv σ δ v)) [hτf : ∀ v, (τf v).IsHaarMeasure]
  (cT : ℝ) (hcT : 0 < cT)
  (hT : ∀ (S : Finset (HeightOneSpectrum (𝓞 K))) (W : Gt K L → ℂ) (Wa : Ht K L → ℂ)
      (WS : ∀ v : HeightOneSpectrum (𝓞 K), Gsl K L v → ℂ),
      AEStronglyMeasurable (fun t : Tarch σ δ => Wa t) τa →
      (∀ v ∈ S, AEStronglyMeasurable (fun t : Tv σ δ v => WS v t) (τf v)) →
      (∀ t : Tad σ δ, (∀ v ∉ S, tensorPlace K L v (t : Gt K L) ∈ semiLocalIntegralSet K L v) →
          W t = Wa (tensorArch K L (t : Gt K L)) * ∏ v ∈ S, WS v (tensorPlace K L v (t : Gt K L))) →
      (∀ t : Tad σ δ, (∃ v ∉ S, tensorPlace K L v (t : Gt K L) ∉ semiLocalIntegralSet K L v) → W t = 0) →
        ∫ t, W t ∂τ = cT * (∫ t, Wa t ∂τa) * ∏ v ∈ S, ∫ t, WS v t ∂(τf v))

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

theorem integral_indC {G : Type*} [Group G] [TopologicalSpace G] (H : Subgroup G) [MeasurableSpace H]
    [BorelSpace H] [T2Space H] (ρ : Measure H) {C : Set H} (hC : IsCompact C) :
    ∫ t, indC H C t ∂ρ = ((ρ C).toReal : ℂ) := by
  simp_rw [indC_coe]
  rw [integral_indicator_const _ hC.measurableSet, Measure.real, Complex.real_smul, mul_one]

include hcT hT in

theorem place (v₀ : HeightOneSpectrum (𝓞 K)) : (τf v₀).IsMulRightInvariant := by
  classical
  refine isMulRightInvariant_of_forall_toReal_eq (τf v₀) fun s C hC => ?_

  obtain ⟨Ca⟩ : Nonempty (PositiveCompacts (Tarch σ δ)) := inferInstance
  have hCa : IsCompact (Ca : Set (Tarch σ δ)) := Ca.isCompact
  have hCapos : τa (Ca : Set (Tarch σ δ)) ≠ 0 :=
    (measure_pos_of_nonempty_interior τa Ca.interior_nonempty).ne'
  have hCatop : τa (Ca : Set (Tarch σ δ)) ≠ ⊤ := hCa.measure_lt_top.ne

  set g : Gt K L := atPlace v₀ (s : Gsl K L v₀) with hg
  have hgT : g ∈ Tad σ δ := atPlace_mem v₀ s
  set Wa : Ht K L → ℂ := indC (Tarch σ δ) (Ca : Set (Tarch σ δ)) with hWa
  set WS : ∀ v : HeightOneSpectrum (𝓞 K), Gsl K L v → ℂ :=
    Function.update (0 : ∀ v : HeightOneSpectrum (𝓞 K), Gsl K L v → ℂ) v₀ (indC (Tv σ δ v₀) C) with hWS
  set WS' : ∀ v : HeightOneSpectrum (𝓞 K), Gsl K L v → ℂ := fun v y => WS v (y * tensorPlace K L v g) with hWS'
  set S : Finset (HeightOneSpectrum (𝓞 K)) := {v₀} with hS
  set W : Gt K L → ℂ := fun x =>
    if ∀ v ∉ S, tensorPlace K L v x ∈ semiLocalIntegralSet K L v then
      Wa (tensorArch K L x) * ∏ v ∈ S, WS v (tensorPlace K L v x) else 0 with hW
  set W' : Gt K L → ℂ := fun x => W (x * g) with hW'

  have hWS₀ : ∀ t : Tv σ δ v₀, WS v₀ t = C.indicator (fun _ => (1 : ℂ)) t := by
    intro t
    rw [hWS, Function.update_self]
    exact indC_coe _ _ t
  have hWS₀' : ∀ t : Tv σ δ v₀, WS' v₀ t = ((fun u : Tv σ δ v₀ => u * s) ⁻¹' C).indicator (fun _ => (1 : ℂ)) t := by
    intro t
    rw [hWS']
    dsimp only
    rw [hg, tensorPlace_atPlace_self]
    have := hWS₀ (t * s)
    rw [Subgroup.coe_mul] at this
    rw [this]
    rfl

  have hWa_meas : AEStronglyMeasurable (fun t : Tarch σ δ => Wa t) τa := by
    have : (fun t : Tarch σ δ => Wa t) = (Ca : Set (Tarch σ δ)).indicator fun _ => (1 : ℂ) := by
      funext t; rw [hWa]; exact indC_coe _ _ t
    rw [this]
    exact (measurable_const.indicator hCa.measurableSet).aestronglyMeasurable
  have hWS_meas : ∀ v ∈ S, AEStronglyMeasurable (fun t : Tv σ δ v => WS v t) (τf v) := by
    intro v hv
    rw [hS, Finset.mem_singleton] at hv
    subst hv
    have : (fun t : Tv σ δ v => WS v t) = C.indicator fun _ => (1 : ℂ) := funext hWS₀
    rw [this]
    exact (measurable_const.indicator hC.measurableSet).aestronglyMeasurable
  have hpreC : IsCompact ((fun u : Tv σ δ v₀ => u * s) ⁻¹' C) := by
    have : (fun u : Tv σ δ v₀ => u * s) ⁻¹' C = (fun u => u * s⁻¹) '' C := by
      ext u
      simp only [Set.mem_preimage, Set.mem_image]
      constructor
      · intro hu; exact ⟨u * s, hu, by group⟩
      · rintro ⟨u', hu', rfl⟩; simpa using hu'
    rw [this]
    exact hC.image (continuous_id.mul continuous_const)
  have hWS'_meas : ∀ v ∈ S, AEStronglyMeasurable (fun t : Tv σ δ v => WS' v t) (τf v) := by
    intro v hv
    rw [hS, Finset.mem_singleton] at hv
    subst hv
    have : (fun t : Tv σ δ v => WS' v t) = ((fun u : Tv σ δ v => u * s) ⁻¹' C).indicator fun _ => (1 : ℂ) :=
      funext hWS₀'
    rw [this]
    exact (measurable_const.indicator hpreC.measurableSet).aestronglyMeasurable

  have hWshape : ∀ t : Tad σ δ, (∀ v ∉ S, tensorPlace K L v (t : Gt K L) ∈ semiLocalIntegralSet K L v) →
      W t = Wa (tensorArch K L (t : Gt K L)) * ∏ v ∈ S, WS v (tensorPlace K L v (t : Gt K L)) := by
    intro t ht; rw [hW]; dsimp only; rw [if_pos ht]
  have hWvan : ∀ t : Tad σ δ, (∃ v ∉ S, tensorPlace K L v (t : Gt K L) ∉ semiLocalIntegralSet K L v) → W t = 0 := by
    intro t ht
    rw [hW]; dsimp only
    rw [if_neg]
    push Not
    exact ht
  have hcomp : ∀ (v : HeightOneSpectrum (𝓞 K)) (x : Gt K L), v ≠ v₀ →
      tensorPlace K L v (x * g) = tensorPlace K L v x := by
    intro v x hv
    rw [map_mul, hg, tensorPlace_atPlace_of_ne v₀ _ hv, mul_one]
  have hW'shape : ∀ t : Tad σ δ, (∀ v ∉ S, tensorPlace K L v (t : Gt K L) ∈ semiLocalIntegralSet K L v) →
      W' t = Wa (tensorArch K L (t : Gt K L)) * ∏ v ∈ S, WS' v (tensorPlace K L v (t : Gt K L)) := by
    intro t ht
    have ht' : ∀ v ∉ S, tensorPlace K L v ((t : Gt K L) * g) ∈ semiLocalIntegralSet K L v := by
      intro v hv
      have hv' : v ≠ v₀ := fun h => hv (by rw [hS, h]; exact Finset.mem_singleton_self _)
      rw [hcomp v _ hv']
      exact ht v hv
    rw [hW', hW]; dsimp only
    rw [if_pos ht']
    simp only [hS, Finset.prod_singleton]
    rw [hWS']
    dsimp only
    rw [map_mul, map_mul, hg, tensorArch_atPlace, mul_one]
  have hW'van : ∀ t : Tad σ δ, (∃ v ∉ S, tensorPlace K L v (t : Gt K L) ∉ semiLocalIntegralSet K L v) → W' t = 0 := by
    intro t ht
    obtain ⟨v, hv, hvt⟩ := ht
    have hv' : v ≠ v₀ := fun h => hv (by rw [hS, h]; exact Finset.mem_singleton_self _)
    rw [hW', hW]; dsimp only
    rw [if_neg]
    push Not
    exact ⟨v, hv, by rwa [hcomp v _ hv']⟩

  have h1 := hT S W Wa WS hWa_meas hWS_meas hWshape hWvan
  have h2 := hT S W' Wa WS' hWa_meas hWS'_meas hW'shape hW'van

  have h12 : ∫ t, W' t ∂τ = ∫ t, W t ∂τ := by
    have : (fun t : Tad σ δ => W' t) = fun t : Tad σ δ => (fun u : Tad σ δ => W u) (t * ⟨g, hgT⟩) := by
      funext t; rfl
    rw [this]
    exact integral_mul_right_eq_self (fun u : Tad σ δ => W u) ⟨g, hgT⟩
  rw [h1, h2, hS, Finset.prod_singleton, Finset.prod_singleton] at h12

  have hIa : ∫ t, Wa t ∂τa = ((τa (Ca : Set (Tarch σ δ))).toReal : ℂ) := by
    rw [hWa]; exact integral_indC _ τa hCa
  have hI1 : ∫ t, WS v₀ t ∂(τf v₀) = (((τf v₀) C).toReal : ℂ) := by
    simp_rw [hWS₀]
    rw [integral_indicator_const _ hC.measurableSet, Measure.real, Complex.real_smul, mul_one]
  have hI2 : ∫ t, WS' v₀ t ∂(τf v₀) = (((τf v₀) ((fun u : Tv σ δ v₀ => u * s) ⁻¹' C)).toReal : ℂ) := by
    simp_rw [hWS₀']
    rw [integral_indicator_const _ hpreC.measurableSet, Measure.real, Complex.real_smul, mul_one]
  rw [hIa, hI1, hI2] at h12
  have hne : ((cT : ℂ) * ((τa (Ca : Set (Tarch σ δ))).toReal : ℂ)) ≠ 0 := by
    refine mul_ne_zero ?_ ?_
    · exact_mod_cast hcT.ne'
    · exact_mod_cast (ENNReal.toReal_ne_zero.2 ⟨hCapos, hCatop⟩)
  have := mul_left_cancel₀ hne h12
  exact_mod_cast this

include hcT hT hτf in

theorem arch : τa.IsMulRightInvariant := by
  classical
  refine isMulRightInvariant_of_forall_toReal_eq τa fun s C hC => ?_
  set g : Gt K L := atArch (s : Ht K L) with hg
  have hgT : g ∈ Tad σ δ := atArch_mem s
  set Wa : Ht K L → ℂ := indC (Tarch σ δ) C with hWa
  set Wa' : Ht K L → ℂ := fun y => Wa (y * tensorArch K L g) with hWa'
  set WS : ∀ v : HeightOneSpectrum (𝓞 K), Gsl K L v → ℂ := fun _ _ => 0 with hWS
  set S : Finset (HeightOneSpectrum (𝓞 K)) := ∅ with hS
  set W : Gt K L → ℂ := fun x =>
    if ∀ v ∉ S, tensorPlace K L v x ∈ semiLocalIntegralSet K L v then
      Wa (tensorArch K L x) * ∏ v ∈ S, WS v (tensorPlace K L v x) else 0 with hW
  set W' : Gt K L → ℂ := fun x => W (x * g) with hW'
  have hWa₀ : ∀ t : Tarch σ δ, Wa t = C.indicator (fun _ => (1 : ℂ)) t := fun t => by
    rw [hWa]; exact indC_coe _ _ t
  have hWa₀' : ∀ t : Tarch σ δ, Wa' t = ((fun u : Tarch σ δ => u * s) ⁻¹' C).indicator (fun _ => (1 : ℂ)) t := by
    intro t
    rw [hWa']
    dsimp only
    rw [hg, tensorArch_atArch]
    have := hWa₀ (t * s)
    rw [Subgroup.coe_mul] at this
    rw [this]
    rfl
  have hpreC : IsCompact ((fun u : Tarch σ δ => u * s) ⁻¹' C) := by
    have : (fun u : Tarch σ δ => u * s) ⁻¹' C = (fun u => u * s⁻¹) '' C := by
      ext u
      simp only [Set.mem_preimage, Set.mem_image]
      constructor
      · intro hu; exact ⟨u * s, hu, by group⟩
      · rintro ⟨u', hu', rfl⟩; simpa using hu'
    rw [this]
    exact hC.image (continuous_id.mul continuous_const)
  have hWa_meas : AEStronglyMeasurable (fun t : Tarch σ δ => Wa t) τa := by
    have : (fun t : Tarch σ δ => Wa t) = C.indicator fun _ => (1 : ℂ) := funext hWa₀
    rw [this]
    exact (measurable_const.indicator hC.measurableSet).aestronglyMeasurable
  have hWa'_meas : AEStronglyMeasurable (fun t : Tarch σ δ => Wa' t) τa := by
    have : (fun t : Tarch σ δ => Wa' t) = ((fun u : Tarch σ δ => u * s) ⁻¹' C).indicator fun _ => (1 : ℂ) :=
      funext hWa₀'
    rw [this]
    exact (measurable_const.indicator hpreC.measurableSet).aestronglyMeasurable
  have hWS_meas : ∀ v ∈ S, AEStronglyMeasurable (fun t : Tv σ δ v => WS v t) (τf v) := by
    intro v hv; rw [hS] at hv; exact absurd hv (Finset.notMem_empty v)
  have hWshape : ∀ t : Tad σ δ, (∀ v ∉ S, tensorPlace K L v (t : Gt K L) ∈ semiLocalIntegralSet K L v) →
      W t = Wa (tensorArch K L (t : Gt K L)) * ∏ v ∈ S, WS v (tensorPlace K L v (t : Gt K L)) := by
    intro t ht; rw [hW]; dsimp only; rw [if_pos ht]
  have hWvan : ∀ t : Tad σ δ, (∃ v ∉ S, tensorPlace K L v (t : Gt K L) ∉ semiLocalIntegralSet K L v) → W t = 0 := by
    intro t ht
    rw [hW]; dsimp only
    rw [if_neg]
    push Not
    exact ht
  have hcomp : ∀ (v : HeightOneSpectrum (𝓞 K)) (x : Gt K L), tensorPlace K L v (x * g) = tensorPlace K L v x := by
    intro v x
    rw [map_mul, hg, tensorPlace_atArch, mul_one]
  have hW'shape : ∀ t : Tad σ δ, (∀ v ∉ S, tensorPlace K L v (t : Gt K L) ∈ semiLocalIntegralSet K L v) →
      W' t = Wa' (tensorArch K L (t : Gt K L)) * ∏ v ∈ S, WS v (tensorPlace K L v (t : Gt K L)) := by
    intro t ht
    have ht' : ∀ v ∉ S, tensorPlace K L v ((t : Gt K L) * g) ∈ semiLocalIntegralSet K L v := by
      intro v hv
      rw [hcomp v]
      exact ht v hv
    rw [hW', hW]; dsimp only
    rw [if_pos ht']
    simp only [hS, Finset.prod_empty, map_mul, hWa']
  have hW'van : ∀ t : Tad σ δ, (∃ v ∉ S, tensorPlace K L v (t : Gt K L) ∉ semiLocalIntegralSet K L v) → W' t = 0 := by
    intro t ht
    obtain ⟨v, hv, hvt⟩ := ht
    rw [hW', hW]; dsimp only
    rw [if_neg]
    push Not
    exact ⟨v, hv, by rwa [hcomp v]⟩
  have h1 := hT S W Wa WS hWa_meas hWS_meas hWshape hWvan
  have h2 := hT S W' Wa' WS hWa'_meas hWS_meas hW'shape hW'van
  have h12 : ∫ t, W' t ∂τ = ∫ t, W t ∂τ := by
    have : (fun t : Tad σ δ => W' t) = fun t : Tad σ δ => (fun u : Tad σ δ => W u) (t * ⟨g, hgT⟩) := by
      funext t; rfl
    rw [this]
    exact integral_mul_right_eq_self (fun u : Tad σ δ => W u) ⟨g, hgT⟩
  rw [h1, h2, hS, Finset.prod_empty, mul_one, mul_one] at h12
  have hI1 : ∫ t, Wa t ∂τa = ((τa C).toReal : ℂ) := by
    simp_rw [hWa₀]
    rw [integral_indicator_const _ hC.measurableSet, Measure.real, Complex.real_smul, mul_one]
  have hI2 : ∫ t, Wa' t ∂τa = ((τa ((fun u : Tarch σ δ => u * s) ⁻¹' C)).toReal : ℂ) := by
    simp_rw [hWa₀']
    rw [integral_indicator_const _ hpreC.measurableSet, Measure.real, Complex.real_smul, mul_one]
  rw [hI1, hI2] at h12
  have hne : (cT : ℂ) ≠ 0 := by exact_mod_cast hcT.ne'
  have := mul_left_cancel₀ hne h12
  exact_mod_cast this

end Main

end AutomorphicForm.TwistedRightInv
p2m_reactivate "P2MW.S_AutomorphicForm_isMulRightInvariant_arch_and_place_of_isMulRightInvariant_of_integral_twistedCentralizer_eq_mul_prod.AutomorphicForm P2MW.S_AutomorphicForm_isMulRightInvariant_arch_and_place_of_isMulRightInvariant_of_integral_twistedCentralizer_eq_mul_prod.AutomorphicForm.TwistedRightInv"
p2m_reactivate "P2MW.S_AutomorphicForm_isMulRightInvariant_arch_and_place_of_isMulRightInvariant_of_integral_twistedCentralizer_eq_mul_prod.AutomorphicForm"

end
p2m_reactivate "P2MW.S_AutomorphicForm_isMulRightInvariant_arch_and_place_of_isMulRightInvariant_of_integral_twistedCentralizer_eq_mul_prod.AutomorphicForm P2MW.S_AutomorphicForm_isMulRightInvariant_arch_and_place_of_isMulRightInvariant_of_integral_twistedCentralizer_eq_mul_prod.AutomorphicForm.TwistedRightInv"

section Solution

open MeasureTheory NumberField IsDedekindDomain
open AutomorphicForm.TwistedRightInv
open scoped TensorProduct TensorProduct.RightActions

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (σ : L ≃ₐ[K] L)
    (δ : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))
    (τ : @Measure (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ δ)
      (AutomorphicForm.twistedCentralizerBorel K L (AdeleRing (𝓞 K) K) σ δ))
    (hτr : @Measure.IsMulRightInvariant _
      (AutomorphicForm.twistedCentralizerBorel K L (AdeleRing (𝓞 K) K) σ δ) _ τ)
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
          ∫ t, W t ∂τ = cT * (∫ t, Wa t ∂τa) * ∏ v ∈ S, ∫ t, WS v t ∂(τf v)) :
    @Measure.IsMulRightInvariant _
        (AutomorphicForm.twistedCentralizerBorel K L (InfiniteAdeleRing K) σ
          (AutomorphicForm.tensorArch K L δ)) _ τa ∧
      ∀ v : HeightOneSpectrum (𝓞 K), @Measure.IsMulRightInvariant _
        (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ
          (AutomorphicForm.tensorPlace K L v δ)) _ (τf v) := by
  haveI := hτr; haveI := hτa; haveI := hτf
  exact ⟨arch σ δ τ τa τf cT hcT hT, fun v => place σ δ τ τa τf cT hcT hT v⟩

end Solution
p2m_reactivate "P2MW.S_AutomorphicForm_isMulRightInvariant_arch_and_place_of_isMulRightInvariant_of_integral_twistedCentralizer_eq_mul_prod.AutomorphicForm P2MW.S_AutomorphicForm_isMulRightInvariant_arch_and_place_of_isMulRightInvariant_of_integral_twistedCentralizer_eq_mul_prod.AutomorphicForm.TwistedRightInv"

end S_AutomorphicForm_isMulRightInvariant_arch_and_place_of_isMulRightInvariant_of_integral_twistedCentralizer_eq_mul_prod
end P2MW
export P2MW.S_AutomorphicForm_isMulRightInvariant_arch_and_place_of_isMulRightInvariant_of_integral_twistedCentralizer_eq_mul_prod (solution)
