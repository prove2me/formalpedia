-- Prove2me | solution 1 for AutomorphicForm.exists_integral_twistedCentralizer_eq_mul_integral_mul_prod_integral_of_isHaarMeasure
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/30ccb505-e308-5b8a-84aa-5efd84af079b

import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_NumberField_AdelicHaar
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Integral.Pi
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_integral_twistedCentralizer_eq_mul_integral_mul_prod_integral_of_isHaarMeasure

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory MeasureTheory.Measure Topology TopologicalSpace Set Filter
open NumberField.AdelicLevel TensorProduct
open scoped TensorProduct.RightActions NNReal ENNReal

noncomputable section

namespace AutomorphicForm
p2m_export "AutomorphicForm" "tensorArch tensorPlace glArch_baseChangeGL semiLocalComponent_glFin_baseChangeGL tensorArch_sigmaGL tensorPlace_sigmaGL baseChangeGLEquiv archIdentGLEquiv semiLocalEval_eq semiLocalHomeomorph_eq continuous_tensorArch continuous_tensorPlace matrix_eq_of_forall_semiLocalEval_mapMatrix_eq eq_of_tensorArch_eq_of_forall_tensorPlace_eq isTopologicalRing_tensor t2Space_tensor locallyCompactSpace_tensor isTopologicalGroup_tensorGL t2Space_tensorGL locallyCompactSpace_tensorGL glBorelOf semiLocalHomeomorph piIntegers semiLocalIntegers semiLocalIntegers_eq_preimage semiLocalIntegralSet one_mem_semiLocalIntegralSet isCompact_semiLocalIntegralSet sigmaTensor sigmaGL twistedCentralizer twistedCentralizerBorel IsTwistedOrbitalIntegralOn semiLocalEval semiLocalComponent integralUnitsSet mem_integralUnitsSet localIntegralSet mem_localIntegralSet unitFinSet one_mem_unitFinSet isCompact_unitFinSet isOpen_unitFinSet mem_sigmaCentralizer_iff"
namespace TwistedCentralizerHaarFactor
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

structure BoxData (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] where

  H : Subgroup (Gt K L)

  Ha : Subgroup (Ht K L)

  Hv : ∀ v : HeightOneSpectrum (𝓞 K), Subgroup (Gsl K L v)
  isClosed_H : IsClosed (H : Set (Gt K L))
  isClosed_Ha : IsClosed (Ha : Set (Ht K L))
  isClosed_Hv : ∀ v, IsClosed (Hv v : Set (Gsl K L v))
  mem_iff : ∀ g : Gt K L, g ∈ H ↔ tensorArch K L g ∈ Ha ∧ ∀ v, tensorPlace K L v g ∈ Hv v

variable (B : BoxData K L)

section BoxInstances

scoped instance (priority := 10000) instMeasurableSpaceH : MeasurableSpace B.H := borel _
scoped instance instBorelSpaceH : BorelSpace B.H := ⟨rfl⟩
scoped instance (priority := 10000) instMeasurableSpaceHa : MeasurableSpace B.Ha := borel _
scoped instance instBorelSpaceHa : BorelSpace B.Ha := ⟨rfl⟩
scoped instance (priority := 10000) instMeasurableSpaceHv (v : HeightOneSpectrum (𝓞 K)) : MeasurableSpace (B.Hv v) :=
  borel _
scoped instance instBorelSpaceHv (v : HeightOneSpectrum (𝓞 K)) : BorelSpace (B.Hv v) := ⟨rfl⟩

scoped instance instLocallyCompactHa : LocallyCompactSpace B.Ha :=
  B.isClosed_Ha.isClosedEmbedding_subtypeVal.locallyCompactSpace
scoped instance instLocallyCompactHv (v : HeightOneSpectrum (𝓞 K)) : LocallyCompactSpace (B.Hv v) :=
  (B.isClosed_Hv v).isClosedEmbedding_subtypeVal.locallyCompactSpace

scoped instance instSecondCountableHa : SecondCountableTopology B.Ha :=
  TopologicalSpace.Subtype.secondCountableTopology (B.Ha : Set (Ht K L))
scoped instance instSecondCountableHv (v : HeightOneSpectrum (𝓞 K)) : SecondCountableTopology (B.Hv v) :=
  TopologicalSpace.Subtype.secondCountableTopology (B.Hv v : Set (Gsl K L v))

scoped instance instSigmaCompactHa : SigmaCompactSpace B.Ha := sigmaCompactSpace_of_locallyCompact_secondCountable
scoped instance instSigmaCompactHv (v : HeightOneSpectrum (𝓞 K)) : SigmaCompactSpace (B.Hv v) :=
  sigmaCompactSpace_of_locallyCompact_secondCountable

scoped instance instMeasurableMulHa : MeasurableMul B.Ha := inferInstance
scoped instance instMeasurableMulHv (v : HeightOneSpectrum (𝓞 K)) : MeasurableMul (B.Hv v) := inferInstance
scoped instance instMeasurableMulH : MeasurableMul B.H := inferInstance

abbrev HS : Type := (v : S) → B.Hv v.1

abbrev HP : Type := B.Ha × HS S B

scoped instance instBorelSpaceHS : BorelSpace (HS S B) := Pi.borelSpace
scoped instance instBorelSpaceHP : BorelSpace (HP S B) := Prod.borelSpace

set_option synthInstance.maxHeartbeats 800000 in
scoped instance instLocallyCompactHP : LocallyCompactSpace (HP S B) := inferInstance

set_option synthInstance.maxHeartbeats 800000 in
scoped instance instMeasurableMulHS : MeasurableMul (HS S B) := inferInstance

set_option synthInstance.maxHeartbeats 800000 in
scoped instance instMeasurableMulHP : MeasurableMul (HP S B) := inferInstance

set_option synthInstance.maxHeartbeats 800000 in
scoped instance instSecondCountableHP : SecondCountableTopology (HP S B) := inferInstance

end BoxInstances

section BoxMaps

def toLocH : B.H →* HP S B where
  toFun t := (⟨tensorArch K L (t : Gt K L), ((B.mem_iff t).1 t.2).1⟩,
    fun v => ⟨tensorPlace K L v.1 (t : Gt K L), ((B.mem_iff t).1 t.2).2 v.1⟩)
  map_one' := by
    refine Prod.ext (Subtype.ext ?_) (funext fun v => Subtype.ext ?_)
    · simp only [OneMemClass.coe_one, map_one]; rfl
    · simp only [OneMemClass.coe_one, map_one]; rfl
  map_mul' s t := by
    refine Prod.ext (Subtype.ext ?_) (funext fun v => Subtype.ext ?_)
    · simp only [Subgroup.coe_mul, map_mul]; rfl
    · simp only [Subgroup.coe_mul, map_mul]; rfl

theorem coe_toLocH_fst (t : B.H) : ((toLocH S B t).1 : Ht K L) = tensorArch K L (t : Gt K L) := rfl

theorem coe_toLocH_snd (t : B.H) (v : S) : ((toLocH S B t).2 v : Gsl K L v.1) = tensorPlace K L v.1 (t : Gt K L) :=
  rfl

def valHP (x : HP S B) : LocProd K L S := ((x.1 : Ht K L), fun v => (x.2 v : Gsl K L v.1))

theorem valHP_toLocH (t : B.H) : valHP S B (toLocH S B t) = toLoc S (t : Gt K L) :=
  Prod.ext (toLoc_apply_fst S _).symm (funext fun v => (toLoc_apply_snd S _ v).symm)

theorem fromLoc_valHP_mem (x : HP S B) : fromLoc S (valHP S B x) ∈ B.H := by
  refine (B.mem_iff _).2 ⟨?_, fun w => ?_⟩
  · rw [tensorArch_fromLoc]; exact x.1.2
  · by_cases hw : w ∈ S
    · rw [tensorPlace_fromLoc_of_mem S _ hw]; exact (x.2 ⟨w, hw⟩).2
    · rw [tensorPlace_fromLoc_of_not_mem S _ hw]; exact one_mem _

def fromLocH : HP S B →* B.H where
  toFun x := ⟨fromLoc S (valHP S B x), fromLoc_valHP_mem S B x⟩
  map_one' := Subtype.ext (by
    show fromLoc S (valHP S B 1) = 1
    have : valHP S B 1 = 1 := rfl
    rw [this, map_one])
  map_mul' x y := Subtype.ext (by
    show fromLoc S (valHP S B (x * y)) = fromLoc S (valHP S B x) * fromLoc S (valHP S B y)
    have : valHP S B (x * y) = valHP S B x * valHP S B y := rfl
    rw [this, map_mul])

theorem coe_fromLocH (x : HP S B) : ((fromLocH S B x : B.H) : Gt K L) = fromLoc S (valHP S B x) := rfl

theorem toLocH_fromLocH (x : HP S B) : toLocH S B (fromLocH S B x) = x := by
  have h := toLoc_fromLoc S (valHP S B x)
  refine Prod.ext (Subtype.ext ?_) (funext fun v => Subtype.ext ?_)
  · exact congrArg Prod.fst h
  · exact congrFun (congrArg Prod.snd h) v

theorem continuous_toLocH : Continuous (toLocH S B) := by
  refine Continuous.prodMk ?_ (continuous_pi fun v => ?_)
  · exact ((continuous_tensorArch K L).comp continuous_subtype_val).subtype_mk _
  · exact ((continuous_tensorPlace K L v.1).comp continuous_subtype_val).subtype_mk _

theorem continuous_valHP : Continuous (valHP S B) :=
  (continuous_subtype_val.comp continuous_fst).prodMk
    (continuous_pi fun v => continuous_subtype_val.comp ((continuous_apply v).comp continuous_snd))

theorem continuous_fromLocH : Continuous (fromLocH S B) :=
  ((continuous_fromLoc S).comp (continuous_valHP S B)).subtype_mk _

def unitsAwayH : Set B.H := Subtype.val ⁻¹' (unitsAway K L S : Set (Gt K L))

theorem isOpen_unitsAwayH : IsOpen (unitsAwayH S B) :=
  (isOpen_unitsAway S).preimage continuous_subtype_val

theorem measurableSet_unitsAwayH : MeasurableSet (unitsAwayH S B) :=
  (isOpen_unitsAwayH S B).measurableSet

theorem fromLocH_mem_unitsAwayH (x : HP S B) : fromLocH S B x ∈ unitsAwayH S B :=
  fromLoc_mem_unitsAway S _

theorem mul_mem_unitsAwayH_iff {g : B.H} (hg : g ∈ unitsAwayH S B) (a : B.H) :
    g * a ∈ unitsAwayH S B ↔ a ∈ unitsAwayH S B := by
  show (g : Gt K L) * a ∈ (unitsAway K L S : Set (Gt K L)) ↔ (a : Gt K L) ∈ (unitsAway K L S : Set (Gt K L))
  exact Subgroup.mul_mem_cancel_left _ hg

def kerSetH : Set B.H := Subtype.val ⁻¹' kerSet K L S

theorem isCompact_kerSetH : IsCompact (kerSetH S B) :=
  B.isClosed_H.isClosedEmbedding_subtypeVal.isCompact_preimage (isCompact_kerSet S)

theorem mem_image_mul_of_memH (C : Set (HP S B)) {a : B.H}
    (haU : a ∈ unitsAwayH S B) (haC : toLocH S B a ∈ C) :
    a ∈ (fun p : B.H × B.H => p.1 * p.2) '' ((fromLocH S B '' C) ×ˢ kerSetH S B) := by
  set b := fromLocH S B (toLocH S B a) with hb
  refine ⟨(b, b⁻¹ * a), ⟨⟨toLocH S B a, haC, rfl⟩, ?_⟩, mul_inv_cancel_left b a⟩
  have hbv : (b : Gt K L) = fromLoc S (toLoc S (a : Gt K L)) := by
    rw [hb, coe_fromLocH, valHP_toLocH]
  show ((b⁻¹ * a : B.H) : Gt K L) ∈ kerSet K L S
  have hval : ((b⁻¹ * a : B.H) : Gt K L) = (fromLoc S (toLoc S (a : Gt K L)))⁻¹ * (a : Gt K L) := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv, hbv]
  rw [hval]
  have hinf : tensorArch K L ((fromLoc S (toLoc S (a : Gt K L)))⁻¹ * (a : Gt K L)) = 1 := by
    rw [map_mul, map_inv, tensorArch_fromLoc, toLoc_apply_fst, inv_mul_cancel]
  have hfinS : ∀ v ∈ S, tensorPlace K L v ((fromLoc S (toLoc S (a : Gt K L)))⁻¹ * (a : Gt K L)) = 1 := by
    intro v hv
    rw [map_mul, map_inv, tensorPlace_fromLoc_of_mem S _ hv, toLoc_apply_snd, inv_mul_cancel]
  have hfin : ∀ v, v ∉ S →
      tensorPlace K L v ((fromLoc S (toLoc S (a : Gt K L)))⁻¹ * (a : Gt K L)) = tensorPlace K L v (a : Gt K L) := by
    intro v hv
    rw [map_mul, map_inv, tensorPlace_fromLoc_of_not_mem S _ hv, inv_one, one_mul]
  refine ⟨hinf, hfinS, fun v => ?_⟩
  by_cases hv : v ∈ S
  · rw [hfinS v hv]; exact one_mem_semiLocalIntegralSet K L v
  · rw [hfin v hv]; exact haU v hv

theorem preimage_inter_subsetH (C : Set (HP S B)) :
    toLocH S B ⁻¹' C ∩ unitsAwayH S B ⊆
      (fun p : B.H × B.H => p.1 * p.2) '' ((fromLocH S B '' C) ×ˢ kerSetH S B) :=
  fun _ ha => mem_image_mul_of_memH S B C ha.2 ha.1

end BoxMaps

section BoxPush

variable (τ : Measure B.H) [IsHaarMeasure τ]

def locMeasureH : Measure (HP S B) := Measure.map (toLocH S B) (τ.restrict (unitsAwayH S B))

theorem map_mul_left_restrict_unitsAwayH {g : B.H} (hg : g ∈ unitsAwayH S B) :
    Measure.map (fun a => g * a) (τ.restrict (unitsAwayH S B)) = τ.restrict (unitsAwayH S B) := by
  have hemb : MeasurableEmbedding (fun a : B.H => g * a) := (MeasurableEquiv.mulLeft g).measurableEmbedding
  have hpre : (fun a => g * a) ⁻¹' unitsAwayH S B = unitsAwayH S B := by
    ext a
    simp only [Set.mem_preimage]
    exact mul_mem_unitsAwayH_iff S B hg a
  calc Measure.map (fun a => g * a) (τ.restrict (unitsAwayH S B))
      = Measure.map (fun a => g * a) (τ.restrict ((fun a => g * a) ⁻¹' unitsAwayH S B)) := by rw [hpre]
    _ = (Measure.map (fun a => g * a) τ).restrict (unitsAwayH S B) := (hemb.restrict_map _ _).symm
    _ = τ.restrict (unitsAwayH S B) := by rw [map_mul_left_eq_self]

scoped instance isMulLeftInvariant_locMeasureH : (locMeasureH S B τ).IsMulLeftInvariant := by
  refine ⟨fun x => ?_⟩
  have hmeas : Measurable (toLocH S B) := (continuous_toLocH S B).measurable
  have hmx : Measurable (fun y : HP S B => x * y) := measurable_const_mul x
  rw [locMeasureH, Measure.map_map hmx hmeas]
  have hcomp : (fun y => x * y) ∘ toLocH S B = toLocH S B ∘ (fun a => fromLocH S B x * a) := by
    funext a
    simp only [Function.comp_apply, map_mul, toLocH_fromLocH]
  rw [hcomp, ← Measure.map_map hmeas (measurable_const_mul _),
    map_mul_left_restrict_unitsAwayH S B τ (fromLocH_mem_unitsAwayH S B x)]

scoped instance isFiniteMeasureOnCompacts_locMeasureH : IsFiniteMeasureOnCompacts (locMeasureH S B τ) := by
  refine ⟨fun C hC => ?_⟩
  rw [locMeasureH, Measure.map_apply (continuous_toLocH S B).measurable hC.measurableSet,
    Measure.restrict_apply ((continuous_toLocH S B).measurable hC.measurableSet)]
  have hK : IsCompact ((fun p : B.H × B.H => p.1 * p.2) '' ((fromLocH S B '' C) ×ˢ kerSetH S B)) :=
    ((hC.image (continuous_fromLocH S B)).prod (isCompact_kerSetH S B)).image continuous_mul
  exact (measure_mono (preimage_inter_subsetH S B C)).trans_lt hK.measure_lt_top

omit [IsHaarMeasure τ] in
theorem locMeasureH_univ : locMeasureH S B τ Set.univ = τ (unitsAwayH S B) := by
  rw [locMeasureH, Measure.map_apply (continuous_toLocH S B).measurable MeasurableSet.univ, Set.preimage_univ,
    Measure.restrict_apply_univ]

theorem locMeasureH_ne_zero : locMeasureH S B τ ≠ 0 := by
  intro h
  have h1 := congrArg (fun m : Measure (HP S B) => m Set.univ) h
  simp only [locMeasureH_univ, Measure.coe_zero, Pi.zero_apply] at h1
  exact (isOpen_unitsAwayH S B).measure_ne_zero τ
    ⟨1, show ((1 : B.H) : Gt K L) ∈ unitsAway K L S from one_mem _⟩ h1

variable (τa : Measure B.Ha) [IsHaarMeasure τa]
  (τf : ∀ v : HeightOneSpectrum (𝓞 K), Measure (B.Hv v)) [∀ v, IsHaarMeasure (τf v)]

scoped instance instSigmaFiniteτf (v : HeightOneSpectrum (𝓞 K)) : SigmaFinite (τf v) := inferInstance

scoped instance isHaarMeasure_piH : (Measure.pi fun v : S => τf v.1 : Measure (HS S B)).IsHaarMeasure :=
  Measure.pi.isHaarMeasure _

scoped instance sigmaFinite_piH : SigmaFinite (Measure.pi fun v : S => τf v.1 : Measure (HS S B)) := inferInstance

def refMeasureH : Measure (HP S B) := τa.prod (Measure.pi fun v : S => τf v.1)

scoped instance isHaarMeasure_refMeasureH : (refMeasureH S B τa τf).IsHaarMeasure := by
  unfold refMeasureH; infer_instance

def kappaH : ℝ≥0 := haarScalarFactor (locMeasureH S B τ) (refMeasureH S B τa τf)

theorem locMeasureH_eq_smul : locMeasureH S B τ = kappaH S B τ τa τf • refMeasureH S B τa τf :=
  isMulLeftInvariant_eq_smul _ _

theorem kappaH_ne_zero : kappaH S B τ τa τf ≠ 0 := by
  intro hc
  have h := locMeasureH_eq_smul S B τ τa τf
  rw [hc, zero_smul] at h
  exact locMeasureH_ne_zero S B τ h

theorem integral_eq_kappaH_mul (W : Gt K L → ℂ) (Wa : Ht K L → ℂ)
    (WS : ∀ v : HeightOneSpectrum (𝓞 K), Gsl K L v → ℂ)
    (hWa : AEStronglyMeasurable (fun t : B.Ha => Wa t) τa)
    (hWS : ∀ v ∈ S, AEStronglyMeasurable (fun t : B.Hv v => WS v t) (τf v))
    (hWe : ∀ t : B.H, (∀ v ∉ S, tensorPlace K L v (t : Gt K L) ∈ semiLocalIntegralSet K L v) →
      W t = Wa (tensorArch K L (t : Gt K L)) * ∏ v ∈ S, WS v (tensorPlace K L v (t : Gt K L)))
    (hW0 : ∀ t : B.H, (∃ v ∉ S, tensorPlace K L v (t : Gt K L) ∉ semiLocalIntegralSet K L v) → W t = 0) :
    ∫ t, W t ∂τ = kappaH S B τ τa τf * (∫ t, Wa t ∂τa) * ∏ v ∈ S, ∫ t, WS v t ∂(τf v) := by
  set F : HP S B → ℂ := fun x => Wa (x.1 : Ht K L) * ∏ v : S, WS v.1 ((x.2 v : Gsl K L v.1)) with hF
  have hoff : ∀ t, t ∉ unitsAwayH S B → W t = 0 := by
    intro t ht
    apply hW0
    by_contra hcon
    push Not at hcon
    exact ht fun v hv => hcon v hv
  have hon : Set.EqOn (fun t : B.H => W t) (F ∘ toLocH S B) (unitsAwayH S B) := by
    intro t ht
    simp only [Function.comp_apply, hF, coe_toLocH_fst, coe_toLocH_snd]
    rw [hWe t ht, ← Finset.prod_coe_sort S (fun v => WS v (tensorPlace K L v (t : Gt K L)))]
  have hFm : AEStronglyMeasurable F (refMeasureH S B τa τf) := by
    have h1 : AEStronglyMeasurable (fun x : HP S B => Wa (x.1 : Ht K L)) (refMeasureH S B τa τf) :=
      MeasureTheory.AEStronglyMeasurable.comp_fst hWa
    have h2' : AEStronglyMeasurable (fun t : HS S B => ∏ v : S, WS v.1 ((t v : Gsl K L v.1)))
        (Measure.pi fun v : S => τf v.1) := by
      refine Finset.aestronglyMeasurable_fun_prod Finset.univ fun v _ => ?_
      exact (hWS v.1 v.2).comp_quasiMeasurePreserving
        (Measure.quasiMeasurePreserving_eval (fun w : S => τf w.1) v)
    have h2 : AEStronglyMeasurable (fun x : HP S B => ∏ v : S, WS v.1 ((x.2 v : Gsl K L v.1)))
        (refMeasureH S B τa τf) :=
      MeasureTheory.AEStronglyMeasurable.comp_snd h2'
    exact h1.mul h2
  have hFm' : AEStronglyMeasurable F (locMeasureH S B τ) := by
    rw [locMeasureH_eq_smul S B τ τa τf]
    exact hFm.smul_measure _
  calc ∫ t, W t ∂τ
      = ∫ t in unitsAwayH S B, W t ∂τ := (setIntegral_eq_integral_of_forall_compl_eq_zero hoff).symm
    _ = ∫ t in unitsAwayH S B, (F ∘ toLocH S B) t ∂τ := setIntegral_congr_fun (measurableSet_unitsAwayH S B) hon
    _ = ∫ x, F x ∂(locMeasureH S B τ) := by
        rw [locMeasureH, integral_map (continuous_toLocH S B).measurable.aemeasurable]
        · rfl
        · rw [← locMeasureH]; exact hFm'
    _ = kappaH S B τ τa τf * ∫ x, F x ∂(refMeasureH S B τa τf) := by
        rw [locMeasureH_eq_smul S B τ τa τf, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]
    _ = kappaH S B τ τa τf * ((∫ t, Wa t ∂τa) * ∏ v ∈ S, ∫ t, WS v t ∂(τf v)) := by
        congr 1
        rw [refMeasureH, hF, integral_prod_mul (μ := τa) (fun t : B.Ha => Wa t)
            (fun t : HS S B => ∏ v : S, WS v.1 ((t v : Gsl K L v.1))),
          integral_fintype_prod_eq_prod (ι := S) (E := fun v : S => B.Hv v.1)
            (fun (v : S) (t : B.Hv v.1) => WS v.1 (t : Gsl K L v.1)),
          Finset.prod_coe_sort S (fun v => ∫ t, WS v t ∂(τf v))]
    _ = kappaH S B τ τa τf * (∫ t, Wa t ∂τa) * ∏ v ∈ S, ∫ t, WS v t ∂(τf v) := by ring

end BoxPush

section BoxUniform

variable (τ : Measure B.H) [IsHaarMeasure τ] (τa : Measure B.Ha) [IsHaarMeasure τa]
  (τf : ∀ v : HeightOneSpectrum (𝓞 K), Measure (B.Hv v)) [∀ v, IsHaarMeasure (τf v)]
  (hτf1 : ∀ v, τf v (Subtype.val ⁻¹' semiLocalIntegralSet K L v) = 1)

def archCompactH : PositiveCompacts B.Ha := Classical.arbitrary _

def testSetH : Set B.H :=
  {t : B.H | (⟨tensorArch K L (t : Gt K L), ((B.mem_iff t).1 t.2).1⟩ : B.Ha) ∈
      (archCompactH B : Set B.Ha) ∧ ∀ v, tensorPlace K L v (t : Gt K L) ∈ semiLocalIntegralSet K L v}

theorem mem_testSetH_iff (t : B.H) : t ∈ testSetH B ↔
    (⟨tensorArch K L (t : Gt K L), ((B.mem_iff t).1 t.2).1⟩ : B.Ha) ∈ (archCompactH B : Set B.Ha) ∧
      ∀ v, tensorPlace K L v (t : Gt K L) ∈ semiLocalIntegralSet K L v :=
  Iff.rfl

open scoped Classical in

def testFnH : Gt K L → ℂ := fun g =>
  if hg : g ∈ B.H then (testSetH B).indicator (fun _ => (1 : ℂ)) ⟨g, hg⟩ else 0

theorem testFnH_coe (t : B.H) : testFnH B (t : Gt K L) = (testSetH B).indicator (fun _ => (1 : ℂ)) t := by
  unfold testFnH
  rw [dif_pos t.2]

open scoped Classical in

def testFa : Ht K L → ℂ := fun x =>
  if hx : x ∈ B.Ha then ((archCompactH B : Set B.Ha).indicator (fun _ => (1 : ℂ))) ⟨x, hx⟩ else 0

theorem testFa_coe (x : B.Ha) : testFa B (x : Ht K L) = ((archCompactH B : Set B.Ha).indicator (fun _ => (1 : ℂ))) x := by
  unfold testFa
  rw [dif_pos x.2]

theorem testFnH_eq (t : B.H) (ht : ∀ v ∉ S, tensorPlace K L v (t : Gt K L) ∈ semiLocalIntegralSet K L v) :
    testFnH B t = testFa B (tensorArch K L (t : Gt K L)) *
      ∏ v ∈ S, ((semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ))) (tensorPlace K L v (t : Gt K L)) := by
  classical
  rw [testFnH_coe]
  have hfa : testFa B (tensorArch K L (t : Gt K L)) =
      ((archCompactH B : Set B.Ha).indicator (fun _ => (1 : ℂ)))
        (⟨tensorArch K L (t : Gt K L), ((B.mem_iff t).1 t.2).1⟩ : B.Ha) :=
    testFa_coe B ⟨tensorArch K L (t : Gt K L), ((B.mem_iff t).1 t.2).1⟩
  rw [hfa]
  by_cases harch : (⟨tensorArch K L (t : Gt K L), ((B.mem_iff t).1 t.2).1⟩ : B.Ha) ∈ (archCompactH B : Set B.Ha)
  · rw [Set.indicator_of_mem harch]
    by_cases hall : ∀ v, tensorPlace K L v (t : Gt K L) ∈ semiLocalIntegralSet K L v
    · rw [Set.indicator_of_mem ((mem_testSetH_iff B t).2 ⟨harch, hall⟩), one_mul]
      exact (Finset.prod_eq_one fun v _ => Set.indicator_of_mem (hall v) _).symm
    · rw [Set.indicator_of_notMem (fun h => hall ((mem_testSetH_iff B t).1 h).2), one_mul]
      obtain ⟨v, hv⟩ : ∃ v, tensorPlace K L v (t : Gt K L) ∉ semiLocalIntegralSet K L v := by
        by_contra hcon; push Not at hcon; exact hall hcon
      have hvS : v ∈ S := by by_contra hvS; exact hv (ht v hvS)
      exact (Finset.prod_eq_zero hvS (Set.indicator_of_notMem hv _)).symm
  · rw [Set.indicator_of_notMem harch, zero_mul,
      Set.indicator_of_notMem (fun h => harch ((mem_testSetH_iff B t).1 h).1)]

theorem testFnH_eq_zero (t : B.H) (ht : ∃ v ∉ S, tensorPlace K L v (t : Gt K L) ∉ semiLocalIntegralSet K L v) :
    testFnH B t = 0 := by
  obtain ⟨v, -, hv⟩ := ht
  rw [testFnH_coe]
  exact Set.indicator_of_notMem (fun h => hv (((mem_testSetH_iff B t).1 h).2 v)) _

theorem indicator_comp_val_eq (v : HeightOneSpectrum (𝓞 K)) :
    (fun t : B.Hv v => (semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ)) (t : Gsl K L v)) =
      (Subtype.val ⁻¹' semiLocalIntegralSet K L v : Set (B.Hv v)).indicator (fun _ => (1 : ℂ)) := by
  funext t
  by_cases h : (t : Gsl K L v) ∈ semiLocalIntegralSet K L v
  · have h' : t ∈ (Subtype.val ⁻¹' semiLocalIntegralSet K L v : Set (B.Hv v)) := h
    rw [Set.indicator_of_mem h, Set.indicator_of_mem h']
  · have h' : t ∉ (Subtype.val ⁻¹' semiLocalIntegralSet K L v : Set (B.Hv v)) := h
    rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h']

include hτf1 in
theorem integral_testFnH_eq :
    ∫ t, testFnH B t ∂τ = kappaH S B τ τa τf * (τa.real (archCompactH B : Set B.Ha)) := by
  have hmeasA : MeasurableSet (archCompactH B : Set B.Ha) := (archCompactH B).isCompact.isClosed.measurableSet
  have hmeasv : ∀ v, MeasurableSet (Subtype.val ⁻¹' semiLocalIntegralSet K L v : Set (B.Hv v)) := fun v =>
    ((isCompact_semiLocalIntegralSet K L v).isClosed.preimage continuous_subtype_val).measurableSet
  have hfa_eq : (fun x : B.Ha => testFa B x) = (archCompactH B : Set B.Ha).indicator (fun _ => (1 : ℂ)) :=
    funext fun x => testFa_coe B x
  have hfa : AEStronglyMeasurable (fun x : B.Ha => testFa B x) τa := by
    rw [hfa_eq]
    exact aestronglyMeasurable_const.indicator hmeasA
  have hfS : ∀ v ∈ S, AEStronglyMeasurable
      (fun t : B.Hv v => (semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ)) (t : Gsl K L v)) (τf v) := by
    intro v _
    rw [indicator_comp_val_eq B v]
    exact aestronglyMeasurable_const.indicator (hmeasv v)
  have h := integral_eq_kappaH_mul S B τ τa τf (testFnH B) (testFa B)
    (fun v => (semiLocalIntegralSet K L v).indicator fun _ => (1 : ℂ)) hfa hfS (testFnH_eq S B) (testFnH_eq_zero S B)
  rw [h]
  have ha : ∫ x : B.Ha, testFa B x ∂τa = τa.real (archCompactH B : Set B.Ha) := by
    rw [hfa_eq, integral_indicator_const _ hmeasA]
    simp [Complex.real_smul]
  have h1 : ∀ v ∈ S, ∫ t : B.Hv v,
      (semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ)) (t : Gsl K L v) ∂(τf v) = 1 := by
    intro v _
    rw [indicator_comp_val_eq B v, integral_indicator_const _ (hmeasv v), Measure.real, hτf1 v]
    simp
  rw [ha, Finset.prod_eq_one h1, mul_one]

theorem real_archCompactH_ne_zero : τa.real (archCompactH B : Set B.Ha) ≠ 0 := by
  rw [Measure.real, ENNReal.toReal_ne_zero]
  exact ⟨(measure_pos_of_nonempty_interior τa (archCompactH B).interior_nonempty).ne',
    (archCompactH B).isCompact.measure_lt_top.ne⟩

include hτf1 in
theorem kappaH_eq_kappaH_empty : kappaH S B τ τa τf = kappaH ∅ B τ τa τf := by
  have h1 := integral_testFnH_eq S B τ τa τf hτf1
  have h2 := integral_testFnH_eq ∅ B τ τa τf hτf1
  rw [h1] at h2
  have hpos := real_archCompactH_ne_zero B τa
  have h3 : ((kappaH S B τ τa τf : ℝ) : ℂ) = ((kappaH ∅ B τ τa τf : ℝ) : ℂ) :=
    mul_right_cancel₀ (Complex.ofReal_ne_zero.mpr hpos) h2
  exact_mod_cast h3

include hτf1 in

theorem exists_integral_box_eq :
    ∃ c : ℝ, 0 < c ∧
      ∀ (S : Finset (HeightOneSpectrum (𝓞 K))) (W : Gt K L → ℂ) (Wa : Ht K L → ℂ)
        (WS : ∀ v : HeightOneSpectrum (𝓞 K), Gsl K L v → ℂ),
        AEStronglyMeasurable (fun t : B.Ha => Wa t) τa →
        (∀ v ∈ S, AEStronglyMeasurable (fun t : B.Hv v => WS v t) (τf v)) →
        (∀ t : B.H, (∀ v ∉ S, tensorPlace K L v (t : Gt K L) ∈ semiLocalIntegralSet K L v) →
            W t = Wa (tensorArch K L (t : Gt K L)) * ∏ v ∈ S, WS v (tensorPlace K L v (t : Gt K L))) →
        (∀ t : B.H, (∃ v ∉ S, tensorPlace K L v (t : Gt K L) ∉ semiLocalIntegralSet K L v) → W t = 0) →
          ∫ t, W t ∂τ = c * (∫ t, Wa t ∂τa) * ∏ v ∈ S, ∫ t, WS v t ∂(τf v) := by
  refine ⟨(kappaH ∅ B τ τa τf : ℝ), NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (kappaH_ne_zero ∅ B τ τa τf)),
    fun S W Wa WS hWa hWS hWe hW0 => ?_⟩
  rw [← kappaH_eq_kappaH_empty S B τ τa τf hτf1]
  exact integral_eq_kappaH_mul S B τ τa τf W Wa WS hWa hWS hWe hW0

end BoxUniform

section Twisted

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

def twistedCentralizerBox (σ : L ≃ₐ[K] L) (δ : Gt K L) : BoxData K L where
  H := twistedCentralizer K L (AdeleRing (𝓞 K) K) σ δ
  Ha := twistedCentralizer K L (InfiniteAdeleRing K) σ (tensorArch K L δ)
  Hv v := twistedCentralizer K L (v.adicCompletion K) σ (tensorPlace K L v δ)
  isClosed_H := isClosed_twistedCentralizer K L _ σ δ
  isClosed_Ha := isClosed_twistedCentralizer K L _ σ _
  isClosed_Hv v := isClosed_twistedCentralizer K L _ σ _
  mem_iff g := by
    simp only [mem_sigmaCentralizer_iff]
    constructor
    · intro h
      refine ⟨?_, fun v => ?_⟩
      · rw [← tensorArch_sigmaGL, ← map_inv, ← map_mul, ← map_mul, h]
      · rw [← tensorPlace_sigmaGL, ← map_inv, ← map_mul, ← map_mul, h]
    · rintro ⟨h1, h2⟩
      refine eq_of_tensorArch_eq_of_forall_tensorPlace_eq K L ?_ fun v => ?_
      · rw [map_mul, map_mul, map_inv, tensorArch_sigmaGL]; exact h1
      · rw [map_mul, map_mul, map_inv, tensorPlace_sigmaGL]; exact h2 v

end Twisted

end AutomorphicForm.TwistedCentralizerHaarFactor
p2m_reactivate "P2MW.S_AutomorphicForm_exists_integral_twistedCentralizer_eq_mul_integral_mul_prod_integral_of_isHaarMeasure.AutomorphicForm P2MW.S_AutomorphicForm_exists_integral_twistedCentralizer_eq_mul_integral_mul_prod_integral_of_isHaarMeasure.AutomorphicForm.TwistedCentralizerHaarFactor"
p2m_reactivate "P2MW.S_AutomorphicForm_exists_integral_twistedCentralizer_eq_mul_integral_mul_prod_integral_of_isHaarMeasure.AutomorphicForm"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_integral_twistedCentralizer_eq_mul_integral_mul_prod_integral_of_isHaarMeasure.AutomorphicForm P2MW.S_AutomorphicForm_exists_integral_twistedCentralizer_eq_mul_integral_mul_prod_integral_of_isHaarMeasure.AutomorphicForm.TwistedCentralizerHaarFactor"

section Solution

open MeasureTheory NumberField NumberField.AdelicHaar IsDedekindDomain
open AutomorphicForm.TwistedCentralizerHaarFactor
open scoped TensorProduct TensorProduct.RightActions

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (σ : L ≃ₐ[K] L) (δ : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))
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
      τf v (Subtype.val ⁻¹' AutomorphicForm.semiLocalIntegralSet K L v) = 1) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (S : Finset (HeightOneSpectrum (𝓞 K)))
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
          ∫ t, W t ∂τ = c * (∫ t, Wa t ∂τa) * ∏ v ∈ S, ∫ t, WS v t ∂(τf v) := by
  let B : BoxData K L := twistedCentralizerBox σ δ
  haveI : Measure.IsHaarMeasure (show Measure B.H from τ) := hτ
  haveI : Measure.IsHaarMeasure (show Measure B.Ha from τa) := hτa
  haveI : ∀ v, Measure.IsHaarMeasure (show Measure (B.Hv v) from τf v) := hτf
  exact exists_integral_box_eq B τ τa τf hτf1

end Solution
p2m_reactivate "P2MW.S_AutomorphicForm_exists_integral_twistedCentralizer_eq_mul_integral_mul_prod_integral_of_isHaarMeasure.AutomorphicForm P2MW.S_AutomorphicForm_exists_integral_twistedCentralizer_eq_mul_integral_mul_prod_integral_of_isHaarMeasure.AutomorphicForm.TwistedCentralizerHaarFactor"

end S_AutomorphicForm_exists_integral_twistedCentralizer_eq_mul_integral_mul_prod_integral_of_isHaarMeasure
end P2MW
export P2MW.S_AutomorphicForm_exists_integral_twistedCentralizer_eq_mul_integral_mul_prod_integral_of_isHaarMeasure (solution)
