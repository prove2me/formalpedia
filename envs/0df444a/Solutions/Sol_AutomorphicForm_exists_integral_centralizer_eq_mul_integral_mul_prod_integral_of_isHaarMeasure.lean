-- Prove2me | solution 1 for AutomorphicForm.exists_integral_centralizer_eq_mul_integral_mul_prod_integral_of_isHaarMeasure
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/01e9d54d-4e9e-588e-9d0f-3237cfc6eaa8

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_AdelicHaar
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Integral.Pi
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_AutomorphicForm_exists_integral_centralizer_eq_mul_integral_mul_prod_integral_of_isHaarMeasure

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory MeasureTheory.Measure Topology TopologicalSpace Set Filter
open NumberField.AdelicLevel

open scoped NNReal ENNReal

noncomputable section

namespace AutomorphicForm
p2m_export "AutomorphicForm" "glBorelOf centralizerBorel integralUnitsSet localIntegralSet one_mem_localIntegralSet isCompact_localIntegralSet localGLBorel locallyCompactSpace_localGL localHaar isHaarMeasure_localHaar localCentralizer localCentralizerBorel unitFinSet one_mem_unitFinSet isOpen_unitFinSet"
namespace AdelicCentralizerHaarFactor
p2m_open "AutomorphicForm"

variable {K : Type} [Field K] [NumberField K]

abbrev Garch (K : Type) [Field K] [NumberField K] : Type := GL (Fin 2) (InfiniteAdeleRing K)

abbrev Gfin (K : Type) [Field K] [NumberField K] : Type := GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)

abbrev Gad (K : Type) [Field K] [NumberField K] : Type := GL (Fin 2) (AdeleRing (𝓞 K) K)

abbrev Gv (v : HeightOneSpectrum (𝓞 K)) : Type := GL (Fin 2) (v.adicCompletion K)

abbrev SProd (S : Finset (HeightOneSpectrum (𝓞 K))) : Type := (v : S) → Gv (K := K) v.1

abbrev LocProd (S : Finset (HeightOneSpectrum (𝓞 K))) : Type := Garch K × SProd (K := K) S

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

scoped instance instMeasurableSpaceGarch : MeasurableSpace (Garch K) := borel _
scoped instance instBorelSpaceGarch : BorelSpace (Garch K) := ⟨rfl⟩
scoped instance instMeasurableSpaceGv (v : HeightOneSpectrum (𝓞 K)) : MeasurableSpace (Gv (K := K) v) := borel _
scoped instance instBorelSpaceGv (v : HeightOneSpectrum (𝓞 K)) : BorelSpace (Gv (K := K) v) := ⟨rfl⟩
scoped instance instMeasurableSpaceGad : MeasurableSpace (Gad K) := borel _
scoped instance instBorelSpaceGad : BorelSpace (Gad K) := ⟨rfl⟩

variable (S : Finset (HeightOneSpectrum (𝓞 K)))

scoped instance instBorelSpaceSProd : BorelSpace (SProd (K := K) S) := Pi.borelSpace
scoped instance instBorelSpaceLocProd : BorelSpace (LocProd (K := K) S) := Prod.borelSpace

set_option synthInstance.maxHeartbeats 800000 in
scoped instance instLocallyCompactLocProd : LocallyCompactSpace (LocProd (K := K) S) := inferInstance

scoped instance instMeasurableMulGarch : MeasurableMul (Garch K) := inferInstance
scoped instance instMeasurableMulGv (v : HeightOneSpectrum (𝓞 K)) : MeasurableMul (Gv (K := K) v) := inferInstance
scoped instance instMeasurableMulGad : MeasurableMul (Gad K) := inferInstance

set_option synthInstance.maxHeartbeats 800000 in
scoped instance instMeasurableMulSProd : MeasurableMul (SProd (K := K) S) := inferInstance

set_option synthInstance.maxHeartbeats 800000 in
scoped instance instMeasurableMulLocProd : MeasurableMul (LocProd (K := K) S) := inferInstance

scoped instance instSigmaCompactGv (v : HeightOneSpectrum (𝓞 K)) : SigmaCompactSpace (Gv (K := K) v) :=
  sigmaCompactSpace_of_locallyCompact_secondCountable

scoped instance instSigmaCompactGarch : SigmaCompactSpace (Garch K) :=
  sigmaCompactSpace_of_locallyCompact_secondCountable

scoped instance instIsHaarLocalHaar (v : HeightOneSpectrum (𝓞 K)) : IsHaarMeasure (localHaar K v) :=
  isHaarMeasure_localHaar K v

scoped instance instSigmaFiniteLocalHaar (v : HeightOneSpectrum (𝓞 K)) : SigmaFinite (localHaar K v) :=
  inferInstance

scoped instance isHaarMeasure_pi :
    (Measure.pi fun v : S => localHaar K v.1 : Measure (SProd (K := K) S)).IsHaarMeasure :=
  Measure.pi.isHaarMeasure _

scoped instance sigmaFinite_pi :
    SigmaFinite (Measure.pi fun v : S => localHaar K v.1 : Measure (SProd (K := K) S)) :=
  inferInstance

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

variable (S : Finset (HeightOneSpectrum (𝓞 K)))

abbrev cpt (v : HeightOneSpectrum (𝓞 K)) (g : Gad K) : Gv (K := K) v :=
  finComponent (𝓞 K) K v (glFin (𝓞 K) K g)

theorem cpt_mul (v : HeightOneSpectrum (𝓞 K)) (g h : Gad K) : cpt v (g * h) = cpt v g * cpt v h := by
  simp only [cpt, map_mul]

theorem cpt_inv (v : HeightOneSpectrum (𝓞 K)) (g : Gad K) : cpt v g⁻¹ = (cpt v g)⁻¹ := by
  simp only [cpt, map_inv]

theorem cpt_one (v : HeightOneSpectrum (𝓞 K)) : cpt v (1 : Gad K) = 1 := by
  simp only [cpt, map_one]

def unitsAway : Subgroup (Gad K) where
  carrier := {g | ∀ v ∉ S, cpt v g ∈ localIntegralSet K v}
  mul_mem' {g h} hg hh v hv := by
    rw [cpt_mul]
    exact mul_mem_integralUnitsSet (v.adicCompletionIntegers K).toSubring (hg v hv) (hh v hv)
  one_mem' v _ := by rw [cpt_one]; exact one_mem_localIntegralSet K v
  inv_mem' {g} hg v hv := by
    rw [cpt_inv]
    exact inv_mem_integralUnitsSet _ (hg v hv)

theorem mem_unitsAway_iff (g : Gad K) : g ∈ unitsAway S ↔ ∀ v ∉ S, cpt v g ∈ localIntegralSet K v :=
  Iff.rfl

theorem continuous_cpt (v : HeightOneSpectrum (𝓞 K)) : Continuous (cpt (K := K) v) :=
  (continuous_finComponent (𝓞 K) K v).comp (continuous_glFin (𝓞 K) K)

theorem isOpen_unitsAway : IsOpen (unitsAway S : Set (Gad K)) := by
  refine Subgroup.isOpen_of_mem_nhds (unitsAway S) (g := 1) ?_
  have h1 : (glFin (𝓞 K) K) ⁻¹' unitFinSet K ⊆ (unitsAway S : Set (Gad K)) := fun g hg v _ => hg v
  refine Filter.mem_of_superset ?_ h1
  exact ((isOpen_unitFinSet K).preimage (continuous_glFin (𝓞 K) K)).mem_nhds
    (by rw [Set.mem_preimage, map_one]; exact one_mem_unitFinSet K)

theorem measurableSet_unitsAway : MeasurableSet (unitsAway S : Set (Gad K)) :=
  (isOpen_unitsAway S).measurableSet

section Embedding

open scoped Classical in

def finPrincipal (a : (w : HeightOneSpectrum (𝓞 K)) → w.adicCompletion K)
    (ha : ∀ w, a w ∈ w.adicCompletionIntegers K)
    (t : (v : S) → v.1.adicCompletion K) :
    RestrictedProduct (fun w : HeightOneSpectrum (𝓞 K) => w.adicCompletion K)
      (fun w : HeightOneSpectrum (𝓞 K) => (w.adicCompletionIntegers K : Set (w.adicCompletion K)))
      (𝓟 ((↑S : Set (HeightOneSpectrum (𝓞 K)))ᶜ)) :=
  ⟨fun w => if h : w ∈ S then t ⟨w, h⟩ else a w,
    Filter.eventually_principal.mpr fun w hw => by
      have hwS : w ∉ S := hw
      simp only [dif_neg hwS]
      exact ha w⟩

omit [NumberField K] in
theorem cofinite_le_principal_compl :
    (cofinite : Filter (HeightOneSpectrum (𝓞 K))) ≤ 𝓟 ((↑S : Set (HeightOneSpectrum (𝓞 K)))ᶜ) :=
  Filter.le_principal_iff.mpr S.finite_toSet.compl_mem_cofinite

open scoped Classical in

def finAdeleOf (a : (w : HeightOneSpectrum (𝓞 K)) → w.adicCompletion K)
    (ha : ∀ w, a w ∈ w.adicCompletionIntegers K)
    (t : (v : S) → v.1.adicCompletion K) : FiniteAdeleRing (𝓞 K) K :=
  RestrictedProduct.inclusion (fun w : HeightOneSpectrum (𝓞 K) => w.adicCompletion K)
    (fun w : HeightOneSpectrum (𝓞 K) => (w.adicCompletionIntegers K : Set (w.adicCompletion K)))
    (cofinite_le_principal_compl S) (finPrincipal S a ha t)

open scoped Classical in
theorem finAdeleOf_apply (a : (w : HeightOneSpectrum (𝓞 K)) → w.adicCompletion K)
    (ha : ∀ w, a w ∈ w.adicCompletionIntegers K) (t : (v : S) → v.1.adicCompletion K)
    (w : HeightOneSpectrum (𝓞 K)) :
    finAdeleOf S a ha t w = if h : w ∈ S then t ⟨w, h⟩ else a w := rfl

open scoped Classical in
theorem continuous_finAdeleOf (a : (w : HeightOneSpectrum (𝓞 K)) → w.adicCompletion K)
    (ha : ∀ w, a w ∈ w.adicCompletionIntegers K) : Continuous (finAdeleOf (K := K) S a ha) := by
  refine (RestrictedProduct.continuous_inclusion _).comp ?_
  refine RestrictedProduct.continuous_rng_of_principal_iff_forall.mpr fun w => ?_
  show Continuous fun t : (v : S) → v.1.adicCompletion K => if h : w ∈ S then t ⟨w, h⟩ else a w
  by_cases hw : w ∈ S
  · simp only [dif_pos hw]; exact continuous_apply _
  · simp only [dif_neg hw]; exact continuous_const

def sMat (t : (v : S) → Matrix (Fin 2) (Fin 2) (v.1.adicCompletion K)) :
    Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K) :=
  Matrix.of fun i j => finAdeleOf S (fun w => (1 : Matrix (Fin 2) (Fin 2) (w.adicCompletion K)) i j)
    (fun w => by
      show (1 : Matrix (Fin 2) (Fin 2) (w.adicCompletion K)) i j ∈ w.adicCompletionIntegers K
      rw [Matrix.one_apply]
      split_ifs
      · exact one_mem _
      · exact zero_mem _)
    (fun v => t v i j)

theorem sMat_apply_of_mem (t : (v : S) → Matrix (Fin 2) (Fin 2) (v.1.adicCompletion K)) (i j : Fin 2)
    {w : HeightOneSpectrum (𝓞 K)} (hw : w ∈ S) : sMat S t i j w = t ⟨w, hw⟩ i j := by
  classical
  simp only [sMat, Matrix.of_apply, finAdeleOf_apply, dif_pos hw]

theorem sMat_apply_of_not_mem (t : (v : S) → Matrix (Fin 2) (Fin 2) (v.1.adicCompletion K)) (i j : Fin 2)
    {w : HeightOneSpectrum (𝓞 K)} (hw : w ∉ S) :
    sMat S t i j w = (1 : Matrix (Fin 2) (Fin 2) (w.adicCompletion K)) i j := by
  classical
  simp only [sMat, Matrix.of_apply, finAdeleOf_apply, dif_neg hw]

theorem mapMatrix_sMat_of_mem (t : (v : S) → Matrix (Fin 2) (Fin 2) (v.1.adicCompletion K))
    {w : HeightOneSpectrum (𝓞 K)} (hw : w ∈ S) :
    (finAdeleEval (𝓞 K) K w).mapMatrix (sMat S t) = t ⟨w, hw⟩ := by
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, finAdeleEval_apply, sMat_apply_of_mem S t i j hw]

theorem mapMatrix_sMat_of_not_mem (t : (v : S) → Matrix (Fin 2) (Fin 2) (v.1.adicCompletion K))
    {w : HeightOneSpectrum (𝓞 K)} (hw : w ∉ S) :
    (finAdeleEval (𝓞 K) K w).mapMatrix (sMat S t) = 1 := by
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, finAdeleEval_apply, sMat_apply_of_not_mem S t i j hw]

theorem matrix_eq_of_forall_mapMatrix_eq {M N : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)}
    (h : ∀ w : HeightOneSpectrum (𝓞 K),
      (finAdeleEval (𝓞 K) K w).mapMatrix M = (finAdeleEval (𝓞 K) K w).mapMatrix N) :
    M = N := by
  ext i j w
  have hw := congrFun (congrFun (h w) i) j
  simpa only [RingHom.mapMatrix_apply, Matrix.map_apply, finAdeleEval_apply] using hw

theorem sMat_one : sMat S (fun _ => (1 : Matrix (Fin 2) (Fin 2) _)) = 1 := by
  refine matrix_eq_of_forall_mapMatrix_eq fun w => ?_
  by_cases hw : w ∈ S
  · rw [mapMatrix_sMat_of_mem S _ hw, map_one]
  · rw [mapMatrix_sMat_of_not_mem S _ hw, map_one]

theorem sMat_mul (t t' : (v : S) → Matrix (Fin 2) (Fin 2) (v.1.adicCompletion K)) :
    sMat S (fun v => t v * t' v) = sMat S t * sMat S t' := by
  refine matrix_eq_of_forall_mapMatrix_eq fun w => ?_
  by_cases hw : w ∈ S
  · rw [map_mul, mapMatrix_sMat_of_mem S _ hw, mapMatrix_sMat_of_mem S _ hw, mapMatrix_sMat_of_mem S _ hw]
  · rw [map_mul, mapMatrix_sMat_of_not_mem S _ hw, mapMatrix_sMat_of_not_mem S _ hw,
      mapMatrix_sMat_of_not_mem S _ hw, mul_one]

def sEmbedFin : SProd (K := K) S →* Gfin K where
  toFun t :=
    { val := sMat S fun v => (t v : Matrix (Fin 2) (Fin 2) _)
      inv := sMat S fun v => ((t v)⁻¹ : Gv (K := K) v.1)
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

theorem coe_sEmbedFin (t : SProd (K := K) S) :
    (sEmbedFin S t).val = sMat S fun v => (t v : Matrix (Fin 2) (Fin 2) _) :=
  rfl

theorem finComponent_sEmbedFin_of_mem (t : SProd (K := K) S) {w : HeightOneSpectrum (𝓞 K)} (hw : w ∈ S) :
    finComponent (𝓞 K) K w (sEmbedFin S t) = t ⟨w, hw⟩ := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [finComponent_apply, coe_sEmbedFin, sMat_apply_of_mem S _ i j hw]

theorem finComponent_sEmbedFin_of_not_mem (t : SProd (K := K) S) {w : HeightOneSpectrum (𝓞 K)}
    (hw : w ∉ S) : finComponent (𝓞 K) K w (sEmbedFin S t) = 1 := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [finComponent_apply, coe_sEmbedFin, sMat_apply_of_not_mem S _ i j hw, Units.val_one]

theorem matrix_eq_of_arch_fin_eq {M N : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)}
    (h₁ : (adeleArch (𝓞 K) K).mapMatrix M = (adeleArch (𝓞 K) K).mapMatrix N)
    (h₂ : (adeleFin (𝓞 K) K).mapMatrix M = (adeleFin (𝓞 K) K).mapMatrix N) : M = N := by
  ext i j
  have hw₁ := congrFun (congrFun h₁ i) j
  have hw₂ := congrFun (congrFun h₂ i) j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, adeleArch_apply, adeleFin_apply] at hw₁ hw₂
  exact Prod.ext hw₁ hw₂

def pairMat (a : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) (b : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) :
    Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K) :=
  Matrix.of fun i j => ((a i j, b i j) : AdeleRing (𝓞 K) K)

theorem mapMatrix_arch_pairMat (a : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K))
    (b : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) :
    (adeleArch (𝓞 K) K).mapMatrix (pairMat a b) = a := by
  ext i j; rfl

theorem mapMatrix_fin_pairMat (a : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K))
    (b : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) :
    (adeleFin (𝓞 K) K).mapMatrix (pairMat a b) = b := by
  ext i j; rfl

theorem pairMat_one : pairMat (K := K) 1 1 = 1 :=
  matrix_eq_of_arch_fin_eq (by rw [mapMatrix_arch_pairMat, map_one])
    (by rw [mapMatrix_fin_pairMat, map_one])

theorem pairMat_mul (a a' : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K))
    (b b' : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) :
    pairMat (a * a') (b * b') = pairMat a b * pairMat a' b' :=
  matrix_eq_of_arch_fin_eq
    (by rw [map_mul, mapMatrix_arch_pairMat, mapMatrix_arch_pairMat, mapMatrix_arch_pairMat])
    (by rw [map_mul, mapMatrix_fin_pairMat, mapMatrix_fin_pairMat, mapMatrix_fin_pairMat])

def pairGL : Garch K × Gfin K →* Gad K where
  toFun x :=
    { val := pairMat (x.1 : Matrix (Fin 2) (Fin 2) _) (x.2 : Matrix (Fin 2) (Fin 2) _)
      inv := pairMat ((x.1⁻¹ : Garch K) : Matrix (Fin 2) (Fin 2) _) ((x.2⁻¹ : Gfin K) : Matrix (Fin 2) (Fin 2) _)
      val_inv := by rw [← pairMat_mul]; simp only [Units.mul_inv]; exact pairMat_one
      inv_val := by rw [← pairMat_mul]; simp only [Units.inv_mul]; exact pairMat_one }
  map_one' := Units.ext (by simp only [Units.val_one, Prod.fst_one, Prod.snd_one]; exact pairMat_one)
  map_mul' x y := Units.ext (by
    simp only [Units.val_mul, Prod.fst_mul, Prod.snd_mul]
    exact pairMat_mul _ _ _ _)

theorem glArch_pairGL (x : Garch K × Gfin K) : glArch (𝓞 K) K (pairGL x) = x.1 :=
  Matrix.GeneralLinearGroup.ext fun _ _ => rfl

theorem glFin_pairGL (x : Garch K × Gfin K) : glFin (𝓞 K) K (pairGL x) = x.2 :=
  Matrix.GeneralLinearGroup.ext fun _ _ => rfl

def fromLoc : LocProd (K := K) S →* Gad K :=
  pairGL.comp ((MonoidHom.id (Garch K)).prodMap (sEmbedFin S))

theorem glArch_fromLoc (x : LocProd (K := K) S) : glArch (𝓞 K) K (fromLoc S x) = x.1 :=
  glArch_pairGL _

theorem glFin_fromLoc (x : LocProd (K := K) S) : glFin (𝓞 K) K (fromLoc S x) = sEmbedFin S x.2 :=
  glFin_pairGL _

theorem cpt_fromLoc_of_mem (x : LocProd (K := K) S) {w : HeightOneSpectrum (𝓞 K)} (hw : w ∈ S) :
    cpt w (fromLoc S x) = x.2 ⟨w, hw⟩ := by
  rw [cpt, glFin_fromLoc, finComponent_sEmbedFin_of_mem S _ hw]

theorem cpt_fromLoc_of_not_mem (x : LocProd (K := K) S) {w : HeightOneSpectrum (𝓞 K)} (hw : w ∉ S) :
    cpt w (fromLoc S x) = 1 := by
  rw [cpt, glFin_fromLoc, finComponent_sEmbedFin_of_not_mem S _ hw]

theorem fromLoc_mem_unitsAway (x : LocProd (K := K) S) : fromLoc S x ∈ unitsAway S := fun w hw => by
  rw [cpt_fromLoc_of_not_mem S x hw]
  exact one_mem_localIntegralSet K w

def toLoc : Gad K →* LocProd (K := K) S :=
  MonoidHom.prod (glArch (𝓞 K) K) (MonoidHom.pi fun v : S => (finComponent (𝓞 K) K v.1).comp (glFin (𝓞 K) K))

theorem toLoc_apply_fst (g : Gad K) : (toLoc S g).1 = glArch (𝓞 K) K g := rfl

theorem toLoc_apply_snd (g : Gad K) (v : S) : (toLoc S g).2 v = cpt v.1 g := rfl

theorem toLoc_fromLoc (x : LocProd (K := K) S) : toLoc S (fromLoc S x) = x := by
  refine Prod.ext ?_ (funext fun v => ?_)
  · rw [toLoc_apply_fst, glArch_fromLoc]
  · rw [toLoc_apply_snd, cpt_fromLoc_of_mem S x v.2]

theorem gad_ext {g h : Gad K} (h₁ : glArch (𝓞 K) K g = glArch (𝓞 K) K h) (h₂ : ∀ w, cpt w g = cpt w h) :
    g = h := by
  have e₁ : (glArch (𝓞 K) K g).val = (glArch (𝓞 K) K h).val := by rw [h₁]
  have e₂ : ∀ w, (cpt w g).val = (cpt w h).val := fun w => by rw [h₂ w]
  refine Matrix.GeneralLinearGroup.ext fun i j => Prod.ext ?_ ?_
  · exact congrFun (congrFun e₁ i) j
  · refine RestrictedProduct.ext (fun w : HeightOneSpectrum (𝓞 K) => w.adicCompletion K)
      (fun w : HeightOneSpectrum (𝓞 K) => (w.adicCompletionIntegers K : Set (w.adicCompletion K))) fun w => ?_
    exact congrFun (congrFun (e₂ w) i) j

theorem continuous_sEmbedFin : Continuous (sEmbedFin (K := K) S) := by
  have hval : Continuous fun t : SProd (K := K) S => (sEmbedFin S t).val := by
    refine continuous_matrix fun i j => ?_
    show Continuous fun t : SProd (K := K) S =>
      finAdeleOf S (fun w => (1 : Matrix (Fin 2) (Fin 2) (w.adicCompletion K)) i j) _
        (fun v => (t v).val i j)
    refine (continuous_finAdeleOf S _ _).comp (continuous_pi fun v => ?_)
    exact (Continuous.matrix_elem (Units.continuous_val.comp (continuous_apply v)) i j)
  refine Units.continuous_iff.mpr ⟨hval, ?_⟩
  have h : (fun t : SProd (K := K) S => ((sEmbedFin S t)⁻¹).val) =
      (fun t : SProd (K := K) S => (sEmbedFin S t).val) ∘ fun t => t⁻¹ := by
    funext t; simp only [Function.comp_apply, map_inv]
  rw [h]
  exact hval.comp continuous_inv

theorem continuous_pairGL : Continuous (pairGL (K := K)) := by
  have hval : ∀ (φ : Garch K × Gfin K → Garch K × Gfin K), Continuous φ →
      Continuous fun x => (pairGL (φ x)).val := by
    intro φ hφ
    refine continuous_matrix fun i j => ?_
    show Continuous fun x => (((φ x).1.val i j, (φ x).2.val i j) : AdeleRing (𝓞 K) K)
    exact ((Units.continuous_val.comp (continuous_fst.comp hφ)).matrix_elem i j).prodMk
      ((Units.continuous_val.comp (continuous_snd.comp hφ)).matrix_elem i j)
  refine Units.continuous_iff.mpr ⟨hval id continuous_id, ?_⟩
  have h : (fun x : Garch K × Gfin K => ((pairGL x)⁻¹).val) =
      fun x => (pairGL (x⁻¹)).val := by
    funext x; simp only [map_inv]
  rw [h]
  exact hval _ continuous_inv

theorem continuous_fromLoc : Continuous (fromLoc (K := K) S) :=
  continuous_pairGL.comp (continuous_id.prodMap (continuous_sEmbedFin S))

theorem continuous_toLoc : Continuous (toLoc (K := K) S) :=
  (continuous_glArch (𝓞 K) K).prodMk (continuous_pi fun v => continuous_cpt v.1)

end Embedding

section Kernel

def kerSet : Set (Gad K) :=
  {k | glArch (𝓞 K) K k = 1 ∧ (∀ v ∈ S, cpt v k = 1) ∧ ∀ v, cpt v k ∈ localIntegralSet K v}

def kerBox : Set (Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) :=
  {M | ∀ i j, (M i j).1 = (1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) i j ∧
    (M i j).2 ∈ integralFiniteAdeles (𝓞 K) K}

theorem kerBox_eq_pi : kerBox (K := K) = Set.pi Set.univ fun i : Fin 2 => Set.pi Set.univ fun j : Fin 2 =>
    ({(1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) i j} : Set (InfiniteAdeleRing K)) ×ˢ
      integralFiniteAdeles (𝓞 K) K := by
  ext M
  constructor
  · intro h i _ j _
    exact ⟨(h i j).1, (h i j).2⟩
  · intro h i j
    have hij := h i (Set.mem_univ i) j (Set.mem_univ j)
    exact ⟨hij.1, hij.2⟩

theorem isCompact_kerBox : IsCompact (kerBox (K := K)) := by
  rw [kerBox_eq_pi]
  exact isCompact_univ_pi fun i => isCompact_univ_pi fun j =>
    isCompact_singleton.prod (isCompact_integralFiniteAdeles (𝓞 K) K)

theorem val_mem_kerBox {k : Gad K} (h1 : glArch (𝓞 K) K k = 1) (h3 : ∀ v, cpt v k ∈ localIntegralSet K v) :
    k.val ∈ kerBox (K := K) := by
  intro i j
  refine ⟨?_, fun v => ?_⟩
  · have e₁ : (glArch (𝓞 K) K k).val = (1 : Garch K).val := by rw [h1]
    have := congrFun (congrFun e₁ i) j
    simpa only [glArch_apply, Units.val_one] using this
  · exact (h3 v).1 i j

theorem kerSet_subset_preimage :
    kerSet (K := K) S ⊆ Units.embedProduct (Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) ⁻¹'
      (kerBox ×ˢ (MulOpposite.op '' kerBox)) := by
  intro k hk
  obtain ⟨h1, -, h3⟩ := hk
  simp only [Set.mem_preimage, Units.embedProduct_apply, Set.mem_prod, Set.mem_image]
  refine ⟨val_mem_kerBox h1 h3, ⟨(k⁻¹).val, ?_, rfl⟩⟩
  refine val_mem_kerBox (by rw [map_inv, h1, inv_one]) fun v => ?_
  rw [cpt_inv]
  exact inv_mem_integralUnitsSet _ (h3 v)

theorem isClosed_kerSet : IsClosed (kerSet (K := K) S) := by
  have h1 : IsClosed {k : Gad K | glArch (𝓞 K) K k = 1} :=
    isClosed_eq (continuous_glArch (𝓞 K) K) continuous_const
  have h2 : IsClosed {k : Gad K | ∀ v ∈ S, cpt v k = 1} := by
    have : {k : Gad K | ∀ v ∈ S, cpt v k = 1} = ⋂ v ∈ S, {k | cpt v k = 1} := by
      ext k; simp only [Set.mem_setOf_eq, Set.mem_iInter]
    rw [this]
    exact isClosed_biInter fun v _ => isClosed_eq (continuous_cpt v) continuous_const
  have h3 : IsClosed {k : Gad K | ∀ v, cpt v k ∈ localIntegralSet K v} := by
    have : {k : Gad K | ∀ v, cpt v k ∈ localIntegralSet K v} = ⋂ v, cpt v ⁻¹' localIntegralSet K v := by
      ext k; simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage]
    rw [this]
    exact isClosed_iInter fun v =>
      (isCompact_localIntegralSet K v).isClosed.preimage (continuous_cpt v)
  have hK : kerSet (K := K) S = ({k : Gad K | glArch (𝓞 K) K k = 1} ∩ {k : Gad K | ∀ v ∈ S, cpt v k = 1}) ∩
      {k : Gad K | ∀ v, cpt v k ∈ localIntegralSet K v} := by
    ext k; simp only [kerSet, Set.mem_inter_iff, Set.mem_setOf_eq, and_assoc]
  rw [hK]
  exact (h1.inter h2).inter h3

theorem isCompact_kerSet : IsCompact (kerSet (K := K) S) :=
  (Units.isClosedEmbedding_embedProduct.isCompact_preimage
    (isCompact_kerBox.prod (isCompact_kerBox.image MulOpposite.continuous_op))).of_isClosed_subset
    (isClosed_kerSet S) (kerSet_subset_preimage S)

theorem mem_image_mul_of_mem (C : Set (LocProd (K := K) S)) {a : Gad K}
    (haU : a ∈ unitsAway S) (haC : toLoc S a ∈ C) :
    a ∈ (fun p : Gad K × Gad K => p.1 * p.2) '' ((fromLoc S '' C) ×ˢ kerSet S) := by
  set b := fromLoc S (toLoc S a) with hb
  refine ⟨(b, b⁻¹ * a), ⟨⟨toLoc S a, haC, rfl⟩, ?_⟩, mul_inv_cancel_left b a⟩
  have hinf : glArch (𝓞 K) K (b⁻¹ * a) = 1 := by
    rw [map_mul, map_inv, hb, glArch_fromLoc, toLoc_apply_fst, inv_mul_cancel]
  have hfinS : ∀ v ∈ S, cpt v (b⁻¹ * a) = 1 := by
    intro v hv
    rw [cpt_mul, cpt_inv, hb, cpt_fromLoc_of_mem S _ hv, toLoc_apply_snd, inv_mul_cancel]
  have hfin : ∀ v, v ∉ S → cpt v (b⁻¹ * a) = cpt v a := by
    intro v hv
    rw [cpt_mul, cpt_inv, hb, cpt_fromLoc_of_not_mem S _ hv, inv_one, one_mul]
  refine ⟨hinf, hfinS, fun v => ?_⟩
  by_cases hv : v ∈ S
  · rw [hfinS v hv]; exact one_mem_localIntegralSet K v
  · rw [hfin v hv]; exact haU v hv

theorem preimage_inter_subset (C : Set (LocProd (K := K) S)) :
    toLoc S ⁻¹' C ∩ (unitsAway S : Set (Gad K)) ⊆
      (fun p : Gad K × Gad K => p.1 * p.2) '' ((fromLoc S '' C) ×ˢ kerSet S) :=
  fun _ ha => mem_image_mul_of_mem S C ha.2 ha.1

end Kernel

structure BoxData (K : Type) [Field K] [NumberField K] where

  H : Subgroup (Gad K)

  Ha : Subgroup (Garch K)

  Hv : ∀ v : HeightOneSpectrum (𝓞 K), Subgroup (Gv (K := K) v)
  isClosed_H : IsClosed (H : Set (Gad K))
  isClosed_Ha : IsClosed (Ha : Set (Garch K))
  isClosed_Hv : ∀ v, IsClosed (Hv v : Set (Gv (K := K) v))
  mem_iff : ∀ g : Gad K, g ∈ H ↔ glArch (𝓞 K) K g ∈ Ha ∧ ∀ v, cpt v g ∈ Hv v

variable (B : BoxData K)

section BoxInstances

scoped instance (priority := 10000) instMeasurableSpaceH : MeasurableSpace B.H := borel _
scoped instance instBorelSpaceH : BorelSpace B.H := ⟨rfl⟩
scoped instance (priority := 10000) instMeasurableSpaceHa : MeasurableSpace B.Ha := borel _
scoped instance instBorelSpaceHa : BorelSpace B.Ha := ⟨rfl⟩
scoped instance (priority := 10000) instMeasurableSpaceHv (v : HeightOneSpectrum (𝓞 K)) : MeasurableSpace (B.Hv v) :=
  borel _
scoped instance instBorelSpaceHv (v : HeightOneSpectrum (𝓞 K)) : BorelSpace (B.Hv v) := ⟨rfl⟩

scoped instance instLocallyCompactH : LocallyCompactSpace B.H :=
  B.isClosed_H.isClosedEmbedding_subtypeVal.locallyCompactSpace
scoped instance instLocallyCompactHa : LocallyCompactSpace B.Ha :=
  B.isClosed_Ha.isClosedEmbedding_subtypeVal.locallyCompactSpace
scoped instance instLocallyCompactHv (v : HeightOneSpectrum (𝓞 K)) : LocallyCompactSpace (B.Hv v) :=
  (B.isClosed_Hv v).isClosedEmbedding_subtypeVal.locallyCompactSpace

scoped instance instSecondCountableHa : SecondCountableTopology B.Ha :=
  TopologicalSpace.Subtype.secondCountableTopology (B.Ha : Set (Garch K))
scoped instance instSecondCountableHv (v : HeightOneSpectrum (𝓞 K)) : SecondCountableTopology (B.Hv v) :=
  TopologicalSpace.Subtype.secondCountableTopology (B.Hv v : Set (Gv (K := K) v))

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
  toFun t := (⟨glArch (𝓞 K) K (t : Gad K), ((B.mem_iff t).1 t.2).1⟩,
    fun v => ⟨cpt v.1 (t : Gad K), ((B.mem_iff t).1 t.2).2 v.1⟩)
  map_one' := by
    refine Prod.ext (Subtype.ext ?_) (funext fun v => Subtype.ext ?_)
    · simp only [OneMemClass.coe_one, map_one]; rfl
    · simp only [OneMemClass.coe_one, cpt_one]; rfl
  map_mul' s t := by
    refine Prod.ext (Subtype.ext ?_) (funext fun v => Subtype.ext ?_)
    · simp only [Subgroup.coe_mul, map_mul]; rfl
    · simp only [Subgroup.coe_mul, cpt_mul]; rfl

theorem coe_toLocH_fst (t : B.H) : ((toLocH S B t).1 : Garch K) = glArch (𝓞 K) K (t : Gad K) := rfl

theorem coe_toLocH_snd (t : B.H) (v : S) : ((toLocH S B t).2 v : Gv (K := K) v.1) = cpt v.1 (t : Gad K) := rfl

theorem toLocH_eq (t : B.H) :
    toLoc S (t : Gad K) = (((toLocH S B t).1 : Garch K), fun v => ((toLocH S B t).2 v : Gv (K := K) v.1)) := rfl

def valHP (x : HP S B) : LocProd (K := K) S := ((x.1 : Garch K), fun v => (x.2 v : Gv (K := K) v.1))

theorem fromLoc_valHP_mem (x : HP S B) : fromLoc S (valHP S B x) ∈ B.H := by
  refine (B.mem_iff _).2 ⟨?_, fun w => ?_⟩
  · rw [glArch_fromLoc]; exact x.1.2
  · by_cases hw : w ∈ S
    · rw [cpt_fromLoc_of_mem S _ hw]; exact (x.2 ⟨w, hw⟩).2
    · rw [cpt_fromLoc_of_not_mem S _ hw]; exact one_mem _

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

theorem coe_fromLocH (x : HP S B) : ((fromLocH S B x : B.H) : Gad K) = fromLoc S (valHP S B x) := rfl

theorem toLocH_fromLocH (x : HP S B) : toLocH S B (fromLocH S B x) = x := by
  have h := toLoc_fromLoc S (valHP S B x)
  refine Prod.ext (Subtype.ext ?_) (funext fun v => Subtype.ext ?_)
  · have h1 := congrArg Prod.fst h
    exact h1
  · have h2 := congrFun (congrArg Prod.snd h) v
    exact h2

theorem continuous_toLocH : Continuous (toLocH S B) := by
  refine Continuous.prodMk ?_ (continuous_pi fun v => ?_)
  · exact ((continuous_glArch (𝓞 K) K).comp continuous_subtype_val).subtype_mk _
  · exact ((continuous_cpt v.1).comp continuous_subtype_val).subtype_mk _

theorem continuous_valHP : Continuous (valHP S B) :=
  (continuous_subtype_val.comp continuous_fst).prodMk
    (continuous_pi fun v => continuous_subtype_val.comp ((continuous_apply v).comp continuous_snd))

theorem continuous_fromLocH : Continuous (fromLocH S B) :=
  ((continuous_fromLoc S).comp (continuous_valHP S B)).subtype_mk _

def unitsAwayH : Set B.H := Subtype.val ⁻¹' (unitsAway S : Set (Gad K))

theorem isOpen_unitsAwayH : IsOpen (unitsAwayH S B) :=
  (isOpen_unitsAway S).preimage continuous_subtype_val

theorem measurableSet_unitsAwayH : MeasurableSet (unitsAwayH S B) :=
  (isOpen_unitsAwayH S B).measurableSet

theorem fromLocH_mem_unitsAwayH (x : HP S B) : fromLocH S B x ∈ unitsAwayH S B :=
  fromLoc_mem_unitsAway S _

theorem mul_mem_unitsAwayH_iff {g : B.H} (hg : g ∈ unitsAwayH S B) (a : B.H) :
    g * a ∈ unitsAwayH S B ↔ a ∈ unitsAwayH S B := by
  show (g : Gad K) * a ∈ (unitsAway S : Set (Gad K)) ↔ (a : Gad K) ∈ (unitsAway S : Set (Gad K))
  exact Subgroup.mul_mem_cancel_left _ hg

def kerSetH : Set B.H := Subtype.val ⁻¹' kerSet S

theorem isCompact_kerSetH : IsCompact (kerSetH S B) :=
  B.isClosed_H.isClosedEmbedding_subtypeVal.isCompact_preimage (isCompact_kerSet S)

theorem mem_image_mul_of_memH (C : Set (HP S B)) {a : B.H}
    (haU : a ∈ unitsAwayH S B) (haC : toLocH S B a ∈ C) :
    a ∈ (fun p : B.H × B.H => p.1 * p.2) '' ((fromLocH S B '' C) ×ˢ kerSetH S B) := by
  set b := fromLocH S B (toLocH S B a) with hb
  refine ⟨(b, b⁻¹ * a), ⟨⟨toLocH S B a, haC, rfl⟩, ?_⟩, mul_inv_cancel_left b a⟩

  have hbv : (b : Gad K) = fromLoc S (toLoc S (a : Gad K)) := by
    rw [hb, coe_fromLocH, toLocH_eq]; rfl
  show ((b⁻¹ * a : B.H) : Gad K) ∈ kerSet S
  have hval : ((b⁻¹ * a : B.H) : Gad K) = (fromLoc S (toLoc S (a : Gad K)))⁻¹ * (a : Gad K) := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv, hbv]
  rw [hval]
  obtain ⟨p, ⟨⟨x, hx, hpx⟩, hk⟩, hp⟩ := mem_image_mul_of_mem S (Set.univ) (a := (a : Gad K)) haU (Set.mem_univ _)

  have hinf : glArch (𝓞 K) K ((fromLoc S (toLoc S (a : Gad K)))⁻¹ * (a : Gad K)) = 1 := by
    rw [map_mul, map_inv, glArch_fromLoc, toLoc_apply_fst, inv_mul_cancel]
  have hfinS : ∀ v ∈ S, cpt v ((fromLoc S (toLoc S (a : Gad K)))⁻¹ * (a : Gad K)) = 1 := by
    intro v hv
    rw [cpt_mul, cpt_inv, cpt_fromLoc_of_mem S _ hv, toLoc_apply_snd, inv_mul_cancel]
  have hfin : ∀ v, v ∉ S → cpt v ((fromLoc S (toLoc S (a : Gad K)))⁻¹ * (a : Gad K)) = cpt v (a : Gad K) := by
    intro v hv
    rw [cpt_mul, cpt_inv, cpt_fromLoc_of_not_mem S _ hv, inv_one, one_mul]
  refine ⟨hinf, hfinS, fun v => ?_⟩
  by_cases hv : v ∈ S
  · rw [hfinS v hv]; exact one_mem_localIntegralSet K v
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
  exact (isOpen_unitsAwayH S B).measure_ne_zero τ ⟨1, show ((1 : B.H) : Gad K) ∈ unitsAway S from one_mem _⟩ h1

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

theorem integral_eq_kappaH_mul (W : Gad K → ℂ) (Wa : Garch K → ℂ)
    (WS : ∀ v : HeightOneSpectrum (𝓞 K), Gv (K := K) v → ℂ)
    (hWa : AEStronglyMeasurable (fun t : B.Ha => Wa t) τa)
    (hWS : ∀ v ∈ S, AEStronglyMeasurable (fun t : B.Hv v => WS v t) (τf v))
    (hWe : ∀ t : B.H, (∀ v ∉ S, cpt v (t : Gad K) ∈ localIntegralSet K v) →
      W t = Wa (glArch (𝓞 K) K (t : Gad K)) * ∏ v ∈ S, WS v (cpt v (t : Gad K)))
    (hW0 : ∀ t : B.H, (∃ v ∉ S, cpt v (t : Gad K) ∉ localIntegralSet K v) → W t = 0) :
    ∫ t, W t ∂τ = kappaH S B τ τa τf * (∫ t, Wa t ∂τa) * ∏ v ∈ S, ∫ t, WS v t ∂(τf v) := by
  set F : HP S B → ℂ := fun x => Wa (x.1 : Garch K) * ∏ v : S, WS v.1 ((x.2 v : Gv (K := K) v.1)) with hF
  have hoff : ∀ t, t ∉ unitsAwayH S B → W t = 0 := by
    intro t ht
    apply hW0
    by_contra hcon
    push Not at hcon
    exact ht fun v hv => hcon v hv
  have hon : Set.EqOn (fun t : B.H => W t) (F ∘ toLocH S B) (unitsAwayH S B) := by
    intro t ht
    simp only [Function.comp_apply, hF, coe_toLocH_fst, coe_toLocH_snd]
    rw [hWe t ht, ← Finset.prod_coe_sort S (fun v => WS v (cpt v (t : Gad K)))]
  have hFm : AEStronglyMeasurable F (refMeasureH S B τa τf) := by
    have h1 : AEStronglyMeasurable (fun x : HP S B => Wa (x.1 : Garch K)) (refMeasureH S B τa τf) :=
      MeasureTheory.AEStronglyMeasurable.comp_fst hWa
    have h2' : AEStronglyMeasurable (fun t : HS S B => ∏ v : S, WS v.1 ((t v : Gv (K := K) v.1)))
        (Measure.pi fun v : S => τf v.1) := by
      refine Finset.aestronglyMeasurable_fun_prod Finset.univ fun v _ => ?_
      exact (hWS v.1 v.2).comp_quasiMeasurePreserving
        (Measure.quasiMeasurePreserving_eval (fun w : S => τf w.1) v)
    have h2 : AEStronglyMeasurable (fun x : HP S B => ∏ v : S, WS v.1 ((x.2 v : Gv (K := K) v.1)))
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
            (fun t : HS S B => ∏ v : S, WS v.1 ((t v : Gv (K := K) v.1))),
          integral_fintype_prod_eq_prod (ι := S) (E := fun v : S => B.Hv v.1)
            (fun (v : S) (t : B.Hv v.1) => WS v.1 (t : Gv (K := K) v.1)),
          Finset.prod_coe_sort S (fun v => ∫ t, WS v t ∂(τf v))]
    _ = kappaH S B τ τa τf * (∫ t, Wa t ∂τa) * ∏ v ∈ S, ∫ t, WS v t ∂(τf v) := by ring

end BoxPush

section BoxUniform

variable (τ : Measure B.H) [IsHaarMeasure τ] (τa : Measure B.Ha) [IsHaarMeasure τa]
  (τf : ∀ v : HeightOneSpectrum (𝓞 K), Measure (B.Hv v)) [∀ v, IsHaarMeasure (τf v)]
  (hτf1 : ∀ v, τf v (Subtype.val ⁻¹' localIntegralSet K v) = 1)

def archCompactH : PositiveCompacts B.Ha := Classical.arbitrary _

def testSetH : Set B.H :=
  {t : B.H | (⟨glArch (𝓞 K) K (t : Gad K), ((B.mem_iff t).1 t.2).1⟩ : B.Ha) ∈
      (archCompactH B : Set B.Ha) ∧ ∀ v, cpt v (t : Gad K) ∈ localIntegralSet K v}

theorem mem_testSetH_iff (t : B.H) : t ∈ testSetH B ↔
    (⟨glArch (𝓞 K) K (t : Gad K), ((B.mem_iff t).1 t.2).1⟩ : B.Ha) ∈ (archCompactH B : Set B.Ha) ∧
      ∀ v, cpt v (t : Gad K) ∈ localIntegralSet K v :=
  Iff.rfl

open scoped Classical in

def testFnH : Gad K → ℂ := fun g =>
  if hg : g ∈ B.H then (testSetH B).indicator (fun _ => (1 : ℂ)) ⟨g, hg⟩ else 0

theorem testFnH_coe (t : B.H) : testFnH B (t : Gad K) = (testSetH B).indicator (fun _ => (1 : ℂ)) t := by
  unfold testFnH
  rw [dif_pos t.2]

open scoped Classical in

def testFa : Garch K → ℂ := fun x =>
  if hx : x ∈ B.Ha then ((archCompactH B : Set B.Ha).indicator (fun _ => (1 : ℂ))) ⟨x, hx⟩ else 0

theorem testFa_coe (x : B.Ha) : testFa B (x : Garch K) = ((archCompactH B : Set B.Ha).indicator (fun _ => (1 : ℂ))) x := by
  unfold testFa
  rw [dif_pos x.2]

theorem testFnH_eq (t : B.H) (ht : ∀ v ∉ S, cpt v (t : Gad K) ∈ localIntegralSet K v) :
    testFnH B t = testFa B (glArch (𝓞 K) K (t : Gad K)) *
      ∏ v ∈ S, ((localIntegralSet K v).indicator (fun _ => (1 : ℂ))) (cpt v (t : Gad K)) := by
  classical
  rw [testFnH_coe]
  have hfa : testFa B (glArch (𝓞 K) K (t : Gad K)) =
      ((archCompactH B : Set B.Ha).indicator (fun _ => (1 : ℂ)))
        (⟨glArch (𝓞 K) K (t : Gad K), ((B.mem_iff t).1 t.2).1⟩ : B.Ha) :=
    testFa_coe B ⟨glArch (𝓞 K) K (t : Gad K), ((B.mem_iff t).1 t.2).1⟩
  rw [hfa]
  by_cases harch : (⟨glArch (𝓞 K) K (t : Gad K), ((B.mem_iff t).1 t.2).1⟩ : B.Ha) ∈ (archCompactH B : Set B.Ha)
  · rw [Set.indicator_of_mem harch]
    by_cases hall : ∀ v, cpt v (t : Gad K) ∈ localIntegralSet K v
    · rw [Set.indicator_of_mem ((mem_testSetH_iff B t).2 ⟨harch, hall⟩), one_mul]
      exact (Finset.prod_eq_one fun v _ => Set.indicator_of_mem (hall v) _).symm
    · rw [Set.indicator_of_notMem (fun h => hall ((mem_testSetH_iff B t).1 h).2), one_mul]
      obtain ⟨v, hv⟩ : ∃ v, cpt v (t : Gad K) ∉ localIntegralSet K v := by
        by_contra hcon; push Not at hcon; exact hall hcon
      have hvS : v ∈ S := by by_contra hvS; exact hv (ht v hvS)
      exact (Finset.prod_eq_zero hvS (Set.indicator_of_notMem hv _)).symm
  · rw [Set.indicator_of_notMem harch, zero_mul,
      Set.indicator_of_notMem (fun h => harch ((mem_testSetH_iff B t).1 h).1)]

theorem testFnH_eq_zero (t : B.H) (ht : ∃ v ∉ S, cpt v (t : Gad K) ∉ localIntegralSet K v) : testFnH B t = 0 := by
  obtain ⟨v, -, hv⟩ := ht
  rw [testFnH_coe]
  exact Set.indicator_of_notMem (fun h => hv (((mem_testSetH_iff B t).1 h).2 v)) _

include hτf1 in
theorem integral_testFnH_eq :
    ∫ t, testFnH B t ∂τ = kappaH S B τ τa τf * (τa.real (archCompactH B : Set B.Ha)) := by
  have hmeasA : MeasurableSet (archCompactH B : Set B.Ha) := (archCompactH B).isCompact.isClosed.measurableSet
  have hmeasv : ∀ v, MeasurableSet (Subtype.val ⁻¹' localIntegralSet K v : Set (B.Hv v)) := fun v =>
    ((isCompact_localIntegralSet K v).isClosed.preimage continuous_subtype_val).measurableSet
  have hfa : AEStronglyMeasurable (fun x : B.Ha => testFa B x) τa := by
    have : (fun x : B.Ha => testFa B x) = (archCompactH B : Set B.Ha).indicator (fun _ => (1 : ℂ)) :=
      funext fun x => testFa_coe B x
    rw [this]
    exact aestronglyMeasurable_const.indicator hmeasA
  have hfS : ∀ v ∈ S, AEStronglyMeasurable
      (fun t : B.Hv v => (localIntegralSet K v).indicator (fun _ => (1 : ℂ)) (t : Gv (K := K) v)) (τf v) := by
    intro v _
    have : (fun t : B.Hv v => (localIntegralSet K v).indicator (fun _ => (1 : ℂ)) (t : Gv (K := K) v)) =
        (Subtype.val ⁻¹' localIntegralSet K v : Set (B.Hv v)).indicator (fun _ => (1 : ℂ)) := by
      funext t
      by_cases h : (t : Gv (K := K) v) ∈ localIntegralSet K v
      · have h' : t ∈ (Subtype.val ⁻¹' localIntegralSet K v : Set (B.Hv v)) := h
        rw [Set.indicator_of_mem h, Set.indicator_of_mem h']
      · have h' : t ∉ (Subtype.val ⁻¹' localIntegralSet K v : Set (B.Hv v)) := h
        rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h']
    rw [this]
    exact aestronglyMeasurable_const.indicator (hmeasv v)
  have h := integral_eq_kappaH_mul S B τ τa τf (testFnH B) (testFa B)
    (fun v => (localIntegralSet K v).indicator fun _ => (1 : ℂ)) hfa hfS (testFnH_eq S B) (testFnH_eq_zero S B)
  rw [h]
  have ha : ∫ x : B.Ha, testFa B x ∂τa = τa.real (archCompactH B : Set B.Ha) := by
    have : (fun x : B.Ha => testFa B x) = (archCompactH B : Set B.Ha).indicator (fun _ => (1 : ℂ)) :=
      funext fun x => testFa_coe B x
    rw [this, integral_indicator_const _ hmeasA]
    simp [Complex.real_smul]
  have h1 : ∀ v ∈ S, ∫ t : B.Hv v, (localIntegralSet K v).indicator (fun _ => (1 : ℂ)) (t : Gv (K := K) v) ∂(τf v) = 1 := by
    intro v _
    have : (fun t : B.Hv v => (localIntegralSet K v).indicator (fun _ => (1 : ℂ)) (t : Gv (K := K) v)) =
        (Subtype.val ⁻¹' localIntegralSet K v : Set (B.Hv v)).indicator (fun _ => (1 : ℂ)) := by
      funext t
      by_cases h : (t : Gv (K := K) v) ∈ localIntegralSet K v
      · have h' : t ∈ (Subtype.val ⁻¹' localIntegralSet K v : Set (B.Hv v)) := h
        rw [Set.indicator_of_mem h, Set.indicator_of_mem h']
      · have h' : t ∉ (Subtype.val ⁻¹' localIntegralSet K v : Set (B.Hv v)) := h
        rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h']
    rw [this, integral_indicator_const _ (hmeasv v), Measure.real, hτf1 v]
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
      ∀ (S : Finset (HeightOneSpectrum (𝓞 K))) (W : Gad K → ℂ) (Wa : Garch K → ℂ)
        (WS : ∀ v : HeightOneSpectrum (𝓞 K), Gv (K := K) v → ℂ),
        AEStronglyMeasurable (fun t : B.Ha => Wa t) τa →
        (∀ v ∈ S, AEStronglyMeasurable (fun t : B.Hv v => WS v t) (τf v)) →
        (∀ t : B.H, (∀ v ∉ S, cpt v (t : Gad K) ∈ localIntegralSet K v) →
            W t = Wa (glArch (𝓞 K) K (t : Gad K)) * ∏ v ∈ S, WS v (cpt v (t : Gad K))) →
        (∀ t : B.H, (∃ v ∉ S, cpt v (t : Gad K) ∉ localIntegralSet K v) → W t = 0) →
          ∫ t, W t ∂τ = c * (∫ t, Wa t ∂τa) * ∏ v ∈ S, ∫ t, WS v t ∂(τf v) := by
  refine ⟨(kappaH ∅ B τ τa τf : ℝ), NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (kappaH_ne_zero ∅ B τ τa τf)),
    fun S W Wa WS hWa hWS hWe hW0 => ?_⟩
  rw [← kappaH_eq_kappaH_empty S B τ τa τf hτf1]
  exact integral_eq_kappaH_mul S B τ τa τf W Wa WS hWa hWS hWe hW0

end BoxUniform

section Centralizer

def centralizerBox (γ : Gad K) : BoxData K where
  H := Subgroup.centralizer ({γ} : Set (Gad K))
  Ha := Subgroup.centralizer ({glArch (𝓞 K) K γ} : Set (Garch K))
  Hv v := Subgroup.centralizer ({cpt v γ} : Set (Gv (K := K) v))
  isClosed_H := Set.isClosed_centralizer _
  isClosed_Ha := Set.isClosed_centralizer _
  isClosed_Hv v := Set.isClosed_centralizer _
  mem_iff g := by
    simp only [Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      refine ⟨?_, fun v => ?_⟩
      · rw [← map_mul, ← map_mul, h]
      · rw [← cpt_mul, ← cpt_mul, h]
    · rintro ⟨h1, h2⟩
      refine gad_ext ?_ fun w => ?_
      · rw [map_mul, map_mul]; exact h1
      · rw [cpt_mul, cpt_mul]; exact h2 w

end Centralizer

end AutomorphicForm.AdelicCentralizerHaarFactor
p2m_reactivate "P2MW.S_AutomorphicForm_exists_integral_centralizer_eq_mul_integral_mul_prod_integral_of_isHaarMeasure.AutomorphicForm P2MW.S_AutomorphicForm_exists_integral_centralizer_eq_mul_integral_mul_prod_integral_of_isHaarMeasure.AutomorphicForm.AdelicCentralizerHaarFactor"
p2m_reactivate "P2MW.S_AutomorphicForm_exists_integral_centralizer_eq_mul_integral_mul_prod_integral_of_isHaarMeasure.AutomorphicForm"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_integral_centralizer_eq_mul_integral_mul_prod_integral_of_isHaarMeasure.AutomorphicForm P2MW.S_AutomorphicForm_exists_integral_centralizer_eq_mul_integral_mul_prod_integral_of_isHaarMeasure.AutomorphicForm.AdelicCentralizerHaarFactor"

section Solution

open MeasureTheory NumberField NumberField.AdelicHaar IsDedekindDomain
open AutomorphicForm.AdelicCentralizerHaarFactor

theorem solution
    (K : Type) [Field K] [NumberField K] (γ : GL (Fin 2) (AdeleRing (𝓞 K) K))
    (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))))
      (AutomorphicForm.centralizerBorel (AdeleRing (𝓞 K) K) γ))
    (hτ : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.centralizerBorel (AdeleRing (𝓞 K) K) γ) τ)
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
    (hτf1 : ∀ v : HeightOneSpectrum (𝓞 K),
      τf v (Subtype.val ⁻¹' AutomorphicForm.localIntegralSet K v) = 1) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (S : Finset (HeightOneSpectrum (𝓞 K)))
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
          ∫ t, W t ∂τ = c * (∫ t, Wa t ∂τa) * ∏ v ∈ S, ∫ t, WS v t ∂(τf v) := by
  let B : BoxData K := centralizerBox γ
  haveI : Measure.IsHaarMeasure (show Measure B.H from τ) := hτ
  haveI : Measure.IsHaarMeasure (show Measure B.Ha from τa) := hτa
  haveI : ∀ v, Measure.IsHaarMeasure (show Measure (B.Hv v) from τf v) := hτf
  exact exists_integral_box_eq B τ τa τf hτf1

end Solution
p2m_reactivate "P2MW.S_AutomorphicForm_exists_integral_centralizer_eq_mul_integral_mul_prod_integral_of_isHaarMeasure.AutomorphicForm P2MW.S_AutomorphicForm_exists_integral_centralizer_eq_mul_integral_mul_prod_integral_of_isHaarMeasure.AutomorphicForm.AdelicCentralizerHaarFactor"

end S_AutomorphicForm_exists_integral_centralizer_eq_mul_integral_mul_prod_integral_of_isHaarMeasure
end P2MW
export P2MW.S_AutomorphicForm_exists_integral_centralizer_eq_mul_integral_mul_prod_integral_of_isHaarMeasure (solution)
