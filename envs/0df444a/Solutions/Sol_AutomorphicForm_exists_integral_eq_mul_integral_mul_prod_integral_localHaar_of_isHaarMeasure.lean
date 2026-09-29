-- Prove2me | solution 1 for AutomorphicForm.exists_integral_eq_mul_integral_mul_prod_integral_localHaar_of_isHaarMeasure
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/c7c39750-0c86-5d52-b74e-b055cb3dc2ad

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_AdelicHaar
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Integral.Pi
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_AutomorphicForm_exists_integral_eq_mul_integral_mul_prod_integral_localHaar_of_isHaarMeasure

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory MeasureTheory.Measure Topology TopologicalSpace Set Filter
open NumberField.AdelicLevel

open scoped NNReal ENNReal

noncomputable section

namespace AutomorphicForm
p2m_export "AutomorphicForm" "glBorelOf integralUnitsSet localIntegralSet one_mem_localIntegralSet isCompact_localIntegralSet localGLBorel locallyCompactSpace_localGL localHaar isHaarMeasure_localHaar localHaar_localIntegralSet unitFinSet one_mem_unitFinSet isOpen_unitFinSet"
namespace AdelicGL2HaarFactor
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

section PushForward

variable (μ : Measure (Gad K)) [IsHaarMeasure μ]

def locMeasure : Measure (LocProd (K := K) S) :=
  Measure.map (toLoc S) (μ.restrict (unitsAway S : Set (Gad K)))

theorem map_mul_left_restrict_unitsAway {g : Gad K} (hg : g ∈ unitsAway S) :
    Measure.map (fun a => g * a) (μ.restrict (unitsAway S : Set (Gad K))) =
      μ.restrict (unitsAway S : Set (Gad K)) := by
  have hemb : MeasurableEmbedding (fun a : Gad K => g * a) :=
    (MeasurableEquiv.mulLeft g).measurableEmbedding
  have hpre : (fun a => g * a) ⁻¹' (unitsAway S : Set (Gad K)) = unitsAway S := by
    ext a
    simp only [Set.mem_preimage, SetLike.mem_coe]
    exact Subgroup.mul_mem_cancel_left _ hg
  calc Measure.map (fun a => g * a) (μ.restrict (unitsAway S : Set (Gad K)))
      = Measure.map (fun a => g * a) (μ.restrict ((fun a => g * a) ⁻¹' (unitsAway S : Set (Gad K)))) := by
        rw [hpre]
    _ = (Measure.map (fun a => g * a) μ).restrict (unitsAway S : Set (Gad K)) :=
        (hemb.restrict_map _ _).symm
    _ = μ.restrict (unitsAway S : Set (Gad K)) := by rw [map_mul_left_eq_self]

scoped instance isMulLeftInvariant_locMeasure : (locMeasure S μ).IsMulLeftInvariant := by
  refine ⟨fun x => ?_⟩
  have hmeas : Measurable (toLoc (K := K) S) := (continuous_toLoc S).measurable
  have hmx : Measurable (fun y : LocProd (K := K) S => x * y) := measurable_const_mul x
  rw [locMeasure, Measure.map_map hmx hmeas]
  have hcomp : (fun y => x * y) ∘ toLoc S = toLoc S ∘ (fun a => fromLoc S x * a) := by
    funext a
    simp only [Function.comp_apply, map_mul, toLoc_fromLoc]
  rw [hcomp, ← Measure.map_map hmeas (measurable_const_mul _),
    map_mul_left_restrict_unitsAway S μ (fromLoc_mem_unitsAway S x)]

scoped instance isFiniteMeasureOnCompacts_locMeasure : IsFiniteMeasureOnCompacts (locMeasure S μ) := by
  refine ⟨fun C hC => ?_⟩
  rw [locMeasure, Measure.map_apply (continuous_toLoc S).measurable hC.measurableSet,
    Measure.restrict_apply ((continuous_toLoc S).measurable hC.measurableSet)]
  have hK : IsCompact ((fun p : Gad K × Gad K => p.1 * p.2) '' ((fromLoc S '' C) ×ˢ kerSet S)) :=
    ((hC.image (continuous_fromLoc S)).prod (isCompact_kerSet S)).image continuous_mul
  exact (measure_mono (preimage_inter_subset S C)).trans_lt hK.measure_lt_top

omit [IsHaarMeasure μ] in
theorem locMeasure_univ : locMeasure S μ Set.univ = μ (unitsAway S : Set (Gad K)) := by
  rw [locMeasure, Measure.map_apply (continuous_toLoc S).measurable MeasurableSet.univ, Set.preimage_univ,
    Measure.restrict_apply_univ]

theorem locMeasure_ne_zero : locMeasure S μ ≠ 0 := by
  intro h
  have h1 := congrArg (fun m : Measure (LocProd (K := K) S) => m Set.univ) h
  simp only [locMeasure_univ, Measure.coe_zero, Pi.zero_apply] at h1
  exact (isOpen_unitsAway S).measure_ne_zero μ ⟨1, one_mem _⟩ h1

variable (ν : Measure (Garch K)) [IsHaarMeasure ν]

def refMeasure : Measure (LocProd (K := K) S) :=
  ν.prod (Measure.pi fun v : S => localHaar K v.1)

scoped instance isHaarMeasure_refMeasure : (refMeasure S ν).IsHaarMeasure := by
  unfold refMeasure; infer_instance

def kappa : ℝ≥0 := haarScalarFactor (locMeasure S μ) (refMeasure S ν)

theorem locMeasure_eq_smul : locMeasure S μ = kappa S μ ν • refMeasure S ν :=
  isMulLeftInvariant_eq_smul _ _

theorem kappa_ne_zero : kappa S μ ν ≠ 0 := by
  intro hc
  have h := locMeasure_eq_smul S μ ν
  rw [hc, zero_smul] at h
  exact locMeasure_ne_zero S μ h

theorem integral_eq_kappa_mul (f : Gad K → ℂ) (fa : Garch K → ℂ)
    (fS : ∀ v : HeightOneSpectrum (𝓞 K), Gv (K := K) v → ℂ)
    (hfa : AEStronglyMeasurable fa ν)
    (hfS : ∀ v ∈ S, AEStronglyMeasurable (fS v) (localHaar K v))
    (hfe : ∀ g : Gad K, (∀ v ∉ S, cpt v g ∈ localIntegralSet K v) →
      f g = fa (glArch (𝓞 K) K g) * ∏ v ∈ S, fS v (cpt v g))
    (hf0 : ∀ g : Gad K, (∃ v ∉ S, cpt v g ∉ localIntegralSet K v) → f g = 0) :
    ∫ g, f g ∂μ = kappa S μ ν * (∫ x, fa x ∂ν) * ∏ v ∈ S, ∫ y, fS v y ∂(localHaar K v) := by

  set F : LocProd (K := K) S → ℂ := fun x => fa x.1 * ∏ v : S, fS v.1 (x.2 v) with hF

  have hoff : ∀ g, g ∉ (unitsAway S : Set (Gad K)) → f g = 0 := by
    intro g hg
    apply hf0
    by_contra hcon
    push Not at hcon
    exact hg fun v hv => hcon v hv
  have hon : Set.EqOn f (F ∘ toLoc S) (unitsAway S : Set (Gad K)) := by
    intro g hg
    simp only [Function.comp_apply, hF, toLoc_apply_fst, toLoc_apply_snd]
    rw [hfe g hg, ← Finset.prod_coe_sort S (fun v => fS v (cpt v g))]

  have hFm : AEStronglyMeasurable F (refMeasure S ν) := by
    have h1 : AEStronglyMeasurable (fun x : LocProd (K := K) S => fa x.1) (refMeasure S ν) :=
      MeasureTheory.AEStronglyMeasurable.comp_fst hfa
    have h2' : AEStronglyMeasurable (fun t : SProd (K := K) S => ∏ v : S, fS v.1 (t v))
        (Measure.pi fun v : S => localHaar K v.1) := by
      refine Finset.aestronglyMeasurable_fun_prod Finset.univ fun v _ => ?_
      exact (hfS v.1 v.2).comp_quasiMeasurePreserving
        (Measure.quasiMeasurePreserving_eval (fun w : S => localHaar K w.1) v)
    have h2 : AEStronglyMeasurable (fun x : LocProd (K := K) S => ∏ v : S, fS v.1 (x.2 v)) (refMeasure S ν) :=
      MeasureTheory.AEStronglyMeasurable.comp_snd h2'
    exact h1.mul h2
  have hFm' : AEStronglyMeasurable F (locMeasure S μ) := by
    rw [locMeasure_eq_smul S μ ν]
    exact hFm.smul_measure _
  calc ∫ g, f g ∂μ
      = ∫ g in (unitsAway S : Set (Gad K)), f g ∂μ := (setIntegral_eq_integral_of_forall_compl_eq_zero hoff).symm
    _ = ∫ g in (unitsAway S : Set (Gad K)), (F ∘ toLoc S) g ∂μ := setIntegral_congr_fun (measurableSet_unitsAway S) hon
    _ = ∫ x, F x ∂(locMeasure S μ) := by
        rw [locMeasure, integral_map (continuous_toLoc S).measurable.aemeasurable]
        · rfl
        · rw [← locMeasure]; exact hFm'
    _ = kappa S μ ν * ∫ x, F x ∂(refMeasure S ν) := by
        rw [locMeasure_eq_smul S μ ν, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]
    _ = kappa S μ ν * ((∫ x, fa x ∂ν) * ∏ v ∈ S, ∫ y, fS v y ∂(localHaar K v)) := by
        congr 1
        rw [refMeasure, hF, integral_prod_mul (μ := ν) fa (fun t : SProd (K := K) S => ∏ v : S, fS v.1 (t v)),
          integral_fintype_prod_eq_prod (ι := S) (E := fun v : S => Gv (K := K) v.1)
            (fun (v : S) (y : Gv (K := K) v.1) => fS v.1 y),
          Finset.prod_coe_sort S (fun v => ∫ y, fS v y ∂(localHaar K v))]
    _ = kappa S μ ν * (∫ x, fa x ∂ν) * ∏ v ∈ S, ∫ y, fS v y ∂(localHaar K v) := by ring

end PushForward

section Uniform

variable (μ : Measure (Gad K)) [IsHaarMeasure μ] (ν : Measure (Garch K)) [IsHaarMeasure ν]

def archCompact : PositiveCompacts (Garch K) := Classical.arbitrary _

def testSet : Set (Gad K) :=
  {g : Gad K | glArch (𝓞 K) K g ∈ (archCompact (K := K) : Set (Garch K)) ∧
    ∀ v, cpt v g ∈ localIntegralSet K v}

theorem mem_testSet_iff (g : Gad K) : g ∈ testSet (K := K) ↔
    glArch (𝓞 K) K g ∈ (archCompact (K := K) : Set (Garch K)) ∧ ∀ v, cpt v g ∈ localIntegralSet K v :=
  Iff.rfl

def testFn : Gad K → ℂ := (testSet (K := K)).indicator fun _ => 1

theorem testFn_eq (g : Gad K) (hg : ∀ v ∉ S, cpt v g ∈ localIntegralSet K v) :
    testFn g = ((archCompact (K := K) : Set (Garch K)).indicator (fun _ => (1 : ℂ))) (glArch (𝓞 K) K g) *
      ∏ v ∈ S, ((localIntegralSet K v).indicator (fun _ => (1 : ℂ))) (cpt v g) := by
  classical
  unfold testFn
  by_cases harch : glArch (𝓞 K) K g ∈ (archCompact (K := K) : Set (Garch K))
  · rw [Set.indicator_of_mem harch]
    by_cases hall : ∀ v, cpt v g ∈ localIntegralSet K v
    · rw [Set.indicator_of_mem ((mem_testSet_iff g).2 ⟨harch, hall⟩), one_mul]
      exact (Finset.prod_eq_one fun v _ => Set.indicator_of_mem (hall v) _).symm
    · rw [Set.indicator_of_notMem (fun h => hall ((mem_testSet_iff g).1 h).2), one_mul]
      obtain ⟨v, hv⟩ : ∃ v, cpt v g ∉ localIntegralSet K v := by
        by_contra hcon; push Not at hcon; exact hall hcon
      have hvS : v ∈ S := by by_contra hvS; exact hv (hg v hvS)
      exact (Finset.prod_eq_zero hvS (Set.indicator_of_notMem hv _)).symm
  · rw [Set.indicator_of_notMem harch, zero_mul,
      Set.indicator_of_notMem (fun h => harch ((mem_testSet_iff g).1 h).1)]

theorem testFn_eq_zero (g : Gad K) (hg : ∃ v ∉ S, cpt v g ∉ localIntegralSet K v) : testFn g = 0 := by
  obtain ⟨v, -, hv⟩ := hg
  exact Set.indicator_of_notMem (fun h => hv (((mem_testSet_iff g).1 h).2 v)) _

theorem integral_testFn_eq :
    ∫ g, testFn g ∂μ = kappa S μ ν * (ν.real (archCompact (K := K) : Set (Garch K))) := by
  have hmeasA : MeasurableSet (archCompact (K := K) : Set (Garch K)) :=
    (archCompact (K := K)).isCompact.isClosed.measurableSet
  have h := integral_eq_kappa_mul S μ ν testFn ((archCompact (K := K) : Set (Garch K)).indicator fun _ => (1 : ℂ))
    (fun v => (localIntegralSet K v).indicator fun _ => (1 : ℂ))
    ((aestronglyMeasurable_const.indicator hmeasA))
    (fun v _ => aestronglyMeasurable_const.indicator (isCompact_localIntegralSet K v).isClosed.measurableSet)
    (testFn_eq S) (testFn_eq_zero S)
  rw [h, integral_indicator_const _ hmeasA]
  have h1 : ∀ v ∈ S, ∫ y, (localIntegralSet K v).indicator (fun _ => (1 : ℂ)) y ∂(localHaar K v) = 1 := by
    intro v _
    rw [integral_indicator_const _ (isCompact_localIntegralSet K v).isClosed.measurableSet,
      Measure.real, localHaar_localIntegralSet]
    simp
  rw [Finset.prod_eq_one h1]
  simp [Complex.real_smul, Measure.real]

theorem real_archCompact_ne_zero : ν.real (archCompact (K := K) : Set (Garch K)) ≠ 0 := by
  rw [Measure.real, ENNReal.toReal_ne_zero]
  exact ⟨(measure_pos_of_nonempty_interior ν (archCompact (K := K)).interior_nonempty).ne',
    (archCompact (K := K)).isCompact.measure_lt_top.ne⟩

theorem kappa_eq_kappa_empty : kappa S μ ν = kappa ∅ μ ν := by
  have h1 := integral_testFn_eq S μ ν
  have h2 := integral_testFn_eq ∅ μ ν
  rw [h1] at h2
  have hpos := real_archCompact_ne_zero (K := K) ν
  have h3 : ((kappa S μ ν : ℝ) : ℂ) = ((kappa ∅ μ ν : ℝ) : ℂ) := by
    have := mul_right_cancel₀ (Complex.ofReal_ne_zero.mpr hpos) h2
    exact this
  exact_mod_cast h3

end Uniform

end AutomorphicForm.AdelicGL2HaarFactor
p2m_reactivate "P2MW.S_AutomorphicForm_exists_integral_eq_mul_integral_mul_prod_integral_localHaar_of_isHaarMeasure.AutomorphicForm P2MW.S_AutomorphicForm_exists_integral_eq_mul_integral_mul_prod_integral_localHaar_of_isHaarMeasure.AutomorphicForm.AdelicGL2HaarFactor"
p2m_reactivate "P2MW.S_AutomorphicForm_exists_integral_eq_mul_integral_mul_prod_integral_localHaar_of_isHaarMeasure.AutomorphicForm"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_integral_eq_mul_integral_mul_prod_integral_localHaar_of_isHaarMeasure.AutomorphicForm P2MW.S_AutomorphicForm_exists_integral_eq_mul_integral_mul_prod_integral_localHaar_of_isHaarMeasure.AutomorphicForm.AdelicGL2HaarFactor"

section Solution

open MeasureTheory NumberField NumberField.AdelicHaar IsDedekindDomain
open AutomorphicForm.AdelicGL2HaarFactor

theorem solution
    (K : Type) [Field K] [NumberField K]
    (μ : @Measure (GL (Fin 2) (AdeleRing (𝓞 K) K)) (glBorel (Fin 2) (𝓞 K) K))
    (hμ : @Measure.IsHaarMeasure (GL (Fin 2) (AdeleRing (𝓞 K) K)) _ _ (glBorel (Fin 2) (𝓞 K) K) μ)
    (ν : @Measure (GL (Fin 2) (InfiniteAdeleRing K)) (AutomorphicForm.glBorelOf (InfiniteAdeleRing K)))
    (hν : @Measure.IsHaarMeasure (GL (Fin 2) (InfiniteAdeleRing K)) _ _
      (AutomorphicForm.glBorelOf (InfiniteAdeleRing K)) ν) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (S : Finset (HeightOneSpectrum (𝓞 K)))
        (f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) (fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)
        (fS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ),
        AEStronglyMeasurable[AutomorphicForm.glBorelOf (InfiniteAdeleRing K)] fa ν →
        (∀ v ∈ S, AEStronglyMeasurable[AutomorphicForm.localGLBorel K v] (fS v)
          (AutomorphicForm.localHaar K v)) →
        (∀ g : GL (Fin 2) (AdeleRing (𝓞 K) K),
          (∀ v ∉ S, AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K g) ∈
              AutomorphicForm.localIntegralSet K v) →
            f g = fa (AdelicLevel.glArch (𝓞 K) K g) *
              ∏ v ∈ S, fS v (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K g))) →
        (∀ g : GL (Fin 2) (AdeleRing (𝓞 K) K),
          (∃ v ∉ S, AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K g) ∉
              AutomorphicForm.localIntegralSet K v) → f g = 0) →
          ∫ g, f g ∂μ = c * (∫ x, fa x ∂ν) * ∏ v ∈ S, ∫ y, fS v y ∂(AutomorphicForm.localHaar K v) := by
  haveI : Measure.IsHaarMeasure μ := hμ
  haveI : Measure.IsHaarMeasure ν := hν
  refine ⟨(kappa ∅ μ ν : ℝ), NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (kappa_ne_zero ∅ μ ν)),
    fun S f fa fS hfa hfS hfe hf0 => ?_⟩
  rw [← kappa_eq_kappa_empty S μ ν]
  exact integral_eq_kappa_mul S μ ν f fa fS hfa hfS hfe hf0

end Solution
p2m_reactivate "P2MW.S_AutomorphicForm_exists_integral_eq_mul_integral_mul_prod_integral_localHaar_of_isHaarMeasure.AutomorphicForm P2MW.S_AutomorphicForm_exists_integral_eq_mul_integral_mul_prod_integral_localHaar_of_isHaarMeasure.AutomorphicForm.AdelicGL2HaarFactor"

end S_AutomorphicForm_exists_integral_eq_mul_integral_mul_prod_integral_localHaar_of_isHaarMeasure
end P2MW
export P2MW.S_AutomorphicForm_exists_integral_eq_mul_integral_mul_prod_integral_localHaar_of_isHaarMeasure (solution)
