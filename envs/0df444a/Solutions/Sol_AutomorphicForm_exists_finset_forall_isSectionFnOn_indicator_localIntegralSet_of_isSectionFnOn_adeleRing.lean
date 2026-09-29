-- Prove2me | solution 1 for AutomorphicForm.exists_finset_forall_isSectionFnOn_indicator_localIntegralSet_of_isSectionFnOn_adeleRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/13cbf19f-3466-5ed3-982f-c912e9010a73

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_AutomorphicForm_exists_finset_forall_isSectionFnOn_indicator_localIntegralSet_of_isSectionFnOn_adeleRing

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory MeasureTheory.Measure Topology TopologicalSpace Set Filter
open NumberField.AdelicLevel

open scoped NNReal ENNReal Pointwise

noncomputable section

namespace AutomorphicForm
p2m_export "AutomorphicForm" "glBorelOf centralizerBorel IsSectionFnOn IsOrbitalIntegralOn integralUnitsSet localIntegralSet one_mem_localIntegralSet isCompact_localIntegralSet isOpen_localIntegralSet localGLBorel localCentralizer localCentralizerBorel unitFinSet one_mem_unitFinSet isOpen_unitFinSet IsRegularSemisimple"
namespace AdelicUnitSectionFn
p2m_open "AutomorphicForm"

variable {K : Type} [Field K] [NumberField K]

abbrev Garch (K : Type) [Field K] [NumberField K] : Type := GL (Fin 2) (InfiniteAdeleRing K)

abbrev Gfin (K : Type) [Field K] [NumberField K] : Type := GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)

abbrev Gad (K : Type) [Field K] [NumberField K] : Type := GL (Fin 2) (AdeleRing (𝓞 K) K)

abbrev Gv (v : HeightOneSpectrum (𝓞 K)) : Type := GL (Fin 2) (v.adicCompletion K)

abbrev SProd (S : Finset (HeightOneSpectrum (𝓞 K))) : Type := (v : S) → Gv (K := K) v.1

abbrev LocProd (S : Finset (HeightOneSpectrum (𝓞 K))) : Type := Garch K × SProd (K := K) S

section Instances

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

theorem mul_mem_localIntegralSet (v : HeightOneSpectrum (𝓞 K)) {g h : Gv (K := K) v}
    (hg : g ∈ localIntegralSet K v) (hh : h ∈ localIntegralSet K v) : g * h ∈ localIntegralSet K v :=
  mul_mem_integralUnitsSet (v.adicCompletionIntegers K).toSubring hg hh

theorem inv_mem_localIntegralSet (v : HeightOneSpectrum (𝓞 K)) {g : Gv (K := K) v}
    (hg : g ∈ localIntegralSet K v) : g⁻¹ ∈ localIntegralSet K v :=
  inv_mem_integralUnitsSet _ hg

theorem mul_mem_localIntegralSet_iff_left (v : HeightOneSpectrum (𝓞 K)) {g h : Gv (K := K) v}
    (hg : g ∈ localIntegralSet K v) : g * h ∈ localIntegralSet K v ↔ h ∈ localIntegralSet K v := by
  refine ⟨fun hgh => ?_, fun hh => mul_mem_localIntegralSet v hg hh⟩
  have := mul_mem_localIntegralSet v (inv_mem_localIntegralSet v hg) hgh
  rwa [inv_mul_cancel_left] at this

theorem mul_mem_localIntegralSet_iff_right (v : HeightOneSpectrum (𝓞 K)) {g h : Gv (K := K) v}
    (hh : h ∈ localIntegralSet K v) : g * h ∈ localIntegralSet K v ↔ g ∈ localIntegralSet K v := by
  refine ⟨fun hgh => ?_, fun hg => mul_mem_localIntegralSet v hg hh⟩
  have := mul_mem_localIntegralSet v hgh (inv_mem_localIntegralSet v hh)
  rwa [mul_inv_cancel_right] at this

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
    exact mul_mem_localIntegralSet v (hg v hv) (hh v hv)
  one_mem' v _ := by rw [cpt_one]; exact one_mem_localIntegralSet K v
  inv_mem' {g} hg v hv := by
    rw [cpt_inv]
    exact inv_mem_localIntegralSet v (hg v hv)

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

theorem isClosed_unitsAway : IsClosed (unitsAway S : Set (Gad K)) := by
  have : (unitsAway S : Set (Gad K)) = ⋂ v ∈ (↑S : Set (HeightOneSpectrum (𝓞 K)))ᶜ,
      cpt v ⁻¹' localIntegralSet K v := by
    ext g
    simp only [SetLike.mem_coe, mem_unitsAway_iff, Set.mem_iInter, Set.mem_preimage, Set.mem_compl_iff]
  rw [this]
  exact isClosed_biInter fun v _ => (isCompact_localIntegralSet K v).isClosed.preimage (continuous_cpt v)

theorem measurableSet_unitsAway : MeasurableSet (unitsAway S : Set (Gad K)) :=
  (isOpen_unitsAway S).measurableSet

theorem eventually_cpt_mem (g : Gad K) : ∀ᶠ v in cofinite, cpt v g ∈ localIntegralSet K v := by
  have h1 : ∀ i j : Fin 2, ∀ᶠ v : HeightOneSpectrum (𝓞 K) in cofinite,
      ((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j).2 v ∈ v.adicCompletionIntegers K :=
    fun i j => ((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j).2.2
  have h2 : ∀ i j : Fin 2, ∀ᶠ v : HeightOneSpectrum (𝓞 K) in cofinite,
      (((g⁻¹ : Gad K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j).2 v ∈ v.adicCompletionIntegers K :=
    fun i j => (((g⁻¹ : Gad K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j).2.2
  have h1' : ∀ᶠ v : HeightOneSpectrum (𝓞 K) in cofinite, ∀ i j : Fin 2,
      ((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j).2 v ∈ v.adicCompletionIntegers K :=
    eventually_all.2 fun i => eventually_all.2 fun j => h1 i j
  have h2' : ∀ᶠ v : HeightOneSpectrum (𝓞 K) in cofinite, ∀ i j : Fin 2,
      (((g⁻¹ : Gad K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j).2 v ∈ v.adicCompletionIntegers K :=
    eventually_all.2 fun i => eventually_all.2 fun j => h2 i j
  filter_upwards [h1', h2'] with v hv1 hv2
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [finComponent_apply, glFin_apply]
    exact hv1 i j
  · rw [← map_inv, ← map_inv, finComponent_apply, glFin_apply]
    exact hv2 i j

theorem finite_setOf_cpt_not_mem (g : Gad K) : {v | cpt v g ∉ localIntegralSet K v}.Finite :=
  Filter.eventually_cofinite.1 (eventually_cpt_mem g)

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

def toLoc : Gad K →* LocProd (K := K) S :=
  MonoidHom.prod (glArch (𝓞 K) K) (MonoidHom.pi fun v : S => (finComponent (𝓞 K) K v.1).comp (glFin (𝓞 K) K))

theorem toLoc_apply_fst (g : Gad K) : (toLoc S g).1 = glArch (𝓞 K) K g := rfl

theorem toLoc_apply_snd (g : Gad K) (v : S) : (toLoc S g).2 v = cpt v.1 g := rfl

end Embedding

theorem unitsAway_mono {S S' : Finset (HeightOneSpectrum (𝓞 K))} (h : S ⊆ S') : unitsAway (K := K) S ≤ unitsAway S' :=
  fun _ hg v hv => hg v fun h' => hv (h h')

theorem exists_finset_subset_unitsAway {C : Set (Gad K)} (hC : IsCompact C) :
    ∃ S₀ : Finset (HeightOneSpectrum (𝓞 K)), C ⊆ (unitsAway S₀ : Set (Gad K)) := by
  classical
  obtain ⟨t, ht⟩ := hC.elim_finite_subcover
    (fun S : Finset (HeightOneSpectrum (𝓞 K)) => (unitsAway S : Set (Gad K)))
    (fun S => isOpen_unitsAway S)
    (fun g _ => Set.mem_iUnion.2 ⟨(finite_setOf_cpt_not_mem g).toFinset, fun v hv => by
      by_contra h
      exact hv ((Set.Finite.mem_toFinset _).2 h)⟩)
  refine ⟨t.biUnion id, fun g hg => ?_⟩
  obtain ⟨S, hS, hgS⟩ := Set.mem_iUnion₂.1 (ht hg)
  exact unitsAway_mono (fun v hv => Finset.mem_biUnion.2 ⟨S, hS, hv⟩) hgS

section AtPlace

variable (v : HeightOneSpectrum (𝓞 K))

open scoped Classical in

def atPlace (y : Gv (K := K) v) : Gad K :=
  fromLoc ({v} : Finset (HeightOneSpectrum (𝓞 K)))
    (1, Function.update (1 : SProd (K := K) ({v} : Finset (HeightOneSpectrum (𝓞 K))))
      ⟨v, Finset.mem_singleton_self v⟩ y)

theorem glArch_atPlace (y : Gv (K := K) v) : glArch (𝓞 K) K (atPlace v y) = 1 :=
  glArch_fromLoc _ _

theorem cpt_atPlace_self (y : Gv (K := K) v) : cpt v (atPlace v y) = y := by
  classical
  rw [atPlace, cpt_fromLoc_of_mem _ _ (Finset.mem_singleton_self v)]
  exact Function.update_self _ _ _

theorem cpt_atPlace_of_ne (y : Gv (K := K) v) {w : HeightOneSpectrum (𝓞 K)} (hw : w ≠ v) :
    cpt w (atPlace v y) = 1 :=
  cpt_fromLoc_of_not_mem _ _ (fun h => hw (Finset.mem_singleton.1 h))

end AtPlace

section Regular

variable {A : Type*} [CommRing A]

theorem entries_of_commute (g X : Matrix (Fin 2) (Fin 2) A) (h : X * g = g * X) (u : A)
    (hu : u * ((g 0 0 - g 1 1) ^ 2 + 4 * g 0 1 * g 1 0) = 1) :
    X 0 1 = u * (4 * g 1 0 * X 0 1 + (g 0 0 - g 1 1) * (X 0 0 - X 1 1)) * g 0 1 ∧
    X 1 0 = u * (4 * g 1 0 * X 0 1 + (g 0 0 - g 1 1) * (X 0 0 - X 1 1)) * g 1 0 ∧
    X 0 0 - X 1 1 = u * (4 * g 1 0 * X 0 1 + (g 0 0 - g 1 1) * (X 0 0 - X 1 1)) * (g 0 0 - g 1 1) := by
  have e00 := congr_fun (congr_fun h 0) 0
  have e01 := congr_fun (congr_fun h 0) 1
  have e10 := congr_fun (congr_fun h 1) 0
  have e11 := congr_fun (congr_fun h 1) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11
  refine ⟨?_, ?_, ?_⟩
  · linear_combination (-(X 0 1)) * hu + (-(u * (g 0 0 - g 1 1))) * e01
  · linear_combination (-(X 1 0)) * hu + (u * (g 0 0 - g 1 1)) * e10 +
      (-(4 * u * g 1 0)) * e00
  · linear_combination (-(X 0 0 - X 1 1)) * hu + (4 * u * g 1 0) * e01

theorem mul_comm_of_mem_centralizer {γ : GL (Fin 2) A} (hγ : AutomorphicForm.IsRegularSemisimple γ)
    {s t : GL (Fin 2) A} (hs : s ∈ Subgroup.centralizer ({γ} : Set (GL (Fin 2) A)))
    (ht : t ∈ Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) : s * t = t * s := by
  rw [Subgroup.mem_centralizer_singleton_iff] at hs ht
  obtain ⟨u, hu⟩ := IsUnit.exists_left_inv hγ
  set g : Matrix (Fin 2) (Fin 2) A := (γ : Matrix (Fin 2) (Fin 2) A) with hg
  have hu' : u * ((g 0 0 - g 1 1) ^ 2 + 4 * g 0 1 * g 1 0) = 1 := by
    rw [Matrix.trace_fin_two, Matrix.det_fin_two] at hu
    linear_combination hu
  have hsX : (s : Matrix (Fin 2) (Fin 2) A) * g = g * s := by
    simpa [hg] using congrArg Units.val hs
  have htX : (t : Matrix (Fin 2) (Fin 2) A) * g = g * t := by
    simpa [hg] using congrArg Units.val ht
  obtain ⟨a1, a2, a3⟩ := entries_of_commute g s hsX u hu'
  obtain ⟨b1, b2, b3⟩ := entries_of_commute g t htX u hu'
  set X : Matrix (Fin 2) (Fin 2) A := (s : Matrix (Fin 2) (Fin 2) A)
  set Y : Matrix (Fin 2) (Fin 2) A := (t : Matrix (Fin 2) (Fin 2) A)
  set p := u * (4 * g 1 0 * X 0 1 + (g 0 0 - g 1 1) * (X 0 0 - X 1 1))
  set q := u * (4 * g 1 0 * Y 0 1 + (g 0 0 - g 1 1) * (Y 0 0 - Y 1 1))
  apply Units.ext
  change X * Y = Y * X
  ext i j
  fin_cases i <;> fin_cases j <;> simp only [Matrix.mul_apply, Fin.sum_univ_two, Fin.zero_eta,
    Fin.mk_one]
  · linear_combination (Y 1 0) * a1 + (p * g 0 1) * b2 - (X 1 0) * b1 - (q * g 0 1) * a2
  · linear_combination (X 0 0 - X 1 1) * b1 + (q * g 0 1) * a3 - (Y 0 0 - Y 1 1) * a1 -
      (p * g 0 1) * b3
  · linear_combination (Y 0 0 - Y 1 1) * a2 + (p * g 1 0) * b3 - (X 0 0 - X 1 1) * b2 -
      (q * g 1 0) * a3
  · linear_combination (Y 0 1) * a2 + (p * g 1 0) * b1 - (X 0 1) * b2 - (q * g 1 0) * a1

end Regular

theorem isRegularSemisimple_cpt {γ : Gad K} (hγ : IsRegularSemisimple γ) (v : HeightOneSpectrum (𝓞 K)) :
    IsRegularSemisimple (cpt v γ) := by
  let φ : AdeleRing (𝓞 K) K →+* v.adicCompletion K := (finAdeleEval (𝓞 K) K v).comp (adeleFin (𝓞 K) K)
  have hval : ((cpt v γ : Gv (K := K) v) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      φ.mapMatrix (γ : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) := by
    ext i j; rfl
  unfold IsRegularSemisimple
  rw [hval]
  have e : (φ.mapMatrix (γ : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))).trace ^ 2 -
      4 * (φ.mapMatrix (γ : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))).det =
      φ ((γ : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)).trace ^ 2 -
        4 * (γ : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)).det) := by
    rw [map_sub, map_pow, map_mul, map_ofNat, RingHom.map_det, AddMonoidHom.map_trace φ]
    rfl
  rw [e]
  exact hγ.map φ

section Main

variable (γ : Gad K)

abbrev Tad : Subgroup (Gad K) := Subgroup.centralizer ({γ} : Set (Gad K))

abbrev Tarch : Subgroup (Garch K) := Subgroup.centralizer ({glArch (𝓞 K) K γ} : Set (Garch K))

abbrev Tv (v : HeightOneSpectrum (𝓞 K)) : Subgroup (Gv (K := K) v) :=
  Subgroup.centralizer ({cpt v γ} : Set (Gv (K := K) v))

variable {γ}

theorem cpt_conj (v : HeightOneSpectrum (𝓞 K)) (x : Gad K) :
    cpt v (x⁻¹ * γ * x) = (cpt v x)⁻¹ * cpt v γ * cpt v x := by
  rw [cpt_mul, cpt_mul, cpt_inv]

theorem glArch_conj (x : Gad K) :
    glArch (𝓞 K) K (x⁻¹ * γ * x) = (glArch (𝓞 K) K x)⁻¹ * glArch (𝓞 K) K γ * glArch (𝓞 K) K x := by
  rw [map_mul, map_mul, map_inv]

theorem cpt_mem_Tv (t : Tad γ) (v : HeightOneSpectrum (𝓞 K)) : cpt v (t : Gad K) ∈ Tv γ v := by
  have ht := t.2
  rw [Subgroup.mem_centralizer_singleton_iff] at ht ⊢
  rw [← cpt_mul, ← cpt_mul, ht]

theorem glArch_mem_Tarch (t : Tad γ) : glArch (𝓞 K) K (t : Gad K) ∈ Tarch γ := by
  have ht := t.2
  rw [Subgroup.mem_centralizer_singleton_iff] at ht ⊢
  rw [← map_mul, ← map_mul, ht]

theorem integral_indicator_translate_eq_one (hγ : IsRegularSemisimple γ) (v : HeightOneSpectrum (𝓞 K))
    (τv : Measure (Tv γ v)) [τv.IsMulLeftInvariant]
    (hτv1 : τv (Subtype.val ⁻¹' localIntegralSet K v) = 1)
    (s : Tv γ v) (y : Gv (K := K) v) (hsy : (s : Gv (K := K) v) * y ∈ localIntegralSet K v) :
    ∫ t : Tv γ v, (localIntegralSet K v).indicator (fun _ => (1 : ℝ)) ((t : Gv (K := K) v) * y) ∂τv = 1 := by
  have hset : (fun t : Tv γ v => (t : Gv (K := K) v) * y) ⁻¹' localIntegralSet K v =
      (fun t : Tv γ v => s⁻¹ * t) ⁻¹' (Subtype.val ⁻¹' localIntegralSet K v) := by
    ext t
    simp only [Set.mem_preimage, Subgroup.coe_mul, Subgroup.coe_inv]
    have hcomm : (s : Gv (K := K) v)⁻¹ * (t : Gv (K := K) v) = (t : Gv (K := K) v) * (s : Gv (K := K) v)⁻¹ := by
      have h := mul_comm_of_mem_centralizer (isRegularSemisimple_cpt hγ v) s.2 t.2
      calc (s : Gv (K := K) v)⁻¹ * (t : Gv (K := K) v)
          = (s : Gv (K := K) v)⁻¹ * ((t : Gv (K := K) v) * (s : Gv (K := K) v)) * (s : Gv (K := K) v)⁻¹ := by group
        _ = (s : Gv (K := K) v)⁻¹ * ((s : Gv (K := K) v) * (t : Gv (K := K) v)) * (s : Gv (K := K) v)⁻¹ := by rw [h]
        _ = (t : Gv (K := K) v) * (s : Gv (K := K) v)⁻¹ := by group
    rw [hcomm]
    have e : (t : Gv (K := K) v) * y = (t : Gv (K := K) v) * (s : Gv (K := K) v)⁻¹ * ((s : Gv (K := K) v) * y) := by
      group
    rw [e]
    exact mul_mem_localIntegralSet_iff_right v hsy
  have hmeas : MeasurableSet ((fun t : Tv γ v => (t : Gv (K := K) v) * y) ⁻¹' localIntegralSet K v) :=
    ((isOpen_localIntegralSet K v).preimage (continuous_subtype_val.mul continuous_const)).measurableSet
  have hind : (fun t : Tv γ v => (localIntegralSet K v).indicator (fun _ => (1 : ℝ)) ((t : Gv (K := K) v) * y)) =
      ((fun t : Tv γ v => (t : Gv (K := K) v) * y) ⁻¹' localIntegralSet K v).indicator (fun _ => (1 : ℝ)) := by
    funext t
    rfl
  rw [hind, integral_indicator_const _ hmeas, smul_eq_mul, mul_one, Measure.real, hset, measure_preimage_mul,
    hτv1, ENNReal.toReal_one]

variable (γ) (S : Finset (HeightOneSpectrum (𝓞 K)))
  (f : Gad K → ℂ) (fa : Garch K → ℂ) (fS : ∀ v : HeightOneSpectrum (𝓞 K), Gv (K := K) v → ℂ)

structure Data (τ : Measure (Tad γ)) (w : Gad K → ℝ) (x₀ : Gad K) : Prop where
  hf : ∀ g : Gad K, (∀ v ∉ S, cpt v g ∈ localIntegralSet K v) →
    f g = fa (glArch (𝓞 K) K g) * ∏ v ∈ S, fS v (cpt v g)
  hf0 : ∀ g : Gad K, (∃ v ∉ S, cpt v g ∉ localIntegralSet K v) → f g = 0
  hwc : HasCompactSupport w
  hw1 : ∀ x : Gad K, f (x⁻¹ * γ * x) ≠ 0 → ∫ t : Tad γ, w ((t : Gad K) * x) ∂τ = 1
  hx₀ : f (x₀⁻¹ * γ * x₀) ≠ 0

variable {γ S f fa fS} {τ : Measure (Tad γ)} {w : Gad K → ℝ} {x₀ : Gad K}

namespace Data

variable (D : Data γ S f fa fS τ w x₀)
include D

theorem int₀ : ∀ v ∉ S, cpt v (x₀⁻¹ * γ * x₀) ∈ localIntegralSet K v := by
  by_contra h
  push Not at h
  obtain ⟨v, hv, hv'⟩ := h
  exact D.hx₀ (D.hf0 _ ⟨v, hv, hv'⟩)

theorem fx₀ : f (x₀⁻¹ * γ * x₀) = fa (glArch (𝓞 K) K (x₀⁻¹ * γ * x₀)) * ∏ v ∈ S, fS v (cpt v (x₀⁻¹ * γ * x₀)) :=
  D.hf _ D.int₀

theorem fa₀ : fa (glArch (𝓞 K) K (x₀⁻¹ * γ * x₀)) ≠ 0 := by
  intro h
  have := D.hx₀
  rw [D.fx₀, h, zero_mul] at this
  exact this rfl

theorem fS₀ : ∀ v ∈ S, fS v (cpt v (x₀⁻¹ * γ * x₀)) ≠ 0 := by
  intro v hv h
  have := D.hx₀
  rw [D.fx₀, Finset.prod_eq_zero hv h, mul_zero] at this
  exact this rfl

theorem exists_translate_mem {x : Gad K} (hx : f (x⁻¹ * γ * x) ≠ 0) :
    ∃ t : Tad γ, (t : Gad K) * x ∈ tsupport w := by
  obtain ⟨t, ht⟩ : ∃ t : Tad γ, w ((t : Gad K) * x) ≠ 0 := by
    by_contra h
    push Not at h
    have h0 : ∫ t : Tad γ, w ((t : Gad K) * x) ∂τ = 0 := by
      rw [show (fun t : Tad γ => w ((t : Gad K) * x)) = fun _ => 0 from funext h, integral_zero]
    have h1 := D.hw1 x hx
    rw [h0] at h1
    exact zero_ne_one h1
  exact ⟨t, subset_tsupport _ (Function.mem_support.2 ht)⟩

theorem cpt_mem_mul {x : Gad K} (hx : f (x⁻¹ * γ * x) ≠ 0) (v : HeightOneSpectrum (𝓞 K)) :
    cpt v x ∈ (Tv γ v : Set (Gv (K := K) v)) * (cpt v '' tsupport w) := by
  obtain ⟨t, ht⟩ := D.exists_translate_mem hx
  refine ⟨(cpt v (t : Gad K))⁻¹, (Tv γ v).inv_mem (cpt_mem_Tv t v), cpt v ((t : Gad K) * x), ⟨_, ht, rfl⟩, ?_⟩
  simp only [cpt_mul, inv_mul_cancel_left]

theorem glArch_mem_mul {x : Gad K} (hx : f (x⁻¹ * γ * x) ≠ 0) :
    glArch (𝓞 K) K x ∈ (Tarch γ : Set (Garch K)) * (glArch (𝓞 K) K '' tsupport w) := by
  obtain ⟨t, ht⟩ := D.exists_translate_mem hx
  refine ⟨(glArch (𝓞 K) K (t : Gad K))⁻¹, (Tarch γ).inv_mem (glArch_mem_Tarch t),
    glArch (𝓞 K) K ((t : Gad K) * x), ⟨_, ht, rfl⟩, ?_⟩
  simp only [map_mul, inv_mul_cancel_left]

theorem mem_E_of_not_mem {v : HeightOneSpectrum (𝓞 K)} (hv : v ∉ S)
    (y : Gv (K := K) v) (hy : y⁻¹ * cpt v γ * y ∈ localIntegralSet K v) :
    f ((x₀ * atPlace v ((cpt v x₀)⁻¹ * y))⁻¹ * γ * (x₀ * atPlace v ((cpt v x₀)⁻¹ * y))) ≠ 0 := by
  set x : Gad K := x₀ * atPlace v ((cpt v x₀)⁻¹ * y) with hx
  have hcv : cpt v x = y := by
    rw [hx, cpt_mul, cpt_atPlace_self, mul_inv_cancel_left]
  have hcw : ∀ w, w ≠ v → cpt w x = cpt w x₀ := by
    intro w hw
    rw [hx, cpt_mul, cpt_atPlace_of_ne v _ hw, mul_one]
  have harch : glArch (𝓞 K) K x = glArch (𝓞 K) K x₀ := by
    rw [hx, map_mul, glArch_atPlace, mul_one]
  have hconj_w : ∀ w, w ≠ v → cpt w (x⁻¹ * γ * x) = cpt w (x₀⁻¹ * γ * x₀) := by
    intro w hw
    rw [cpt_conj, cpt_conj, hcw w hw]
  have hconj_arch : glArch (𝓞 K) K (x⁻¹ * γ * x) = glArch (𝓞 K) K (x₀⁻¹ * γ * x₀) := by
    rw [glArch_conj, glArch_conj, harch]
  have hint : ∀ w ∉ S, cpt w (x⁻¹ * γ * x) ∈ localIntegralSet K w := by
    intro w hw
    by_cases hwv : w = v
    · subst hwv; rw [cpt_conj, hcv]; exact hy
    · rw [hconj_w w hwv]; exact D.int₀ w hw
  rw [D.hf _ hint, hconj_arch, Finset.prod_congr rfl fun w hw => by rw [hconj_w w (fun h => hv (h ▸ hw))],
    ← D.fx₀]
  exact D.hx₀

theorem mem_E_of_mem {v : HeightOneSpectrum (𝓞 K)} (hv : v ∈ S)
    (y : Gv (K := K) v) (hy : fS v (y⁻¹ * cpt v γ * y) ≠ 0) :
    f ((x₀ * atPlace v ((cpt v x₀)⁻¹ * y))⁻¹ * γ * (x₀ * atPlace v ((cpt v x₀)⁻¹ * y))) ≠ 0 := by
  classical
  set x : Gad K := x₀ * atPlace v ((cpt v x₀)⁻¹ * y) with hx
  have hcv : cpt v x = y := by
    rw [hx, cpt_mul, cpt_atPlace_self, mul_inv_cancel_left]
  have hcw : ∀ w, w ≠ v → cpt w x = cpt w x₀ := by
    intro w hw
    rw [hx, cpt_mul, cpt_atPlace_of_ne v _ hw, mul_one]
  have harch : glArch (𝓞 K) K x = glArch (𝓞 K) K x₀ := by
    rw [hx, map_mul, glArch_atPlace, mul_one]
  have hconj_w : ∀ w, w ≠ v → cpt w (x⁻¹ * γ * x) = cpt w (x₀⁻¹ * γ * x₀) := by
    intro w hw
    rw [cpt_conj, cpt_conj, hcw w hw]
  have hconj_arch : glArch (𝓞 K) K (x⁻¹ * γ * x) = glArch (𝓞 K) K (x₀⁻¹ * γ * x₀) := by
    rw [glArch_conj, glArch_conj, harch]
  have hint : ∀ w ∉ S, cpt w (x⁻¹ * γ * x) ∈ localIntegralSet K w := by
    intro w hw
    have hwv : w ≠ v := fun h => hw (h ▸ hv)
    rw [hconj_w w hwv]; exact D.int₀ w hw
  rw [D.hf _ hint, hconj_arch]
  refine mul_ne_zero D.fa₀ (Finset.prod_ne_zero_iff.2 fun w hw => ?_)
  by_cases hwv : w = v
  · subst hwv; rw [cpt_conj, hcv]; exact hy
  · rw [hconj_w w hwv]; exact D.fS₀ w hw

theorem mem_E_arch (y : Garch K) (hy : fa (y⁻¹ * glArch (𝓞 K) K γ * y) ≠ 0) :
    f ((x₀ * pairGL ((glArch (𝓞 K) K x₀)⁻¹ * y, 1))⁻¹ * γ * (x₀ * pairGL ((glArch (𝓞 K) K x₀)⁻¹ * y, 1))) ≠ 0 := by
  set x : Gad K := x₀ * pairGL ((glArch (𝓞 K) K x₀)⁻¹ * y, 1) with hx
  have harch : glArch (𝓞 K) K x = y := by
    rw [hx, map_mul, glArch_pairGL, mul_inv_cancel_left]
  have hcw : ∀ w, cpt w x = cpt w x₀ := by
    intro w
    rw [hx, cpt_mul]
    show _ * finComponent (𝓞 K) K w (glFin (𝓞 K) K (pairGL _)) = _
    rw [glFin_pairGL, map_one, mul_one]
  have hconj_w : ∀ w, cpt w (x⁻¹ * γ * x) = cpt w (x₀⁻¹ * γ * x₀) := by
    intro w
    rw [cpt_conj, cpt_conj, hcw w]
  have hint : ∀ w ∉ S, cpt w (x⁻¹ * γ * x) ∈ localIntegralSet K w := by
    intro w hw
    rw [hconj_w w]; exact D.int₀ w hw
  rw [D.hf _ hint, glArch_conj, harch, Finset.prod_congr rfl fun w _ => by rw [hconj_w w]]
  exact mul_ne_zero hy (Finset.prod_ne_zero_iff.2 D.fS₀)

theorem exists_finset : ∃ S₁ : Finset (HeightOneSpectrum (𝓞 K)), S ⊆ S₁ ∧ ∀ v ∉ S₁, ∀ y : Gv (K := K) v,
    y⁻¹ * cpt v γ * y ∈ localIntegralSet K v → ∃ s : Tv γ v, (s : Gv (K := K) v) * y ∈ localIntegralSet K v := by
  classical
  obtain ⟨S₀, hS₀⟩ := exists_finset_subset_unitsAway (K := K) D.hwc
  refine ⟨S ∪ S₀, Finset.subset_union_left, fun v hv y hy => ?_⟩
  have hvS : v ∉ S := fun h => hv (Finset.mem_union_left _ h)
  have hvS₀ : v ∉ S₀ := fun h => hv (Finset.mem_union_right _ h)
  set x : Gad K := x₀ * atPlace v ((cpt v x₀)⁻¹ * y) with hx
  have hxE : f (x⁻¹ * γ * x) ≠ 0 := D.mem_E_of_not_mem hvS y hy
  have hcv : cpt v x = y := by
    rw [hx, cpt_mul, cpt_atPlace_self, mul_inv_cancel_left]
  obtain ⟨t, ht⟩ := D.exists_translate_mem hxE
  have htx : (t : Gad K) * x ∈ unitsAway S₀ := hS₀ ht
  refine ⟨⟨cpt v (t : Gad K), cpt_mem_Tv t v⟩, ?_⟩
  have := htx v hvS₀
  rwa [cpt_mul, hcv] at this

theorem subset_mul_of_mem {v : HeightOneSpectrum (𝓞 K)} (hv : v ∈ S) :
    {y : Gv (K := K) v | fS v (y⁻¹ * cpt v γ * y) ≠ 0} ⊆ (Tv γ v : Set (Gv (K := K) v)) * (cpt v '' tsupport w) := by
  intro y hy
  have h := D.cpt_mem_mul (D.mem_E_of_mem hv y hy) v
  rwa [cpt_mul, cpt_atPlace_self, mul_inv_cancel_left] at h

theorem subset_mul_of_not_mem {v : HeightOneSpectrum (𝓞 K)} (hv : v ∉ S) :
    {y : Gv (K := K) v | y⁻¹ * cpt v γ * y ∈ localIntegralSet K v} ⊆
      (Tv γ v : Set (Gv (K := K) v)) * (cpt v '' tsupport w) := by
  intro y hy
  have h := D.cpt_mem_mul (D.mem_E_of_not_mem hv y hy) v
  rwa [cpt_mul, cpt_atPlace_self, mul_inv_cancel_left] at h

theorem subset_mul_arch :
    {y : Garch K | fa (y⁻¹ * glArch (𝓞 K) K γ * y) ≠ 0} ⊆
      (Tarch γ : Set (Garch K)) * (glArch (𝓞 K) K '' tsupport w) := by
  intro y hy
  have h := D.glArch_mem_mul (D.mem_E_arch y hy)
  rwa [map_mul, glArch_pairGL, mul_inv_cancel_left] at h

end Data

end Main

end AutomorphicForm.AdelicUnitSectionFn
p2m_reactivate "P2MW.S_AutomorphicForm_exists_finset_forall_isSectionFnOn_indicator_localIntegralSet_of_isSectionFnOn_adeleRing.AutomorphicForm P2MW.S_AutomorphicForm_exists_finset_forall_isSectionFnOn_indicator_localIntegralSet_of_isSectionFnOn_adeleRing.AutomorphicForm.AdelicUnitSectionFn"
p2m_reactivate "P2MW.S_AutomorphicForm_exists_finset_forall_isSectionFnOn_indicator_localIntegralSet_of_isSectionFnOn_adeleRing.AutomorphicForm"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_finset_forall_isSectionFnOn_indicator_localIntegralSet_of_isSectionFnOn_adeleRing.AutomorphicForm P2MW.S_AutomorphicForm_exists_finset_forall_isSectionFnOn_indicator_localIntegralSet_of_isSectionFnOn_adeleRing.AutomorphicForm.AdelicUnitSectionFn"

section Solution

open MeasureTheory NumberField IsDedekindDomain
open AutomorphicForm.AdelicUnitSectionFn
open scoped Pointwise

theorem solution
    (K : Type) [Field K] [NumberField K] (γ : GL (Fin 2) (AdeleRing (𝓞 K) K))
    (hγ : AutomorphicForm.IsRegularSemisimple γ)
    (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))))
      (AutomorphicForm.centralizerBorel (AdeleRing (𝓞 K) K) γ))
    (τf : ∀ v : HeightOneSpectrum (𝓞 K),
      @Measure (AutomorphicForm.localCentralizer K v
          (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K γ)))
        (AutomorphicForm.localCentralizerBorel K v
          (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K γ))))
    (hτf : ∀ v : HeightOneSpectrum (𝓞 K), @Measure.IsMulLeftInvariant _
      (AutomorphicForm.localCentralizerBorel K v
        (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K γ))) _ (τf v))
    (hτf1 : ∀ v : HeightOneSpectrum (𝓞 K),
      τf v (Subtype.val ⁻¹' AutomorphicForm.localIntegralSet K v) = 1)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) (fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)
    (fS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ)
    (hf : ∀ g : GL (Fin 2) (AdeleRing (𝓞 K) K),
      (∀ v ∉ S, AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K g) ∈
          AutomorphicForm.localIntegralSet K v) →
        f g = fa (AdelicLevel.glArch (𝓞 K) K g) *
          ∏ v ∈ S, fS v (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K g)))
    (hf0 : ∀ g : GL (Fin 2) (AdeleRing (𝓞 K) K),
      (∃ v ∉ S, AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K g) ∉
          AutomorphicForm.localIntegralSet K v) → f g = 0)
    (hw : ∃ w : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℝ,
      AutomorphicForm.IsSectionFnOn (AdeleRing (𝓞 K) K) γ τ f w)
    (hne : ∃ x : GL (Fin 2) (AdeleRing (𝓞 K) K), f (x⁻¹ * γ * x) ≠ 0) :
    (∃ S₁ : Finset (HeightOneSpectrum (𝓞 K)), S ⊆ S₁ ∧ ∀ v ∉ S₁,
      AutomorphicForm.IsSectionFnOn (v.adicCompletion K)
        (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K γ)) (τf v)
        ((AutomorphicForm.localIntegralSet K v).indicator fun _ => (1 : ℂ))
        ((AutomorphicForm.localIntegralSet K v).indicator fun _ => (1 : ℝ))) ∧
    (∀ v ∈ S, ∃ C : Set (GL (Fin 2) (v.adicCompletion K)), IsCompact C ∧
      {y : GL (Fin 2) (v.adicCompletion K) |
          fS v (y⁻¹ * AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K γ) * y) ≠ 0} ⊆
        (AutomorphicForm.localCentralizer K v
            (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K γ)) :
          Set (GL (Fin 2) (v.adicCompletion K))) * C) ∧
    (∀ v ∉ S, ∃ C : Set (GL (Fin 2) (v.adicCompletion K)), IsCompact C ∧
      {y : GL (Fin 2) (v.adicCompletion K) |
          y⁻¹ * AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K γ) * y ∈
            AutomorphicForm.localIntegralSet K v} ⊆
        (AutomorphicForm.localCentralizer K v
            (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K γ)) :
          Set (GL (Fin 2) (v.adicCompletion K))) * C) ∧
    (∃ C : Set (GL (Fin 2) (InfiniteAdeleRing K)), IsCompact C ∧
      {y : GL (Fin 2) (InfiniteAdeleRing K) |
          fa (y⁻¹ * AdelicLevel.glArch (𝓞 K) K γ * y) ≠ 0} ⊆
        (Subgroup.centralizer ({AdelicLevel.glArch (𝓞 K) K γ} : Set (GL (Fin 2) (InfiniteAdeleRing K))) :
          Set (GL (Fin 2) (InfiniteAdeleRing K))) * C) := by
  obtain ⟨w, -, -, hwc, hw1⟩ := hw
  obtain ⟨x₀, hx₀⟩ := hne
  have D : Data γ S f fa fS τ w x₀ := ⟨hf, hf0, hwc, hw1, hx₀⟩
  refine ⟨?_, fun v hv => ⟨_, hwc.image (continuous_cpt v), D.subset_mul_of_mem hv⟩,
    fun v hv => ⟨_, hwc.image (continuous_cpt v), D.subset_mul_of_not_mem hv⟩,
    ⟨_, hwc.image (AdelicLevel.continuous_glArch (𝓞 K) K), D.subset_mul_arch⟩⟩
  obtain ⟨S₁, hSS₁, hS₁⟩ := D.exists_finset
  refine ⟨S₁, hSS₁, fun v hv => ?_⟩
  haveI := hτf v
  refine ⟨fun y => Set.indicator_nonneg (fun _ _ => zero_le_one) y,
    measurable_const.indicator (AutomorphicForm.isOpen_localIntegralSet K v).measurableSet,
    HasCompactSupport.intro' (AutomorphicForm.isCompact_localIntegralSet K v)
      (AutomorphicForm.isCompact_localIntegralSet K v).isClosed fun y hy => Set.indicator_of_notMem hy _,
    fun y hy => ?_⟩
  have hy' : y⁻¹ * cpt v γ * y ∈ AutomorphicForm.localIntegralSet K v := by
    by_contra h
    exact hy (Set.indicator_of_notMem h _)
  obtain ⟨s, hs⟩ := hS₁ v hv y hy'
  exact integral_indicator_translate_eq_one hγ v (τf v) (hτf1 v) s y hs

end Solution
p2m_reactivate "P2MW.S_AutomorphicForm_exists_finset_forall_isSectionFnOn_indicator_localIntegralSet_of_isSectionFnOn_adeleRing.AutomorphicForm P2MW.S_AutomorphicForm_exists_finset_forall_isSectionFnOn_indicator_localIntegralSet_of_isSectionFnOn_adeleRing.AutomorphicForm.AdelicUnitSectionFn"

end S_AutomorphicForm_exists_finset_forall_isSectionFnOn_indicator_localIntegralSet_of_isSectionFnOn_adeleRing
end P2MW
export P2MW.S_AutomorphicForm_exists_finset_forall_isSectionFnOn_indicator_localIntegralSet_of_isSectionFnOn_adeleRing (solution)
