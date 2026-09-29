-- Prove2me | solution 1 for AutomorphicForm.isSectionFnOn_adeleRing_indicator_prod_of_forall_isSectionFnOn
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/f9ecb12c-3944-5a99-be63-a93447d916cd

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_AutomorphicForm_isSectionFnOn_adeleRing_indicator_prod_of_forall_isSectionFnOn

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory MeasureTheory.Measure Topology TopologicalSpace Set Filter
open NumberField.AdelicLevel

open scoped NNReal ENNReal

noncomputable section

namespace AutomorphicForm
p2m_export "AutomorphicForm" "glBorelOf centralizerBorel IsSectionFnOn integralUnitsSet localIntegralSet one_mem_localIntegralSet isCompact_localIntegralSet isOpen_localIntegralSet localGLBorel localCentralizer localCentralizerBorel unitFinSet one_mem_unitFinSet isOpen_unitFinSet"
namespace AdelicProductSectionFn
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
  exact inv_mem_localIntegralSet _ (h3 v)

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

def box (Ca : Set (Garch K)) (Cv : ∀ v : S, Set (Gv (K := K) v.1)) : Set (Gad K) :=
  {x : Gad K | glArch (𝓞 K) K x ∈ Ca ∧ (∀ v : S, cpt v.1 x ∈ Cv v) ∧ ∀ v ∉ S, cpt v x ∈ localIntegralSet K v}

theorem mem_box_iff {Ca : Set (Garch K)} {Cv : ∀ v : S, Set (Gv (K := K) v.1)} (x : Gad K) :
    x ∈ box S Ca Cv ↔ glArch (𝓞 K) K x ∈ Ca ∧ (∀ v : S, cpt v.1 x ∈ Cv v) ∧
      ∀ v ∉ S, cpt v x ∈ localIntegralSet K v :=
  Iff.rfl

theorem box_eq (Ca : Set (Garch K)) (Cv : ∀ v : S, Set (Gv (K := K) v.1)) :
    box S Ca Cv = (glArch (𝓞 K) K ⁻¹' Ca ∩ ⋂ v : S, cpt v.1 ⁻¹' Cv v) ∩ (unitsAway S : Set (Gad K)) := by
  ext x
  simp only [mem_box_iff, Set.mem_inter_iff, Set.mem_preimage, Set.mem_iInter, SetLike.mem_coe,
    mem_unitsAway_iff, and_assoc]

theorem isClosed_box {Ca : Set (Garch K)} (hCa : IsClosed Ca) {Cv : ∀ v : S, Set (Gv (K := K) v.1)}
    (hCv : ∀ v, IsClosed (Cv v)) : IsClosed (box S Ca Cv) := by
  rw [box_eq]
  exact ((hCa.preimage (continuous_glArch (𝓞 K) K)).inter
    (isClosed_iInter fun v => (hCv v).preimage (continuous_cpt v.1))).inter (isClosed_unitsAway S)

theorem isCompact_box {Ca : Set (Garch K)} (hCa : IsCompact Ca) {Cv : ∀ v : S, Set (Gv (K := K) v.1)}
    (hCv : ∀ v, IsCompact (Cv v)) : IsCompact (box S Ca Cv) := by
  have hCc : IsCompact (Ca ×ˢ Set.pi Set.univ Cv) := hCa.prod (isCompact_univ_pi hCv)
  have hbig : IsCompact ((fun p : Gad K × Gad K => p.1 * p.2) ''
      ((fromLoc S '' (Ca ×ˢ Set.pi Set.univ Cv)) ×ˢ kerSet S)) :=
    ((hCc.image (continuous_fromLoc S)).prod (isCompact_kerSet S)).image continuous_mul
  refine hbig.of_isClosed_subset (isClosed_box S hCa.isClosed fun v => (hCv v).isClosed) fun x hx => ?_
  refine mem_image_mul_of_mem S _ (fun v hv => hx.2.2 v hv) ?_
  rw [Set.mem_prod, toLoc_apply_fst, Set.mem_univ_pi]
  exact ⟨hx.1, fun v => hx.2.1 v⟩

end Kernel

section Main

variable (γ : Gad K)

abbrev Tad : Subgroup (Gad K) := Subgroup.centralizer ({γ} : Set (Gad K))

abbrev Tarch : Subgroup (Garch K) := Subgroup.centralizer ({glArch (𝓞 K) K γ} : Set (Garch K))

abbrev Tv (v : HeightOneSpectrum (𝓞 K)) : Subgroup (Gv (K := K) v) :=
  Subgroup.centralizer ({cpt v γ} : Set (Gv (K := K) v))

variable {γ}

theorem glArch_conj (x : Gad K) :
    glArch (𝓞 K) K (x⁻¹ * γ * x) = (glArch (𝓞 K) K x)⁻¹ * glArch (𝓞 K) K γ * glArch (𝓞 K) K x := by
  rw [map_mul, map_mul, map_inv]

theorem cpt_conj (v : HeightOneSpectrum (𝓞 K)) (x : Gad K) :
    cpt v (x⁻¹ * γ * x) = (cpt v x)⁻¹ * cpt v γ * cpt v x := by
  rw [cpt_mul, cpt_mul, cpt_inv]

variable (γ)
variable (τ : Measure (Tad γ)) (τa : Measure (Tarch γ)) (τf : ∀ v : HeightOneSpectrum (𝓞 K), Measure (Tv γ v))
  (c : ℝ)
  (f : Gad K → ℂ) (fa : Garch K → ℂ) (fS : ∀ v : HeightOneSpectrum (𝓞 K), Gv (K := K) v → ℂ)
  (wa : Garch K → ℝ) (wf : ∀ v : HeightOneSpectrum (𝓞 K), Gv (K := K) v → ℝ)

def prodFn : Gad K → ℝ :=
  (unitsAway S : Set (Gad K)).indicator fun x => c⁻¹ * (wa (glArch (𝓞 K) K x) * ∏ v ∈ S, wf v (cpt v x))

theorem prodFn_of_mem {x : Gad K} (hx : x ∈ unitsAway S) :
    prodFn S c wa wf x = c⁻¹ * (wa (glArch (𝓞 K) K x) * ∏ v ∈ S, wf v (cpt v x)) :=
  Set.indicator_of_mem hx _

theorem prodFn_of_not_mem {x : Gad K} (hx : x ∉ unitsAway S) : prodFn S c wa wf x = 0 :=
  Set.indicator_of_notMem hx _

theorem prodFn_nonneg (hc : 0 < c) (hwa : ∀ y, 0 ≤ wa y) (hwf : ∀ v ∈ S, ∀ y, 0 ≤ wf v y) (x : Gad K) :
    0 ≤ prodFn S c wa wf x := by
  by_cases hx : x ∈ unitsAway S
  · rw [prodFn_of_mem S c wa wf hx]
    exact mul_nonneg (inv_nonneg.2 hc.le)
      (mul_nonneg (hwa _) (Finset.prod_nonneg fun v hv => hwf v hv _))
  · rw [prodFn_of_not_mem S c wa wf hx]

theorem measurable_prodFn (hwa : Measurable wa) (hwf : ∀ v ∈ S, Measurable (wf v)) :
    Measurable (prodFn S c wa wf) := by
  refine Measurable.indicator ?_ (measurableSet_unitsAway S)
  refine measurable_const.mul ((hwa.comp (continuous_glArch (𝓞 K) K).measurable).mul ?_)
  exact Finset.measurable_prod S fun v hv => (hwf v hv).comp (continuous_cpt v).measurable

theorem hasCompactSupport_prodFn (hwa : HasCompactSupport wa) (hwf : ∀ v ∈ S, HasCompactSupport (wf v)) :
    HasCompactSupport (prodFn S c wa wf) := by
  have hBc : IsCompact (box S (tsupport wa) fun v : S => tsupport (wf v.1)) :=
    isCompact_box S hwa fun v => hwf v.1 v.2
  have hBcl : IsClosed (box S (tsupport wa) fun v : S => tsupport (wf v.1)) :=
    isClosed_box S (isClosed_tsupport wa) fun v => isClosed_tsupport _
  refine HasCompactSupport.intro' hBc hBcl fun x hx => ?_
  by_cases hxU : x ∈ unitsAway S
  · rw [prodFn_of_mem S c wa wf hxU]
    have : ¬ (glArch (𝓞 K) K x ∈ tsupport wa ∧ ∀ v : S, cpt v.1 x ∈ tsupport (wf v.1)) := by
      intro h
      exact hx ⟨h.1, h.2, hxU⟩
    rw [not_and_or, not_forall] at this
    rcases this with h | ⟨v, hv⟩
    · rw [image_eq_zero_of_notMem_tsupport h, zero_mul, mul_zero]
    · have h0 : wf v.1 (cpt v.1 x) = 0 := image_eq_zero_of_notMem_tsupport hv
      rw [Finset.prod_eq_zero (Finset.coe_mem v) h0, mul_zero, mul_zero]
  · exact prodFn_of_not_mem S c wa wf hxU

theorem integral_prodFn_translate_eq_one (hc : 0 < c)
    (hτ : ∀ (S' : Finset (HeightOneSpectrum (𝓞 K)))
        (W : Gad K → ℂ) (Wa : Garch K → ℂ) (WS : ∀ v : HeightOneSpectrum (𝓞 K), Gv (K := K) v → ℂ),
        AEStronglyMeasurable (fun t : Tarch γ => Wa t) τa →
        (∀ v ∈ S', AEStronglyMeasurable (fun t : Tv γ v => WS v t) (τf v)) →
        (∀ t : Tad γ, (∀ v ∉ S', cpt v (t : Gad K) ∈ localIntegralSet K v) →
            W t = Wa (glArch (𝓞 K) K (t : Gad K)) * ∏ v ∈ S', WS v (cpt v (t : Gad K))) →
        (∀ t : Tad γ, (∃ v ∉ S', cpt v (t : Gad K) ∉ localIntegralSet K v) → W t = 0) →
          ∫ t, W t ∂τ = c * (∫ t, Wa t ∂τa) * ∏ v ∈ S', ∫ t, WS v t ∂(τf v))
    (hf : ∀ g : Gad K, (∀ v ∉ S, cpt v g ∈ localIntegralSet K v) →
        f g = fa (glArch (𝓞 K) K g) * ∏ v ∈ S, fS v (cpt v g))
    (hf0 : ∀ g : Gad K, (∃ v ∉ S, cpt v g ∉ localIntegralSet K v) → f g = 0)
    (hwam : Measurable wa)
    (hwa1 : ∀ y : Garch K, fa (y⁻¹ * glArch (𝓞 K) K γ * y) ≠ 0 →
      ∫ t : Tarch γ, wa ((t : Garch K) * y) ∂τa = 1)
    (hwfm : ∀ v ∈ S, Measurable (wf v))
    (hwf1 : ∀ v ∈ S, ∀ y : Gv (K := K) v, fS v (y⁻¹ * cpt v γ * y) ≠ 0 →
      ∫ t : Tv γ v, wf v ((t : Gv (K := K) v) * y) ∂(τf v) = 1)
    (hunit : ∀ v ∉ S, ∀ y : Gv (K := K) v, y⁻¹ * cpt v γ * y ∈ localIntegralSet K v →
      ∫ t : Tv γ v, (localIntegralSet K v).indicator (fun _ => (1 : ℝ)) ((t : Gv (K := K) v) * y) ∂(τf v) = 1)
    (x : Gad K) (hx : f (x⁻¹ * γ * x) ≠ 0) :
    ∫ t : Tad γ, prodFn S c wa wf ((t : Gad K) * x) ∂τ = 1 := by
  classical

  have hint : ∀ v ∉ S, cpt v (x⁻¹ * γ * x) ∈ localIntegralSet K v := by
    by_contra h
    push Not at h
    obtain ⟨v, hv, hv'⟩ := h
    exact hx (hf0 _ ⟨v, hv, hv'⟩)
  have hfx : f (x⁻¹ * γ * x) = fa (glArch (𝓞 K) K (x⁻¹ * γ * x)) * ∏ v ∈ S, fS v (cpt v (x⁻¹ * γ * x)) :=
    hf _ hint
  have hfa : fa ((glArch (𝓞 K) K x)⁻¹ * glArch (𝓞 K) K γ * glArch (𝓞 K) K x) ≠ 0 := by
    rw [← glArch_conj]
    intro h
    rw [hfx, h, zero_mul] at hx
    exact hx rfl
  have hfS : ∀ v ∈ S, fS v ((cpt v x)⁻¹ * cpt v γ * cpt v x) ≠ 0 := by
    intro v hv h
    rw [← cpt_conj] at h
    rw [hfx, Finset.prod_eq_zero hv h, mul_zero] at hx
    exact hx rfl

  set B : Finset (HeightOneSpectrum (𝓞 K)) := (finite_setOf_cpt_not_mem x).toFinset \ S with hB
  have hBS : Disjoint S B := Finset.disjoint_sdiff
  have hmemB : ∀ v, v ∈ B ↔ cpt v x ∉ localIntegralSet K v ∧ v ∉ S := fun v => by
    rw [hB, Finset.mem_sdiff, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  set Sx : Finset (HeightOneSpectrum (𝓞 K)) := S ∪ B with hSx
  have hSSx : S ⊆ Sx := Finset.subset_union_left
  have hxint : ∀ v ∉ Sx, cpt v x ∈ localIntegralSet K v := by
    intro v hv
    by_contra h
    have hvS : v ∉ S := fun h' => hv (hSSx h')
    exact hv (Finset.mem_union_right _ ((hmemB v).2 ⟨h, hvS⟩))

  let Wa : Garch K → ℂ := fun y => ((c⁻¹ * wa (y * glArch (𝓞 K) K x) : ℝ) : ℂ)
  let WS : ∀ v : HeightOneSpectrum (𝓞 K), Gv (K := K) v → ℂ := fun v y =>
    if v ∈ S then ((wf v (y * cpt v x) : ℝ) : ℂ)
    else (((localIntegralSet K v).indicator (fun _ => (1 : ℝ)) (y * cpt v x) : ℝ) : ℂ)
  let W : Gad K → ℂ := fun g => ((prodFn S c wa wf (g * x) : ℝ) : ℂ)

  have hWa : AEStronglyMeasurable (fun t : Tarch γ => Wa t) τa := by
    refine (Complex.measurable_ofReal.comp ?_).aestronglyMeasurable
    refine measurable_const.mul (hwam.comp ?_)
    exact (continuous_subtype_val.mul continuous_const).measurable
  have hWS : ∀ v ∈ Sx, AEStronglyMeasurable (fun t : Tv γ v => WS v t) (τf v) := by
    intro v _
    by_cases hv : v ∈ S
    · have : (fun t : Tv γ v => WS v t) = fun t : Tv γ v => ((wf v ((t : Gv (K := K) v) * cpt v x) : ℝ) : ℂ) := by
        funext t; simp only [WS, if_pos hv]
      rw [this]
      refine (Complex.measurable_ofReal.comp ((hwfm v hv).comp ?_)).aestronglyMeasurable
      exact (continuous_subtype_val.mul continuous_const).measurable
    · have : (fun t : Tv γ v => WS v t) = fun t : Tv γ v =>
          (((localIntegralSet K v).indicator (fun _ => (1 : ℝ)) ((t : Gv (K := K) v) * cpt v x) : ℝ) : ℂ) := by
        funext t; simp only [WS, if_neg hv]
      rw [this]
      refine (Complex.measurable_ofReal.comp ((measurable_const.indicator
        (isOpen_localIntegralSet K v).measurableSet).comp ?_)).aestronglyMeasurable
      exact (continuous_subtype_val.mul continuous_const).measurable

  have hshape : ∀ t : Tad γ, (∀ v ∉ Sx, cpt v (t : Gad K) ∈ localIntegralSet K v) →
      W t = Wa (glArch (𝓞 K) K (t : Gad K)) * ∏ v ∈ Sx, WS v (cpt v (t : Gad K)) := by
    intro t ht
    have hprodSx : ∏ v ∈ Sx, WS v (cpt v (t : Gad K)) =
        (∏ v ∈ S, ((wf v (cpt v (t : Gad K) * cpt v x) : ℝ) : ℂ)) *
          ∏ v ∈ B, (((localIntegralSet K v).indicator (fun _ => (1 : ℝ)) (cpt v (t : Gad K) * cpt v x) : ℝ) : ℂ) := by
      rw [hSx, Finset.prod_union hBS]
      congr 1
      · exact Finset.prod_congr rfl fun v hv => by simp only [WS, if_pos hv]
      · exact Finset.prod_congr rfl fun v hv => by simp only [WS, if_neg ((hmemB v).1 hv).2]
    by_cases htx : (t : Gad K) * x ∈ unitsAway S
    ·
      have hB1 : ∏ v ∈ B, (((localIntegralSet K v).indicator (fun _ => (1 : ℝ))
          (cpt v (t : Gad K) * cpt v x) : ℝ) : ℂ) = 1 := by
        refine Finset.prod_eq_one fun v hv => ?_
        have hvS : v ∉ S := ((hmemB v).1 hv).2
        have : cpt v (t : Gad K) * cpt v x ∈ localIntegralSet K v := by
          rw [← cpt_mul]; exact htx v hvS
        rw [Set.indicator_of_mem this, Complex.ofReal_one]
      simp only [W]
      rw [prodFn_of_mem S c wa wf htx, hprodSx, hB1, mul_one, map_mul, Complex.ofReal_mul,
        Complex.ofReal_mul, Complex.ofReal_prod]
      simp only [Wa, cpt_mul, Complex.ofReal_mul]
      ring
    ·
      obtain ⟨v, hvS, hv⟩ : ∃ v ∉ S, cpt v ((t : Gad K) * x) ∉ localIntegralSet K v := by
        by_contra h
        push Not at h
        exact htx h
      have hvSx : v ∈ Sx := by
        by_contra h'
        rw [cpt_mul] at hv
        exact hv (mul_mem_localIntegralSet v (ht v h') (hxint v h'))
      have hvB : v ∈ B := by
        rcases Finset.mem_union.1 hvSx with h | h
        · exact absurd h hvS
        · exact h
      have hB0 : ∏ v ∈ B, (((localIntegralSet K v).indicator (fun _ => (1 : ℝ))
          (cpt v (t : Gad K) * cpt v x) : ℝ) : ℂ) = 0 := by
        refine Finset.prod_eq_zero hvB ?_
        rw [← cpt_mul, Set.indicator_of_notMem hv, Complex.ofReal_zero]
      simp only [W]
      rw [prodFn_of_not_mem S c wa wf htx, hprodSx, hB0, mul_zero, mul_zero, Complex.ofReal_zero]
  have hvanish : ∀ t : Tad γ, (∃ v ∉ Sx, cpt v (t : Gad K) ∉ localIntegralSet K v) → W t = 0 := by
    rintro t ⟨v, hv, hvt⟩
    have hvS : v ∉ S := fun h => hv (hSSx h)
    have htx : (t : Gad K) * x ∉ unitsAway S := by
      intro h
      have := h v hvS
      rw [cpt_mul, mul_mem_localIntegralSet_iff_right v (hxint v hv)] at this
      exact hvt this
    simp only [W]
    rw [prodFn_of_not_mem S c wa wf htx, Complex.ofReal_zero]

  have key := hτ Sx W Wa WS hWa hWS hshape hvanish
  have hIa : ∫ t : Tarch γ, Wa t ∂τa = ((c⁻¹ : ℝ) : ℂ) := by
    simp only [Wa]
    rw [integral_complex_ofReal, integral_const_mul, hwa1 _ hfa, mul_one]
  have hIS : ∏ v ∈ Sx, ∫ t : Tv γ v, WS v t ∂(τf v) = 1 := by
    refine Finset.prod_eq_one fun v _ => ?_
    by_cases hv : v ∈ S
    · simp only [WS, if_pos hv]
      rw [integral_complex_ofReal, hwf1 v hv _ (hfS v hv), Complex.ofReal_one]
    · simp only [WS, if_neg hv]
      rw [integral_complex_ofReal, hunit v hv _ (by rw [← cpt_conj]; exact hint v hv), Complex.ofReal_one]
  rw [hIa, hIS, mul_one, ← Complex.ofReal_mul, mul_inv_cancel₀ hc.ne'] at key
  have hW : ∫ t : Tad γ, W t ∂τ = ((∫ t : Tad γ, prodFn S c wa wf ((t : Gad K) * x) ∂τ : ℝ) : ℂ) := by
    simp only [W]
    exact integral_complex_ofReal
  rw [hW, Complex.ofReal_one] at key
  exact_mod_cast key

end Main

end AutomorphicForm.AdelicProductSectionFn
p2m_reactivate "P2MW.S_AutomorphicForm_isSectionFnOn_adeleRing_indicator_prod_of_forall_isSectionFnOn.AutomorphicForm P2MW.S_AutomorphicForm_isSectionFnOn_adeleRing_indicator_prod_of_forall_isSectionFnOn.AutomorphicForm.AdelicProductSectionFn"
p2m_reactivate "P2MW.S_AutomorphicForm_isSectionFnOn_adeleRing_indicator_prod_of_forall_isSectionFnOn.AutomorphicForm"

end
p2m_reactivate "P2MW.S_AutomorphicForm_isSectionFnOn_adeleRing_indicator_prod_of_forall_isSectionFnOn.AutomorphicForm P2MW.S_AutomorphicForm_isSectionFnOn_adeleRing_indicator_prod_of_forall_isSectionFnOn.AutomorphicForm.AdelicProductSectionFn"

section Solution

open MeasureTheory NumberField IsDedekindDomain
open AutomorphicForm.AdelicProductSectionFn

theorem solution
    (K : Type) [Field K] [NumberField K] (γ : GL (Fin 2) (AdeleRing (𝓞 K) K))
    (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))))
      (AutomorphicForm.centralizerBorel (AdeleRing (𝓞 K) K) γ))
    (τa : @Measure (Subgroup.centralizer
        ({AdelicLevel.glArch (𝓞 K) K γ} : Set (GL (Fin 2) (InfiniteAdeleRing K))))
      (AutomorphicForm.centralizerBorel (InfiniteAdeleRing K) (AdelicLevel.glArch (𝓞 K) K γ)))
    (τf : ∀ v : HeightOneSpectrum (𝓞 K),
      @Measure (AutomorphicForm.localCentralizer K v
          (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K γ)))
        (AutomorphicForm.localCentralizerBorel K v
          (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K γ))))
    (c : ℝ) (hc : 0 < c)
    (hτ : ∀ (S : Finset (HeightOneSpectrum (𝓞 K)))
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
          ∫ t, W t ∂τ = c * (∫ t, Wa t ∂τa) * ∏ v ∈ S, ∫ t, WS v t ∂(τf v))
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
    (wa : GL (Fin 2) (InfiniteAdeleRing K) → ℝ)
    (hwa : AutomorphicForm.IsSectionFnOn (InfiniteAdeleRing K) (AdelicLevel.glArch (𝓞 K) K γ) τa fa wa)
    (wf : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℝ)
    (hwf : ∀ v ∈ S, AutomorphicForm.IsSectionFnOn (v.adicCompletion K)
      (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K γ)) (τf v) (fS v) (wf v))
    (hunit : ∀ v ∉ S, AutomorphicForm.IsSectionFnOn (v.adicCompletion K)
      (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K γ)) (τf v)
      ((AutomorphicForm.localIntegralSet K v).indicator fun _ => (1 : ℂ))
      ((AutomorphicForm.localIntegralSet K v).indicator fun _ => (1 : ℝ))) :
    AutomorphicForm.IsSectionFnOn (AdeleRing (𝓞 K) K) γ τ f
      ({x : GL (Fin 2) (AdeleRing (𝓞 K) K) |
          ∀ v ∉ S, AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K x) ∈
            AutomorphicForm.localIntegralSet K v}.indicator
        fun x => c⁻¹ * (wa (AdelicLevel.glArch (𝓞 K) K x) *
          ∏ v ∈ S, wf v (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K x)))) := by
  obtain ⟨hwa0, hwam, hwac, hwa1⟩ := hwa
  have hwf0 : ∀ v ∈ S, ∀ y, 0 ≤ wf v y := fun v hv => (hwf v hv).1
  have hwfm : ∀ v ∈ S, Measurable (wf v) := fun v hv => (hwf v hv).2.1
  have hwfc : ∀ v ∈ S, HasCompactSupport (wf v) := fun v hv => (hwf v hv).2.2.1
  have hwf1 : ∀ v ∈ S, ∀ y : Gv (K := K) v, fS v (y⁻¹ * cpt v γ * y) ≠ 0 →
      ∫ t : Tv γ v, wf v ((t : Gv (K := K) v) * y) ∂(τf v) = 1 := fun v hv => (hwf v hv).2.2.2
  have hunit' : ∀ v ∉ S, ∀ y : Gv (K := K) v, y⁻¹ * cpt v γ * y ∈ AutomorphicForm.localIntegralSet K v →
      ∫ t : Tv γ v, (AutomorphicForm.localIntegralSet K v).indicator (fun _ => (1 : ℝ))
        ((t : Gv (K := K) v) * y) ∂(τf v) = 1 := by
    intro v hv y hy
    refine (hunit v hv).2.2.2 y ?_
    rw [Set.indicator_of_mem hy]
    exact one_ne_zero
  show (∀ x, 0 ≤ prodFn S c wa wf x) ∧ Measurable (prodFn S c wa wf) ∧ HasCompactSupport (prodFn S c wa wf) ∧
    ∀ x, f (x⁻¹ * γ * x) ≠ 0 → ∫ t : Tad γ, prodFn S c wa wf ((t : Gad K) * x) ∂τ = 1
  exact ⟨prodFn_nonneg S c wa wf hc hwa0 hwf0, measurable_prodFn S c wa wf hwam hwfm,
    hasCompactSupport_prodFn S c wa wf hwac hwfc,
    fun x hx => integral_prodFn_translate_eq_one S γ τ τa τf c f fa fS wa wf hc hτ hf hf0 hwam hwa1 hwfm
      hwf1 hunit' x hx⟩

end Solution
p2m_reactivate "P2MW.S_AutomorphicForm_isSectionFnOn_adeleRing_indicator_prod_of_forall_isSectionFnOn.AutomorphicForm P2MW.S_AutomorphicForm_isSectionFnOn_adeleRing_indicator_prod_of_forall_isSectionFnOn.AutomorphicForm.AdelicProductSectionFn"

end S_AutomorphicForm_isSectionFnOn_adeleRing_indicator_prod_of_forall_isSectionFnOn
end P2MW
export P2MW.S_AutomorphicForm_isSectionFnOn_adeleRing_indicator_prod_of_forall_isSectionFnOn (solution)
