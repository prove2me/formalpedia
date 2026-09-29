-- Prove2me | solution 1 for AutomorphicForm.exists_isOrbitalIntegralOn_adeleRing_eq_mul_prod_of_isUnitFactorization
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/4e7273ff-2c43-5c4a-a6c7-3b9e4e724127

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_AdelicHaar
import Theorems.Thm_AutomorphicForm_exists_finset_forall_isSectionFnOn_indicator_localIntegralSet_of_isSectionFnOn_adeleRing
import Theorems.Thm_AutomorphicForm_isSectionFnOn_adeleRing_indicator_prod_of_forall_isSectionFnOn
import Theorems.Thm_AutomorphicForm_IsOrbitalIntegralOn_unique_of_isRegularSemisimple
import Theorems.Thm_MeasureTheory_exists_hasCompactSupport_integral_subgroup_translate_eq_one_of_subset_mul
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
p2m_attr_erase "ext" "NumberField.InfinitePlace.Completion.ext"
namespace P2MW.S_AutomorphicForm_exists_isOrbitalIntegralOn_adeleRing_eq_mul_prod_of_isUnitFactorization
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory MeasureTheory.Measure Topology TopologicalSpace Set Filter
open NumberField.AdelicLevel NumberField.AdelicHaar
open scoped NNReal ENNReal Pointwise Classical

noncomputable section

namespace AutomorphicForm
p2m_export "AutomorphicForm" "glBorelOf centralizerBorel IsSectionFnOn IsOrbitalIntegralOn IsUnitFactorization integralUnitsSet localIntegralSet one_mem_localIntegralSet isCompact_localIntegralSet isOpen_localIntegralSet localGLBorel locallyCompactSpace_localGL localHaar localHaar_localIntegralSet localCentralizer localCentralizerBorel IsSectionFn IsOrbitalIntegral unitFinSet one_mem_unitFinSet isOpen_unitFinSet IsRegularSemisimple archEntries IsArchTestFactor exists_finset_forall_isSectionFnOn_indicator_localIntegralSet_of_isSectionFnOn_adeleRing isSectionFnOn_adeleRing_indicator_prod_of_forall_isSectionFnOn IsOrbitalIntegralOn.unique_of_isRegularSemisimple"
namespace AdelicOrbitalEuler
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

section MoreInstances

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

scoped instance instT2Gad : T2Space (Gad K) := by
  haveI : T2Space (Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) :=
    inferInstanceAs (T2Space (Fin 2 → Fin 2 → AdeleRing (𝓞 K) K))
  exact Units.isEmbedding_embedProduct.t2Space

end MoreInstances

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

theorem isRegularSemisimple_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    {g : GL (Fin 2) R} (hg : IsRegularSemisimple g) :
    IsRegularSemisimple (Matrix.GeneralLinearGroup.map f g) := by
  unfold IsRegularSemisimple at hg ⊢
  have hval : ((Matrix.GeneralLinearGroup.map f g : GL (Fin 2) S) : Matrix (Fin 2) (Fin 2) S) =
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

private theorem _root_.AutomorphicForm.AdelicOrbitalEuler.isClosed_centralizer {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    (g : G) : IsClosed ((Subgroup.centralizer ({g} : Set G) : Subgroup G) : Set G) := by
  show IsClosed (Set.centralizer ({g} : Set G))
  exact Set.isClosed_centralizer _

p2m_export "AutomorphicForm.AdelicOrbitalEuler" "isClosed_centralizer"
theorem continuous_conj {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (g : G) :
    Continuous fun x : G => x⁻¹ * g * x :=
  (continuous_id.inv.mul continuous_const).mul continuous_id

end Regular

section TestFn

open NumberField.InfinitePlace NumberField.InfinitePlace.Completion

omit [NumberField K] in
theorem continuous_ringEquiv_mixedSpace : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace K) := by
  refine continuous_prodMk.2 ⟨continuous_pi fun v => ?_, continuous_pi fun v => ?_⟩
  · exact (isometry_extensionEmbeddingOfIsReal v.2).continuous.comp (continuous_apply _)
  · exact (isometry_extensionEmbedding v.1).continuous.comp (continuous_apply _)

omit [NumberField K] in
theorem continuous_archEntries : Continuous (archEntries K : Garch K → _) :=
  continuous_pi fun i => continuous_pi fun j =>
    (continuous_ringEquiv_mixedSpace (K := K)).comp (Units.continuous_val.matrix_elem i j)

namespace IsArchTestFactor
private theorem _root_.AutomorphicForm.AdelicOrbitalEuler.IsArchTestFactor.continuous {fa : Garch K → ℂ} (h : IsArchTestFactor K fa) : Continuous fa := by
  obtain ⟨⟨Φ, hΦ, hfa⟩, -⟩ := h
  have : fa = Φ ∘ archEntries K := funext hfa
  rw [this]
  exact hΦ.continuous.comp continuous_archEntries

end IsArchTestFactor
p2m_export "AutomorphicForm.AdelicOrbitalEuler" "IsArchTestFactor.continuous"
variable {S : Finset (HeightOneSpectrum (𝓞 K))} {f : Gad K → ℂ} {fa : Garch K → ℂ} {ff : Gfin K → ℂ}
  {fS : ∀ v : HeightOneSpectrum (𝓞 K), Gv (K := K) v → ℂ}

theorem continuous_of_isUnitFactorization (hf : IsUnitFactorization K S f fa ff fS) : Continuous f := by
  have h : f = fun g => fa (glArch (𝓞 K) K g) * ff (glFin (𝓞 K) K g) := funext hf.2.2.2.2.2
  rw [h]
  exact ((IsArchTestFactor.continuous hf.1).comp (continuous_glArch (𝓞 K) K)).mul
    (hf.2.1.1.continuous.comp (continuous_glFin (𝓞 K) K))

theorem bounded_of_isUnitFactorization (hf : IsUnitFactorization K S f fa ff fS) : ∃ C : ℝ, ∀ g, ‖f g‖ ≤ C := by
  obtain ⟨Ca, hCa⟩ := ((IsArchTestFactor.continuous hf.1).norm).bddAbove_range_of_hasCompactSupport hf.1.2.norm
  obtain ⟨Cf, hCf⟩ := (hf.2.1.1.continuous.norm).bddAbove_range_of_hasCompactSupport hf.2.1.2.norm
  refine ⟨Ca * Cf, fun g => ?_⟩
  rw [hf.2.2.2.2.2 g, norm_mul]
  have ha : ‖fa (glArch (𝓞 K) K g)‖ ≤ Ca := hCa ⟨_, rfl⟩
  have hb : ‖ff (glFin (𝓞 K) K g)‖ ≤ Cf := hCf ⟨_, rfl⟩
  have hCa0 : 0 ≤ Ca := (norm_nonneg _).trans ha
  exact mul_le_mul ha hb (norm_nonneg _) hCa0

end TestFn

section Shape

variable (S : Finset (HeightOneSpectrum (𝓞 K))) (f : Gad K → ℂ) (fa : Garch K → ℂ) (ff : Gfin K → ℂ)
  (fS : ∀ v : HeightOneSpectrum (𝓞 K), Gv (K := K) v → ℂ)

def fSp (v : HeightOneSpectrum (𝓞 K)) : Gv (K := K) v → ℂ :=
  if v ∈ S then fS v else (localIntegralSet K v).indicator fun _ => (1 : ℂ)

theorem fSp_of_mem {v : HeightOneSpectrum (𝓞 K)} (hv : v ∈ S) : fSp S fS v = fS v := by
  simp only [fSp, hv, if_true]

theorem fSp_of_not_mem {v : HeightOneSpectrum (𝓞 K)} (hv : v ∉ S) :
    fSp S fS v = (localIntegralSet K v).indicator fun _ => (1 : ℂ) := by
  simp only [fSp, hv, if_false]

variable {S f fa ff fS}

theorem shape_of_subset (hf : IsUnitFactorization K S f fa ff fS) {S' : Finset (HeightOneSpectrum (𝓞 K))}
    (hSS' : S ⊆ S') (g : Gad K) (hg : ∀ v ∉ S', cpt v g ∈ localIntegralSet K v) :
    f g = fa (glArch (𝓞 K) K g) * ∏ v ∈ S', fSp S fS v (cpt v g) := by
  rw [hf.2.2.2.2.2 g]
  by_cases hall : ∀ v ∈ S', v ∉ S → cpt v g ∈ localIntegralSet K v
  · have hint : ∀ v ∉ S, cpt v g ∈ localIntegralSet K v := by
      intro v hv
      by_cases hv' : v ∈ S'
      · exact hall v hv' hv
      · exact hg v hv'
    rw [hf.2.2.2.1 _ hint]
    congr 1
    rw [← Finset.prod_subset hSS' (fun v hv' hv => ?_)]
    · exact Finset.prod_congr rfl fun v hv => by rw [fSp_of_mem S fS hv]
    · rw [fSp_of_not_mem S fS hv, Set.indicator_of_mem (hall v hv' hv)]
  · push Not at hall
    obtain ⟨v, hv', hv, hgv⟩ := hall
    rw [hf.2.2.2.2.1 _ ⟨v, hv, hgv⟩, mul_zero]
    symm
    apply mul_eq_zero_of_right
    exact Finset.prod_eq_zero hv' (by rw [fSp_of_not_mem S fS hv, Set.indicator_of_notMem hgv])

theorem vanish_of_subset (hf : IsUnitFactorization K S f fa ff fS) {S' : Finset (HeightOneSpectrum (𝓞 K))}
    (hSS' : S ⊆ S') (g : Gad K) (hg : ∃ v ∉ S', cpt v g ∉ localIntegralSet K v) : f g = 0 := by
  obtain ⟨v, hv', hgv⟩ := hg
  rw [hf.2.2.2.2.2 g, hf.2.2.2.2.1 _ ⟨v, fun hv => hv' (hSS' hv), hgv⟩, mul_zero]

theorem measurable_fSp (hf : IsUnitFactorization K S f fa ff fS) (v : HeightOneSpectrum (𝓞 K)) :
    Measurable (fSp S fS v) := by
  by_cases hv : v ∈ S
  · rw [fSp_of_mem S fS hv]
    exact (hf.2.2.1 v hv).1.continuous.measurable
  · rw [fSp_of_not_mem S fS hv]
    exact measurable_const.indicator (isOpen_localIntegralSet K v).measurableSet

end Shape

section Dichotomy

variable {S : Finset (HeightOneSpectrum (𝓞 K))} {f : Gad K → ℂ} {fa : Garch K → ℂ} {ff : Gfin K → ℂ}
  {fS : ∀ v : HeightOneSpectrum (𝓞 K), Gv (K := K) v → ℂ}

theorem glArch_conj (γ x : Gad K) :
    glArch (𝓞 K) K (x⁻¹ * γ * x) = (glArch (𝓞 K) K x)⁻¹ * glArch (𝓞 K) K γ * glArch (𝓞 K) K x := by
  rw [map_mul, map_mul, map_inv]

theorem cpt_conj (v : HeightOneSpectrum (𝓞 K)) (γ x : Gad K) :
    cpt v (x⁻¹ * γ * x) = (cpt v x)⁻¹ * cpt v γ * cpt v x := by
  rw [cpt_mul, cpt_mul, cpt_inv]

theorem exists_ne_zero_of_local (hf : IsUnitFactorization K S f fa ff fS) (γ : Gad K)
    (ha : ∃ x : Garch K, fa (x⁻¹ * glArch (𝓞 K) K γ * x) ≠ 0)
    (hS : ∀ v ∈ S, ∃ x : Gv (K := K) v, fS v (x⁻¹ * cpt v γ * x) ≠ 0)
    (hnS : ∀ v ∉ S, ∃ x : Gv (K := K) v, x⁻¹ * cpt v γ * x ∈ localIntegralSet K v) :
    ∃ x : Gad K, f (x⁻¹ * γ * x) ≠ 0 := by
  obtain ⟨xa, hxa⟩ := ha
  have hloc : ∀ v : HeightOneSpectrum (𝓞 K), ∃ x : Gv (K := K) v,
      (v ∈ S → fS v (x⁻¹ * cpt v γ * x) ≠ 0) ∧ (v ∉ S → x⁻¹ * cpt v γ * x ∈ localIntegralSet K v) := by
    intro v
    by_cases hv : v ∈ S
    · obtain ⟨x, hx⟩ := hS v hv
      exact ⟨x, fun _ => hx, fun h => absurd hv h⟩
    · obtain ⟨x, hx⟩ := hnS v hv
      exact ⟨x, fun h => absurd h hv, fun _ => hx⟩
  choose xv hxvS hxvnS using hloc
  set B : Finset (HeightOneSpectrum (𝓞 K)) := S ∪ (finite_setOf_cpt_not_mem γ).toFinset with hB
  set x : Gad K := fromLoc B (xa, fun v => xv v.1) with hx
  have hxa' : glArch (𝓞 K) K x = xa := glArch_fromLoc B _
  have hxB : ∀ v ∈ B, cpt v x = xv v := fun v hv => cpt_fromLoc_of_mem B _ hv
  have hxnB : ∀ v ∉ B, cpt v x = 1 := fun v hv => cpt_fromLoc_of_not_mem B _ hv
  have hγint : ∀ v ∉ B, cpt v γ ∈ localIntegralSet K v := by
    intro v hv
    by_contra h
    exact hv (Finset.mem_union_right _ ((Set.Finite.mem_toFinset _).2 h))
  refine ⟨x, ?_⟩
  have hint : ∀ v ∉ S, cpt v (x⁻¹ * γ * x) ∈ localIntegralSet K v := by
    intro v hv
    rw [cpt_conj]
    by_cases hvB : v ∈ B
    · rw [hxB v hvB]; exact hxvnS v hv
    · rw [hxnB v hvB, inv_one, one_mul, mul_one]; exact hγint v hvB
  rw [hf.2.2.2.2.2, hf.2.2.2.1 _ hint, glArch_conj, hxa']
  refine mul_ne_zero hxa (Finset.prod_ne_zero_iff.2 fun v hv => ?_)
  show fS v (cpt v (x⁻¹ * γ * x)) ≠ 0
  rw [cpt_conj, hxB v (Finset.mem_union_left _ hv)]
  exact hxvS v hv

end Dichotomy

section Euler

variable (μ : Measure (Gad K)) [IsHaarMeasure μ] (ν : Measure (Garch K)) (cG : ℝ)
  (hG : ∀ (S : Finset (HeightOneSpectrum (𝓞 K))) (f : Gad K → ℂ) (fa : Garch K → ℂ)
      (fS : ∀ v : HeightOneSpectrum (𝓞 K), Gv (K := K) v → ℂ),
      AEStronglyMeasurable fa ν → (∀ v ∈ S, AEStronglyMeasurable (fS v) (localHaar K v)) →
      (∀ g : Gad K, (∀ v ∉ S, cpt v g ∈ localIntegralSet K v) → f g = fa (glArch (𝓞 K) K g) * ∏ v ∈ S, fS v (cpt v g)) →
      (∀ g : Gad K, (∃ v ∉ S, cpt v g ∉ localIntegralSet K v) → f g = 0) →
        ∫ g, f g ∂μ = cG * (∫ x, fa x ∂ν) * ∏ v ∈ S, ∫ y, fS v y ∂(localHaar K v))
  (γ : Gad K) (hγ : IsRegularSemisimple γ)

abbrev Tad : Subgroup (Gad K) := Subgroup.centralizer ({γ} : Set (Gad K))
abbrev Ta : Subgroup (Garch K) := Subgroup.centralizer ({glArch (𝓞 K) K γ} : Set (Garch K))
abbrev Tv (v : HeightOneSpectrum (𝓞 K)) : Subgroup (Gv (K := K) v) := localCentralizer K v (cpt v γ)

variable (τ : Measure (Tad γ)) [IsHaarMeasure τ] (τa : Measure (Ta γ)) [IsHaarMeasure τa]
  (τf : ∀ v : HeightOneSpectrum (𝓞 K), Measure (Tv γ v)) (hτf : ∀ v, IsHaarMeasure (τf v))
  (hτf1 : ∀ v, τf v (Subtype.val ⁻¹' localIntegralSet K v) = 1)
  (cT : ℝ) (hcT : 0 < cT)
  (hT : ∀ (S : Finset (HeightOneSpectrum (𝓞 K))) (W : Gad K → ℂ) (Wa : Garch K → ℂ)
      (WS : ∀ v : HeightOneSpectrum (𝓞 K), Gv (K := K) v → ℂ),
      AEStronglyMeasurable (fun t : Ta γ => Wa t) τa →
      (∀ v ∈ S, AEStronglyMeasurable (fun t : Tv γ v => WS v t) (τf v)) →
      (∀ t : Tad γ, (∀ v ∉ S, cpt v (t : Gad K) ∈ localIntegralSet K v) →
          W t = Wa (glArch (𝓞 K) K (t : Gad K)) * ∏ v ∈ S, WS v (cpt v (t : Gad K))) →
      (∀ t : Tad γ, (∃ v ∉ S, cpt v (t : Gad K) ∉ localIntegralSet K v) → W t = 0) →
        ∫ t, W t ∂τ = cT * (∫ t, Wa t ∂τa) * ∏ v ∈ S, ∫ t, WS v t ∂(τf v))
  (S : Finset (HeightOneSpectrum (𝓞 K))) (f : Gad K → ℂ) (fa : Garch K → ℂ) (ff : Gfin K → ℂ)
  (fS : ∀ v : HeightOneSpectrum (𝓞 K), Gv (K := K) v → ℂ) (hf : IsUnitFactorization K S f fa ff fS)

include hγ in

theorem exists_local_sectionFn (v : HeightOneSpectrum (𝓞 K)) [IsHaarMeasure (τf v)]
    (g : Gv (K := K) v → ℂ) (C : Set (Gv (K := K) v)) (hC : IsCompact C)
    (hE : {y : Gv (K := K) v | g (y⁻¹ * cpt v γ * y) ≠ 0} ⊆ (Tv γ v : Set (Gv (K := K) v)) * C) :
    ∃ w : Gv (K := K) v → ℝ, IsSectionFn K v (cpt v γ) (τf v) g w := by
  have hcomm : ∀ s t : Tv γ v, s * t = t * s := fun s t =>
    Subtype.ext (mul_comm_of_mem_centralizer (isRegularSemisimple_map _ (isRegularSemisimple_map _ hγ)) s.2 t.2)
  haveI : (τf v).IsMulRightInvariant := isMulRightInvariant_of_comm _ hcomm (τf v)
  obtain ⟨w, hw0, hwm, hws, hw1⟩ :=
    MeasureTheory.exists_hasCompactSupport_integral_subgroup_translate_eq_one_of_subset_mul
      (Tv γ v) (isClosed_centralizer _) (τf v) hC hE
  exact ⟨w, hw0, hwm, hws, fun x hx => hw1 x hx⟩

include hγ in
theorem exists_arch_sectionFn (C : Set (Garch K)) (hC : IsCompact C)
    (hE : {y : Garch K | fa (y⁻¹ * glArch (𝓞 K) K γ * y) ≠ 0} ⊆ (Ta γ : Set (Garch K)) * C) :
    ∃ w : Garch K → ℝ, IsSectionFnOn (InfiniteAdeleRing K) (glArch (𝓞 K) K γ) τa fa w := by
  have hcomm : ∀ s t : Ta γ, s * t = t * s := fun s t =>
    Subtype.ext (mul_comm_of_mem_centralizer (isRegularSemisimple_map _ hγ) s.2 t.2)
  haveI : τa.IsMulRightInvariant := isMulRightInvariant_of_comm _ hcomm τa
  obtain ⟨w, hw0, hwm, hws, hw1⟩ :=
    MeasureTheory.exists_hasCompactSupport_integral_subgroup_translate_eq_one_of_subset_mul
      (Ta γ) (isClosed_centralizer _) τa hC hE
  exact ⟨w, hw0, hwm, hws, fun x hx => hw1 x hx⟩

theorem unit_orbitalIntegral (v : HeightOneSpectrum (𝓞 K)) (hγv : cpt v γ ∈ localIntegralSet K v)
    (hunit : IsSectionFnOn (v.adicCompletion K) (cpt v γ) (τf v)
      ((localIntegralSet K v).indicator fun _ => (1 : ℂ)) ((localIntegralSet K v).indicator fun _ => (1 : ℝ))) :
    IsOrbitalIntegral K v (cpt v γ) (τf v) ((localIntegralSet K v).indicator fun _ => (1 : ℂ)) 1 := by
  refine ⟨(localIntegralSet K v).indicator fun _ => (1 : ℝ), hunit, ?_⟩
  have h : (fun x : Gv (K := K) v => (localIntegralSet K v).indicator (fun _ => (1 : ℂ)) (x⁻¹ * cpt v γ * x) *
      (((localIntegralSet K v).indicator (fun _ => (1 : ℝ)) x : ℝ) : ℂ)) =
      (localIntegralSet K v).indicator fun _ => (1 : ℂ) := by
    funext x
    by_cases hx : x ∈ localIntegralSet K v
    · have hc : x⁻¹ * cpt v γ * x ∈ localIntegralSet K v :=
        mul_mem_localIntegralSet v (mul_mem_localIntegralSet v (inv_mem_localIntegralSet v hx) hγv) hx
      simp only [Set.indicator_of_mem hx, Set.indicator_of_mem hc, Complex.ofReal_one, mul_one]
    · simp only [Set.indicator_of_notMem hx, Complex.ofReal_zero, mul_zero]
  show (1 : ℂ) = ∫ x, (localIntegralSet K v).indicator (fun _ => (1 : ℂ)) (x⁻¹ * cpt v γ * x) *
      (((localIntegralSet K v).indicator (fun _ => (1 : ℝ)) x : ℝ) : ℂ) ∂(localHaar K v)
  rw [h, integral_indicator_const _ (isOpen_localIntegralSet K v).measurableSet, Measure.real,
    localHaar_localIntegralSet]
  simp

omit [IsHaarMeasure μ] [IsHaarMeasure τa] in
include hG hf in

theorem euler_core (S₁ : Finset (HeightOneSpectrum (𝓞 K))) (hSS₁ : S ⊆ S₁)
    (hγint₁ : ∀ v ∉ S₁, cpt v γ ∈ localIntegralSet K v)
    (wa : Garch K → ℝ) (hwa : IsSectionFnOn (InfiniteAdeleRing K) (glArch (𝓞 K) K γ) τa fa wa)
    (wf : ∀ v : HeightOneSpectrum (𝓞 K), Gv (K := K) v → ℝ)
    (hwf : ∀ v ∈ S₁, IsSectionFn K v (cpt v γ) (τf v) (fSp S fS v) (wf v))
    (hunit : ∀ v ∉ S₁, IsSectionFnOn (v.adicCompletion K) (cpt v γ) (τf v)
      ((localIntegralSet K v).indicator fun _ => (1 : ℂ)) ((localIntegralSet K v).indicator fun _ => (1 : ℝ)))
    (wt : Gad K → ℝ)
    (hwt : wt = {x : Gad K | ∀ v ∉ S₁, cpt v x ∈ localIntegralSet K v}.indicator
      fun x => cT⁻¹ * (wa (glArch (𝓞 K) K x) * ∏ v ∈ S₁, wf v (cpt v x)))
    (I : ℂ) (hIt : I = ∫ x, f (x⁻¹ * γ * x) * (wt x : ℂ) ∂μ) :
    ∃ (Ia : ℂ) (Iv : HeightOneSpectrum (𝓞 K) → ℂ),
      IsOrbitalIntegralOn (InfiniteAdeleRing K) ν (glArch (𝓞 K) K γ) τa fa Ia ∧
      (∀ v, IsOrbitalIntegral K v (cpt v γ) (τf v) (fSp S fS v) (Iv v)) ∧
      ∀ T : Finset (HeightOneSpectrum (𝓞 K)), S₁ ⊆ T → I = cG * cT⁻¹ * Ia * ∏ v ∈ T, Iv v := by

  obtain ⟨F, hF⟩ : ∃ F : Gad K → ℂ, F = fun x => f (x⁻¹ * γ * x) * (wt x : ℂ) := ⟨_, rfl⟩
  obtain ⟨Fa, hFa⟩ : ∃ Fa : Garch K → ℂ,
      Fa = fun x => ((cT⁻¹ : ℝ) : ℂ) * (fa (x⁻¹ * glArch (𝓞 K) K γ * x) * (wa x : ℂ)) := ⟨_, rfl⟩
  obtain ⟨Fv, hFv⟩ : ∃ Fv : ∀ v : HeightOneSpectrum (𝓞 K), Gv (K := K) v → ℂ,
      Fv = fun v x => fSp S fS v (x⁻¹ * cpt v γ * x) * (wf v x : ℂ) := ⟨_, rfl⟩
  have hFshape : ∀ x : Gad K, (∀ v ∉ S₁, cpt v x ∈ localIntegralSet K v) →
      F x = Fa (glArch (𝓞 K) K x) * ∏ v ∈ S₁, Fv v (cpt v x) := by
    intro x hx
    have hcx : ∀ v ∉ S₁, cpt v (x⁻¹ * γ * x) ∈ localIntegralSet K v := by
      intro v hv
      rw [cpt_conj]
      exact mul_mem_localIntegralSet v (mul_mem_localIntegralSet v (inv_mem_localIntegralSet v (hx v hv))
        (hγint₁ v hv)) (hx v hv)
    have hwtx : wt x = cT⁻¹ * (wa (glArch (𝓞 K) K x) * ∏ v ∈ S₁, wf v (cpt v x)) := by
      rw [hwt, Set.indicator_of_mem (show x ∈ {x : Gad K | ∀ v ∉ S₁, cpt v x ∈ localIntegralSet K v} from hx)]
    rw [hF, hFa, hFv]
    dsimp only
    rw [shape_of_subset hf hSS₁ _ hcx, hwtx, glArch_conj]
    simp only [cpt_conj]
    push_cast
    rw [Finset.prod_mul_distrib]
    ring
  have hFvanish : ∀ x : Gad K, (∃ v ∉ S₁, cpt v x ∉ localIntegralSet K v) → F x = 0 := by
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
    exact measurable_const.mul ((((IsArchTestFactor.continuous hf.1).comp (continuous_conj _)).measurable).mul
      (Complex.measurable_ofReal.comp hwa.2.1))
  have hFv_meas : ∀ v ∈ S₁, AEStronglyMeasurable (Fv v) (localHaar K v) := by
    intro v hv
    rw [hFv]
    refine (Measurable.aestronglyMeasurable ?_)
    exact ((measurable_fSp hf v).comp (continuous_conj _).measurable).mul (Complex.measurable_ofReal.comp (hwf v hv).2.1)

  have hEuler := hG S₁ F Fa Fv hFa_meas hFv_meas hFshape hFvanish

  obtain ⟨Ia, hIa⟩ : ∃ Ia : ℂ, Ia = ∫ x, fa (x⁻¹ * glArch (𝓞 K) K γ * x) * (wa x : ℂ) ∂ν := ⟨_, rfl⟩
  obtain ⟨Iv, hIv⟩ : ∃ Iv : HeightOneSpectrum (𝓞 K) → ℂ,
      Iv = fun v => if v ∈ S₁ then ∫ y, Fv v y ∂(localHaar K v) else 1 := ⟨_, rfl⟩
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
      rw [if_neg hv, fSp_of_not_mem S fS (fun h => hv (hSS₁ h))]
      exact unit_orbitalIntegral γ τf v (hγint₁ v hv) (hunit v hv)
  · have hprod : ∏ v ∈ T, Iv v = ∏ v ∈ S₁, ∫ y, Fv v y ∂(localHaar K v) := by
      rw [← Finset.prod_subset hT₁ (fun v _ hv => by rw [hIv]; dsimp only; rw [if_neg hv])]
      exact Finset.prod_congr rfl fun v hv => by rw [hIv]; dsimp only; rw [if_pos hv]
    have hIF : I = ∫ x, F x ∂μ := by rw [hIt, hF]
    rw [hprod, hIF, hEuler, hIa']
    push_cast
    ring

include hG hγ hτf hτf1 hcT hT hf in

theorem euler (I : ℂ) (hI : IsOrbitalIntegralOn (AdeleRing (𝓞 K) K) μ γ τ f I)
    (hne : ∃ x : Gad K, f (x⁻¹ * γ * x) ≠ 0) :
    ∃ S₁ : Finset (HeightOneSpectrum (𝓞 K)), S ⊆ S₁ ∧
      ∃ (Ia : ℂ) (Iv : HeightOneSpectrum (𝓞 K) → ℂ),
        IsOrbitalIntegralOn (InfiniteAdeleRing K) ν (glArch (𝓞 K) K γ) τa fa Ia ∧
        (∀ v, IsOrbitalIntegral K v (cpt v γ) (τf v) (fSp S fS v) (Iv v)) ∧
        ∀ T : Finset (HeightOneSpectrum (𝓞 K)), S₁ ⊆ T → I = cG * cT⁻¹ * Ia * ∏ v ∈ T, Iv v := by
  haveI := hτf
  haveI : SecondCountableTopology (AdeleRing (𝓞 K) K) := NumberField.AdeleRing.secondCountableTopology K

  obtain ⟨S₀, hS₀⟩ : ∃ S₀ : Finset (HeightOneSpectrum (𝓞 K)), S₀ = S ∪ (finite_setOf_cpt_not_mem γ).toFinset :=
    ⟨_, rfl⟩
  have hSS₀ : S ⊆ S₀ := by rw [hS₀]; exact Finset.subset_union_left
  have hγint : ∀ v ∉ S₀, cpt v γ ∈ localIntegralSet K v := by
    intro v hv
    by_contra h
    exact hv (by rw [hS₀]; exact Finset.mem_union_right _ ((Set.Finite.mem_toFinset _).2 h))

  obtain ⟨w, hw, hIw⟩ := hI

  obtain ⟨⟨S₁, hS₀S₁, hunit⟩, hcpS, hcpnS, hcpa⟩ :=
    AutomorphicForm.exists_finset_forall_isSectionFnOn_indicator_localIntegralSet_of_isSectionFnOn_adeleRing K γ hγ
      τ τf (fun v => inferInstance) hτf1 S₀ f fa (fSp S fS)
      (fun g hg => shape_of_subset hf hSS₀ g hg) (fun g hg => vanish_of_subset hf hSS₀ g hg) ⟨w, hw⟩ hne
  have hSS₁ : S ⊆ S₁ := hSS₀.trans hS₀S₁
  have hγint₁ : ∀ v ∉ S₁, cpt v γ ∈ localIntegralSet K v := fun v hv => hγint v fun h => hv (hS₀S₁ h)

  have hloc : ∀ v : HeightOneSpectrum (𝓞 K), ∃ wv : Gv (K := K) v → ℝ,
      v ∈ S₁ → IsSectionFn K v (cpt v γ) (τf v) (fSp S fS v) wv := by
    intro v
    by_cases hv : v ∈ S₁
    · by_cases hv₀ : v ∈ S₀
      · obtain ⟨C, hC, hE⟩ := hcpS v hv₀
        obtain ⟨wv, hwv⟩ := exists_local_sectionFn γ hγ τf v (fSp S fS v) C hC hE
        exact ⟨wv, fun _ => hwv⟩
      · obtain ⟨C, hC, hE⟩ := hcpnS v hv₀
        have hE' : {y : Gv (K := K) v | fSp S fS v (y⁻¹ * cpt v γ * y) ≠ 0} ⊆ (Tv γ v : Set (Gv (K := K) v)) * C := by
          intro y hy
          apply hE
          rw [Set.mem_setOf_eq, fSp_of_not_mem S fS (fun h => hv₀ (hSS₀ h))] at hy
          simpa [Set.indicator_apply_ne_zero] using hy
        obtain ⟨wv, hwv⟩ := exists_local_sectionFn γ hγ τf v (fSp S fS v) C hC hE'
        exact ⟨wv, fun _ => hwv⟩
    · exact ⟨fun _ => 0, fun h => absurd h hv⟩
  choose wf hwf using hloc

  obtain ⟨Ca, hCa, hEa⟩ := hcpa
  obtain ⟨wa, hwa⟩ := exists_arch_sectionFn γ hγ τa fa Ca hCa hEa

  have hsec := AutomorphicForm.isSectionFnOn_adeleRing_indicator_prod_of_forall_isSectionFnOn K γ τ τa τf cT hcT
    hT S₁ f fa (fSp S fS) (fun g hg => shape_of_subset hf hSS₁ g hg) (fun g hg => vanish_of_subset hf hSS₁ g hg)
    wa hwa wf (fun v hv => hwf v hv) (fun v hv => hunit v hv)
  obtain ⟨wt, hwt⟩ : ∃ wt : Gad K → ℝ, wt = {x : Gad K | ∀ v ∉ S₁, cpt v x ∈ localIntegralSet K v}.indicator
    fun x => cT⁻¹ * (wa (glArch (𝓞 K) K x) * ∏ v ∈ S₁, wf v (cpt v x)) := ⟨_, rfl⟩
  rw [← hwt] at hsec

  have hIt : I = ∫ x, f (x⁻¹ * γ * x) * (wt x : ℂ) ∂μ :=
    AutomorphicForm.IsOrbitalIntegralOn.unique_of_isRegularSemisimple (AdeleRing (𝓞 K) K) μ inferInstance γ hγ τ
      inferInstance f (continuous_of_isUnitFactorization hf).measurable (bounded_of_isUnitFactorization hf)
      ⟨w, hw, hIw⟩ ⟨wt, hsec, rfl⟩
  obtain ⟨Ia, Iv, h1, h2, h3⟩ := euler_core μ ν cG hG γ τa τf cT S f fa ff fS hf S₁ hSS₁ hγint₁ wa hwa wf hwf hunit
    wt hwt I hIt
  exact ⟨S₁, hSS₁, Ia, Iv, h1, h2, h3⟩

end Euler

end AutomorphicForm.AdelicOrbitalEuler
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isOrbitalIntegralOn_adeleRing_eq_mul_prod_of_isUnitFactorization.AutomorphicForm P2MW.S_AutomorphicForm_exists_isOrbitalIntegralOn_adeleRing_eq_mul_prod_of_isUnitFactorization.AutomorphicForm.AdelicOrbitalEuler"
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isOrbitalIntegralOn_adeleRing_eq_mul_prod_of_isUnitFactorization.AutomorphicForm"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_isOrbitalIntegralOn_adeleRing_eq_mul_prod_of_isUnitFactorization.AutomorphicForm P2MW.S_AutomorphicForm_exists_isOrbitalIntegralOn_adeleRing_eq_mul_prod_of_isUnitFactorization.AutomorphicForm.AdelicOrbitalEuler"

open _root_.AutomorphicForm _root_.P2MW.S_AutomorphicForm_exists_isOrbitalIntegralOn_adeleRing_eq_mul_prod_of_isUnitFactorization.AutomorphicForm AutomorphicForm.AdelicOrbitalEuler in
theorem solution
    (K : Type) [Field K] [NumberField K]
    (μ : @Measure (GL (Fin 2) (AdeleRing (𝓞 K) K)) (glBorel (Fin 2) (𝓞 K) K))
    (hμ : @Measure.IsHaarMeasure (GL (Fin 2) (AdeleRing (𝓞 K) K)) _ _ (glBorel (Fin 2) (𝓞 K) K) μ)
    (ν : @Measure (GL (Fin 2) (InfiniteAdeleRing K)) (AutomorphicForm.glBorelOf (InfiniteAdeleRing K)))
    (cG : ℝ)
    (hG : ∀ (S : Finset (HeightOneSpectrum (𝓞 K)))
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
          ∫ g, f g ∂μ = cG * (∫ x, fa x ∂ν) * ∏ v ∈ S, ∫ y, fS v y ∂(AutomorphicForm.localHaar K v))
    (γ : GL (Fin 2) (AdeleRing (𝓞 K) K)) (hγ : AutomorphicForm.IsRegularSemisimple γ)
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
      τf v (Subtype.val ⁻¹' AutomorphicForm.localIntegralSet K v) = 1)
    (cT : ℝ) (hcT : 0 < cT)
    (hT : ∀ (S : Finset (HeightOneSpectrum (𝓞 K)))
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
          ∫ t, W t ∂τ = cT * (∫ t, Wa t ∂τa) * ∏ v ∈ S, ∫ t, WS v t ∂(τf v))
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) (fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)
    (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ)
    (fS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ)
    (hf : AutomorphicForm.IsUnitFactorization K S f fa ff fS)
    (I : ℂ) (hI : AutomorphicForm.IsOrbitalIntegralOn (AdeleRing (𝓞 K) K) μ γ τ f I) :
    (I = 0 ∧
      ((∀ x : GL (Fin 2) (InfiniteAdeleRing K), fa (x⁻¹ * AdelicLevel.glArch (𝓞 K) K γ * x) = 0) ∨
        (∃ v ∈ S, ∀ x : GL (Fin 2) (v.adicCompletion K),
          fS v (x⁻¹ * AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K γ) * x) = 0) ∨
        (∃ v ∉ S, ∀ x : GL (Fin 2) (v.adicCompletion K),
          x⁻¹ * AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K γ) * x ∉
            AutomorphicForm.localIntegralSet K v))) ∨
    ∃ S₁ : Finset (HeightOneSpectrum (𝓞 K)), S ⊆ S₁ ∧
      ∃ (Ia : ℂ) (Iv : HeightOneSpectrum (𝓞 K) → ℂ),
        AutomorphicForm.IsOrbitalIntegralOn (InfiniteAdeleRing K) ν (AdelicLevel.glArch (𝓞 K) K γ) τa
          fa Ia ∧
        (∀ v ∈ S, AutomorphicForm.IsOrbitalIntegral K v
          (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K γ)) (τf v) (fS v) (Iv v)) ∧
        (∀ v ∉ S, AutomorphicForm.IsOrbitalIntegral K v
          (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K γ)) (τf v)
          ((AutomorphicForm.localIntegralSet K v).indicator fun _ => (1 : ℂ)) (Iv v)) ∧
        ∀ T : Finset (HeightOneSpectrum (𝓞 K)), S₁ ⊆ T →
          I = cG * cT⁻¹ * Ia * ∏ v ∈ T, Iv v := by
  haveI := hμ; haveI := hτ; haveI := hτa
  by_cases hne : ∃ x : GL (Fin 2) (AdeleRing (𝓞 K) K), f (x⁻¹ * γ * x) ≠ 0
  · right
    obtain ⟨S₁, hSS₁, Ia, Iv, hIa, hIv, hIeq⟩ :=
      euler μ ν cG hG γ hγ τ τa τf hτf hτf1 cT hcT hT S f fa ff fS hf I hI hne
    refine ⟨S₁, hSS₁, Ia, Iv, hIa, fun v hv => ?_, fun v hv => ?_, hIeq⟩
    · have h := hIv v
      rwa [fSp_of_mem S fS hv] at h
    · have h := hIv v
      rwa [fSp_of_not_mem S fS hv] at h
  · left
    refine ⟨?_, ?_⟩
    · obtain ⟨w, -, rfl⟩ := hI
      push Not at hne
      simp [hne]
    · by_contra hcon
      push Not at hcon
      obtain ⟨ha, hS, hnS⟩ := hcon
      exact hne (exists_ne_zero_of_local hf γ ha hS hnS)

end S_AutomorphicForm_exists_isOrbitalIntegralOn_adeleRing_eq_mul_prod_of_isUnitFactorization
end P2MW
export P2MW.S_AutomorphicForm_exists_isOrbitalIntegralOn_adeleRing_eq_mul_prod_of_isUnitFactorization (solution)
