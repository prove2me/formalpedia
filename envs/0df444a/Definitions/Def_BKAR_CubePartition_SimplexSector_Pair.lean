-- Prove2me | Definitions.Def_BKAR_CubePartition_SimplexSector_Pair
-- name    : BKAR_CubePartition_SimplexSector_Pair
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T08:57:18.133401+00:00
-- url     : https://prove2.me/theorems/08fcf752-d954-5c94-b8e1-67685bb4c640
-- title:
--   Pair
-- statement:
--   Definitions and structural lemmas for Pair, from Scott Armstrong (scottnarmstrong/BKARForestFormula; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned BKAR forest interpolation formula development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/SimplexSector/Pair.lean

import Definitions.Def_BKAR_CubePartition_SimplexSector_Equiv
import Theorems.Thm_BKAR_ForestIndex_ext
import Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegralAux_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegral_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegrand_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_derivativeOrder_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_params_cons_cons
import Theorems.Thm_BKAR_Forest_OrderedGrowth_params_cons_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_params_nil
import Theorems.Thm_BKAR_Forest_edgeParamFinEquivOfOrder_apply_val
import Theorems.Thm_BKAR_Forest_emptyActiveEdge_val
import Theorems.Thm_BKAR_Forest_nodup_of_mem_edgeOrders
import Theorems.Thm_BKAR_Forest_paramValue_of_mem
import Theorems.Thm_BKAR_Forest_pathMin_cons
import Theorems.Thm_BKAR_Forest_pathMin_nil
import Theorems.Thm_BKAR_Forest_toFinset_eq_of_mem_edgeOrders
import Theorems.Thm_BKAR_edgeBasis_self
import Theorems.Thm_BKAR_mixedPartialList_cons
import Theorems.Thm_BKAR_mixedPartialList_cons_apply
import Theorems.Thm_BKAR_mixedPartialList_nil
import Theorems.Thm_BKAR_mixedPartialList_nil_apply
import Theorems.Thm_BKAR_orderedSimplexIntegralAux_cons
import Theorems.Thm_BKAR_orderedSimplexIntegralAux_nil
import Theorems.Thm_BKAR_orderedSimplexIntegral_cons
import Theorems.Thm_BKAR_orderedSimplexIntegral_nil
import Theorems.Thm_BKAR_orderedSimplexParams_cons
import Theorems.Thm_BKAR_orderedSimplexParams_nil
import Theorems.Thm_BKAR_updateCoord_same_value
import Theorems.Thm_BKAR_updateCoord_self
import Theorems.Thm_BKAR_updateCoord_update_same
attribute [local simp] BKAR.Forest.OrderedGrowth.branchIntegralAux_nil
attribute [local simp] BKAR.Forest.OrderedGrowth.branchIntegral_nil
attribute [local simp] BKAR.Forest.OrderedGrowth.branchIntegrand_nil
attribute [local simp] BKAR.Forest.OrderedGrowth.derivativeOrder_nil
attribute [local simp] BKAR.Forest.OrderedGrowth.params_cons_cons
attribute [local simp] BKAR.Forest.OrderedGrowth.params_cons_nil
attribute [local simp] BKAR.Forest.OrderedGrowth.params_nil
attribute [local simp] BKAR.Forest.edgeParamFinEquivOfOrder_apply_val
attribute [local simp] BKAR.Forest.emptyActiveEdge_val
attribute [local simp] BKAR.Forest.paramValue_of_mem
attribute [local simp] BKAR.Forest.pathMin_cons
attribute [local simp] BKAR.Forest.pathMin_nil
attribute [local simp] BKAR.edgeBasis_self
attribute [local simp] BKAR.mixedPartialList_cons
attribute [local simp] BKAR.mixedPartialList_cons_apply
attribute [local simp] BKAR.mixedPartialList_nil
attribute [local simp] BKAR.mixedPartialList_nil_apply
attribute [local simp] BKAR.orderedSimplexIntegralAux_cons
attribute [local simp] BKAR.orderedSimplexIntegralAux_nil
attribute [local simp] BKAR.orderedSimplexIntegral_cons
attribute [local simp] BKAR.orderedSimplexIntegral_nil
attribute [local simp] BKAR.orderedSimplexParams_cons
attribute [local simp] BKAR.orderedSimplexParams_nil
attribute [local simp] BKAR.updateCoord_same_value
attribute [local simp] BKAR.updateCoord_self
attribute [local simp] BKAR.updateCoord_update_same


set_option autoImplicit false
noncomputable section
namespace BKAR
namespace Forest
open MeasureTheory
variable {V : Type*} [Fintype V] [DecidableEq V]
theorem edges_eq_pair_of_pair_mem_edgeOrders
    (F : Forest V) {e₁ e₂ : Edge V} (horder : [e₁, e₂] ∈ F.edgeOrders) :
    F.edges = ({e₁, e₂} : Finset (Edge V)) := by
  have hset := F.toFinset_eq_of_mem_edgeOrders horder
  simpa using hset.symm
theorem ne_of_pair_mem_edgeOrders
    (F : Forest V) {e₁ e₂ : Edge V} (horder : [e₁, e₂] ∈ F.edgeOrders) :
    e₁ ≠ e₂ := by
  have hnodup := F.nodup_of_mem_edgeOrders horder
  simpa using hnodup
theorem edgeParam_eq_left_or_right_of_edges_eq_pair
    (F : Forest V) {e₁ e₂ : Edge V}
    (hedges : F.edges = ({e₁, e₂} : Finset (Edge V)))
    (p : F.EdgeParam) :
    p.val = e₁ ∨ p.val = e₂ := by
  have hp : p.val ∈ ({e₁, e₂} : Finset (Edge V)) := by
    rw [← hedges]
    exact p.property
  simpa using hp
def pairCoordOfOrder (F : Forest V) (e₁ e₂ : Edge V)
    (u : F.EdgeParam → ℝ) : ℝ × ℝ :=
  (F.paramValue u e₁, F.paramValue u e₂)
def orderedPairSector : Set (ℝ × ℝ) :=
  {z | 0 ≤ z.1 ∧ z.1 ≤ 1 ∧ 0 ≤ z.2 ∧ z.2 ≤ 1 ∧ z.2 ≤ z.1}
def edgeParamFinTwoEquivOfPair
    (F : Forest V) {e₁ e₂ : Edge V}
    (hedges : F.edges = ({e₁, e₂} : Finset (Edge V))) (hne : e₁ ≠ e₂) :
    Fin 2 ≃ F.EdgeParam where
  toFun i :=
    if i = 0 then
      ⟨e₁, by
        rw [hedges]
        exact Finset.mem_insert_self e₁ {e₂}⟩
    else
      ⟨e₂, by
        rw [hedges]
        exact Finset.mem_insert_of_mem (Finset.mem_singleton_self e₂)⟩
  invFun p := if p.val = e₁ then 0 else 1
  left_inv := by
    intro i
    fin_cases i <;> simp [hne.symm]
  right_inv := by
    intro p
    have he₁ : e₁ ∈ F.edges := by
      rw [hedges]
      exact Finset.mem_insert_self e₁ {e₂}
    have he₂ : e₂ ∈ F.edges := by
      rw [hedges]
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self e₂)
    rcases F.edgeParam_eq_left_or_right_of_edges_eq_pair hedges p with hp | hp
    · have hp_eq : p = ⟨e₁, he₁⟩ := Subtype.ext hp
      simp [hp_eq]
    · have hp_eq : p = ⟨e₂, he₂⟩ := Subtype.ext hp
      simp [hp_eq, hne.symm]
def pairMeasurableEquivOfPair
    (F : Forest V) {e₁ e₂ : Edge V}
    (hedges : F.edges = ({e₁, e₂} : Finset (Edge V))) (hne : e₁ ≠ e₂) :
    (F.EdgeParam → ℝ) ≃ᵐ (ℝ × ℝ) :=
  ((MeasurableEquiv.piCongrLeft (fun _ : F.EdgeParam => ℝ)
    (F.edgeParamFinTwoEquivOfPair hedges hne)).symm).trans
      (@MeasurableEquiv.finTwoArrow ℝ _)
end Forest
end BKAR


