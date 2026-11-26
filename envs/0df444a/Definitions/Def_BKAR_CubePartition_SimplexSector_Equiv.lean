-- Prove2me | Definitions.Def_BKAR_CubePartition_SimplexSector_Equiv
-- name    : BKAR_CubePartition_SimplexSector_Equiv
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T08:54:27.865247+00:00
-- url     : https://prove2.me/theorems/79b98a6f-9bff-43e5-92d7-13612ead2921
-- title:
--   Equiv
-- statement:
--   Definitions and structural lemmas for Equiv, from Scott Armstrong (scottnarmstrong/BKARForestFormula; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned BKAR forest interpolation formula development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/SimplexSector/Equiv.lean

import Definitions.Def_BKAR_CubePartition_SimplexSector_Singleton
import Theorems.Thm_BKAR_ForestIndex_ext
import Theorems.Thm_BKAR_Forest_nodup_of_mem_edgeOrders
import Theorems.Thm_BKAR_Forest_toFinset_eq_of_mem_edgeOrders

set_option autoImplicit false
noncomputable section
namespace BKAR
namespace Forest
open MeasureTheory
variable {V : Type*} [Fintype V] [DecidableEq V]
def edgeParamEquivOrderSubtype
    (F : Forest V) {order : List (Edge V)} (horder : order ∈ F.edgeOrders) :
    {e : Edge V // e ∈ order} ≃ F.EdgeParam where
  toFun e :=
    ⟨e.val, by
      have hset := F.toFinset_eq_of_mem_edgeOrders horder
      rw [← hset]
      exact List.mem_toFinset.mpr e.property⟩
  invFun e :=
    ⟨e.val, by
      have hset := F.toFinset_eq_of_mem_edgeOrders horder
      have he : e.val ∈ order.toFinset := by
        rw [hset]
        exact e.property
      exact List.mem_toFinset.mp he⟩
  left_inv e := by
    exact Subtype.ext rfl
  right_inv e := by
    exact Subtype.ext rfl
def edgeParamFinEquivOfOrder
    (F : Forest V) {order : List (Edge V)} (horder : order ∈ F.edgeOrders) :
    Fin order.length ≃ F.EdgeParam :=
  (List.Nodup.getEquiv order (F.nodup_of_mem_edgeOrders horder)).trans
    (F.edgeParamEquivOrderSubtype horder)
def orderMeasurableEquivOfOrder
    (F : Forest V) {order : List (Edge V)} (horder : order ∈ F.edgeOrders) :
    (F.EdgeParam → ℝ) ≃ᵐ (Fin order.length → ℝ) :=
  (MeasurableEquiv.piCongrLeft (fun _ : F.EdgeParam => ℝ)
    (F.edgeParamFinEquivOfOrder horder)).symm
def orderedFinSimplex (n : ℕ) : Set (Fin n → ℝ) :=
  {ts | (∀ i, 0 ≤ ts i ∧ ts i ≤ 1) ∧
    OrderedSimplexParams 1 (List.ofFn ts)}
end Forest
end BKAR


