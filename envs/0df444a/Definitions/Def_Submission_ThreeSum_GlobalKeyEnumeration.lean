-- Prove2me | Definitions.Def_Submission_ThreeSum_GlobalKeyEnumeration
-- name    : Submission_ThreeSum_GlobalKeyEnumeration
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T09:05:29.259212+00:00
-- url     : https://prove2.me/theorems/0525494e-043c-4381-9259-da6bd94e63d8
-- title:
--   Global Key Enumeration
-- statement:
--   Definitions and structural lemmas for Global Key Enumeration, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/GlobalKeyEnumeration.lean

import Definitions.Def_Submission_ThreeSum_RadixKeyLists
import Definitions.Def_Submission_ThreeSum_LocalMaskGraph
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.ProdSigma
import Theorems.Thm_Light_Seg_get
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Theorems.Thm_ThreeSum_LocalMaskGraph_setAt_card
import Theorems.Thm_ThreeSum_RadixKeyLists_mem_tuples
attribute [local simp] ThreeSum.LayerCounts.mem_vertices


set_option autoImplicit false
namespace ThreeSum.GlobalKeyEnumeration
open GlobalEncoding LocalGraph LocalCoverBounds LocalHashMoments
open RadixKeyLists
open scoped BigOperators
set_option maxHeartbeats 1800000
def layerRecord (h : ℕ) (i : Fin ((512*h).choose (2*h))) :
    {Q // Q ∈ LayerCounts.vertices (512*h) (2*h)} :=
  ⟨LocalMaskGraph.setAt (512*h) (2*h) i,
    LayerCounts.mem_vertices.mpr (LocalMaskGraph.setAt_card i.isLt)⟩
def layers (h : ℕ) := List.ofFn (layerRecord h)
def localRecords (h : ℕ) : List (OutputBlock h) :=
  (List.finRange (scheduleSize h)).product (layers h)
def localKeys (h : ℕ) : List ℤ := (localRecords h).map blockKey
def tupleOfList {α : Type*} {J : ℕ} (xs : List α) (hlen : xs.length=J) : Fin J → α :=
  fun i => xs.get (Fin.cast hlen.symm i)
def globalRecords (h J : ℕ) : List (GlobalOutput h J) :=
  (tuples (localRecords h) J).attach.map fun xs =>
    tupleOfList xs.val ((mem_tuples _ _ _).mp xs.property).1
def globalKeys (h J : ℕ) : List ℤ :=
  values (localPrime h : ℤ) (localKeys h) J
end ThreeSum.GlobalKeyEnumeration


