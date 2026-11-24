-- Prove2me | Definitions.Def_CSL_Interchange_Framework_Memory_FileTranspose
-- name    : CSL_Interchange_Framework_Memory_FileTranspose
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T12:09:22.04691+00:00
-- url     : https://prove2.me/theorems/4dc09f70-a715-415f-bf88-5a4e363084f0
-- title:
--   Coded sorting library: Interchange / Framework / Memory / FileTranspose
-- statement:
--   Module `CodedSorting.Interchange.Framework.Memory.FileTranspose` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   Reorder a rectangular on-disk directory from row/key to key/row order.
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Interchange.Framework.Memory.FileTranspose

import Definitions.Def_CSL_Compat
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Perm.Basic

/-! Reorder a rectangular on-disk directory from row/key to key/row order. -/
namespace CSL.FileTranspose
variable {α β : Type*}

def select (K : ℕ) (fallback : α) (rows : List (List α)) : List α :=
  (List.finRange K).flatMap (fun k => rows.map (fun row => row[k.val]?.getD fallback))

theorem enumerate_row (K : ℕ) (fallback : α) (row : List α) (h : row.length = K) :
    (List.finRange K).map (fun k => row[k.val]?.getD fallback) = row := by
  subst K
  calc
    (List.finRange row.length).map (fun k => row[k.val]?.getD fallback) =
        (List.finRange row.length).map (fun k => row[k.val]) := by
      apply List.map_congr_left
      intro k _
      rw [List.getElem?_eq_getElem k.isLt]
      rfl
    _ = row := List.map_getElem_finRange row

theorem select_perm (K : ℕ) (fallback : α) (rows : List (List α))
    (h : ∀ row ∈ rows, row.length = K) : (select K fallback rows).Perm rows.flatten := by
  induction rows with
  | nil => simp [select]
  | cons row rest ih =>
    have hp := List.map_append_flatMap_perm (List.finRange K)
      (fun k => row[k.val]?.getD fallback)
      (fun k => rest.map (fun row => row[k.val]?.getD fallback))
    have he := enumerate_row K fallback row (h row (by simp))
    rw [he] at hp
    change (select K fallback (row :: rest)).Perm (row ++ rest.flatten)
    exact hp.symm.trans ((ih (fun row hr => h row (by simp [hr]))).append_left row)

theorem map_select (K : ℕ) (fallback : α) (rows : List (List α)) (f : α → β) :
    (select K fallback rows).map f =
      select K (f fallback) (rows.map (List.map f)) := by
  simp [select, List.map_flatMap, List.map_map, Function.comp_def, List.getElem?_map,
    Option.getD_map]

end CSL.FileTranspose


