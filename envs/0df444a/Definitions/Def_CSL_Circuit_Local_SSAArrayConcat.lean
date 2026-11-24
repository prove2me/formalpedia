-- Prove2me | Definitions.Def_CSL_Circuit_Local_SSAArrayConcat
-- name    : CSL_Circuit_Local_SSAArrayConcat
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T12:55:49.667485+00:00
-- url     : https://prove2.me/theorems/63fcc0d5-9731-4dce-805b-6393e9511951
-- title:
--   Coded sorting library: Circuit / Local / SSAArrayConcat
-- statement:
--   Module `CodedSorting.Circuit.Local.SSAArrayConcat` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Circuit.Local.SSAArrayConcat

import Definitions.Def_CSL_Compat
import Definitions.Def_CSL_Circuit_Local_SSAComposition

namespace CSL.Construction.FiniteSSA.Verified
set_option autoImplicit false

theorem concat_toList_aux {α : Type} (chunks : List (Array α)) (start : Array α) :
    (chunks.foldl (fun a b => a ++ b) start).toList =
      start.toList ++ chunks.flatMap Array.toList := by
  induction chunks generalizing start with
  | nil => simp
  | cons c cs ih =>
      simpa only [List.foldl_cons, List.flatMap_cons, Array.toList_append,
        List.append_assoc] using ih (start ++ c)

/-- Open the concatenation only at the chunk level, never reduce large
concrete chunks while binding the certified trace to the original word. -/
theorem concat_toList {α : Type} (chunks : Array (Array α)) :
    (chunks.foldl (fun a b => a ++ b) #[]).toList =
      chunks.toList.flatMap Array.toList := by
  rw [← Array.foldl_toList, concat_toList_aux]
  simp

end CSL.Construction.FiniteSSA.Verified

#print axioms CSL.Construction.FiniteSSA.Verified.concat_toList


