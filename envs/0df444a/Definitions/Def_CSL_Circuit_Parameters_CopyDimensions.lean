-- Prove2me | Definitions.Def_CSL_Circuit_Parameters_CopyDimensions
-- name    : CSL_Circuit_Parameters_CopyDimensions
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T12:51:29.908833+00:00
-- url     : https://prove2.me/theorems/6108508d-345a-415f-b6e6-c171b0289faf
-- title:
--   Coded sorting library: Circuit / Parameters / CopyDimensions
-- statement:
--   Module `CodedSorting.Circuit.Parameters.CopyDimensions` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Circuit.Parameters.CopyDimensions

import Definitions.Def_CSL_Compat
import Definitions.Def_CSL_Generated_FiniteCircuit_ArrayLookup

namespace CSL.Construction
open FiniteCertificate

theorem actualCopyDimensions (t : Fin 9) : projections[510+t.val]!.dimension = 7 := by
  have ht := t.isLt
  rcases (show t.val = 0 ∨ t.val = 1 ∨ t.val = 2 ∨ t.val = 3 ∨
    t.val = 4 ∨ t.val = 5 ∨ t.val = 6 ∨ t.val = 7 ∨ t.val = 8 by omega) with
    h | h | h | h | h | h | h | h | h <;>
    rw [h, projections_lookup] <;> rfl

#print axioms actualCopyDimensions
end CSL.Construction


