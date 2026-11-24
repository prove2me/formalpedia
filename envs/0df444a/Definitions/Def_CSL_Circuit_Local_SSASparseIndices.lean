-- Prove2me | Definitions.Def_CSL_Circuit_Local_SSASparseIndices
-- name    : CSL_Circuit_Local_SSASparseIndices
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T12:44:12.596081+00:00
-- url     : https://prove2.me/theorems/1cb0922a-6936-417b-88ff-e87be10798f4
-- title:
--   Coded sorting library: Circuit / Local / SSASparseIndices
-- statement:
--   Module `CodedSorting.Circuit.Local.SSASparseIndices` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   Check changed register indices; reuse one proof for every untouched register.
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Circuit.Local.SSASparseIndices

import Definitions.Def_CSL_Compat
import Definitions.Def_CSL_Circuit_Local_SSAFunctionCertificate

/-! Check changed register indices; reuse one proof for every untouched register. -/
namespace CSL.Construction.SSAFunctionCertificate

def writtenRegisters (es : List Step) : List Nat :=
  es.map (fun e => e.gate.destination)

theorem runIds_unchanged (es : List Step) (ids : Nat → Nat) (r : Nat)
    (h : r ∉ writtenRegisters es) : runIds es ids r = ids r := by
  induction es generalizing ids with
  | nil => rfl
  | cons e es ih =>
    have hne : r ≠ e.gate.destination := by
      intro he
      exact h (by simp [writtenRegisters, he])
    have htail : r ∉ writtenRegisters es := by
      intro hr
      exact h (by simpa only [writtenRegisters, List.map_cons, List.mem_cons] using Or.inr hr)
    change runIds es (stepIds ids e) r = ids r
    rw [ih _ htail]
    simp only [stepIds, if_neg hne]

theorem runIds_eq_of_sparse (es : List Step) (before after : Nat → Nat) (n : Nat)
    (hchanged : ∀ r ∈ writtenRegisters es, runIds es before r = after r)
    (houtside : ∀ r : Fin n, before r.val = after r.val ∨ r.val ∈ writtenRegisters es) :
    ∀ r : Fin n, runIds es before r.val = after r.val := by
  intro r
  by_cases h : r.val ∈ writtenRegisters es
  · exact hchanged r.val h
  · exact (runIds_unchanged es before r.val h).trans ((houtside r).resolve_right h)

end CSL.Construction.SSAFunctionCertificate


