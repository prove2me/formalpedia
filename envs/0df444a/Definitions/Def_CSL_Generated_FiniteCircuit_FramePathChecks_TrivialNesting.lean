-- Prove2me | Definitions.Def_CSL_Generated_FiniteCircuit_FramePathChecks_TrivialNesting
-- name    : CSL_Generated_FiniteCircuit_FramePathChecks_TrivialNesting
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T13:55:46.72148+00:00
-- url     : https://prove2.me/theorems/6bb494cb-db23-4e4f-b901-407a08a677c8
-- title:
--   Coded sorting library: Generated / FiniteCircuit / FramePathChecks / TrivialNesting
-- statement:
--   Module `CodedSorting.Generated.FiniteCircuit.FramePathChecks.TrivialNesting` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   Zero and identity matrices need no instance-by-instance matrix products.
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Generated.FiniteCircuit.FramePathChecks.TrivialNesting

import Definitions.Def_CSL_Compat
import Definitions.Def_CSL_Generated_FiniteCircuit_FramePathChecks_Entries_Batch00

/-! Zero and identity matrices need no instance-by-instance matrix products. -/
namespace CSL.Construction.PhysicalFramePaths
open FiniteCertificate

theorem nestingIdentity_denominator : nestingProjection001.denominator = 1 := rfl

theorem nestingEntries_zero : nestingEntries000 = (fun _ => 0) := by
  funext n
  simp [nestingEntries000]

theorem nestingIdentity_entries (n : Nat) :
    nestingProjection001.numerator[n]! = identityEntries n := by
  apply entries_of_check _ _ (by rfl) (by decide)
  intro n hn
  have h : n / 8 ≠ n % 8 := by omega
  simp [identityEntries, h]

end CSL.Construction.PhysicalFramePaths


