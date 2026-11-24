-- Prove2me | Definitions.Def_CSL_Circuit_Local_SSAComposition
-- name    : CSL_Circuit_Local_SSAComposition
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T12:44:03.052302+00:00
-- url     : https://prove2.me/theorems/69aa3cae-045e-4069-b951-ca508c4dabed
-- title:
--   Coded sorting library: Circuit / Local / SSAComposition
-- statement:
--   Module `CodedSorting.Circuit.Local.SSAComposition` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Circuit.Local.SSAComposition

import Definitions.Def_CSL_Compat
import Definitions.Def_CSL_Circuit_Local_SSAFunctionCertificate

namespace CSL.Construction.FiniteSSA.Verified
open CSL.Construction.SSAFunctionCertificate
set_option autoImplicit false

def WellFormed (e : Step) : Prop :=
  e.gate.destination < 661 ∧ (∀ s ∈ e.gate.sources, s < 661) ∧
    e.gate.sources.Nodup ∧ e.gate.destination ∉ e.gate.sources

theorem wellFormed_of_checks (es : List Step)
    (bounds : es.all (fun e => e.gate.destination < 661 &&
      e.gate.sources.all (fun s => s < 661)) = true)
    (nodup : ∀ e ∈ es, e.gate.sources.Nodup)
    (noSelf : es.all (fun e => !e.gate.sources.contains e.gate.destination) = true) :
    ∀ e ∈ es, WellFormed e := by
  intro e he
  have hb := (List.all_eq_true.mp bounds) e he
  have hn := (List.all_eq_true.mp noSelf) e he
  have hb' : e.gate.destination < 661 ∧ (∀ s ∈ e.gate.sources, s < 661) := by
    simpa only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] using hb
  exact ⟨hb'.1, hb'.2, nodup e he, by simpa using hn⟩

theorem wellFormed_append (a b : List Step)
    (ha : ∀ e ∈ a, WellFormed e) (hb : ∀ e ∈ b, WellFormed e) :
    ∀ e ∈ a ++ b, WellFormed e := by
  intro e he
  rcases List.mem_append.mp he with he | he
  · exact ha e he
  · exact hb e he

end CSL.Construction.FiniteSSA.Verified

#print axioms CSL.Construction.FiniteSSA.Verified.wellFormed_of_checks
#print axioms CSL.Construction.FiniteSSA.Verified.wellFormed_append


