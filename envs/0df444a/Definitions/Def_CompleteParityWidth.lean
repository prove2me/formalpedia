-- Prove2me | Definitions.Def_CompleteParityWidth
-- name    : CompleteParityWidth
-- status  : Definition
-- author  : @Jie Luo
-- created : 2026-11-26T21:28:33.497782+00:00
-- url     : https://prove2.me/theorems/3e65f89b-3f33-4531-a9b1-9c929b89b97e
-- title:
--   Complete-graph parity CNFs with width-bounded resolution
-- statement:
--   Take two separately labelled Boolean edge variables for each pair of distinct vertices, one per orientation. Each vertex constrains the parity of the variables incident with it. Its equation is written as the CNF of all clauses excluding assignments of the wrong parity at that vertex. A width-bounded resolution derivation uses input clauses, resolution, and weakening, subject to a bound on literal count in every clause.
-- source:
--   Tseitin parity contradictions and the ordinary resolution calculus. See Ben-Sasson and Wigderson, Short Proofs Are Narrow, JACM 48(2), 2001, Section 4.1.

import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace CompleteParityWidth

open scoped BigOperators

abbrev Bit := ZMod 2
abbrev Arc (V : Type*) := V × V
abbrev Assignment (V : Type*) := Arc V → Bit
abbrev Clause (V : Type*) := Finset (Arc V × Bit)

variable {V : Type*} [Fintype V] [DecidableEq V]

def incident (v : V) (e : Arc V) : Prop := e.1 ≠ e.2 ∧ (e.1 = v ∨ e.2 = v)

instance (v : V) (e : Arc V) : Decidable (incident v e) := by
  unfold incident
  infer_instance

def Holds (x : Assignment V) (C : Clause V) : Prop :=
  ∃ p ∈ C, x p.1 = p.2

def incidentArcs (v : V) : Finset (Arc V) :=
  Finset.univ.filter (incident v)

def patternClause (v : V) (bad : ↥(incidentArcs v) → Bit) : Clause V :=
  Finset.univ.image (fun e => (e.val,bad e + 1))

def rowCNF (v : V) (target : Bit) : Finset (Clause V) :=
  (Finset.univ.filter (fun bad : ↥(incidentArcs v) → Bit => (∑ e, bad e) ≠ target)).image
    (patternClause v)

def parityCNF (charge : V → Bit) : Finset (Clause V) :=
  Finset.univ.biUnion (fun v => rowCNF v (charge v))

inductive BoundedResolution (F : Finset (Clause V)) (limit : ℕ) : Clause V → Prop
  | premise {C : Clause V} : C ∈ F → C.card ≤ limit → BoundedResolution F limit C
  | resolve {A B : Clause V} (e : Arc V) :
      BoundedResolution F limit A → BoundedResolution F limit B →
      ((A.erase (e,0)) ∪ (B.erase (e,1))).card ≤ limit →
      BoundedResolution F limit ((A.erase (e,0)) ∪ (B.erase (e,1)))
  | weaken {A C : Clause V} : A ⊆ C → BoundedResolution F limit A → C.card ≤ limit →
      BoundedResolution F limit C

def oneCharge (root v : V) : Bit := if v = root then 1 else 0

end CompleteParityWidth


