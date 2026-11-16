-- Prove2me | Definitions.Def_OddPermSum_Evaluation_Supplement_digraph
-- name    : OddPermSum_Evaluation_Supplement_digraph
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T20:33:45.749129+00:00
-- url     : https://prove2.me/theorems/dd27d213-da50-4c22-acd3-686d8913e60e
-- title:
--   Loopless digraphs and rotation classes of directed cycles
-- statement:
--   Let $D=(\{0,\ldots,n-1\},E)$ be a simple directed graph with no loops; antiparallel arcs are allowed. A closed vertex list of length $r+1$ describes a simple directed cycle when $r\ge2$, its first and last vertices agree, its first $r$ vertices are distinct, and every consecutive ordered pair belongs to $E$. A cycle is identified by its arc set, hence only cyclic rotations are identified. Write $\mathcal C_r$ for the even cycles of length $r$ and $E_r$ for their arc union. The predicate that $\ell$ is shortest asserts that an even cycle of that length exists and no even cycle is shorter.
--
--   These objects retain 2-cycles and distinguish opposite orientations. They supply the graph layer for both companion algorithms.
-- source:
--   Boxuan Chen, Bin Cui, Hanqing Li, Xupeng Miao, Haoze Wang, STOC 2027 submission #716 (October 2026), p. 13, §5

import Mathlib

set_option autoImplicit false

namespace OddPermSum.Evaluation.Supplement

/-- A loopless simple directed graph; opposite arcs are independent. -/
structure Digraph (n : ℕ) where
  arcs : Finset (Fin n × Fin n)
  loopless : ∀ v, (v,v) ∉ arcs

abbrev Digraph.Arc {n : ℕ} (D : Digraph n) := {e // e ∈ D.arcs}

/-- Explicit closed vertex sequence, including the repeated start at the end. -/
def ValidCycle {n : ℕ} (D : Digraph n) (r : ℕ) (p : List (Fin n)) : Prop :=
  2 ≤ r ∧ p.length = r + 1 ∧ p.head? = p.getLast? ∧ p.dropLast.Nodup ∧
    ∀ e ∈ p.zip p.tail, e ∈ D.arcs

/-- Arc sets quotient directed cycles by rotation without identifying opposite orientations. -/
def DirectedCycle {n : ℕ} (D : Digraph n) (C : Finset (Fin n × Fin n)) : Prop :=
  ∃ p, ValidCycle D C.card p ∧ (p.zip p.tail).toFinset = C

noncomputable def evenCycles {n : ℕ} (D : Digraph n) : Finset (Finset (Fin n × Fin n)) := by
  classical
  exact D.arcs.powerset.filter (fun C => DirectedCycle D C ∧ Even C.card)

noncomputable def cyclesAt {n : ℕ} (D : Digraph n) (r : ℕ) :=
  (evenCycles D).filter (fun C => C.card = r)

def IsShortest {n : ℕ} (D : Digraph n) (ℓ : ℕ) : Prop :=
  (∃ C ∈ evenCycles D, C.card = ℓ) ∧ ∀ C ∈ evenCycles D, ℓ ≤ C.card

noncomputable def shortestArcs {n : ℕ} (D : Digraph n) (ℓ : ℕ) :=
  (cyclesAt D ℓ).biUnion id

end OddPermSum.Evaluation.Supplement


