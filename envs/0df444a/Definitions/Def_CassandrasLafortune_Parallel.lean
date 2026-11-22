-- Prove2me | Definitions.Def_CassandrasLafortune_Parallel
-- name    : CassandrasLafortune_Parallel
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-22T18:52:27.730703+00:00
-- url     : https://prove2.me/theorems/f2afbdff-b940-46bb-ace0-8a9c046b4a6a
-- title:
--   Parallel generator and projection of partially shared events
-- statement:
--   Partition the union alphabet into the events private to each side and the shared events. Project each event to zero or one local letter on each side. Construct a generator whose transition updates precisely the participating components and whose marked pairs have both states marked.
-- source:
--   C. G. Cassandras and S. Lafortune, Introduction to Discrete Event Systems, 2nd ed. (Springer, 2008), ch. 2, §2.3.2, Composition Operations, parallel composition. https://doi.org/10.1007/978-0-387-68612-7_2 Lean source https://github.com/kmehltretter82/linux-rv-lean/blob/d516e69a81f09c0a017196ea954e4676316cfa3f/Definitions/Def_CassandrasLafortune_Parallel.lean

import Definitions.Def_RamadgeWonham_Shared_Generator

/-! Parallel composition of deterministic generators with partially overlapping event alphabets.
The three letter types represent the two set differences and the intersection. -/

namespace CassandrasLafortune

open RamadgeWonham.Shared

/-- The union alphabet, partitioned by which components participate in each event. -/
inductive Event (A B C : Type) where
  | leftOnly (a : A)
  | rightOnly (b : B)
  | shared (c : C)
  deriving DecidableEq

variable {A B C : Type}

/-- Projection of an event onto the left alphabet. -/
def Event.left : Event A B C → Option (A ⊕ C)
  | .leftOnly a => some (.inl a)
  | .rightOnly _ => none
  | .shared c => some (.inr c)

/-- Projection of an event onto the right alphabet. -/
def Event.right : Event A B C → Option (B ⊕ C)
  | .leftOnly _ => none
  | .rightOnly b => some (.inl b)
  | .shared c => some (.inr c)

/-- A component stutters on a foreign event and takes its own partial transition otherwise. -/
def localStep {α : Type} (G : Generator α) (q : G.Q) : Option α → Option G.Q
  | none => some q
  | some a => G.δ a q

/-- The operational product: a transition requires a successor in each participating component.
Runs from the initial pair visit precisely the accessible part of the product. -/
def parallel (G : Generator (A ⊕ C)) (H : Generator (B ⊕ C)) : Generator (Event A B C) where
  Q := G.Q × H.Q
  δ e p := do
    let q ← localStep G p.1 e.left
    let r ← localStep H p.2 e.right
    return (q, r)
  q0 := (G.q0, H.q0)
  Qm := {p | p.1 ∈ G.Qm ∧ p.2 ∈ H.Qm}

end CassandrasLafortune


