-- Prove2me | Definitions.Def_MinorFreeOracle_LinearSpace_CopyExpansion
-- name    : MinorFreeOracle_LinearSpace_CopyExpansion
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T15:42:36.074664+00:00
-- url     : https://prove2.me/theorems/985c4fbe-5b85-4ad1-83f3-38674a8b6c40
-- title:
--   Cyclic vertex copies, edge lifts, subdivisions and their natural projection
-- statement:
--   For each vertex v of a finite weighted undirected graph G, choose a positive number of copies and arrange them in a cyclic order. Choose a positive number of lifts of each original edge, specifying its endpoint copies. Connect successive copies of each vertex by zero-weight edges when there is more than one copy. The construction may reverse and subdivide any resulting edge once, giving its old weight to the first half and weight zero to the second half.
--
--   The expanded graph is the graph with exactly these vertices and edges, enumerated by finite initial segments. Its projection sends a copy to its original vertex and a subdivision vertex to the original vertex at its zero-weight end. This defines the projection on every output vertex; distance preservation and surjectivity are conclusions of the separate theorem, not fields of the construction data.
--
--   This is a generalization of the metric part of scaffolding. In the source, copies are facial corners in local cyclic order, embedded edges have two lifts, vortex edges have one lift, and only embedded edges are subdivided. Untouched vortex vertices have one copy. No surface or genus hypothesis is built into this more general construction.
-- source:
--   Eunjin Oh, Linear-Space Exact Distance Oracle for Minor-Free Graphs, STOC 2027 submission #160 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/160.pdf, §3.2, PDF p.17 (printed p.15); §7.1, PDF pp.35–36 (printed pp.33–34)

import Mathlib
import Definitions.Def_TZLevelsADO_Graph

noncomputable section

namespace MinorFreeOracle.LinearSpace

/-- Combinatorial data for vertex-copy expansion. `extra v + 1` copies of each vertex are
arranged cyclically. Each original edge has `repeatExtra e + 1` lifts with specified copies
of its two ends. Thus no original vertex or edge can disappear. The paper's scaffolding has
two lifts per embedded edge, one per vortex edge, facial corners in local rotation order,
and one copy of each untouched vortex vertex. No metric property is a field of this data. -/
structure CopyExpansion (G : TZLevelsADO.Graph) where
  extra : Fin G.n → ℕ
  repeatExtra : Fin G.m → ℕ
  sourceCopy : (e : Fin G.m) → Fin (repeatExtra e + 1) → Fin (extra (G.src e) + 1)
  targetCopy : (e : Fin G.m) → Fin (repeatExtra e + 1) → Fin (extra (G.dst e) + 1)

namespace CopyExpansion

variable {G : TZLevelsADO.Graph} (D : CopyExpansion G)

abbrev Corner := (v : Fin G.n) × Fin (D.extra v + 1)

abbrev Lift := (e : Fin G.m) × Fin (D.repeatExtra e + 1)

/-- Cyclic connecting edges are present exactly for fibers with at least two copies. -/
abbrev Connector := {v : D.Corner // 0 < D.extra v.1}

abbrev UnsplitEdge := D.Lift ⊕ D.Connector

/-- Per-edge subdivision and orientation choices. Vortex edges are not subdivided in §7.1;
the embedded edges are subdivided. Reversal allows either half to carry the original weight. -/
structure Subdivision where
  split : D.UnsplitEdge → Bool
  backwards : D.UnsplitEdge → Bool

def start : D.UnsplitEdge → D.Corner
  | .inl e => ⟨G.src e.1, D.sourceCopy e.1 e.2⟩
  | .inr z => z.val

def finish : D.UnsplitEdge → D.Corner
  | .inl e => ⟨G.dst e.1, D.targetCopy e.1 e.2⟩
  | .inr z => ⟨z.val.1,
      ⟨(z.val.2.val + 1) % (D.extra z.val.1 + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩⟩

def weight : D.UnsplitEdge → ℝ
  | .inl e => G.wt e.1
  | .inr _ => 0

variable (K : D.Subdivision)

def orientedStart (e : D.UnsplitEdge) : D.Corner :=
  if K.backwards e then D.finish e else D.start e

def orientedFinish (e : D.UnsplitEdge) : D.Corner :=
  if K.backwards e then D.start e else D.finish e

abbrev SplitEdge := {e : D.UnsplitEdge // K.split e = true}

abbrev KeptEdge := {e : D.UnsplitEdge // K.split e = false}

/-- A subdivision vertex is a copy of the head of the oriented old edge;
the first half has the old weight and the second half has weight zero. -/
abbrev Vertex := D.Corner ⊕ D.SplitEdge K

abbrev Edge := D.KeptEdge K ⊕ (D.SplitEdge K × Bool)

def edgeSrc : D.Edge K → D.Vertex K
  | .inl e => .inl (D.orientedStart K e.val)
  | .inr e => if e.2 then .inr e.1 else .inl (D.orientedStart K e.1.val)

def edgeDst : D.Edge K → D.Vertex K
  | .inl e => .inl (D.orientedFinish K e.val)
  | .inr e => if e.2 then .inl (D.orientedFinish K e.1.val) else .inr e.1

def edgeWeight : D.Edge K → ℝ
  | .inl e => D.weight e.val
  | .inr e => if e.2 then 0 else D.weight e.1.val

def original : D.Vertex K → Fin G.n
  | .inl v => v.1
  | .inr e => (D.orientedFinish K e.val).1

/-- The actual expanded weighted edge-list graph; no distance preservation is assumed. -/
def graph : TZLevelsADO.Graph := by
  classical
  exact {
    n := Fintype.card (D.Vertex K)
    m := Fintype.card (D.Edge K)
    src := fun e => Fintype.equivFin (D.Vertex K) (D.edgeSrc K ((Fintype.equivFin (D.Edge K)).symm e))
    dst := fun e => Fintype.equivFin (D.Vertex K) (D.edgeDst K ((Fintype.equivFin (D.Edge K)).symm e))
    wt := fun e => D.edgeWeight K ((Fintype.equivFin (D.Edge K)).symm e) }

/-- The prescribed projection, including subdivision vertices. -/
def projection (v : Fin (D.graph K).n) : Fin G.n := by
  classical
  exact D.original K ((Fintype.equivFin (D.Vertex K)).symm v)

end CopyExpansion

end MinorFreeOracle.LinearSpace


