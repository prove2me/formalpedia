-- Prove2me | Definitions.Def_ForestPersuasion_Symmetric_Hierarchy
-- name    : ForestPersuasion_Symmetric_Hierarchy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:17:08.592864+00:00
-- url     : https://prove2.me/theorems/1e26cc95-850b-4f03-a628-71c9529f47d2
-- title:
--   Rooted forest communication hierarchy
-- statement:
--   A hierarchy on $n$ labelled receivers assigns at most one parent to each receiver. A valid hierarchy has no cycle. An edge $(j,i)$ points from the parent $j$ to its child $i$.
--
--   The set $D_i$ consists of $i$ and all its descendants; children are the immediate descendants. These sets specify which directly transmitted messages receiver $i$ observes. This representation is independent of the utilities and probability model.
-- source:
--   Konstantin Zabarnyi, Designing Information in a Forest: Algorithmic Aspects, STOC 2027 submission #271 (October 2026; PDF dated November 2, 2026), §2, forest communication hierarchies, PDF pp. 6–7 (printed pp. 5–6). https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/271.pdf

import Mathlib

open scoped NNReal ENNReal
open Classical

namespace ForestPersuasion.Symmetric

/-- A rooted directed forest is represented by one optional parent per vertex.
Validity is separate from the raw data. Source: §2, PDF pp. 6–7. -/
structure Hierarchy (n : ℕ) where
  parent : Fin n → Option (Fin n)

def Hierarchy.Edge {n : ℕ} (G : Hierarchy n) (j i : Fin n) : Prop :=
  G.parent i = some j

def Hierarchy.Valid {n : ℕ} (G : Hierarchy n) : Prop :=
  WellFounded G.Edge

noncomputable def Hierarchy.descendants {n : ℕ} (G : Hierarchy n) (i : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun j => Relation.ReflTransGen G.Edge i j)

noncomputable def Hierarchy.children {n : ℕ} (G : Hierarchy n) (i : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (G.Edge i)

noncomputable def Hierarchy.edges {n : ℕ} (G : Hierarchy n) : Finset (Fin n × Fin n) :=
  Finset.univ.filter (fun e => G.Edge e.1 e.2)

end ForestPersuasion.Symmetric


