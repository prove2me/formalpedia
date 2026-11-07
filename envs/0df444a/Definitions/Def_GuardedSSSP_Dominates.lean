-- Prove2me | Definitions.Def_GuardedSSSP_Dominates
-- name    : GuardedSSSP_Dominates
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:47:18.071796+00:00
-- url     : https://prove2.me/theorems/908c1418-4dcd-4a44-a10a-c40b08c0d665
-- title:
--   Dominators, rooted orders and forward arcs
-- statement:
--   Let $(G,s)$ be a rooted directed multigraph.
--
--   1. A vertex $v$ **dominates** $u$ if every walk from $s$ to $u$ visits $v$ (counting both endpoints). A primitive arc $(u,v)$ is *inactive* if its head $v$ dominates its tail $u$.
--   2. A **rooted order** is a linear order $\prec$ of the vertices in which $s$ is first and every other vertex has an incoming arc from an earlier vertex.
--   3. An arc is **forward** in $\prec$ if its tail precedes its head.
--
--   These notions define the active core of the paper (§4.2) and the forward-arc charge of Lemma B.2.
--
--   **Formalization Note** Quantifying over walks is equivalent to quantifying over simple paths, because every walk contains a simple path with the same endpoints whose vertices are among the walk's. A vertex unreachable from $s$ is dominated by every vertex. A rooted order is a bijection `pos : Fin n ≃ Fin n` giving each vertex its position.
-- source:
--   Cai, Uniform Guarded Bootstrapping for Topology-Sensitive Directed Shortest Paths, STOC 2027 submission (manuscript sha256 bcda0e91…), §3.3, p.8 (PDF p.9); §4.2, p.9 (PDF p.10); Lemma B.2, p.32 (PDF p.33)

import Mathlib
import Definitions.Def_AtomicDynRouting_ResidenceTime_Network

namespace GuardedSSSP

open AtomicDynRouting.ResidenceTime

/-!
# Dominators, rooted orders and forward arcs

Bin Cai, *Uniform Guarded Bootstrapping for Topology-Sensitive Directed Shortest Paths*, STOC 2027
submission (manuscript sha256 bcda0e91…).

* §3.3, p.8 (PDF p.9) and §4.2, p.9 (PDF p.10): "A vertex v dominates u when every source-to-u path
  contains v." A primitive `(u, v)` is *inactive* if its head `v` dominates its tail `u`.
* Lemma B.2, p.32 (PDF p.33): "Let ≺ be a rooted order of a reachable directed multigraph G: the source is
  first and every other vertex has an incoming arc from an earlier vertex." An arc is *forward* when its
  tail precedes its head.

**Formalization Note.**
* The vertices of a walk `P` from `s` are `s` followed by the heads of its arcs. Domination quantifies
  over walks; this is equivalent to quantifying over simple paths, because every walk from `s` to `u`
  contains a simple path from `s` to `u` whose vertices are among the walk's. A vertex `u` unreachable
  from `s` is dominated by every vertex (the condition is vacuous), so arcs leaving it are inactive.
* A rooted order is a bijective position map `pos : Fin n ≃ Fin n` (`u ≺ v` iff `pos u < pos v`). Loops
  are never forward.
-/

/-- The vertex sequence of the walk `P` started at `s`: `s`, then the head of each arc. -/
def walkVertices {n m : ℕ} (G : Network (Fin n) (Fin m)) (s : Fin n) (P : List (Fin m)) :
    List (Fin n) :=
  s :: P.map G.head

/-- `v` dominates `u` (with respect to the source `s`): every walk from `s` to `u` visits `v`. -/
def Dominates {n m : ℕ} (G : Network (Fin n) (Fin m)) (s v u : Fin n) : Prop :=
  ∀ P : List (Fin m), G.IsPathFrom s u P → v ∈ walkVertices G s P

/-- `pos` is a rooted order of `(G, s)`: the source is first and every other vertex has an incoming arc
from an earlier vertex. -/
def IsRootedOrder {n m : ℕ} (G : Network (Fin n) (Fin m)) (s : Fin n) (pos : Fin n ≃ Fin n) :
    Prop :=
  (∀ v, pos s ≤ pos v) ∧ ∀ v, v ≠ s → ∃ e : Fin m, G.head e = v ∧ pos (G.tail e) < pos v

/-- The arc `e` is forward in the order `pos`: its tail precedes its head. -/
def IsForward {n m : ℕ} (G : Network (Fin n) (Fin m)) (pos : Fin n ≃ Fin n) (e : Fin m) : Prop :=
  pos (G.tail e) < pos (G.head e)

instance {n m : ℕ} (G : Network (Fin n) (Fin m)) (pos : Fin n ≃ Fin n) (e : Fin m) :
    Decidable (IsForward G pos e) := by unfold IsForward; infer_instance

end GuardedSSSP


