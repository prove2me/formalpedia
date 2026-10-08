-- Prove2me | Definitions.Def_HararySachs_Hyper_Veblen
-- name    : HararySachs_Hyper_Veblen
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T12:36:34.903159+00:00
-- url     : https://prove2.me/theorems/2216f8cc-aab8-4103-95bd-ac68ffc4f1d2
-- title:
--   Definitions 6 and 8–10 — Veblen multi-hypergraphs, rootings, and associated coefficients
-- statement:
--   A $k$-uniform multi-hypergraph is a multiset of $k$-element edges. It is **Veblen** when every vertex degree is divisible by $k$. A rooting is an ordered sequence of rooted edges with nondecreasing roots and exactly the prescribed edge multiset. Each rooted edge contributes an arc from its root to each of its other vertices; their sum is $D_R$.
--
--   $$C_S=\sum_{R:\,D_R\text{ Eulerian}}\frac{\tau(D_R)}{\prod_{v\in V(D_R)}\deg^-(v)}$$
--
--   for connected $S$, and $C_S$ is the product of these coefficients over the components of a disconnected $S$. The definitions also enumerate ordered tuples of labeled multi-hypergraphs with bounded edge counts for the labeled form of Theorem 14.
--
--   **Formalization Note** Rootings are functions from sequence positions, so different orders within an equal-root block count separately when their rooted edges differ. Covered vertices, rather than padded isolated vertices, determine components and the denominator.
-- source:
--   Clark and Cooper, A Harary-Sachs theorem for hypergraphs, arXiv:1812.00468v2, pp. 7–10, Definitions 6, 8, 9, and 10

import Mathlib
import Definitions.Def_HararySachs_Hyper_Digraph

namespace HararySachs.Hyper

abbrev MultiGraph (n : ℕ) := Multiset (Finset (Fin n))

def IsUniform {n : ℕ} (S : MultiGraph n) (k : ℕ) : Prop :=
  ∀ e ∈ S, e.card = k

def vertexDegree {n : ℕ} (S : MultiGraph n) (v : Fin n) : ℕ :=
  (S.filter (fun e => v ∈ e)).card

def covered {n : ℕ} (S : MultiGraph n) : Finset (Fin n) :=
  Finset.univ.filter (fun v => 0 < vertexDegree S v)

def IsVeblen {n : ℕ} (S : MultiGraph n) (k : ℕ) : Prop :=
  IsUniform S k ∧ ∀ v : Fin n, k ∣ vertexDegree S v

def EdgeAdjacent {n : ℕ} (S : MultiGraph n) (u v : Fin n) : Prop :=
  ∃ e ∈ S, u ∈ e ∧ v ∈ e

def IsConnected {n : ℕ} (S : MultiGraph n) : Prop :=
  S ≠ 0 ∧ ∀ u ∈ covered S, ∀ v ∈ covered S,
    Relation.ReflTransGen (EdgeAdjacent S) u v

noncomputable def componentAt {n : ℕ} (S : MultiGraph n) (v : Fin n) : MultiGraph n := by
  classical
  exact S.filter (fun e => ∃ u ∈ e, Relation.ReflTransGen (EdgeAdjacent S) v u)

noncomputable def components {n : ℕ} (S : MultiGraph n) : Finset (MultiGraph n) := by
  classical
  exact (covered S).image (componentAt S)

def IsRooting {n : ℕ} (S : MultiGraph n)
    (R : Fin S.card → Fin n × Finset (Fin n)) : Prop :=
  (∀ i, (R i).1 ∈ (R i).2) ∧
  Monotone (fun i => (R i).1) ∧
  ((List.ofFn (fun i => (R i).2) : List (Finset (Fin n))) : Multiset (Finset (Fin n))) = S

def rootedArcs {n : ℕ} {S : MultiGraph n}
    (R : Fin S.card → Fin n × Finset (Fin n)) : ArcMult n :=
  fun u v => (Finset.univ.filter (fun i => (R i).1 = u ∧ v ∈ (R i).2 ∧ v ≠ u)).card

def IsEulerRooting {n : ℕ} (S : MultiGraph n)
    (R : Fin S.card → Fin n × Finset (Fin n)) : Prop :=
  IsRooting S R ∧ IsEulerian (rootedArcs R)

noncomputable def connectedCoeff {n : ℕ} (S : MultiGraph n) : ℚ := by
  classical
  exact ∑ R : Fin S.card → Fin n × Finset (Fin n),
    if IsEulerRooting S R then
      (numArb (rootedArcs R) : ℚ) /
        ∏ v ∈ active (rootedArcs R), (inDeg (rootedArcs R) v : ℚ)
    else 0

noncomputable def assocCoeff {n : ℕ} (S : MultiGraph n) : ℚ :=
  ∏ C ∈ components S, connectedCoeff C

abbrev SizedEdges {n : ℕ} (E : Finset (Finset (Fin n))) (d : ℕ) :=
  Σ t : Fin (d + 1), Fin t.val → E

def toMulti {n d : ℕ} {E : Finset (Finset (Fin n))}
    (a : SizedEdges E d) : MultiGraph n :=
  ((List.ofFn (fun i => (a.2 i : Finset (Fin n))) : List (Finset (Fin n))) :
    Multiset (Finset (Fin n)))

noncomputable def tuples {n : ℕ} (E : Finset (Finset (Fin n)))
    (d m : ℕ) : Finset (Fin m → MultiGraph n) := by
  classical
  exact Finset.univ.image (fun f : Fin m → SizedEdges E d => fun i => toMulti (f i))

noncomputable def allMultisets {n : ℕ} (E : Finset (Finset (Fin n)))
    (d : ℕ) : Finset (MultiGraph n) := by
  classical
  exact Finset.univ.image (fun f : Fin d → E =>
    ((List.ofFn (fun i => (f i : Finset (Fin n))) : List (Finset (Fin n))) :
      MultiGraph n))

end HararySachs.Hyper


