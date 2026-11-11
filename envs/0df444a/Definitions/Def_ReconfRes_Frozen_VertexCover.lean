-- Prove2me | Definitions.Def_ReconfRes_Frozen_VertexCover
-- name    : ReconfRes_Frozen_VertexCover
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T19:20:45.942233+00:00
-- url     : https://prove2.me/theorems/8af7099c-307b-4223-9ba9-b73189b18971
-- title:
--   Vertex cover reconfiguration under token addition/removal (Theorem 3.5) and independent-set paths with a lower bound
-- statement:
--   A **vertex cover** of a finite graph $G$ is a set of vertices meeting every edge. An instance of **vertex cover reconfiguration** is a graph $G$ on $\{0,\dots,n-1\}$, an integer $K$ and two vertex covers $S_s$, $S_t$ of size at most $K-1$; the answer is yes when there is a sequence of vertex covers, each of size at most $K$, from $S_s$ to $S_t$, each obtained from the previous one by adding or removing one vertex:
--   $$S_s=S_0,S_1,\dots,S_N=S_t,\qquad |S_i|\le K,\quad |S_{i}\,\triangle\,S_{i+1}|=1 .$$
--   An **independent-set path with lower bound $K$** is the analogous sequence of independent sets of size at least $K$ (used in Lemma 3.61).
--
--   **Formalization Note.** The graph is given by an adjacency matrix; the promise asks that it be symmetric and irreflexive, and that $S_s$, $S_t$ be covers with $|S|+1\le K$. The encoding `encVC` writes $n$ and $K$ as binary numerals (`encNat`), the $n^2$ matrix bits, and the characteristic vectors of $S_s$, $S_t$.
-- source:
--   Myrisiotis, Reconfiguring Resolution Refutations, STOC 2027 submission (manuscript sha256 8b5124c1…), p. 23, Theorem 3.5; pp. 78, 80 (independent-set paths)

import Mathlib
import Definitions.Def_OptimalQueuingComplexity_Restless_encNat

open OptimalQueuingComplexity.Restless

namespace ReconfRes.Frozen

/-!
# Vertex cover reconfiguration (Theorem 3.5) and independent-set paths (Lemma 3.61)

Myrisiotis, *Reconfiguring Resolution Refutations*, STOC 2027 submission, §3.3, p. 23
(Theorem 3.5, [IDH+11]); p. 78 and p. 80 (independent-set paths with lower bound `K`).

A graph on the vertices `Fin n` is given by its adjacency matrix `adj`; the promise of
Theorem 3.5 asks that it be symmetric and irreflexive (a simple graph). The instance
encoding is `encNat n`, the `n²` matrix bits row by row, `encNat K`, and the characteristic
vectors (`n` bits each) of `Ss` and `St`.
-/

/-- A vertex cover of `G`: a set of vertices meeting every edge. -/
def IsVertexCover {n : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) : Prop :=
  ∀ u v, G.Adj u v → u ∈ S ∨ v ∈ S

/-- One step of vertex cover reconfiguration with upper bound `K`: both sets are vertex covers of
size at most `K`, and the second is obtained from the first by adding or removing one vertex. -/
def VCStep {n : ℕ} (G : SimpleGraph (Fin n)) (K : ℕ) (A B : Finset (Fin n)) : Prop :=
  IsVertexCover G A ∧ IsVertexCover G B ∧ A.card ≤ K ∧ B.card ≤ K ∧
    ((∃ v, v ∉ A ∧ B = insert v A) ∨ (∃ v, v ∈ A ∧ B = A.erase v))

/-- An instance `(G, K, Ss, St)` of vertex cover reconfiguration. -/
structure VCInstance where
  /-- number of vertices -/
  n : ℕ
  /-- adjacency matrix -/
  adj : Fin n → Fin n → Bool
  /-- the bound `K` -/
  K : ℕ
  /-- the start cover -/
  Ss : Finset (Fin n)
  /-- the target cover -/
  St : Finset (Fin n)

/-- The graph of an instance (the symmetric closure of `adj` off the diagonal; equal to `adj`
under the promise). -/
def VCInstance.graph (x : VCInstance) : SimpleGraph (Fin x.n) :=
  SimpleGraph.fromRel fun u v => x.adj u v = true

/-- The promise of Theorem 3.5: `adj` is symmetric and irreflexive, and `Ss`, `St` are vertex
covers of size at most `K − 1`. -/
def VCInstance.Promise (x : VCInstance) : Prop :=
  (∀ u v, x.adj u v = x.adj v u) ∧ (∀ u, x.adj u u = false) ∧
  IsVertexCover x.graph x.Ss ∧ IsVertexCover x.graph x.St ∧
  x.Ss.card + 1 ≤ x.K ∧ x.St.card + 1 ≤ x.K

/-- The answer: a sequence of vertex covers, each of size at most `K`, from `Ss` to `St`, each
obtained from the previous one by adding or removing one vertex. -/
def VCInstance.Yes (x : VCInstance) : Prop :=
  Relation.ReflTransGen (VCStep x.graph x.K) x.Ss x.St

/-- The encoding of an instance. -/
def encVC (x : VCInstance) : List Bool :=
  encNat x.n ++
    (List.finRange x.n).flatMap (fun i => (List.finRange x.n).map fun j => x.adj i j) ++
    encNat x.K ++
    (List.finRange x.n).map (fun i => decide (i ∈ x.Ss)) ++
    (List.finRange x.n).map (fun i => decide (i ∈ x.St))

/-- An independent set of `G`. -/
def IsIndepSet {τ : Type} (G : SimpleGraph τ) (A : Finset τ) : Prop :=
  ∀ u ∈ A, ∀ v ∈ A, ¬ G.Adj u v

/-- One step of independent-set reconfiguration with lower bound `K`: both sets are independent
of size at least `K`, and the second is obtained from the first by adding or removing one
vertex. -/
def ISStep {τ : Type} [DecidableEq τ] (G : SimpleGraph τ) (K : ℕ) (A B : Finset τ) : Prop :=
  IsIndepSet G A ∧ IsIndepSet G B ∧ K ≤ A.card ∧ K ≤ B.card ∧
    ((∃ v, v ∉ A ∧ B = insert v A) ∨ (∃ v, v ∈ A ∧ B = A.erase v))

/-- An independent-set path with lower bound `K` from `A` to `B`. -/
def ISConnected {τ : Type} [DecidableEq τ] (G : SimpleGraph τ) (K : ℕ) (A B : Finset τ) :
    Prop :=
  Relation.ReflTransGen (ISStep G K) A B

end ReconfRes.Frozen


