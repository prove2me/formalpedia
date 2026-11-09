-- Prove2me | Definitions.Def_AlmostKing_Query_Goal
-- name    : AlmostKing_Query_Goal
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:50:13.738165+00:00
-- url     : https://prove2.me/theorems/7481b4ad-ec57-41d2-bcf8-22804113fda8
-- title:
--   Tournaments, controlled vertices, and deterministic query trees
-- statement:
--   A tournament is a loopless directed graph with exactly one arc between every pair of distinct vertices. An oriented graph is loopless and has no pair of opposite arcs. All vertex types used for counting are finite. Write $N_D^+(v)$ for the vertices receiving an arc from $v$, and $N_D^+(X)$ for the union of these sets over $v\in X$; vertices of $X$ are allowed in this union. The set of controlled vertices excludes $v$ itself and consists of vertices reachable from $v$ in one or two arcs. A $\delta$-king satisfies
--   $$|N_D^{++}(v)|\ge\delta(|V|-1).$$
--   Subtraction on the right is in the real numbers.
--
--   For known size $n$, a deterministic query algorithm is a finite decision tree with leaves labelled by vertices of $\mathrm{Fin}\,n$ and internal nodes labelled by a pair of vertices. Evaluation follows the first branch exactly when the oracle reports the corresponding forward arc. Its query count is the number of internal nodes visited on that input. A self-query returns false on a tournament and still costs one. No correctness assertion or cost bound is part of this type.
--
--   These definitions provide the oracle model and the reachability notion for the main theorem; the neighborhood operations also support the structural milestones.
-- source:
--   Ziad Ismaili Alaoui, Oded Lachish, Nikhil S. Mande, A King for Almost Everyone, STOC 2027 submission #472 (October 2026), SHA-256 c262b203b2088dcae48025a77e016df4cc78f93c1856a6fac580c7577d8dea92, §1 query model, p. 2; §2 and Definitions 2–3, p. 5. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/472.pdf

import Mathlib

namespace AlmostKing.Query

/-- Definition 2, p. 5: no loops and exactly one arc between distinct vertices. -/
def IsTournament {V : Type*} (T : Digraph V) : Prop :=
  (∀ v, ¬ T.Adj v v) ∧
  ∀ u v, u ≠ v → (T.Adj u v ∨ T.Adj v u) ∧ ¬ (T.Adj u v ∧ T.Adj v u)

/-- Section 2, p. 5: an oriented graph need not be complete. -/
def IsOriented {V : Type*} (D : Digraph V) : Prop :=
  (∀ v, ¬ D.Adj v v) ∧ ∀ u v, D.Adj u v → ¬ D.Adj v u

/-- Section 2, p. 5: the out-neighbourhood of a vertex. -/
noncomputable def outNbhd {V : Type*} [Fintype V] (D : Digraph V) (v : V) : Finset V :=
  by classical exact Finset.univ.filter (D.Adj v)

/-- Section 2, p. 5: the union of the out-neighbourhoods, without deleting X. -/
noncomputable def outNbhdSet {V : Type*} [Fintype V] (D : Digraph V) (X : Finset V) : Finset V :=
  by classical exact Finset.univ.filter (fun u => ∃ v ∈ X, D.Adj v u)

/-- Definition 3, p. 5: other vertices reachable within two arcs; the starting vertex is excluded. -/
noncomputable def controlled {V : Type*} [Fintype V] (D : Digraph V) (v : V) : Finset V :=
  by classical exact Finset.univ.filter (fun u => u ≠ v ∧
    (D.Adj v u ∨ ∃ z, D.Adj v z ∧ D.Adj z u))

/-- Definition 3. Subtraction occurs in the reals, not in the natural numbers. -/
def IsDeltaKing {V : Type*} [Fintype V] (D : Digraph V) (δ : ℝ) (v : V) : Prop :=
  δ * ((Fintype.card V : ℝ) - 1) ≤ (controlled D v).card

/-- Section 1, p. 2: a finite adaptive deterministic oracle decision tree.
The type carries neither a correctness assertion nor a query bound. -/
inductive QueryTree (n : ℕ) where
  | output (v : Fin n)
  | query (u v : Fin n) (ifUV ifVU : QueryTree n)

/-- Follow the answers of the oracle, including the false answer on a self-query. -/
noncomputable def QueryTree.eval {n : ℕ} (t : QueryTree n) (T : Digraph (Fin n)) : Fin n := by
  classical
  exact match t with
  | .output v => v
  | .query u v yes no => if T.Adj u v then yes.eval T else no.eval T

/-- Number of oracle queries on the evaluation path, rather than tree size. -/
noncomputable def QueryTree.queries {n : ℕ} (t : QueryTree n) (T : Digraph (Fin n)) : ℕ := by
  classical
  exact match t with
  | .output _ => 0
  | .query u v yes no => 1 + if T.Adj u v then yes.queries T else no.queries T

end AlmostKing.Query


