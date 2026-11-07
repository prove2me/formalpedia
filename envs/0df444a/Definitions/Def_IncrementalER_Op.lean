-- Prove2me | Definitions.Def_IncrementalER_Op
-- name    : IncrementalER_Op
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T17:04:58.604182+00:00
-- url     : https://prove2.me/theorems/465e8d65-6abd-4203-aaa6-95c567feb319
-- title:
--   Operations InsertEdge / Query and valid operation sequences
-- statement:
--   An operation on a graph with $n$ vertices is either $\mathrm{InsertEdge}(u,v,c)$ or $\mathrm{Query}(d)$, where the demand $d$ is given by the list of its nonzero entries $(v_1,x_1),\dots,(v_s,x_s)$ (distinct vertices, nonzero values). The graph seen by operation $j$ consists of the edges inserted by operations $0,\dots,j-1$.
--
--   For exponents $a,b\in\mathbb N$, a sequence of operations is **valid** if
--
--   1. every inserted capacity is positive and any two inserted capacities satisfy $c\le n^b c'$ (polynomially bounded capacity ratio);
--   2. every query has at most $(1+\log n)^a$ nonzero entries, satisfies $d^\top\mathbf 1=0$, and satisfies $d^\top\mathbf 1_C=0$ on every connected component $C$ of the graph seen by it.
--
--   These are the hypotheses of Theorem 1.1 on the input.
--
--   **Formalization Note** $\tilde O(1)$ hides factors polynomial in $\log N$ (p.10), so "$\tilde O(1)$ nonzero entries" is read as $\le(1+\log n)^a$ for an exponent $a$ that the theorem quantifies before its constants; $\log$ is the natural logarithm.
-- source:
--   Goranci, Kyng, Probst Gutenberg, Zhao, Zöcklein, Incremental All-Pairs Effective Resistance in Almost-Linear Time, STOC 2027 submission (manuscript sha256 a0415fd5…), Theorem 1.1 and footnote 1, p.4; notation, p.10

import Mathlib
import Definitions.Def_IncrementalER_Edge

namespace IncrementalER

/-!
# Operation sequences of the incremental data structure

Goranci, Kyng, Probst Gutenberg, Zhao, Zöcklein, *Incremental All-Pairs Effective Resistance in
Almost-Linear Time*, STOC 2027 submission (manuscript sha256 a0415fd5…), Theorem 1.1 and
footnote 1, p.4; conventions of §3, p.10.

**Formalization Note.**
* The graph on `n` vertices starts empty; `InsertEdge(u, v, c)` appends an edge and `Query(d)`
  carries `d` as a sparse list of (vertex, value) pairs with distinct vertices and nonzero values,
  so the list length is the number of nonzero entries of `d`.
* `ValidSeq n a b ops` is the theorem's preamble for a whole (oblivious) sequence:
  1. capacities are positive and their ratio is polynomially bounded, `c ≤ n^b · c'` for any two
     inserted capacities;
  2. every query has at most `(1 + log n)^a` nonzero entries (the `Õ(1)` of the statement, since
     `Õ` hides factors polynomial in `log N`, p.10; natural logarithm), sums to zero, and sums to
     zero on every connected component of the graph of the edges inserted before it
     (footnote 1).
-/

/-- An operation: insert an edge `(u, v)` with capacity `c`, or query the energy of a sparse
demand. -/
inductive Op (n : ℕ) where
  | insertEdge (u v : Fin n) (c : ℝ)
  | query (d : List (Fin n × ℝ))

/-- The edge carried by an operation, if it is an insertion. -/
def Op.edge? {n : ℕ} : Op n → Option (Edge n)
  | .insertEdge u v c => some ⟨u, v, c⟩
  | .query _ => none

/-- The edges inserted by the first `j` operations: the graph seen by operation `j`
(0-indexed). -/
def edgesBefore {n : ℕ} (ops : List (Op n)) (j : ℕ) : List (Edge n) :=
  (ops.take j).filterMap Op.edge?

/-- A sparse demand admissible in the graph `es`: distinct vertices, nonzero values, at most
`(1 + log n)^a` entries, total sum zero, and zero sum on every connected component of `es`. -/
def ValidQuery {n : ℕ} (a : ℕ) (es : List (Edge n)) (l : List (Fin n × ℝ)) : Prop :=
  (l.map Prod.fst).Nodup ∧ (∀ p ∈ l, p.2 ≠ 0) ∧
    (l.length : ℝ) ≤ (1 + Real.log n) ^ a ∧
    ∑ x, sparseVec l x = 0 ∧ ComponentFeasible es (sparseVec l)

/-- The hypotheses of Theorem 1.1 on an operation sequence: positive capacities with ratio at
most `n^b`, and every query admissible in the graph of the edges inserted before it. -/
def ValidSeq {n : ℕ} (a b : ℕ) (ops : List (Op n)) : Prop :=
  (∀ e ∈ ops.filterMap Op.edge?, 0 < e.c) ∧
    (∀ e ∈ ops.filterMap Op.edge?, ∀ e' ∈ ops.filterMap Op.edge?,
      e.c ≤ (n : ℝ) ^ b * e'.c) ∧
    ∀ j : ℕ, ∀ h : j < ops.length, ∀ l : List (Fin n × ℝ), ops[j] = .query l →
      ValidQuery a (edgesBefore ops j) l

end IncrementalER


