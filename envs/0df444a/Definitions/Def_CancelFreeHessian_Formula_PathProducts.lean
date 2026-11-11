-- Prove2me | Definitions.Def_CancelFreeHessian_Formula_PathProducts
-- name    : CancelFreeHessian_Formula_PathProducts
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T22:54:57.897496+00:00
-- url     : https://prove2.me/theorems/fa7204ba-2dd4-426b-91c4-c4d2b94a99bb
-- title:
--   Offline ancestor-path products in a commutative semigroup: rooted trees, path queries, product-only programs and their encodings
-- statement:
--   A **rooted tree** has nodes $0,\dots,N-1$, root $N-1$, and a parent array with $v<\mathrm{parent}(v)<N$ for every non-root $v$. The edge from $v$ to its parent carries a label $\lambda(v)$ in a commutative semigroup $M$. A **path query** $(u,v)$, with $u$ a strict ancestor of $v$, asks for
--   $$\prod_{e\text{ on the path from }v\text{ up to }u}\lambda(e).$$
--   A **product-only program** is a straight-line program of binary products whose operands are edge labels or earlier products, with one designated output per query. It is a formal object, fixed by the tree and the queries, and it **answers** a query list if in every commutative semigroup, under every labelling, each output equals the queried path product. Its size is its number of products.
--
--   The tree and queries are given to a RAM as $[N,Q]$, the parent of each node ($0$ for the root), then each query $(u,v)$; a program is output as its number of products, two operands per product ($[0,e]$ for a label, $[1,j]$ for a product), the number of outputs and each output operand.
--
--   **Formalization Note.** `RTree.path u v` lists the lower endpoints $v,\mathrm{parent}(v),\dots$ of the edges on the path; `nprod` multiplies the labels of a nonempty list (the empty list, never queried, gives $\lambda(0)$). A forward reference in a program reads $\lambda(0)$, a leaf value, so it adds no power. Semigroups range over `Type`.
-- source:
--   Tianlang Chen, The Cancellation-Free Cost of Hessian Diagonals: Exact Counts, Formulas and Interfaces, STOC 2027 submission (manuscript sha256 de5c3ef4…), p. 12, §4 Cost; p. 9, §2 Tree path products [Tar79]

import Mathlib

open Classical

namespace CancelFreeHessian.Formula

/-!
# Offline ancestor-path products in a commutative semigroup

Tianlang Chen, *The Cancellation-Free Cost of Hessian Diagonals*, §4 "Cost" (p. 12) and §2 "Tree
path products" (p. 9), after Tarjan [Tar79]. A rooted tree has nodes `0, …, N − 1`, root `N − 1`
and a parent array with `v < parent v` for every non-root `v`. The edge from `v` to its parent
carries the label `lab v` in a commutative semigroup. A query `(u, v)`, with `u` a strict ancestor
of `v`, asks for the product of the labels of the edges on the path from `v` up to `u`.

A product-only program is a straight-line program of binary products whose operands are edge
labels or earlier products, with one designated output operand per query. It is a formal object:
it is fixed by the tree and the queries and must be correct for every commutative semigroup and
every labelling.
-/

/-- A rooted tree on the nodes `0, …, N − 1` with root `N − 1`, given by its parent array. -/
structure RTree where
  N : ℕ
  parent : ℕ → ℕ

namespace RTree

variable (T : RTree)

/-- Parent array of a tree numbered from the leaves up: every non-root node `v` has a parent
`parent v` with `v < parent v < N`. -/
def WF : Prop := ∀ v, v + 1 < T.N → v < T.parent v ∧ T.parent v < T.N

/-- `u` is the parent of the non-root node `v`. -/
def ParentOf (v u : ℕ) : Prop := v + 1 < T.N ∧ T.parent v = u

/-- `u` is a strict ancestor of `v`. -/
def StrictAnc (u v : ℕ) : Prop := Relation.TransGen T.ParentOf v u

/-- The edges on the path from `v` up to its strict ancestor `u`, each edge named by its lower
endpoint: `v, parent v, …`, up to the child of `u` on the path. -/
def path (u v : ℕ) : List ℕ :=
  if _h : v + 1 < T.N ∧ v < T.parent v ∧ v < u then
    v :: (if T.parent v = u then [] else path u (T.parent v))
  else []
termination_by u - v
decreasing_by omega

end RTree

/-- The product of the labels of a nonempty list of edges (the empty list, never used, gives
`lab 0`). -/
def nprod {M : Type} [CommSemigroup M] (lab : ℕ → M) : List ℕ → M
  | [] => lab 0
  | v :: rest => rest.foldl (fun a w => a * lab w) (lab v)

/-- An operand of a product-only program: an edge label, or the product computed at gate `j`. -/
inductive SOperand where
  | label (e : ℕ)
  | gate (j : ℕ)
  deriving DecidableEq

/-- A product-only (semigroup) straight-line program: its product gates in order, each the
product of two operands, and one output operand per query. -/
structure SProgram where
  gates : List (SOperand × SOperand)
  outs : List SOperand

/-- The number of semigroup operations of the program. -/
def SProgram.size (S : SProgram) : ℕ := S.gates.length

/-- The value of an operand under the labelling `lab`, the products computed so far being `prev`
(a forward reference, never needed, reads `lab 0`). -/
def SOperand.eval {M : Type} [CommSemigroup M] (lab : ℕ → M) (prev : List M) : SOperand → M
  | .label e => lab e
  | .gate j => prev.getD j (lab 0)

/-- The values of all product gates, in order. -/
def SProgram.values (S : SProgram) {M : Type} [CommSemigroup M] (lab : ℕ → M) : List M :=
  S.gates.foldl (fun acc g => acc ++ [g.1.eval lab acc * g.2.eval lab acc]) []

/-- The program answers the query list `Qs` on the tree `T`: it has one output per query, and in
every commutative semigroup, under every labelling of the edges, the output for the query
`(u, v)` is the product of the labels on the path from `v` up to `u`. -/
def SProgram.Computes (S : SProgram) (T : RTree) (Qs : List (ℕ × ℕ)) : Prop :=
  S.outs.length = Qs.length ∧
    ∀ (M : Type) [CommSemigroup M] (lab : ℕ → M), ∀ q ∈ Qs.zip S.outs,
      q.2.eval lab (S.values lab) = nprod lab (T.path q.1.1 q.1.2)

/-- The input encoding of a tree and its queries: `[N, Q]`, the parent of each node
`0, …, N − 1` (`0` for the root), then each query `(u, v)`. -/
def encPathInput (T : RTree) (Qs : List (ℕ × ℕ)) : List ℤ :=
  [(T.N : ℤ), (Qs.length : ℤ)] ++
    (List.range T.N).map (fun v => if v + 1 < T.N then (T.parent v : ℤ) else 0) ++
    Qs.flatMap fun q => [(q.1 : ℤ), (q.2 : ℤ)]

/-- An operand as two integers: `[0, e]` for a label, `[1, j]` for a gate. -/
def encSOperand : SOperand → List ℤ
  | .label e => [0, (e : ℤ)]
  | .gate j => [1, (j : ℤ)]

/-- The output encoding of a product-only program: the number of gates, each gate's two operands,
the number of outputs, each output operand. -/
def encSProgram (S : SProgram) : List ℤ :=
  [(S.gates.length : ℤ)] ++ S.gates.flatMap (fun g => encSOperand g.1 ++ encSOperand g.2) ++
    [(S.outs.length : ℤ)] ++ S.outs.flatMap encSOperand

end CancelFreeHessian.Formula


