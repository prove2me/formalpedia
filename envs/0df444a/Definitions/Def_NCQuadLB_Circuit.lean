-- Prove2me | Definitions.Def_NCQuadLB_Circuit
-- name    : NCQuadLB_Circuit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T20:27:19.537548+00:00
-- url     : https://prove2.me/theorems/b9cec939-5d30-478e-9b2f-d04368ff5cd0
-- title:
--   Fan-in 2 noncommutative arithmetic circuits with edge scalars; product-gate count
-- statement:
--   Let $\mathbb F$ be a field and $V$ a set of noncommuting variables. A **fan-in 2 noncommutative arithmetic circuit** is a directed acyclic graph whose leaves are labeled by field constants and variables and whose internal vertices (**gates**) are labeled by $+$ or $\times$. Every gate has in-degree $2$; the $\times$ gates have a designated left and right child, and every edge carries a field scalar that multiplies the polynomial it carries.
--
--   Each vertex $g$ computes a noncommutative polynomial $\hat g\in\mathbb F\langle V\rangle$: a leaf computes its label, a sum gate with in-edges from $a$ (scalar $\alpha$) and $b$ (scalar $\beta$) computes $\alpha\hat a+\beta\hat b$, and a product gate with left child $a$ and right child $b$ computes
--
--   $$
--   \hat g=(\alpha\hat a)\cdot(\beta\hat b)\qquad(\text{left factor first}).
--   $$
--
--   The **size** of the circuit is its number of vertices, leaves included; $S$ denotes its number of $\times$ (product) gates. The circuit **computes** $f$ if its output vertex computes $f$.
--
--   This is the model of every lower bound in the mission.
--
--   **Formalization Note** The vertices are $0,1,\dots,s-1$ in a topological order: the children of vertex $k$ have index less than $k$, so acyclicity is built into the type and the value is defined by recursion on the index. An unlabeled edge is the scalar $1$. The two in-edges of a gate may come from the same vertex (as in $x\times x$). The output is a designated vertex; other vertices are allowed and counted.
-- source:
--   Shastri, Willumsgaard, A Quadratic Lower Bound for Noncommutative Circuits, arXiv:2604.20575 (version of November 2, 2026, sha256 34159453…), Definition 2.2, p.5; §2, p.5 ("We allow our circuits to have edges labeled by scalars from the field")

import Mathlib

namespace NCQuadLB

/-- A vertex of a fan-in 2 noncommutative arithmetic circuit (Shastri, Willumsgaard, *A Quadratic
Lower Bound for Noncommutative Circuits*, arXiv:2604.20575, version of November 2, 2026, sha256
34159453…, Definition 2.2, p.5). A vertex at position `k` is a leaf labeled by a field constant or by
a variable, or a gate labeled `+` or `×` with two in-edges coming from the vertices `a`, `b`, which
are earlier vertices (`a b : Fin k`), each in-edge carrying a field scalar (`α` on the edge from `a`,
`β` on the edge from `b`).

**Formalization Note** For a `×` gate, `a` is the designated left child and `b` the right child. The
two in-edges may come from the same vertex (`a = b`). -/
inductive Node (F : Type*) (V : Type*) (k : ℕ) where
  /-- a leaf labeled by the field constant `c` -/
  | const (c : F)
  /-- a leaf labeled by the variable `v` -/
  | var (v : V)
  /-- a `+` gate with in-edges from `a` (scalar `α`) and `b` (scalar `β`) -/
  | add (a b : Fin k) (α β : F)
  /-- a `×` gate with left child `a` (edge scalar `α`) and right child `b` (edge scalar `β`) -/
  | mul (a b : Fin k) (α β : F)

/-- `true` exactly for the `×` gates. -/
def Node.isMul {F V : Type*} {k : ℕ} : Node F V k → Bool
  | .mul .. => true
  | _ => false

/-- `true` exactly for the leaves (constant or variable). -/
def Node.isLeaf {F V : Type*} {k : ℕ} : Node F V k → Bool
  | .const _ => true
  | .var _ => true
  | _ => false

/-- **Fan-in 2 noncommutative arithmetic circuit** (arXiv:2604.20575, version of November 2, 2026,
sha256 34159453…, Definition 2.2, p.5): a directed acyclic graph whose leaves are labeled by field
constants and variables and whose internal nodes (gates) are labeled by `+` or `×`, each of in-degree
2, the `×` gates having designated left and right children, the edges labeled by field constants,
together with the vertex whose polynomial is the circuit's output (the root).

**Formalization Note** The vertices are `Fin size`, listed in a topological order: the children of
vertex `k` have index `< k`, which builds acyclicity into the type (every finite DAG has such an
order). Every in-edge of every gate carries a scalar (an unlabeled edge is the scalar `1`). Both
in-edges of a gate may come from the same vertex. `output` is the designated output vertex; other
vertices, even ones not below the output, are allowed and are counted in the size and in the number
of product gates. -/
structure Circuit (F : Type*) (V : Type*) where
  /-- the number of vertices (leaves included) -/
  size : ℕ
  /-- the label of vertex `k`; its children are earlier vertices -/
  node : (k : Fin size) → Node F V k
  /-- the output vertex (the root) -/
  output : Fin size

namespace Circuit

variable {F V : Type*}

/-- A child index `i : Fin k` of vertex `k`, viewed as a vertex of the circuit. -/
def child (C : Circuit F V) {k : Fin C.size} (i : Fin k) : Fin C.size :=
  ⟨i.val, lt_trans i.isLt k.isLt⟩

/-- The polynomial `ĝ ∈ F⟨V⟩` computed at vertex `g` (Definition 2.2: "Each gate computes a
noncommutative polynomial in the natural way … edges labeled by field constants … simply scale the
polynomial carried by the edge"). A constant leaf `c` computes `c`, a variable leaf `v` computes `v`,
`add a b α β` computes `α â + β b̂` and `mul a b α β` computes `(α â) · (β b̂)` (left child first). -/
noncomputable def value [CommSemiring F] (C : Circuit F V) (k : Fin C.size) : FreeAlgebra F V :=
  match C.node k with
  | .const c => algebraMap F (FreeAlgebra F V) c
  | .var v => FreeAlgebra.ι F v
  | .add a b α β => α • C.value (C.child a) + β • C.value (C.child b)
  | .mul a b α β => (α • C.value (C.child a)) * (β • C.value (C.child b))
termination_by k.val
decreasing_by all_goals simp only [child]; omega

/-- The number of `×` (product) gates of the circuit. -/
def numMul (C : Circuit F V) : ℕ :=
  (Finset.univ.filter fun k : Fin C.size => (C.node k).isMul = true).card

/-- The circuit **computes** `f` if its output vertex computes `f`. -/
def Computes [CommSemiring F] (C : Circuit F V) (f : FreeAlgebra F V) : Prop :=
  C.value C.output = f

end Circuit

end NCQuadLB


