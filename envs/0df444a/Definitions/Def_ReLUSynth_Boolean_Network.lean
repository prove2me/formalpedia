-- Prove2me | Definitions.Def_ReLUSynth_Boolean_Network
-- name    : ReLUSynth_Boolean_Network
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T00:07:47.985204+00:00
-- url     : https://prove2.me/theorems/698b9016-1fab-41f5-a51d-4f57cb8ac04e
-- title:
--   Permitted ReLU networks: DAGs with at most n_max computational vertices whose weights and biases consume distinct inventory occurrences
-- statement:
--   An **inventory** is a finite multiset of numbers whose occurrences are distinguished: here a finite type $\alpha$ of occurrences with values $W:\alpha\to\mathbb R$. A **network** on the input index set $\iota$ (the input vertices, with values $x_t$) has $h+1$ **computational vertices** $0,\dots,h$, numbered in a topological order; vertex $h$ is the **output**, the others are **hidden**. Its parameter positions are the input edges $t\to i$, the edges $j\to i$ between computational vertices with $j<i$, and the biases of the computational vertices; each position is empty or carries one occurrence $o\in\alpha$, and then has the value $W(o)$ (an empty bias is $0$).
--
--   A hidden vertex computes $z_i=\rho\big(b_i+\sum_t a_{ti}x_t+\sum_{j<i}a_{ji}z_j\big)$ with $\rho(s)=\max\{0,s\}$; the output computes the affine form $b_h+\sum_t a_{th}x_t+\sum_{j<h}a_{jh}z_j$ (**affine output**). The expression inside $\rho$ is the **preactivation**; the **actual activation pattern** at an input marks the hidden vertices with positive preactivation; **freezing** a pattern replaces each active ReLU by the identity and each inactive one by $0$, and the frozen network can be evaluated in any commutative ring.
--
--   A network is **permitted** (Definition 2.1) under the cap $n_{\max}$ and the rule *at-most-once* or *exactly-once* when: it has between one and $n_{\max}$ computational vertices; every computational vertex has an incoming edge or a present bias and lies on a directed path to the output; distinct positions carry distinct occurrences; and, under exactly-once, every occurrence is used. Acyclicity and "at most one edge per ordered pair" hold by construction.
--
--   The module also defines Boolean vectors as $0/1$ real vectors and the pairwise **mixed difference** $h(1,1)-h(1,0)-h(0,1)+h(0,0)$ of a function on the Boolean cube in two coordinates, the others fixed.
--
--   **Formalization Note.** Numbering the computational vertices in a topological order with the output last loses no network: every DAG has a topological order and the output, reachable from every computational vertex, comes last.
-- source:
--   Myrisiotis, The Complexity of ReLU Network Synthesis from a Parameter Multiset, arXiv:2611.04074v1, p. 10, Definition 2.1; p. 9 (§2); p. 22 (mixed difference)

import Mathlib

namespace ReLUSynth.Boolean

/-! Myrisiotis, *The Complexity of ReLU Network Synthesis from a Parameter Multiset*,
arXiv:2611.04074v1, §2 (pp. 9–11), Definition 2.1 (p. 10).

A network has input vertices indexed by a finite type `ι` and `h + 1` computational vertices
`0, …, h`, listed in a topological order; vertex `h` is the scalar output, the others are hidden.
Every edge and every present bias carries one inventory occurrence, an element of the occurrence
type `α`; the inventory assigns each occurrence its numerical value `W o`. -/

/-- The parameter positions of a network with input index type `ι` and computational vertices
`0, …, h`: an input edge `t → i`, an edge `j → i` between computational vertices with `j < i`
(the vertices are numbered in a topological order), and the bias of vertex `i`. Each position
carries at most one occurrence, so there is at most one edge per ordered pair of vertices. -/
inductive Pos (ι : Type) (h : ℕ) where
  /-- the edge from input vertex `t` into computational vertex `i` -/
  | inEdge (t : ι) (i : Fin (h + 1))
  /-- the edge from computational vertex `j` into computational vertex `i`, where `j < i` -/
  | hidEdge (i : Fin (h + 1)) (j : Fin i.val)
  /-- the bias of computational vertex `i` -/
  | bias (i : Fin (h + 1))

/-- A position is an edge (input edge or edge between computational vertices), not a bias. -/
def Pos.IsEdge {ι : Type} {h : ℕ} : Pos ι h → Prop
  | .inEdge _ _ => True
  | .hidEdge _ _ => True
  | .bias _ => False

/-- A network skeleton with an occurrence assignment (Definition 2.1, p. 10): `h + 1`
computational vertices `0, …, h` in topological order (vertex `h` is the output), and for each
parameter position either no parameter (`none`: the edge is absent, or the bias is absent and
equals `0`) or the inventory occurrence it consumes (`some o`). -/
structure Net (ι α : Type) where
  /-- the number of hidden vertices; the computational vertices are `0, …, h` -/
  h : ℕ
  /-- the occurrence assigned to each parameter position, `none` when the position is empty -/
  occ : Pos ι h → Option α

namespace Net

variable {ι α : Type}

/-- The output vertex `h`. -/
def out (N : Net ι α) : Fin (N.h + 1) := Fin.last N.h

/-- The numerical value of a parameter position under the values `W` of the occurrences:
`W o` if occurrence `o` is assigned to it, and `0` if the position is empty (absent edge or
absent bias). -/
def wt {R : Type} [Zero R] (N : Net ι α) (W : α → R) (p : Pos ι N.h) : R :=
  match N.occ p with
  | some o => W o
  | none => 0

/-- The values of the computational vertices when vertex `i` applies the map `act i` to its
preactivation `b_i + ∑_t a_{t i} x_t + ∑_{j < i} a_{j i} z_j` (computed in topological order). -/
def vertexVal {R : Type} [CommRing R] [Fintype ι] (N : Net ι α) (W : α → R) (x : ι → R)
    (act : Fin (N.h + 1) → R → R) : (i : Fin (N.h + 1)) → R
  | ⟨i, hi⟩ =>
    act ⟨i, hi⟩
      (N.wt W (.bias ⟨i, hi⟩) + ∑ t, N.wt W (.inEdge t ⟨i, hi⟩) * x t +
        ∑ j : Fin i, N.wt W (.hidEdge ⟨i, hi⟩ j) * vertexVal N W x act ⟨j.val, by omega⟩)
termination_by i => i.val
decreasing_by exact j.isLt

/-- The ReLU function `ρ(t) = max{0, t}`. -/
noncomputable def relu (s : ℝ) : ℝ := max 0 s

/-- The real activation rule with an affine output: every hidden vertex applies ReLU, the output
vertex applies nothing. -/
noncomputable def reluAct (N : Net ι α) (i : Fin (N.h + 1)) (s : ℝ) : ℝ :=
  if i = N.out then s else relu s

/-- The real values `z_v` of the computational vertices at the input `x ∈ ℝ^ι`
(Definition 2.1: `z_v = max(0, b_v + ∑_{(u,v) ∈ E} a_{uv} z_u)` at a hidden vertex, the affine
form at the output). -/
noncomputable def vals [Fintype ι] (N : Net ι α) (W : α → ℝ) (x : ι → ℝ) : Fin (N.h + 1) → ℝ :=
  N.vertexVal W x N.reluAct

/-- **The function computed by the network, with an affine output**: the value of the output
vertex at the input `x ∈ ℝ^ι`. -/
noncomputable def eval [Fintype ι] (N : Net ι α) (W : α → ℝ) (x : ι → ℝ) : ℝ :=
  N.vals W x N.out

/-- The preactivation of computational vertex `i` at the input `x`: the affine expression
`b_i + ∑_t a_{t i} x_t + ∑_{j < i} a_{j i} z_j` supplied to it (§2, p. 10). -/
noncomputable def preact [Fintype ι] (N : Net ι α) (W : α → ℝ) (x : ι → ℝ)
    (i : Fin (N.h + 1)) : ℝ :=
  N.wt W (.bias i) + ∑ t, N.wt W (.inEdge t i) * x t +
    ∑ j : Fin i.val, N.wt W (.hidEdge i j) * N.vals W x ⟨j.val, by omega⟩

/-- The actual activation pattern at the input `x` (§2, p. 10): the indicator `η_v` is `true`
exactly when the preactivation of vertex `v` is positive. (Its entry at the output vertex is
never used.) -/
noncomputable def actPattern [Fintype ι] (N : Net ι α) (W : α → ℝ) (x : ι → ℝ) :
    Fin (N.h + 1) → Bool :=
  fun i => decide (0 < N.preact W x i)

/-- The frozen network (§2, p. 10; Lemma 4.6): with the activation pattern `η` fixed, each
active hidden ReLU is replaced by the identity and each inactive one by zero; the output stays
affine. Its output value, computed in an arbitrary commutative ring `R` from parameter values
`W : α → R` and input values `x : ι → R`. -/
def frozenEval {R : Type} [CommRing R] [Fintype ι] (N : Net ι α) (W : α → R) (η : Fin (N.h + 1) → Bool)
    (x : ι → R) : R :=
  N.vertexVal W x (fun i s => if i = N.out then s else if η i then s else 0) N.out

/-- The edge relation between computational vertices: there is an edge `j → i`. -/
def Edge (N : Net ι α) (j i : Fin (N.h + 1)) : Prop :=
  ∃ hji : j.val < i.val, (N.occ (.hidEdge i ⟨j.val, hji⟩)).isSome

/-- Computational vertex `i` has at least one incoming edge or a present bias. -/
def HasInput (N : Net ι α) (i : Fin (N.h + 1)) : Prop :=
  (N.occ (.bias i)).isSome ∨ (∃ t, (N.occ (.inEdge t i)).isSome) ∨
    ∃ j : Fin i.val, (N.occ (.hidEdge i j)).isSome

end Net

/-- The two inventory rules (p. 2, p. 10): at-most-once use (occurrences may stay unused) and
exactly-once use (every occurrence is assigned). -/
inductive InventoryRule where
  | atMostOnce
  | exactlyOnce
  deriving DecidableEq

/-- **Permitted network** (Definition 2.1, p. 10) for the inventory with occurrence type `α`
under the rule `rule` and the cap `nmax` on computational vertices:
* between one and `nmax` computational vertices (`h + 1 ≤ nmax`);
* every computational vertex has an incoming edge or a present bias, and lies on a directed path
  to the output;
* distinct positions carry distinct occurrences (each occurrence index is assigned at most once);
* under the exactly-once rule every occurrence is assigned.
Acyclicity, "inputs have no incoming edges", "at most one edge per ordered pair" and "edges enter
computational vertices" hold by construction of `Pos`. -/
def Net.Permitted {ι α : Type} (N : Net ι α) (rule : InventoryRule) (nmax : ℕ) : Prop :=
  N.h + 1 ≤ nmax ∧
  (∀ i, N.HasInput i) ∧
  (∀ i, Relation.ReflTransGen N.Edge i N.out) ∧
  (∀ p p' : Pos ι N.h, ∀ o : α, N.occ p = some o → N.occ p' = some o → p = p') ∧
  (rule = InventoryRule.exactlyOnce → ∀ o : α, ∃ p, N.occ p = some o)

/-- A Boolean vector as a real vector with coordinates in `{0, 1}`. -/
def boolVec {ι : Type} (x : ι → Bool) : ι → ℝ := fun t => if x t then 1 else 0

/-- A bit as the real number `0` or `1`. -/
def bitR (b : Bool) : ℝ := if b then 1 else 0

/-- The pairwise mixed difference `h(1,1) − h(1,0) − h(0,1) + h(0,0)` of a real function on the
Boolean cube in the coordinates `s, t`, the other coordinates fixed as in `x` (§4.3, p. 22). -/
def mixedDiff {ι : Type} [DecidableEq ι] (g : (ι → Bool) → ℝ) (s t : ι) (x : ι → Bool) : ℝ :=
  g (Function.update (Function.update x s true) t true) -
    g (Function.update (Function.update x s true) t false) -
    g (Function.update (Function.update x s false) t true) +
    g (Function.update (Function.update x s false) t false)

end ReLUSynth.Boolean


