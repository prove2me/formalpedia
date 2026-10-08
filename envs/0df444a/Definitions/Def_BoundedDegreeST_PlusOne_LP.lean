-- Prove2me | Definitions.Def_BoundedDegreeST_PlusOne_LP
-- name    : BoundedDegreeST_PlusOne_LP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:49:58.282986+00:00
-- url     : https://prove2.me/theorems/6625a97e-0685-4053-b2a8-6dd1c88ea2d9
-- title:
--   LP-MBDCT(G, B, W, F), (15)–(19), p. 665: edge sets, supernodes, feasibility, basic and optimal solutions, laminar bases, tokens
-- statement:
--   Let $V$ be a finite vertex set, let $G=(V,E)$ be a graph given by its finite set $E$ of edges (unordered pairs of vertices), and let $F$ be a forest on $V$. For $S\subseteq V$ write $E(S)$ and $F(S)$ for the edges of $E$, respectively of $F$, with both endpoints in $S$, and $\delta(v)$ for the edges of $E$ incident to $v$. For a vector $x$ indexed by edges and a set $U$ of edges, $x(U)=\sum_{e\in U}x_e$. The **supernodes** $\mathcal C(F)$ are the vertex sets of the connected components of $(V,F)$, isolated vertices included, and $\mathcal I(F)$ is the family of sets $S$ that are **non-intersecting with $F$**: every $C\in\mathcal C(F)$ satisfies $C\subseteq S$ or $C\cap S=\varnothing$.
--
--   Given integer degree bounds $B_v$ for the vertices $v$ of a subset $W\subseteq V$, a vector $x$ with one variable per edge of $E$ is **feasible for LP-MBDCT$(G,\mathcal B,W,F)$** when
--
--   $$
--   x(E(V))=|V|-|F(V)|-1,\qquad x(E(S))\le |S|-|F(S)|-1\ \ (S\in\mathcal I(F),\ S\neq\varnothing),\qquad x(\delta(v))\le B_v\ \ (v\in W),\qquad x_e\ge 0\ \ (e\in E).
--   $$
--
--   Its cost is $c(x)=\sum_{e\in E}c_e x_e$ for an arbitrary real cost $c$ (no sign condition), and an **optimal** solution is a feasible $x$ whose cost is at most that of every feasible vector.
--
--   The module defines, on top of these rows:
--
--   1. a **basic feasible solution**: a feasible $x$ that is the only vector in the edge-variable space satisfying with equality every constraint tight at $x$ (the equality row, the tight subtour rows, the tight degree rows and the tight rows $x_e=0$); this is the paper's "unique solution of $m$ linearly independent tight constraints, where $m$ is the number of variables";
--   2. the **support** $E^*=\{e\in E: x_e\neq 0\}$ and the degree $\deg_{E^*}(v)$;
--   3. **intersecting** sets ($X\cap Y$, $X-Y$, $Y-X$ all nonempty) and **laminar** families (no two members intersecting);
--   4. the conclusion shape of Lemma 4.3: a nonempty laminar family $\mathcal L\subseteq\mathcal I(F)$ and a set $T\subseteq W$ such that $x$ makes every row $x(E(S))=|S|-|F(S)|-1$ ($S\in\mathcal L$) and $x(\delta(v))=B_v$ ($v\in T$) tight, $x$ restricted to $E^*$ is the unique solution of that system, the characteristic vectors $\chi_{E(S)}$, $\chi_{\delta(v)}$ restricted to $E^*$ are linearly independent, and $|E^*|=|\mathcal L|+|T|$;
--   5. the **excess tokens** of a vertex in the counting argument of §4.2: each vertex receives one token per incident support edge, and a vertex of $T$ keeps two of them, so the excess is $\deg_{E^*}(v)-2$ for $v\in T$ and $\deg_{E^*}(v)$ otherwise;
--   6. simple edge sets (no loops), forests and spanning trees on the whole vertex set.
--
--   These objects are shared by both missions of the paper: the $(1,B_v+1)$ algorithm of §4 and the lower/upper bound algorithm of §5 build their linear programs, algorithms and counting lemmas on them.
--
--   **Formalization Note** Vectors are functions on all unordered pairs that vanish outside $E$. The subtour rows range over nonempty $S$: the row for $S=\varnothing$ would read $0\le -1$ and empty the LP, which the paper does not intend; at $|V|=0$ the equality row reads $0=-1$, so the LP is infeasible there. Right-hand sides are computed in the reals and the bounds $B_v$ are integers. The paper assumes without loss of generality that $E$ has no edge inside a supernode; here such edges keep a variable, which the row $x(E(C))\le |C|-|F(C)|-1=0$ for the supernode $C$ forces to $0$, so feasibility and basicness are unchanged. In the Lemma 4.3 shape the linear system is solved in the variables of $E^*$, as the paper does after deleting the zero edges in Step 2.
-- source:
--   Singh, Lau, Approximating minimum bounded degree spanning trees to within one of optimal, STOC 2007, p. 665, Eqs. (15)–(19) and the notation F(S), C(F), I(F); p. 663, basic solutions, characteristic vectors, intersecting sets and laminar families; p. 666, Lemma 4.3 (the system defining a basic solution); p. 667, §4.2 (token assignment)

import Mathlib

namespace BoundedDegreeST.PlusOne

/-- The graph is simple: loops are excluded from its finite edge set. -/
def SimpleEdges {V : Type*} (E : Finset (Sym2 V)) : Prop :=
  ∀ e ∈ E, ¬ e.IsDiag

/-- A forest on the full vertex set, including isolated vertices. -/
def IsForest {V : Type*} (F : Finset (Sym2 V)) : Prop :=
  SimpleEdges F ∧ (SimpleGraph.fromEdgeSet (↑F : Set (Sym2 V))).IsAcyclic

/-- A spanning tree is connected and acyclic on the full vertex set. -/
def IsSpanningTree {V : Type*} (F : Finset (Sym2 V)) : Prop :=
  SimpleEdges F ∧ (SimpleGraph.fromEdgeSet (↑F : Set (Sym2 V))).IsTree

/-- The vertex set of the component of `v` in `F`. -/
def component {V : Type*} (F : Finset (Sym2 V)) (v : V) : Set V :=
  {w | (SimpleGraph.fromEdgeSet (↑F : Set (Sym2 V))).Reachable v w}

/-- All components of `F`, including singleton components. -/
def components {V : Type*} (F : Finset (Sym2 V)) : Set (Set V) :=
  Set.range (component F)

/-- `S` is a union of components of `F`. -/
def Compatible {V : Type*} (F : Finset (Sym2 V)) (S : Finset V) : Prop :=
  ∀ C ∈ components F, C ⊆ (↑S : Set V) ∨ Disjoint C (↑S : Set V)

/-- `E(S)` or `F(S)`: edges with both endpoints in `S`. -/
noncomputable def internal {V : Type*} [DecidableEq V] (E : Finset (Sym2 V))
    (S : Finset V) : Finset (Sym2 V) := by
  classical
  exact E.filter (fun e => ∀ v ∈ e, v ∈ S)

/-- `δ_E(S)`: edges with exactly one endpoint in `S`. -/
noncomputable def cut {V : Type*} [DecidableEq V] (E : Finset (Sym2 V))
    (S : Finset V) : Finset (Sym2 V) := by
  classical
  exact E.filter (fun e => ∃ v ∈ e, v ∈ S ∧ ∃ w ∈ e, w ∉ S)

/-- Number of edges of `E` incident to `v`. -/
def degree {V : Type*} [DecidableEq V] (E : Finset (Sym2 V)) (v : V) : ℕ :=
  (E.filter (fun e => v ∈ e)).card

/-- The cost of an edge set. Costs need not be nonnegative. -/
def cost {V : Type*} (c : Sym2 V → ℝ) (E : Finset (Sym2 V)) : ℝ :=
  ∑ e ∈ E, c e

/-- The sum of a vector on an edge set. -/
def edgeSum {V : Type*} (x : Sym2 V → ℝ) (E : Finset (Sym2 V)) : ℝ :=
  ∑ e ∈ E, x e

/-- Vectors have variables only on the current graph's edges. -/
def Supported {V : Type*} (E : Finset (Sym2 V)) (x : Sym2 V → ℝ) : Prop :=
  ∀ e, e ∉ E → x e = 0

/-- Feasibility for LP-MBDCT, equations (16)–(19). The subtour rows range over
nonempty component unions, since the literal empty-set row would be impossible. -/
def Feasible {V : Type*} [Fintype V] [DecidableEq V]
    (E : Finset (Sym2 V)) (B : V → ℤ) (W : Finset V)
    (F : Finset (Sym2 V)) (x : Sym2 V → ℝ) : Prop :=
  Supported E x ∧
  edgeSum x E = (Fintype.card V : ℝ) - (F.card : ℝ) - 1 ∧
  (∀ S : Finset V, S.Nonempty → Compatible F S →
    edgeSum x (internal E S) ≤ (S.card : ℝ) - ((internal F S).card : ℝ) - 1) ∧
  (∀ v ∈ W, edgeSum x (cut E {v}) ≤ (B v : ℝ)) ∧
  ∀ e ∈ E, 0 ≤ x e

/-- The tight equations determine `x` uniquely in the current edge-variable
space. This includes the tight nonnegativity rows. -/
def Basic {V : Type*} [Fintype V] [DecidableEq V]
    (E : Finset (Sym2 V)) (B : V → ℤ) (W : Finset V)
    (F : Finset (Sym2 V)) (x : Sym2 V → ℝ) : Prop :=
  Feasible E B W F x ∧
  ∀ y : Sym2 V → ℝ, Supported E y →
    edgeSum y E = (Fintype.card V : ℝ) - (F.card : ℝ) - 1 →
    (∀ S : Finset V, S.Nonempty → Compatible F S →
      edgeSum x (internal E S) = (S.card : ℝ) - ((internal F S).card : ℝ) - 1 →
      edgeSum y (internal E S) = (S.card : ℝ) - ((internal F S).card : ℝ) - 1) →
    (∀ v ∈ W, edgeSum x (cut E {v}) = (B v : ℝ) →
      edgeSum y (cut E {v}) = (B v : ℝ)) →
    (∀ e ∈ E, x e = 0 → y e = 0) → y = x

/-- A feasible vector whose cost is no larger than every feasible cost. -/
def Optimal {V : Type*} [Fintype V] [DecidableEq V]
    (c : Sym2 V → ℝ) (E : Finset (Sym2 V)) (B : V → ℤ)
    (W : Finset V) (F : Finset (Sym2 V)) (x : Sym2 V → ℝ) : Prop :=
  Feasible E B W F x ∧
  ∀ y, Feasible E B W F y → ∑ e ∈ E, c e * x e ≤ ∑ e ∈ E, c e * y e

/-- The positive support of a feasible vector. -/
noncomputable def support {V : Type*} [DecidableEq V]
    (E : Finset (Sym2 V)) (x : Sym2 V → ℝ) : Finset (Sym2 V) := by
  classical
  exact E.filter (fun e => x e ≠ 0)

/-- Intersecting vertex sets cross in all three regions. -/
def Intersecting {V : Type*} [DecidableEq V]
    (S T : Finset V) : Prop :=
  (S ∩ T).Nonempty ∧ (S \ T).Nonempty ∧ (T \ S).Nonempty

/-- A family with no intersecting pair. -/
def Laminar {V : Type*} [DecidableEq V]
    (L : Finset (Finset V)) : Prop :=
  ∀ S ∈ L, ∀ T ∈ L, ¬ Intersecting S T

/-- The vector indexed by the support of `x` for an edge indicator. -/
def indicatorOnSupport {V : Type*} [DecidableEq V]
    (E : Finset (Sym2 V)) (x : Sym2 V → ℝ)
    (A : Finset (Sym2 V)) : {e : Sym2 V // e ∈ support E x} → ℝ :=
  fun e => if e.val ∈ A then 1 else 0

/-- The tight laminar rows and degree rows form a basis on the support, and
uniquely determine the positive variables. -/
def DefinesBasis {V : Type*} [Fintype V] [DecidableEq V]
    (E : Finset (Sym2 V)) (B : V → ℤ) (W : Finset V)
    (F : Finset (Sym2 V)) (x : Sym2 V → ℝ)
    (L : Finset (Finset V)) (T : Finset V) : Prop :=
  L.Nonempty ∧ Laminar L ∧
  (∀ S ∈ L, S.Nonempty ∧ Compatible F S) ∧ T ⊆ W ∧
  (∀ S ∈ L, edgeSum x (internal E S) =
      (S.card : ℝ) - ((internal F S).card : ℝ) - 1) ∧
  (∀ v ∈ T, edgeSum x (cut E {v}) = (B v : ℝ)) ∧
  (∀ y : {e : Sym2 V // e ∈ support E x} → ℝ,
    (∀ S ∈ L, (∑ e, if e.val ∈ internal E S then y e else 0) =
      (S.card : ℝ) - ((internal F S).card : ℝ) - 1) →
    (∀ v ∈ T, (∑ e, if e.val ∈ cut E {v} then y e else 0) = (B v : ℝ)) →
    y = fun e => x e.val) ∧
  LinearIndependent ℝ (fun i : Sum {S : Finset V // S ∈ L} {v : V // v ∈ T} =>
    match i with
    | .inl S => indicatorOnSupport E x (internal E S.val)
    | .inr v => indicatorOnSupport E x (cut E {v.val})) ∧
  (support E x).card = L.card + T.card

/-- Excess vertex tokens after reserving two for each vertex in `T`. -/
def excessTokens {V : Type*} [DecidableEq V]
    (E : Finset (Sym2 V)) (T : Finset V) (v : V) : ℤ :=
  (degree E v : ℤ) - (if v ∈ T then 2 else 0)

end BoundedDegreeST.PlusOne


