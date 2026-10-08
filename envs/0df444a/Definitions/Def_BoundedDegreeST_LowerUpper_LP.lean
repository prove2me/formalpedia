-- Prove2me | Definitions.Def_BoundedDegreeST_LowerUpper_LP
-- name    : BoundedDegreeST_LowerUpper_LP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T19:20:01.552646+00:00
-- url     : https://prove2.me/theorems/0b647ebe-8fb9-46eb-a33c-6a7d6af3eb42
-- title:
--   LP-MBDCT(G, 𝓐, 𝓑, U, W, F), p. 668: edge-set notation, supernodes, 𝓘(F), feasibility, basic and optimal solutions, laminar bases
-- statement:
--   Let $G=(V,E)$ be a finite simple graph and $F$ a forest on $V$ with $E(F)\cap E(G)=\varnothing$. For $S\subseteq V$ write $E(S)$ (resp. $F(S)$) for the edges of $E$ (resp. $F$) with both endpoints in $S$, $\delta(S)$ for the edges with exactly one endpoint in $S$, $\delta(v)=\delta(\{v\})$, and $x(D)=\sum_{e\in D}x_e$. The **supernodes** are the vertex sets of the connected components of $(V,F)$, isolated vertices included, and $\mathcal I(F)$ is the family of sets that are unions of supernodes. Given integer lower bounds $A_v$ on $U\subseteq V$ and upper bounds $B_v$ on $W\subseteq V$, LP-MBDCT$(G,\mathcal A,\mathcal B,U,W,F)$ is
--
--   $$
--   \begin{aligned}
--   \min\ & \textstyle\sum_{e\in E}c_e x_e\\
--   \text{s.t. } & x(E(V)) = |V|-|F(V)|-1,\\
--   & x(E(S)) \le |S|-|F(S)|-1 \quad (\varnothing\neq S\in\mathcal I(F)),\\
--   & x(\delta(v)) \ge A_v \quad (v\in U),\qquad x(\delta(v)) \le B_v \quad (v\in W),\\
--   & x_e\ge 0 \quad (e\in E).
--   \end{aligned}
--   $$
--
--   A feasible $x$ is **basic** if it is the only vector on $E$ that satisfies with equality every constraint tight at $x$ (including the tight rows $x_e=0$), and **optimal** if no feasible vector has smaller cost. A family of sets is **laminar** if no two members $X,Y$ have $X\cap Y$, $X-Y$, $Y-X$ all nonempty. The module also packages the conclusion of Lemma 5.3: sets $T_U\subseteq U$, $T_W\subseteq W$ and a nonempty laminar family $\mathcal L\subseteq\mathcal I(F)$ whose tight rows have $x^*$ restricted to the support $E^*$ as unique solution, whose characteristic vectors $\chi_{E(S)}$ ($S\in\mathcal L$), $\chi_{\delta(v)}$ ($v\in T_U$), $\chi_{\delta(v)}$ ($v\in T_W$) are linearly independent in $\mathbb R^{E^*}$, and with $|E^*|=|\mathcal L|+|T_U|+|T_W|$.
--
--   These are the objects every statement of the mission is about.
--
--   **Formalization Note** Edges are elements of `Sym2 V`; vectors are functions on `Sym2 V` that vanish off $E$. The subtour rows range over nonempty $S$: the literal row at $S=\varnothing$ reads $0\le -1$ and would make the LP empty. All right-hand sides are computed in $\mathbb R$, so there is no truncated subtraction. The independent family is indexed by $\mathcal L\sqcup T_U\sqcup T_W$, so a vertex in $T_U\cap T_W$ would repeat a vector; the paper's count $|E^*|=|\mathcal L|+|T_U|+|T_W|$ is the same reading.
-- source:
--   Singh, Lau, Approximating minimum bounded degree spanning trees to within one of optimal, STOC 2007, p. 668, the LP-MBDCT(G, 𝓐, 𝓑, U, W, F) display; p. 665, F-trees, supernodes and 𝓘(F); p. 663, basic solutions and laminar families; p. 668, Lemma 5.3 (conclusion)

import Mathlib
import Definitions.Def_BoundedDegreeST_PlusOne_LP

namespace BoundedDegreeST.LowerUpper

/-- The supernode of `v`: the vertex set of the connected component of `v` in
the graph `(V, F)`, as a finite set (a singleton when `v` is isolated in `F`). -/
noncomputable def supernodeOf {V : Type*} [Fintype V] (F : Finset (Sym2 V)) (v : V) :
    Finset V := by
  classical
  exact Finset.univ.filter
    (fun w => (SimpleGraph.fromEdgeSet (↑F : Set (Sym2 V))).Reachable v w)

/-- `C(F)`: all supernodes of `F`, including singleton components. -/
noncomputable def supernodes {V : Type*} [Fintype V] [DecidableEq V]
    (F : Finset (Sym2 V)) : Finset (Finset V) :=
  Finset.univ.image (supernodeOf F)

/-- `S ∈ 𝓘(F)`: `S` is a union of supernodes, i.e. every component of `F`
lies inside `S` or is disjoint from `S`. -/
def Compatible {V : Type*} [Fintype V] [DecidableEq V]
    (F : Finset (Sym2 V)) (S : Finset V) : Prop :=
  ∀ C ∈ supernodes F, C ⊆ S ∨ Disjoint C S

/-- `E(S)` (or `F(S)`): the edges of `E` with both endpoints in `S`. -/
noncomputable def internal {V : Type*} (E : Finset (Sym2 V))
    (S : Finset V) : Finset (Sym2 V) := by
  classical
  exact E.filter (fun e => ∀ v ∈ e, v ∈ S)

/-- `δ_E(S)`: the edges of `E` with exactly one endpoint in `S`. -/
noncomputable def cut {V : Type*} (E : Finset (Sym2 V))
    (S : Finset V) : Finset (Sym2 V) := by
  classical
  exact E.filter (fun e => (∃ v ∈ e, v ∈ S) ∧ ∃ w ∈ e, w ∉ S)

/-- `deg_E(v)`: the number of edges of `E` incident to `v`. -/
noncomputable def degree {V : Type*} (E : Finset (Sym2 V)) (v : V) : ℕ := by
  classical
  exact (E.filter (fun e => v ∈ e)).card

/-- Feasibility for LP-MBDCT(G, 𝓐, 𝓑, U, W, F) (p. 668):
`x(E(V)) = |V| − |F(V)| − 1`, `x(E(S)) ≤ |S| − |F(S)| − 1` for nonempty
`S ∈ 𝓘(F)`, `x(δ(v)) ≥ A_v` on `U`, `x(δ(v)) ≤ B_v` on `W`, `x ≥ 0`.
Right-hand sides are computed in `ℝ`. -/
def Feasible {V : Type*} [Fintype V] [DecidableEq V]
    (E : Finset (Sym2 V)) (A B : V → ℤ) (U W : Finset V)
    (F : Finset (Sym2 V)) (x : Sym2 V → ℝ) : Prop :=
  BoundedDegreeST.PlusOne.Supported E x ∧
  BoundedDegreeST.PlusOne.edgeSum x (internal E Finset.univ) =
    (Fintype.card V : ℝ) - ((internal F Finset.univ).card : ℝ) - 1 ∧
  (∀ S : Finset V, S.Nonempty → Compatible F S →
    BoundedDegreeST.PlusOne.edgeSum x (internal E S) ≤ (S.card : ℝ) - ((internal F S).card : ℝ) - 1) ∧
  (∀ v ∈ U, (A v : ℝ) ≤ BoundedDegreeST.PlusOne.edgeSum x (cut E {v})) ∧
  (∀ v ∈ W, BoundedDegreeST.PlusOne.edgeSum x (cut E {v}) ≤ (B v : ℝ)) ∧
  ∀ e ∈ E, 0 ≤ x e

/-- A basic feasible solution (p. 663): `x` is feasible and is the unique vector
supported on `E` satisfying with equality every constraint tight at `x`
(the equality row, the tight subtour rows, the tight lower- and upper-degree
rows, and the tight nonnegativity rows `x_e = 0`). -/
def Basic {V : Type*} [Fintype V] [DecidableEq V]
    (E : Finset (Sym2 V)) (A B : V → ℤ) (U W : Finset V)
    (F : Finset (Sym2 V)) (x : Sym2 V → ℝ) : Prop :=
  Feasible E A B U W F x ∧
  ∀ y : Sym2 V → ℝ, BoundedDegreeST.PlusOne.Supported E y →
    BoundedDegreeST.PlusOne.edgeSum y (internal E Finset.univ) =
      (Fintype.card V : ℝ) - ((internal F Finset.univ).card : ℝ) - 1 →
    (∀ S : Finset V, S.Nonempty → Compatible F S →
      BoundedDegreeST.PlusOne.edgeSum x (internal E S) = (S.card : ℝ) - ((internal F S).card : ℝ) - 1 →
      BoundedDegreeST.PlusOne.edgeSum y (internal E S) = (S.card : ℝ) - ((internal F S).card : ℝ) - 1) →
    (∀ v ∈ U, BoundedDegreeST.PlusOne.edgeSum x (cut E {v}) = (A v : ℝ) →
      BoundedDegreeST.PlusOne.edgeSum y (cut E {v}) = (A v : ℝ)) →
    (∀ v ∈ W, BoundedDegreeST.PlusOne.edgeSum x (cut E {v}) = (B v : ℝ) →
      BoundedDegreeST.PlusOne.edgeSum y (cut E {v}) = (B v : ℝ)) →
    (∀ e ∈ E, x e = 0 → y e = 0) → y = x

/-- An optimal solution: feasible, with BoundedDegreeST.PlusOne.cost no larger than every feasible BoundedDegreeST.PlusOne.cost. -/
def Optimal {V : Type*} [Fintype V] [DecidableEq V]
    (c : Sym2 V → ℝ) (E : Finset (Sym2 V)) (A B : V → ℤ) (U W : Finset V)
    (F : Finset (Sym2 V)) (x : Sym2 V → ℝ) : Prop :=
  Feasible E A B U W F x ∧
  ∀ y, Feasible E A B U W F y → ∑ e ∈ E, c e * x e ≤ ∑ e ∈ E, c e * y e

/-- The support `E* = {e ∈ E : x_e ≠ 0}`. -/
noncomputable def support {V : Type*}
    (E : Finset (Sym2 V)) (x : Sym2 V → ℝ) : Finset (Sym2 V) := by
  classical
  exact E.filter (fun e => x e ≠ 0)

/-- The characteristic vector `χ_D ∈ ℝ^{E*}` of an edge set `D`, indexed by the
support `E*` of `x`. -/
noncomputable def indicatorOnSupport {V : Type*}
    (E : Finset (Sym2 V)) (x : Sym2 V → ℝ)
    (D : Finset (Sym2 V)) : {e : Sym2 V // e ∈ support E x} → ℝ := by
  classical
  exact fun e => if e.val ∈ D then 1 else 0

/-- The conclusion of Lemma 5.3 (p. 668): `T_U ⊆ U`, `T_W ⊆ W` and a nonempty
laminar family `𝓛 ⊆ 𝓘(F)` of nonempty sets such that the rows
`x(δ(v)) = A_v` (`v ∈ T_U`), `x(δ(v)) = B_v` (`v ∈ T_W`),
`x(E(S)) = |S| − |F(S)| − 1` (`S ∈ 𝓛`) hold at `x`, `x` restricted to `E*` is
their unique solution in `ℝ^{E*}`, the vectors `χ_{E(S)}`, `χ_{δ(v)}`, `χ_{δ(v)}`
indexed by `𝓛 ⊕ T_U ⊕ T_W` are linearly independent in `ℝ^{E*}`, and
`|E*| = |𝓛| + |T_U| + |T_W|`. -/
def DefinesBasis {V : Type*} [Fintype V] [DecidableEq V]
    (E : Finset (Sym2 V)) (A B : V → ℤ) (U W : Finset V)
    (F : Finset (Sym2 V)) (x : Sym2 V → ℝ)
    (L : Finset (Finset V)) (TU TW : Finset V) : Prop :=
  L.Nonempty ∧ BoundedDegreeST.PlusOne.Laminar L ∧
  (∀ S ∈ L, S.Nonempty ∧ Compatible F S) ∧ TU ⊆ U ∧ TW ⊆ W ∧
  (∀ v ∈ TU, BoundedDegreeST.PlusOne.edgeSum x (cut E {v}) = (A v : ℝ)) ∧
  (∀ v ∈ TW, BoundedDegreeST.PlusOne.edgeSum x (cut E {v}) = (B v : ℝ)) ∧
  (∀ S ∈ L, BoundedDegreeST.PlusOne.edgeSum x (internal E S) =
      (S.card : ℝ) - ((internal F S).card : ℝ) - 1) ∧
  (∀ y : {e : Sym2 V // e ∈ support E x} → ℝ,
    (∀ v ∈ TU, (∑ e, indicatorOnSupport E x (cut E {v}) e * y e) = (A v : ℝ)) →
    (∀ v ∈ TW, (∑ e, indicatorOnSupport E x (cut E {v}) e * y e) = (B v : ℝ)) →
    (∀ S ∈ L, (∑ e, indicatorOnSupport E x (internal E S) e * y e) =
      (S.card : ℝ) - ((internal F S).card : ℝ) - 1) →
    y = fun e => x e.val) ∧
  LinearIndependent ℝ
    (fun i : {S : Finset V // S ∈ L} ⊕ ({v : V // v ∈ TU} ⊕ {v : V // v ∈ TW}) =>
      match i with
      | .inl S => indicatorOnSupport E x (internal E S.val)
      | .inr (.inl v) => indicatorOnSupport E x (cut E {v.val})
      | .inr (.inr v) => indicatorOnSupport E x (cut E {v.val})) ∧
  (support E x).card = L.card + TU.card + TW.card

end BoundedDegreeST.LowerUpper


