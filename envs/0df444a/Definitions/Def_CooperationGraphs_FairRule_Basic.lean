-- Prove2me | Definitions.Def_CooperationGraphs_FairRule_Basic
-- name    : CooperationGraphs_FairRule_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:22:21.600997+00:00
-- url     : https://prove2.me/theorems/518fafcf-0766-4cb0-ba6c-a64e0abac03a
-- title:
--   Cooperation graphs, the partition $S/g$, the graph-restricted game $v/g$, fair and totally stable allocation rules, superadditivity, games in graph function form
-- statement:
--   This module sets up the objects of Myerson's *Graphs and Cooperation in Games* (1976).
--
--   1. **Players and games.** The set of players is a nonempty finite set $N$; a **coalition** is a nonempty subset $S \subseteq N$, and $CL$ is the set of coalitions. A **game in characteristic function form** is a vector $v \in \mathbb R^{CL}$; $v_S$ is the transferable wealth coalition $S$ can divide if it forms.
--   2. **Graphs.** A **link** $n{:}m$ is an unordered pair of distinct players, and a **graph** $g$ on $N$ is a set of links; $\bar g^N$ is the complete graph and $GR$ the set of all graphs. $g\setminus n{:}m$ is $g$ with the link $n{:}m$ removed, and $|g|$ is the number of links of $g$.
--   3. **Connectedness and $S/g$.** Players $a,b$ are **connected in $S$ by $g$** if $a=b\in S$ or there is a path $a=n^0,n^1,\dots,n^k=b$ of links of $g$ all of whose vertices lie in $S$. The classes of this equivalence relation form a partition $S/g$ of $S$; $N/g$ is the set of connected components of $g$.
--   4. **The graph-restricted game.** For $v\in\mathbb R^{CL}$ and $g\in GR$,
--   $$(v/g)_S=\sum_{T\in S/g} v_T\qquad(S\in CL).$$
--   5. **Allocation rules.** A function $Y:GR\to\mathbb R^N$ is an **allocation rule** for $v$ if $\sum_{n\in S}Y_n(g)=v_S$ for every $g$ and every $S\in N/g$ (condition (7)); it is **equitable** if $Y_n(g)-Y_n(g\setminus n{:}m)=Y_m(g)-Y_m(g\setminus n{:}m)$ for every $g$ and every link $n{:}m\in g$ (condition (10)); it is a **fair allocation rule** for $v$ if it satisfies both. $Y$ is **totally stable** if $Y_n(g)\ge Y_n(g\setminus n{:}m)$ for every $g$ and every link $n{:}m\in g$ (condition (9)).
--   6. **Superadditivity.** $v$ is **superadditive** if $v_{S\cup T}\ge v_S+v_T$ for all disjoint $S,T\in CL$ (condition (12)).
--   7. **The Shapley value** $\varphi:\mathbb R^{CL}\to\mathbb R^N$ (Shapley 1953), $\varphi_n(v)=\sum_{S\subseteq N\setminus n}\frac{|S|!\,(|N|-|S|-1)!}{|N|!}\,(v_{S\cup n}-v_S)$ with $v_\emptyset=0$.
--   8. **Auxiliary quantities of the proofs.** For a rule $Y$, $t_n(g)=\sum_{h\subset g}(-1)^{|g|+|h|+1}Y_n(h)$ with $h\subset g$ a strict subgraph (display (18a)); for a component $S$ of $g$, the game $u^S_T=\sum_{R\in(T\cap S)/g}v_R$ (proof of Theorem 2).
--   9. **Games in graph function form.** A set $W\subseteq\mathbb R^S$ is **comprehensive** if $a\in W$ and $b\le a$ coordinatewise imply $b\in W$, and **proper** if $\emptyset\ne W\ne\mathbb R^S$. An **embedded subgraph** is a pair $(S,g)$ with $S\in N/g$. A **game in graph function form** assigns to every embedded subgraph a closed, comprehensive, proper subset $w(S,g)\subseteq\mathbb R^S$. A rule $Y$ satisfies the efficiency condition (14) if $(Y_n(g))_{n\in S}\in\partial w(S,g)$, the boundary of $w(S,g)$ in $\mathbb R^S$, for every $g$ and $S\in N/g$.
--
--   These are the objects of the paper's four theorems: the existence and uniqueness of the fair allocation rule (Theorems 1 and 4), its formula $Y(g)=\varphi(v/g)$ (Theorem 2), and its total stability for superadditive games (Theorem 3).
--
--   **Formalization Note.** Players are `Fin n` (the paper's player $k$ is index $k-1$); graphs are `SimpleGraph (Fin n)`, so $\bar g^N$ is `⊤`, the empty graph is `⊥`, $h\subseteq g$ is `h ≤ g`, $h\subset g$ is `h < g`, and $|g|$ is the cardinality of the edge set. A game is a function `Finset (Fin n) → ℝ`; its value at $\emptyset$ is a junk coordinate that none of the definitions reads ($S/g$ has only nonempty blocks, superadditivity quantifies over nonempty coalitions, and the Shapley value is the platform's `Supermodularity.Cooperative.ShapleyValue` applied after resetting the value at $\emptyset$ to $0$). The paper states connectedness asking $n^i\in S$ only for $i=1,\dots,k$; we require every vertex of the path, including $n^0$, to lie in $S$, which is what makes $S/g$ the partition of $S$ the paper says it is. $\mathbb R^S$ is the function space `↥S → ℝ` with its product (Euclidean) topology, and $\partial$ is the topological frontier. The paper's comprehensiveness prints "$\forall n\in N$" for the coordinates; we read $n\in S$, the only coordinates of $\mathbb R^S$. A game in graph function form is a family $w(g,S)$ defined for all pairs, constrained only on embedded subgraphs; values off them are never read.
-- source:
--   Myerson, Graphs and Cooperation in Games, Discussion Paper No. 246 (Sept. 1976), §2–§4 and §6, displays (1)–(5), (7), (9)–(12), (14), pp. 2–10; (18a) and u^S, pp. 11–12; Shapley value (19), p. 13

import Mathlib
import Definitions.Def_CooperationGraphs_FairRule_Game
import Definitions.Def_Supermodularity_Cooperative_ShapleyValue

namespace CooperationGraphs.FairRule

open Finset
open scoped Classical

/-- A candidate allocation rule `Y : GR → ℝ^N` (§3). A graph on `N` (a set of links, i.e. unordered
pairs of distinct players) is a `SimpleGraph (Fin n)`; `Y g i` is player `i`'s payoff `Y_i(g)`. -/
abbrev Rule (n : ℕ) := SimpleGraph (Fin n) → Fin n → ℝ

/-- `g \ a,b`: the graph `g` with the link `a,b` removed (§2, (4)). -/
def removeLink {n : ℕ} (g : SimpleGraph (Fin n)) (a b : Fin n) : SimpleGraph (Fin n) :=
  g.deleteEdges {s(a, b)}

/-- `a` and `b` are connected in `S` by `g` (§2): `a = b ∈ S`, or there is a path from `a` to `b`
along links of `g` all of whose vertices lie in `S`. (Read with both endpoints in `S`, as needed
for `S/g` to be a partition of `S`.) -/
def ConnectedIn {n : ℕ} (g : SimpleGraph (Fin n)) (S : Finset (Fin n)) (a b : Fin n) : Prop :=
  a ∈ S ∧ b ∈ S ∧ Relation.ReflTransGen (fun x y => x ∈ S ∧ y ∈ S ∧ g.Adj x y) a b

/-- `S/g` (§2, (5)): the partition of `S` into the classes of players connected in `S` by `g`.
`N/g`, the set of connected components of `g`, is `quot Finset.univ g`. -/
noncomputable def quot {n : ℕ} (S : Finset (Fin n)) (g : SimpleGraph (Fin n)) :
    Finset (Finset (Fin n)) :=
  S.image (fun j => S.filter (fun i => ConnectedIn g S i j))

/-- The graph-restricted game `v/g` (§4, (11)): `(v/g)_S = ∑_{T ∈ S/g} v_T`. -/
noncomputable def restrict {n : ℕ} (v : Game n) (g : SimpleGraph (Fin n)) : Game n :=
  fun S => ∑ T ∈ quot S g, v T

/-- The Shapley value operator `φ : ℝ^CL → ℝ^N` (Theorem 2, (19)): the platform's
`Supermodularity.Cooperative.ShapleyValue`, applied to `v` with its junk `∅` coordinate set to `0`. -/
noncomputable def shapley {n : ℕ} (v : Game n) : Fin n → ℝ :=
  Supermodularity.Cooperative.ShapleyValue (Function.update v ∅ 0)

/-- Condition (7): `Y` is an allocation rule for `v` — on every connected component `S ∈ N/g`
of every graph `g`, the payoffs sum to `v_S`. -/
def IsAllocationRule {n : ℕ} (v : Game n) (Y : Rule n) : Prop :=
  ∀ g : SimpleGraph (Fin n), ∀ S ∈ quot univ g, ∑ i ∈ S, Y g i = v S

/-- The equity condition (10): for every graph `g` and every link `a,b ∈ g`,
`Y_a(g) − Y_a(g \ a,b) = Y_b(g) − Y_b(g \ a,b)`. -/
def IsEquitable {n : ℕ} (Y : Rule n) : Prop :=
  ∀ (g : SimpleGraph (Fin n)) (a b : Fin n), g.Adj a b →
    Y g a - Y (removeLink g a b) a = Y g b - Y (removeLink g a b) b

/-- A fair allocation rule for `v` (§4): conditions (7) and (10). -/
def IsFair {n : ℕ} (v : Game n) (Y : Rule n) : Prop :=
  IsAllocationRule v Y ∧ IsEquitable Y

/-- Total stability (9): for every graph `g` and link `a,b ∈ g`, `Y_a(g) ≥ Y_a(g \ a,b)`. -/
def IsTotallyStable {n : ℕ} (Y : Rule n) : Prop :=
  ∀ (g : SimpleGraph (Fin n)) (a b : Fin n), g.Adj a b → Y (removeLink g a b) a ≤ Y g a

/-- Superadditivity (12), over nonempty disjoint coalitions `S, T ∈ CL`. -/
def IsSuperadditive {n : ℕ} (v : Game n) : Prop :=
  ∀ S T : Finset (Fin n), S.Nonempty → T.Nonempty → Disjoint S T → v S + v T ≤ v (S ∪ T)

/-- `|g|`, the number of links of `g` (§7, p. 11). -/
noncomputable def numLinks {n : ℕ} (g : SimpleGraph (Fin n)) : ℕ := g.edgeSet.ncard

/-- `t_i(g) = ∑_{h ⊂ g} (−1)^{|g|+|h|+1} Y_i(h)` (proof of Theorem 4, (18a)); `h ⊂ g` is strict. -/
noncomputable def altSum {n : ℕ} (Y : Rule n) (g : SimpleGraph (Fin n)) (i : Fin n) : ℝ :=
  ∑ h ∈ univ.filter (fun h : SimpleGraph (Fin n) => h < g),
    (-1 : ℝ) ^ (numLinks g + numLinks h + 1) * Y h i

/-- The game `u^S` of the proof of Theorem 2 (p. 12): `u^S_T = ∑_{R ∈ (T ∩ S)/g} v_R`. -/
noncomputable def uGame {n : ℕ} (v : Game n) (g : SimpleGraph (Fin n)) (S : Finset (Fin n)) :
    Game n :=
  fun T => ∑ R ∈ quot (T ∩ S) g, v R

/-- `W ⊆ ℝ^S` is comprehensive (§6, p. 10): `a ∈ W` and `b ≤ a` coordinatewise imply `b ∈ W`. -/
def IsComprehensive {n : ℕ} {S : Finset (Fin n)} (W : Set (↥S → ℝ)) : Prop :=
  ∀ a ∈ W, ∀ b : ↥S → ℝ, (∀ i, b i ≤ a i) → b ∈ W

/-- `W` is a proper subset of `ℝ^S` (§6, p. 10): `∅ ≠ W ≠ ℝ^S`. -/
def IsProperSubset {n : ℕ} {S : Finset (Fin n)} (W : Set (↥S → ℝ)) : Prop :=
  W.Nonempty ∧ W ≠ Set.univ

/-- A game in graph function form (§6, p. 10): for every embedded subgraph `(S, g)`
(`S ∈ N/g`), `w g S ⊆ ℝ^S` is closed, comprehensive and a proper subset of `ℝ^S`.
Values of `w g S` for `S ∉ N/g` are unconstrained and never read. -/
structure GraphFunctionGame (n : ℕ) where
  w : SimpleGraph (Fin n) → (S : Finset (Fin n)) → Set (↥S → ℝ)
  isClosed : ∀ g : SimpleGraph (Fin n), ∀ S ∈ quot univ g, IsClosed (w g S)
  comprehensive : ∀ g : SimpleGraph (Fin n), ∀ S ∈ quot univ g, IsComprehensive (w g S)
  proper : ∀ g : SimpleGraph (Fin n), ∀ S ∈ quot univ g, IsProperSubset (w g S)

/-- The efficiency condition (14): for every graph `g` and component `S ∈ N/g`,
`(Y_i(g))_{i ∈ S}` lies on the boundary `∂w(S,g)` of `w(S,g)` in `ℝ^S`. -/
def IsEfficientGF {n : ℕ} (G : GraphFunctionGame n) (Y : Rule n) : Prop :=
  ∀ g : SimpleGraph (Fin n), ∀ S ∈ quot univ g, (fun i : ↥S => Y g i) ∈ frontier (G.w g S)

end CooperationGraphs.FairRule


