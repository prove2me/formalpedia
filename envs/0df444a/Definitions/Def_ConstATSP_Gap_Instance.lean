-- Prove2me | Definitions.Def_ConstATSP_Gap_Instance
-- name    : ConstATSP_Gap_Instance
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T01:46:33.340977+00:00
-- url     : https://prove2.me/theorems/bcd252dd-6ecd-4db1-8355-41ebb695f7b0
-- title:
--   Defs. 2.3, 2.5, 2.6, 3.1, 8.1, 9.1, 9.2, §3, §7.1, pp. 9–43 — laminarly-weighted instances, Subtour Partition Cover, lightness, irreducibility, vertebrate pairs, quasi-backbones
-- statement:
--   This file defines the instances on which the paper's algorithm operates and the notions in which its intermediate results are stated.
--
--   1. **Laminarly-weighted instance** (Def. 2.3). A tuple $I=(G,\mathcal L,x,y)$ where $G=(V,E)$ is a strongly connected digraph, $\mathcal L$ a laminar family of vertex sets, $x$ a feasible solution of LP$(G,0)$ with $x_e>0$ for every edge, every $S\in\mathcal L$ is **tight**: $x(\delta^+(S))=x(\delta^-(S))=1$, and $y:\mathcal L\to\mathbb R_{\ge0}$. The **induced weight** is
--   $$w_I(e)=\sum_{S\in\mathcal L:\ e\in\delta(S)}y_S ,$$
--   and $w_I(F)=\sum_e F(e)\,w_I(e)$ for an edge multiset $F$.
--   2. **Values and lower bounds** (Def. 2.6, §3, (5.1)). $\mathrm{value}_I(S)=2\sum_{R\in\mathcal L:\,R\subsetneq S}y_R$ and $\mathrm{value}(I)=\mathrm{value}_I(V)$, the Held–Karp lower bound of the instance. With $y_v=y_{\{v\}}$ if $\{v\}\in\mathcal L$ and $y_v=0$ otherwise, $\mathrm{lb}_I(U)=\sum_{v\in U}2y_v$, and $\mathrm{lb}_I(\bar B)=\mathrm{lb}_I(V\setminus V(B))$. $I$ is a **singleton instance** (Def. 2.5) if every set of $\mathcal L$ is a singleton.
--   3. **Subtour Partition Cover** (§3). Given $I$ and a subtour $B$, an input is a partition $(V_1,\dots,V_k)$ of $V\setminus V(B)$ into sets inducing strongly connected subgraphs. An algorithm is **$(\alpha,\beta)$-light** for $I$ and $B$ (Def. 3.1) if for every such partition it returns a collection $F$ of subtours with $|\delta^+_F(V_i)|\ge1$ for all $i$, such that $w_I(T)\le\alpha\,\mathrm{lb}(T)$ for every subtour $T$ in $F$ with $V(T)\cap V(B)=\emptyset$, and $w_I(F_B)\le\beta$, where $F_B$ consists of the subtours in $F$ that intersect $B$.
--   4. **Irreducibility** (§7.1, Def. 8.1). For $S\in\mathcal L$, $S_{\mathrm{in}}$ and $S_{\mathrm{out}}$ are the vertices of $S$ with an incoming edge from, resp. an outgoing edge to, $V\setminus S$; $d_S(u,v)$ is the least $w_I$-weight of a path inside $S$ from $u$ to $v$ ($\infty$ if none), and
--   $$D_S(u,v)=\sum_{R\in\mathcal L:\,u\in R\subsetneq S}y_R+d_S(u,v)+\sum_{R\in\mathcal L:\,v\in R\subsetneq S}y_R .$$
--   For a parameter $\delta$, $S$ is **irreducible** if $\max_{u\in S_{\mathrm{in}},v\in S_{\mathrm{out}}}D_S(u,v)\ge\delta\cdot\mathrm{value}(S)$, and $I$ is irreducible if every $S\in\mathcal L$ is.
--   5. **Vertebrate pairs and quasi-backbones** (Defs. 9.1, 9.2). $(I,B)$ is a vertebrate pair if $B$ is a subtour that visits every $S\in\mathcal L$ with $|S|\ge2$. A subtour $B$ is a quasi-backbone if $2\sum_{S\in\mathcal L^*}y_S\le(1-\delta)\,\mathrm{value}(I)$, where $\mathcal L^*$ is the set of $S\in\mathcal L$ with $S\cap V(B)=\emptyset$.
--
--   **Formalization Note** The instance requirements are collected in the predicate `Instance.IsValid`, which in addition requires $|V|\ge 2$: on one vertex Definition 2.1 admits no loop-free tour while LP$(G,0)$ is feasible, so every statement about all instances would fail or become vacuous there. Lightness is stated existentially (for every admissible partition a light $F$ exists). Partition parts are required to be nonempty and different from $V$; for $B\ne\emptyset$ this is automatic, and for $B=\emptyset$ the one-part partition $(V)$ admits no solution since $\delta^+(V)=\emptyset$. "A collection of subtours" is an Eulerian multiset, whose components are its subtours; a component meets $B$ if it shares a vertex with $V(B)$. Irreducibility of $S$ is stated without an infimum: some $u\in S_{\mathrm{in}}$, $v\in S_{\mathrm{out}}$ are such that every walk inside $S$ from $u$ to $v$ has $D$-weight at least $\delta\,\mathrm{value}(S)$; since $w_I\ge0$, least walk weight equals least path weight, and the absence of a walk gives $D_S=\infty$.
-- source:
--   Svensson, Tarnawski, Végh, A constant-factor approximation algorithm for the asymmetric traveling salesman problem, J. ACM 67(6) (2020), accepted manuscript (LSE Research Online 106582), pp. 9–43, Definition 2.3, Definition 2.5, Definition 2.6, §3 (lb, Subtour Partition Cover, Definition 3.1), (5.1) p. 16, §2 p. 7 (S_in, S_out), §7.1 p. 35 (d_S, D_S), Definition 8.1 p. 41, Definitions 9.1–9.2 p. 43

import Mathlib
import Definitions.Def_ConstATSP_Gap_Graph

namespace ConstATSP.Gap

/-- The data of a laminarly-weighted ATSP instance `I = (G, L, x, y)` (Def. 2.3, p. 9). Only the values
`y S` for `S ∈ L` are ever read. The requirements are in `Instance.IsValid`. -/
structure Instance (V E : Type) where
  /-- the digraph -/
  G : Graph V E
  /-- the laminar family -/
  L : Finset (Finset V)
  /-- the LP solution -/
  x : E → ℝ
  /-- the weights of the laminar sets -/
  y : Finset V → ℝ

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E]

/-- The requirements of Def. 2.3 (p. 9): `G` strongly connected, `L` laminar, `x` feasible for LP(G, 0),
`x_e > 0` for every edge, every `S ∈ L` tight (`x(δ⁺(S)) = x(δ⁻(S)) = 1`), `y ≥ 0` on `L`; plus the
disclosed pin `|V| ≥ 2`. -/
def Instance.IsValid (I : Instance V E) : Prop :=
  2 ≤ Fintype.card V ∧ IsStronglyConnected I.G ∧ IsLaminar I.L ∧ IsHeldKarpFeasible I.G I.x ∧
    (∀ e, 0 < I.x e) ∧
    (∀ S ∈ I.L, ∑ e ∈ outE I.G S, I.x e = 1 ∧ ∑ e ∈ inE I.G S, I.x e = 1) ∧
    (∀ S ∈ I.L, 0 ≤ I.y S)

open Classical in
/-- The induced weight `w_I(e) = ∑_{S ∈ L : e ∈ δ(S)} y_S` (Def. 2.3, p. 9). -/
noncomputable def Instance.w (I : Instance V E) (e : E) : ℝ :=
  ∑ S ∈ I.L.filter (fun S => e ∈ bdE I.G S), I.y S

/-- The weight `w_I(F) = ∑_e F(e) w_I(e)` of an edge multiset `F`. -/
noncomputable def Instance.wt (I : Instance V E) (F : E → ℕ) : ℝ :=
  ∑ e, (F e : ℝ) * I.w e

/-- `value_I(S) = 2 ∑_{R ∈ L : R ⊊ S} y_R` (Def. 2.6, p. 11). -/
def Instance.valueOf (I : Instance V E) (S : Finset V) : ℝ :=
  2 * ∑ R ∈ I.L.filter (fun R => R ⊂ S), I.y R

/-- `value(I) = value_I(V)`, the Held–Karp lower bound of the instance (Def. 2.6, p. 11). -/
def Instance.value (I : Instance V E) : ℝ :=
  I.valueOf Finset.univ

/-- `y_v`, extended to all singletons by `y_v = 0` if `{v} ∉ L` (§3, p. 12). -/
def Instance.yv (I : Instance V E) (v : V) : ℝ :=
  if {v} ∈ I.L then I.y {v} else 0

/-- `lb_I(U) = ∑_{v ∈ U} 2 y_v` (§3, p. 12). -/
def Instance.lb (I : Instance V E) (U : Finset V) : ℝ :=
  2 * ∑ v ∈ U, I.yv v

/-- `lb_I(B̄) = lb_I(V ∖ V(B))` ((5.1), p. 16). -/
def Instance.lbCompl (I : Instance V E) (B : E → ℕ) : ℝ :=
  I.lb (Finset.univ \ vertsOf I.G B)

/-- A singleton instance: every set of `L` is a singleton (Def. 2.5, p. 10). -/
def Instance.IsSingleton (I : Instance V E) : Prop :=
  ∀ S ∈ I.L, S.card = 1

/-- An admissible input partition of Subtour Partition Cover (§3, p. 12) for the subtour `B`:
nonempty, proper parts, pairwise disjoint, each inducing a strongly connected subgraph, covering exactly
`V ∖ V(B)`. -/
def IsSPCPartition (G : Graph V E) (B : E → ℕ) (P : Finset (Finset V)) : Prop :=
  (∀ U ∈ P, U.Nonempty ∧ U ≠ Finset.univ ∧ IsStronglyConnectedOn G U) ∧
    (∀ U ∈ P, ∀ U' ∈ P, U ≠ U' → Disjoint U U') ∧
    (∀ v, v ∉ vertsOf G B ↔ ∃ U ∈ P, v ∈ U)

/-- `(α, β)`-lightness for `I` and `B` (Def. 3.1, p. 13), read existentially: for every admissible
partition there is an Eulerian `F` with `|δ⁺_F(U)| ≥ 1` for every part, `w_I(T) ≤ α lb(T)` for every
subtour `T` in `F` (connected component) vertex-disjoint from `B`, and `w_I(F_B) ≤ β` for the union `F_B`
of the components of `F` meeting `V(B)`. -/
def IsLight (I : Instance V E) (B : E → ℕ) (α β : ℝ) : Prop :=
  ∀ P, IsSPCPartition I.G B P → ∃ F : E → ℕ, IsEulerian I.G F ∧
    (∀ U ∈ P, 1 ≤ ∑ e ∈ outE I.G U, F e) ∧
    (∀ v ∈ vertsOf I.G F, Disjoint (comp I.G F v) (vertsOf I.G B) →
        I.wt (restrictTo I.G F (comp I.G F v)) ≤ α * I.lb (comp I.G F v)) ∧
    I.wt (fun e => if Disjoint (comp I.G F (I.G.src e)) (vertsOf I.G B) then 0 else F e) ≤ β

/-- `S_in`: the vertices of `S` with an incoming edge from outside `S` (§2, p. 7). -/
def Sin (G : Graph V E) (S : Finset V) : Finset V :=
  S.filter (fun v => ∃ e, G.src e ∉ S ∧ G.tgt e = v)

/-- `S_out`: the vertices of `S` with an outgoing edge to outside `S` (§2, p. 7). -/
def Sout (G : Graph V E) (S : Finset V) : Finset V :=
  S.filter (fun v => ∃ e, G.src e = v ∧ G.tgt e ∉ S)

/-- `IsWalkIn G S u v p`: the list of edges `p` is a walk from `u` to `v` all of whose vertices lie in `S`. -/
def IsWalkIn (G : Graph V E) (S : Finset V) : V → V → List E → Prop
  | u, v, [] => u = v ∧ u ∈ S
  | u, v, e :: p => G.src e = u ∧ u ∈ S ∧ G.tgt e ∈ S ∧ IsWalkIn G S (G.tgt e) v p

/-- `S` is irreducible (Def. 8.1, p. 41; `D_S` from §7.1, p. 35):
`max_{u ∈ S_in, v ∈ S_out} D_S(u, v) ≥ δ value(S)`, where
`D_S(u, v) = ∑_{u ∈ R ⊊ S} y_R + d_S(u, v) + ∑_{v ∈ R ⊊ S} y_R` and `d_S(u, v)` is the least `w_I`-weight
of a path inside `S` (`∞` if none). Stated without an infimum: some `u ∈ S_in`, `v ∈ S_out` are such that
every walk inside `S` from `u` to `v` has `D`-weight at least `δ value(S)`. -/
def Instance.IsIrreducibleSet (I : Instance V E) (δ : ℝ) (S : Finset V) : Prop :=
  ∃ u ∈ Sin I.G S, ∃ v ∈ Sout I.G S, ∀ p, IsWalkIn I.G S u v p →
    δ * I.valueOf S ≤ (∑ R ∈ I.L.filter (fun R => u ∈ R ∧ R ⊂ S), I.y R) + (p.map I.w).sum +
      (∑ R ∈ I.L.filter (fun R => v ∈ R ∧ R ⊂ S), I.y R)

/-- The instance is irreducible: no set of `L` is reducible (Def. 8.1, p. 41). -/
def Instance.IsIrreducible (I : Instance V E) (δ : ℝ) : Prop :=
  ∀ S ∈ I.L, I.IsIrreducibleSet δ S

/-- `(I, B)` is a vertebrate pair (Def. 9.1, p. 43): `B` is a subtour visiting every `S ∈ L` with
`|S| ≥ 2`. -/
def Instance.IsVertebrate (I : Instance V E) (B : E → ℕ) : Prop :=
  IsSubtour I.G B ∧ ∀ S ∈ I.L, 2 ≤ S.card → ¬ Disjoint S (vertsOf I.G B)

/-- `B` is a quasi-backbone (Def. 9.2, p. 43): a subtour with `2 ∑_{S ∈ L*} y_S ≤ (1 − δ) value(I)`,
where `L* = {S ∈ L : S ∩ V(B) = ∅}`. -/
def Instance.IsQuasiBackbone (I : Instance V E) (δ : ℝ) (B : E → ℕ) : Prop :=
  IsSubtour I.G B ∧
    2 * ∑ S ∈ I.L.filter (fun S => Disjoint S (vertsOf I.G B)), I.y S ≤ (1 - δ) * I.value

end ConstATSP.Gap


