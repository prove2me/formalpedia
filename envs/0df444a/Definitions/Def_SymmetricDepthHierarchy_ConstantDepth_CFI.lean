-- Prove2me | Definitions.Def_SymmetricDepthHierarchy_ConstantDepth_CFI
-- name    : SymmetricDepthHierarchy_ConstantDepth_CFI
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T04:31:00.245093+00:00
-- url     : https://prove2.me/theorems/9aea7278-a991-4a00-92fc-0db3080f9628
-- title:
--   Homomorphism counts, CFI graphs $G_W$ and $\widehat G_i$, $\gamma(G)$, bipartite graphs, $\mathrm{hom}_{\mathrm{bip}}$, $B(H)$ and $F/\mathcal R$
-- statement:
--   $\mathrm{hom}(F,G)$ is the number of homomorphisms from $F$ to $G$.
--
--   **CFI graphs.** For a connected graph $G$ and $v\in V(G)$ let $E(v)$ be the set of edges incident to $v$. For $W\in\mathbb Z_2^{V(G)}$ the graph $G_W$ has vertices $(v,T)$ with $v\in V(G)$, $T\in\mathbb Z_2^{E(v)}$ and $\sum_{e\in E(v)}T(e)=W(v)$; $(u,S)$ and $(v,T)$ are adjacent if $uv\in E(G)$ and $S(uv)=T(uv)$. $G_0$ and $G_1$ are the graphs for even and odd total weight $\sum_vW(v)$. The graph $\widehat G_i$ is obtained from $G_i$ by adding all edges $(u,S)(v,T)$ for distinct non-adjacent $u,v\in V(G)$. Further
--   $$\gamma(G)=\sum_{v\in V(G)}2^{\deg_G(v)-1}.$$
--
--   **Bipartite graphs.** For bipartite graphs $F$ and $B$ with fixed bipartitions, $\mathrm{hom}_{\mathrm{bip}}(F,B)$ is the number of homomorphisms $F\to B$ mapping the left side of $F$ to the left side of $B$ and the right side to the right side. For a simple graph $H$, $B(H)$ has left side $V(H)\times\{0\}$, right side $V(H)\times\{1\}$, and $(u,0)\sim(v,1)$ iff $u=v$ or $uv\in E(H)$.
--
--   **Quotients.** $\Gamma(F)$ is the set of partitions $\mathcal R$ of $V(F)$ such that $F[R]$ is connected for all $R\in\mathcal R$; $F/\mathcal R$ has vertex set $\mathcal R$, two distinct parts adjacent iff an edge of $F$ joins them.
--
--   These objects carry the lower-bound argument behind Theorem 3.7.
--
--   **Formalization Note.** $G_1$ is taken with the weight $W=\mathbb 1_{v_0}$ at a vertex $v_0$ chosen by the user of the definition; up to isomorphism $G_W$ depends only on $\sum_vW(v)$ [Rob26, Corollary 3.7]. Both sides of $B(H)$ are encoded by $V(H)$. $\gamma$ uses natural-number subtraction in the exponent; it is applied only to connected graphs with at least two vertices, where all degrees are positive.
-- source:
--   Anuj Dawar, Prateek Dwivedi, Benedikt Pago, Tim Seppelt, STOC 2027 submission #1521 (October 2026), §B.4.1, pp. 36–38 (PDF pp. 39–41)

import Mathlib

open scoped Classical

noncomputable section

namespace SymmetricDepthHierarchy.ConstantDepth

/-!
# Homomorphism counts, CFI graphs for non-induced minors, bipartite graphs and `B(H)`

STOC 2027 submission #1521, §B.4.1 (printed pp. 36–38, PDF pp. 39–41).

* `homCount F G = hom(F, G)`, the number of graph homomorphisms `F → G`.
* For a connected graph `G` and `W : V(G) → ℤ₂`, the CFI graph `G_W` has vertices `(v, T)` with
  `T : E(v) → ℤ₂`, `∑_{e ∈ E(v)} T(e) = W(v)`, where `E(v)` is the set of edges incident to `v`;
  `(u, S)` and `(v, T)` are adjacent iff `uv ∈ E(G)` and `S(uv) = T(uv)`.
  `G₀ = G_0` and `G₁ = G_W` for any `W` of odd total weight; here `G₁` is taken with the twist
  `W = 𝟙_{v₀}` at a chosen vertex `v₀` (up to isomorphism `G_W` depends only on `∑ W`,
  [Rob26, Corollary 3.7]).
* `Ĝᵢ` adds all edges `(u, S)(v, T)` for distinct non-adjacent `u, v ∈ V(G)`.
* `γ(G) = ∑_{v ∈ V(G)} 2^{deg_G(v) − 1}` (used only for connected `G` with at least two vertices,
  where every degree is positive).
* A bipartite graph with fixed bipartition is a `BipGraph`; `hombip(F, B)` counts the
  homomorphisms mapping left to left and right to right.
* `B(H)` has left side `V(H) × {0}`, right side `V(H) × {1}`, and `(u,0) ~ (v,1)` iff `u = v`
  or `uv ∈ E(H)`; both sides are encoded by `V(H)` itself.
* `Γ(F)` is the set of partitions of `V(F)` into parts inducing connected subgraphs, and `F/R`
  has one vertex per part, two distinct parts adjacent iff an edge of `F` joins them.
-/

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The number `hom(F, G)` of homomorphisms from `F` to `G`. -/
def homCount {X Y : Type} (F : SimpleGraph X) (G : SimpleGraph Y) : ℕ := Nat.card (F →g G)

/-- The vertices `(v, T)` of the CFI graph `G_W`: `T : E(v) → ℤ₂` with `∑_{e ∈ E(v)} T(e) = W(v)`. -/
def CFIVertex (G : SimpleGraph V) (W : V → ZMod 2) : Type :=
  Σ v : V, {T : G.incidenceSet v → ZMod 2 // ∑ e, T e = W v}

instance (G : SimpleGraph V) (W : V → ZMod 2) : Fintype (CFIVertex G W) := by
  unfold CFIVertex; infer_instance

/-- Adjacency in `G_W`: `(u, S) ~ (v, T)` iff `uv ∈ E(G)` and `S(uv) = T(uv)`. -/
def CFIAdj (G : SimpleGraph V) (W : V → ZMod 2) (x y : CFIVertex G W) : Prop :=
  ∃ h : G.Adj x.1 y.1,
    x.2.1 ⟨s(x.1, y.1), h, Sym2.mem_mk_left _ _⟩ = y.2.1 ⟨s(x.1, y.1), h, Sym2.mem_mk_right _ _⟩

/-- The CFI graph `G_W`. -/
def cfiGraph (G : SimpleGraph V) (W : V → ZMod 2) : SimpleGraph (CFIVertex G W) :=
  SimpleGraph.fromRel (CFIAdj G W)

/-- The modified CFI graph `Ĝ_W`: `G_W` plus all edges `(u, S)(v, T)` for distinct
non-adjacent `u, v ∈ V(G)`. -/
def cfiHat (G : SimpleGraph V) (W : V → ZMod 2) : SimpleGraph (CFIVertex G W) :=
  SimpleGraph.fromRel fun x y => CFIAdj G W x y ∨ (x.1 ≠ y.1 ∧ ¬ G.Adj x.1 y.1)

/-- The untwisted weight `W = 0` (giving `G₀`). -/
def twist0 : V → ZMod 2 := fun _ => 0

/-- The weight `W = 𝟙_{v₀}`, of odd total weight (giving `G₁`). -/
def twist1 (v₀ : V) : V → ZMod 2 := Pi.single v₀ 1

/-- `γ(G) = ∑_{v ∈ V(G)} 2^{deg_G(v) − 1}`. -/
def cfiSize (G : SimpleGraph V) : ℕ := ∑ v, 2 ^ (G.degree v - 1)

/-- A simple bipartite graph with fixed bipartition (left side `L`, right side `R`). -/
structure BipGraph where
  L : Type
  R : Type
  [fintypeL : Fintype L]
  [fintypeR : Fintype R]
  [decEqL : DecidableEq L]
  [decEqR : DecidableEq R]
  adj : L → R → Prop

attribute [instance] BipGraph.fintypeL BipGraph.fintypeR BipGraph.decEqL BipGraph.decEqR

namespace BipGraph

/-- The underlying simple graph on `L ⊕ R`. -/
def graph (F : BipGraph) : SimpleGraph (F.L ⊕ F.R) :=
  SimpleGraph.fromRel fun x y =>
    match x, y with
    | Sum.inl a, Sum.inr b => F.adj a b
    | _, _ => False

/-- `hombip(F, B)`: the number of homomorphisms `F → B` mapping the left side of `F` to the left
side of `B` and the right side of `F` to the right side of `B`. -/
def hombip (F B : BipGraph) : ℕ :=
  Nat.card {f : (F.L → B.L) × (F.R → B.R) // ∀ a b, F.adj a b → B.adj (f.1 a) (f.2 b)}

/-- `B(H)`: left side `V(H) × {0}`, right side `V(H) × {1}` (both encoded by `V(H)`), with
`(u, 0) ~ (v, 1)` iff `u = v` or `uv ∈ E(H)`. -/
def lift {X : Type} [Fintype X] [DecidableEq X] (H : SimpleGraph X) : BipGraph where
  L := X
  R := X
  adj u v := u = v ∨ H.Adj u v

end BipGraph

/-- `Γ(F)`: the partitions `R` of `V(F)` such that `F[R]` is connected for every part `R`. -/
def connectedPartitions (F : SimpleGraph V) : Finset (Finpartition (Finset.univ : Finset V)) :=
  Finset.univ.filter fun P => ∀ R ∈ P.parts, (F.induce (R : Set V)).Connected

/-- `F/R`: one vertex per part of `R`, two distinct parts adjacent iff an edge of `F` joins them. -/
def quotientGraph (F : SimpleGraph V) (P : Finpartition (Finset.univ : Finset V)) :
    SimpleGraph {R // R ∈ P.parts} :=
  SimpleGraph.fromRel fun R S => R ≠ S ∧ ∃ a ∈ R.1, ∃ b ∈ S.1, F.Adj a b

end SymmetricDepthHierarchy.ConstantDepth


