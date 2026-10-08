-- Prove2me | Definitions.Def_EdgeTransBiCayley_BiAbelian_Setting
-- name    : EdgeTransBiCayley_BiAbelian_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T12:35:52.707725+00:00
-- url     : https://prove2.me/theorems/af4e9c5d-6a4d-43cb-91e1-a20ba5c99e9b
-- title:
--   pp. 1–5 — bi-Cayley data, graph, automorphisms and transitivity
-- statement:
--   Let $H$ be a finite group. A bi-Cayley datum consists of finite subsets $R,L,S\subseteq H$ with $R=R^{-1}$, $L=L^{-1}$, $1\notin R\cup L$, and $|R|=|L|$. It determines a graph on two labelled copies $H_0,H_1$ of $H$: vertices $h_0,(xh)_0$ are adjacent for $x\in R$; $h_1,(yh)_1$ are adjacent for $y\in L$; and $h_0,(zh)_1$ are adjacent for $z\in S$.
--
--   $$
--   \Gamma=\operatorname{BiCay}(H,R,L,S),\qquad R(H)=\{R(g):g\in H\},\quad h_i^{R(g)}=(hg)_i.
--   $$
--
--   The file also defines the normaliser $N_{\operatorname{Aut}(\Gamma)}(R(H))$ of $R(H)$ in the full automorphism group of $\Gamma$. For an automorphism $\alpha$ of $H$ and $x,y,g\in H$, display (2.1) of the paper defines two permutations of $H_0\cup H_1$,
--
--   $$
--   \delta_{\alpha,x,y}:\ h_0\mapsto (x\,h^{\alpha})_1,\ \ h_1\mapsto (y\,h^{\alpha})_0,\qquad \sigma_{\alpha,g}:\ h_0\mapsto (h^{\alpha})_0,\ \ h_1\mapsto (g\,h^{\alpha})_1,
--   $$
--
--   and display (2.2) singles out those satisfying
--
--   $$
--   \mathrm{I}:\ R^{\alpha}=x^{-1}Lx,\ L^{\alpha}=y^{-1}Ry,\ S^{\alpha}=y^{-1}S^{-1}x;\qquad \mathrm{F}:\ R^{\alpha}=R,\ L^{\alpha}=g^{-1}Lg,\ S^{\alpha}=g^{-1}S.
--   $$
--
--   A subgroup $K$ of $\operatorname{Aut}(\Gamma)$ is transitive on vertices if every vertex can be moved to every other by an element of $K$, on edges if every (unordered) edge can be moved to every other, and on arcs if every ordered pair of adjacent vertices can be moved to every other. The graph $\Gamma$ is vertex-, edge- or arc-transitive when the full group $\operatorname{Aut}(\Gamma)$ is. A semisymmetric graph has constant valency and is edge- but not vertex-transitive; a half-arc-transitive graph is vertex- and edge- but not arc-transitive (§2.1, p. 4). These definitions provide the shared vocabulary for this mission.
--
--   **Formalization Note** The vertex set is $H\sqcup H$, with `Sum.inl h` for $h_0$ and `Sum.inr h` for $h_1$; the adjacency relation is written directly (no symmetrisation), and its symmetry and looplessness come from $R=R^{-1}$, $L=L^{-1}$ and $1\notin R\cup L$. Valency is the graph degree. Automorphisms of $H$ are elements of `MulAut H` applied as functions ($h^{\alpha}$ is `α h`, $S^{\alpha}$ is the image of $S$); the conditions F and I are predicates on the parameters $(\alpha,g)$ and $(\alpha,x,y)$, and the permutations $\sigma,\delta$ are plain permutations of $H\sqcup H$, which are graph automorphisms exactly when these conditions hold.
-- source:
--   Conder, Zhou, Feng and Zhang, Edge-transitive bi-Cayley graphs, arXiv:1606.04625v1, pp. 1–5, §1–§2

import Mathlib
open Pointwise

namespace EdgeTransBiCayley.BiAbelian

/-- The data of `BiCay(H,R,L,S)` in §1, p. 1. -/
structure BiCayData (H : Type*) [Group H] [DecidableEq H] where
  R : Finset H
  L : Finset H
  S : Finset H
  inv_R : R⁻¹ = R
  inv_L : L⁻¹ = L
  one_notMem_R : (1 : H) ∉ R
  one_notMem_L : (1 : H) ∉ L
  card_R_eq_card_L : R.card = L.card

private theorem inv_mem_iff {H : Type*} [Group H] [DecidableEq H]
    (A : Finset H) (hA : A⁻¹ = A) (x : H) : x⁻¹ ∈ A ↔ x ∈ A := by
  calc
    x⁻¹ ∈ A ↔ x⁻¹ ∈ A⁻¹ := by rw [hA]
    _ ↔ x ∈ A := by simp

/-- The two copies of `H` have internal edges from `R,L` and cross edges from `S`. -/
def BiCayData.graph {H : Type*} [Group H] [DecidableEq H] (D : BiCayData H) :
    SimpleGraph (H ⊕ H) where
  Adj
    | .inl h, .inl h' => h' * h⁻¹ ∈ D.R
    | .inr h, .inr h' => h' * h⁻¹ ∈ D.L
    | .inl h, .inr h' => h' * h⁻¹ ∈ D.S
    | .inr h, .inl h' => h * h'⁻¹ ∈ D.S
  symm := by
    constructor
    intro a b hab
    cases a with
    | inl a =>
      cases b with
      | inl b =>
        change a * b⁻¹ ∈ D.R
        change b * a⁻¹ ∈ D.R at hab
        rw [← inv_mem_iff D.R D.inv_R (b * a⁻¹)] at hab
        simpa only [mul_inv_rev, inv_inv] using hab
      | inr b => exact hab
    | inr a =>
      cases b with
      | inl b => exact hab
      | inr b =>
        change a * b⁻¹ ∈ D.L
        change b * a⁻¹ ∈ D.L at hab
        rw [← inv_mem_iff D.L D.inv_L (b * a⁻¹)] at hab
        simpa only [mul_inv_rev, inv_inv] using hab
  loopless := by
    constructor
    intro a haa
    cases a with
    | inl a =>
      change a * a⁻¹ ∈ D.R at haa
      exact D.one_notMem_R (by simpa using haa)
    | inr a =>
      change a * a⁻¹ ∈ D.L at haa
      exact D.one_notMem_L (by simpa using haa)

instance {H : Type*} [Group H] [DecidableEq H] (D : BiCayData H) :
    DecidableRel D.graph.Adj := by
  intro a b
  cases a <;> cases b <;> dsimp [BiCayData.graph] <;> infer_instance

/-- Right multiplication by `g`, the paper's `R(g)`. -/
def rightMulPerm {H : Type*} [Group H] (g : H) : Equiv.Perm (H ⊕ H) where
  toFun := fun v => match v with
    | .inl h => .inl (h * g)
    | .inr h => .inr (h * g)
  invFun := fun v => match v with
    | .inl h => .inl (h * g⁻¹)
    | .inr h => .inr (h * g⁻¹)
  left_inv := by intro v; cases v <;> simp [mul_assoc]
  right_inv := by intro v; cases v <;> simp [mul_assoc]

/-- `R(g)` as an automorphism of the bi-Cayley graph. -/
def rightMul {H : Type*} [Group H] [DecidableEq H] (D : BiCayData H) (g : H) :
    D.graph ≃g D.graph where
  toEquiv := rightMulPerm g
  map_rel_iff' := by
    intro a b
    cases a <;> cases b <;>
      simp only [BiCayData.graph, rightMulPerm, Equiv.coe_fn_mk] <;>
      congr 1 <;> group

/-- The right regular subgroup `R(H)`. -/
def RH {H : Type*} [Group H] [DecidableEq H] (D : BiCayData H) :
    Subgroup (D.graph ≃g D.graph) := Subgroup.closure (Set.range (rightMul D))

/-- The normaliser `N_{Aut(Γ)}(R(H))`. -/
def normRH {H : Type*} [Group H] [DecidableEq H] (D : BiCayData H) :
    Subgroup (D.graph ≃g D.graph) := Subgroup.normalizer (RH D : Set (D.graph ≃g D.graph))

/-- The permutation `σ_{α,g}` from (2.1). -/
def sigmaPerm {H : Type*} [Group H] (α : MulAut H) (g : H) : Equiv.Perm (H ⊕ H) where
  toFun := fun v => match v with
    | .inl h => .inl (α h)
    | .inr h => .inr (g * α h)
  invFun := fun v => match v with
    | .inl h => .inl (α.symm h)
    | .inr h => .inr (α.symm (g⁻¹ * h))
  left_inv := by intro v; cases v <;> simp [mul_assoc]
  right_inv := by intro v; cases v <;> simp [mul_assoc]

/-- The permutation `δ_{α,x,y}` from (2.1). -/
def deltaPerm {H : Type*} [Group H] (α : MulAut H) (x y : H) : Equiv.Perm (H ⊕ H) where
  toFun := fun v => match v with
    | .inl h => .inr (x * α h)
    | .inr h => .inl (y * α h)
  invFun := fun v => match v with
    | .inl h => .inr (α.symm (y⁻¹ * h))
    | .inr h => .inl (α.symm (x⁻¹ * h))
  left_inv := by intro v; cases v <;> simp [mul_assoc]
  right_inv := by intro v; cases v <;> simp [mul_assoc]

/-- The condition defining membership in `F` in (2.2). -/
def IsF {H : Type*} [Group H] [DecidableEq H] (D : BiCayData H)
    (α : MulAut H) (g : H) : Prop :=
  D.R.image α = D.R ∧
  D.L.image α = (g⁻¹ • D.L) * ({g} : Finset H) ∧
  D.S.image α = g⁻¹ • D.S

/-- The condition defining membership in `I` in (2.2). -/
def IsI {H : Type*} [Group H] [DecidableEq H] (D : BiCayData H)
    (α : MulAut H) (x y : H) : Prop :=
  D.R.image α = (x⁻¹ • D.L) * ({x} : Finset H) ∧
  D.L.image α = (y⁻¹ • D.R) * ({y} : Finset H) ∧
  D.S.image α = (y⁻¹ • D.S⁻¹) * ({x} : Finset H)

/-- A subgroup acts transitively on the vertices. -/
def IsVertexTransitiveOn {V : Type*} (G : SimpleGraph V)
    (K : Subgroup (G ≃g G)) : Prop :=
  ∀ u v : V, ∃ φ ∈ K, φ u = v

/-- A subgroup acts transitively on the undirected edges. -/
def IsEdgeTransitiveOn {V : Type*} (G : SimpleGraph V)
    (K : Subgroup (G ≃g G)) : Prop :=
  ∀ e ∈ G.edgeSet, ∀ e' ∈ G.edgeSet, ∃ φ ∈ K, Sym2.map φ e = e'

/-- A subgroup acts transitively on directed edges. -/
def IsArcTransitiveOn {V : Type*} (G : SimpleGraph V)
    (K : Subgroup (G ≃g G)) : Prop :=
  ∀ u v u' v', G.Adj u v → G.Adj u' v' →
    ∃ φ ∈ K, φ u = u' ∧ φ v = v'

/-- Graph-level vertex transitivity uses the full automorphism group. -/
def IsVertexTransitive {V : Type*} (G : SimpleGraph V) : Prop :=
  IsVertexTransitiveOn G ⊤

/-- Graph-level edge transitivity uses the full automorphism group. -/
def IsEdgeTransitive {V : Type*} (G : SimpleGraph V) : Prop :=
  IsEdgeTransitiveOn G ⊤

/-- Graph-level arc transitivity uses the full automorphism group. -/
def IsArcTransitive {V : Type*} (G : SimpleGraph V) : Prop :=
  IsArcTransitiveOn G ⊤

/-- Constant valency, edge transitive, but not vertex transitive. -/
def IsSemisymmetric {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  (∃ d : ℕ, ∀ v : V, G.degree v = d) ∧
    IsEdgeTransitive G ∧ ¬ IsVertexTransitive G

/-- Vertex and edge transitive, but not arc transitive. -/
def IsHalfArcTransitive {V : Type*} (G : SimpleGraph V) : Prop :=
  IsVertexTransitive G ∧ IsEdgeTransitive G ∧ ¬ IsArcTransitive G

end EdgeTransBiCayley.BiAbelian


