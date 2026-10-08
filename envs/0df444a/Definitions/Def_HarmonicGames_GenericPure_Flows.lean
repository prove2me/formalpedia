-- Prove2me | Definitions.Def_HarmonicGames_GenericPure_Flows
-- name    : HarmonicGames_GenericPure_Flows
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T05:42:32.328119+00:00
-- url     : https://prove2.me/theorems/209a2d29-084c-490a-a251-af849aa619d9
-- title:
--   Node functions $C_0$, edge flows $C_1$ with the inner products (7), and the combinatorial gradient $\delta_0$ (Section 3)
-- statement:
--   Let $\mathcal G = (E, A)$ be a finite simple undirected graph with node set $E$ and edge set $A$ (with $(p,q) \in A$ iff $(q,p) \in A$, and no loops).
--
--   1. $C_0 = \{ f : E \to \mathbb R \}$ is the space of functions on the nodes, with inner product $\langle \varphi_1, \varphi_2 \rangle_0 = \sum_{p \in E} \varphi_1(p)\varphi_2(p)$.
--   2. $C_1$ is the space of **edge flows**: functions $X : E \times E \to \mathbb R$ with $X(p,q) = -X(q,p)$ if $(p,q) \in A$ and $X(p,q) = 0$ otherwise (equation (5)). Its inner product is
--
--   $$
--   \langle X, Y \rangle_1 = \frac12 \sum_{(p,q) \in A} X(p,q)\,Y(p,q) ,
--   $$
--
--   the sum running over ordered pairs, so each undirected edge is counted once (equation (7)).
--   3. $W(p,q)$ is the $0/1$ indicator of $(p,q) \in A$ (equation (8)), and the **combinatorial gradient** $\delta_0 : C_0 \to C_1$ is
--
--   $$
--   (\delta_0 \varphi)(p,q) = W(p,q)\,\big(\varphi(q) - \varphi(p)\big) \qquad (9).
--   $$
--
--   The file also provides the gradient along the edges of a subgraph, $(p,q) \mapsto W_{\mathcal H}(p,q)(\varphi(q)-\varphi(p))$, used for the player-specific operators $D_m$.
--
--   These are the spaces and the operator on which the paper's decomposition of games is built; the adjoint $\delta_0^*$ (the negative divergence) is taken with respect to these inner products.
--
--   **Formalization Note** $C_0$ is `EuclideanSpace ℝ E`. $C_1$ is a type synonym of the subspace of edge flows inside $E \to E \to \mathbb R$, equipped with the inner product $\tfrac12\sum$ above (not the sup norm of the function space). The factor $\tfrac12$ matters: the adjoints of $\delta_0$ and $D_m$ depend on it.
-- source:
--   Candogan, Menache, Ozdaglar, Parrilo, Flows and Decompositions of Games: Harmonic and Potential Games, arXiv:1005.2405v2, p. 9, Section 3, equations (5), (7), (8), (9)

import Mathlib

/-!
Flows on an arbitrary finite simple graph `G` on a node set `V` (Section 3 of Candogan,
Menache, Ozdaglar, Parrilo): the node space `C0` and the edge-flow space `C1` with the inner
products (7), and the combinatorial gradient `δ0` (9).
-/

noncomputable section

namespace HarmonicGames.GenericPure

open scoped InnerProductSpace

set_option linter.unusedSectionVars false

/-- `C0 = {f : V → ℝ}`, with `⟨φ₁, φ₂⟩₀ = ∑_p φ₁(p) φ₂(p)` (7). -/
abbrev C0 (V : Type*) := EuclideanSpace ℝ V

section Graph

variable {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The edge-flow condition (5): `X(p,q) = -X(q,p)` if `(p,q)` is an edge, and
`X(p,q) = 0` otherwise. -/
def IsEdgeFlow (X : V → V → ℝ) : Prop :=
  ∀ p q, (G.Adj p q → X p q = -X q p) ∧ (¬ G.Adj p q → X p q = 0)

/-- The subspace of edge flows on `G`, inside `V → V → ℝ`. -/
def edgeFlows : Submodule ℝ (V → V → ℝ) where
  carrier := {X | IsEdgeFlow G X}
  add_mem' {X Y} hX hY p q :=
    ⟨fun h => by simp [(hX p q).1 h, (hY p q).1 h]; ring,
     fun h => by simp [(hX p q).2 h, (hY p q).2 h]⟩
  zero_mem' p q := ⟨fun _ => by simp, fun _ => by simp⟩
  smul_mem' c {X} hX p q :=
    ⟨fun h => by simp [(hX p q).1 h], fun h => by simp [(hX p q).2 h]⟩

/-- `C1`: the space of edge flows on `G` (5). A type synonym of the subspace `edgeFlows G`,
carrying the inner product `⟨X, Y⟩₁ = ½ ∑_{(p,q) ∈ A} X(p,q) Y(p,q)` of (7). -/
def C1 : Type _ := ↥(edgeFlows G)

instance : AddCommGroup (C1 G) := inferInstanceAs (AddCommGroup ↥(edgeFlows G))
instance : Module ℝ (C1 G) := inferInstanceAs (Module ℝ ↥(edgeFlows G))
/-- The underlying function `V → V → ℝ` of an edge flow. -/
instance : CoeFun (C1 G) (fun _ => V → V → ℝ) := ⟨fun X => (X : ↥(edgeFlows G)).1⟩

/-- The inner product (7) on `C1`: `⟨X, Y⟩₁ = ½ ∑_{(p,q) ∈ A} X(p,q) Y(p,q)`. -/
def innerC1 (X Y : C1 G) : ℝ :=
  (1 / 2 : ℝ) * ∑ p, ∑ q, if G.Adj p q then X p q * Y p q else 0

instance coreC1 : InnerProductSpace.Core ℝ (C1 G) where
  inner := innerC1 G
  conj_inner_symm X Y := by
    simp only [innerC1, conj_trivial]
    congr 1; refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    split_ifs <;> ring
  re_inner_nonneg X := by
    simp only [innerC1, RCLike.re_to_real]
    refine mul_nonneg (by norm_num) (Finset.sum_nonneg fun p _ => Finset.sum_nonneg fun q _ => ?_)
    split_ifs
    · exact mul_self_nonneg _
    · exact le_rfl
  add_left X Y Z := by
    simp only [innerC1, ← mul_add, ← Finset.sum_add_distrib]
    congr 1; refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    split_ifs
    · show ((X : ↥(edgeFlows G)).1 + (Y : ↥(edgeFlows G)).1) p q * _ = _
      simp [add_mul]
    · simp
  smul_left X Y c := by
    simp only [innerC1, conj_trivial, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    split_ifs
    · show (1 / 2 : ℝ) * ((c • (X : ↥(edgeFlows G)).1) p q * _) = _
      simp only [Pi.smul_apply, smul_eq_mul]; ring
    · simp
  definite X hX := by
    simp only [innerC1] at hX
    have h0 : ∀ p q, (if G.Adj p q then X p q * X p q else 0) = 0 := by
      have hs : (∑ p, ∑ q, if G.Adj p q then X p q * X p q else 0) = 0 := by
        have := hX; field_simp at this; linarith
      have hnn : ∀ p q, 0 ≤ (if G.Adj p q then X p q * X p q else 0) := fun p q => by
        split_ifs
        · exact mul_self_nonneg _
        · exact le_rfl
      intro p q
      have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun p _ => Finset.sum_nonneg
        fun q _ => hnn p q)).1 hs p (Finset.mem_univ _)
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun q _ => hnn p q)).1 h1 q (Finset.mem_univ _)
    apply Subtype.ext; funext p q
    show (X : ↥(edgeFlows G)).1 p q = 0
    by_cases h : G.Adj p q
    · have := h0 p q; rw [if_pos h] at this; exact mul_self_eq_zero.1 this
    · exact ((X : ↥(edgeFlows G)).2 p q).2 h

instance : NormedAddCommGroup (C1 G) := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℝ)
instance : InnerProductSpace ℝ (C1 G) := InnerProductSpace.ofCore _
instance : FiniteDimensional ℝ (C1 G) := inferInstanceAs (FiniteDimensional ℝ ↥(edgeFlows G))
/-- Antisymmetry of an edge flow on an edge. -/
theorem C1.antisymm (X : C1 G) {p q : V} (h : G.Adj p q) : X q p = -X p q := by
  have := ((X : ↥(edgeFlows G)).2 q p).1 h.symm
  change (X : ↥(edgeFlows G)).1 q p = -(X : ↥(edgeFlows G)).1 p q
  exact this

/-- An edge flow vanishes off the edges. -/
theorem C1.eq_zero_of_not_adj (X : C1 G) {p q : V} (h : ¬ G.Adj p q) : X p q = 0 :=
  ((X : ↥(edgeFlows G)).2 p q).2 h

/-- Build an element of `C1 G` from a function and a proof of (5). -/
def C1.mk (X : V → V → ℝ) (hX : IsEdgeFlow G X) : C1 G := (⟨X, hX⟩ : ↥(edgeFlows G))

@[simp] theorem C1.mk_apply (X : V → V → ℝ) (hX : IsEdgeFlow G X) (p q : V) :
    C1.mk G X hX p q = X p q := rfl

@[simp] theorem C1.add_apply (X Y : C1 G) (p q : V) : (X + Y) p q = X p q + Y p q := rfl
@[simp] theorem C1.smul_apply (c : ℝ) (X : C1 G) (p q : V) : (c • X) p q = c * X p q := rfl
@[simp] theorem C1.zero_apply (p q : V) : (0 : C1 G) p q = 0 := rfl

@[ext] theorem C1.ext {X Y : C1 G} (h : ∀ p q, X p q = Y p q) : X = Y := by
  apply Subtype.ext; funext p q; exact h p q

/-- The gradient along the edges of a subgraph `H ≤ G`:
`φ ↦ ((p,q) ↦ W_H(p,q) (φ(q) - φ(p)))`, where `W_H` is the `0/1` indicator of the edges of
`H`; an edge flow on `G`. With `H = G` this is the combinatorial gradient `δ0` of (9). -/
def gradOn (H : SimpleGraph V) [DecidableRel H.Adj] (hH : H ≤ G) : C0 V →ₗ[ℝ] C1 G where
  toFun φ := C1.mk G (fun p q => (if H.Adj p q then (1 : ℝ) else 0) * (φ q - φ p))
    (fun p q => ⟨fun h => by
        by_cases hpq : H.Adj p q
        · simp [hpq, hpq.symm]
        · have : ¬ H.Adj q p := fun h' => hpq h'.symm
          simp [hpq, this],
      fun h => by
        have : ¬ H.Adj p q := fun h' => h (hH h')
        simp [this]⟩)
  map_add' φ ψ := by
    ext p q
    change (if H.Adj p q then (1 : ℝ) else 0) * ((φ + ψ) q - (φ + ψ) p) =
      (if H.Adj p q then (1 : ℝ) else 0) * (φ q - φ p) +
        (if H.Adj p q then (1 : ℝ) else 0) * (ψ q - ψ p)
    simp only [PiLp.add_apply]; ring
  map_smul' c φ := by
    ext p q
    change (if H.Adj p q then (1 : ℝ) else 0) * ((c • φ) q - (c • φ) p) =
      c * ((if H.Adj p q then (1 : ℝ) else 0) * (φ q - φ p))
    simp only [PiLp.smul_apply, smul_eq_mul]; ring

/-- The `0/1` edge indicator `W` of (8). -/
def W (p q : V) : ℝ := if G.Adj p q then 1 else 0

/-- The combinatorial gradient `δ0 : C0 → C1` of (9): `(δ0 φ)(p,q) = W(p,q) (φ(q) - φ(p))`. -/
def delta0 : C0 V →ₗ[ℝ] C1 G := gradOn G G le_rfl

end Graph

end HarmonicGames.GenericPure

end


