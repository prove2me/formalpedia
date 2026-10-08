-- Prove2me | Definitions.Def_HarmonicGames_Decomposition_Flows
-- name    : HarmonicGames_Decomposition_Flows
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T04:51:04.049981+00:00
-- url     : https://prove2.me/theorems/b23a344f-90a4-476b-9e0a-3455ce98af6e
-- title:
--   Edge flows and triangular flows on a graph, the inner products (7), the gradient δ0, the curl δ1 and the Laplacians Δ0, Δ1 (Section 3)
-- statement:
--   Let $G = (E, A)$ be a finite undirected simple graph with node set $E$ and (symmetric) edge set $A$. Write $T = \{(p,q,r) \mid (p,q),(q,r),(p,r) \in A\}$ for the set of ordered 3-cliques. The paper's Section 3 works on an arbitrary such graph (footnote 1, p. 9).
--
--   1. $C_0 = \{f : E \to \mathbb R\}$ with $\langle \varphi_1, \varphi_2\rangle_0 = \sum_{p} \varphi_1(p)\varphi_2(p)$.
--   2. $C_1$, the **edge flows**: functions $X : E \times E \to \mathbb R$ with $X(p,q) = -X(q,p)$ if $(p,q) \in A$ and $X(p,q) = 0$ otherwise (5), with inner product
--   $$
--   \langle X, Y\rangle_1 = \frac12 \sum_{(p,q) \in A} X(p,q)\,Y(p,q).
--   $$
--   3. $C_2$, the **triangular flows**: functions $\Psi : E\times E\times E \to \mathbb R$ invariant under cyclic shifts of the arguments, changing sign under transpositions, and vanishing off $T$ (6), with $\langle \Psi_1, \Psi_2\rangle_2 = \sum_{(p,q,r)\in T} \Psi_1(p,q,r)\Psi_2(p,q,r)$.
--   4. With $W(p,q) = 1$ if $(p,q) \in A$ and $0$ otherwise (8), the **combinatorial gradient** $\delta_0 : C_0 \to C_1$, $(\delta_0\varphi)(p,q) = W(p,q)(\varphi(q) - \varphi(p))$ (9).
--   5. The **curl** $\delta_1 : C_1 \to C_2$, $(\delta_1 X)(p,q,r) = X(p,q) + X(q,r) + X(r,p)$ if $(p,q,r) \in T$ and $0$ otherwise (10).
--   6. The **Laplacian** $\Delta_0 = \delta_0^*\delta_0$ (14) and the **vector Laplacian** $\Delta_1 = \delta_1^*\delta_1 + \delta_0\delta_0^*$ (16), where $\delta_k^*$ is the adjoint of $\delta_k$ for the inner products (7).
--
--   These objects carry the Helmholtz decomposition (Theorem 3.1) and, instantiated at the game graph, the decomposition of games.
--
--   **Formalization Note** The graph is a Mathlib `SimpleGraph` (irreflexive), so $X(p,p) = 0$ for every edge flow. $C_0$ is `EuclideanSpace ℝ V`. $C_1$ and $C_2$ are type synonyms of subspaces of `V → V → ℝ` and `V → V → V → ℝ`; their inner products are built from an `InnerProductSpace.Core` and sum over all pairs (triples) of the indicator-restricted product, which equals the sum over $A$ (over $T$). The factor $\tfrac12$ in $\langle\cdot,\cdot\rangle_1$ is kept, so adjoints agree with the paper's formulas (12) and (22). Adjoints are Mathlib's `LinearMap.adjoint`. The auxiliary `gradOn H` is the gradient restricted to the edges of a subgraph $H \le G$; $\delta_0$ is `gradOn G`.
-- source:
--   Candogan, Menache, Ozdaglar, Parrilo, Flows and Decompositions of Games: Harmonic and Potential Games, arXiv:1005.2405v2, pp. 9–10, Section 3, eqs. (5)–(10), (14), (16)

import Mathlib

/-!
Flows on an arbitrary finite simple graph `G` on a node set `V` (Section 3 of Candogan,
Menache, Ozdaglar, Parrilo): the spaces `C0`, `C1`, `C2` with the inner products (7),
the gradient `δ0` (9), the curl `δ1` (10), and the Laplacians `Δ0` (14), `Δ1` (16).
-/

noncomputable section

namespace HarmonicGames.Decomposition

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

/-- The set `T = {(p,q,r) | (p,q), (q,r), (p,r) ∈ A}` of ordered 3-cliques. -/
def IsTriangle (p q r : V) : Prop := G.Adj p q ∧ G.Adj q r ∧ G.Adj p r

instance (p q r : V) : Decidable (IsTriangle G p q r) := by
  unfold IsTriangle; infer_instance

/-- The triangular-flow condition (6): `Ψ` is invariant under cyclic shifts of its
arguments, changes sign under transpositions, and vanishes off `T`. -/
def IsTriangularFlow (Ψ : V → V → V → ℝ) : Prop :=
  ∀ p q r, Ψ p q r = Ψ q r p ∧ Ψ p q r = Ψ r p q ∧ Ψ p q r = -Ψ q p r ∧
    Ψ p q r = -Ψ p r q ∧ Ψ p q r = -Ψ r q p ∧ (¬ IsTriangle G p q r → Ψ p q r = 0)

/-- The subspace of edge flows on `G`, inside `V → V → ℝ`. -/
def edgeFlows : Submodule ℝ (V → V → ℝ) where
  carrier := {X | IsEdgeFlow G X}
  add_mem' {X Y} hX hY p q :=
    ⟨fun h => by simp [(hX p q).1 h, (hY p q).1 h]; ring,
     fun h => by simp [(hX p q).2 h, (hY p q).2 h]⟩
  zero_mem' p q := ⟨fun _ => by simp, fun _ => by simp⟩
  smul_mem' c {X} hX p q :=
    ⟨fun h => by simp [(hX p q).1 h], fun h => by simp [(hX p q).2 h]⟩

/-- The subspace of triangular flows on `G`, inside `V → V → V → ℝ`. -/
def triangularFlows : Submodule ℝ (V → V → V → ℝ) where
  carrier := {Ψ | IsTriangularFlow G Ψ}
  add_mem' {X Y} hX hY p q r := by
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hX p q r
    obtain ⟨b1, b2, b3, b4, b5, b6⟩ := hY p q r
    refine ⟨?_, ?_, ?_, ?_, ?_, fun h => ?_⟩ <;> simp only [Pi.add_apply]
    · rw [a1, b1]
    · rw [a2, b2]
    · rw [a3, b3]; ring
    · rw [a4, b4]; ring
    · rw [a5, b5]; ring
    · rw [a6 h, b6 h]; ring
  zero_mem' p q r := by simp
  smul_mem' c {X} hX p q r := by
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hX p q r
    refine ⟨?_, ?_, ?_, ?_, ?_, fun h => ?_⟩ <;> simp only [Pi.smul_apply, smul_eq_mul]
    · rw [a1]
    · rw [a2]
    · rw [a3]; ring
    · rw [a4]; ring
    · rw [a5]; ring
    · rw [a6 h]; ring

/-- `C1`: the space of edge flows on `G` (5). A type synonym of the subspace `edgeFlows G`,
carrying the inner product `⟨X, Y⟩₁ = ½ ∑_{(p,q) ∈ A} X(p,q) Y(p,q)` of (7). -/
def C1 : Type _ := ↥(edgeFlows G)

/-- `C2`: the space of triangular flows on `G` (6). A type synonym of the subspace
`triangularFlows G`, carrying the inner product `⟨Ψ₁, Ψ₂⟩₂ = ∑_{(p,q,r) ∈ T} Ψ₁ Ψ₂` of (7). -/
def C2 : Type _ := ↥(triangularFlows G)

instance : AddCommGroup (C1 G) := inferInstanceAs (AddCommGroup ↥(edgeFlows G))
instance : Module ℝ (C1 G) := inferInstanceAs (Module ℝ ↥(edgeFlows G))
instance : AddCommGroup (C2 G) := inferInstanceAs (AddCommGroup ↥(triangularFlows G))
instance : Module ℝ (C2 G) := inferInstanceAs (Module ℝ ↥(triangularFlows G))

/-- The underlying function `V → V → ℝ` of an edge flow. -/
instance : CoeFun (C1 G) (fun _ => V → V → ℝ) := ⟨fun X => (X : ↥(edgeFlows G)).1⟩

/-- The underlying function `V → V → V → ℝ` of a triangular flow. -/
instance : CoeFun (C2 G) (fun _ => V → V → V → ℝ) := ⟨fun Ψ => (Ψ : ↥(triangularFlows G)).1⟩

/-- The inner product (7) on `C1`: `⟨X, Y⟩₁ = ½ ∑_{(p,q) ∈ A} X(p,q) Y(p,q)`. -/
def innerC1 (X Y : C1 G) : ℝ :=
  (1 / 2 : ℝ) * ∑ p, ∑ q, if G.Adj p q then X p q * Y p q else 0

/-- The inner product (7) on `C2`: `⟨Ψ₁, Ψ₂⟩₂ = ∑_{(p,q,r) ∈ T} Ψ₁(p,q,r) Ψ₂(p,q,r)`. -/
def innerC2 (X Y : C2 G) : ℝ :=
  ∑ p, ∑ q, ∑ r, if IsTriangle G p q r then X p q r * Y p q r else 0

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

instance coreC2 : InnerProductSpace.Core ℝ (C2 G) where
  inner := innerC2 G
  conj_inner_symm X Y := by
    simp only [innerC2, conj_trivial]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ =>
      Finset.sum_congr rfl fun r _ => ?_
    split_ifs <;> ring
  re_inner_nonneg X := by
    simp only [innerC2, RCLike.re_to_real]
    refine Finset.sum_nonneg fun p _ => Finset.sum_nonneg fun q _ => Finset.sum_nonneg
      fun r _ => ?_
    split_ifs
    · exact mul_self_nonneg _
    · exact le_rfl
  add_left X Y Z := by
    simp only [innerC2, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ =>
      Finset.sum_congr rfl fun r _ => ?_
    split_ifs
    · show ((X : ↥(triangularFlows G)).1 + (Y : ↥(triangularFlows G)).1) p q r * _ = _
      simp [add_mul]
    · simp
  smul_left X Y c := by
    simp only [innerC2, conj_trivial, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ =>
      Finset.sum_congr rfl fun r _ => ?_
    split_ifs
    · show (c • (X : ↥(triangularFlows G)).1) p q r * _ = _
      simp only [Pi.smul_apply, smul_eq_mul]; ring
    · simp
  definite X hX := by
    simp only [innerC2] at hX
    have hnn : ∀ p q r, 0 ≤ (if IsTriangle G p q r then X p q r * X p q r else 0) :=
      fun p q r => by
        split_ifs
        · exact mul_self_nonneg _
        · exact le_rfl
    apply Subtype.ext; funext p q r
    show (X : ↥(triangularFlows G)).1 p q r = 0
    have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun p _ => Finset.sum_nonneg
      fun q _ => Finset.sum_nonneg fun r _ => hnn p q r)).1 hX p (Finset.mem_univ _)
    have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun q _ => Finset.sum_nonneg
      fun r _ => hnn p q r)).1 h1 q (Finset.mem_univ _)
    have h3 := (Finset.sum_eq_zero_iff_of_nonneg (fun r _ => hnn p q r)).1 h2 r
      (Finset.mem_univ _)
    by_cases h : IsTriangle G p q r
    · rw [if_pos h] at h3; exact mul_self_eq_zero.1 h3
    · exact ((X : ↥(triangularFlows G)).2 p q r).2.2.2.2.2 h

instance : NormedAddCommGroup (C1 G) := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℝ)
instance : InnerProductSpace ℝ (C1 G) := InnerProductSpace.ofCore _
instance : NormedAddCommGroup (C2 G) := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℝ)
instance : InnerProductSpace ℝ (C2 G) := InnerProductSpace.ofCore _
instance : FiniteDimensional ℝ (C1 G) := inferInstanceAs (FiniteDimensional ℝ ↥(edgeFlows G))
instance : FiniteDimensional ℝ (C2 G) :=
  inferInstanceAs (FiniteDimensional ℝ ↥(triangularFlows G))

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

/-- Build an element of `C2 G` from a function and a proof of (6). -/
def C2.mk (Ψ : V → V → V → ℝ) (hΨ : IsTriangularFlow G Ψ) : C2 G :=
  (⟨Ψ, hΨ⟩ : ↥(triangularFlows G))

@[simp] theorem C2.mk_apply (Ψ : V → V → V → ℝ) (hΨ : IsTriangularFlow G Ψ) (p q r : V) :
    C2.mk G Ψ hΨ p q r = Ψ p q r := rfl

@[simp] theorem C2.add_apply (X Y : C2 G) (p q r : V) : (X + Y) p q r = X p q r + Y p q r := rfl
@[simp] theorem C2.smul_apply (c : ℝ) (X : C2 G) (p q r : V) : (c • X) p q r = c * X p q r :=
  rfl

@[ext] theorem C2.ext {X Y : C2 G} (h : ∀ p q r, X p q r = Y p q r) : X = Y := by
  apply Subtype.ext; funext p q r; exact h p q r

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

/-- The curl `δ1 : C1 → C2` of (10): `(δ1 X)(p,q,r) = X(p,q) + X(q,r) + X(r,p)` if
`(p,q,r) ∈ T`, and `0` otherwise. -/
def delta1 : C1 G →ₗ[ℝ] C2 G where
  toFun X := C2.mk G
    (fun p q r => if IsTriangle G p q r then X p q + X q r + X r p else 0)
    (fun p q r => by
      dsimp only
      have c1 : IsTriangle G p q r ↔ IsTriangle G q r p := by
        unfold IsTriangle; exact ⟨fun ⟨a, b, c⟩ => ⟨b, c.symm, a.symm⟩,
          fun ⟨a, b, c⟩ => ⟨c.symm, a, b.symm⟩⟩
      have c2 : IsTriangle G p q r ↔ IsTriangle G r p q := by
        unfold IsTriangle; exact ⟨fun ⟨a, b, c⟩ => ⟨c.symm, a, b.symm⟩,
          fun ⟨a, b, c⟩ => ⟨b, c.symm, a.symm⟩⟩
      have t1 : IsTriangle G p q r ↔ IsTriangle G q p r := by
        unfold IsTriangle; exact ⟨fun ⟨a, b, c⟩ => ⟨a.symm, c, b⟩, fun ⟨a, b, c⟩ => ⟨a.symm, c, b⟩⟩
      have t2 : IsTriangle G p q r ↔ IsTriangle G p r q := by
        unfold IsTriangle; exact ⟨fun ⟨a, b, c⟩ => ⟨c, b.symm, a⟩, fun ⟨a, b, c⟩ => ⟨c, b.symm, a⟩⟩
      have t3 : IsTriangle G p q r ↔ IsTriangle G r q p := by
        unfold IsTriangle
        exact ⟨fun ⟨a, b, c⟩ => ⟨b.symm, a.symm, c.symm⟩, fun ⟨a, b, c⟩ => ⟨b.symm, a.symm, c.symm⟩⟩
      by_cases hT : IsTriangle G p q r
      · obtain ⟨a, b, c⟩ := hT
        have hT' : IsTriangle G p q r := ⟨a, b, c⟩
        rw [if_pos hT', if_pos (c1.1 hT'), if_pos (c2.1 hT'), if_pos (t1.1 hT'),
          if_pos (t2.1 hT'), if_pos (t3.1 hT')]
        rw [C1.antisymm G X a, C1.antisymm G X b, C1.antisymm G X c]
        refine ⟨by ring, by ring, by ring, ?_, by ring, fun h => absurd hT' h⟩
        rw [C1.antisymm G X c.symm, C1.antisymm G X b.symm, C1.antisymm G X a.symm]; ring
      · rw [if_neg hT, if_neg (fun h => hT (c1.2 h)), if_neg (fun h => hT (c2.2 h)),
          if_neg (fun h => hT (t1.2 h)), if_neg (fun h => hT (t2.2 h)),
          if_neg (fun h => hT (t3.2 h))]
        simp)
  map_add' X Y := by
    ext p q r
    change (if IsTriangle G p q r then (X + Y) p q + (X + Y) q r + (X + Y) r p else 0) =
      (if IsTriangle G p q r then X p q + X q r + X r p else 0) +
        (if IsTriangle G p q r then Y p q + Y q r + Y r p else 0)
    simp only [C1.add_apply]; split_ifs <;> ring
  map_smul' c X := by
    ext p q r
    change (if IsTriangle G p q r then (c • X) p q + (c • X) q r + (c • X) r p else 0) =
      c * (if IsTriangle G p q r then X p q + X q r + X r p else 0)
    simp only [C1.smul_apply]; split_ifs <;> ring

/-- The graph Laplacian `Δ0 = δ0* δ0 : C0 → C0` of (14), with `δ0*` the adjoint of `δ0`
for the inner products (7). -/
def Delta0 : C0 V →ₗ[ℝ] C0 V := LinearMap.adjoint (delta0 G) ∘ₗ delta0 G

/-- The vector Laplacian `Δ1 = δ1* δ1 + δ0 δ0* : C1 → C1` of (16), with adjoints for the
inner products (7). -/
def Delta1 : C1 G →ₗ[ℝ] C1 G :=
  LinearMap.adjoint (delta1 G) ∘ₗ delta1 G + delta0 G ∘ₗ LinearMap.adjoint (delta0 G)

end Graph

end HarmonicGames.Decomposition

end


