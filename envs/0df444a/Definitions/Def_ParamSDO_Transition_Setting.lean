-- Prove2me | Definitions.Def_ParamSDO_Transition_Setting
-- name    : ParamSDO_Transition_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T04:18:30.258795+00:00
-- url     : https://prove2.me/theorems/ed27c9c7-e7a1-45d2-b77a-1a6d3e9d986f
-- title:
--   (P_ϵ)/(D_ϵ), v, 𝓔, 𝓟*, 𝓓*, Assumptions 1–2, Definitions 1 and 5, 𝓢_(θ,σ), pp. 1–7, 22 — parametric SDO and transition points
-- statement:
--   This file fixes the objects of Hauenstein, Mohammad-Nezhad, Tang and Terlaky (§1, pp. 1–2; Definition 5, p. 7; Appendix, p. 22).
--
--   Let $\mathbb S^n$ be the space of real symmetric $n\times n$ matrices with the trace inner product $\langle M,X\rangle=\operatorname{tr}(MX)$. The data are matrices $A^1,\dots,A^m,C,\bar C\in\mathbb S^n$ and a vector $b\in\mathbb R^m$; $\bar C$ is a fixed direction along which the objective is perturbed by a real parameter $\epsilon$. The parametric primal–dual pair is
--   $$
--   (\mathrm P_\epsilon)\ \inf_X\{\langle C+\epsilon\bar C,X\rangle:\ \langle A^i,X\rangle=b_i,\ i=1,\dots,m,\ X\succeq0\},\qquad
--   (\mathrm D_\epsilon)\ \sup_{(y,S)}\Big\{b^Ty:\ \sum_{i=1}^m y_iA^i+S=C+\epsilon\bar C,\ S\succeq0\Big\}.
--   $$
--
--   1. **Feasible sets.** $\mathcal P=\{X\succeq0:\ \langle A^i,X\rangle=b_i\ \forall i\}$ (independent of $\epsilon$) and $\mathcal D(\epsilon)=\{(y,S):\ \sum_i y_iA^i+S=C+\epsilon\bar C,\ S\succeq0\}$. Here $X\succeq0$ means $X$ is symmetric positive semidefinite.
--   2. **Optimal value function.** $v(\epsilon)=\inf_{X\in\mathcal P}\langle C+\epsilon\bar C,X\rangle\in\mathbb R\cup\{-\infty,+\infty\}$, and its domain $\mathcal E=\{\epsilon:\ v(\epsilon)>-\infty\}$.
--   3. **Optimal sets.** $\mathcal P^*(\epsilon)=\{X\in\mathcal P:\ \langle C+\epsilon\bar C,X\rangle=v(\epsilon)\}$ and $\mathcal D^*(\epsilon)=\{(y,S)\in\mathcal D(\epsilon):\ b^Ty=v(\epsilon)\}$; as printed, the dual objective is compared with the primal value $v(\epsilon)$.
--   4. **Assumption 1.** $A^1,\dots,A^m$ are linearly independent. **Assumption 2.** There are $X^\circ\in\mathcal P$ and $(y^\circ,S^\circ)\in\mathcal D(0)$ with $X^\circ\succ0$ and $S^\circ\succ0$.
--   5. **Ranks of a maximally complementary solution** (Definition 1). For $\epsilon\in\operatorname{int}(\mathcal E)$, $\operatorname{rank}X^*(\epsilon)$ is the rank of a point of the relative interior $\operatorname{ri}\mathcal P^*(\epsilon)$, and $\operatorname{rank}S^*(\epsilon)$ the rank of the $S$-part of a point of $\operatorname{ri}\mathcal D^*(\epsilon)$.
--   6. **Transition point** (Definition 5). $\bar\epsilon\in\operatorname{int}(\mathcal E)$ is a transition point if for every $\delta>0$ there is $\epsilon\in(\bar\epsilon-\delta,\bar\epsilon+\delta)\cap\operatorname{int}(\mathcal E)$ with
--   $$\operatorname{rank}X^*(\epsilon)\ne\operatorname{rank}X^*(\bar\epsilon)\quad\text{or}\quad\operatorname{rank}S^*(\epsilon)\ne\operatorname{rank}S^*(\bar\epsilon).$$
--   7. **The sets $\mathcal S_{(\theta,\sigma)}$** (Appendix, p. 22): the $\epsilon\in\operatorname{int}(\mathcal E)$ for which some $(X,y,S)\in\operatorname{ri}(\mathcal P^*(\epsilon)\times\mathcal D^*(\epsilon))$ has $\operatorname{rank}X=\theta$ and $\operatorname{rank}S=\sigma$.
--   8. **Semi-algebraic sets.** $T\subseteq\mathbb R^N$ is semi-algebraic if it is a finite union of sets $\{p_1=\dots=p_k=0,\ g_1<0,\dots,g_l<0\}$ with real polynomials $p_i,g_j$; a subset of $\mathbb R$ is semi-algebraic when it is so as a subset of $\mathbb R^1$.
--
--   These are the objects of Theorem 1 (finiteness of the set of transition points) and of the steps of its proof in the Appendix.
--
--   **Formalization Note** Matrices are `Matrix (Fin n) (Fin n) ℝ`; symmetry of the data is not built into the definitions but is a hypothesis of every theorem. $v$ is an `EReal` infimum, so $v=+\infty$ when $\mathcal P=\emptyset$ and $v=-\infty$ when the objective is unbounded below. The relative interior is Mathlib's `intrinsicInterior`. Definition 1 lets $X^*(\epsilon)$ be any maximally complementary solution; to avoid a choice, $\operatorname{rank}X^*(\epsilon)$ is the supremum of the ranks over $\operatorname{ri}\mathcal P^*(\epsilon)$ (and likewise for $S^*$). On $\operatorname{int}(\mathcal E)$ every point of the relative interior has this same rank (a milestone of this mission); off $\operatorname{int}(\mathcal E)$, where Definition 5 never evaluates it, the supremum may be the junk value $0$. $\mathcal S_{(\theta,\sigma)}$ uses the relative interior of the product, as printed; Definition 1 uses the relative interiors of the factors, which agree for convex sets. The semi-algebraic predicate has the same body as the published `NonconvexSplitting.ADMMKL.IsSemialgebraicSet`.
-- source:
--   Hauenstein, Mohammad-Nezhad, Tang & Terlaky, On computing the nonlinearity interval in parametric semidefinite optimization, arXiv:1908.10499v3, pp. 1–2 ((P_ϵ), (D_ϵ), v, E, P*, D*, P, D, Assumptions 1–2, Definition 1), p. 7 (Definition 5), p. 22 (Appendix, proof of Theorem 1, the sets S_(θ,σ))

import Mathlib

namespace ParamSDO.Transition

/-- The trace inner product `⟨M, X⟩ := tr(M X)` on `n × n` real matrices (p. 1). -/
def pair {n : ℕ} (M X : Matrix (Fin n) (Fin n) ℝ) : ℝ := (M * X).trace

/-- The primal feasible set `𝓟 = {X : ⟨Aᵢ, X⟩ = bᵢ, i = 1, …, m, X ⪰ 0}` (p. 1). It does not depend
on `ϵ`. `X.PosSemidef` includes the symmetry of `X`. -/
def Pfeas {n m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (b : Fin m → ℝ) :
    Set (Matrix (Fin n) (Fin n) ℝ) :=
  {X | X.PosSemidef ∧ ∀ i, pair (A i) X = b i}

/-- The dual feasible set `𝓓(ϵ) = {(y, S) : ∑ᵢ yᵢ Aᵢ + S = C + ϵ C̄, S ⪰ 0}` (p. 2). -/
def Dfeas {n m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (C Cbar : Matrix (Fin n) (Fin n) ℝ)
    (ϵ : ℝ) : Set ((Fin m → ℝ) × Matrix (Fin n) (Fin n) ℝ) :=
  {p | ∑ i, p.1 i • A i + p.2 = C + ϵ • Cbar ∧ p.2.PosSemidef}

/-- The optimal value `v(ϵ) ∈ ℝ ∪ {−∞, +∞}` of `(P_ϵ)` (p. 1): the infimum, in `EReal`, of
`⟨C + ϵ C̄, X⟩` over `X ∈ 𝓟`. It is `+∞` when `𝓟 = ∅` and `−∞` when the objective is unbounded
below on `𝓟`. -/
noncomputable def v {n m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (b : Fin m → ℝ)
    (C Cbar : Matrix (Fin n) (Fin n) ℝ) (ϵ : ℝ) : EReal :=
  ⨅ X ∈ Pfeas A b, ((pair (C + ϵ • Cbar) X : ℝ) : EReal)

/-- The domain `𝓔 := {ϵ ∈ ℝ : v(ϵ) > −∞}` of the optimal value function (p. 1). -/
def domE {n m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (b : Fin m → ℝ)
    (C Cbar : Matrix (Fin n) (Fin n) ℝ) : Set ℝ :=
  {ϵ | ⊥ < v A b C Cbar ϵ}

/-- The primal optimal set `𝓟*(ϵ) = {X : ⟨C + ϵ C̄, X⟩ = v(ϵ), X ∈ 𝓟}` (p. 1). -/
def Pstar {n m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (b : Fin m → ℝ)
    (C Cbar : Matrix (Fin n) (Fin n) ℝ) (ϵ : ℝ) : Set (Matrix (Fin n) (Fin n) ℝ) :=
  {X | X ∈ Pfeas A b ∧ ((pair (C + ϵ • Cbar) X : ℝ) : EReal) = v A b C Cbar ϵ}

/-- The dual optimal set `𝓓*(ϵ) = {(y, S) : bᵀy = v(ϵ), (y, S) ∈ 𝓓(ϵ)}` (p. 1). As printed, the
dual objective is compared with the *primal* optimal value `v(ϵ)`. -/
def Dstar {n m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (b : Fin m → ℝ)
    (C Cbar : Matrix (Fin n) (Fin n) ℝ) (ϵ : ℝ) :
    Set ((Fin m → ℝ) × Matrix (Fin n) (Fin n) ℝ) :=
  {p | p ∈ Dfeas A C Cbar ϵ ∧ ((b ⬝ᵥ p.1 : ℝ) : EReal) = v A b C Cbar ϵ}

/-- Assumption 1 (p. 2): the coefficient matrices `A₁, …, A_m` are linearly independent. -/
def Assumption1 {n m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ) : Prop :=
  LinearIndependent ℝ A

/-- Assumption 2 (p. 2): the interior point condition at `ϵ = 0`, i.e. there are `X° ∈ 𝓟` and
`(y°, S°) ∈ 𝓓(0)` with `X° ≻ 0` and `S° ≻ 0`. -/
def Assumption2 {n m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (b : Fin m → ℝ)
    (C Cbar : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  (∃ X ∈ Pfeas A b, X.PosDef) ∧ ∃ p ∈ Dfeas A C Cbar 0, p.2.PosDef

/-- `rank X*(ϵ)` for a maximally complementary optimal solution (Definition 1, p. 2): the rank of a
point of the relative interior `ri 𝓟*(ϵ)`, taken as the supremum over all such points so that no
choice is made. On `int 𝓔` every point of `ri 𝓟*(ϵ)` has this same rank. -/
noncomputable def rkX {n m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (b : Fin m → ℝ)
    (C Cbar : Matrix (Fin n) (Fin n) ℝ) (ϵ : ℝ) : ℕ :=
  sSup (Matrix.rank '' intrinsicInterior ℝ (Pstar A b C Cbar ϵ))

/-- `rank S*(ϵ)` for a maximally complementary optimal solution (Definition 1, p. 2): the rank of
the `S`-component of a point of `ri 𝓓*(ϵ)`, taken as the supremum over all such points. -/
noncomputable def rkS {n m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (b : Fin m → ℝ)
    (C Cbar : Matrix (Fin n) (Fin n) ℝ) (ϵ : ℝ) : ℕ :=
  sSup ((fun p : (Fin m → ℝ) × Matrix (Fin n) (Fin n) ℝ => p.2.rank) ''
    intrinsicInterior ℝ (Dstar A b C Cbar ϵ))

/-- Definition 5 (p. 7): `ϵ̄ ∈ int 𝓔` is a transition point if every neighbourhood
`(ϵ̄ − δ, ϵ̄ + δ) ∩ int 𝓔` contains an `ϵ` with `rank X*(ϵ) ≠ rank X*(ϵ̄)` or
`rank S*(ϵ) ≠ rank S*(ϵ̄)`. -/
def IsTransitionPoint {n m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (b : Fin m → ℝ)
    (C Cbar : Matrix (Fin n) (Fin n) ℝ) (ϵbar : ℝ) : Prop :=
  ϵbar ∈ interior (domE A b C Cbar) ∧
    ∀ δ > 0, ∃ ϵ ∈ Set.Ioo (ϵbar - δ) (ϵbar + δ) ∩ interior (domE A b C Cbar),
      rkX A b C Cbar ϵ ≠ rkX A b C Cbar ϵbar ∨ rkS A b C Cbar ϵ ≠ rkS A b C Cbar ϵbar

/-- The set `𝓢_(θ,σ)` (Appendix, p. 22): the `ϵ ∈ int 𝓔` for which some
`(X, y, S) ∈ ri(𝓟*(ϵ) × 𝓓*(ϵ))` has `rank X = θ` and `rank S = σ`. -/
def Srank {n m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (b : Fin m → ℝ)
    (C Cbar : Matrix (Fin n) (Fin n) ℝ) (θ σ : ℕ) : Set ℝ :=
  {ϵ | (∃ X : Matrix (Fin n) (Fin n) ℝ, ∃ p : (Fin m → ℝ) × Matrix (Fin n) (Fin n) ℝ,
      (X, p) ∈ intrinsicInterior ℝ (Pstar A b C Cbar ϵ ×ˢ Dstar A b C Cbar ϵ) ∧
      X.rank = θ ∧ p.2.rank = σ) ∧ ϵ ∈ interior (domE A b C Cbar)}

/-- A semi-algebraic subset of `ℝᴺ`: a finite union of basic sets
`{v | p₁(v) = ⋯ = p_k(v) = 0, g₁(v) < 0, …, g_l(v) < 0}` with real polynomials `pᵢ, gⱼ` in `N`
variables (`k, l ≥ 0`; the empty union is allowed). Identical body to the published
`NonconvexSplitting.ADMMKL.IsSemialgebraicSet`. -/
def IsSemialgebraicSet {N : ℕ} (S : Set (Fin N → ℝ)) : Prop :=
  ∃ (K : ℕ) (eqs lts : Fin K → Finset (MvPolynomial (Fin N) ℝ)),
    S = ⋃ i, {v | (∀ p ∈ eqs i, MvPolynomial.eval v p = 0) ∧
      ∀ g ∈ lts i, MvPolynomial.eval v g < 0}

/-- A subset `T ⊆ ℝ` is semi-algebraic when its copy in `ℝ¹ = (Fin 1 → ℝ)` is. -/
def IsSemialgebraicReal (T : Set ℝ) : Prop :=
  IsSemialgebraicSet ((fun x : Fin 1 → ℝ => x 0) ⁻¹' T)

end ParamSDO.Transition


