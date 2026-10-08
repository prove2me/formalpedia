-- Prove2me | Definitions.Def_SoysterInexactLP_Auxiliary_Problems
-- name    : SoysterInexactLP_Auxiliary_Problems
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:32:06.341994+00:00
-- url     : https://prove2.me/theorems/0c5ab850-8561-4150-9255-2e417f9f4745
-- title:
--   Problems (I) and (Ib): x₁K₁+⋯+xₙKₙ ⊆ K, K(b) = {y ≦ b}, support functionals, the matrix Ā, LP(Ā), the set M, hypersphere activity sets
-- statement:
--   This file sets up the objects of Soyster's set-inclusive linear programming. Fix integers $m,n\ge 0$. Vectors of $\mathbb R^m$ are columns; the order $y\le b$ on $\mathbb R^m$ is componentwise.
--
--   1. **Support functional.** For a set $S\subseteq\mathbb R^m$ and $y\in\mathbb R^m$,
--   $$\delta^*(y\mid S)=\sup_{a\in S}\, y\cdot a\ \in[-\infty,+\infty],$$
--   with $\delta^*(y\mid\emptyset)=-\infty$.
--
--   2. **Problem (I).** Given $n$ activity sets $K_1,\dots,K_n\subseteq\mathbb R^m$ and a resource set $K\subseteq\mathbb R^m$, a vector $x\in\mathbb R^n$ is *feasible for (I)* when
--   $$x_j\ge 0\ (j=1,\dots,n)\qquad\text{and}\qquad x_1K_1+x_2K_2+\cdots+x_nK_n\subseteq K,$$
--   where $x_jK_j=\{x_ja : a\in K_j\}$ and $+$ is Minkowski addition of sets. The feasible set is $X=\{x\in\mathbb R^n \mid x\text{ is feasible for (I)}\}$.
--
--   3. **Problem (Ib).** For $b\in\mathbb R^m$ let $K(b)=\{y\in\mathbb R^m\mid y\le b\}$; $x$ is feasible for (Ib) when it is feasible for (I) with resource set $K(b)$.
--
--   4. **The matrix $\bar A$.** With $e_i$ the $i$-th unit vector, $\bar A$ is the $m\times n$ matrix whose $(i,j)$ entry is
--   $$\bar a_{ij}=\delta^*(e_i\mid K_j)=\sup_{a_j\in K_j} a_{ij}.$$
--
--   5. **LP$(\bar A)$.** For an $m\times n$ matrix $A$, $x$ is feasible for the linear program $\max c\cdot x$ s.t. $Ax\le b$, $x\ge0$ when $x\ge 0$ and $Ax\le b$; with $A=\bar A$ this is LP$(\bar A)$.
--
--   6. **The set $M$** of $m\times n$ matrices $(a_1,\dots,a_n)$ with $a_j\in K_j$ for every $j$ (column $j$ lies in $K_j$).
--
--   7. **Optimal solution.** For a feasibility predicate $F$ on $\mathbb R^n$ and $c\in\mathbb R^n$, $x$ is an optimal solution of $\sup c\cdot x$ over $F$ when $x$ is feasible and $c\cdot y\le c\cdot x$ for every feasible $y$.
--
--   8. **Hypersphere activity sets.** Given an $m\times n$ matrix $A_0=(a_1,\dots,a_n)$ of nominal activity vectors and radii $\rho_1,\dots,\rho_n$,
--   $$K_j=\{a\in\mathbb R^m \mid \|a-a_j\|_2\le\rho_j\},$$
--   the closed Euclidean ball of radius $\rho_j$ around the $j$-th column of $A_0$.
--
--   These are the objects of every statement in the mission: the problem (I) whose constraint is a set inclusion, its special case (Ib), and the ordinary linear program LP$(\bar A)$ built from the support functionals of the activity sets.
--
--   **Formalization Note** Vectors are `Fin m → ℝ`, so indices run over $0,\dots,m-1$ instead of $1,\dots,m$. Feasibility of (I) is the Minkowski-sum inclusion itself (pointwise set scaling and the pointwise set sum), not the equivalent "for every choice of $a_j\in K_j$" condition, which is a separate theorem. $\delta^*$ takes values in `EReal`; $\bar a_{ij}$ is its conversion to a real number, which is exact only when $K_j\neq\emptyset$ and $\delta^*(e_i\mid K_j)<\infty$, so every statement about $\bar A$ assumes both. The support functional has the same body as the published `FenchelRobust.Counterpart.supportFun`; it is restated here because that module could not be loaded into the drafting workspace. "Optimal solution" is read as an attained maximum; the paper writes $\sup c\cdot x$ and does not discuss attainment. The ball uses the Euclidean norm (`EuclideanSpace ℝ (Fin m)`), not the sup norm of `Fin m → ℝ`.
-- source:
--   Soyster, Convex Programming with Set-Inclusive Constraints and Applications to Inexact Linear Programming, Operations Research 21 (1973), pp. 1154–1157 (PDF pp. 2–5): problems (I), (Ib), definition of X (p. 1155), δ* and āⱼ (p. 1155), Ā, LP(Ā) and M (p. 1156), hypersphere sets Kⱼ (p. 1157)

import Mathlib
open Pointwise Matrix

namespace SoysterInexactLP.Auxiliary

/-- The support functional `δ*(y|S) = sup_{a ∈ S} y·a` (p. 1155), valued in `EReal`
(`+∞` when unbounded above, `⊥ = −∞` when `S = ∅`). Same body as the published
`FenchelRobust.Counterpart.supportFun`. -/
noncomputable def supportFun {k : ℕ} (S : Set (Fin k → ℝ)) (y : Fin k → ℝ) : EReal :=
  ⨆ a ∈ S, ((y ⬝ᵥ a : ℝ) : EReal)

/-- Feasibility for problem (I) (p. 1154): `xⱼ ≥ 0` for all `j` and the Minkowski sum
`x₁K₁ + ⋯ + xₙKₙ` of the scaled activity sets is contained in the resource set `R`. -/
def FeasibleI {m n : ℕ} (K : Fin n → Set (Fin m → ℝ)) (R : Set (Fin m → ℝ))
    (x : Fin n → ℝ) : Prop :=
  (∀ j, 0 ≤ x j) ∧ (∑ j, x j • K j) ⊆ R

/-- The resource set `K(b) = {y ∈ ℝᵐ | y ≤ b}` (componentwise order), p. 1154. -/
def Kb {m : ℕ} (b : Fin m → ℝ) : Set (Fin m → ℝ) :=
  {y | y ≤ b}

/-- Feasibility for problem (Ib) (p. 1154): feasibility for (I) with resource set `K(b)`. -/
def FeasibleIb {m n : ℕ} (K : Fin n → Set (Fin m → ℝ)) (b : Fin m → ℝ)
    (x : Fin n → ℝ) : Prop :=
  FeasibleI K (Kb b) x

/-- The feasible set `X = {x ∈ ℝⁿ | x is feasible for (I)}` (p. 1155). -/
def X {m n : ℕ} (K : Fin n → Set (Fin m → ℝ)) (R : Set (Fin m → ℝ)) : Set (Fin n → ℝ) :=
  {x | FeasibleI K R x}

/-- The matrix `Ā = (ā₁, …, āₙ)` (pp. 1155–1156): entry `(i, j)` is `δ*(eᵢ|Kⱼ) = sup_{aⱼ ∈ Kⱼ} aᵢⱼ`,
with `eᵢ = Pi.single i 1`. The `toReal` is exact only when `Kⱼ` is nonempty and `δ*(eᵢ|Kⱼ) < ∞`;
every statement about `Ā` carries those hypotheses. -/
noncomputable def Abar {m n : ℕ} (K : Fin n → Set (Fin m → ℝ)) : Matrix (Fin m) (Fin n) ℝ :=
  Matrix.of fun i j => (supportFun (K j) (Pi.single i 1)).toReal

/-- Feasibility for the linear program `max c·x` s.t. `A·x ≤ b`, `x ≥ 0`; with `A = Ā` this is
`LP(Ā)` (p. 1156). -/
def FeasibleLP {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (x : Fin n → ℝ) : Prop :=
  (∀ j, 0 ≤ x j) ∧ A *ᵥ x ≤ b

/-- The set `M = {(a₁, …, aₙ) | a₁ ∈ K₁, …, aₙ ∈ Kₙ}` of `m × n` matrices whose `j`-th column
lies in `Kⱼ` (p. 1156). -/
def MSet {m n : ℕ} (K : Fin n → Set (Fin m → ℝ)) : Set (Matrix (Fin m) (Fin n) ℝ) :=
  {A | ∀ j, (fun i => A i j) ∈ K j}

/-- `x` is an optimal solution of `sup c·x` over the feasibility predicate `F`: it is feasible
and attains the maximum of `c·x` over all feasible points. -/
def IsOptimal {n : ℕ} (F : (Fin n → ℝ) → Prop) (c x : Fin n → ℝ) : Prop :=
  F x ∧ ∀ y, F y → c ⬝ᵥ y ≤ c ⬝ᵥ x

/-- The hypersphere activity set `Kⱼ = {a ∈ ℝᵐ | ‖a − aⱼ‖ ≤ ρⱼ}` (p. 1157), with the
**Euclidean** norm; the nominal centre `aⱼ` is the `j`-th column of `A₀`. -/
noncomputable def hyperBall {m n : ℕ} (A₀ : Matrix (Fin m) (Fin n) ℝ) (ρ : Fin n → ℝ)
    (j : Fin n) : Set (Fin m → ℝ) :=
  {a | ‖(WithLp.toLp 2 (a - fun i => A₀ i j) : EuclideanSpace ℝ (Fin m))‖ ≤ ρ j}

end SoysterInexactLP.Auxiliary


