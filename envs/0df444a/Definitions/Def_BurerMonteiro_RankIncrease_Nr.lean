-- Prove2me | Definitions.Def_BurerMonteiro_RankIncrease_Nr
-- name    : BurerMonteiro_RankIncrease_Nr
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T11:16:44.775035+00:00
-- url     : https://prove2.me/theorems/e11636df-fdc1-4b91-a6b3-c5f692f959ac
-- title:
--   The low-rank program $(N_r)$, its Lagrangian (7), regular and stationary points, and the injection $\hat R$
-- statement:
--   This module fixes the nonlinear reformulation $(N_r)$ of the SDP and the notions used in its optimality conditions.
--
--   For a positive integer $r\le n$, the program $(N_r)$ is
--   $$(N_r)\qquad \min\{\,C\bullet(RR^{T}) : A_i\bullet(RR^{T})=b_i,\ i=1,\dots,m,\ R\in\mathbb R^{n\times r}\,\}.$$
--
--   1. $R$ is a **local minimum** of $(N_r)$ if $R$ is feasible and $C\bullet(RR^T)\le C\bullet(R'R'^T)$ for every feasible $R'$ in some neighbourhood of $R$.
--   2. The **Lagrangian** (7) is $L(R,y)=C\bullet(RR^{T})-\sum_{i=1}^m y_i\big(A_i\bullet(RR^{T})-b_i\big)$, with unrestricted multipliers $y\in\mathbb R^m$.
--   3. For $G\in\mathbb R^{p\times q}$, the linear functional $D\mapsto G\bullet D$; a function $g$ has gradient $\nabla g(R)=G$ when its derivative at $R$ is this functional.
--   4. $R$ is a **regular point** if the matrices $A_1R,\dots,A_mR$ (the constraint gradients, up to the factor $2$) are linearly independent.
--   5. $R$ is a **stationary point** of $(N_r)$ with multiplier $y$ if $R$ is feasible and $\nabla_R L(R,y)=0$.
--   6. The **injection** of $R\in\mathbb R^{n\times r}$ into $\mathbb R^{n\times(r+1)}$ is $\hat R=[\,R\ \ 0\,]$, the matrix $R$ with a zero column appended as its last column.
--
--   These are the objects of Propositions 2.3–2.5: local minima and stationary points of the factorized problem, and the rank-increase step $R\mapsto\hat R$.
--
--   **Formalization Note** Derivatives are Fréchet derivatives on `Matrix (Fin n) (Fin r) ℝ` with the Frobenius norm (`open scoped Matrix.Norms.Frobenius`); in finite dimension the derivative does not depend on the norm, and this instance keeps the product topology, which is also the topology of the neighbourhoods in "local minimum". A local minimum is `IsLocalMinOn` on the feasible set together with feasibility. Stationarity does not include any sign condition on $S$. The bound $0<r\le n$ is not part of these definitions; every theorem about $(N_r)$ carries it as a hypothesis.
-- source:
--   Burer & Monteiro, A nonlinear programming algorithm for solving semidefinite programs via low-rank factorization (manuscript of March 9, 2001; Math. Program. 95 (2003)), p. 5, (N_r); p. 6, §2.2, Eq. (7) and Proposition 2.3 (regular point); p. 7, Propositions 2.4 (stationary point) and 2.5 with its proof (injection)

import Mathlib
import Definitions.Def_BurerMonteiro_RankIncrease_SDP

open Matrix
open scoped Matrix.Norms.Frobenius

namespace BurerMonteiro.RankIncrease

/-- The feasible set of `(N_r)`: `R ∈ ℝ^{n×r}` with `Aᵢ • (R Rᵀ) = bᵢ` for every `i` (p. 5). -/
def nrFeasible {n m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (b : Fin m → ℝ) (r : ℕ) :
    Set (Matrix (Fin n) (Fin r) ℝ) :=
  {R | ∀ i, frob (A i) (R * Rᵀ) = b i}

/-- The objective of `(N_r)`: `C • (R Rᵀ)` (p. 5). -/
def nrObjective {n r : ℕ} (C : Matrix (Fin n) (Fin n) ℝ) (R : Matrix (Fin n) (Fin r) ℝ) : ℝ :=
  frob C (R * Rᵀ)

/-- `R` is a local minimum of `(N_r)`: `R` is feasible and minimizes the objective over the
feasible points in some neighbourhood of `R`. -/
def IsNrLocalMin {n m r : ℕ} (C : Matrix (Fin n) (Fin n) ℝ)
    (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (b : Fin m → ℝ) (R : Matrix (Fin n) (Fin r) ℝ) :
    Prop :=
  R ∈ nrFeasible A b r ∧ IsLocalMinOn (nrObjective C) (nrFeasible A b r) R

/-- The Lagrangian (7) of `(N_r)`:
`L(R, y) = C • (R Rᵀ) − ∑ᵢ yᵢ (Aᵢ • (R Rᵀ) − bᵢ)` (p. 6). -/
def lagrangian {n m r : ℕ} (C : Matrix (Fin n) (Fin n) ℝ)
    (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (b : Fin m → ℝ) (R : Matrix (Fin n) (Fin r) ℝ)
    (y : Fin m → ℝ) : ℝ :=
  frob C (R * Rᵀ) - ∑ i, y i * (frob (A i) (R * Rᵀ) - b i)

/-- The linear functional `D ↦ G • D` on `ℝ^{p×q}`, as a continuous linear map (for the
Frobenius norm). "`∇_R g = G`" means that the derivative of `g` at `R` is `frobCLM G`. -/
noncomputable def frobCLM {p q : ℕ} (G : Matrix (Fin p) (Fin q) ℝ) : Matrix (Fin p) (Fin q) ℝ →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun D => frob G D
      map_add' := fun D E => by simp [frob, Matrix.mul_add, Matrix.trace_add]
      map_smul' := fun c D => by simp [frob, Matrix.mul_smul, Matrix.trace_smul] }

/-- `R` is a regular point: the constraint gradients `{Aᵢ R}` are linearly independent
(Proposition 2.3, p. 6). -/
def IsRegular {n m r : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (R : Matrix (Fin n) (Fin r) ℝ) : Prop :=
  LinearIndependent ℝ (fun i => A i * R)

/-- `R` is a stationary point of `(N_r)` with multiplier `y`: `R` is feasible and
`∇_R L(R, y) = 0` (Proposition 2.4, p. 7). -/
def IsStationary {n m r : ℕ} (C : Matrix (Fin n) (Fin n) ℝ)
    (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (b : Fin m → ℝ) (R : Matrix (Fin n) (Fin r) ℝ)
    (y : Fin m → ℝ) : Prop :=
  R ∈ nrFeasible A b r ∧ HasFDerivAt (fun R' => lagrangian C A b R' y) (0 : Matrix (Fin n) (Fin r) ℝ →L[ℝ] ℝ) R

/-- The injection `R̂ ∈ ℝ^{n×(r+1)}` of `R ∈ ℝ^{n×r}`: `R` with a zero column appended last
(Proposition 2.5 and its proof, p. 7). -/
def inject {n r : ℕ} (R : Matrix (Fin n) (Fin r) ℝ) : Matrix (Fin n) (Fin (r + 1)) ℝ :=
  Matrix.of fun i j => Fin.lastCases 0 (fun k => R i k) j

end BurerMonteiro.RankIncrease


