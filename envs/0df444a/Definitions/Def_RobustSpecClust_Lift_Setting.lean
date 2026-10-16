-- Prove2me | Definitions.Def_RobustSpecClust_Lift_Setting
-- name    : RobustSpecClust_Lift_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-16T09:42:45.749091+00:00
-- url     : https://prove2.me/theorems/91ae109f-d555-447a-a99b-254b0f6a5ae8
-- title:
--   Formulations (3) and (4): binary assignments and binary PSD lifting
-- statement:
--   Let $N$ be the number of observations and $r$ the number of available clusters. An **assignment matrix** $Z\in\mathbb R^{N\times r}$ is feasible for (3) when every entry is zero or one and each row has at most one entry equal to one. A zero row represents an outlier. A **lifted matrix** $X\in\mathbb R^{N\times N}$ is feasible for (4) when every entry is zero or one, $X$ is positive semidefinite, and $\operatorname{rank}(X)\le r$.
--
--   For a real similarity matrix $K$, real penalty $\gamma$, and all-ones matrix $E_N$, the two objectives are
--
--   $$
--   F_3(Z)=\langle K-\gamma E_N,ZZ^\top\rangle,
--   \qquad F_4(X)=\langle K-\gamma E_N,X\rangle,
--   $$
--
--   where $\langle A,B\rangle=\sum_{i,j}A_{ij}B_{ij}$. Global optimality means feasibility together with an objective at least as large as that of every feasible competitor. These definitions identify precisely the two optimization problems compared in Proposition 1.
--
--   **Formalization Note** The result is deterministic and quantifies over any real $K$ and $\gamma$; neither a Gaussian-kernel assumption nor a range restriction on $\gamma$ is used in Proposition 1. Zero observations and zero clusters are permitted.
-- source:
--   arXiv:1912.07546v3, §3, p. 8, formulations (3) and (4)

import Mathlib

namespace RobustSpecClust.Lift

/-- The Frobenius inner product used in (3) and (4). -/
def frobInner {N : ℕ} (A B : Matrix (Fin N) (Fin N) ℝ) : ℝ :=
  ∑ i, ∑ j, A i j * B i j

/-- The all-ones matrix `E_N`. -/
def ones (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.of fun _ _ => 1

/-- Feasible binary cluster assignments in (3); a zero row represents an outlier. -/
def Feas3 {N r : ℕ} (Z : Matrix (Fin N) (Fin r) ℝ) : Prop :=
  (∀ i k, Z i k = 0 ∨ Z i k = 1) ∧ ∀ i, ∑ k, Z i k ≤ 1

/-- Feasible binary, positive semidefinite matrices of rank at most `r` in (4). -/
def Feas4 {N : ℕ} (r : ℕ) (X : Matrix (Fin N) (Fin N) ℝ) : Prop :=
  (∀ i j, X i j = 0 ∨ X i j = 1) ∧ X.PosSemidef ∧ X.rank ≤ r

/-- The objective of the binary assignment program (3). -/
def obj3 {N r : ℕ} (K : Matrix (Fin N) (Fin N) ℝ) (γ : ℝ)
    (Z : Matrix (Fin N) (Fin r) ℝ) : ℝ :=
  frobInner (K - γ • ones N) (Z * Z.transpose)

/-- The objective of the lifted program (4). -/
def obj4 {N : ℕ} (K : Matrix (Fin N) (Fin N) ℝ) (γ : ℝ)
    (X : Matrix (Fin N) (Fin N) ℝ) : ℝ :=
  frobInner (K - γ • ones N) X

/-- Global optimality for (3). -/
def IsOpt3 {N r : ℕ} (K : Matrix (Fin N) (Fin N) ℝ) (γ : ℝ)
    (Z : Matrix (Fin N) (Fin r) ℝ) : Prop :=
  Feas3 Z ∧ ∀ Z' : Matrix (Fin N) (Fin r) ℝ,
    Feas3 Z' → obj3 K γ Z' ≤ obj3 K γ Z

/-- Global optimality for (4). -/
def IsOpt4 {N : ℕ} (K : Matrix (Fin N) (Fin N) ℝ) (γ : ℝ)
    (r : ℕ) (X : Matrix (Fin N) (Fin N) ℝ) : Prop :=
  Feas4 r X ∧ ∀ X', Feas4 r X' → obj4 K γ X' ≤ obj4 K γ X

end RobustSpecClust.Lift


