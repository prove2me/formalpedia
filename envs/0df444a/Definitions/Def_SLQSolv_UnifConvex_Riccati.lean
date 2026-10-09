-- Prove2me | Definitions.Def_SLQSolv_UnifConvex_Riccati
-- name    : SLQSolv_UnifConvex_Riccati
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T09:17:48.477482+00:00
-- url     : https://prove2.me/theorems/007348e0-96bb-47f5-88d4-d0651bd6328a
-- title:
--   (2.5), (4.6)–(4.10), p. 2279 and p. 2285 — the Riccati equation, regular and strongly regular solutions, Lyapunov equations
-- statement:
--   For a matrix function $P:[0,T]\to\mathbb S^n$ write
--
--   $$\Sigma_P=R+D^\top PD,\qquad K_P=B^\top P+D^\top PC+S .$$
--
--   The **Riccati equation** associated with Problem (SLQ) is
--
--   $$\dot P+PA+A^\top P+C^\top PC+Q-K_P^\top\,\Sigma_P^{\dagger}\,K_P=0\quad\text{a.e. }s\in[0,T],\qquad P(T)=G,\qquad(4.6)$$
--
--   where $M^\dagger$ is the Moore–Penrose pseudoinverse. A solution $P\in C([0,T];\mathbb S^n)$ is **regular** if
--
--   1. $\mathcal R(K_P(s))\subseteq\mathcal R(\Sigma_P(s))$ a.e. (4.7),
--   2. $\Sigma_P^\dagger K_P\in L^2(0,T;\mathbb R^{m\times n})$ (4.8),
--   3. $\Sigma_P(s)\ge0$ a.e. (4.9),
--
--   and **strongly regular** if $\Sigma_P(s)\ge\lambda I$ a.e. on $[0,T]$ for some $\lambda>0$ (4.10).
--
--   For a feedback $\Theta\in L^2(0,T;\mathbb R^{m\times n})$ the **Lyapunov equation** is
--
--   $$\dot P+P(A+B\Theta)+(A+B\Theta)^\top P+(C+D\Theta)^\top P(C+D\Theta)+\Theta^\top R\Theta+S^\top\Theta+\Theta^\top S+Q=0,\qquad P(T)=G,\qquad(2.5)/(4.15)$$
--
--   with (4.18) the case $\Theta=0$.
--
--   These equations are the deterministic side of the paper's characterizations of solvability.
--
--   **Formalization Note** Both equations are stated in integral form: $P$ is continuous and symmetric on $[t_0,T]$, the right-hand side $F(s,P(s))$ is entrywise integrable, and $P(t)=G+\int_t^TF(s,P(s))\,ds$ for $t\in[t_0,T]$; the paper's equations are the case $t_0=0$. The pseudoinverse is the published `HarmonicGames.Decomposition.pinv` read on matrices through the Euclidean inner products; on a strongly regular solution it equals the inverse. Ranges are those of the matrices as linear maps; $L^2$ is entrywise.
-- source:
--   Sun–Li–Yong, SIAM J. Control Optim. 54 (2016), (2.5) p. 2279, (4.6)–(4.10) p. 2285, (4.15) p. 2287, (4.18) p. 2288

import Mathlib
import Definitions.Def_SLQSolv_UnifConvex_Setting
import Definitions.Def_HarmonicGames_Decomposition_Pinv

open MeasureTheory Set
open scoped NNReal Matrix

namespace SLQSolv.UnifConvex

variable {Ω : Type*} {n m : ℕ}

/-- The Moore–Penrose pseudoinverse `M†` of a real matrix (p. 2277), w.r.t. the Euclidean inner
products: the published `HarmonicGames.Decomposition.pinv` of `M` as a linear map. -/
noncomputable def mpinv {k l : ℕ} (M : Matrix (Fin k) (Fin l) ℝ) : Matrix (Fin l) (Fin k) ℝ :=
  Matrix.toEuclideanLin.symm (HarmonicGames.Decomposition.pinv (Matrix.toEuclideanLin M))

/-- `∫ₐᵇ F(s) ds` for a matrix-valued `F`, entrywise. -/
noncomputable def matInt {k l : ℕ} (a b : ℝ) (F : ℝ≥0 → Matrix (Fin k) (Fin l) ℝ) :
    Matrix (Fin k) (Fin l) ℝ :=
  Matrix.of fun i j => ∫ s in Icc a b, F s.toNNReal i j

/-- `R + DᵀPD` at time `s`. -/
def sigmaR (d : Data Ω n m) (P : ℝ≥0 → Matrix (Fin n) (Fin n) ℝ) (s : ℝ≥0) :
    Matrix (Fin m) (Fin m) ℝ :=
  d.R s + (d.D s)ᵀ * P s * d.D s

/-- `BᵀP + DᵀPC + S` at time `s`. -/
def gainK (d : Data Ω n m) (P : ℝ≥0 → Matrix (Fin n) (Fin n) ℝ) (s : ℝ≥0) :
    Matrix (Fin m) (Fin n) ℝ :=
  (d.B s)ᵀ * P s + (d.D s)ᵀ * P s * d.C s + d.S s

/-- The right-hand side of the Riccati equation (4.6), written `Ṗ + F(s, P) = 0`:
`F = PA + AᵀP + CᵀPC + Q − (PB + CᵀPD + Sᵀ)(R + DᵀPD)†(BᵀP + DᵀPC + S)`. -/
noncomputable def riccatiRhs (d : Data Ω n m) (P : ℝ≥0 → Matrix (Fin n) (Fin n) ℝ) (s : ℝ≥0) :
    Matrix (Fin n) (Fin n) ℝ :=
  P s * d.A s + (d.A s)ᵀ * P s + (d.C s)ᵀ * P s * d.C s + d.Q s
    - (gainK d P s)ᵀ * mpinv (sigmaR d P s) * gainK d P s

/-- `P ∈ C([t₀, T]; 𝕊ⁿ)` solves the Riccati equation (4.6) (p. 2285) on `[t₀, T]`, in integral form:
`P(t) = G + ∫ₜᵀ F(s, P(s)) ds` for `t ∈ [t₀, T]` with an integrable right-hand side (i.e. `P` is
absolutely continuous, `Ṗ + F(s, P) = 0` a.e., `P(T) = G`). The paper's equation is the case `t₀ = 0`;
Example 7.1 (p. 2305) uses it on `[t, T]`. -/
structure IsRiccatiSolOn (d : Data Ω n m) (t₀ : ℝ≥0) (P : ℝ≥0 → Matrix (Fin n) (Fin n) ℝ) :
    Prop where
  cont : ContinuousOn P (Icc t₀ d.T)
  symm : ∀ s, t₀ ≤ s → s ≤ d.T → (P s).IsSymm
  integrable : ∀ i j,
    IntegrableOn (fun s : ℝ => riccatiRhs d P s.toNNReal i j) (Icc (t₀ : ℝ) d.T)
  eq : ∀ t, t₀ ≤ t → t ≤ d.T → ∀ i j,
    P t i j = d.G i j + ∫ s in Icc (t : ℝ) d.T, riccatiRhs d P s.toNNReal i j

/-- `P ∈ C([0, T]; 𝕊ⁿ)` solves the Riccati equation (4.6) on `[0, T]`. -/
def IsRiccatiSol (d : Data Ω n m) (P : ℝ≥0 → Matrix (Fin n) (Fin n) ℝ) : Prop :=
  IsRiccatiSolOn d 0 P

/-- A regular solution on `[t₀, T]` (p. 2285): a solution with (4.7)
`ℛ(BᵀP + DᵀPC + S) ⊆ ℛ(R + DᵀPD)` a.e., (4.8) `(R + DᵀPD)†(BᵀP + DᵀPC + S) ∈ L²(t₀, T; ℝ^{m×n})`
and (4.9) `R + DᵀPD ≥ 0` a.e. on `[t₀, T]`. -/
def IsRegularOn (d : Data Ω n m) (t₀ : ℝ≥0) (P : ℝ≥0 → Matrix (Fin n) (Fin n) ℝ) : Prop :=
  IsRiccatiSolOn d t₀ P ∧
    (∀ᵐ s ∂(volume.restrict (Icc (t₀ : ℝ) d.T)),
      LinearMap.range (Matrix.mulVecLin (gainK d P s.toNNReal))
        ≤ LinearMap.range (Matrix.mulVecLin (sigmaR d P s.toNNReal))) ∧
    MatLpOn 2 t₀ d.T (fun s => mpinv (sigmaR d P s) * gainK d P s) ∧
    ∀ᵐ s ∂(volume.restrict (Icc (t₀ : ℝ) d.T)), (sigmaR d P s.toNNReal).PosSemidef

/-- A regular solution of (4.6) on `[0, T]` (p. 2285). -/
def IsRegular (d : Data Ω n m) (P : ℝ≥0 → Matrix (Fin n) (Fin n) ℝ) : Prop :=
  IsRegularOn d 0 P

/-- A strongly regular solution (p. 2285): a solution on `[0, T]` with (4.10) `R + DᵀPD ≥ λI` a.e.
for some `λ > 0`. -/
def IsStronglyRegular (d : Data Ω n m) (P : ℝ≥0 → Matrix (Fin n) (Fin n) ℝ) : Prop :=
  IsRiccatiSol d P ∧ ∃ lam : ℝ, 0 < lam ∧
    ∀ᵐ s ∂(volume.restrict (Icc (0 : ℝ) d.T)),
      (sigmaR d P s.toNNReal - lam • (1 : Matrix (Fin m) (Fin m) ℝ)).PosSemidef

/-- The right-hand side of the Lyapunov equation (2.5)/(4.15) for a feedback `Θ`:
`P(A + BΘ) + (A + BΘ)ᵀP + (C + DΘ)ᵀP(C + DΘ) + ΘᵀRΘ + SᵀΘ + ΘᵀS + Q`. With `Θ = 0` it is (3.2)/(4.18). -/
noncomputable def lyapunovRhs (d : Data Ω n m) (Θ : ℝ≥0 → Matrix (Fin m) (Fin n) ℝ)
    (P : ℝ≥0 → Matrix (Fin n) (Fin n) ℝ) (s : ℝ≥0) : Matrix (Fin n) (Fin n) ℝ :=
  P s * (d.A s + d.B s * Θ s) + (d.A s + d.B s * Θ s)ᵀ * P s
    + (d.C s + d.D s * Θ s)ᵀ * P s * (d.C s + d.D s * Θ s)
    + (Θ s)ᵀ * d.R s * Θ s + (d.S s)ᵀ * Θ s + (Θ s)ᵀ * d.S s + d.Q s

/-- `P ∈ C([0, T]; 𝕊ⁿ)` solves the Lyapunov equation (2.5) for `Θ`, in integral form:
`P(t) = G + ∫ₜᵀ L(s, P(s)) ds` on `[0, T]`. -/
structure IsLyapunovSol (d : Data Ω n m) (Θ : ℝ≥0 → Matrix (Fin m) (Fin n) ℝ)
    (P : ℝ≥0 → Matrix (Fin n) (Fin n) ℝ) : Prop where
  cont : ContinuousOn P (Icc 0 d.T)
  symm : ∀ s ≤ d.T, (P s).IsSymm
  integrable : ∀ i j,
    IntegrableOn (fun s : ℝ => lyapunovRhs d Θ P s.toNNReal i j) (Icc 0 (d.T : ℝ))
  eq : ∀ t ≤ d.T, ∀ i j,
    P t i j = d.G i j + ∫ s in Icc (t : ℝ) d.T, lyapunovRhs d Θ P s.toNNReal i j

end SLQSolv.UnifConvex


