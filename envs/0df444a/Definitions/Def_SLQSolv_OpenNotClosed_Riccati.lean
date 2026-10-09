-- Prove2me | Definitions.Def_SLQSolv_OpenNotClosed_Riccati
-- name    : SLQSolv_OpenNotClosed_Riccati
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T09:19:32.96452+00:00
-- url     : https://prove2.me/theorems/5859a35c-940d-41f3-8e67-51a0343b1d10
-- title:
--   (2.5), (4.6)–(4.10), p. 2285 — the Riccati equation with pseudoinverse, regular and strongly regular solutions
-- statement:
--   This file defines the Riccati equation of Problem (SLQ) and its regular solutions.
--
--   Write $M^\dagger$ for the Moore–Penrose pseudoinverse of a real matrix $M$. The **Riccati equation** (4.6) is
--
--   $$
--   \begin{cases}
--   \dot P+PA+A^\top P+C^\top PC+Q-\big(PB+C^\top PD+S^\top\big)\big(R+D^\top PD\big)^\dagger\big(B^\top P+D^\top PC+S\big)=0 \quad\text{a.e. } s\in[t_0,T],\\
--   P(T)=G,
--   \end{cases}
--   $$
--
--   for a continuous function $P:[t_0,T]\to\mathbb S^n$. A solution is **regular** on $[t_0,T]$ if
--
--   1. (4.7) $\mathcal R\big(B^\top P+D^\top PC+S\big)\subseteq\mathcal R\big(R+D^\top PD\big)$ for a.e. $s\in[t_0,T]$;
--   2. (4.8) $\big(R+D^\top PD\big)^\dagger\big(B^\top P+D^\top PC+S\big)\in L^2(t_0,T;\mathbb R^{m\times n})$;
--   3. (4.9) $R+D^\top PD\ge 0$ for a.e. $s\in[t_0,T]$;
--
--   and **strongly regular** (on $[0,T]$) if $R+D^\top PD\ge\lambda I$ a.e. for some $\lambda>0$ (4.10). Here $\mathcal R(M)$ is the range of $M$. The file also defines the Lyapunov equation (2.5) of a feedback $\Theta$.
--
--   Regular solvability of (4.6) is the criterion for closed-loop solvability (Theorem 4.3); its failure in Example 7.1 is what separates closed-loop from open-loop solvability.
--
--   **Formalization Note** The equation is stated in integral form, $P(t)=G+\int_t^T F(s,P(s))\,ds$ for $t\in[t_0,T]$ with an integrable right-hand side $F$, which is equivalent to absolute continuity of $P$ with $\dot P+F(s,P)=0$ a.e. The paper's equation is the case $t_0=0$. The pseudoinverse is the published `HarmonicGames.Decomposition.pinv` read on matrices through the Euclidean inner product. Ranges are ranges of the matrices as linear maps.
-- source:
--   Sun–Li–Yong, SIAM J. Control Optim. 54 (2016), (2.5), (4.6)–(4.10), pp. 2279, 2285

import Mathlib
import Definitions.Def_SLQSolv_OpenNotClosed_Setting
import Definitions.Def_HarmonicGames_Decomposition_Pinv

open MeasureTheory Set
open scoped NNReal Matrix

namespace SLQSolv.OpenNotClosed

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

end SLQSolv.OpenNotClosed


