-- Prove2me | Definitions.Def_MeanFieldLQ_Feedback_Riccati
-- name    : MeanFieldLQ_Feedback_Riccati
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T05:35:39.703983+00:00
-- url     : https://prove2.me/theorems/b10d2dc2-994b-4263-b283-e4df755100a8
-- title:
--   §4, pp. 2825–2828 — Σ₀, Σ₁, the Riccati equations (4.8)–(4.9) in integral form, the feedback gains, the closed-loop system and the processes u*, Y, Z of Theorem 4.1
-- statement:
--   This file defines the Riccati objects of Theorem 4.1 of Yong (2013), on top of the data of Problem (MF-LQ).
--
--   For a symmetric-matrix-valued function $P$ on $[0,T]$ set, pointwise in $s$,
--   $$\Sigma_0=R+D^TPD,\qquad \Sigma_1=R+\bar R+(D+\bar D)^TP(D+\bar D).$$
--
--   1. **Riccati equation (4.8).** $P$ solves
--   $$\dot P+PA+A^TP+C^TPC+Q-(PB+C^TPD)\Sigma_0^{-1}(B^TP+D^TPC)=0,\qquad P(T)=G,$$
--   in integral form: $P$ is continuous and symmetric on $[0,T]$, the right-hand side is integrable, $P(t)=G+\int_t^T F(s,P(s))\,ds$ for $t\in[0,T]$, and $\Sigma_0(s)\ge\varepsilon I$ on $[0,T]$ for some $\varepsilon>0$ (the regular class).
--   2. **Riccati equation (4.9).** Given $P$, $\Pi$ solves
--   $$\dot\Pi+\Pi(A+\bar A)+(A+\bar A)^T\Pi+(C+\bar C)^TP(C+\bar C)+Q+\bar Q-\big[\Pi(B+\bar B)+(C+\bar C)^TP(D+\bar D)\big]\Sigma_1^{-1}\big[(B+\bar B)^T\Pi+(D+\bar D)^TP(C+\bar C)\big]=0,$$
--   with $\Pi(T)=G+\bar G$, in the same integral sense (continuous, symmetric, integrable right-hand side).
--   3. **Gains.** $K_0=\Sigma_0^{-1}(B^TP+D^TPC)$ and $K_1=\Sigma_1^{-1}\big[(B+\bar B)^T\Pi+(D+\bar D)^TP(C+\bar C)\big]$.
--   4. **Closed-loop system.** $X^*$ solves
--   $$dX^*=\Big\{[A-BK_0](X^*-\mathbb E[X^*])+[(A+\bar A)-(B+\bar B)K_1]\mathbb E[X^*]\Big\}dt+\Big\{[C-DK_0](X^*-\mathbb E[X^*])+[(C+\bar C)-(D+\bar D)K_1]\mathbb E[X^*]\Big\}dW,$$
--   with $X^*(0)=x$, where $\mathbb E[X^*]$ is the mean of the solution itself.
--   5. **Feedback and adjoint processes.** $u^*=-K_0(X^*-\mathbb E[X^*])-K_1\mathbb E[X^*]$, $Y=P(X^*-\mathbb E[X^*])+\Pi\,\mathbb E[X^*]$ and $Z=[PC-PDK_0](X^*-\mathbb E[X^*])+[P(C+\bar C)-P(D+\bar D)K_1]\mathbb E[X^*]$.
--   6. **Squares of the verification argument.** $w_0=u-\mathbb E[u]+K_0(X-\mathbb E[X])$ and $w_1=\mathbb E[u]+K_1\mathbb E[X]$.
--
--   These are the objects in which Theorem 4.1 expresses the optimal control as a state feedback.
--
--   **Formalization Note.** The coefficients are only $L^\infty$, so Riccati solutions are absolutely continuous and solve the equation for a.e. $s$. The equations are therefore stated in integral form, entrywise. The paper's "differentiable" in (4.1) is not used. `Matrix.inv` is $0$ on singular matrices. The regular class $\Sigma_0\ge\varepsilon I$ keeps $\Sigma_0^{-1}$ a true inverse. For (4.9), $\Sigma_1\ge\delta I$ follows from (H2) once $P\ge0$, and no condition is added to the class of $\Pi$.
-- source:
--   Yong, Linear-Quadratic Optimal Control Problems for Mean-Field Stochastic Differential Equations, SIAM J. Control Optim. 51(4) (2013), pp. 2825–2828, (4.5)–(4.6), (4.8)–(4.9), Theorem 4.1 (closed-loop system, u*, Y, Z), proof of Theorem 4.1

import Mathlib
import Definitions.Def_MeanFieldLQ_Feedback_Setting

open MeasureTheory ProbabilityTheory Matrix
open scoped NNReal ENNReal

namespace MeanFieldLQ.Feedback

open Peng1990.SMP

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- `Σ₀ = R + DᵀPD` (p. 2827), pointwise in `s`, for a matrix function `P`. -/
def Sigma0 {n m : ℕ} (d : Data n m) (P : ℝ≥0 → Matrix (Fin n) (Fin n) ℝ) (s : ℝ≥0) :
    Matrix (Fin m) (Fin m) ℝ :=
  d.R s + (d.D s)ᵀ * P s * d.D s

/-- `Σ₁ = R + R̄ + (D + D̄)ᵀP(D + D̄)` (p. 2827), pointwise in `s`. -/
def Sigma1 {n m : ℕ} (d : Data n m) (P : ℝ≥0 → Matrix (Fin n) (Fin n) ℝ) (s : ℝ≥0) :
    Matrix (Fin m) (Fin m) ℝ :=
  d.R s + d.Rbar s + (d.D s + d.Dbar s)ᵀ * P s * (d.D s + d.Dbar s)

/-- The right-hand side `F(s, P)` of the Riccati equation (4.8), written `Ṗ + F(s, P) = 0`:
`F = PA + AᵀP + CᵀPC + Q − (PB + CᵀPD)Σ₀⁻¹(BᵀP + DᵀPC)`. -/
noncomputable def riccatiPRhs {n m : ℕ} (d : Data n m) (P : ℝ≥0 → Matrix (Fin n) (Fin n) ℝ)
    (s : ℝ≥0) : Matrix (Fin n) (Fin n) ℝ :=
  P s * d.A s + (d.A s)ᵀ * P s + (d.C s)ᵀ * P s * d.C s + d.Q s
    - (P s * d.B s + (d.C s)ᵀ * P s * d.D s) * (Sigma0 d P s)⁻¹
      * ((d.B s)ᵀ * P s + (d.D s)ᵀ * P s * d.C s)

/-- The right-hand side `F(s, Π)` of the Riccati equation (4.9), written `Π̇ + F(s, Π) = 0`
(the solution `P` of (4.8) enters as a coefficient):
`F = Π(A + Ā) + (A + Ā)ᵀΠ + (C + C̄)ᵀP(C + C̄) + Q + Q̄
  − [Π(B + B̄) + (C + C̄)ᵀP(D + D̄)]Σ₁⁻¹[(B + B̄)ᵀΠ + (D + D̄)ᵀP(C + C̄)]`. -/
noncomputable def riccatiPiRhs {n m : ℕ} (d : Data n m)
    (P Pi : ℝ≥0 → Matrix (Fin n) (Fin n) ℝ) (s : ℝ≥0) : Matrix (Fin n) (Fin n) ℝ :=
  Pi s * (d.A s + d.Abar s) + (d.A s + d.Abar s)ᵀ * Pi s
    + (d.C s + d.Cbar s)ᵀ * P s * (d.C s + d.Cbar s) + d.Q s + d.Qbar s
    - (Pi s * (d.B s + d.Bbar s) + (d.C s + d.Cbar s)ᵀ * P s * (d.D s + d.Dbar s))
      * (Sigma1 d P s)⁻¹
      * ((d.B s + d.Bbar s)ᵀ * Pi s + (d.D s + d.Dbar s)ᵀ * P s * (d.C s + d.Cbar s))

/-- `P` solves the Riccati equation (4.8) on `[0, T]` (p. 2827) in integral form, in the regular
class: `P` is continuous and symmetric on `[0, T]`, the right-hand side is integrable on `[0, T]`
(entrywise), `P(t) = G + ∫ₜᵀ F(s, P(s)) ds` for every `t ∈ [0, T]` (equivalently `P` is absolutely
continuous with `Ṗ + F(s, P) = 0` for a.e. `s` and `P(T) = G`), and `Σ₀(s) ≥ εI` on `[0, T]` for some
`ε > 0`. -/
structure IsRiccatiP {n m : ℕ} (T : ℝ≥0) (d : Data n m) (P : ℝ≥0 → Matrix (Fin n) (Fin n) ℝ) :
    Prop where
  cont : ContinuousOn P (Set.Icc 0 T)
  symm : ∀ s ≤ T, (P s).IsSymm
  integrable : ∀ i j, IntegrableOn (fun s : ℝ => riccatiPRhs d P s.toNNReal i j)
    (Set.Icc 0 (T : ℝ))
  eq : ∀ t ≤ T, ∀ i j,
    P t i j = d.G i j + ∫ s in Set.Icc (t : ℝ) T, riccatiPRhs d P s.toNNReal i j
  regular : ∃ ε : ℝ, 0 < ε ∧
    ∀ s ≤ T, (Sigma0 d P s - ε • (1 : Matrix (Fin m) (Fin m) ℝ)).PosSemidef

/-- `Π` solves the Riccati equation (4.9) on `[0, T]` (p. 2827), for the given `P`, in integral
form: `Π` is continuous and symmetric on `[0, T]`, the right-hand side is integrable on `[0, T]`,
and `Π(t) = G + Ḡ + ∫ₜᵀ F(s, Π(s)) ds` for every `t ∈ [0, T]`. -/
structure IsRiccatiPi {n m : ℕ} (T : ℝ≥0) (d : Data n m)
    (P Pi : ℝ≥0 → Matrix (Fin n) (Fin n) ℝ) : Prop where
  cont : ContinuousOn Pi (Set.Icc 0 T)
  symm : ∀ s ≤ T, (Pi s).IsSymm
  integrable : ∀ i j, IntegrableOn (fun s : ℝ => riccatiPiRhs d P Pi s.toNNReal i j)
    (Set.Icc 0 (T : ℝ))
  eq : ∀ t ≤ T, ∀ i j,
    Pi t i j = d.G i j + d.Gbar i j + ∫ s in Set.Icc (t : ℝ) T, riccatiPiRhs d P Pi s.toNNReal i j

/-- The first feedback gain `K₀ = Σ₀⁻¹(BᵀP + DᵀPC)` (p. 2827). -/
noncomputable def K0 {n m : ℕ} (d : Data n m) (P : ℝ≥0 → Matrix (Fin n) (Fin n) ℝ) (s : ℝ≥0) :
    Matrix (Fin m) (Fin n) ℝ :=
  (Sigma0 d P s)⁻¹ * ((d.B s)ᵀ * P s + (d.D s)ᵀ * P s * d.C s)

/-- The second feedback gain `K₁ = Σ₁⁻¹[(B + B̄)ᵀΠ + (D + D̄)ᵀP(C + C̄)]` (p. 2827). -/
noncomputable def K1 {n m : ℕ} (d : Data n m) (P Pi : ℝ≥0 → Matrix (Fin n) (Fin n) ℝ)
    (s : ℝ≥0) : Matrix (Fin m) (Fin n) ℝ :=
  (Sigma1 d P s)⁻¹ * ((d.B s + d.Bbar s)ᵀ * Pi s + (d.D s + d.Dbar s)ᵀ * P s * (d.C s + d.Cbar s))

/-- The closed-loop system of Theorem 4.1 (p. 2827): `X*` solves on `[0, T]`
`dX* = {[A − BK₀](X* − 𝔼[X*]) + [(A + Ā) − (B + B̄)K₁]𝔼[X*]} dt
  + {[C − DK₀](X* − 𝔼[X*]) + [(C + C̄) − (D + D̄)K₁]𝔼[X*]} dW`, `X*(0) = x`,
where `𝔼[X*]` is the mean of the solution itself. -/
def IsClosedLoop {n m : ℕ} (μ : Measure Ω) {W : ℝ≥0 → Ω → Fin 1 → ℝ}
    (hW : IsStdBrownian μ W) (T : ℝ≥0) (d : Data n m) (P Pi : ℝ≥0 → Matrix (Fin n) (Fin n) ℝ)
    (x : Fin n → ℝ) (X : ℝ≥0 → Ω → Fin n → ℝ) : Prop :=
  SolvesSDE (filt μ hW) μ T W x
    (fun s _ y => (d.A s - d.B s * K0 d P s) *ᵥ (y - mean μ X s)
      + ((d.A s + d.Abar s) - (d.B s + d.Bbar s) * K1 d P Pi s) *ᵥ mean μ X s)
    (fun _ s _ y => (d.C s - d.D s * K0 d P s) *ᵥ (y - mean μ X s)
      + ((d.C s + d.Cbar s) - (d.D s + d.Dbar s) * K1 d P Pi s) *ᵥ mean μ X s)
    X

/-- The feedback control of Theorem 4.1 (p. 2827):
`u* = −K₀(X* − 𝔼[X*]) − K₁𝔼[X*]`. -/
noncomputable def feedbackU {n m : ℕ} (μ : Measure Ω) (d : Data n m)
    (P Pi : ℝ≥0 → Matrix (Fin n) (Fin n) ℝ) (X : ℝ≥0 → Ω → Fin n → ℝ) (s : ℝ≥0) (ω : Ω) :
    Fin m → ℝ :=
  -(K0 d P s *ᵥ (X s ω - mean μ X s)) - K1 d P Pi s *ᵥ mean μ X s

/-- The adjoint process of Theorem 4.1 (p. 2827): `Y = P(X* − 𝔼[X*]) + Π𝔼[X*]`. -/
noncomputable def adjY {n : ℕ} (μ : Measure Ω) (P Pi : ℝ≥0 → Matrix (Fin n) (Fin n) ℝ)
    (X : ℝ≥0 → Ω → Fin n → ℝ) (s : ℝ≥0) (ω : Ω) : Fin n → ℝ :=
  P s *ᵥ (X s ω - mean μ X s) + Pi s *ᵥ mean μ X s

/-- The adjoint process of Theorem 4.1 (p. 2827):
`Z = [PC − PDK₀](X* − 𝔼[X*]) + [P(C + C̄) − P(D + D̄)K₁]𝔼[X*]`. -/
noncomputable def adjZ {n m : ℕ} (μ : Measure Ω) (d : Data n m)
    (P Pi : ℝ≥0 → Matrix (Fin n) (Fin n) ℝ) (X : ℝ≥0 → Ω → Fin n → ℝ) (s : ℝ≥0) (ω : Ω) :
    Fin n → ℝ :=
  (P s * d.C s - P s * d.D s * K0 d P s) *ᵥ (X s ω - mean μ X s)
    + (P s * (d.C s + d.Cbar s) - P s * (d.D s + d.Dbar s) * K1 d P Pi s) *ᵥ mean μ X s

/-- The first square in the completion of squares (proof of Theorem 4.1, p. 2828):
`u − 𝔼[u] + Σ₀⁻¹(BᵀP + DᵀPC)(X − 𝔼[X])`. -/
noncomputable def gap0 {n m : ℕ} (μ : Measure Ω) (d : Data n m)
    (P : ℝ≥0 → Matrix (Fin n) (Fin n) ℝ) (u : ℝ≥0 → Ω → Fin m → ℝ)
    (X : ℝ≥0 → Ω → Fin n → ℝ) (s : ℝ≥0) (ω : Ω) : Fin m → ℝ :=
  u s ω - mean μ u s + K0 d P s *ᵥ (X s ω - mean μ X s)

/-- The second square in the completion of squares (proof of Theorem 4.1, p. 2828):
`𝔼[u] + Σ₁⁻¹((B + B̄)ᵀΠ + (D + D̄)ᵀP(C + C̄))𝔼[X]`. -/
noncomputable def gap1 {n m : ℕ} (μ : Measure Ω) (d : Data n m)
    (P Pi : ℝ≥0 → Matrix (Fin n) (Fin n) ℝ) (u : ℝ≥0 → Ω → Fin m → ℝ)
    (X : ℝ≥0 → Ω → Fin n → ℝ) (s : ℝ≥0) : Fin m → ℝ :=
  mean μ u s + K1 d P Pi s *ᵥ mean μ X s

end MeanFieldLQ.Feedback


