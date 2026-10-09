-- Prove2me | Definitions.Def_SLQSolv_OpenNotClosed_Examples
-- name    : SLQSolv_OpenNotClosed_Examples
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T09:20:35.496595+00:00
-- url     : https://prove2.me/theorems/23fcb095-aaf2-4073-b879-fd0f0841ada7
-- title:
--   Examples 7.1 and 7.2, pp. 2305–2306 — the data of the two counterexamples, and the feedback gain Θ
-- statement:
--   This file fixes the data of the two examples of §7 and the feedback gain built from a Riccati solution.
--
--   **Example 7.1** is Problem (SLQ)$^0$ with $n=1$, $m=2$, $T=1$ and
--
--   $$
--   A=0,\quad B=(1,1),\quad C=0,\quad D=(1,-1),\quad G=1,\quad Q=0,\quad S=(0,0)^\top,\quad R=\begin{pmatrix}0&0\\0&0\end{pmatrix},
--   $$
--
--   and no inhomogeneous terms. With $u=(u_1,u_2)^\top$ the state equation is $dX=[u_1+u_2]ds+[u_1-u_2]dW$, $X(t)=x$, and the cost is $J^0(t,x;u)=\mathbb EX(1)^2$ ((7.1)–(7.2)).
--
--   **Example 7.2** has $n=m=1$, $T=1$, the deterministic state equation $dX=u\,ds$ ($A=0$, $B=1$, $C=0$, $D=0$) and the cost $J(t,x;u)=X(1)^2+\int_t^1 s^2u(s)^2ds$ ($G=1$, $Q=0$, $S=0$, $R(s)=s^2$), with no inhomogeneous terms.
--
--   For data $(A,B,C,D,Q,S,R)$ and a matrix function $P$, the **feedback gain** is
--
--   $$
--   \Theta(s)=-\big(R(s)+D(s)^\top P(s)D(s)\big)^{-1}\big(B(s)^\top P(s)+D(s)^\top P(s)C(s)+S(s)\big).
--   $$
--
--   For the problem of Example 7.1 with $R$ replaced by $R+\varepsilon I$ and $P=P_\varepsilon$, this is the $\Theta_\varepsilon$ of p. 2306.
--
--   **Formalization Note** The matrix inverse is Lean's `⁻¹`, which agrees with the true inverse whenever $R+D^\top PD$ is invertible (as it is on a strongly regular solution); the paper prints $^{-1}$ there for the same reason.
-- source:
--   Sun–Li–Yong, SIAM J. Control Optim. 54 (2016), Example 7.1 (7.1)–(7.2) p. 2305, Θ_ε p. 2306, Example 7.2 p. 2306

import Mathlib
import Definitions.Def_SLQSolv_OpenNotClosed_Riccati

open MeasureTheory Set
open scoped NNReal Matrix

namespace SLQSolv.OpenNotClosed

variable {Ω : Type*} {n m : ℕ}

/-- The feedback gain `Θ = −(R + DᵀPD)⁻¹(BᵀP + DᵀPC + S)` built from a solution `P` of the Riccati
equation (Lean's matrix inverse; on a strongly regular solution `R + DᵀPD` is invertible). Θ_ε of
§7, p. 2306, is `thetaOf (ex71.addR ε) P_ε`. -/
noncomputable def thetaOf (d : Data Ω n m) (P : ℝ≥0 → Matrix (Fin n) (Fin n) ℝ) (s : ℝ≥0) :
    Matrix (Fin m) (Fin n) ℝ :=
  -((sigmaR d P s)⁻¹ * gainK d P s)

/-- Example 7.1 (p. 2305), (7.1)–(7.2): `n = 1`, `m = 2`, `T = 1`, `A = 0`, `B = (1, 1)`, `C = 0`,
`D = (1, −1)`, `G = 1`, `Q = 0`, `S = (0, 0)ᵀ`, `R = 0`; no inhomogeneous terms (Problem (SLQ)⁰).
The state equation is `dX = [u₁ + u₂] ds + [u₁ − u₂] dW` and the cost is `J⁰ = E X(1)²`. -/
def ex71 : Data Ω 1 2 where
  T := 1
  A := 0
  B := fun _ => !![1, 1]
  C := 0
  D := fun _ => !![1, -1]
  b := 0
  σ := 0
  Q := 0
  S := 0
  R := 0
  q := 0
  ρ := 0
  G := 1
  g := 0

/-- Example 7.2 (p. 2306): `n = m = 1`, `T = 1`, the deterministic state equation `dX = u ds`
(`A = 0`, `B = 1`, `C = 0`, `D = 0`) and the cost `J = X(1)² + ∫ₜ¹ s² u(s)² ds`
(`G = 1`, `Q = 0`, `S = 0`, `R(s) = s²`); no inhomogeneous terms. -/
def ex72 : Data Ω 1 1 where
  T := 1
  A := 0
  B := fun _ => 1
  C := 0
  D := 0
  b := 0
  σ := 0
  Q := 0
  S := 0
  R := fun s => !![(s : ℝ) ^ 2]
  q := 0
  ρ := 0
  G := 1
  g := 0

end SLQSolv.OpenNotClosed


