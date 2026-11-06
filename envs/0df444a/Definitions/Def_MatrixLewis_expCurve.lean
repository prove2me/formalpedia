-- Prove2me | Definitions.Def_MatrixLewis_expCurve
-- name    : MatrixLewis_expCurve
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:12:13.170122+00:00
-- url     : https://prove2.me/theorems/4ffe8589-33e5-471a-ac5e-6dad448a99b2
-- title:
--   Exponential-curve objects $\dot M$, $\Xi$, $\tilde T_t$ and $\psi(t)$
-- statement:
--   Let the data be in normalized position, let $T$ be the row operator of the $B_i=B_i(I)$, and let $X\in\mathbb S^n$. Put
--   $$
--   \dot M:=\frac{d}{dt}M_*(I+tX)\Big|_{t=0},\qquad \Xi:=\tfrac12(\dot M\otimes I_n-I_m\otimes X),
--   $$
--   $$
--   \tilde T_t:=e^{t\Xi}\,T\,e^{-tX/2},\qquad \psi(t):=\operatorname{tr}\bigl((\tilde T_t^\top\tilde T_t)^{p'}\bigr)\quad(t\in\mathbb R).
--   $$
--   $\dot M$ is the velocity of the dual minimizer and $\psi$ the power trace along the exponential curve $t\mapsto(e^{tX},e^{t\dot M})$.
--
--   **Formalization Note** $\dot M$ is the entrywise derivative; the exponentials are the functional calculus.
-- source:
--   Kelner, Jiang, Sidford, Zhang, Matrix Lewis Weights: Solving Semidefinite Programs in Square Root Constraints Iterations, STOC 2027 submission (manuscript sha256 31ce765b…), Lemma 3.16, p.25

import Mathlib
import Definitions.Def_MatrixLewis_maximizer
import Definitions.Def_MatrixLewis_rowOp

open scoped Kronecker

namespace MatrixLewis

/-- The velocity `Ṁ := d/dt M*(I + tX)|_{t=0}` of the dual minimizer at the slack `I` in the
direction `X` (Kelner–Jiang–Sidford–Zhang, *Matrix Lewis Weights: Solving Semidefinite Programs in Square Root Constraints Iterations*, STOC 2027 submission (manuscript sha256 31ce765b…), Lemma 3.16, p.25), taken entrywise. -/
noncomputable def dualVelocity {n m : ℕ} (q : ℝ) (A : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (X : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  Matrix.of fun a b => deriv (fun t : ℝ => dualMin q A (1 + t • X) a b) 0

/-- The generator `Ξ := ½(Ṁ ⊗ Iₙ − I_m ⊗ X)` on `ℝᵐ ⊗ ℝⁿ` (Kelner–Jiang–Sidford–Zhang, *Matrix Lewis Weights: Solving Semidefinite Programs in Square Root Constraints Iterations*, STOC 2027 submission (manuscript sha256 31ce765b…), Lemma 3.16, p.25). -/
noncomputable def xiGen {n m : ℕ} (q : ℝ) (A : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (X : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin m × Fin n) (Fin m × Fin n) ℝ :=
  (1 / 2 : ℝ) • (dualVelocity q A X ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℝ) -
    (1 : Matrix (Fin m) (Fin m) ℝ) ⊗ₖ X)

/-- `T̃_t := e^{tΞ} T e^{−tX/2}`, with `T` the row operator of the `Bᵢ(I)` (Kelner–Jiang–Sidford–Zhang, *Matrix Lewis Weights: Solving Semidefinite Programs in Square Root Constraints Iterations*, STOC 2027 submission (manuscript sha256 31ce765b…),
Lemma 3.16, p.25). -/
noncomputable def Ttilde {n m : ℕ} (q : ℝ) (A : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (X : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) : Matrix (Fin m × Fin n) (Fin n) ℝ :=
  mexp (t • xiGen q A X) * rowOp (scaled A 1) * mexp ((-t / 2) • X)

/-- The power trace `ψ(t) := tr((T̃_tᵀ T̃_t)^{p′})` along the exponential curve (Kelner–Jiang–Sidford–Zhang, *Matrix Lewis Weights: Solving Semidefinite Programs in Square Root Constraints Iterations*, STOC 2027 submission (manuscript sha256 31ce765b…),
Lemma 3.16, p.25). -/
noncomputable def psiTrace {n m : ℕ} (q : ℝ) (A : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (X : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) : ℝ :=
  (mpow (pDual q) ((Ttilde q A X t).transpose * Ttilde q A X t)).trace

end MatrixLewis


