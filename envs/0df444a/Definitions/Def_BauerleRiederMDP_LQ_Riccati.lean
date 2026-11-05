-- Prove2me | Definitions.Def_BauerleRiederMDP_LQ_Riccati
-- name    : BauerleRiederMDP_LQ_Riccati
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:24:22.020143+00:00
-- url     : https://prove2.me/theorems/9792d8ce-cc12-48c6-8172-24fc90aa2493
-- title:
--   The Riccati recursion $\tilde Q_n$, the linear feedback $f^*_n$ and the minimal cost operator of the LQ problem
-- statement:
--   In the stochastic linear-quadratic problem, write, for a matrix $Q\in\mathbb R^{(m,m)}$ and $n<N$, the expectations $\mathbb E[A_{n+1}^\top QA_{n+1}]$, $\mathbb E[A_{n+1}^\top QB_{n+1}]$, $\mathbb E[B_{n+1}^\top QB_{n+1}]$ and $\mathbb E[B_{n+1}^\top QA_{n+1}]$ under the law of $(A_{n+1},B_{n+1})$. The **Riccati step** is
--   $$
--   \tilde Q=Q_n+\mathbb E[A_{n+1}^\top QA_{n+1}]-\mathbb E[A_{n+1}^\top QB_{n+1}]\big(\mathbb E[B_{n+1}^\top QB_{n+1}]\big)^{-1}\mathbb E[B_{n+1}^\top QA_{n+1}],
--   $$
--   and the **Riccati matrices** are $\tilde Q_N:=Q_N$ and $\tilde Q_n:=$ the Riccati step applied to $\tilde Q_{n+1}$, for $n=N-1,\dots,0$. The **feedback gain** for $Q$ is $-(\mathbb E[B_{n+1}^\top QB_{n+1}])^{-1}\mathbb E[B_{n+1}^\top QA_{n+1}]\in\mathbb R^{(d,m)}$, and the **candidate optimal decision rule** is
--   $$
--   f^*_n(x)=-\big(\mathbb E[B_{n+1}^\top\tilde Q_{n+1}B_{n+1}]\big)^{-1}\mathbb E[B_{n+1}^\top\tilde Q_{n+1}A_{n+1}]\,x .
--   $$
--   Finally, for $v(x)=x^\top Qx$, the **minimal cost operator** is
--   $$
--   T_nv(x)=\inf_{a\in\mathbb R^d}\big\{x^\top Q_nx+\mathbb E\,v(A_{n+1}x+B_{n+1}a)\big\}.
--   $$
--
--   These are the objects of Theorem 2.6.3 and of the two steps of §2.6.3 that lead to it.
--
--   **Formalization Note** $\tilde Q$ is written `Qt`. The inverse is Mathlib's matrix inverse, which returns $0$ for a singular matrix; under the standing assumptions every inverted matrix is positive definite, so this value is never reached. `Qt n` for $n>N$ is $Q_N$ and is never used. $T_nv(x)$ is a real infimum over the nonempty set $\mathbb R^d$ of a family bounded below by $0$ when $Q_n$ and $Q$ are positive semidefinite.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), §2.6.3, pp.51–52 (PDF 66–67); Theorem 2.6.3, p.52 (PDF 67)

import Mathlib
import Definitions.Def_BauerleRiederMDP_LQ_Model

open MeasureTheory ProbabilityTheory Matrix

namespace BauerleRiederMDP.LQ

namespace LQData

variable {m d N : ℕ}

/-- `𝔼[A_{n+1}^⊤ Q A_{n+1}]` (Bäuerle & Rieder 2011, §2.6.3, p.51, PDF 66), under `ν (n+1)`. -/
noncomputable def EAQA (M : LQData m d N) (n : ℕ) (Q : Matrix (Fin m) (Fin m) ℝ) :
    Matrix (Fin m) (Fin m) ℝ :=
  matExp (m := m) (d := d) (M.ν (n + 1) : Measure _) (fun z => z.1ᵀ * Q * z.1)

/-- `𝔼[A_{n+1}^⊤ Q B_{n+1}]` (Bäuerle & Rieder 2011, §2.6.3, p.51, PDF 66), under `ν (n+1)`. -/
noncomputable def EAQB (M : LQData m d N) (n : ℕ) (Q : Matrix (Fin m) (Fin m) ℝ) :
    Matrix (Fin m) (Fin d) ℝ :=
  matExp (m := m) (d := d) (M.ν (n + 1) : Measure _) (fun z => z.1ᵀ * Q * z.2)

/-- `𝔼[B_{n+1}^⊤ Q B_{n+1}]` (Bäuerle & Rieder 2011, §2.6.3, p.51, PDF 66), under `ν (n+1)`. -/
noncomputable def EBQB (M : LQData m d N) (n : ℕ) (Q : Matrix (Fin m) (Fin m) ℝ) :
    Matrix (Fin d) (Fin d) ℝ :=
  matExp (m := m) (d := d) (M.ν (n + 1) : Measure _) (fun z => z.2ᵀ * Q * z.2)

/-- `𝔼[B_{n+1}^⊤ Q A_{n+1}]` (Bäuerle & Rieder 2011, §2.6.3, p.51, PDF 66), under `ν (n+1)`. -/
noncomputable def EBQA (M : LQData m d N) (n : ℕ) (Q : Matrix (Fin m) (Fin m) ℝ) :
    Matrix (Fin d) (Fin m) ℝ :=
  matExp (m := m) (d := d) (M.ν (n + 1) : Measure _) (fun z => z.2ᵀ * Q * z.1)

/-- **One step of the Riccati recursion** (Bäuerle & Rieder 2011, §2.6.3, p.52, PDF 67, the matrix
`Q̃` "defined as the expression in the brackets"):
`Q_n + 𝔼[A_{n+1}^⊤ Q A_{n+1}] − 𝔼[A_{n+1}^⊤ Q B_{n+1}] (𝔼[B_{n+1}^⊤ Q B_{n+1}])^{−1} 𝔼[B_{n+1}^⊤ Q A_{n+1}]`.

**Formalization Note.** `⁻¹` is Mathlib's matrix inverse (`Matrix.inv`), which returns `0` for a
singular matrix; under `LQData.Standing` and `Q` positive definite, `𝔼[B_{n+1}^⊤ Q B_{n+1}]` is
positive definite, hence invertible, so the junk value is never reached. -/
noncomputable def riccatiStep (M : LQData m d N) (n : ℕ) (Q : Matrix (Fin m) (Fin m) ℝ) :
    Matrix (Fin m) (Fin m) ℝ :=
  M.Q n + M.EAQA n Q - M.EAQB n Q * (M.EBQB n Q)⁻¹ * M.EBQA n Q

/-- **The Riccati matrices `Q̃_n`** of Theorem 2.6.3 a) (Bäuerle & Rieder 2011, p.52, PDF 67):
`Q̃_N := Q_N` and, for `n < N`, `Q̃_n := riccatiStep n Q̃_{n+1}`.

**Formalization Note.** `Q̃` is written `Qt`. For `n > N` the value is `Q_N` (never used: every
statement quantifies over `n ≤ N`). -/
noncomputable def Qt (M : LQData m d N) (n : ℕ) : Matrix (Fin m) (Fin m) ℝ :=
  if n < N then M.riccatiStep n (M.Qt (n + 1)) else M.Q N
termination_by N - n

/-- The feedback gain `−(𝔼[B_{n+1}^⊤ Q B_{n+1}])^{−1} 𝔼[B_{n+1}^⊤ Q A_{n+1}] ∈ ℝ^{(d,m)}` of the
one-step minimizer for the quadratic cost-to-go `v(x) = x^⊤ Q x` (Bäuerle & Rieder 2011, §2.6.3,
p.51, PDF 66). -/
noncomputable def gainOf (M : LQData m d N) (n : ℕ) (Q : Matrix (Fin m) (Fin m) ℝ) :
    Matrix (Fin d) (Fin m) ℝ :=
  -((M.EBQB n Q)⁻¹ * M.EBQA n Q)

/-- **The optimal decision rule** of Theorem 2.6.3 b) (Bäuerle & Rieder 2011, p.52, PDF 67):
`f*_n(x) := −(𝔼[B_{n+1}^⊤ Q̃_{n+1} B_{n+1}])^{−1} 𝔼[B_{n+1}^⊤ Q̃_{n+1} A_{n+1}] x`. -/
noncomputable def fstar (M : LQData m d N) (n : ℕ) (x : Fin m → ℝ) : Fin d → ℝ :=
  M.gainOf n (M.Qt (n + 1)) *ᵥ x

/-- The bracket of the minimal cost operator at `v(x) = x^⊤ Q x` (Bäuerle & Rieder 2011, §2.6.3,
p.51, PDF 66): `x^⊤ Q_n x + 𝔼 v(A_{n+1} x + B_{n+1} a)`.

**Formalization Note.** The expectation is a Bochner integral under `ν (n+1)`; the integrand is a
quadratic polynomial in the entries of `(A_{n+1}, B_{n+1})`, integrable under `LQData.Standing`
(square-integrable entries), so it is a genuine expectation. -/
noncomputable def costArg (M : LQData m d N) (n : ℕ) (Q : Matrix (Fin m) (Fin m) ℝ)
    (x : Fin m → ℝ) (a : Fin d → ℝ) : ℝ :=
  quadForm (M.Q n) x + ∫ z, quadForm Q (lqTransition x a z) ∂(M.ν (n + 1) : Measure _)

/-- **The minimal cost operator** at `v(x) = x^⊤ Q x` (Bäuerle & Rieder 2011, §2.6.3, p.51, PDF 66):
`T_n v(x) = inf_{a ∈ ℝ^d} {x^⊤ Q_n x + 𝔼 v(A_{n+1} x + B_{n+1} a)}`.

**Formalization Note.** A real infimum over the nonempty set `ℝ^d`; for positive semidefinite
`Q_n`, `Q` the bracket is bounded below by `0` (the integrand is nonnegative), so it is the true
infimum, not Lean's junk value of an unbounded family. -/
noncomputable def costOp (M : LQData m d N) (n : ℕ) (Q : Matrix (Fin m) (Fin m) ℝ)
    (x : Fin m → ℝ) : ℝ :=
  ⨅ a : Fin d → ℝ, M.costArg n Q x a

end LQData

end BauerleRiederMDP.LQ


