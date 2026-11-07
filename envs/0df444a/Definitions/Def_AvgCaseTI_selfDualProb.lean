-- Prove2me | Definitions.Def_AvgCaseTI_selfDualProb
-- name    : AvgCaseTI_selfDualProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:42:30.707524+00:00
-- url     : https://prove2.me/theorems/82f0d9f9-0dc2-40b0-8d25-07cebf2fb3d8
-- title:
--   Probability $\sigma(n,q)$ that a uniform matrix is self-dual
-- statement:
--   For a finite field $\mathbb F_q$,
--   $$
--   \sigma(n,q)=\Pr_{A\in_R\mathrm M(n,q)}\bigl[\mathrm{Tr}(A^2)=0\bigr]=\frac{|\{A\in\mathrm M(n,q):\mathrm{Tr}(A^2)=0\}|}{|\mathrm M(n,q)|}.
--   $$
--   It is the probability of the conditioning event of Theorems 3.5 and 6.11.
-- source:
--   Li, Li, Qiao, Tao, Wang, On the average-case complexity landscape for Tensor-Isomorphism-complete problems over finite fields, arXiv:2604.00591 (held version sha256 baf552e1…), Theorem 6.5, p.38 (PDF p.40)

import Mathlib
import Definitions.Def_AvgCaseTI_hull

set_option autoImplicit false

namespace AvgCaseTI

/-- **`σ(n, q)`, the probability that a uniform matrix is self-dual.**

Li, Li, Qiao, Tao, Wang, arXiv:2604.00591 (held version sha256 baf552e1…), Theorem 6.5, p.38
(PDF p.40): "Let σ(n, q) be the probability of a random matrix A ∈ M(n, q) being self-dual,
i.e. Tr(A²) = 0."

`selfDualProb K n = |{A ∈ M(n, K) : Tr(A²) = 0}| / |M(n, K)|`. -/
noncomputable def selfDualProb (K : Type*) [Field K] (n : ℕ) : ℝ :=
  (Nat.card {A : Mat K n // SelfDual A} : ℝ) / Nat.card (Mat K n)

end AvgCaseTI


