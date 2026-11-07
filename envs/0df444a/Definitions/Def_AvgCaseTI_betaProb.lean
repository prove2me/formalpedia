-- Prove2me | Definitions.Def_AvgCaseTI_betaProb
-- name    : AvgCaseTI_betaProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:43:22.851849+00:00
-- url     : https://prove2.me/theorems/750b348d-b3b0-4dcc-8f53-7640d70d2907
-- title:
--   Probability $\beta(n,q,k)$ and the error term $\Gamma(n,q)$
-- statement:
--   For a finite field $\mathbb F_q$ and $k\in\mathbb F_q$,
--   $$
--   \beta(n,q,k)=\Pr_{A\in_R\mathrm{GL}(n,q)}\bigl[A\text{ eigenvalue-free in }\mathbb F_q\text{ and }\mathrm{Tr}(A^2)=k\bigr],
--   $$
--   and, for integers $q\ge2$, $n\ge0$,
--   $$
--   \Gamma(n,q)=\tfrac12\,16^{q-1}q^{-\frac{(n+1)(n+q)}{2(q-1)}-1}+(n+1)^2\binom{n+q-2}{q-2}\Bigl(\frac{q}{q-1}\Bigr)^{n}q^{-\frac{n^2}{2(q+1)}+\frac{(q-1)n}{2(q+1)}+\frac{q-1}{4(q+1)}}.
--   $$
--   $\Gamma(n,q)$ is the convergence rate of $\beta(n,q,k)$ in Theorem 6.12 and enters the error bound of Theorem 6.11.
--
--   **Formalization Note** In every use $q\ge2$, so the natural-number differences in $\Gamma$ are exact; non-integer exponents are real powers.
-- source:
--   Li, Li, Qiao, Tao, Wang, On the average-case complexity landscape for Tensor-Isomorphism-complete problems over finite fields, arXiv:2604.00591 (held version sha256 baf552e1…), Theorem 6.12, p.43 (PDF p.45)

import Mathlib
import Definitions.Def_AvgCaseTI_UniqueSimpleEig

set_option autoImplicit false

namespace AvgCaseTI

/-- **`β(n, q, k)`, eigenvalue-free invertible matrices with `Tr(A²) = k`.**

Li, Li, Qiao, Tao, Wang, arXiv:2604.00591 (held version sha256 baf552e1…), Theorem 6.12, p.43
(PDF p.45): "let β(n, q, k) be the probability of a random matrix A ∈ GL(n, q) that satisfies that
(1) A is eigenvalue-free in F_q and (2) Tr(A²) = k."

`betaProb K n k = |{A ∈ GL(n, K) : A eigenvalue-free, Tr(A²) = k}| / |GL(n, K)|`. -/
noncomputable def betaProb (K : Type*) [Field K] (n : ℕ) (k : K) : ℝ :=
  (Nat.card {A : GL (Fin n) K //
      EigenvalueFree (A : Mat K n) ∧ Matrix.trace ((A : Mat K n) * (A : Mat K n)) = k} : ℝ) /
    Nat.card (GL (Fin n) K)

/-- **The error term `Γ(n, q)` of Theorem 6.12**, p.43 (PDF p.45):
`Γ(n, q) := ½·16^{q−1}·q^{−(n+1)(n+q)/(2(q−1)) − 1}
  + (n+1)²·C(n+q−2, q−2)·(q/(q−1))^n·q^{−n²/(2(q+1)) + (q−1)n/(2(q+1)) + (q−1)/(4(q+1))}`.

**Formalization Note.** `q ≥ 2` in every use, so the natural-number differences `q − 1`, `q − 2`,
`n + q − 2` are the true ones; non-integer exponents are real powers (`Real.rpow`). -/
noncomputable def GammaBound (q n : ℕ) : ℝ :=
  1 / 2 * (16 : ℝ) ^ (q - 1) *
      (q : ℝ) ^ (-(((n : ℝ) + 1) * ((n : ℝ) + q)) / (2 * ((q : ℝ) - 1)) - 1) +
    ((n : ℝ) + 1) ^ 2 * ((Nat.choose (n + q - 2) (q - 2) : ℕ) : ℝ) * ((q : ℝ) / ((q : ℝ) - 1)) ^ n *
      (q : ℝ) ^ (-(n : ℝ) ^ 2 / (2 * ((q : ℝ) + 1)) + ((q : ℝ) - 1) * n / (2 * ((q : ℝ) + 1)) +
        ((q : ℝ) - 1) / (4 * ((q : ℝ) + 1)))

end AvgCaseTI


