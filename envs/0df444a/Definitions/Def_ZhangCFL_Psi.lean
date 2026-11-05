-- Prove2me | Definitions.Def_ZhangCFL_Psi
-- name    : ZhangCFL_Psi
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:50:13.19079+00:00
-- url     : https://prove2.me/theorems/6122cb24-a697-45a4-aa22-2b5ffd86aaf0
-- title:
--   Trace function $\Psi_{p,q,s}(A,B)=\operatorname{Tr}(B^{q/2}K^*A^pKB^{q/2})^s$
-- statement:
--   Fix a square complex matrix $K$ and real numbers $p,q,s$. For positive definite matrices $A,B$ of the same size, the paper's trace function (1.1) is
--
--   $$
--   \Psi_{p,q,s}(A,B) = \operatorname{Tr}\big(B^{q/2}K^*A^pKB^{q/2}\big)^s ,
--   $$
--
--   where $K^*$ is the conjugate transpose and all real powers of positive definite matrices are taken by the spectral calculus.
--
--   This family contains the Wigner–Yanase–Dyson trace function ($s=1$, $q=1-p$), the quantities behind the sandwiched and Petz Rényi divergences, and the $\alpha$-$z$ Rényi relative entropies; the mission determines exactly when it is jointly concave or jointly convex in $(A,B)$.
--
--   **Formalization Note** Powers are `OgawaNagaoka.matPow` (the continuous functional calculus with the real power `Real.rpow`), which on positive definite input is the usual real power for every exponent. The value is the real part of the trace; for positive definite $A,B$ and invertible $K$ the matrix inside the trace is positive definite, so its trace is real and taking the real part changes no value. The space is $\mathbb C^n$ for a finite index type $n$.
-- source:
--   Zhang, From Wigner-Yanase-Dyson conjecture to Carlen-Frank-Lieb conjecture, arXiv:1811.01205v2, eq. (1.1), p.1; standing notation p.4

import Mathlib
import Definitions.Def_OgawaNagaoka_matPow

namespace ZhangCFL

open OgawaNagaoka

/-- Zhang, *From Wigner-Yanase-Dyson conjecture to Carlen-Frank-Lieb conjecture*,
arXiv:1811.01205v2, eq. (1.1), p.1: the trace function
`Ψ_{p,q,s}(A, B) = Tr(B^{q/2} K* A^p K B^{q/2})^s`, `p, q, s ∈ ℝ`, for a fixed matrix `K`.

**Formalization Note.** Powers are `OgawaNagaoka.matPow` (`cfc` with `Real.rpow`); the paper
evaluates `Ψ` on positive definite `A, B` (p.4: "for A ∈ P(H)^× and α ∈ ℝ, A^α is always
well-defined"), where these are the usual real powers. The value is the real part of the trace:
on positive definite `A, B` and invertible `K` the matrix inside the trace is positive definite,
so its trace is real and taking the real part changes no value. -/
noncomputable def Psi {n : Type} [Fintype n] [DecidableEq n] (p q s : ℝ)
    (K A B : Matrix n n ℂ) : ℝ :=
  (matPow (matPow B (q / 2) * K.conjTranspose * matPow A p * K * matPow B (q / 2)) s).trace.re

end ZhangCFL


