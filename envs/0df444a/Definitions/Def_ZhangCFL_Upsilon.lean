-- Prove2me | Definitions.Def_ZhangCFL_Upsilon
-- name    : ZhangCFL_Upsilon
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:50:17.021222+00:00
-- url     : https://prove2.me/theorems/6d6cd3e9-799a-49cf-939c-1f1129aad40e
-- title:
--   One-variable trace function $\Upsilon_{p,s}(A)=\operatorname{Tr}(K^*A^pK)^s$
-- statement:
--   Fix a square complex matrix $K$ and real numbers $p,s$. For a positive definite matrix $A$, set
--
--   $$
--   \Upsilon_{p,s}(A) = \operatorname{Tr}\big(K^*A^pK\big)^s .
--   $$
--
--   This is $\Psi_{p,0,s}(A,B)$, the case $q=0$ of the two-variable trace function, and it is the function to which the paper reduces the joint convexity and concavity of $\Psi_{p,q,s}$ (Step 1, p.9).
--
--   **Formalization Note** `Upsilon p s K` is the function $A\mapsto\Upsilon_{p,s}(A)$ with $K$ fixed. Powers are `OgawaNagaoka.matPow`; the value is the real part of the trace, which for positive definite $A$ and invertible $K$ is the trace itself.
-- source:
--   Zhang, From Wigner-Yanase-Dyson conjecture to Carlen-Frank-Lieb conjecture, arXiv:1811.01205v2, Step 1, display before Theorem 3.5, p.9

import Mathlib
import Definitions.Def_OgawaNagaoka_matPow

namespace ZhangCFL

open OgawaNagaoka

/-- Zhang, *From Wigner-Yanase-Dyson conjecture to Carlen-Frank-Lieb conjecture*,
arXiv:1811.01205v2, Step 1, p.9: the one-variable trace function
`Υ_{p,s}(A) := Tr(K* A^p K)^s`, `A ∈ P(H)^×`, for a fixed matrix `K`.

**Formalization Note.** `Upsilon p s K` is the function `A ↦ Υ_{p,s}(A)` (with `K` fixed).
Powers are `OgawaNagaoka.matPow` (`cfc` with `Real.rpow`), the usual real powers on positive
definite input. The value is the real part of the trace; on positive definite `A` and invertible
`K` the matrix `(K* A^p K)^s` is positive definite, so this changes no value. -/
noncomputable def Upsilon {n : Type} [Fintype n] [DecidableEq n] (p s : ℝ)
    (K A : Matrix n n ℂ) : ℝ :=
  (matPow (K.conjTranspose * matPow A p * K) s).trace.re

end ZhangCFL


