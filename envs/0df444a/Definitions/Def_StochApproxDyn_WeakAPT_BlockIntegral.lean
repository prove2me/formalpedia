-- Prove2me | Definitions.Def_StochApproxDyn_WeakAPT_BlockIntegral
-- name    : StochApproxDyn_WeakAPT_BlockIntegral
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T07:05:07.304756+00:00
-- url     : https://prove2.me/theorems/1a2ff26c-b88f-41c7-a074-feee92be6a5e
-- title:
--   Block integrals $U_n(f,T)=\int_{(n-1)T}^{nT} f(X(s))\,ds$ (§10, proof of Theorem 10.1)
-- statement:
--   Let $X:\mathbb R_+\times\Omega\to M$ be a process with values in a metric space $M$, let $f:M\to\mathbb R$ and $T>0$. For $n\ge1$ the **block integral** of $f$ along $X$ over the $n$-th window of length $T$ is the random variable
--   $$U_n(f,T)(\omega)=\int_{(n-1)T}^{nT} f\big(X(s,\omega)\big)\,ds .$$
--
--   The proof of Theorem 10.1 splits time into consecutive windows of length $T$ and compares these block integrals for $f$ and for $f\circ\Phi_T$; averages of the $U_n$ are the integrals of $f$ against occupation measures at the times $nT$.
--
--   **Formalization Note** The page prints $f(X(x(s)))$, a typo for $f(X(s))$. The index follows the paper ($n\ge1$); at $n=0$ the definition gives the empty integral $\int_0^0=0$, which is never used. The integral is the interval integral over real $s$, with the path evaluated at $s\in\mathbb R_{\ge0}$.
-- source:
--   Benaïm, Dynamics of Stochastic Approximation Algorithms, Séminaire de Probabilités XXXIII, LNM 1709 (1999), DOI 10.1007/BFb0096509, Section 10, proof of Theorem 10.1, p. 61 (PDF p. 62), definition of U_n(f, T)

import Mathlib

namespace StochApproxDyn.WeakAPT

open scoped NNReal

/-- The block integrals of the proof of Theorem 10.1 (Benaïm 1999, §10, p. 61): for
`f : M → ℝ`, `T > 0` and `n ≥ 1`,
`U_n(f, T)(ω) = ∫_{(n-1)T}^{nT} f(X(s, ω)) ds`.
The paper's printed `f(X(x(s)))` is a typo for `f(X(s))`. The index follows the paper
(`n ≥ 1`); the value at `n = 0` is the empty integral `∫_0^0 = 0` and is never used. Time `s`
runs over `ℝ` for the interval integral and the path is evaluated at `s ∈ ℝ≥0`. -/
noncomputable def blockIntegral {Ω M : Type*} (X : ℝ≥0 → Ω → M) (f : M → ℝ) (T : ℝ≥0)
    (n : ℕ) (ω : Ω) : ℝ :=
  ∫ s in ((n - 1 : ℕ) : ℝ) * T..(n : ℝ) * T, f (X s.toNNReal ω)

end StochApproxDyn.WeakAPT


