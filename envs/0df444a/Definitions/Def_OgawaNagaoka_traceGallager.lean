-- Prove2me | Definitions.Def_OgawaNagaoka_traceGallager
-- name    : OgawaNagaoka_traceGallager
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T15:23:15.861455+00:00
-- url     : https://prove2.me/theorems/f910bcee-0676-4741-a1be-a83f3d5224cc
-- title:
--   $f(\pi)=\mathrm{Tr}\,(\sum_i\pi_i\rho_i^{1/\beta})^\beta$
-- statement:
--   For operators $\rho_i$ indexed by a finite alphabet, a distribution $\pi$ on it and $0<\beta\le1$,
--
--   $$
--   f(\pi)=\mathrm{Tr}\Big(\sum_{i=1}^a\pi_i\rho_i^{1/\beta}\Big)^\beta .
--   $$
--
--   Applied to the codeword states $\rho_u$, $u\in\mathcal X^n$, and a distribution $P$ on $\mathcal X^n$ it gives the quantity $\mathrm{Tr}(\sum_uP(u)\rho_u^{1/\beta})^\beta$ of (5), (6) and Lemma 2; $-\log f$ at $\beta=s+1$ is the function $E_0(s,\pi)$ of (11).
--
--   **Formalization Note** Powers are taken by the functional calculus (`matPow`); the trace is its real part. Defined for every real $\pi$ and $\beta$; statements restrict to the simplex and $0<\beta\le1$.
-- source:
--   Ogawa–Nagaoka, Strong Converse to the Quantum Channel Coding Theorem, arXiv:quant-ph/9808063v2, p.4, proof of Lemma 2

import Mathlib
import Definitions.Def_OgawaNagaoka_matPow

namespace OgawaNagaoka

/-- Ogawa–Nagaoka, *Strong Converse to the Quantum Channel Coding Theorem*,
arXiv:quant-ph/9808063v2, p.4 (proof of Lemma 2): for a family of operators `ρ_i` indexed by a
finite alphabet and a distribution `π` on it,
`f(π) = Tr (Σ_{i=1}^a π_i ρ_i^{1/β})^β`.
Applied to the codeword states `ρ_u` (`HolevoCQ.wordState ρ n`) and a distribution `P` on `Xⁿ` it is the
quantity `Tr (Σ_{u∈Xⁿ} P(u) ρ_u^{1/β})^β` of (5), (6) and Lemma 2.

**Formalization Note.** Powers are `matPow` (functional calculus, `0 ^ p = 0` for `p > 0`); the
trace is its real part. The function is defined for every real vector `π` and every `β`; the
statements that use it take `π` in the simplex and `0 < β ≤ 1`. -/
noncomputable def traceGallager {A D : Type} [Fintype A] [Fintype D] [DecidableEq D]
    (ρ : A → Matrix D D ℂ) (β : ℝ) (π : A → ℝ) : ℝ :=
  (matPow (∑ i, ((π i : ℝ) : ℂ) • matPow (ρ i) (1 / β)) β).trace.re

end OgawaNagaoka


