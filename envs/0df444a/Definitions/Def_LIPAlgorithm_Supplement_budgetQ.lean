-- Prove2me | Definitions.Def_LIPAlgorithm_Supplement_budgetQ
-- name    : LIPAlgorithm_Supplement_budgetQ
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T18:54:09.15708+00:00
-- url     : https://prove2.me/theorems/645a295d-3852-41b1-8250-eb974cdee79e
-- title:
--   Time and QRAM budgets $(Cn^2\log(n+2))^{n/3}$ of Theorems 8.7 and 8.15
-- statement:
--   The resource bounds of Theorems 8.7 and 8.15. With $\ell$ the encoding length of the input and constants $C, K\in\mathbb N$:
--
--   1. the running-time budget of Theorem 8.15,
--   $$\mathrm{budgetQ}(C,K,n,\ell)=\Big\lceil \big(C\,n^2\log(n+2)\big)^{n/3}\,(\ell+1)^K\Big\rceil;$$
--   2. the running-time budget of Theorem 8.7, with confidence parameter $\kappa$,
--   $$\mathrm{budgetQWR}(C,K,n,\kappa,\ell)=\Big\lceil \big(C\,n^2\log(n+2)\big)^{n/3}\,2^{(\log_2(\kappa+2))^K}\,(\kappa+\ell+1)^K\Big\rceil;$$
--   3. the QRAM size bound of both theorems, $\mathrm{qramBound}(C,n)=\lceil (C\,n^2\log(n+2))^{n/3}\rceil$ cells.
--
--   They read the paper's $O(n^2\log n)^{n/3}$ as $(C n^2\log n)^{n/3}$ with a universal constant $C$ (footnote 2), $2^{\mathrm{polylog}(\kappa)}$ as $2^{(\log_2(\kappa+2))^K}$, and the suppressed polynomial factors in the encoding length (Remark 2.2) as $(\ell+1)^K$.
--
--   **Formalization Note** The exponent $n/3$ is a real exponent. $\log(n+2)$ replaces $\log n$, which is $0$ at $n=1$; for $n\ge2$, $\log(n+2)\le 2\log n$, so the class of bounds is unchanged up to $C$. The QRAM bound carries no polynomial factor.
-- source:
--   Aggarwal, Jiang, Li, Liu, An n^{n+o(n)}-Time Algorithm for the Lattice Isomorphism Problem, STOC 2027 submission (manuscript sha256 61ee52aa…), Theorem 8.7, p.45 (PDF p.48); Theorem 8.15, p.49 (PDF p.52); footnote 2, p.2 (PDF p.5); Remark 2.2, p.10 (PDF p.13)

import Mathlib

namespace LIPAlgorithm

namespace Supplement

/-- The running-time budget of Theorem 8.15: `O(n² log n)^{n/3}` up to a polynomial in the encoding
length `ℓ`, read as `⌈(C·n²·log(n+2))^{n/3}·(ℓ+1)^K⌉`.
Aggarwal, Jiang, Li, Liu, *An n^{n+o(n)}-Time Algorithm for the Lattice Isomorphism Problem*, STOC 2027
submission (manuscript sha256 61ee52aa…), Theorem 8.15, p.49 (PDF p.52); footnote 2, p.2 (PDF p.5:
"O(f(n))n stands for (Cf(n))n, where C > 0 is a universal constant"); Remark 2.2, p.10 (PDF p.13).

**Formalization Note.** The exponent `n/3` is a real exponent (`Real.rpow`), not `ℕ` division.
`log(n+2)` replaces `log n` (which is `0` at `n = 1`), as in the published `budget`; for `n ≥ 2`,
`log(n+2) ≤ 2 log n`, so the class of bounds is the same up to `C`. -/
noncomputable def budgetQ (C K n ℓ : ℕ) : ℕ :=
  ⌈((C : ℝ) * (n : ℝ) ^ 2 * Real.log ((n : ℝ) + 2)) ^ ((n : ℝ) / 3) * ((ℓ : ℝ) + 1) ^ K⌉₊

/-- The running-time budget of Theorem 8.7, p.45 (PDF p.48): `O(n² log n)^{n/3}·2^{polylog(κ)}`, up
to a polynomial in the encoding length `ℓ` (Remark 2.2), read as
`⌈(C·n²·log(n+2))^{n/3} · 2^{(log₂(κ+2))^K} · (κ+ℓ+1)^K⌉`.

**Formalization Note.** As in the published `budgetWR`: `κ + 2` keeps the logarithm positive at
`κ = 0, 1`, and one exponent `K` serves the polylogarithm and the polynomial (the constants are
existential). The factor `(κ+ℓ+1)^K` contains the paper's `poly(bits)`; a `poly(κ)` factor is
`≤ 2^{polylog κ}` and adds nothing. -/
noncomputable def budgetQWR (C K n κ ℓ : ℕ) : ℕ :=
  ⌈((C : ℝ) * (n : ℝ) ^ 2 * Real.log ((n : ℝ) + 2)) ^ ((n : ℝ) / 3) *
      (2 : ℝ) ^ (Real.logb 2 ((κ : ℝ) + 2) ^ K) * ((κ : ℝ) + (ℓ : ℝ) + 1) ^ K⌉₊

/-- The QRAM size bound of Theorems 8.7 and 8.15: `O(n² log n)^{n/3}` cells, read as
`⌈(C·n²·log(n+2))^{n/3}⌉`.

**Formalization Note.** No polynomial factor: Remark 2.2 suppresses polynomial factors in running
times only, and Theorem 8.7 states the QRAM size without one. Theorem 8.15's "up to polynomial factors
in the input encoding length" is read as qualifying the running time only (see the theorem). -/
noncomputable def qramBound (C n : ℕ) : ℕ :=
  ⌈((C : ℝ) * (n : ℝ) ^ 2 * Real.log ((n : ℝ) + 2)) ^ ((n : ℝ) / 3)⌉₊

end Supplement

end LIPAlgorithm


