-- Prove2me | Definitions.Def_ReserveLB_lawExpect
-- name    : ReserveLB_lawExpect
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:28:54.335071+00:00
-- url     : https://prove2.me/theorems/8994852d-e41e-4b5d-aacc-df6df3d19b58
-- title:
--   Expectation $\mathbb E\,g(X)$ under a listed finite law
-- statement:
--   For a listed finite law $\mu = ((a_\ell, p_\ell))_\ell$ of a random size $X$ and a function $g:\mathbb R\to\mathbb R$,
--   $$
--   \mathbb E\,g(X) = \sum_{\ell} p_\ell\, g(a_\ell).
--   $$
--
--   This is the exact expectation used for the coefficients $\mu_{jqh}$, $c_{jq}$ and the effective sizes in the system (4).
-- source:
--   Mahboub–Rahgoshay, Stochastic Load Balancing with Strict Machine-Reservation Budgets, manuscript of Oct. 30, 2026 (sha256 aefe1158e8000194527b025b3c358dcb571c94e1038c0bfdd295c6119bc9f630), Section 3, p.5 (the expectations in the coefficients of (4))

import Mathlib

namespace ReserveLB

/-- **Expectation under a listed finite law.**
Mahboub–Rahgoshay, *Stochastic Load Balancing with Strict Machine-Reservation Budgets*,
manuscript of Oct. 30, 2026 (sha256 aefe1158…), Section 3, p.5: the expectations `E Y_jqh`, `E E_jq` and the moments in `β_b` of
one original's size.

`lawExpect μ g = Σ_(a, p) ∈ μ p · g(a)`: the expectation of `g(X)` when `X` has the listed law `μ`.

**Formalization Note.** The values and probabilities are cast from `ℚ` to `ℝ`; repeated atoms are
summed separately, which is the same expectation. -/
noncomputable def lawExpect (μ : List (ℚ × ℚ)) (g : ℝ → ℝ) : ℝ :=
  (μ.map fun a => ((a.2 : ℚ) : ℝ) * g ((a.1 : ℚ) : ℝ)).sum

end ReserveLB


