-- Prove2me | Definitions.Def_WiretapFeedback_tvDist
-- name    : WiretapFeedback_tvDist
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:23:50.679771+00:00
-- url     : https://prove2.me/theorems/96610aca-a2be-4cd0-aa43-f1b1d2d92e3d
-- title:
--   Variation distance $\|P-Q\|_1=\frac12\sum_x|P(x)-Q(x)|$
-- statement:
--   For two probability mass functions $P,Q$ on the same (countable-support) alphabet, the **variation distance** is
--   $$
--   \|P-Q\|_1=\frac12\sum_x |P(x)-Q(x)|.
--   $$
--
--   It measures the secrecy of a wiretap code (the distance between the joint law of the message and the eavesdropper's view and the product of their marginals) and appears in the hypothesis of Theorem 5.
--
--   **Formalization Note** The sum is an $[0,\infty]$-valued sum, with $|P(x)-Q(x)|$ written as $(P(x)\mathbin{\dot-}Q(x))+(Q(x)\mathbin{\dot-}P(x))$ using truncated subtraction, so no summability side condition is needed and the alphabet may be any type. The factor $\tfrac12$ is the paper's.
-- source:
--   Hayashi–Tyagi–Watanabe, Strong Converse for a Degraded Wiretap Channel via Active Hypothesis Testing, arXiv:1410.0443v1, §II, p.2 (definition of ‖P − Q‖₁)

import Mathlib

open scoped ENNReal

namespace WiretapFeedback

/-- The variation distance `‖P − Q‖₁ = ½ Σ_x |P(x) − Q(x)|` of two probability mass functions on
the same alphabet, Hayashi–Tyagi–Watanabe, arXiv:1410.0443v1, §II, p. 2 (display after the
definition of an `(N, n, ϵ, δ)` wiretap code).

**Formalization Note** The sum is taken in `ℝ≥0∞`, where `|P(x) − Q(x)|` is written as
`(P x − Q x) + (Q x − P x)` with truncated subtraction (one of the two summands is `0`). An
`ℝ≥0∞`-valued `tsum` needs no summability side condition, so the alphabet can be any type
(the paper applies the distance to laws of `(M, Zⁿ, 𝐅)` with an arbitrary feedback alphabet).
The factor `½` is the paper's. -/
noncomputable def tvDist {α : Type} (P Q : PMF α) : ℝ≥0∞ :=
  2⁻¹ * ∑' a, ((P a - Q a) + (Q a - P a))

end WiretapFeedback


