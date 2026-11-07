-- Prove2me | Definitions.Def_VDCyclePack_roundingDenom
-- name    : VDCyclePack_roundingDenom
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T13:06:15.831357+00:00
-- url     : https://prove2.me/theorems/64199bd7-26b7-4983-97a4-0bc9fb6189fe
-- title:
--   The rounding denominator $D=1+16\alpha+16\gamma\log(T+3)$
-- statement:
--   For reals $\alpha,\gamma,T$,
--   $$
--   D=1+16\alpha+16\gamma\log_2(T+3).
--   $$
--   Theorem 4.2 returns at least $\lceil T/D\rceil$ cycles, and Lemma 5.3 shows that every greedy step discards weight at most $D$.
--
--   **Formalization Note** Logarithms are base two (p.9; footnote 1, p.3).
-- source:
--   Kundu–Lochet, Nearly Tight Approximation for Vertex-Disjoint Cycle Packing (STOC 2027 submission manuscript, preprint basis, sha256 95f2e61a…cacb1), Theorem 4.2, p.12, and Section 5, p.14

import Mathlib

namespace VDCyclePack

/-- **The rounding denominator D = 1 + 16α + 16γ log(T + 3).**
Kundu–Lochet, *Nearly Tight Approximation for Vertex-Disjoint Cycle Packing* (STOC 2027
submission manuscript), Theorem 4.2, p.12, and Section 5, p.14: "put D = 1 + 16α + 16γ log(T + 3)".

`roundingDenom α γ T = 1 + 16α + 16γ·log₂(T + 3)`.

**Formalization Note.** Logarithms are base two (p.9: "all logarithms are to base two"; footnote
1, p.3: "Explicit inequalities use ordinary base-two logarithms"). -/
noncomputable def roundingDenom (α γ T : ℝ) : ℝ :=
  1 + 16 * α + 16 * γ * Real.logb 2 (T + 3)

end VDCyclePack


