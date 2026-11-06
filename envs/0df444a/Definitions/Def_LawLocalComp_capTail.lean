-- Prove2me | Definitions.Def_LawLocalComp_capTail
-- name    : LawLocalComp_capTail
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:11:32.399209+00:00
-- url     : https://prove2.me/theorems/ed2cf186-ccdd-462e-9226-85bc7c31a123
-- title:
--   Capped-tail envelope $H_Y(k)$
-- statement:
--   For a law $Y$ and real $k\ge0$,
--   $$H_Y(k)=\int_0^\infty\min\{1,k\,\mathbb P(Y\ge t)\}\,dt .$$
--
--   **Formalization Note** The integrand is a bounded step function vanishing beyond the largest atom, so the Lebesgue integral over $(0,\infty)$ is finite.
-- source:
--   Mahboub–Rahgoshay, Optimal Law-Local Compression for Stochastic Loads, STOC 2027 submission (manuscript of Oct. 29, 2026, sha256 5f71501c…aa873), Lemma 2.2, p.4

import Mathlib
import Definitions.Def_LawLocalComp_Law

namespace LawLocalComp

/-- **The capped-tail envelope `H_Y(k)`.**
Mahboub–Rahgoshay, *Optimal Law-Local Compression for Stochastic Loads*, STOC 2027
submission manuscript of Oct. 29, 2026 (sha256 5f71501c…aa873), Lemma 2.2, p.4: `HY(k) = ∫_0^∞ min{1, kP(Y ≥ t)} dt`, for real `k ≥ 0`.

**Formalization Note.** The integrand is a bounded step function vanishing beyond the largest atom,
so the Lebesgue integral over `(0, ∞)` is a genuine (integrable) integral. -/
noncomputable def capTail (Y : Law) (k : ℝ) : ℝ :=
  ∫ t in Set.Ioi (0 : ℝ), min 1 (k * ∑ y ∈ Y.w.support with t ≤ y, Y.w y)

end LawLocalComp


