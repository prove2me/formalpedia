-- Prove2me | Definitions.Def_SkipListConc_phiBench
-- name    : SkipListConc_phiBench
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:50:04.765026+00:00
-- url     : https://prove2.me/theorems/36fa7ab7-b145-4a2c-bbf0-81e1aac03eb9
-- title:
--   Benchmark $\Phi(L)=\sum_x f_x(1+(L-\log_b f_x)_+)$
-- statement:
--   For an operation sequence $\sigma$ and a cutoff $L$, with $b=1/p$,
--   $$
--   \Phi(L)=\sum_x f_x\Bigl(1+\bigl(L-\log_b f_x\bigr)_+\Bigr),
--   $$
--   the sum over the distinct items of $\sigma$. It is the scale of the vertical cost in Lemma 4.7.
-- source:
--   Kapoor–Tanveer, Counter-Free Self-Adjusting Skip Lists: Concentration Bounds, STOC 2027 submission (manuscript sha256 f82c3d35…), Lemma 4.7, p.25

import Mathlib

namespace SkipListConc

/-- The benchmark `Φ(L) = ∑_x f_x (1 + (L − log_b f_x)_+)` of Lemma 4.7 (Kapoor–Tanveer,
*Counter-Free Self-Adjusting Skip Lists: Concentration Bounds*, STOC 2027 submission manuscript
(sha256 f82c3d35…6dab6c), Lemma 4.7, p.25), the sum over the distinct items of `σ`, `b = 1/p`. -/
noncomputable def phiBench {α : Type*} [DecidableEq α] (p : ℝ) (σ : List α) (L : ℕ) : ℝ :=
  ∑ x ∈ σ.toFinset,
    (σ.count x : ℝ) * (1 + max ((L : ℝ) - Real.logb (1 / p) (σ.count x : ℝ)) 0)

end SkipListConc


