-- Prove2me | Definitions.Def_QVolTransducer_coolSched
-- name    : QVolTransducer_coolSched
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:22:47.985356+00:00
-- url     : https://prove2.me/theorems/f2655baa-d7d6-4156-b395-09080d50b4fa
-- title:
--   Inverse cooling schedule $\beta_{j+1}=\beta_j(1-\max\{1/(8\sqrt d),1/(8R\sqrt{\beta_j})\})$
-- statement:
--   Let $d\in\mathbb N$, $R\ge1$ and $\beta_0$ be given. The **inverse cooling schedule** is defined recursively by
--
--   $$
--   \beta_{j+1}=\begin{cases}\beta_j\Bigl(1-\max\Bigl\{\dfrac1{8\sqrt d},\dfrac1{8R\sqrt{\beta_j}}\Bigr\}\Bigr), & \beta_j>\dfrac1{(2R)^2},\\[2mm] 0, & \text{otherwise}.\end{cases}
--   $$
--
--   The volume algorithm estimates the ratios $Z(\beta_{j+1})/Z(\beta_j)$ along this schedule until $\beta_\ell=0$, where $Z(0)=\mathrm{Vol}(K)$; its length controls the number of stages.
-- source:
--   Cornelissen, Apers, Gribling, Improved quantum volume estimation with transducers and amortized quantum walks, arXiv:2609.40217 (version of November 3, 2026, sha256 40d7b52d…), Lemma 9.18, p.64; Algorithm 2 step 4(a), p.71 (PDF pp.66, 73)

import Mathlib

namespace QVolTransducer

/-- The inverse cooling schedule of Lemma 9.18 (Cornelissen, Apers, Gribling, *Improved quantum
volume estimation with transducers and amortized quantum walks*, arXiv:2609.40217 (version of
November 3, 2026, sha256 40d7b52d…), Lemma 9.18, p.64, and Algorithm 2 step 4(a), p.71):
`β_0` is given and
`β_{j+1} = β_j · (1 − max{1/(8√d), 1/(8R√β_j)})` if `β_j > 1/(2R)²`, and `β_{j+1} = 0` otherwise. -/
noncomputable def coolSched (d : ℕ) (R β₀ : ℝ) : ℕ → ℝ
  | 0 => β₀
  | j + 1 =>
    if 1 / (2 * R) ^ 2 < coolSched d R β₀ j then
      coolSched d R β₀ j *
        (1 - max (1 / (8 * Real.sqrt d)) (1 / (8 * R * Real.sqrt (coolSched d R β₀ j))))
    else 0

end QVolTransducer


