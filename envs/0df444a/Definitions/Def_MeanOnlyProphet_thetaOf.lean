-- Prove2me | Definitions.Def_MeanOnlyProphet_thetaOf
-- name    : MeanOnlyProphet_thetaOf
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:21:55.772214+00:00
-- url     : https://prove2.me/theorems/2d330259-5933-48b0-8a72-21b2d21dc8c1
-- title:
--   Threshold $\theta(t)=\int_t^1 b$ from a drop rate, and the step drop rate
-- statement:
--   For a **drop rate** $b$ on $[0,1]$ the threshold is
--   $$
--   \theta(t)=\int_t^1 b(s)\,ds ,
--   $$
--   so $\theta(1)=0$, $\theta(0)=\int_0^1 b$ and $b=-\theta'$ almost everywhere. A nondecreasing $b$ makes $\theta$ concave.
--
--   The **step drop rate** with slopes $b_1,\dots,b_N$ takes the value $b_i$ on the $i$-th of the $N$ equal intervals $[(i-1)/N,i/N)$ of $[0,1]$; its threshold is piecewise linear.
--
--   **Formalization Note** Slopes are `bs : Fin N → ℝ`, 0-based (`bs 0` is $b_1$). The step function is `bs ⌊N t⌋` with the index capped at $N-1$, so its value at $t=1$ is $b_N$; values outside $[0,1)$ do not affect any integral over $[0,1]$.
-- source:
--   Feng, Jin, Wu, Xiang, Mean-only Prophet Inequalities, arXiv:2610.24711 (held version, sha256 c68bfec4…74e93a), §2, pp.5–6 (PDF pp.6–7); §3.3, p.10 (PDF p.11)

import Mathlib

namespace MeanOnlyProphet

/-- **Threshold from a drop rate, `θ(t) = ∫_t^1 b(s) ds`.** Feng, Jin, Wu, Xiang, *Mean-only Prophet
Inequalities*, arXiv:2610.24711 (held version, sha256 c68bfec4…), §2, pp.5–6 (PDF pp.6–7): "For the
absolutely continuous thresholds used by our algorithms, write b(t) = −θ′(t) ≥ 0 (almost everywhere),
θ(0) = ∫_0^1 b(t) dt ≤ 1, θ(t) = ∫_t^1 b(s) ds."

**Formalization Note.** An interval integral; it is the paper's `θ` whenever `b` is integrable on
`[0,1]`. -/
noncomputable def thetaOf (b : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ s in t..1, b s

/-- **Step drop rate on `N` equal intervals.** Feng, Jin, Wu, Xiang, *Mean-only Prophet Inequalities*,
arXiv:2610.24711 (held version), §3.3, p.10 (PDF p.11): "a piecewise linear threshold with N
equal-length intervals and positive nondecreasing drop rates b1 , . . . , bN".

`stepRate bs t = bs_{⌊N t⌋}` for `t ∈ [0,1)`.

**Formalization Note.** `bs : Fin N → ℝ` is 0-based (`bs 0` is the paper's `b_1`, `bs (N-1)` its `b_N`).
The index `⌊N t⌋₊` is capped at `N − 1`, so `stepRate bs 1 = bs (N-1)` and `stepRate bs t = bs 0` for
`t < 0`; values outside `[0,1)` change no integral over `[0,1]`. -/
noncomputable def stepRate {N : ℕ} [NeZero N] (bs : Fin N → ℝ) (t : ℝ) : ℝ :=
  bs ⟨min ⌊(N : ℝ) * t⌋₊ (N - 1),
    lt_of_le_of_lt (min_le_right _ _) (Nat.sub_lt (NeZero.pos N) Nat.one_pos)⟩

end MeanOnlyProphet


