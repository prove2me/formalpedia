-- Prove2me | Definitions.Def_OmniMix_bern
-- name    : OmniMix_bern
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:38:20.674655+00:00
-- url     : https://prove2.me/theorems/386f9bdb-1f94-4afd-8462-826699b02a64
-- title:
--   Bernoulli expectation $\mathbb E_{Y\sim\mathrm{Ber}(p)}[g(Y)]$
-- statement:
--   For $p\in[0,1]$ and $g:\{0,1\}\to\mathbb R\cup\{+\infty\}$,
--   $$
--   \mathbb E_{Y\sim\mathrm{Ber}(p)}[g(Y)]=(1-p)\,g(0)+p\,g(1).
--   $$
--   It is the expected value of $g$ when the outcome is $1$ with probability $p$.
--
--   **Formalization Note** Computed in the extended reals with $0\cdot(+\infty)=0$ and $c\cdot(+\infty)=+\infty$ for $c>0$, so an infinite value counts only when its outcome has positive probability.
-- source:
--   Liu–Luo–Ratliff, Omniprediction for All Mixable Proper Losses and Beyond, arXiv:2610.41023, §1, p.1 and §2, p.8

import Mathlib

namespace OmniMix

/-- **Bernoulli expectation `E_{Y∼Ber(p)}[g(Y)]`.** Liu–Luo–Ratliff, *Omniprediction for All Mixable Proper Losses and Beyond*, arXiv:2610.41023, §1, p.1 (properness) and §2, p.8.

`bern p g = (1 − p)·g(0) + p·g(1)` for `g : {0,1} → ℝ ∪ {+∞}`.

**Formalization Note.** Computed in `EReal`, where `0 · (+∞) = 0` and `c · (+∞) = +∞` for `c > 0`,
so a `+∞` value counts only when the outcome has positive probability, as in the paper. The
outcome `true` is `1`. -/
noncomputable def bern (p : unitInterval) (g : Bool → EReal) : EReal :=
  ((1 - (p : ℝ) : ℝ) : EReal) * g false + ((p : ℝ) : EReal) * g true

end OmniMix


