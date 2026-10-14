-- Prove2me | Definitions.Def_DROReview_PhiDiv_generators
-- name    : DROReview_PhiDiv_generators
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-13T21:16:20.431544+00:00
-- url     : https://prove2.me/theorems/5ede8619-acb4-4da9-9bb5-be3c4db0d2f8
-- title:
--   Table 1 — variation, Hellinger, KL, and J-divergence generators
-- statement:
--   Table 1 supplies four **divergence generators** for $t\ge0$:
--
--   $$
--   \phi_v(t)=|t-1|,\quad
--   \phi_h(t)=(\sqrt t-1)^2,\quad
--   \phi_{\mathrm{kl}}(t)=t\log t-t+1,\quad
--   \phi_j(t)=(t-1)\log t.
--   $$
--
--   The corresponding divergences are $\mathfrak D^{\phi_v}$, $\mathfrak D^{\phi_h}$, $\mathfrak D^{\phi_{\mathrm{kl}}}$, and $\mathfrak D^{\phi_j}$. In particular, the variation and Hellinger divergences have no extra factor of one half. These are the four quantities compared in the corrected Lemma 5.4.
--
--   **Formalization Note** Set $\phi_j(0)=+\infty$ by its limit as $t\downarrow0$; using Lean's value $\log0=0$ would give the wrong generator. The KL generator has $\phi_{\mathrm{kl}}(0)=1$ under $0\log0=0$. Their recession slopes are respectively $1$, $1$, $+\infty$, and $+\infty$.
-- source:
--   Rahimian, Mehrotra, Distributionally Robust Optimization: A Review, arXiv:1908.05659v1 (2019), p. 31, Table 1, Kullback-Leibler, J-divergence, Hellinger distance, and Variation distance rows

import Mathlib

namespace DROReview.PhiDiv

/-- Table 1, p. 31: variation divergence generator, without a factor of 1/2. -/
noncomputable def phiV (t : NNReal) : ENNReal :=
  ENNReal.ofReal |(t : ℝ) - 1|

/-- Table 1, p. 31: Hellinger divergence generator, without a factor of 1/2. -/
noncomputable def phiH (t : NNReal) : ENNReal :=
  ENNReal.ofReal ((Real.sqrt (t : ℝ) - 1) ^ 2)

/-- Table 1, p. 31: Kullback–Leibler divergence generator. At zero,
`0 log 0 = 0`, and the generator has value one. -/
noncomputable def phiKL (t : NNReal) : ENNReal :=
  ENNReal.ofReal ((t : ℝ) * Real.log (t : ℝ) - (t : ℝ) + 1)

/-- Table 1, p. 31: J-divergence generator. Its value at zero is +∞,
the lower-semicontinuous limit, rather than Lean's `Real.log 0 = 0`. -/
noncomputable def phiJ (t : NNReal) : ENNReal :=
  if t = 0 then ⊤ else
    ENNReal.ofReal (((t : ℝ) - 1) * Real.log (t : ℝ))

end DROReview.PhiDiv


