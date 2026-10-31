-- Prove2me | Definitions.Def_UnbiasedTimeAvg_coinProb
-- name    : UnbiasedTimeAvg_coinProb
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:19:25.375193+00:00
-- url     : https://prove2.me/theorems/518de00d-95ff-4e70-a5a3-2cfedc615b0a
-- title:
--   The sampling frequency $q=\bar\nu(\lfloor b'(k)/2\rfloor)/\bar\nu(0)$
-- statement:
--   The paper sets
--   $$q=\frac{\bar\nu(\lfloor b'(k)/2\rfloor)}{\bar\nu(0)}.\qquad(3.10)$$
--   Under A1, $q\in(0,1]$. It is the frequency with which $\hat f_k$ samples the correction $Z'_k$.
--
--   **Formalization Note** $\lfloor b'/2\rfloor$ is natural-number division.
-- source:
--   N. Kahalé, Unbiased time-average estimators for Markov chains, arXiv:2209.09581v1 (20 Sep 2022), (3.10), p.9

import Mathlib
import Definitions.Def_UnbiasedTimeAvg_nuBar

namespace UnbiasedTimeAvg

/-- **The sampling frequency `q`.** Kahalé, arXiv:2209.09581v1, (3.10), p.9:
`q = ν̄(⌊b′(k)/2⌋)/ν̄(0)`.

**Formalization Note.** `⌊b′(k)/2⌋` is the natural-number division `b' / 2`. -/
noncomputable def coinProb (ν : ℕ → ℝ) (b' : ℕ) : ℝ :=
  nuBar ν (b' / 2) / nuBar ν 0

end UnbiasedTimeAvg


