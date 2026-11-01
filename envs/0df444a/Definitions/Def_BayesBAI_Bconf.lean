-- Prove2me | Definitions.Def_BayesBAI_Bconf
-- name    : BayesBAI_Bconf
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T07:52:54.862547+00:00
-- url     : https://prove2.me/theorems/3060c388-6647-4562-9f46-81568e34ad4c
-- title:
--   The confidence width $B_{\mathrm{conf}}(T)$
-- statement:
--   The width of the confidence bounds of Algorithm 1 is
--   $$
--   B_{\mathrm{conf}}(T)=\sqrt{\frac{K\log T}{qT}},
--   $$
--   with the natural logarithm and the unrounded real $qT$.
-- source:
--   Komiyama, Ariu, Kato, Qin, Rate-optimal Bayesian Simple Regret in Best Arm Identification, arXiv:2111.09885v3, §2.1, p.6

import Mathlib

namespace BayesBAI

/-- The confidence width `B_conf(T) = √(K log T / (qT))`, Komiyama, Ariu, Kato, Qin,
arXiv:2111.09885v3, p.6. `log` is natural.

**Formalization Note.** `T` is cast to a real and `qT` is not rounded, as on p.6. At `T = 0` and `T = 1`
Lean gives `0`; Lemma 2 is trivial there and the other items are for large `T`. -/
noncomputable def Bconf (K : ℕ) (q : ℝ) (T : ℕ) : ℝ :=
  Real.sqrt ((K : ℝ) * Real.log T / (q * T))

end BayesBAI


