-- Prove2me | Definitions.Def_BayesBAI_tPrime
-- name    : BayesBAI_tPrime
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T07:52:54.725803+00:00
-- url     : https://prove2.me/theorems/cc1c056a-fa63-4bec-aab9-acce25a2b2ae
-- title:
--   The effective horizon $T'$
-- statement:
--   $T'=2qT/K+(1-q)T$, a real number.
-- source:
--   Komiyama, Ariu, Kato, Qin, Rate-optimal Bayesian Simple Regret in Best Arm Identification, arXiv:2111.09885v3, Theorem 1, p.7

import Mathlib

namespace BayesBAI

/-- `T′ := 2qT/K + (1 - q)T`, a real number, Komiyama, Ariu, Kato, Qin, arXiv:2111.09885v3, p.7. -/
noncomputable def tPrime (K : ℕ) (q : ℝ) (T : ℕ) : ℝ :=
  2 * q * T / K + (1 - q) * T

end BayesBAI


