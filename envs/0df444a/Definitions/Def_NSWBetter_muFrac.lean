-- Prove2me | Definitions.Def_NSWBetter_muFrac
-- name    : NSWBetter_muFrac
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:54:15.329194+00:00
-- url     : https://prove2.me/theorems/72c6d334-fb26-4dc0-9649-cf405d057ace
-- title:
--   Mean value $\mu_i$ of a fractional bundle (Definition 4.8)
-- statement:
--   $\mu_i=\sum_{g\in G\setminus L_i}x_{ig}v_i(g)$, the value of the small part of agent $i$'s fractional bundle (no division).
-- source:
--   Viswanathan, A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations, arXiv:2607.13340 (held version, sha256 08811cb468c2df39231dca4222c5af94163587c7c83e205e50bbf0b91fc1deb3), Definition 4.8, p.20

import Mathlib
import Definitions.Def_NSWBetter_largeSet

namespace NSWBetter

/-- **Mean value µ_i (Definition 4.8).**
Viswanathan, *A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations*, arXiv:2607.13340 (held version, sha256 08811cb4…), Definition 4.8, p.20: "the mean value of the agent i, denoted µi, is defined as the value Σ_(g∈G\Li) xig vi(g)." -/
noncomputable def muFrac {n m : ℕ} (v : Fin n → Fin m → ℝ) (x : Fin n → Fin m → ℝ) (i : Fin n) : ℝ :=
  ∑ g ∈ Finset.univ \ largeSet v x i, x i g * v i g

end NSWBetter


