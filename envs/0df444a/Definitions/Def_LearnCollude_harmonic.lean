-- Prove2me | Definitions.Def_LearnCollude_harmonic
-- name    : LearnCollude_harmonic
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T14:02:41.297057+00:00
-- url     : https://prove2.me/theorems/5c2e7e6e-78ff-4416-b504-2bfe0f674d56
-- title:
--   Generalized harmonic number $H_t^r$
-- statement:
--   For a real $r$ and an integer $t\ge 0$, the **generalized harmonic number** is
--   $$
--   H_t^r=\sum_{i=1}^t i^{-r}.
--   $$
--   It controls the sums of the tuning sequences over the time horizon in the regret analysis of the Composite SPSA policy.
-- source:
--   Meylahn–den Boer, Learning to collude in a pricing duopoly, SSRN:3741385 (PDF of 2021-12-06), p. 41

import Mathlib

namespace LearnCollude

/-- The generalized harmonic number `H_t^r = Σ_{i ≤ t} i^{−r}`, Meylahn–den Boer, SSRN:3741385
(PDF of 2021-12-06), p. 41. -/
noncomputable def harmonic (t : ℕ) (r : ℝ) : ℝ := ∑ i ∈ Finset.Icc 1 t, (i : ℝ) ^ (-r)

end LearnCollude


