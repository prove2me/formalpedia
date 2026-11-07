-- Prove2me | Definitions.Def_NSWBetter_IsRationalScheme
-- name    : NSWBetter_IsRationalScheme
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:51:27.516665+00:00
-- url     : https://prove2.me/theorems/9cddb079-b5ed-4f99-8622-2ae19889a571
-- title:
--   Rationality of a rounding scheme
-- statement:
--   Every matching has rational probability under the rounding scheme $D$ (the Rationality property).
-- source:
--   Viswanathan, A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations, arXiv:2607.13340 (held version, sha256 08811cb468c2df39231dca4222c5af94163587c7c83e205e50bbf0b91fc1deb3), Section 4, p.16 (Rationality)

import Mathlib

namespace NSWBetter

/-- **Rationality.**
Viswanathan, *A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations*, arXiv:2607.13340 (held version, sha256 08811cb4…), Section 4, p.16: "Rationality If the edge weights are rational, the probability of each integral matching is a rational value."; Section 4.1, p.17: "we only work with … rational rounding methods." -/
def IsRationalScheme {n m : ℕ} (D : Finset (Fin n × Fin m × Fin m) → ℝ) : Prop :=
  ∀ M, ∃ q : ℚ, D M = q

end NSWBetter


