-- Prove2me | Definitions.Def_NSWBetter_bundleOf
-- name    : NSWBetter_bundleOf
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:51:28.6493+00:00
-- url     : https://prove2.me/theorems/a5296fa9-195c-4c40-9a2d-38793c5f1e6e
-- title:
--   Bundle $X_i$ of agent $i$ under an integral matching
-- statement:
--   For an integral matching $M$, $X_i(M)$ is the set of goods matched to the buckets of agent $i$.
-- source:
--   Viswanathan, A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations, arXiv:2607.13340 (held version, sha256 08811cb468c2df39231dca4222c5af94163587c7c83e205e50bbf0b91fc1deb3), Section 4, p.16 ("The bundle Xi is the set of goods matched to the buckets of agent i")

import Mathlib

namespace NSWBetter

open Classical in
/-- **The allocation induced by a matching.**
Viswanathan, *A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations*, arXiv:2607.13340 (held version, sha256 08811cb4…), Section 4, p.16: "The allocation for agent i (the bundle Xi) is the set of goods matched to the buckets of agent i". -/
def bundleOf {n m : ℕ} (M : Finset (Fin n × Fin m × Fin m)) (i : Fin n) : Finset (Fin m) :=
  (M.filter fun e => e.1 = i).image fun e => e.2.2

end NSWBetter


