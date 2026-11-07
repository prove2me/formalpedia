-- Prove2me | Definitions.Def_NSWBetter_Nwb
-- name    : NSWBetter_Nwb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:57:52.966551+00:00
-- url     : https://prove2.me/theorems/769d7d06-c772-4550-906f-03f6a4a05da1
-- title:
--   Set $N_{wb}$ of well-behaved agents
-- statement:
--   $N_{wb}$, the set of agents for which $x$ is well-behaved.
-- source:
--   Viswanathan, A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations, arXiv:2607.13340 (held version, sha256 08811cb468c2df39231dca4222c5af94163587c7c83e205e50bbf0b91fc1deb3), Section 5, p.28 (Nwb)

import Mathlib
import Definitions.Def_NSWBetter_WellBehavedAgent

namespace NSWBetter

open Classical in
/-- **Well-behaved agents.**
Viswanathan, *A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations*, arXiv:2607.13340 (held version, sha256 08811cb4…), Section 5, p.28: "we use Nwb to denote the set of well-behaved agents". -/
noncomputable def Nwb {n m : ℕ} (v : Fin n → Fin m → ℝ) (x : Fin n → Fin m → ℝ) : Finset (Fin n) :=
  Finset.univ.filter fun i => WellBehavedAgent v x i

end NSWBetter


