-- Prove2me | Definitions.Def_NSWBetter_Nnwb
-- name    : NSWBetter_Nnwb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:57:38.253487+00:00
-- url     : https://prove2.me/theorems/2c50fd6a-e76c-4593-9d47-dee75f47eef4
-- title:
--   Set $N_{nwb}$ of non-well-behaved agents
-- statement:
--   $N_{nwb}=N\setminus N_{wb}$, the agents for which $x$ is not well-behaved.
-- source:
--   Viswanathan, A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations, arXiv:2607.13340 (held version, sha256 08811cb468c2df39231dca4222c5af94163587c7c83e205e50bbf0b91fc1deb3), Section 5, p.28 (Nnwb)

import Mathlib
import Definitions.Def_NSWBetter_WellBehavedAgent

namespace NSWBetter

open Classical in
/-- **Non-well-behaved agents.**
Viswanathan, *A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations*, arXiv:2607.13340 (held version, sha256 08811cb4…), Section 5, p.28: "Nnwb to denote the set of non-well-behaved agents". -/
noncomputable def Nnwb {n m : ℕ} (v : Fin n → Fin m → ℝ) (x : Fin n → Fin m → ℝ) : Finset (Fin n) :=
  Finset.univ.filter fun i => ¬ WellBehavedAgent v x i

end NSWBetter


