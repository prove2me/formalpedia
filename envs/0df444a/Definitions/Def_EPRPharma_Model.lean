-- Prove2me | Definitions.Def_EPRPharma_Model
-- name    : EPRPharma_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:04:26.47952+00:00
-- url     : https://prove2.me/theorems/5276d87b-d87c-4fcf-9c07-dc1674f80c36
-- title:
--   The EPR implementation models EC and SR
-- statement:
--   There are two EPR implementation models.
--
--   1. **End-of-pipe Control (EC):** the planner mandates a collection rate $r_{EC}$, and the producer collects that fraction of the unused medicine at unit cost $k$.
--   2. **Source Reduction (SR):** the planner charges the producer a unit fee $t$ on every unit dispensed and runs the collection itself at rate $r_{SR}$.
--
--   The social planner chooses one of them.
-- source:
--   Alev, Atasu, Toktay, Zhang, Extended Producer Responsibility for Pharmaceuticals, SSRN 2693169 (2020 posting), §3.3, p. 12 (unnumbered)

import Mathlib

namespace EPRPharma

/-- **The two EPR implementation models.**
Alev, Atasu, Toktay, Zhang, *Extended Producer Responsibility for Pharmaceuticals*, SSRN 2693169 (2020 posting), §3.3, p. 12 (unnumbered): the
End-of-pipe Control model `EC`, in which the producer must collect a fraction r_EC of the unused
medicine at unit collection cost k, and the Source Reduction model `SR`, in which the producer pays a
unit fee t for every unit dispensed and the social planner collects at rate r_SR. -/
inductive Model
  /-- End-of-pipe Control. -/
  | EC
  /-- Source Reduction. -/
  | SR
  deriving DecidableEq

end EPRPharma


