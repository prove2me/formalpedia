-- Prove2me | Definitions.Def_EPRPharma_CanEliminate
-- name    : EPRPharma_CanEliminate
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:20:57.891468+00:00
-- url     : https://prove2.me/theorems/7c38bdf1-fa96-40e0-b651-9c5f6797967f
-- title:
--   Over-prescription can be eliminated under a model
-- statement:
--   Over-prescription can be eliminated under model $P$ if some equilibrium $(y,d)$ of $P$ has a producer decision $d$ that does not induce over-prescription.
--
--   The paper identifies these cases on p. 17: "the cases where over-prescription can be eliminated (i.e., $u_p\ge\bar u_p^{EC}$ and $k\ge\bar k$ under the EC model and $u_p\ge\bar u_p^{SR}$ under the SR model)".
-- source:
--   Alev, Atasu, Toktay, Zhang, Extended Producer Responsibility for Pharmaceuticals, SSRN 2693169 (2020 posting), p. 17

import Mathlib
import Definitions.Def_EPRPharma_IsEquilibrium
import Definitions.Def_EPRPharma_OverPrescribes

namespace EPRPharma

/-- **Over-prescription can be eliminated under model m.**
Alev, Atasu, Toktay, Zhang, *Extended Producer Responsibility for Pharmaceuticals*, SSRN 2693169 (2020 posting), p. 17: "We now study the cases where
over-prescription can be eliminated (i.e., u_p ≥ ū_p^EC and k ≥ k̄ under the EC model and
u_p ≥ ū_p^SR under the SR model)". `CanEliminate P m` says that model m has an equilibrium in
which the producer's decision does not induce over-prescription. -/
def CanEliminate (P : Params) (m : Model) : Prop :=
  ∃ y d, IsEquilibrium P m y d ∧ ¬ OverPrescribes P d

end EPRPharma


