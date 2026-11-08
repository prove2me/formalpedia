-- Prove2me | Definitions.Def_AvoidPlast_Move
-- name    : AvoidPlast_Move
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:37:00.860014+00:00
-- url     : https://prove2.me/theorems/0483440a-bf7f-4ec4-bfe3-226ece2d6fdb
-- title:
--   Head moves
-- statement:
--   A head on a tape moves one cell left, stays, or moves one cell right. Tapes are one-way infinite to the right, and a left move on cell $0$ stays on cell $0$. This is the basic vocabulary of the machine model of the mission.
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Section 3, machine model, p.13

import Mathlib

namespace AvoidPlast

/-- A head move on a tape: one cell left, stay, or one cell right (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728), §3, p.13, the machine
model). Tapes are one-way infinite to the right; a left move on cell `0` stays on cell `0`. -/
inductive Move
  | left
  | stay
  | right
  deriving DecidableEq, Encodable

end AvoidPlast


