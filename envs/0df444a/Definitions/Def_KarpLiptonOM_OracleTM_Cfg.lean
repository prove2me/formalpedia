-- Prove2me | Definitions.Def_KarpLiptonOM_OracleTM_Cfg
-- name    : KarpLiptonOM_OracleTM_Cfg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:39:26.462989+00:00
-- url     : https://prove2.me/theorems/b1363030-7e7a-48a4-b677-a5faada41b02
-- title:
--   Configuration of an oracle machine
-- statement:
--   A **configuration** of an oracle Turing machine records its current state, the contents of its work tape with the head position, and the contents of its query tape with the head position.
-- source:
--   Hirsch–Volkovich, The Ultimate Karp–Lipton Collapse, STOC 2027 submission (manuscript sha256 aca09a2b…), §A.2.2, p.21 (oracle machines)

import Mathlib
import Definitions.Def_KarpLiptonOM_OracleTM

namespace KarpLiptonOM

/-- A configuration of an oracle machine: its state, its work tape and its query tape
(Hirsch–Volkovich, *The Ultimate Karp–Lipton Collapse*, STOC 2027 submission manuscript (sha256 aca09a2b…7c62fd1b), §A.2.2, p.21). -/
structure OracleTM.Cfg (M : OracleTM) where
  /-- the current state -/
  state : M.Q
  /-- the work tape -/
  work : Tape M.Γ
  /-- the query tape -/
  query : Tape M.Γ

end KarpLiptonOM


