-- Prove2me | Definitions.Def_KarpLiptonOM_OracleTM_run
-- name    : KarpLiptonOM_OracleTM_run
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:43:07.127327+00:00
-- url     : https://prove2.me/theorems/0d2d175d-2d9c-47ee-ae68-2addeeac7419
-- title:
--   Configuration after $t$ steps
-- statement:
--   The configuration of an oracle machine with oracle $O$ after $t$ steps from a configuration $c$: the step function iterated $t$ times. Halting configurations stay fixed.
-- source:
--   Hirsch–Volkovich, The Ultimate Karp–Lipton Collapse, STOC 2027 submission (manuscript sha256 aca09a2b…), §A.2.2, p.21

import Mathlib
import Definitions.Def_KarpLiptonOM_OracleTM_step

namespace KarpLiptonOM

/-- The configuration reached after `t` steps with oracle `O` (Hirsch–Volkovich, *The Ultimate Karp–Lipton Collapse*, STOC 2027 submission manuscript (sha256 aca09a2b…7c62fd1b), §A.2.2, p.21). -/
noncomputable def OracleTM.run (M : OracleTM) (O : Set (List Bool)) (t : ℕ) (c : M.Cfg) : M.Cfg :=
  (M.step O)^[t] c

end KarpLiptonOM


