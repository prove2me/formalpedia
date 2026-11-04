-- Prove2me | Definitions.Def_Submission_Weighted_Global_TernaryArenaSourceLayout
-- name    : Submission_Weighted_Global_TernaryArenaSourceLayout
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T13:32:55.604736+00:00
-- url     : https://prove2.me/theorems/3925c141-22e8-4376-bba6-3d05438eaeab
-- title:
--   Ternary Arena Source Layout
-- statement:
--   Definitions and structural lemmas for Ternary Arena Source Layout, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/Weighted/Global/TernaryArenaSourceLayout.lean

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaLayout
import Definitions.Def_Submission_ThreeSum_TernarySourceExecutionFactory
set_option autoImplicit false
namespace ThreeSum.WeightedGlobalArenaSourceLayout
open WeightedGlobalArenaLayout TernarySourceExecutionFactory LightTernarySourceHost
def setup (S : Setup) (free C start : ℕ) : Setup :=
  { S with
    base0 := addr free C start
    dst0 := addr free C (start+1)
    base1 := addr free C (start+2)
    dst1 := addr free C (start+3)
    base2 := addr free C (start+4)
    dst2 := addr free C (start+5)
    free := addr free C (start+6)
    keyBase := addr free C (start+7)
    valueBase := addr free C (start+8) }
structure Geometry (S : Setup) (space : ℕ) : Prop where
  base0 : S.base0+S.xs.length≤S.dst0
  next0 : LightRadixKeys.space S.dst0 S.xs.length S.J≤S.base1
  base1 : S.base1+S.xs.length≤S.dst1
  next1 : LightRadixKeys.space S.dst1 S.xs.length S.J≤S.base2
  base2 : S.base2+S.xs.length≤S.dst2
  initEnd : LightRadixKeys.space S.dst2 S.xs.length S.J≤S.free
  keyBase : LightWantedSetup.space S.free S.M S.input (dictionary S.xs S.p0 S.J)
    S.NL (size S.xs S.J) S.U 0 0≤S.keyBase
  keyEnd : S.keyBase+count S.xs S.p0 S.J S.M S.NL S.input≤S.valueBase
  values : S.valueBase+S.groups*S.bank≤space
end ThreeSum.WeightedGlobalArenaSourceLayout


