-- Prove2me | Definitions.Def_KarpLiptonOM_OracleTM_HaltsWithin
-- name    : KarpLiptonOM_OracleTM_HaltsWithin
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:44:05.990226+00:00
-- url     : https://prove2.me/theorems/2921ec95-8dc5-47ba-a4be-0721772f4655
-- title:
--   Halting within $t$ steps
-- statement:
--   An oracle machine with oracle $O$ **halts within $t$ steps** on input $w$ if after $t$ steps from the initial configuration on $w$ it is in the accepting or the rejecting state.
-- source:
--   Hirsch–Volkovich, The Ultimate Karp–Lipton Collapse, STOC 2027 submission (manuscript sha256 aca09a2b…), §A.2.1, p.20

import Mathlib
import Definitions.Def_KarpLiptonOM_OracleTM_run
import Definitions.Def_KarpLiptonOM_OracleTM_init

namespace KarpLiptonOM

/-- The machine with oracle `O` halts on input `w` within `t` steps (Hirsch–Volkovich, *The Ultimate Karp–Lipton Collapse*, STOC 2027 submission manuscript (sha256 aca09a2b…7c62fd1b), §A.2.1, p.20). -/
def OracleTM.HaltsWithin (M : OracleTM) (O : Set (List Bool)) (t : ℕ) (w : List (Option Bool)) :
    Prop :=
  (M.run O t (M.init w)).state = M.qaccept ∨ (M.run O t (M.init w)).state = M.qreject

end KarpLiptonOM


