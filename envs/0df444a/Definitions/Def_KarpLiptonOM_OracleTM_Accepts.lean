-- Prove2me | Definitions.Def_KarpLiptonOM_OracleTM_Accepts
-- name    : KarpLiptonOM_OracleTM_Accepts
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:44:19.820202+00:00
-- url     : https://prove2.me/theorems/0523e1ca-adf2-4313-97e5-681ed2b37a11
-- title:
--   Acceptance with oracle $O$
-- statement:
--   An oracle machine with oracle $O$ **accepts** $w$ if its computation on $w$ reaches the accepting state. For a polynomial-time machine this is decided within the time bound, so $M^O$ decides the language $\{w : M^O \text{ accepts } w\}$.
-- source:
--   Hirsch–Volkovich, The Ultimate Karp–Lipton Collapse, STOC 2027 submission (manuscript sha256 aca09a2b…), §A.2.2, p.21 (Definition A.2.1)

import Mathlib
import Definitions.Def_KarpLiptonOM_OracleTM_run
import Definitions.Def_KarpLiptonOM_OracleTM_init

namespace KarpLiptonOM

/-- The machine with oracle `O` accepts input `w`: some run reaches `qaccept` (Hirsch–Volkovich, *The Ultimate Karp–Lipton Collapse*, STOC 2027 submission manuscript (sha256 aca09a2b…7c62fd1b), §A.2.2, p.21). -/
def OracleTM.Accepts (M : OracleTM) (O : Set (List Bool)) (w : List (Option Bool)) : Prop :=
  ∃ t, (M.run O t (M.init w)).state = M.qaccept

end KarpLiptonOM


