-- Prove2me | Definitions.Def_AvgPHETH_acceptsAt
-- name    : AvgPHETH_acceptsAt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:27:02.138632+00:00
-- url     : https://prove2.me/theorems/7f091e60-1104-4260-87d9-e74ddfc1324b
-- title:
--   $M^O$ is in its accepting state after $t$ steps
-- statement:
--   The machine $M$ with oracle $O$ on input $w$ is in its accepting state after $t$ steps. Since a halted configuration does not change, for a machine that has halted within $t$ steps this says that $M^O$ accepts $w$.
-- source:
--   Hirahara–Juvekar–Nanashima, Average-Case Hardness of PH from ETH-Type Hypotheses, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), §4.2, p.15 (PDF 17)

import Mathlib
import Definitions.Def_KarpLiptonOM_OracleTM_run
import Definitions.Def_KarpLiptonOM_OracleTM_init
open KarpLiptonOM

namespace AvgPHETH

/-- The machine `M` with oracle `O` is in its accepting state after `t` steps on input `w`
(Hirahara–Juvekar–Nanashima, *Average-Case Hardness of PH from ETH-Type Hypotheses*, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), §4.2, p.15 (PDF 17): "accepts within `T` steps"). -/
def acceptsAt (M : OracleTM) (O : Set (List Bool)) (t : ℕ) (w : List (Option Bool)) : Prop :=
  (M.run O t (M.init w)).state = M.qaccept

end AvgPHETH


