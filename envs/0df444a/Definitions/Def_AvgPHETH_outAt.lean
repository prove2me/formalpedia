-- Prove2me | Definitions.Def_AvgPHETH_outAt
-- name    : AvgPHETH_outAt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:25:23.635602+00:00
-- url     : https://prove2.me/theorems/cfd966f5-0f77-4c71-87d7-d9b1a5125a09
-- title:
--   Tape contents $M^O(w)$ after $t$ steps
-- statement:
--   For an oracle machine $M$, an oracle $O$, a step count $t$ and an input $w$, this is the binary string on the work tape of $M^O$ after $t$ steps, read from the head rightwards up to the first non-bit symbol.
--
--   It is the output of $M^O(w)$ when $M^O$ has halted within $t$ steps; every use is paired with the halting condition.
-- source:
--   Hirahara–Juvekar–Nanashima, Average-Case Hardness of PH from ETH-Type Hypotheses, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), §4.5, p.17 (PDF 19)

import Mathlib
import Definitions.Def_KarpLiptonOM_OracleTM_run
import Definitions.Def_KarpLiptonOM_OracleTM_init
import Definitions.Def_KarpLiptonOM_Tape_bits
open KarpLiptonOM

namespace AvgPHETH

/-- The string `M^O(w)` written on the work tape after `t` steps, read from the head (`Tape.bits`)
(Hirahara–Juvekar–Nanashima, *Average-Case Hardness of PH from ETH-Type Hypotheses*, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), §4.5, p.17 (PDF 19): "`U^O(d, y)` outputs `z` within `t` steps"; §4.1, p.14 (PDF 16)).

**Formalization Note** The string after `t` steps is an output only if the machine has halted by
then; every statement pairs `outAt` with `OracleTM.HaltsWithin`. -/
noncomputable def outAt (M : OracleTM) (O : Set (List Bool)) (t : ℕ) (w : List (Option Bool)) :
    List Bool :=
  (M.run O t (M.init w)).work.bits M.ι

end AvgPHETH


