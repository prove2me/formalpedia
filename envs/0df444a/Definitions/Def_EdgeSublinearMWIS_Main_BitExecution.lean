-- Prove2me | Definitions.Def_EdgeSublinearMWIS_Main_BitExecution
-- name    : EdgeSublinearMWIS_Main_BitExecution
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T13:41:02.235208+00:00
-- url     : https://prove2.me/theorems/3ff85cea-602f-403a-b7ad-a8d872ed5b08
-- title:
--   Actual halting time on a sequential bit Turing machine
-- statement:
--   The published finite transition-table machine has a read-only input tape, one binary work tape and an append-only output. Each transition inspects only scanned symbols and origin flags, moves each head at most one cell, and emits at most one bit. The extra catalyst tape is always initialized to the empty word; it supplies no advice or oracle.
--
--   $$T_M(x)=\min\{s:M\text{ reaches a halting state on }x\text{ at step }s\}.$$
--   The predicate requires the stated output at this first halting step. It contains no assigned clock. A supporting theorem must establish polynomial simulation of the finite multi-stack model in this sequential bit model before its bounds can support the goal.
-- source:
--   Édouard Bonnet, Yeonsu Chang, STOC 2027 submission #1044 (October 2026), Theorem 2 explanatory paragraph; §5.3 computational-model convention, p.2 (PDF p.2), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1044.pdf

import Definitions.Def_EdgeSublinearMWIS_Main_Encoding
import Definitions.Def_CatalyticMatching_General_Machine

namespace EdgeSublinearMWIS.Main

/-- Sequential bit-level Turing execution with no catalyst, oracle, advice or randomness.
The read-only input, one work tape and append-only output have ordinary local head moves. -/
def BitHalts (M : CatalyticMatching.General.Machine) (input output : List Bool) (s : ℕ) : Prop :=
  ∃ c, M.run input [] s = some c ∧ c.state = none ∧ c.output = output ∧
    ∀ j < s, ∀ c', M.run input [] j = some c' → c'.state ≠ none

end EdgeSublinearMWIS.Main


