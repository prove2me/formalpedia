-- Prove2me | Definitions.Def_DecDynMatch_roundStart
-- name    : DecDynMatch_roundStart
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:56:57.783826+00:00
-- url     : https://prove2.me/theorems/2f54b1e1-88de-4877-af64-9d9e7966a87b
-- title:
--   Round-start checks of SC-DA
-- statement:
--   At the start of each round, before proposing, an SC-DA player performs three checks in this order:
--
--   1. if a mode change $\nu$ is pending, it switches to that mode and clears $\nu$; entering Seek clears the rejection flag $\textsf{seenR}$, entering Work sets $h\leftarrow 0$, $k\leftarrow 1$;
--   2. **replay expiration**: if it is in Replay and $a\ge q$, it switches to Seek and clears $\textsf{seenR}$;
--   3. **sweep qualification**: if it is in Seek and $\rho=J$, it switches to Sweep with $s\leftarrow 1$, $\textsf{blockOK}\leftarrow$ true.
--
--   The resulting state is the round-start state used throughout the analysis.
-- source:
--   J. Chen, M. Gao, Z. Zhang, Decentralized Dynamic Stable Matching, arXiv:2610.41912 (held version, sha256 6a27277e…), Algorithm 1, lines 5–18, p.6; execution conventions, p.14

import Mathlib
import Definitions.Def_DecDynMatch_J
import Definitions.Def_DecDynMatch_LState

namespace DecDynMatch

variable {K : ℕ}

/-- Apply the pending mode change and clear `ν` (Algorithm 1, lines 5–12, p.6): entering Seek
clears `seenR`; entering Work sets `h ← 0`, `k ← 1`. -/
def applyPending (st : LState K) : LState K :=
  match st.ν with
  | none => st
  | some .seek => { st with m := .seek, ν := none, seenR := false }
  | some .work => { st with m := .work, ν := none, h := 0, k := 1 }
  | some md => { st with m := md, ν := none }

/-- Replay expiration (lines 13–15): "if m = Replay and a ≥ q then m ← Seek; seenR ← false". -/
def expire (st : LState K) : LState K :=
  if st.m = .replay ∧ st.q ≤ st.a then { st with m := .seek, seenR := false } else st

/-- Sweep qualification (lines 16–18): "if m = Seek and ρ = J then m ← Sweep; s ← 1;
blockOK ← true". -/
def qualify (st : LState K) : LState K :=
  if st.m = .seek ∧ st.ρ = J K then { st with m := .sweep, s := 1, blockOK := true } else st

/-- **Round-start checks of SC-DA.** J. Chen, M. Gao, Z. Zhang, *Decentralized Dynamic Stable
Matching*, arXiv:2610.41912 (held version, sha256 6a27277e…), Algorithm 1, lines 5–18, p.6, in the
order of the execution conventions, p.14: "Before proposing, each player applies its pending mode
change and clears ν, checks replay expiration, and checks sweep qualification, in that order." -/
def roundStart (st : LState K) : LState K := qualify (expire (applyPending st))

end DecDynMatch


