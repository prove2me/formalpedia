-- Prove2me | Definitions.Def_AdvMultiplayer_armOrdinary
-- name    : AdvMultiplayer_armOrdinary
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:59:56.30306+00:00
-- url     : https://prove2.me/theorems/70d25bad-776d-45ea-9b33-bbe07b66a7d7
-- title:
--   Algorithm 3: arms on an active round
-- statement:
--   The coordinator draws the fast arm when the assignment is live and all confirmations have arrived. Otherwise it plays its pilot on DATA, sends the DOWN record of the selected follower while that follower is in $\mathcal P$, and plays $R_0$ in the remaining cases. An unoccupied follower plays its pilot on DATA, sends its UP record when selected on UP, and plays its tuple arm otherwise. A released follower, or any occupied follower on DATA, plays its assigned arm. A pending follower moves to the auxiliary arm $e$ on the release test and to avoid the receiver arm.
-- source:
--   Gan, Square-Root Regret for Adversarial Multiplayer Bandits without Collision Information or Shared Randomness, arXiv:2610.05688, Algorithm 3, p.23

import Mathlib
import Definitions.Def_AdvMultiplayer_startRound

open LNTopology.Hermetization

namespace AdvMultiplayer

variable (p : Size)

/-- The coordinator's branch of Algorithm 3, p.23 (lines 2–10). It returns the arm and the registers
with the fast-draw status set. -/
noncomputable def armCoordinator (d : TableData p) (q t : ℕ) (c : Co p) : Chk (ℕ × Co p) := do
  if c.σ > 0 ∧ c.u = p.T + 1 ∧ c.pcount = 0 then
    let (x, pi) ← fastDraw p d q t c
    pure (x, { c with fastNow := true, fastPi := pi })
  else
    let c' := { c with fastNow := false }
    let sl ← readSlot p d q t
    if sl = Slot.data then
      let a ← readPilot p d q t 0
      pure (a, c')
    else
      let R ← readTuple p d q t
      let k ← readSel p d q t
      if sl = Slot.down ∧ c.P k = true then
        let (cc, b) ← affineAt p d q t false k
        tick p.Bmsg
        let a ← sendArm p cc b (encDown p (c.msg k)) (R 0) (R k)
        pure (a, c')
      else
        pure (R 0, c')

/-- **Algorithm 3 at follower `j`, p.23 (lines 12–26).** Gan, arXiv:2610.05688, Section 4.2. The
module also holds the coordinator's branch. -/
noncomputable def armFollower (d : TableData p) (q t j : ℕ) (f : Fol p) : Chk ℕ := do
  let sl ← readSlot p d q t
  if f.state = 0 then
    if sl = Slot.data then
      readPilot p d q t j
    else
      let R ← readTuple p d q t
      let k ← readSel p d q t
      if sl = Slot.up ∧ k = j then
        let (cc, b) ← affineAt p d q t true j
        tick p.Bmsg
        sendArm p cc b (encUp p ⟨f.rc.σ, f.S, f.δ, f.b⟩) (R j) (R 0)
      else
        pure (R j)
  else if f.state = 2 ∨ sl = Slot.data then
    pure f.rc.a
  else
    let R ← readTuple p d q t
    let i ← readSel p d q t
    if sl = Slot.up ∧ i = j ∧ R 0 = f.rc.e then
      pure f.rc.e
    else if (sl = Slot.down ∧ f.rc.a = R i) ∨ (sl = Slot.up ∧ f.rc.a = R 0) then
      pure f.rc.e
    else
      pure f.rc.a

end AdvMultiplayer


