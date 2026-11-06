-- Prove2me | Definitions.Def_AdvMultiplayer_finishOrdinary
-- name    : AdvMultiplayer_finishOrdinary
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T21:02:39.890867+00:00
-- url     : https://prove2.me/theorems/08a96272-bbfd-4f09-875f-9efa9cadca79
-- title:
--   Algorithm 6 after the arm choice
-- statement:
--   After its observation, an activated player records (Algorithm 4); serves its queues online; if selected, feeds the decoder and tests the acceptance condition (35), applying an accepted record; updates confirmations and releases; and, at the end, applies FinishRound or reads the proposal bit.
--
--   **Formalization Note.** The steps are marked by the line numbers of Algorithm 6. In a reference execution a decoded word other than the one currently encoded on its channel is rejected before any assignment-dependent update, as on p.20; in the actual execution no such test exists.
-- source:
--   Gan, Square-Root Regret for Adversarial Multiplayer Bandits without Collision Information or Shared Randomness, arXiv:2610.05688, Algorithm 6, p.34; Algorithm 5 FinishRound, p.30

import Mathlib
import Definitions.Def_AdvMultiplayer_recordProg

open LNTopology.Hermetization

namespace AdvMultiplayer

variable (p : Size)

/-- The follower's part of Algorithm 6 after its observation (lines 11–14, 21–26, 37–39, 41). -/
noncomputable def finishFollower (d : TableData p) (md : Mode p) (q t i a : ℕ) (y : ℝ)
    (s0 : Local p) : Chk (Local p × Log p) := do
  let st0 := s0.fol.state
  let mut lg := Log.none p
  -- line 11
  let (s1, arr) ← recordProg p d q t i a y s0
  let mut f := s1.fol
  -- lines 12–14
  if st0 = 1 ∨ st0 = 2 then
    let Δ := match arr with
      | some (j, n) => if j = f.rc.a then n else 0
      | none => 0
    let (g, b') ← serveProg p f.b Δ
    ensure (f.S + g ≤ p.T * p.D)
    f := { f with S := f.S + g, δ := g, b := b' }
  let sl ← readSlot p d q t
  let needSel : Bool := sl ≠ Slot.data
  let k ← (if needSel then readSel p d q t else pure 0 : StateM ℕ ℕ)
  let pos ← rlt 0 y
  -- lines 21–26
  if sl = Slot.down ∧ k = i ∧ st0 = 0 then
    let (cc, b) ← affineAt p d q t false i
    let (W, dec) ← decodeStep p f.batch cc b t pos
    f := { f with batch := W }
    match dec with
    | none => pure ()
    | some (full, sol) =>
      lg := { lg with decided := some (false, i, full, sol) }
      tick p.Bmsg
      match sol with
      | none => pure ()
      | some w =>
        match parseDown p w with
        | none => pure ()
        | some M =>
          if f.rc.σ < M.σ ∧ M.σ ≤ t then
            let pass : Bool := !md.kind.reference ||
              (by classical exact decide (md.cur false i = some w))
            if pass then
              let (l, S, δ, b') ← replayDown p d q M t f.cand
              lg := { lg with accepted := some w }
              f := { f with rc := M, S := S, δ := δ, b := b', cand := [],
                            state := if l = t + 1 then 1 else 0 }
            else
              lg := { lg with filtered := true }
  -- lines 37–39
  if st0 = 1 then
    if sl = Slot.up then
      let R ← readTuple p d q t
      if k = i ∧ R 0 = f.rc.e ∧ pos then f := { f with state := 2 }
    if sl = Slot.data then
      let p0 ← readPilot p d q t 0
      if p0 = f.rc.a ∧ pos then f := { f with state := 2 }
  -- line 41
  if f.state = 1 ∨ f.state = 2 then
    let bit ← readProp p d q t
    f := { f with lastProp := bit }
  pure ({ s1 with fol := f }, lg)

/-- The coordinator's part of Algorithm 6 after its observation (lines 10–11, 15–20, 27–36, 40). -/
noncomputable def finishCoordinator (d : TableData p) (md : Mode p) (q t a : ℕ) (y : ℝ)
    (s0 : Local p) : Chk (Local p × Log p) := do
  let pc0 := s0.co.pcount
  let mut lg := Log.none p
  -- lines 10–11
  let mut gl : ℕ → ℕ := fun _ => 0
  let (s1, arr) ← recordProg p d q t 0 a y s0
  let mut c := s1.co
  -- lines 15–19: learning is enabled when not frozen
  if c.σ > 0 ∧ t < c.τbar then
    let coll : Bool := decide (c.u ≤ t)
    for j in armList p do
      tick 1
      let Δ := match arr with
        | some (j', n) => if j' = j then n else 0
        | none => 0
      if coll || !(c.inU j) then
        if c.known j then
          let (g, b') ← serveProg p (c.Bq j) Δ
          gl := Function.update gl j g
          c := { c with Bq := Function.update c.Bq j b' }
          if !coll then
            ensure (c.z j + g ≤ p.T * p.D)
            c := { c with z := Function.update c.z j (c.z j + g) }
        else if Δ > 0 then
          c := { c with buf := Function.update c.buf t (Function.update (c.buf t) j Δ),
                        bufCount := c.bufCount + 1 }
  -- line 20
  for j in armList p do
    tick 1
    if c.known j then c := { c with last := Function.update c.last j (gl j) }
  let sl ← readSlot p d q t
  let needSel : Bool := sl ≠ Slot.data
  let k ← (if needSel then readSel p d q t else pure 0 : StateM ℕ ℕ)
  let pos ← rlt 0 y
  -- lines 27–33
  if c.u ≤ t ∧ sl = Slot.up ∧ c.P k = true then
    let (cc, b) ← affineAt p d q t true k
    let (W, dec) ← decodeStep p (c.upBatch k) cc b t pos
    c := { c with upBatch := Function.update c.upBatch k W }
    match dec with
    | none => pure ()
    | some (full, sol) =>
      lg := { lg with decided := some (true, k, full, sol) }
      tick p.Bmsg
      match sol with
      | none => pure ()
      | some w =>
        match parseUp p w with
        | none => pure ()
        | some M =>
          if M.σ = c.σ then
            let pass : Bool := !md.kind.reference ||
              (by classical exact decide (md.cur true k = some w))
            if pass then
              let ak := c.slow k
              let (acc, g0, b') ← replayUp p c ak t M.q
              ensure (c.base k + M.S ≤ p.T * p.D)
              lg := { lg with accepted := some w }
              c := { c with z := Function.update c.z ak (c.base k + M.S),
                            gamU := Function.update c.gamU ak M.δ,
                            acc := Function.update c.acc ak acc,
                            Bq := Function.update c.Bq ak b',
                            last := Function.update c.last ak g0,
                            known := Function.update c.known ak true,
                            P := Function.update c.P k false,
                            pcount := c.pcount - 1 }
            else
              lg := { lg with filtered := true }
  -- lines 34–36
  if t < c.u ∧ pc0 > 0 ∧ sl = Slot.down ∧ c.P k = true ∧ pos then
    let (cc, b) ← affineAt p d q t false k
    tick p.Bmsg
    let v ← hProg p cc b (encDown p (c.msg k))
    if !v then
      c := { c with P := Function.update c.P k false, pcount := c.pcount - 1 }
  -- line 40, FinishRound of Algorithm 5
  if c.u ≤ t then
    for j in armList p do
      tick 1
      ensure (c.acc j + gl j ≤ p.T * p.D)
      c := { c with acc := Function.update c.acc j (c.acc j + gl j) }
  else
    let bit ← readProp p d q t
    c := { c with lastBit := bit }
  pure ({ s1 with co := c }, lg)

/-- **Algorithm 6 after the arm choice, p.34.** Gan, arXiv:2610.05688, Section 5.4: one player's
operations once its quantized observation `y` is known, on the player's own registers, observation and
row. In the actual execution the only input from outside the player is `y`; `md` is
`Mode.actual`. A reference execution also rejects every decoded word other than the word currently
encoded on its channel (p.20). The lines of Algorithm 6 are marked in `finishFollower` and
`finishCoordinator`; line 42 has no effect on an activated player, since the bootstrap registers are
discarded at activation. -/
noncomputable def finishOrdinary (d : TableData p) (md : Mode p) (i t a : ℕ) (y : ℝ) (s : Local p) :
    Chk (Local p × Log p) :=
  if i = 0 then finishCoordinator p d md s.row t a y s
  else finishFollower p d md s.row t i a y s

end AdvMultiplayer


