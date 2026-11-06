-- Prove2me | Definitions.Def_AdvMultiplayer_recordProg
-- name    : AdvMultiplayer_recordProg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T21:01:16.140796+00:00
-- url     : https://prove2.me/theorems/682cca08-146f-40b9-a5dc-e45a3bafae26
-- title:
--   Algorithm 4 and the delayed replays
-- statement:
--   On a DATA round whose recorder source is the player, an unoccupied follower logs the observation if the recording mask passes. Otherwise, if the score updates are not frozen and the player owns its arm $j$ and the mask passes, the thinning test $V_t\le\xi_j/((1/2)s_i\pi_i(j)\zeta)$ decides whether the raw arrival $\lfloor D\eta Y/\xi_j\rfloor$ is produced.
--
--   After accepting a DOWN record, a follower computes the endpoint $l$ of (36), recovers each arrival on $[\sigma,l)$ from its candidates by (37), and applies (11). After accepting an UP record, the coordinator replays (11) on $u,\dots,t$ from the buffered arrivals, freezing at $\bar\tau$.
-- source:
--   Gan, Square-Root Regret for Adversarial Multiplayer Bandits without Collision Information or Shared Randomness, arXiv:2610.05688, Algorithm 4, p.27; (36), (37), p.33; Algorithm 6 lines 30-32

import Mathlib
import Definitions.Def_AdvMultiplayer_armOrdinary
import Definitions.Def_AdvMultiplayer_Queue

open LNTopology.Hermetization

namespace AdvMultiplayer

variable (p : Size)

/-- The recording mask (28), p.27: `P_{l,t} ≠ j` for every player `l ≠ i`. -/
noncomputable def maskProg (d : TableData p) (q t i j : ℕ) : StateM ℕ Bool := do
  let mut ok := true
  for l in List.range p.m do
    tick 1
    if l ≠ i then
      let x ← readPilot p d q t l
      if x = j then ok := false
  pure ok

/-- The recorder-source probability `s_i` (p.27). -/
noncomputable def sourceProb (i : ℕ) : ℝ := if i = 0 then 1 / 2 else 1 / (2 * (p.d : ℝ))

/-- `2^{-h}`, by repeated squaring. -/
noncomputable def halfPow (h : ℕ) : StateM ℕ ℝ := powProg (Nat.clog 2 (p.bN + 2) + 1) (1 / 2) h

/-- **Algorithm 4, p.27: record a DATA increment or one candidate observation.** Gan,
arXiv:2610.05688, Section 4.4. Input: activated player `i`, its arm `a` and quantized observation
`y`. Output: the state with `ℬ_i` updated, and the raw arrival `(j, Δ_t(j))`, if any.

**Formalization Note.** The player's `π_i(j)` of p.27 is `1` for an occupied follower, `1/K` for the
coordinator on a pilot, and the current fast-arm probability on a fast draw. The checks of App. A.1
test the positivity of the denominator and that the thinning ratio lies in `[0,1]`. -/
noncomputable def recordProg (d : TableData p) (q t i a : ℕ) (y : ℝ) (s : Local p) :
    Chk (Local p × Option (ℕ × ℕ)) := do
  let sl ← readSlot p d q t
  if sl ≠ Slot.data then return (s, none)
  let src ← readRec p d q t
  if src ≠ i then return (s, none)
  let j := a
  let v ← readThin p d q t
  let mask ← maskProg p d q t i j
  if i > 0 ∧ s.fol.state = 0 then
    if mask then
      tick 1
      return ({ s with fol := { s.fol with cand := s.fol.cand ++ [⟨t, j, y, v⟩] } }, none)
    else
      return (s, none)
  if i = 0 ∧ s.co.σ > 0 ∧ s.co.τbar ≤ t then return (s, none)
  let owns : Bool := if i = 0 then decide (s.co.u ≤ t) || !(s.co.inU j) else decide (j = s.fol.rc.a)
  if !owns || !mask then return (s, none)
  let xi ← (if i = 0 then pure (s.co.xi j) else halfPow p s.fol.rc.h : StateM ℕ ℝ)
  let pi : ℝ :=
    if i = 0 then (if s.co.fastNow then s.co.fastPi else 1 / (p.K : ℝ)) else 1
  let u0 ← rmul (1 / 2) (sourceProb p i)
  let u1 ← rmul u0 pi
  let u2 ← rmul u1 p.zeta
  ensureLt 0 u2
  ensureLt 0 xi
  let ratio ← rdiv xi u2
  ensureLe ratio 1
  let pass ← rle v ratio
  if pass then
    let x0 ← rmul (p.D : ℝ) p.eta
    let x1 ← rmul x0 y
    let x2 ← rdiv x1 xi
    let Δ ← floorProg (dFuel p) x2
    ensure (Δ ≤ p.D)
    return (s, some (j, Δ))
  else
    return (s, none)

/-- One queue service by (11): the service and the new queue, with the domain checks of App. A.1. -/
noncomputable def serveProg (B Δ : ℕ) : Chk (ℕ × ℕ) := do
  tick 1
  let cap := p.capOf p.eta
  let g := serviceOf cap B Δ
  let B' := queueNext cap B Δ
  ensure (g ≤ p.D ∧ B' ≤ p.T * p.D)
  pure (g, B')

/-- The contribution `ψ_h(y, v)` of one saved observation (30), p.28. -/
noncomputable def psiProg (h : ℕ) (y v : ℝ) : Chk ℕ := do
  let hp ← halfPow p h
  ensureLt 0 hp
  ensureLt 0 p.zeta
  let u0 ← rmul (4 * (p.d : ℝ) * (p.K : ℝ)) hp
  let u1 ← rdiv u0 p.zeta
  let ok ← rle v u1
  if ok then
    let x0 ← rmul (p.D : ℝ) p.eta
    let x1 ← rdiv x0 hp
    let x2 ← rmul x1 y
    let n ← floorProg (dFuel p) x2
    ensure (n ≤ p.D)
    pure n
  else pure 0

/-- The delayed replay after a DOWN acceptance (36), (37), p.33: the exclusive endpoint `l`, then
(11) on `[σ, l)` from the record's queue with the arrivals recovered from the candidate list. Returns
`(l, S, δ, b)`. -/
noncomputable def replayDown (d : TableData p) (q : ℕ) (M : DownRec) (t : ℕ)
    (cand : List CandRec) : Chk (ℕ × ℕ × ℕ × ℕ) := do
  let mut l := min (t + 1) (p.gridEnd (Size.gridOf p.eta) M.σ)
  let mut found := false
  for s in List.range' M.σ (t - M.σ) do
    tick 1
    if !found && decide (s < l) then
      let bit ← readProp p d q s
      if bit then
        l := min l (s + 1)
        found := true
  let mut arr : ℕ → ℕ := fun _ => 0
  for e in cand do
    tick 1
    if e.s ≥ M.σ ∧ e.s < l ∧ e.j = M.a then
      let n ← psiProg p M.h e.y e.v
      arr := Function.update arr e.s (arr e.s + n)
  let mut S : ℕ := 0
  let mut δ : ℕ := 0
  let mut b : ℕ := M.q
  for r in List.range' M.σ (l - M.σ) do
    tick 1
    let (g, b') ← serveProg p b (arr r)
    S := S + g
    δ := g
    b := b'
  ensure (S ≤ p.T * p.D)
  pure (l, S, δ, b)

/-- The coordinator's replay after an UP acceptance (Algorithm 6, lines 30–32): (11) on `u, …, t`
from the record's queue with the buffered arrivals, including zero arrivals and freezing at `τ̄`.
Returns the accumulated service, the last service and the queue. -/
noncomputable def replayUp (c : Co p) (a t q0 : ℕ) : Chk (ℕ × ℕ × ℕ) := do
  let mut acc : ℕ := 0
  let mut g0 : ℕ := 0
  let mut b : ℕ := q0
  for r in List.range' c.u (t + 1 - c.u) do
    tick 1
    if r < c.τbar then
      let (g, b') ← serveProg p b (c.buf r a)
      acc := acc + g
      g0 := g
      b := b'
    else
      g0 := 0
  ensure (acc ≤ p.T * p.D)
  pure (acc, g0, b)

end AdvMultiplayer


