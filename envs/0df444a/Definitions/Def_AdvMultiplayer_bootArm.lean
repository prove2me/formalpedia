-- Prove2me | Definitions.Def_AdvMultiplayer_bootArm
-- name    : AdvMultiplayer_bootArm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T21:02:13.154538+00:00
-- url     : https://prove2.me/theorems/2aafccd2-6c11-47d2-b013-6888eaf161d4
-- title:
--   Algorithm 7: bootstrap arms
-- statement:
--   Calendar time is divided into blocks of length $B_{\mathrm{boot}}$. At a block start an uninformed follower draws a coin of mean $1/m$; if active, it draws its held arm from $p_i(a)=\frac12(w_i^{\mathrm{boot}}(a)/\sum_zw_i^{\mathrm{boot}}(z)+1/K)$ and an index $\iota\sim\mathrm{Unif}([A])$, and in each round it plays $a$ if $I_\iota(t)=0$ and a fresh uniform arm of $[K]\setminus\{a\}$ otherwise; if inactive it plays a fresh uniform arm. The coordinator draws $J$ once, draws a block target $z$, and plays $z$ on DATA (moving to a uniform arm of $[K]\setminus\{z\}$ in MULTICAST when $\prod_{u\in\Lambda}\varphi_J(u,t)=1$), $R_{0,t}$ on DOWN, and a uniform arm on UP.
--
--   **Formalization Note.** All private draws are read from the tape.
-- source:
--   Gan, Square-Root Regret for Adversarial Multiplayer Bandits without Collision Information or Shared Randomness, arXiv:2610.05688, Algorithm 7, p.43; Algorithm 10, p.59; (46), (48)

import Mathlib
import Definitions.Def_AdvMultiplayer_recordProg

open LNTopology.Hermetization

namespace AdvMultiplayer

variable (p : Size)

/-- The first round of a block `ℬ_s` of length `B_boot` (46). -/
noncomputable def blockStart (t : ℕ) : Bool := decide ((t - 1) % p.Bboot = 0)

/-- The last round of a block; the final block may be shorter (p.41). -/
noncomputable def blockEnd (t : ℕ) : Bool := decide (t % p.Bboot = 0 ∨ t = p.T)

/-- Ticked read of a tape coordinate. -/
def tapeRead (tape : Fin 4 → ℝ) (k : Fin 4) : StateM ℕ ℝ := do
  tick 1
  pure (tape k)

/-- A uniform arm of `[K]`: `1 + ⌊KV⌋`. -/
noncomputable def unifArm (v : ℝ) : StateM ℕ ℕ := do
  let x ← rmul (p.K : ℝ) v
  let k ← floorProg (armFuel p) x
  pure (1 + k)

/-- A uniform arm of `[K]∖{z}`: `1 + ⌊(K-1)V⌋`, shifted past `z`. -/
noncomputable def unifArmExcept (z : ℕ) (v : ℝ) : StateM ℕ ℕ := do
  let x ← rmul ((p.K - 1 : ℕ) : ℝ) v
  let k ← floorProg (armFuel p) x
  pure (if 1 + k < z then 1 + k else 2 + k)

/-- The held arm `a ∼ p_i` of (48), by inverse CDF in increasing order, and its probability. -/
noncomputable def heldDraw (w : ℕ → ℝ) (v : ℝ) : StateM ℕ (ℕ × ℝ) := do
  let mut tot : ℝ := 0
  for a in armList p do
    tick 1
    tot ← radd tot (w a)
  let mut cum : ℝ := 0
  let mut j : ℕ := p.K
  let mut pj : ℝ := 0
  let mut done := false
  for a in armList p do
    tick 1
    let x ← rdiv (w a) tot
    let y ← radd x (1 / (p.K : ℝ))
    let pa ← rmul (1 / 2) y
    cum ← radd cum pa
    let hit ← rlt v cum
    if !done then
      pj := pa
      j := a
      if hit then done := true
  pure (j, pj)

/-- The coordinator's arm before launch: Algorithm 7, lines 6, 12, 14–21. At round `1` it draws its
row index `J = 1 + ⌊MV⌋`, unless an execution fixes `J`. -/
noncomputable def bootArmCoordinator (d : TableData p) (kd : RunKind) (t : ℕ) (tape : Fin 4 → ℝ)
    (s0 : Local p) : StateM ℕ (ℕ × Local p) := do
  let mut s := s0
  if t = 1 then
    let v ← tapeRead tape 2
    let x ← rmul (p.M : ℝ) v
    let j ← floorProg (Nat.clog 2 (p.M + 1) + 1) x
    s := { s with row := kd.forceRow.getD (1 + j) }
  if blockStart p t then
    let v ← tapeRead tape 0
    let z ← unifArm p v
    tick p.A
    s := { s with bc := { s.bc with target := z, lam := List.range' 1 p.A, multicast := false } }
  let q := s.row
  let sl ← readSlot p d q t
  if sl = Slot.data then
    let z := s.bc.target
    if s.bc.multicast then
      let mut all := true
      for u in s.bc.lam do
        tick 1
        let b ← fwdBit p d q u t
        if !b then all := false
      if all then
        let v ← tapeRead tape 1
        let a ← unifArmExcept p z v
        return (a, s)
    return (z, s)
  else if sl = Slot.down then
    let R ← readTuple p d q t
    return (R 0, s)
  else
    let v ← tapeRead tape 1
    let a ← unifArm p v
    return (a, s)

/-- **A follower's arm before activation: Algorithm 7, lines 8–9, 22–25, and Algorithm 10, lines 3–10
(pp.43, 59).** Gan, arXiv:2610.05688, Section 6.1. At a block start it draws the activity coin of mean
`1/m`, the held arm `a ∼ p_i` and the index `ι ∼ Unif([A])`, and clears the block's counters. The
private draws come from the tape.

The module also holds the coordinator's arm before launch. -/
noncomputable def bootArmFollower (d : TableData p) (t : ℕ) (tape : Fin 4 → ℝ) (s0 : Local p) :
    StateM ℕ (ℕ × Local p) := do
  let mut s := s0
  if blockStart p t then
    let v0 ← tapeRead tape 0
    let act ← rlt v0 (1 / (p.m : ℝ))
    tick p.M
    s := { s with bf := { s.bf with active := act, G := 0, pending := none, nv := fun _ => 0,
                                    dead := fun _ => false } }
    if act then
      let v1 ← tapeRead tape 1
      let (a, pa) ← heldDraw p s.bf.bw v1
      let v2 ← tapeRead tape 2
      let x ← rmul (p.A : ℝ) v2
      let u ← floorProg (Nat.clog 2 (p.A + 1) + 1) x
      s := { s with bf := { s.bf with held := a, pheld := pa, iota := 1 + u } }
  let v3 ← tapeRead tape 3
  if s.bf.active then
    let bit ← idBit p d s.bf.iota t
    if bit then
      let a ← unifArmExcept p s.bf.held v3
      return (a, s)
    else
      return (s.bf.held, s)
  else
    let a ← unifArm p v3
    return (a, s)

end AdvMultiplayer


