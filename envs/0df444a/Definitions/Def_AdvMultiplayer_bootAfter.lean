-- Prove2me | Definitions.Def_AdvMultiplayer_bootAfter
-- name    : AdvMultiplayer_bootAfter
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T21:03:56.231217+00:00
-- url     : https://prove2.me/theorems/adff3dc2-891b-4f07-a0c6-8250741a8c7b
-- title:
--   Algorithm 7: bootstrap updates, declaration and launch
-- statement:
--   A follower counts its positive stay observations. Until a declaration is saved it updates, for every candidate row $v$ with slot DATA, the count $n_v$ and the flag dead$_v$ (set if $\varphi_v(\iota,t)=0$), and saves a unique row with $n_v\ge q_{\mathrm{dec}}$ and no mismatch. At a block end it updates the held-arm weight by (49) and activates in a pending declared row in the next round.
--
--   The coordinator shrinks $\Lambda$ on DATA positives, enters MULTICAST when $|\Lambda|\le L_0$, counts DOWN positives per arm, and at a block end launches the zero-score learner in the next round if $\hat D_r=K\max_{S}\sum_{a\in S}C_r(a)>4Q$.
--
--   **Formalization Note.** The floor in (49) is a ticked search. The reference execution tests only the true row.
-- source:
--   Gan, Square-Root Regret for Adversarial Multiplayer Bandits without Collision Information or Shared Randomness, arXiv:2610.05688, Algorithm 7, p.43; Algorithm 10, p.59; (49), (50), (65), (66)

import Mathlib
import Definitions.Def_AdvMultiplayer_bootArm

open LNTopology.Hermetization

namespace AdvMultiplayer

variable (p : Size)

/-- The current-observation candidate update of Algorithm 10, lines 14–18, p.59: counts and flags
over the candidate rows with `τ_{v,t} = DATA`, then a unique passing row is saved as the pending
declaration. The reference execution tests only the true row `J` (Algorithm 8, line 2). -/
noncomputable def candidateUpdate (d : TableData p) (kd : RunKind) (t : ℕ) (b0 : BootF) :
    StateM ℕ BootF := do
  let mut b := b0
  let rowsTested : List ℕ :=
    if kd.reference then (kd.forceRow.map fun j => [j]).getD [] else List.range' 1 p.M
  for v in rowsTested do
    tick 1
    let sl ← readSlot p d v t
    if sl = Slot.data then
      b := { b with nv := Function.update b.nv v (b.nv v + 1) }
      let f ← fwdBit p d v b.iota t
      if !f then b := { b with dead := Function.update b.dead v true }
  let mut count : ℕ := 0
  let mut who : ℕ := 0
  for v in rowsTested do
    tick 1
    if p.qdec ≤ b.nv v ∧ !(b.dead v) then
      count := count + 1
      who := v
  if count = 1 then b := { b with pending := some who }
  pure b

/-- The weight update (49), p.42, with precision `P = 4b_N`:
`w(a) ← 2^{-4b_N} ⌊2^{4b_N} w(a) (1 + G/(4K B_boot p_i(a)))⌋`. Each factor is at most `3/2`, so the
floor's argument stays below `2^{4b_N + n_boot + 1}` (the fuel). -/
noncomputable def gainUpdate (b : BootF) : StateM ℕ BootF := do
  let a := b.held
  let x0 ← rmul (4 * (p.K : ℝ) * (p.Bboot : ℝ)) b.pheld
  let x1 ← rdiv (b.G : ℝ) x0
  let x2 ← radd 1 x1
  let pp ← powProg (Nat.clog 2 (4 * p.bN + 2) + 1) 2 (4 * p.bN)
  let x3 ← rmul pp (b.bw a)
  let x4 ← rmul x3 x2
  let n ← floorProg (4 * p.bN + p.nboot + 2) x4
  let x5 ← rdiv (n : ℝ) pp
  pure { b with bw := Function.update b.bw a x5 }

/-- A follower's update before activation after its observation: Algorithm 7, lines 27–30, 38–40,
and Algorithm 10, lines 12–21. A pending declaration is applied at the block boundary. -/
noncomputable def bootAfterFollower (d : TableData p) (kd : RunKind) (t : ℕ) (y : ℝ) (s0 : Local p) :
    StateM ℕ (Local p) := do
  let mut s := s0
  if s.bf.active then
    let bit ← idBit p d s.bf.iota t
    let pos ← rlt 0 y
    if !bit && pos then
      s := { s with bf := { s.bf with G := s.bf.G + 1 } }
      if s.bf.pending.isNone then
        let b ← candidateUpdate p d kd t s.bf
        s := { s with bf := b }
  if blockEnd p t then
    if s.bf.active then
      let b ← gainUpdate p s.bf
      s := { s with bf := b }
    match s.bf.pending with
    | some v => s := { s with activated := true, row := v }
    | none => pure ()
  pure s

/-- The sum of the `m` largest counters, as in (50), by `m` scans. -/
noncomputable def topSum (cnt : ℕ → ℕ) : StateM ℕ ℕ := do
  let mut taken : ℕ → Bool := fun _ => false
  let mut tot : ℕ := 0
  for _ in List.range p.m do
    let mut best : ℕ := 0
    let mut bestV : ℕ := 0
    for a in armList p do
      tick 1
      if !(taken a) ∧ (best = 0 ∨ bestV < cnt a) then
        best := a
        bestV := cnt a
    taken := Function.update taken best true
    tot := tot + bestV
  pure tot

/-- **The coordinator's update before launch: Algorithm 7, lines 31–36, 41–43, p.43.** Gan,
arXiv:2610.05688, Section 6.1. DISCOVER shrinks `Λ` on DATA positives, MULTICAST starts when
`|Λ| ≤ L₀`, the DOWN counters are updated, and at a block end the readiness test
`D̂_r = K max_S Σ_{a∈S} C_r(a) > 4Q` launches the zero-score, zero-queue learner at `t+1`.

The module also holds the followers' update before activation. -/
noncomputable def bootAfterCoordinator (d : TableData p) (t a : ℕ) (y : ℝ) (s0 : Local p) :
    StateM ℕ (Local p) := do
  let mut s := s0
  let _ := a
  let q := s.row
  let sl ← readSlot p d q t
  let pos ← rlt 0 y
  if sl = Slot.data ∧ !s.bc.multicast ∧ pos then
    let mut lam : List ℕ := []
    for u in s.bc.lam do
      tick 1
      let b ← idBit p d u t
      if b then lam := lam ++ [u]
    tick 1
    s := { s with bc := { s.bc with lam := lam, multicast := decide (lam.length ≤ p.L0) } }
  else if sl = Slot.down then
    let R ← readTuple p d q t
    if pos then
      s := { s with bc := { s.bc with cnt := Function.update s.bc.cnt (R 0) (s.bc.cnt (R 0) + 1) } }
  if blockEnd p t then
    let tot ← topSum p s.bc.cnt
    if 4 * p.Qlaunch < p.K * tot then
      s := { s with activated := true }
  pure s

end AdvMultiplayer


