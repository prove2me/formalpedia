-- Prove2me | Definitions.Def_AdvMultiplayer_startRound
-- name    : AdvMultiplayer_startRound
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:58:49.489269+00:00
-- url     : https://prove2.me/theorems/f6836b94-3b76-44fa-a519-d42b84dd50a6
-- title:
--   StartRound of Algorithm 5 and the rates (7)
-- statement:
--   At the start of a round the coordinator detects a public interruption (a grid boundary or a proposal bit of the previous round) and starts collection. If no assignment has started, or collection has finished, it starts the next assignment: it sets the scores, renews the anchor and rates by (7) and draws the slow set from $p_{w_t}$ at an episode start, or else recovers $w_{u-1},w_u$ and draws from $\nu_t$; then it chooses the auxiliary arm $e$ of smallest anchor weight outside the slow set, retains the base scores, and constructs the DOWN records (21).
--
--   **Formalization Note.** The rates are computed as on p.49, from $e_r(w_{-i})$ by the recursion, and $\xi_i$ by comparison with $2^{-k}$, $0\le k\le b_N$.
-- source:
--   Gan, Square-Root Regret for Adversarial Multiplayer Bandits without Collision Information or Shared Randomness, arXiv:2610.05688, Algorithm 5, p.30; Section 8, p.49

import Mathlib
import Definitions.Def_AdvMultiplayer_drawSlow

open LNTopology.Hermetization

namespace AdvMultiplayer

variable (p : Size)

/-- The weight vector of a score vector, by repeated squaring (p.50). -/
noncomputable def weightsProg (z : ℕ → ℕ) : StateM ℕ (ℕ → ℝ) := do
  let mut w : ℕ → ℝ := fun _ => 0
  for a in armList p do
    tick 1
    let x ← weightProg p (z a)
    w := Function.update w a x
  pure w

/-- The rates of (7) at a new anchor `w̄`: first `e_k(w̄)`, then `θ_w̄(i)` by
`e_r(w_{-i}) = e_r(w) - w_i e_{r-1}(w_{-i})` and `θ_w(i) = w_i e_{m-1}(w_{-i})/e_m(w)` (p.49), then
`f_i`, and `ξ_i = 2^{-h_i}` by comparing `max{β, f_i}` with `2^{-k}` for `0 ≤ k ≤ b_N` (p.49). The
result is the exponents `h_i` and the rates `ξ_i`. -/
noncomputable def ratesProg (w : ℕ → ℝ) : Chk ((ℕ → ℕ) × (ℕ → ℝ)) := do
  let mut e : ℕ → ℝ := fun k => if k = 0 then 1 else 0
  for a in armList p do
    for k' in List.range p.m do
      tick 1
      let k := p.m - k'
      let x ← rmul (w a) (e (k - 1))
      let y ← radd (e k) x
      e := Function.update e k y
  ensureLt 0 (e p.m)
  let beta := p.betaOf p.eta
  let mut hs : ℕ → ℕ := fun _ => 0
  let mut xs : ℕ → ℝ := fun _ => 0
  for a in armList p do
    tick 1
    let mut prev : ℝ := 1
    for r in List.range' 1 (p.m - 1) do
      tick 1
      let x ← rmul (w a) prev
      prev ← rsub (e r) x
    let th0 ← rmul (w a) prev
    let th ← rdiv th0 (e p.m)
    let u0 ← rmul (p.K : ℝ) th
    let u1 ← rsub 1 th
    let u2 ← rmul (p.m : ℝ) u1
    let u3 ← radd u0 u2
    let u4 ← rmul (32 * (p.m : ℝ)) u3
    ensureLt 0 u4
    let f ← rdiv th u4
    let bigger ← rle beta f
    let x := if bigger then f else beta
    ensureLt 0 x
    ensureLe x 1
    let mut h : ℕ := 0
    let mut pw : ℝ := 1
    let mut xi : ℝ := 1
    for k in List.range (p.bN + 1) do
      tick 1
      let ok ← rle x pw
      if ok then
        h := k
        xi := pw
      pw ← rdiv pw 2
    hs := Function.update hs a h
    xs := Function.update xs a xi
  pure (hs, xs)

/-- The set `[d]` as an array. -/
def allFollowers : ℕ → Bool := fun i => decide (1 ≤ i ∧ i ≤ p.d)

/-- The new assignment of `StartRound`, lines 6–18 of Algorithm 5, with `σ = 0` or
`u ≤ t, P = ∅`. -/
noncomputable def newAssignment (d : TableData p) (q t : ℕ) (c0 : Co p) : Chk (Co p) := do
  let mut c := c0
  -- lines 6–9: the scores `z(t)`, keeping `z(u)` for line 13
  let zu := c.z
  if c.σ = 0 then
    tick p.K
    c := { c with z := fun _ => 0, Bq := fun _ => 0 }
  else
    for a in armList p do
      tick 1
      ensure (c.z a + c.acc a ≤ p.T * p.D)
      ensure (c.gamU a ≤ c.z a)
      c := { c with z := Function.update c.z a (c.z a + c.acc a) }
  let wt ← weightsProg p c.z
  -- lines 10–13
  let mut U : List ℕ := List.nil
  if c.σ = 0 ∨ c.τbar ≤ t then
    let (hs, xs) ← ratesProg p wt
    tick p.K
    c := { c with wbar := wt, hexp := hs, xi := xs }
    U ← drawSlow p d q t [(1, wt)] c.wbar
  else
    let wu ← weightsProg p zu
    let wu' ← weightsProg p fun a => zu a - c.gamU a
    let h := p.propOf p.eta
    let x ← rsub 1 h
    let y ← powProg (Nat.clog 2 (p.T + 2) + 1) x (t + 1 - c.u)
    let kap ← rdiv y h
    U ← drawSlow p d q t [(1, wt), (kap, wu), (-kap, wu')] c.wbar
  -- lines 14–15
  let mut inU : ℕ → Bool := fun _ => false
  let mut slow : ℕ → ℕ := fun _ => 0
  let mut idx : ℕ := 1
  for a in U do
    tick 1
    inU := Function.update inU a true
    slow := Function.update slow idx a
    idx := idx + 1
  let mut e : ℕ := 0
  let mut best : ℝ := 0
  for a in armList p do
    tick 1
    if !(inU a) then
      let lt ← rlt (c.wbar a) best
      if e == 0 || lt then
        e := a
        best := c.wbar a
  ensure (e ≠ 0)
  -- lines 16–18
  let mut msg : ℕ → DownRec := fun _ => ⟨0, 0, 0, 0, 0⟩
  let mut base : ℕ → ℕ := fun _ => 0
  for i in List.range' 1 p.d do
    tick 1
    ensure (c.Bq (slow i) ≤ p.T * p.D)
    msg := Function.update msg i ⟨t, slow i, e, c.hexp (slow i), c.Bq (slow i)⟩
    base := Function.update base i (c.z (slow i))
  tick p.K
  pure { c with σ := t, u := p.T + 1, τbar := p.gridEnd (Size.gridOf p.eta) t,
                P := allFollowers p, pcount := p.d, inU := inU, slow := slow, aux := e, msg := msg,
                base := base, known := fun a => !(inU a) }

/-- **`StartRound(t)` of Algorithm 5, p.30.** Gan, arXiv:2610.05688: line 2 detects the public
interruption and starts collection, saving `Γ_{u-1}` from the working last services and clearing the
raw buffer; line 5 starts the next assignment. -/
noncomputable def startRound (d : TableData p) (q t : ℕ) (c0 : Co p) : Chk (Co p) := do
  let mut c := c0
  if c.σ > 0 ∧ c.u = p.T + 1 ∧ (t = c.τbar ∨ c.lastBit = true) then
    tick (1 + c.bufCount)
    c := { c with u := t, P := allFollowers p, pcount := p.d, acc := fun _ => 0,
                  buf := fun _ _ => 0, bufCount := 0, gamU := c.last }
  if c.σ = 0 ∨ (c.u ≤ t ∧ c.pcount = 0) then
    newAssignment p d q t c
  else
    pure c

end AdvMultiplayer


