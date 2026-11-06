-- Prove2me | Definitions.Def_AdvMultiplayer_RowReader
-- name    : AdvMultiplayer_RowReader
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:56:05.467223+00:00
-- url     : https://prove2.me/theorems/a25b16a6-dc80-46d7-bbde-8df2260cb355
-- title:
--   Row readers
-- statement:
--   A row is read by inverse cumulative probabilities: the slot with probabilities $(1/2,1/4,1/4)$ for (DATA, DOWN, UP); the selected follower $k_t=1+\lfloor dV\rfloor$; the recorder source ($s_0=1/2$, $s_i=1/(2d)$); the injective tuple, where $R_{r,t}$ is the arm of rank $1+\lfloor(K-r)V\rfloor$ in the increasing list of unused arms; the pilots $P_{r,t}=1+\lfloor KV\rfloor$; the thinning and fast coordinates; the proposal bit, a threshold test at $h$; and the assignment coordinates.
--
--   Each read of a coordinate costs a tick.
-- source:
--   Gan, Square-Root Regret for Adversarial Multiplayer Bandits without Collision Information or Shared Randomness, arXiv:2610.05688, App. B.1, p.56

import Mathlib
import Definitions.Def_AdvMultiplayer_Table
import Definitions.Def_AdvMultiplayer_floorProg
import Definitions.Def_LNTopology_Hermetization_rlt
import Definitions.Def_LNTopology_Hermetization_rmul

open LNTopology.Hermetization

namespace AdvMultiplayer

variable (p : Size)

/-- The slot type `τ_t` (p.21). -/
inductive Slot
  | data
  | down
  | up
  deriving DecidableEq

/-- Fuel for a floor bounded by `K`. -/
def armFuel : ℕ := Nat.clog 2 (p.K + 1) + 1

/-- Fuel for a floor bounded by `D`. -/
def dFuel : ℕ := p.bN + 1

/-- Ticked read of `I_u(t)`. -/
noncomputable def idBit (d : TableData p) (u t : ℕ) : StateM ℕ Bool := do
  tick 1
  if h : u - 1 < p.A ∧ t - 1 < p.T then pure (d.1 ⟨u - 1, h.1⟩ ⟨t - 1, h.2⟩) else pure false

/-- Ticked read of `φ_q(u,t)`. -/
noncomputable def fwdBit (d : TableData p) (q u t : ℕ) : StateM ℕ Bool := do
  tick 1
  if h : q - 1 < p.M ∧ u - 1 < p.A ∧ t - 1 < p.T then
    pure (d.2.1 ⟨q - 1, h.1⟩ ⟨u - 1, h.2.1⟩ ⟨t - 1, h.2.2⟩)
  else pure false

/-- Ticked read of `V_{q,t,c}`. -/
noncomputable def scalarAt (d : TableData p) (q t : ℕ) (c : Coord p) : StateM ℕ ℝ := do
  tick 1
  if h : q - 1 < p.M ∧ t - 1 < p.T then pure (d.2.2.1 ⟨q - 1, h.1⟩ ⟨t - 1, h.2⟩ c) else pure 0

/-- Ticked read of the affine pair `(c, b)` of follower `i` in direction `dir`, charging the `B`
coefficients it reads. -/
noncomputable def affineAt (d : TableData p) (q t : ℕ) (dir : Bool) (i : ℕ) :
    StateM ℕ ((Fin p.Bmsg → Bool) × Bool) := do
  tick (p.Bmsg + 1)
  if h : q - 1 < p.M ∧ t - 1 < p.T ∧ i - 1 < p.d then
    pure (d.2.2.2 ⟨q - 1, h.1⟩ ⟨t - 1, h.2.1⟩ dir ⟨i - 1, h.2.2⟩)
  else pure (fun _ => false, false)

/-- **Row readers** (App. B.1, p.56): the slot by inverse CDF with probabilities
`(1/2, 1/4, 1/4)` for (DATA, DOWN, UP). Gan, arXiv:2610.05688.

The module holds the row readers of p.56: the selected follower, the recorder source (`s₀ = 1/2`,
`s_i = 1/(2d)`), the injective tuple, the pilots, the thinning coordinate, the proposal bit and the
assignment coordinates. Each read of a coordinate ticks, and floors are ticked searches. -/
noncomputable def readSlot (d : TableData p) (q t : ℕ) : StateM ℕ Slot := do
  let v ← scalarAt p d q t (cSlot p)
  let a ← rlt v (1 / 2)
  if a then pure Slot.data
  else
    let b ← rlt v (3 / 4)
    if b then pure Slot.down else pure Slot.up

/-- The selected follower `k_t = 1 + ⌊dV⌋ ∈ [d]`. -/
noncomputable def readSel (d : TableData p) (q t : ℕ) : StateM ℕ ℕ := do
  let v ← scalarAt p d q t (cSel p)
  let x ← rmul (p.d : ℝ) v
  let k ← floorProg (armFuel p) x
  pure (1 + k)

/-- The recorder source: `0` with probability `1/2`, follower `i` with probability `1/(2d)`. -/
noncomputable def readRec (d : TableData p) (q t : ℕ) : StateM ℕ ℕ := do
  let v ← scalarAt p d q t (cRec p)
  let a ← rlt v (1 / 2)
  if a then pure 0
  else
    let x ← rsub v (1 / 2)
    let y ← rmul (2 * (p.d : ℝ)) x
    let k ← floorProg (armFuel p) y
    pure (1 + k)

/-- The injective tuple `(R_{0,t}, …, R_{d,t})`: `R_{r,t}` is the arm of rank `1 + ⌊(K-r)V⌋` in the
increasing list of arms not yet taken (p.56). Label `0` means no such arm, which fails the arm-label
check. -/
noncomputable def readTuple (d : TableData p) (q t : ℕ) : StateM ℕ (ℕ → ℕ) := do
  let mut used : ℕ → Bool := fun _ => false
  let mut out : ℕ → ℕ := fun _ => 0
  for r in List.finRange p.m do
    tick 1
    let v ← scalarAt p d q t (cTuple p r)
    let x ← rmul ((p.K - r.val : ℕ) : ℝ) v
    let k ← floorProg (armFuel p) x
    let mut cnt : ℕ := 0
    let mut pick : ℕ := 0
    for a in List.range' 1 p.K do
      tick 1
      if !(used a) then
        cnt := cnt + 1
        if cnt = k + 1 then pick := a
    out := Function.update out r.val pick
    used := Function.update used pick true
  pure out

/-- The pilot `P_{r,t} = 1 + ⌊KV⌋` of player `r` (p.56). -/
noncomputable def readPilot (d : TableData p) (q t r : ℕ) : StateM ℕ ℕ := do
  if h : r < p.m then
    let v ← scalarAt p d q t (cPilot p ⟨r, h⟩)
    let x ← rmul (p.K : ℝ) v
    let k ← floorProg (armFuel p) x
    pure (1 + k)
  else pure 0

/-- The thinning coordinate `V_t`. -/
noncomputable def readThin (d : TableData p) (q t : ℕ) : StateM ℕ ℝ := scalarAt p d q t (cThin p)

/-- The fast-arm coordinate. -/
noncomputable def readFast (d : TableData p) (q t : ℕ) : StateM ℕ ℝ := scalarAt p d q t (cFast p)

/-- The proposal bit `B_t`: the threshold test `V_{prop} < h`. -/
noncomputable def readProp (d : TableData p) (q t : ℕ) : StateM ℕ Bool := do
  let v ← scalarAt p d q t (cProp p)
  rlt v (p.propOf p.eta)

/-- The assignment coordinate `assign_r`, `1 ≤ r ≤ K+1`. -/
noncomputable def readAssign (d : TableData p) (q t r : ℕ) : StateM ℕ ℝ := do
  if h : r - 1 < p.K + 1 then scalarAt p d q t (cAssign p ⟨r - 1, h⟩) else pure 0

end AdvMultiplayer


