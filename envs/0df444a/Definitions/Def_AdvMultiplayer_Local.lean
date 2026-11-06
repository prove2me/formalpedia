-- Prove2me | Definitions.Def_AdvMultiplayer_Local
-- name    : AdvMultiplayer_Local
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:54:57.711394+00:00
-- url     : https://prove2.me/theorems/13e73cd6-90b4-48f3-9a85-490afa142894
-- title:
--   The local state of a player
-- statement:
--   A player's state consists of the absorbing error flag $\dagger$, its activation flag, its selected or declared row, its bootstrap registers, and its ordinary registers. A follower keeps gain weights, block draws, a gain counter, a pending declaration and candidate counts before activation; afterwards it keeps its last accepted DOWN record, the served sum $S_i$, last service $\delta_i$, queue $b_i$, state (unoccupied, pending, released), candidate list and DOWN batch. The coordinator keeps its target, list $\Lambda$ and counters before launch; afterwards it keeps $\sigma,u,\bar\tau$, the set $\mathcal P$, scores, queues, the anchor and rates, the assignment, the raw buffer and the UP batches.
--
--   The module also fixes what an execution is: the actual one, or the analysis's reference one, with $J$ drawn or fixed.
--
--   **Formalization Note.** A checked operation runs in an option monad: a failure enters $\dagger$, and ticks already charged persist. The analysis report `Log` is not read by the strategy.
-- source:
--   Gan, Square-Root Regret for Adversarial Multiplayer Bandits without Collision Information or Shared Randomness, arXiv:2610.05688, Algorithms 3-7, 10; Section 5.2, p.31; App. A.1

import Mathlib
import Definitions.Def_AdvMultiplayer_Size
import Definitions.Def_AdvMultiplayer_Channel

namespace AdvMultiplayer

/-- A saved candidate observation `(s, j, y, v)` of a follower's list `ℬ_i` (p.32). -/
structure CandRec where
  s : ℕ
  j : ℕ
  y : ℝ
  v : ℝ

/-- A follower's bootstrap registers (Algorithm 7, Algorithm 10, pp.42–43, 59): gain weights
`w_i^boot`, the block's activity flag, held arm `a` with its probability `p_i(a)`, index `ι`, gain
counter `G`, pending declaration, and the candidate counts `n_v` and flags `dead_v`. -/
structure BootF where
  bw : ℕ → ℝ
  active : Bool
  held : ℕ
  pheld : ℝ
  iota : ℕ
  G : ℕ
  pending : Option ℕ
  nv : ℕ → ℕ
  dead : ℕ → Bool

/-- The coordinator's bootstrap registers (Algorithm 7): the block target `z`, the list `Λ`, the
MULTICAST flag and the cumulative DOWN counters `C_r(a)`. -/
structure BootC where
  target : ℕ
  lam : List ℕ
  multicast : Bool
  cnt : ℕ → ℕ

/-- A follower's ordinary registers (p.31): the last accepted DOWN record, `S_i`, `δ_i`, `b_i`,
`state_i ∈ {0,1,2}` (unoccupied, pending, released), the candidate list `ℬ_i`, the DOWN batch, and the
proposal bit read after the last update (Algorithm 6, line 41). -/
structure Fol (p : Size) where
  rc : DownRec
  S : ℕ
  δ : ℕ
  b : ℕ
  state : ℕ
  cand : List CandRec
  batch : Batch p
  lastProp : Bool

/-- The coordinator's ordinary registers (Algorithms 3, 5, 6, pp.23, 30, 34): `σ`, `u`, `τ̄`, the set
`P` (with its size), scores `z`, queues, the known-queue flags, working last services and the saved
`Γ_{u-1}`, the accumulator `c`, the anchor `w̄`, the rates `ξ_j = 2^{-h_j}`, the slow arms and their
base scores, the auxiliary arm `e`, the DOWN records, the raw buffer (with its entry count), the UP
batches, the last proposal bit, and the current fast draw's status and probability. Arrays are indexed
by arm label or follower label. -/
structure Co (p : Size) where
  σ : ℕ
  u : ℕ
  τbar : ℕ
  P : ℕ → Bool
  pcount : ℕ
  z : ℕ → ℕ
  Bq : ℕ → ℕ
  known : ℕ → Bool
  last : ℕ → ℕ
  gamU : ℕ → ℕ
  acc : ℕ → ℕ
  wbar : ℕ → ℝ
  hexp : ℕ → ℕ
  xi : ℕ → ℝ
  slow : ℕ → ℕ
  inU : ℕ → Bool
  aux : ℕ
  base : ℕ → ℕ
  msg : ℕ → DownRec
  buf : ℕ → ℕ → ℕ
  bufCount : ℕ
  upBatch : ℕ → Batch p
  lastBit : Bool
  fastNow : Bool
  fastPi : ℝ

/-- **The local state of one player.** Gan, arXiv:2610.05688, Algorithms 3–7 and 10, App. A.1: the
absorbing error flag `†`, the activation flag, the selected or declared row, and the registers of the
two stages. It holds only that player's registers. A follower uses `bf` and `fol`; the coordinator uses
`bc` and `co`. -/
structure Local (p : Size) where
  dagger : Bool
  activated : Bool
  row : ℕ
  bf : BootF
  bc : BootC
  fol : Fol p
  co : Co p

/-- The initial state (Algorithm 7, line 1; p.31; Algorithm 5): gain weights one, `σ = 0`,
`τ̄ = T+1`, all other registers zero or empty. -/
def Local.init (p : Size) : Local p where
  dagger := false
  activated := false
  row := 0
  bf := ⟨fun _ => 1, false, 0, 0, 0, 0, none, fun _ => 0, fun _ => false⟩
  bc := ⟨0, [], false, fun _ => 0⟩
  fol := ⟨⟨0, 0, 0, 0, 0⟩, 0, 0, 0, 0, [], [], false⟩
  co :=
    { σ := 0, u := p.T + 1, τbar := p.T + 1, P := fun _ => false, pcount := 0, z := fun _ => 0,
      Bq := fun _ => 0, known := fun _ => false, last := fun _ => 0, gamU := fun _ => 0,
      acc := fun _ => 0, wbar := fun _ => 1, hexp := fun _ => 0, xi := fun _ => 0,
      slow := fun _ => 0, inU := fun _ => false, aux := 0, base := fun _ => 0,
      msg := fun _ => ⟨0, 0, 0, 0, 0⟩, buf := fun _ _ => 0, bufCount := 0,
      upBatch := fun _ => [], lastBit := false, fastNow := false, fastPi := 0 }

instance (p : Size) : Inhabited (Local p) := ⟨Local.init p⟩

/-- What an execution is: the row is drawn by the coordinator (`none`) or fixed at `J = j`, and the
execution is the actual one or the reference one (Algorithm 8, p.44). -/
structure RunKind where
  forceRow : Option ℕ
  reference : Bool

/-- The actual execution of the strategy. -/
def RunKind.actual : RunKind := ⟨none, false⟩

/-- The information a local step receives from its execution. In the actual execution it is
`RunKind.actual` and no word; only the reference execution, an analysis object, reads `cur`, which
gives the word currently encoded on each channel (`false` = DOWN, `true` = UP; p.20). -/
structure Mode (p : Size) where
  kind : RunKind
  cur : Bool → ℕ → Option (Word p)

/-- The mode of the actual execution. -/
def Mode.actual (p : Size) : Mode p := ⟨RunKind.actual, fun _ _ => none⟩

/-- What one local step reports to the analysis: a decoder decision (direction, follower, completed
batch, unique solution), the word it accepted, and whether the reference filter rejected a word that
passed (35). The strategy ignores it. -/
structure Log (p : Size) where
  decided : Option (Bool × ℕ × Batch p × Option (Word p))
  accepted : Option (Word p)
  filtered : Bool

/-- The empty report. -/
def Log.none (p : Size) : Log p := ⟨Option.none, Option.none, false⟩

instance (p : Size) : Inhabited (Log p) := ⟨Log.none p⟩

/-- A checked operation: a failure enters `†` (App. A.1, p.51). Ticks already charged persist. -/
abbrev Chk := OptionT (StateM ℕ)

/-- The check of a condition on registers. -/
def ensure (b : Prop) [Decidable b] : Chk Unit := if b then pure () else failure

end AdvMultiplayer


