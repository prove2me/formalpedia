-- Prove2me | Definitions.Def_AdvMultiplayer_protocol
-- name    : AdvMultiplayer_protocol
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T21:05:52.430908+00:00
-- url     : https://prove2.me/theorems/9a1ad336-6a2d-484a-8038-584d22b8f095
-- title:
--   The protocol as a strategy profile
-- statement:
--   One round at a player has two parts: before the observation (Algorithm 6, lines 1-9) and after it. The observation is rounded down to a multiple of $1/D$ by the player. A player in the error state plays arm $i+1$. The protocol is the strategy obtained by folding these local steps over the player's own history and tape, with the table and $(m,K,T)$ as common knowledge; on the fallback flag, or off the construction branch, player $i$ plays arm $i+1$.
--
--   **Formalization Note.** The scalar constants of `Size` are functions of $(m,K,T)$ and enter as common knowledge; their computation is not charged.
-- source:
--   Gan, Square-Root Regret for Adversarial Multiplayer Bandits without Collision Information or Shared Randomness, arXiv:2610.05688, Algorithm 6, p.34; Algorithm 7, p.43; Algorithm 9 line 3

import Mathlib
import Definitions.Def_AdvMultiplayer_Strategy
import Definitions.Def_AdvMultiplayer_finishOrdinary
import Definitions.Def_AdvMultiplayer_bootAfter

open LNTopology.Hermetization

namespace AdvMultiplayer

variable (p : Size)

/-- Algorithm 6, lines 1–4 and 9, on an activated player outside `†`: the coordinator applies
`StartRound`, a follower applies the interruption, and the player chooses its arm by Algorithm 3. -/
noncomputable def chooseActive (d : TableData p) (i t : ℕ) (s : Local p) : Chk (ℕ × Local p) := do
  if i = 0 then
    let c1 ← startRound p d s.row t s.co
    let (a, c2) ← armCoordinator p d s.row t c1
    ensure (a ∈ Finset.Icc 1 p.K)
    pure (a, { s with co := c2 })
  else
    let f := s.fol
    let cut : Bool := decide (f.state = 1 ∨ f.state = 2) &&
      (decide (t = p.gridEnd (Size.gridOf p.eta) f.rc.σ) || f.lastProp)
    let f' := if cut then { f with state := 0 } else f
    let a ← armFollower p d s.row t i f'
    ensure (a ∈ Finset.Icc 1 p.K)
    pure (a, { s with fol := f' })

/-- **One player's start of round: Algorithm 6, lines 1–9, p.34.** Gan, arXiv:2610.05688, Section
5.4. A player that has not activated plays Algorithm 7's bootstrap arm; a player in `†` plays arm
`i + 1`; otherwise `chooseActive` runs, and a failed check enters `†` (App. A.1, p.51). The inputs are
the player's label, the round, its tape coordinates and its own registers, with the public table. -/
noncomputable def chooseProg (d : TableData p) (kd : RunKind) (i t : ℕ) (tape : Fin 4 → ℝ)
    (s : Local p) : StateM ℕ (ℕ × Local p) := do
  if !s.activated then
    if i = 0 then bootArmCoordinator p d kd t tape s else bootArmFollower p d t tape s
  else if s.dagger then
    pure (i + 1, s)
  else
    match ← (chooseActive p d i t s).run with
    | some x => pure x
    | none => pure (i + 1, { s with dagger := true })

/-- **One player's end of round.** Gan, arXiv:2610.05688, Algorithm 6, lines 6–7, 9–42: the raw
observation `y₀` is rounded down to a multiple of `1/D` (p.6) by the player, then the bootstrap update
or the ordinary operations run. A failed check enters `†`. -/
noncomputable def finishProg (d : TableData p) (md : Mode p) (i t a : ℕ) (y₀ : ℝ) (s : Local p) :
    StateM ℕ (Local p × Log p) := do
  let x ← rmul (p.D : ℝ) y₀
  let n ← floorProg (dFuel p) x
  let y ← rdiv (n : ℝ) (p.D : ℝ)
  if !s.activated then
    if i = 0 then
      let s' ← bootAfterCoordinator p d t a y s
      pure (s', Log.none p)
    else
      let s' ← bootAfterFollower p d md.kind t y s
      pure (s', Log.none p)
  else if s.dagger then
    pure (s, Log.none p)
  else
    match ← (finishOrdinary p d md i t a y s).run with
    | some x => pure x
    | none => pure ({ s with dagger := true }, Log.none p)

/-- The element of `Fin K` of arm label `a ∈ [K]`. -/
def armOf (a : ℕ) : Fin p.K :=
  ⟨(a - 1) % p.K, Nat.mod_lt _ (by have := p.m_lt_K; omega)⟩

/-- A player's tape coordinates in round `t`. -/
def tapeAt (tape : Tape p) (t : ℕ) : Fin 4 → ℝ :=
  if h : t - 1 < p.T then tape ⟨t - 1, h⟩ else fun _ => 0

/-- One local round, without the analysis report. -/
noncomputable def localRound (d : TableData p) (i t : ℕ) (tape : Tape p) (y : ℝ) (s : Local p) :
    Local p :=
  let ch := (chooseProg p d RunKind.actual i t (tapeAt p tape t) s).run' 0
  ((finishProg p d (Mode.actual p) i t ch.1 y ch.2).run' 0).1

/-- The player's registers after its own history: the local step folded over the observations. The
private registers are recomputed from the tape, so no other memory is needed. -/
noncomputable def replay (d : TableData p) (i : ℕ) (tape : Tape p) (h : History p) : Local p :=
  (h.zipIdx.foldl (fun s e => localRound p d i (e.2 + 1) tape e.1.2 s) (Local.init p))

/-- The fixed assignment of the fallback: player `i` plays arm `i + 1` (Algorithm 9, line 3; p.41). -/
def fallbackArm (i : Fin p.m) : Fin p.K := ⟨i.val, lt_trans i.isLt p.m_lt_K⟩

/-- **The protocol as a strategy profile of model (1).** Gan, arXiv:2610.05688: Algorithm 7's loop
(p.43) over Algorithm 6, the local step folded over the player's own history, plus the fixed-arm
fallback off the construction branch or on the fallback flag (Algorithm 9, line 3). The table and
`(m, K, T)` are common knowledge; the rest of the inputs are the player's own, as the type of
`Strategy` requires.

**Formalization Note.** The scalar constants of `Size` are functions of `(m, K, T)` and enter as
common knowledge (p.3); their computation is not charged. -/
noncomputable def protocol (tab : Table p) : Strategy p := fun i t h tape =>
  match tab with
  | Sum.inl _ => fallbackArm p i
  | Sum.inr d =>
    if p.branch then
      armOf p ((chooseProg p d RunKind.actual i.val t (tapeAt p tape t)
        (replay p d i.val tape h)).run' 0).1
    else fallbackArm p i

end AdvMultiplayer


