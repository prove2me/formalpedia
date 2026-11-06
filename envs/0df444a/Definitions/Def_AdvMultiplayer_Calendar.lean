-- Prove2me | Definitions.Def_AdvMultiplayer_Calendar
-- name    : AdvMultiplayer_Calendar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T21:11:08.322617+00:00
-- url     : https://prove2.me/theorems/78b70c9d-ff9b-45d2-abf4-afcfac0e2206
-- title:
--   Calendar-round quantities
-- statement:
--   From the record of an execution the analysis defines the recorded arm $I_t$ of p.28: on enabled rounds, $I_t=j$ when the round is DATA, the selected source owns its played arm $j$, and the mask and thinning tests pass, with the tests of an unoccupied follower evaluated on its observation using the true assignment. This gives the raw arrivals, attributed to their calendar rounds, and by (11) the services $\Gamma_r$, queues $\mathsf B_r$ and scores $Z(r)=\sum_{s<r}\Gamma_s$, together with the physical overflow time $\tau_*^{\mathrm{phys}}$, the phases of a round, and the deferred law $\bar\nu_t$ of (39).
-- source:
--   Gan, Square-Root Regret for Adversarial Multiplayer Bandits without Collision Information or Shared Randomness, arXiv:2610.05688, Section 4.4, p.28; Section 5.1; p.36; (39); App. A.1 paragraph 1

import Mathlib
import Definitions.Def_AdvMultiplayer_Execution
import Definitions.Def_AdvMultiplayer_Learner

open LNTopology.Hermetization

namespace AdvMultiplayer

variable (p : Size)

/-- A trace: the record of each round of an execution. -/
abbrev Trace := ℕ → RoundRec p

/-- The coordinator's registers at round `t`, after `StartRound` and arm choice. -/
def coAt (X : Trace p) (t : ℕ) : Local p := (X t).mid (coordinator p)

/-- The row the coordinator uses. -/
def rowAt (X : Trace p) (t : ℕ) : ℕ := (coAt p X t).row

/-- The slot of the coordinator's row at round `t`. -/
noncomputable def slotAt (d : TableData p) (X : Trace p) (t : ℕ) : Slot :=
  (readSlot p d (rowAt p X t) t).run' 0

/-- The selected follower of the coordinator's row at round `t`. -/
noncomputable def selAt (d : TableData p) (X : Trace p) (t : ℕ) : ℕ :=
  (readSel p d (rowAt p X t) t).run' 0

/-- An assignment is live at round `t`: from its start until its cutoff (p.22). -/
def liveAt (X : Trace p) (t : ℕ) : Prop :=
  (coAt p X t).activated = true ∧ 0 < (coAt p X t).co.σ ∧ t < (coAt p X t).co.u

/-- Round `t` is in a collection: from the cutoff through the round before the next assignment
start (p.39). -/
def collAt (X : Trace p) (t : ℕ) : Prop :=
  (coAt p X t).activated = true ∧ 0 < (coAt p X t).co.σ ∧ (coAt p X t).co.u ≤ t

/-- Round `t` is a delivery round: live with a confirmation missing at arm choice (p.39). -/
def delivAt (X : Trace p) (t : ℕ) : Prop := liveAt p X t ∧ 0 < (coAt p X t).co.pcount

/-- Round `t` is a release round: live with all confirmations (p.39). -/
def relAt (X : Trace p) (t : ℕ) : Prop := liveAt p X t ∧ (coAt p X t).co.pcount = 0

/-- Round `t` is an assignment start. -/
def assignStartAt (X : Trace p) (t : ℕ) : Prop :=
  (coAt p X t).activated = true ∧ (coAt p X t).co.σ = t ∧ 1 ≤ t

/-- Round `t` is an episode start of the physical schedule: the first assignment, or an assignment
start at or after the previous grid boundary, which renews the anchor (Algorithm 5, line 10). -/
def episodeStartAt (X : Trace p) (t : ℕ) : Prop :=
  assignStartAt p X t ∧
    (((X t).pre (coordinator p)).co.σ = 0 ∨ ((X t).pre (coordinator p)).co.τbar ≤ t)

/-- Round `t` is enabled: score updates are not frozen (Section 4.4, p.27). -/
def enabledAt (X : Trace p) (t : ℕ) : Prop :=
  (coAt p X t).activated = true ∧ 0 < (coAt p X t).co.σ ∧ t < (coAt p X t).co.τbar

/-- The rounded observation `⌊Dy⌋/D` (p.6). -/
noncomputable def quant (y : ℝ) : ℝ := (⌊(p.D : ℝ) * y⌋₊ : ℝ) / (p.D : ℝ)

/-- A follower's label as a player. -/
def playerOf (i : ℕ) : Fin p.m := if h : i < p.m then ⟨i, h⟩ else coordinator p

/-- The recording probability `π_i(j)` of the owner of the played arm (p.27, p.28): `1` for an
occupied follower, `1/K` for an unoccupied follower or a pilot coordinator, and the fast-arm
probability for a fast coordinator. -/
noncomputable def ownerProb (X : Trace p) (t i : ℕ) : ℝ :=
  if i = 0 then
    (if (coAt p X t).co.fastNow then (coAt p X t).co.fastPi else 1 / (p.K : ℝ))
  else if ((X t).mid (playerOf p i)).fol.state = 0 then 1 / (p.K : ℝ) else 1

open Classical in
/-- **The recorded arm `I_t`** (p.28). Gan, arXiv:2610.05688, Section 4.4: on enabled rounds, `I_t = j`
when the round is DATA, the selected source owns its played arm `j`, and the mask and thinning tests of
Algorithm 4 pass; otherwise `⊥` (`none`). For an unoccupied follower these tests are evaluated with the
true assignment. The result names the source as well as the arm.

The module holds the calendar-round quantities of Section 5 and App. A.1 ¶1: arrivals, services,
queues `B_r`, scores `Z(r)`, weights, the physical overflow time and the deferred law. -/
noncomputable def recAt (d : TableData p) (X : Trace p) (t : ℕ) : Option (ℕ × Fin p.K) :=
    let c := (coAt p X t).co
    let q := rowAt p X t
    let i : ℕ := (readRec p d q t).run' 0
    let a := (X t).labels (playerOf p i)
    let owns : Prop := if i = 0 then (c.u ≤ t ∨ c.inU a = false) else (t < c.u ∧ a = c.slow i)
    let v : ℝ := (readThin p d q t).run' 0
    if enabledAt p X t ∧ slotAt p d X t = Slot.data ∧ owns ∧
        (maskProg p d q t i a).run' 0 = true ∧
        v ≤ c.xi a / ((1 / 2) * sourceProb p i * ownerProb p X t i * p.zeta) then
      some (i, armOf p a)
    else none

open Classical in
/-- The raw arrival `Δ_t(j)` attributed to its calendar round (App. A.1 ¶1, (38)). -/
noncomputable def calArrival (d : TableData p) (X : Trace p) (t : ℕ) (j : Fin p.K) : ℕ :=
  match recAt p d X t with
  | some (i, a) =>
    if a = j then
        arrivalOf p p.eta ((coAt p X t).co.xi (j.val + 1)) (quant p ((X t).obs (playerOf p i)))
      else 0
  | none => 0

/-- The calendar-round queue `B_t(j)` (11); `B_1 = 0`, unchanged on disabled rounds. -/
noncomputable def calQueue (d : TableData p) (X : Trace p) : ℕ → Fin p.K → ℕ
  | 0 => fun _ => 0
  | t + 1 => fun j => by
    classical exact
      if enabledAt p X t then queueNext (p.capOf p.eta) (calQueue d X t j) (calArrival p d X t j)
      else calQueue d X t j

open Classical in
/-- The calendar-round service `Γ_t(j)` (11), zero on disabled rounds. -/
noncomputable def calService (d : TableData p) (X : Trace p) (t : ℕ) (j : Fin p.K) : ℕ :=
    if enabledAt p X t then serviceOf (p.capOf p.eta) (calQueue p d X t j) (calArrival p d X t j)
    else 0

/-- The calendar-round score `Z_j(r) = Σ_{s<r} Γ_s(j)` (p.30). -/
noncomputable def calScore (d : TableData p) (X : Trace p) (r : ℕ) (j : Fin p.K) : ℕ :=
  ∑ s ∈ Finset.range r, calService p d X s j

/-- The calendar-round weights `w_{r,j} = (1+1/D)^{Z_j(r)}`. -/
noncomputable def calWeight (d : TableData p) (X : Trace p) (r : ℕ) (j : Fin p.K) : ℝ :=
  weightOf p (calScore p d X r j)

/-- The physical overflow time `τ_*^phys` (p.36), with `inf ∅ = +∞`. -/
noncomputable def tauPhys (d : TableData p) (X : Trace p) : ℕ∞ :=
  sInf ((fun s : ℕ => (s : ℕ∞)) ''
    {s | s ∈ Finset.Icc 1 p.T ∧
      ∃ j, Size.BcapOf p.eta < (calQueue p d X (s + 1) j : ℝ) / (p.eta * (p.D : ℝ))})

/-- The anchor in the coordinator's registers, as a function on `Fin K`. -/
def anchorAt (X : Trace p) (t : ℕ) : Fin p.K → ℝ := fun j => (coAt p X t).co.wbar (j.val + 1)

open Classical in
/-- The assigned physical slow set at round `t`. -/
def slowSetAt (X : Trace p) (t : ℕ) : Finset (Fin p.K) := by
  classical exact (Finset.range p.d).image fun i => armOf p ((coAt p X t).co.slow (i + 1))

open Classical in
/-- The deferred law `ν̄_t` (39), p.36, at an assignment start `t`, with `σ, u` the start and cutoff of
the preceding assignment. On a first start or `t ≥ τ̄(σ)` the renewed anchor is `w_t`. -/
noncomputable def nuBar (d : TableData p) (X : Trace p) (t : ℕ) (U : Finset (Fin p.K)) : ℝ :=
    let c0 := ((X t).pre (coordinator p)).co
    if c0.σ = 0 ∨ c0.τbar ≤ t then
      pw p (calWeight p d X t) (calWeight p d X t) U
    else
      nuLaw p p.eta (fun j => c0.wbar (j.val + 1)) (calWeight p d X t) (calWeight p d X c0.u)
        (calWeight p d X (c0.u - 1)) t c0.u U

end AdvMultiplayer


