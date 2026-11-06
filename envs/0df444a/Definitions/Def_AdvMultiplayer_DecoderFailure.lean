-- Prove2me | Definitions.Def_AdvMultiplayer_DecoderFailure
-- name    : AdvMultiplayer_DecoderFailure
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T21:13:40.752766+00:00
-- url     : https://prove2.me/theorems/b52e5a51-dbb7-488f-8ff6-8b614406771b
-- title:
--   Decoder failures and transfer charges
-- statement:
--   A decoder failure at a decision is either a completed batch with a unique solution different from the word currently encoded on its channel that passes the acceptance test (35), or a completed batch formed entirely from one fixed awaited word with multiple solutions. $\tau_{\mathrm{bad}}$ is the first decoder failure or queue-overflow update, or $T+1$. With $g_t$ the number of arms of positive rounded reward and $\bar g_t=\min\{m,g_t\}$, a transfer's charge is
--   $$J_s=\sum_{t\in\mathcal C\cup\mathcal D}\bar g_t+\sum_{t\in\mathcal R}\Big(r_t(U_t)+r_t(X_t)-\sum_{i=0}^dY_{i,t}\Big),$$
--   over its collection, delivery and release phases truncated after $\tau_{\mathrm{bad}}$. $J_{\mathrm{stop}}$ is the same sum over all transfers.
-- source:
--   Gan, Square-Root Regret for Adversarial Multiplayer Bandits without Collision Information or Shared Randomness, arXiv:2610.05688, Section 4.1, p.21; App. A.2; Section 5.6, (41), pp.39-40

import Mathlib
import Definitions.Def_AdvMultiplayer_Calendar

namespace AdvMultiplayer

variable (p : Size)

/-- The word `w` passes the acceptance test (35), p.32, on channel `(dir, k)` at round `t`:
`Acc^DOWN` with `σ_k < M.σ ≤ t`, or `Acc^UP` with `u ≤ t`, `k ∈ P`, `M.σ = σ`. -/
def passesAcc (X : Trace p) (dir : Bool) (k t : ℕ) (w : Word p) : Prop :=
  if dir then
    ∃ M, parseUp p w = some M ∧ (coAt p X t).co.u ≤ t ∧ (coAt p X t).co.P k = true ∧
      M.σ = (coAt p X t).co.σ
  else
    ∃ M, parseDown p w = some M ∧ ((X t).mid (playerOf p k)).fol.rc.σ < M.σ ∧ M.σ ≤ t

/-- The receiver runs `DecodeStep` on channel `(dir, k)` at round `t`: an activated follower `k`
unoccupied at arm choice, or the coordinator during collection with `k ∈ P`. -/
def receiverRuns (X : Trace p) (dir : Bool) (k t : ℕ) : Prop :=
  if dir then collAt p X t ∧ (coAt p X t).co.P k = true
  else ((X t).mid (playerOf p k)).activated = true ∧ ((X t).mid (playerOf p k)).fol.state = 0

/-- `w` is awaited on channel `(dir, k)` during the rounds `s, …, t` (p.21): the sender encodes it,
the receiver runs `DecodeStep`, and it satisfies (35). -/
def Awaited (X : Trace p) (dir : Bool) (k : ℕ) (w : Word p) (s t : ℕ) : Prop :=
  ∀ v ∈ Finset.Icc s t, curWord p (X v).mid dir k = some w ∧ receiverRuns p X dir k v ∧
    passesAcc p X dir k v w

/-- A completed batch at round `t`, on channel `(dir, k)`. -/
def batchAt (X : Trace p) (t : ℕ) (dir : Bool) (k : ℕ) (W : Batch p) : Prop :=
  ∃ i sol, ((X t).logs i).decided = some (dir, k, W, sol)

/-- `E_false` at round `t` (p.45, App. A.2): a completed batch has a unique solution, different from
the word currently encoded on its channel, that passes (35). -/
def falseDecode (X : Trace p) (t : ℕ) : Prop :=
  ∃ dir k W w, batchAt p X t dir k W ∧ solutions p W = {w} ∧
    curWord p (X t).mid dir k ≠ some w ∧ passesAcc p X dir k t w

/-- `E_amb` at round `t` (App. A.2): a completed batch formed entirely from one fixed awaited word has
multiple solutions. -/
def ambiguousDecode (X : Trace p) (t : ℕ) : Prop :=
  ∃ dir k W w, batchAt p X t dir k W ∧ (∀ e ∈ W, Awaited p X dir k w e.rnd t) ∧
    ¬ (solutions p W).Subsingleton

/-- **A decoder failure at round `t`** (p.21): either excluded batch event of Lemma 7. Gan,
arXiv:2610.05688, Section 4.1 and App. A.2. -/
def decoderFailure (X : Trace p) (t : ℕ) : Prop := falseDecode p X t ∨ ambiguousDecode p X t

/-- Round `t` is a positive receiver observation on channel `(dir, k)`: the round selects the channel
and the receiver's rounded observation is positive. -/
noncomputable def positiveAt (d : TableData p) (X : Trace p) (dir : Bool) (k t : ℕ) : Prop :=
  slotAt p d X t = (if dir then Slot.up else Slot.down) ∧ selAt p d X t = k ∧
    0 < quant p ((X t).obs (if dir then coordinator p else playerOf p k))

open Classical in
/-- The number of positive receiver observations on a channel during the rounds `s, …, t`. -/
noncomputable def positiveCount (d : TableData p) (X : Trace p) (dir : Bool) (k s t : ℕ) : ℕ := by
  classical exact ((Finset.Icc s t).filter (fun v => positiveAt p d X dir k v)).card

/-- The first decoder failure or first queue-overflow update, with value `T+1` if neither occurs
(`τ_bad`, p.40). -/
noncomputable def tauBad (d : TableData p) (X : Trace p) : ℕ :=
  sInf {t | t = p.T + 1 ∨ (t ∈ Finset.Icc 1 p.T ∧
    (decoderFailure p X t ∨ (t : ℕ∞) = tauPhys p d X))}

open Classical in
/-- `g_t = #{a : r_t(a) > 0}` (p.5). -/
noncomputable def gSupport (r : Rewards p) (t : ℕ) : ℕ := by
  classical exact (Finset.univ.filter fun a => 0 < r t a).card

/-- `ḡ_t = min{m, g_t}` (p.5). -/
noncomputable def gCap (r : Rewards p) (t : ℕ) : ℕ := min p.m (gSupport p r t)

open Classical in
/-- The per-round charge of (41), p.39, in the rounded rewards: `ḡ_t` on collection and delivery
rounds, and `r_t(U_t) + r_t(X_t) - Σ_i Y_{i,t}` on release rounds, with `X_t` the coordinator's fast
arm. -/
noncomputable def charge (r : Rewards p) (X : Trace p) (t : ℕ) : ℝ :=
    if collAt p X t ∨ delivAt p X t then (gCap p r t : ℝ)
    else if relAt p X t then
      setReward p r t (slowSetAt p X t) + r t ((X t).arms (coordinator p)) - ∑ i, (X t).obs i
    else 0

/-- Round `t` starts a transfer: the first assignment, or a cutoff (p.39). -/
def transferStartAt (X : Trace p) (t : ℕ) : Prop :=
  1 ≤ t ∧ t ≤ p.T ∧
    ((assignStartAt p X t ∧ ((X t).pre (coordinator p)).co.σ = 0) ∨
      ((coAt p X t).activated = true ∧ (coAt p X t).co.u = t))

/-- The next transfer start after `s`, or `T+1`. -/
noncomputable def nextTransfer (X : Trace p) (s : ℕ) : ℕ :=
  sInf {t | s < t ∧ (t = p.T + 1 ∨ transferStartAt p X t)}

/-- The stopped transfer charge `J_s` (41), p.39: the phases of the transfer started at `s`, truncated
immediately after `τ_bad`, including that round, or at the horizon. -/
noncomputable def Jcharge (d : TableData p) (r : Rewards p) (X : Trace p) (s : ℕ) : ℝ :=
  ∑ t ∈ (Finset.Ico s (nextTransfer p X s)) ∩ Finset.Icc 1 (min (tauBad p d X) p.T), charge p r X t

/-- The total stopped charge `J_stop` of Prop. 21, p.40: the disjoint union of the stopped phases of
all transfers, from launch through `min{τ_bad, T}`. -/
noncomputable def Jstop (d : TableData p) (r : Rewards p) (X : Trace p) : ℝ :=
  ∑ t ∈ Finset.Icc 1 (min (tauBad p d X) p.T), charge p r X t

end AdvMultiplayer


