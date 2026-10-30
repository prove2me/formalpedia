-- Prove2me | Definitions.Def_FreemiumActions_Threshold_Dynamics
-- name    : FreemiumActions_Threshold_Dynamics
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T08:58:09.757852+00:00
-- url     : https://prove2.me/theorems/55a875ed-59d6-47f6-9534-259b235cfdaa
-- title:
--   Player actions, transition probabilities, and the finite MDP
-- statement:
--   The player actions are monetize, take an incented action, and quit. The incented action is available only under the offer control and otherwise has probability zero. Conditional on monetization or an incented action, an interior state advances by one with probability $\tau_M$ or $\tau_I$, respectively, and otherwise stays. At $N$ either action stays with probability one. Quitting leads to the absorbing quit state.
--
--   The controlled transition matrix averages these action transitions with the corresponding $p$ or $q$ probabilities. Expected revenue is $p_M\mu_M+p_I\mu_I$ with an offer and $q_M\mu_M$ without one; it is zero at quit. These functions instantiate the published finite MDP with a point-mass initial law at any specified state. For a stationary policy, its transient matrix restricts the controlled transition to $E\times E$, using the chosen control at the row state. The initial-law field does not affect the conditional transition matrix. This realizes Assumption 2 and equations (4)–(6) without imposing any discount or time limit.
-- source:
--   Sheng, Ryan and Nagarajan, Incentivized actions in freemium games, supplied source.pdf dated October 8, 2016, §3.1–3.2, pp. 8–11 (PDF pp. 8–11), Assumption 2 and equations (3)–(6); catalog DOI 10.1287/msom.2020.0925.

import Definitions.Def_FreemiumActions_Threshold_Data
import Definitions.Def_DouyinDQ_Bias_FiniteMDP

namespace FreemiumActions.Threshold

inductive PlayerAction where
  | monetize | incented | quit
  deriving DecidableEq

instance : Fintype PlayerAction where
  elems := {.monetize, .incented, .quit}
  complete := by intro a; cases a <;> simp

def available (u : Bool) (a : PlayerAction) : Prop :=
  u = true ∨ a ≠ PlayerAction.incented

noncomputable def choice {N : ℕ} (d : Data N) (e : Level N)
    (u : Bool) : PlayerAction → ℝ
  | .monetize => if u then d.pM e else d.qM e
  | .incented => if u then d.pI e else 0
  | .quit => if u then d.pQ e else d.qQ e

noncomputable def actionTransition {N : ℕ} (d : Data N)
    (a : PlayerAction) (s t : State N) : ℝ :=
  match s, t with
  | none, none => 1
  | none, some _ => 0
  | some _, none => if a = .quit then 1 else 0
  | some e, some f =>
    if a = .quit then 0 else
    let tau := if a = .monetize then d.tauM else d.tauI
    if e = f then (if e.val = N then 1 else 1 - tau)
    else if f.val = e.val + 1 then tau else 0

noncomputable def transition {N : ℕ} (d : Data N)
    (u : Bool) (s t : State N) : ℝ :=
  match s with
  | none => if t = none then 1 else 0
  | some e => ∑ a : PlayerAction, choice d e u a * actionTransition d a s t

noncomputable def reward {N : ℕ} (d : Data N) (e : Level N) (u : Bool) : ℝ :=
  if u then d.pM e * d.muM + d.pI e * d.muI else d.qM e * d.muM

noncomputable def toMDP {N : ℕ} (d : Data N) (initial : State N) :
    DouyinDQ.Bias.MDP (State N) Bool where
  P := transition d
  r := fun s u => match s with
    | none => 0
    | some e => reward d e u
  ρ := fun s => if s = initial then 1 else 0

noncomputable def transient {N : ℕ} (d : Data N) (y : Policy N) :
    Matrix (Level N) (Level N) ℝ :=
  fun e f => (toMDP d (some e)).P (y e) (some e) (some f)

end FreemiumActions.Threshold


