-- Prove2me | Definitions.Def_DevContest_pcsd
-- name    : DevContest_pcsd
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:51:04.97099+00:00
-- url     : https://prove2.me/theorems/41aab91b-c5a4-4232-8e74-b6b006c75818
-- title:
--   The policy PCSD and its equilibrium strategies
-- statement:
--   **PCSD** uses one uniform draw $V\in[0,1]$ and a public message. If the first success of the contest arrives at $s$, it is disclosed at that instant when $V<\phi^*_s$, so with probability $\phi^*_s$; the message then names the first mover and $s$ from that date on. A first success that is not disclosed at its arrival is never disclosed later, and the rival's later first success is not disclosed.
--
--   The **equilibrium strategy** of an agent is effort $0$ at $t$ if she has no success by $t$ and the message at $t$ names her rival, and full effort otherwise.
--
--   Thus an agent with no success works until her first success, or the end of the contest, or the disclosure of her opponent's progress, and an agent with one success works until the end. This is the object of the mission's goal.
--
--   **Formalization Note** The strict inequality makes the silent phase, where $\phi^*=0$, silent for every draw. Only the first success is disclosed, which is the reading of "any change in the state of partial progress": §5.3 ties the commitment to the arrival of the first success.
-- source:
--   Khorasani, Körpeoğlu, Krishnan, Dynamic Development Contests, author manuscript, §5.3, p.21; Theorem 2, p.22

import Mathlib
import Definitions.Def_DevContest_Policy
import Definitions.Def_DevContest_pcsdBelief

open scoped ENNReal NNReal
open MeasureTheory

namespace DevContest

/-- The agent who obtained the first success in the contest and its date, and `none` if nobody has
a success yet or the two dates tie. -/
noncomputable def firstMover (r : Rec) : Option (Fin 2 × ℝ≥0∞) :=
  if r 0 < r 1 then some (0, r 0) else if r 1 < r 0 then some (1, r 1) else none

/-- The public message of PCSD at time `t`, Khorasani, Körpeoğlu, Krishnan, *Dynamic Development
Contests*, author manuscript, §5.3, p.21, and Theorem 2, p.22: it names the first mover and the date
`s` of her success once that success has been disclosed. A first success at `s` is disclosed, at
the instant it arrives, when the uniform draw `u` lies below `φ*_s`, so with probability `φ*_s`; and
it is never disclosed later.

**Formalization Note.** Only the first success is disclosed (reading of "any change in the state of
partial progress", p.21). The inequality is strict, so that nothing at all is disclosed when
`φ*_s = 0`, which is the silent phase. -/
noncomputable def pcsdMsg (lam c Rbar : ℝ) (t : ℝ≥0) (r : Rec) (u : unitInterval) :
    Option (Fin 2 × ℝ≥0∞) :=
  match firstMover (trunc t r) with
  | some (l, s) => if (u : ℝ) < phiStar lam c Rbar s.toReal then some (l, s) else none
  | none => none

/-- The policy PCSD, §5.3, p.21, and Theorem 2, p.22, with the probabilities `φ*_t` of
`phiStar`. The randomization is one uniform draw and the message is public. -/
noncomputable def pcsd (lam c Rbar : ℝ) : Policy unitInterval (Option (Fin 2 × ℝ≥0∞)) where
  ν := volume
  isProb := inferInstance
  sig t r u _ := pcsdMsg lam c Rbar t r u
  nonanticipating t r u _ := by
    have h : trunc t (trunc t r) = trunc t r := by
      funext i
      by_cases hr : r i ≤ (t : ℝ≥0∞) <;> simp [trunc, hr]
    simp only [pcsdMsg, h]

/-- The equilibrium strategy of Theorem 2 (Equilibrium), p.22: effort `0` if the agent has no success
by `t` and the message at `t` names her rival, and full effort otherwise. Thus an agent with no
success works until her own success, the rival's completion, or the disclosure of the rival's
progress, and an agent with one success works until the end. -/
noncomputable def pcsdEffort (lam c Rbar : ℝ) : Fin 2 → Strategy unitInterval :=
  fun i t r u =>
    open Classical in
    if ¬ r i ≤ (t : ℝ≥0∞) ∧ ∃ s, pcsdMsg lam c Rbar t r u = some (rival i, s) then 0 else 1

end DevContest


