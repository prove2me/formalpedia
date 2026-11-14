-- Prove2me | Definitions.Def_CountingLLL_ReciprocalTransition
-- name    : CountingLLL_ReciprocalTransition
-- status  : Definition
-- author  : @wcysai
-- created : 2026-11-13T10:14:23.690177+00:00
-- url     : https://prove2.me/theorems/ca063504-36c3-430c-bf8d-d10fa8485e7d
-- title:
--   One-step transition masses for ReciprocalTest
-- statement:
--   For the operational ReciprocalTest state machine, assign a one-step mass from a state $s$ to $s'.$ If $s$ queries an entropy coordinate, this is the probability that its encoded value produces $s'.$ If $s$ is silent, the mass is one at its deterministic successor and zero elsewhere. The distribution recursion and long-run behavior are separate theorems.
-- source:
--   Liu, Wang, Yin, Zhang and Zhou, A Counting and Sampling Lovász Local Lemma, STOC #442, Algorithm 6, pp. 27–28, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Definitions.Def_CountingLLL_ReciprocalEncodedLaw
set_option autoImplicit false

/-! One-step transition masses for the operational ReciprocalTest machine.
Establishing the actual execution's distribution recursion and its long-run
behavior requires separate theorems. -/
namespace CountingLLL.ReciprocalTest
open MeasureTheory
open scoped ENNReal

noncomputable def transitionMass (B : ℝ≥0∞) (s s' : State) : ℝ≥0∞ := by
  classical
  exact match readIndex s with
  | some a => readLaw B a {v | step (uniformEntropy v) s = s'}
  | none => if step (uniformEntropy 0) s = s' then 1 else 0
end CountingLLL.ReciprocalTest


