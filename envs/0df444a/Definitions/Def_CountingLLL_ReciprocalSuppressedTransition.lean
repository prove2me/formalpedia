-- Prove2me | Definitions.Def_CountingLLL_ReciprocalSuppressedTransition
-- name    : CountingLLL_ReciprocalSuppressedTransition
-- status  : Definition
-- author  : @wcysai
-- created : 2026-11-13T10:57:22.148761+00:00
-- url     : https://prove2.me/theorems/e66e8d2d-2ba9-483b-8ffc-fd10d34fcfa2
-- title:
--   Transition mass for the fully suppressed ReciprocalTest
-- statement:
--   For each pair of states, this definition assigns the probability mass that one atomic step of the fully suppressed ReciprocalTest changes the first state to the second, using the appropriate encoded entropy-coordinate law. A separate theorem establishes its conditional meaning for the actual adaptive execution.
-- source:
--   Liu, Wang, Yin, Zhang, Zhou, A Counting and Sampling Lovász Local Lemma, STOC submission #442, §6.2, Lemma 6.5; operational suppressed-walk transition model.

import Definitions.Def_CountingLLL_ReciprocalEncodedLaw
import Definitions.Def_CountingLLL_ReciprocalSuppressedReveal
set_option autoImplicit false

/-! One-step transition masses for the fully suppressed ReciprocalTest execution. -/
namespace CountingLLL.ReciprocalTest
open MeasureTheory
open scoped ENNReal

noncomputable def suppressedTransitionMass (B : ℝ≥0∞) (s s' : State) : ℝ≥0∞ := by
  classical
  exact match readIndex s with
  | some a => readLaw B a {v | allSuppressedStep (uniformEntropy v) s = s'}
  | none => if allSuppressedStep (uniformEntropy 0) s = s' then 1 else 0
end CountingLLL.ReciprocalTest


