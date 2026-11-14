-- Prove2me | Definitions.Def_CountingLLL_ReciprocalSuppressed
-- name    : CountingLLL_ReciprocalSuppressed
-- status  : Definition
-- author  : @wcysai
-- created : 2026-11-13T10:38:56.710891+00:00
-- url     : https://prove2.me/theorems/75a0fc9e-2db0-46b7-bc7d-e5f2f78643e8
-- title:
--   ReciprocalTest with return checks suppressed
-- statement:
--   This auxiliary small-step execution modifies the operational ReciprocalTest program by suppressing its initial counter-dependent return check and each later uniform return check. It advances the same entropy counters at those checks and otherwise uses the original transition on the same entropy tape. The original first fair-bit return and absorption at counter zero remain in place. A separate theorem establishes its pathwise relationship to the real program.
-- source:
--   Liu, Wang, Yin, Zhang, Zhou, A Counting and Sampling Lovász Local Lemma, STOC submission #442, §6.2, Lemma 6.5, random-walk proof. This is an auxiliary execution for formalizing the paper’s suppressed-return coupling.

import Definitions.Def_CountingLLL_ReciprocalTest
set_option autoImplicit false

/-! The coupled execution of Algorithm 6 with the initial and per-upstep
return checks suppressed. It consumes the same entropy coordinates as the
original machine and agrees with it until one of those checks would return true.
The original first fair-bit return and absorption at i = 0 are retained. -/
namespace CountingLLL.ReciprocalTest

def suppressedStep (ω : Entropy) (s : State) : State :=
  match s.phase with
  | .initialCheck => {s with fairUsed := s.fairUsed + 1, phase := .loop}
  | .uniformCheck => {s with uniformUsed := s.uniformUsed + 1, phase := .loop}
  | _ => step ω s

def suppressedRun (ω : Entropy) (n : ℕ) : State := (suppressedStep ω)^[n] initial

end CountingLLL.ReciprocalTest


