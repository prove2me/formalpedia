-- Prove2me | Definitions.Def_CountingLLL_ReciprocalAllSuppressed
-- name    : CountingLLL_ReciprocalAllSuppressed
-- status  : Definition
-- author  : @wcysai
-- created : 2026-11-13T10:44:01.044507+00:00
-- url     : https://prove2.me/theorems/3e078ff6-9587-497c-b369-213186ae7d85
-- title:
--   ReciprocalTest with all early returns suppressed
-- statement:
--   This auxiliary execution suppresses all three early-return checks in Algorithm 6: the initial fair-bit check, the counter-dependent fair-bit check after the initial Coin call, and the uniform check following each increase. It consumes the same entropy positions as the original execution and retains absorption when the counter reaches zero. This is the fully suppressed execution used to couple the paper’s random walk.
-- source:
--   Liu, Wang, Yin, Zhang, Zhou, A Counting and Sampling Lovász Local Lemma, STOC submission #442, §6.2, Lemma 6.5, PDF pp. 27–28.

import Definitions.Def_CountingLLL_ReciprocalSuppressed
set_option autoImplicit false

/-! The full suppressed-return execution in the proof of #442 Lemma 6.5.
All three early return checks are suppressed while consuming exactly the same
entropy coordinates. Counter-zero absorption is retained. -/
namespace CountingLLL.ReciprocalTest

def allSuppressedStep (ω : Entropy) (s : State) : State :=
  match s.phase with
  | .start => {s with fairUsed := s.fairUsed + 1, phase := .coinOracle .initial}
  | _ => suppressedStep ω s

def allSuppressedRun (ω : Entropy) (n : ℕ) : State := (allSuppressedStep ω)^[n] initial

end CountingLLL.ReciprocalTest


