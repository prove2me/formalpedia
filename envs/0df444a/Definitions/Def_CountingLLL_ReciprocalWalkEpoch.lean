-- Prove2me | Definitions.Def_CountingLLL_ReciprocalWalkEpoch
-- name    : CountingLLL_ReciprocalWalkEpoch
-- status  : Definition
-- author  : @wcysai
-- created : 2026-11-13T10:51:34.46575+00:00
-- url     : https://prove2.me/theorems/a9dcc07f-7f9f-4881-a757-591bdcfb0d39
-- title:
--   Counter-change epochs and directions of the fully suppressed run
-- statement:
--   Starting from a prescribed time in the fully suppressed operational execution, define each successive change epoch as the first later step at which the first counter changes, and record whether that change is an increase by two. At zero, or if no later change exists, the epoch is held fixed. The definition makes no claim that nonzero states eventually change; the coupling theorem states that property as an explicit hypothesis.
-- source:
--   Liu, Wang, Yin, Zhang, Zhou, A Counting and Sampling Lovász Local Lemma, STOC submission #442, §6.2, Lemma 6.5, PDF p. 28, contraction of iterations that leave the counters unchanged.

import Definitions.Def_CountingLLL_ReciprocalAllSuppressed
import Definitions.Def_CountingLLL_ContractedWalk
set_option autoImplicit false

/-! Deterministically erase all atomic steps that do not change the first
counter of the fully suppressed execution. If a nonzero counter never changes
again, the epoch is held fixed; a separate theorem supplies any needed
almost-sure nonsticking assumption. -/
namespace CountingLLL.ReciprocalTest

noncomputable def nextChangeTime (ω : Entropy) (t : ℕ) : ℕ := by
  classical
  exact if (allSuppressedRun ω t).i = 0 then t else
    if h : ∃ k, t < k ∧ (allSuppressedRun ω k).i ≠ (allSuppressedRun ω t).i then Nat.find h else t

noncomputable def changeEpoch (ω : Entropy) (start : ℕ) : ℕ → ℕ
  | 0 => start
  | n+1 => nextChangeTime ω (changeEpoch ω start n)

noncomputable def changeDirection (ω : Entropy) (start n : ℕ) : Bool := by
  classical
  exact if (allSuppressedRun ω (changeEpoch ω start (n+1))).i =
      (allSuppressedRun ω (changeEpoch ω start n)).i + 2 then true else false

end CountingLLL.ReciprocalTest


