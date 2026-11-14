-- Prove2me | Definitions.Def_CountingLLL_ReciprocalSuppressedReveal
-- name    : CountingLLL_ReciprocalSuppressedReveal
-- status  : Definition
-- author  : @wcysai
-- created : 2026-11-13T10:54:15.667355+00:00
-- url     : https://prove2.me/theorems/f0c1683f-6c07-4c27-b214-05c641bc1cac
-- title:
--   Reveal-machine encoding of the fully suppressed execution
-- statement:
--   This reveal-machine program executes the fully suppressed ReciprocalTest transitions using the same encoded oracle, fair-bit, and finite-uniform coordinates as the operational model. At a suppressed return check, the queried coordinate is conservatively marked as revealed even though its value cannot affect the transition. This bookkeeping permits later freshness and adaptive-law arguments.
-- source:
--   Liu, Wang, Yin, Zhang, Zhou, A Counting and Sampling Lovász Local Lemma, STOC submission #442, §6.2, Lemma 6.5; operational suppressed-return coupling.

import Definitions.Def_CountingLLL_ReciprocalAllSuppressed
import Definitions.Def_CountingLLL_ReciprocalReveal
set_option autoImplicit false

/-! Reveal-machine encoding of the fully suppressed operational execution.
The query positions at suppressed checks are still marked as revealed even
though the transition ignores their values. This conservative bookkeeping
preserves freshness of every later query. -/
namespace CountingLLL.ReciprocalTest
open CountingLLL.RevealMachine

def suppressedRevealProgram : Program State ReadIndex ℕ where
  query := readIndex
  read := fun s v => allSuppressedStep (uniformEntropy v) s
  silent := fun s => allSuppressedStep (uniformEntropy 0) s
end CountingLLL.ReciprocalTest


