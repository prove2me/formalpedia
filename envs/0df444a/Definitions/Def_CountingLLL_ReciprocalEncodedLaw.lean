-- Prove2me | Definitions.Def_CountingLLL_ReciprocalEncodedLaw
-- name    : CountingLLL_ReciprocalEncodedLaw
-- status  : Definition
-- author  : @wcysai
-- created : 2026-11-13T09:57:01.680013+00:00
-- url     : https://prove2.me/theorems/aadb7cc6-2d84-4ca4-8c65-3d681ef019f9
-- title:
--   Independent encoded entropy law for ReciprocalTest
-- statement:
--   Assign each tagged oracle, fair-bit and finite-uniform coordinate the natural-number encoding of its original marginal law, and take their independent product. This provides an independent encoded input law for the reveal-machine representation. Equality with the pushforward of the original entropy law is a separate theorem.
-- source:
--   Liu, Wang, Yin, Zhang and Zhou, A Counting and Sampling Lovász Local Lemma, STOC #442, Algorithm 6, pp. 27–28, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Definitions.Def_CountingLLL_ReciprocalReveal
set_option autoImplicit false

/-! Independent natural-number encoded entropy law for the reveal-machine
representation. Its relation to the original entropy law is a separate theorem. -/
namespace CountingLLL.ReciprocalTest
open MeasureTheory
open scoped ENNReal

def bitCode (b : Bool) : ℕ := if b then 1 else 0

noncomputable def readLaw (B : ℝ≥0∞) : ReadIndex → Measure ℕ
  | .inl _ => (oracleLaw B).map bitCode
  | .inr (.inl _) => fairLaw.map bitCode
  | .inr (.inr a) => (uniformLaw a.1).map (fun x => x.val)

noncomputable def encodedEntropyLaw (B : ℝ≥0∞) : Measure (ReadIndex → ℕ) :=
  Measure.infinitePi (readLaw B)
end CountingLLL.ReciprocalTest


