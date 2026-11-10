-- Prove2me | Definitions.Def_GreedyColoringLCA969_LowerBound_RandomTape
-- name    : GreedyColoringLCA969_LowerBound_RandomTape
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T09:45:51.566617+00:00
-- url     : https://prove2.me/theorems/7d929be9-6949-4e3d-aa0b-5ad7813bf0ce
-- title:
--   The product law of independent fair binary bits
-- statement:
--   Each tape coordinate is a uniformly distributed Boolean value, and the complete tape law is their countable product:
--
--   $$\mathbb P=\bigotimes_{j\in\mathbb N}\operatorname{Uniform}(\{0,1\}).$$
--
--   This is the fixed randomness in Definition 2.6, including repeated and arbitrary-index reads. The law is a probability measure; it is not a supplied parameter that an algorithm could choose. Its product measurable structure supports the finite adaptive read operations.
--
--   Differences from the source:
--   - encoding: independent uniform binary coordinates → the infinite product of uniform Boolean probability measures; reason: this is exactly the specified shared random tape law
-- source:
--   Zi Song Yeoh, Krzysztof Onak, Dragos-Florian Ristache, STOC 2027 submission #969 (October 2026), Definition 2.6, p.8 (PDF 9); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/969.pdf

import Definitions.Def_GreedyColoringLCA969_LowerBound_Algorithm

open scoped ENNReal
open MeasureTheory
open Classical

namespace GreedyColoringLCA969.LowerBound

/-- Independent fair bits for the shared random-access tape. -/
noncomputable def fairBitLaw : MeasureTheory.Measure Bool :=
  (PMF.uniformOfFintype Bool).toMeasure

instance : MeasureTheory.IsProbabilityMeasure fairBitLaw := by
  unfold fairBitLaw
  infer_instance

noncomputable def tapeLaw : MeasureTheory.Measure Tape :=
  MeasureTheory.Measure.infinitePi (fun _ : ℕ => fairBitLaw)

instance : MeasureTheory.IsProbabilityMeasure tapeLaw := by
  unfold tapeLaw
  infer_instance

end GreedyColoringLCA969.LowerBound


