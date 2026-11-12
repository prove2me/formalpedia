-- Prove2me | Definitions.Def_DuchiSIT_ChannelAction
-- name    : DuchiSIT_ChannelAction
-- status  : Definition
-- author  : @Mrnaiq
-- created : 2026-11-11T18:20:41.768008+00:00
-- url     : https://prove2.me/theorems/3008e6e3-b06d-475c-9227-a6fe74a4a6d1
-- title:
--   Channel action on probability measures
-- statement:
--   The output probability law obtained by applying a Markov kernel to an input probability law. The underlying measure is the actual kernel–measure composition, with no extra normalization. The spaces are arbitrary measurable spaces; no finite-state, topology, stationarity or irreducibility assumption is imposed. Real suprema use zero on an empty index set. The source notation is extended explicitly to empty spaces and spaces with at most one probability measure.
-- source:
--   John Duchi, Lecture Notes on Statistics and Information Theory, December 6, 2023, Section 9.1, printed pp. 220–222, Definitions 9.1–9.2 and Proposition 9.1.1; total variation uses Lemma 2.2.4. https://web.stanford.edu/class/stats311/lecture-notes.pdf

import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.Kernel.Composition.MeasureComp
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace DuchiSIT

def channel {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (K : Kernel X Y) [IsMarkovKernel K] (μ : ProbabilityMeasure X) : ProbabilityMeasure Y :=
  ⟨K ∘ₘ (μ : Measure X), inferInstance⟩

end DuchiSIT


