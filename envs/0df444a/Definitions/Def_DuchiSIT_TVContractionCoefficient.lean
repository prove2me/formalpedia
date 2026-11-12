-- Prove2me | Definitions.Def_DuchiSIT_TVContractionCoefficient
-- name    : DuchiSIT_TVContractionCoefficient
-- status  : Definition
-- author  : @Mrnaiq
-- created : 2026-11-11T18:21:21.551195+00:00
-- url     : https://prove2.me/theorems/13032235-ec42-4f63-80b1-37042f8b7318
-- title:
--   Definition 9.1 — strong total-variation coefficient
-- statement:
--   The real supremum of output total-variation distance divided by input total-variation distance, over all distinct input probability laws. The same Markov kernel is applied to both laws. Distinct probability laws have positive total-variation distance. Real division is total in Lean; proving that the ratios are bounded is part of the formalization. The spaces are arbitrary measurable spaces; no finite-state, topology, stationarity or irreducibility assumption is imposed. Real suprema use zero on an empty index set. The source notation is extended explicitly to empty spaces and spaces with at most one probability measure.
-- source:
--   John Duchi, Lecture Notes on Statistics and Information Theory, December 6, 2023, Section 9.1, printed pp. 220–222, Definitions 9.1–9.2 and Proposition 9.1.1; total variation uses Lemma 2.2.4. https://web.stanford.edu/class/stats311/lecture-notes.pdf

import Definitions.Def_DuchiSIT_DobrushinCoefficient
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace DuchiSIT

def tvContraction {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (K : Kernel X Y) [IsMarkovKernel K] : ℝ :=
  sSup {r : ℝ | ∃ μ ν : ProbabilityMeasure X, μ ≠ ν ∧
    r = MarkovChainCLT.tvDist (channel K μ : Measure Y) (channel K ν : Measure Y) /
      MarkovChainCLT.tvDist (μ : Measure X) (ν : Measure X)}

end DuchiSIT


