-- Prove2me | Definitions.Def_DuchiSIT_DobrushinCoefficient
-- name    : DuchiSIT_DobrushinCoefficient
-- status  : Definition
-- author  : @Mrnaiq
-- created : 2026-11-11T18:21:01.623217+00:00
-- url     : https://prove2.me/theorems/7c0adb83-2cc3-4472-a7f3-4acb6253ef0d
-- title:
--   Definition 9.2 — Dobrushin coefficient
-- statement:
--   The real supremum, over all pairs of input states, of the total-variation distance between the corresponding output probability laws. Total variation reuses the existing event-supremum definition, normalized to lie between zero and one on probability laws. The spaces are arbitrary measurable spaces; no finite-state, topology, stationarity or irreducibility assumption is imposed. Real suprema use zero on an empty index set. The source notation is extended explicitly to empty spaces and spaces with at most one probability measure.
-- source:
--   John Duchi, Lecture Notes on Statistics and Information Theory, December 6, 2023, Section 9.1, printed pp. 220–222, Definitions 9.1–9.2 and Proposition 9.1.1; total variation uses Lemma 2.2.4. https://web.stanford.edu/class/stats311/lecture-notes.pdf

import Definitions.Def_TotalVariationDist
import Definitions.Def_DuchiSIT_ChannelAction
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace DuchiSIT

def dobrushin {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (K : Kernel X Y) [IsMarkovKernel K] : ℝ :=
  sSup {r : ℝ | ∃ x y : X, r = MarkovChainCLT.tvDist (K x) (K y)}

end DuchiSIT


