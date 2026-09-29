-- Prove2me | Definitions.Def_EthierKurtz_spinFlipGraph
-- name    : EthierKurtz_spinFlipGraph
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T06:41:54.668055+00:00
-- url     : https://prove2.me/theorems/533eed6a-d013-44d8-acc3-d4495243194d
-- title:
--   Spin-flip generator graph
-- statement:
--   The graph of the spin-flip operator on the full domain of continuous observables with summable coordinate variations, with continuous output equal pointwise to the countable rate-weighted flip series.
-- source:
--   Stewart N. Ethier and Thomas G. Kurtz, Markov Processes: Characterization and Convergence, Wiley, 1986, Chapter 8, Section 3, equation (3.25) and Theorem 3.5, printed p. 381 (PDF p. 390).

import Definitions.Def_EthierKurtz_spinVariation

open Filter
open scoped Topology BigOperators

namespace EthierKurtz

/-- Equation (3.25) on the full summable-variation domain, before closure.
The output is a continuous function equal to the actual pointwise series. -/
def spinFlipGraph {S : Type*} (c : S → C(S → Bool, ℝ)) :
    Set (C(S → Bool, ℝ) × C(S → Bool, ℝ)) :=
  {fg | Summable (spinVariation fg.1) ∧
    ∀ η, fg.2 η = ∑' i, c i η * (fg.1 (spinFlip i η) - fg.1 η)}

end EthierKurtz


