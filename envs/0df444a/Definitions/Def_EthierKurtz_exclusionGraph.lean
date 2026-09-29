-- Prove2me | Definitions.Def_EthierKurtz_exclusionGraph
-- name    : EthierKurtz_exclusionGraph
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T06:59:25.809327+00:00
-- url     : https://prove2.me/theorems/94ca98bd-5c74-49c7-a678-822cbdf8b303
-- title:
--   Weighted exclusion generator graph
-- statement:
--   The graph of the exclusion operator on the full domain where the ordered-pair sum of gamma-weighted two-site variations is summable, with continuous output equal pointwise to the countable rate-weighted exchange series.
-- source:
--   Stewart N. Ethier and Thomas G. Kurtz, Markov Processes: Characterization and Convergence, Wiley, 1986, Chapter 8, Section 3, equation (3.29) and Theorem 3.6, printed p. 381 (PDF p. 390).

import Definitions.Def_EthierKurtz_exclusionVariation

open Filter
open scoped Topology BigOperators

namespace EthierKurtz

/-- The exact weighted domain and ordered-pair sum in (3.29).
Continuous outputs are specified by equality to the pointwise series. -/
def exclusionGraph {S : Type*} (c : S → S → C(S → Bool, ℝ))
    (γ : S → S → ℝ) : Set (C(S → Bool, ℝ) × C(S → Bool, ℝ)) :=
  {fg | Summable (fun ij : S × S => γ ij.1 ij.2 * exclusionVariation fg.1 ij.1 ij.2) ∧
    ∀ η, fg.2 η = ∑' ij : S × S,
      c ij.1 ij.2 η * (fg.1 (exclusionExchange ij.1 ij.2 η) - fg.1 η)}

end EthierKurtz


