-- Prove2me | Definitions.Def_EthierKurtz_boundedPointwiseClosure
-- name    : EthierKurtz_boundedPointwiseClosure
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T06:02:50.877192+00:00
-- url     : https://prove2.me/theorems/c70ca414-2444-48dd-b5e6-73c0dd6ae891
-- title:
--   Bounded-pointwise sequential closure
-- statement:
--   The smallest superset closed under pointwise limits of uniformly bounded sequences.
-- source:
--   Stewart N. Ethier and Thomas G. Kurtz, Markov Processes: Characterization and Convergence, Wiley, 1986, Appendix 3, printed pp. 495–496 (PDF pp. 504–505).

import Mathlib

open Filter
open scoped Topology

namespace EthierKurtz

/-- Appendix 3: the smallest set closed under uniformly bounded pointwise
sequential limits. Starting with bounded Borel functions, this remains in the
bounded Borel functions, although the ambient function type is unbundled. -/
def boundedPointwiseClosure {E : Type*} (H : Set (E → ℝ × ℝ)) : Set (E → ℝ × ℝ) :=
  {f | ∀ S : Set (E → ℝ × ℝ), H ⊆ S →
    (∀ (u : ℕ → E → ℝ × ℝ) (v : E → ℝ × ℝ),
      (∀ n, u n ∈ S) → (∃ M : ℝ, ∀ n x, ‖u n x‖ ≤ M) →
      (∀ x, Tendsto (fun n => u n x) atTop (𝓝 (v x))) → v ∈ S) → f ∈ S}

end EthierKurtz


