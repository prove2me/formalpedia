-- Prove2me | Definitions.Def_RotationLadder_Protocol_offlineCost
-- name    : RotationLadder_Protocol_offlineCost
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:38:41.532784+00:00
-- url     : https://prove2.me/theorems/dae56fa2-2c59-415d-96aa-38c68e71d650
-- title:
--   Offline cost of a run
-- statement:
--   The offline cost of a run is the number of copies of $|H\rangle$ used by all its ladders:
--
--   $$\sum_{t<\tau}\bar c\bigl(\mathrm{pick}(r_t)\bigr),$$
--
--   where $\bar c(i)$ is the mean ladder cost of level $i$.
--
--   **Formalization Note** Each ladder enters through its mean. The paper simulates one ladder per step and averages; the ladders' randomness is independent of the outcomes $\omega$, so the expectation over $\omega$ is the same quantity.
-- source:
--   Duclos-Cianci, Svore, A State Distillation Protocol to Implement Arbitrary Single-qubit Rotations, arXiv:1210.1980v1, Sec. III, unnumbered, p. 4

import Mathlib
import Definitions.Def_RotationLadder_Protocol_ladderMeanCost
import Definitions.Def_RotationLadder_Protocol_stopTime
open scoped ENNReal

namespace RotationLadder.Protocol

/-- **The offline cost of a run.**
Duclos-Cianci, Svore, *A State Distillation Protocol to Implement Arbitrary Single-qubit Rotations*,
arXiv:1210.1980v1, Sec. III, p. 4: the offline cost "is the total number of distilled `|H⟩` states required to
obtain all of the intermediate `|H_i⟩` states used to perform the given unitary operation, that is,
the sum of the `|H⟩` states used for each ladder process."

`offlineCost pick φ ε ω = Σ_(t < τ) ladderMeanCost (pick r_t)`.

**Formalization Note.** Each ladder enters through its mean. The paper simulates one ladder per
step and averages; the ladders' randomness is independent of the rotation outcomes, so the
expectation over `ω` agrees with that average. -/
noncomputable def offlineCost (pick : ℝ → ℕ) (φ ε : ℝ) (ω : Coins) : ℝ≥0∞ :=
  ∑' t : ℕ, if (t : ℕ∞) < stopTime pick φ ε ω then
    ladderMeanCost (pick (residual pick φ ω t)) else 0

end RotationLadder.Protocol


