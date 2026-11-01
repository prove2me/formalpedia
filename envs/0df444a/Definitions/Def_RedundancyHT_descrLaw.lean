-- Prove2me | Definitions.Def_RedundancyHT_descrLaw
-- name    : RedundancyHT_descrLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:26:13.448559+00:00
-- url     : https://prove2.me/theorems/419793e7-e832-4473-a090-6f829740ea7d
-- title:
--   The law of the descriptor $(c;u)$
-- statement:
--   If the state of the cancel-on-start queue has law $p$, this is the probability that its descriptor equals $d$.
-- source:
--   Cardinaels, Borst & van Leeuwaarden, Heavy-Traffic Universality of Redundancy Systems with Assignment Constraints, arXiv:2005.14566v5, §2.3.2, p.8

import Definitions.Def_RedundancyHT_descr

set_option autoImplicit false

open MeasureTheory Filter Topology BipartiteMatchingHT.Delay Classical
open scoped BigOperators ENNReal BoundedContinuousFunction

noncomputable section

namespace RedundancyHT

/-- **The marginal law of the descriptor `(c;u)`** under a law `p` of the full state
(arXiv:2005.14566v5, p.8). -/
def descrLaw {n m : ℕ} (D : Model n m) (p : QueueState n m → ℝ≥0∞)
    (d : List (Fin n) × List (Fin m)) : ℝ≥0∞ :=
  ∑' q, if descr D q = d then p q else 0

end RedundancyHT


