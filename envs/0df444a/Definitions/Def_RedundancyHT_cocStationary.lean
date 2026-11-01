-- Prove2me | Definitions.Def_RedundancyHT_cocStationary
-- name    : RedundancyHT_cocStationary
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:25:32.675838+00:00
-- url     : https://prove2.me/theorems/ecf61c43-2105-4234-8d3f-d4a08730ce0f
-- title:
--   Stationary laws of the c.o.c. chain
-- statement:
--   A function $p$ on job sequences is a stationary law of the cancel-on-completion chain at load $\rho\ge0$ if it is a probability distribution satisfying the balance equations of the chain.
-- source:
--   Cardinaels, Borst & van Leeuwaarden, Heavy-Traffic Universality of Redundancy Systems with Assignment Constraints, arXiv:2005.14566v5, §2.3.1, p.7

import Definitions.Def_RedundancyHT_cocChain

set_option autoImplicit false

open MeasureTheory Filter Topology BipartiteMatchingHT.Delay
open scoped BigOperators ENNReal BoundedContinuousFunction

noncomputable section

namespace RedundancyHT

/-- **A stationary law of the c.o.c. chain at load `ρ`** (arXiv:2005.14566v5, §2.3.1, p.7), shaped
like the published `stationary` of the c.o.s. queue. -/
def cocStationary {n m : ℕ} (D : Model n m) (ρ : ℝ) (p : List (Fin n) → ℝ≥0∞) : Prop :=
  ∃ hρ : 0 ≤ ρ, (cocChain D ρ hρ).IsStationary p

end RedundancyHT


