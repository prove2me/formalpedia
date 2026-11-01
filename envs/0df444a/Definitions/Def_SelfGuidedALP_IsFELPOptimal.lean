-- Prove2me | Definitions.Def_SelfGuidedALP_IsFELPOptimal
-- name    : SelfGuidedALP_IsFELPOptimal
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:27:04.478164+00:00
-- url     : https://prove2.me/theorems/6fbc2067-6786-4b67-bd02-ffc7931c8a7e
-- title:
--   Optimal FELP solution
-- statement:
--   A pair $(\beta_0,B)$ with $B\in\mathcal B$ is an **optimal FELP solution** when it is FELP-feasible and its objective dominates that of every FELP-feasible pair.
--
--   Proposition 1 relates such solutions to $V^*$.
-- source:
--   Pakiman, Nadarajah, Soheili, Lin, Self-guided Approximate Linear Programs, arXiv:2001.02798v2, FELP, p.9

import Mathlib
import Definitions.Def_SelfGuidedALP_FELPFeasible
import Definitions.Def_SelfGuidedALP_felpObjective

open MeasureTheory

namespace SelfGuidedALP

/-- `(β₀, B)` is an optimal FELP solution with state-relevance distribution `ν`: it is FELP-feasible
and its objective dominates that of every FELP-feasible pair
(Pakiman, Nadarajah, Soheili, Lin, Self-guided Approximate Linear Programs, arXiv:2001.02798v2, FELP, p.9). -/
def IsFELPOptimal {d m : ℕ} (M : MDP d m) (R : RBClass d) (ν : Measure (EuclideanSpace ℝ (Fin d)))
    (β₀ : ℝ) (B : Bspace R) : Prop :=
  FELPFeasible M R β₀ B ∧
    ∀ (β₀' : ℝ) (B' : Bspace R), FELPFeasible M R β₀' B' →
      felpObjective R ν β₀' B' ≤ felpObjective R ν β₀ B

end SelfGuidedALP


