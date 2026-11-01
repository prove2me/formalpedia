-- Prove2me | Definitions.Def_SelfGuidedALP_IsFALPSGOptimal
-- name    : SelfGuidedALP_IsFALPSGOptimal
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:25:43.230657+00:00
-- url     : https://prove2.me/theorems/aa3b0c8c-051c-4a80-8955-4f45d3caecc1
-- title:
--   Optimal solution of $\mathrm{FALP}^{\mathrm{SG}}_n$
-- statement:
--   A vector $\beta$ is an **optimal solution of** $\mathrm{FALP}^{\mathrm{SG}}_n$ with previous VFA $V_{\mathrm{prev}}$ when it is feasible to (8)–(9) and its objective dominates that of every feasible vector.
--
--   This is the subproblem of each later iteration of Algorithm 2.
-- source:
--   Pakiman, Nadarajah, Soheili, Lin, Self-guided Approximate Linear Programs, arXiv:2001.02798v2, p.16

import Mathlib
import Definitions.Def_SelfGuidedALP_FALPSGFeasible
import Definitions.Def_SelfGuidedALP_falpObjective

open MeasureTheory

namespace SelfGuidedALP

/-- `β` is an optimal solution of `FALP^SG_n` with state-relevance distribution `ν` and previous VFA
`Vprev` (Pakiman, Nadarajah, Soheili, Lin, Self-guided Approximate Linear Programs, arXiv:2001.02798v2, p.16). -/
def IsFALPSGOptimal {d m n : ℕ} (M : MDP d m) (R : RBClass d)
    (ν : Measure (EuclideanSpace ℝ (Fin d))) (θs : Fin n → EuclideanSpace ℝ (Fin (d + 1)))
    (Vprev : EuclideanSpace ℝ (Fin d) → ℝ) (β : Fin (n + 1) → ℝ) : Prop :=
  FALPSGFeasible M R θs Vprev β ∧
    ∀ β' : Fin (n + 1) → ℝ, FALPSGFeasible M R θs Vprev β' →
      falpObjective R ν θs β' ≤ falpObjective R ν θs β

end SelfGuidedALP


