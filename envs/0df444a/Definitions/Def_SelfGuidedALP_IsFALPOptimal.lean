-- Prove2me | Definitions.Def_SelfGuidedALP_IsFALPOptimal
-- name    : SelfGuidedALP_IsFALPOptimal
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:24:44.031663+00:00
-- url     : https://prove2.me/theorems/c1875dec-052f-49bb-8d65-7736c4404934
-- title:
--   Optimal solution of $\mathrm{FALP}_n$
-- statement:
--   A vector $\beta\in\mathbb R^{n+1}$ is an **optimal solution of** $\mathrm{FALP}_n$ when it satisfies the constraints (8) and its objective dominates that of every vector satisfying (8).
--
--   This is the first iteration of self-guided FALP.
-- source:
--   Pakiman, Nadarajah, Soheili, Lin, Self-guided Approximate Linear Programs, arXiv:2001.02798v2, p.10

import Mathlib
import Definitions.Def_SelfGuidedALP_FALPFeasible
import Definitions.Def_SelfGuidedALP_falpObjective

open MeasureTheory

namespace SelfGuidedALP

/-- `β` is an optimal solution of `FALP_n` with state-relevance distribution `ν`
(Pakiman, Nadarajah, Soheili, Lin, Self-guided Approximate Linear Programs, arXiv:2001.02798v2, p.10). -/
def IsFALPOptimal {d m n : ℕ} (M : MDP d m) (R : RBClass d) (ν : Measure (EuclideanSpace ℝ (Fin d)))
    (θs : Fin n → EuclideanSpace ℝ (Fin (d + 1))) (β : Fin (n + 1) → ℝ) : Prop :=
  FALPFeasible M R θs β ∧
    ∀ β' : Fin (n + 1) → ℝ, FALPFeasible M R θs β' →
      falpObjective R ν θs β' ≤ falpObjective R ν θs β

end SelfGuidedALP


