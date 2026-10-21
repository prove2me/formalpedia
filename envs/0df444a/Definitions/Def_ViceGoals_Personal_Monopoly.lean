-- Prove2me | Definitions.Def_ViceGoals_Personal_Monopoly
-- name    : ViceGoals_Personal_Monopoly
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T09:14:02.128969+00:00
-- url     : https://prove2.me/theorems/2094f5b8-da46-42e1-a2b3-cd77fa629a6c
-- title:
--   Nonnegative monopoly price with zero marginal cost
-- statement:
--   A monopoly sets a unit price $p≥0$ and faces a demand relation $D(p,Q)$. With zero marginal cost, its profit is $pQ$. A monopoly price is a feasible price with some corresponding demand $Q$ such that
--
--   $$pQ≥p'Q'$$
--
--   for every feasible alternative price $p'≥0$ and every demand $Q'$ allowed by $D$ at that price. This global optimality predicate can be reused for either consumer regime.
-- source:
--   Amaldoss & Harutyunyan, Pricing of Vice Goods for Goal-Driven Consumers, SSRN 4226237 (version of September 2022), pp. 7, 10, 12–13 (PDF 8, 11, 13–14), §3 and §4.1–4.2

import Mathlib

namespace ViceGoals.Personal

/-- A nonnegative price maximizes revenue against a demand relation, with zero marginal cost. -/
def IsMonopolyPrice (D : ℝ → ℝ → Prop) (p : ℝ) : Prop :=
  0 ≤ p ∧ ∃ Q, D p Q ∧
    ∀ p' Q' : ℝ, 0 ≤ p' → D p' Q' → p' * Q' ≤ p * Q

end ViceGoals.Personal


