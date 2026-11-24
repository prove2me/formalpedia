-- Prove2me | Definitions.Def_WaitTimePricing_Existence_Supplement_RewardInterface
-- name    : WaitTimePricing_Existence_Supplement_RewardInterface
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T03:37:00.456272+00:00
-- url     : https://prove2.me/theorems/066749f5-8aa4-47ae-a550-89de9f22a5d6
-- title:
--   Abstract rewards and exact counterexample data
-- statement:
--   A reward consists of a function $v:\mathbb R\to\mathbb R$ and a waiting-cost weight $\alpha$. The interface records precisely
--   $$\alpha\ge0,\quad v(p)\le U'(0)t(p)\ (0\le p\le U'(0)),\quad v(U'(0))=0,\quad \exists p\in[0,U'(0)):v(p)>0.$$
--   It adds no regularity or attainment assumption. The concrete revenue and welfare rewards reuse the published definitions. The bundle also specifies the exact polynomial model $U(t)=2t-t^2/2$, $c(w)=w$, $C=1$ and an adjustable arrival rate, and the test reward $v(p)=2-p$ for $0<p<1$ and zero otherwise, with $\alpha=0$. These are explicit counterexample data, not claims made by the paper.
--
--   These definitions allow the printed abstract-reward claim to be examined without quietly imposing continuity on $v$.
-- source:
--   Lin, Shang, Sun, Wait Time Based Pricing for Queues with Customer-Chosen Service Times, SSRN 3709573 (version of October 12, 2020), p. 11, (V1), (V2), and the paragraph following Proposition 3

import Mathlib
import Definitions.Def_WaitTimePricing_Existence_Setting

set_option autoImplicit false

namespace WaitTimePricing.Existence.Supplement
noncomputable section
open Set

/-- Lin, Shang, Sun, Wait Time Based Pricing for Queues with Customer-Chosen Service Times,
SSRN 3709573 (version of October 12, 2020), p. 11, the abstract reward paragraph.
Formalization Note: no continuity, measurability, lower bound, or attainment is imposed. -/
structure Reward where
  value : ℝ → ℝ
  weight : ℝ

/-- Lin, Shang, Sun, Wait Time Based Pricing for Queues with Customer-Chosen Service Times, SSRN 3709573 (version of October 12, 2020), p. 11, (V1), (V2) and the abstract-reward paragraph.

Exactly (V1), (V2), and α ≥ 0 on the meaningful price domain of (5).
Lin, Shang, Sun, SSRN 3709573 (version of October 12, 2020), p. 11.
Formalization Note: the domain is [0,U′(0)], as in the base definition. -/
def Reward.Conditions (M : Model) (R : Reward) : Prop :=
  0 ≤ R.weight ∧
  (∀ p ∈ Icc 0 (deriv M.U 0), R.value p ≤ deriv M.U 0 * tOf M p) ∧
  R.value (deriv M.U 0) = 0 ∧
  ∃ p ∈ Ico 0 (deriv M.U 0), 0 < R.value p

/-- Lin, Shang, Sun, Wait Time Based Pricing for Queues with Customer-Chosen Service Times, SSRN 3709573 (version of October 12, 2020), p. 11, (V1), (V2) and the abstract-reward paragraph.

The concrete objectives of Lemma 1, p. 10, using the immutable base definitions. -/
def concreteReward (M : Model) (obj : Objective) : Reward := ⟨v M obj, alpha obj⟩

/-- Lin, Shang, Sun, Wait Time Based Pricing for Queues with Customer-Chosen Service Times, SSRN 3709573 (version of October 12, 2020), p. 11, (V1), (V2) and the abstract-reward paragraph.

Exact polynomial primitives used to test the source claims, not numerical approximations.
Lin, Shang, Sun, SSRN 3709573 (version of October 12, 2020), pp. 11, 21, Assumption 1 and Theorem 3.
Formalization Note: c(w)=w has c′(0)>0; the paper's numerical c(w)=.01w² does not. -/
def testModel (rate : ℝ) : Model :=
  ⟨fun t => 2 * t - t ^ 2 / 2, id, rate, 1⟩

/-- Lin, Shang, Sun, Wait Time Based Pricing for Queues with Customer-Chosen Service Times, SSRN 3709573 (version of October 12, 2020), p. 11, (V1), (V2) and the abstract-reward paragraph.

A reward allowed by (V1),(V2), p. 11, with unattained positive suprema on (0,1).
Formalization Note: v(0)=v(1)=v(2)=0; this is a Borel function, so the obstruction is attainment. -/
def nonattainingReward : Reward :=
  ⟨fun p => if 0 < p ∧ p < 1 then 2 - p else 0, 0⟩

end
end WaitTimePricing.Existence.Supplement


