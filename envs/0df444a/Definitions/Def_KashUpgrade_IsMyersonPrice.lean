-- Prove2me | Definitions.Def_KashUpgrade_IsMyersonPrice
-- name    : KashUpgrade_IsMyersonPrice
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:20:00.951978+00:00
-- url     : https://prove2.me/theorems/bbc7aeb7-122b-4da7-93b2-e2662d9de4e6
-- title:
--   The Myerson price $p^*$
-- statement:
--   The number $p\ge 0$ is a Myerson price of the type law if it solves
--   $$
--   p^*:=\arg\max_{\theta\ge 0}\,(1-F(\theta))\cdot\theta .
--   $$
--   It is the price per unit of quality that maximizes the one-period expected revenue when a single technology class is offered.
-- source:
--   Kash, Key & Zoumpoulis, Optimal Pricing and Introduction Timing of Technology Upgrades in Subscription-Based Services, SSRN 3934603 (Aug. 3, 2022), §4.1, p.13

import Mathlib
import Definitions.Def_KashUpgrade_typeCdf

namespace KashUpgrade

/-- **The Myerson price `p*`.** Kash, Key & Zoumpoulis, *Optimal Pricing and Introduction Timing of Technology Upgrades in Subscription-Based Services*, SSRN 3934603 (Aug. 3, 2022), §4.1, p.13: `p* := argmax_{θ ≥ 0} (1 - F θ) · θ`.
-/
def IsMyersonPrice (f : ℝ → ℝ) (p : ℝ) : Prop :=
  0 ≤ p ∧ ∀ θ, 0 ≤ θ → (1 - typeCdf f θ) * θ ≤ (1 - typeCdf f p) * p

end KashUpgrade


