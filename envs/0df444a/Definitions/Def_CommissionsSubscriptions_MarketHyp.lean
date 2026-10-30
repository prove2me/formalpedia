-- Prove2me | Definitions.Def_CommissionsSubscriptions_MarketHyp
-- name    : CommissionsSubscriptions_MarketHyp
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:23:15.662628+00:00
-- url     : https://prove2.me/theorems/1bc0d039-ba80-48eb-b3ae-ac9ae7d15806
-- title:
--   Standing hypotheses of the model (§2, Assumption 1)
-- statement:
--   A market satisfies the **standing hypotheses** of §2 if
--
--   1. all masses are positive: $s_i>0$ and $b_j>0$;
--   2. the disutilities are nonnegative: $c\in\mathbb R^n_+$;
--   3. every node of the compatibility network has degree at least one: each seller type and each buyer type has a neighbour in $E$;
--   4. every value distribution $F_{s_i}$ and $F_{b_j}$ satisfies Assumption 1.
--
--   The paper keeps these conditions throughout.
-- source:
--   Birge, Candogan, Chen, Saban, Optimal Commissions and Subscriptions in Networked Markets, SSRN abstract 3259716 (version of 2019-09-13), §2, p. 7 (masses, c ∈ ℝⁿ₊, degree at least one); Assumption 1, p. 8

import Mathlib
import Definitions.Def_CommissionsSubscriptions_Market
import Definitions.Def_CommissionsSubscriptions_IsValueCDF

namespace CommissionsSubscriptions

/-- **Standing hypotheses of the model (§2), including Assumption 1.**
Birge, Candogan, Chen, Saban, *Optimal Commissions and Subscriptions in Networked Markets*,
SSRN 3259716 (version of 2019-09-13), §2, pp. 7–8.

1. masses `s_i > 0`, `b_j > 0` (p. 7);
2. disutilities `c ∈ ℝⁿ₊`, i.e. `c_i ≥ 0` (p. 7);
3. "each node has degree at least one" (p. 7): every seller type and every buyer type has a
   neighbour in `E`;
4. Assumption 1 (p. 8) for every seller and every buyer value distribution (`IsValueCDF`). -/
def MarketHyp {S B : Type} (M : Market S B) : Prop :=
  (∀ i, 0 < M.s i) ∧ (∀ j, 0 < M.b j) ∧ (∀ i, 0 ≤ M.c i) ∧
    (∀ i, ∃ j, (i, j) ∈ M.E) ∧ (∀ j, ∃ i, (i, j) ∈ M.E) ∧
    (∀ i, IsValueCDF (M.Fs i)) ∧ (∀ j, IsValueCDF (M.Fb j))

end CommissionsSubscriptions


