-- Prove2me | Definitions.Def_ChoiceRM_FareOrder_Example2
-- name    : ChoiceRM_FareOrder_Example2
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:46:34.15427+00:00
-- url     : https://prove2.me/theorems/babe8f0b-48ca-4e33-a9c1-474f05d2e9c7
-- title:
--   Example 2, pp. 18–19 (Table 5) — a three-fare choice model
-- statement:
--   The choice model of Example 2 on $N = \{1, 2, 3\}$, given by Table 5 (p. 19). For each nonempty offer set the purchase probabilities of the offered products, in increasing product index, are:
--
--   | offer set $S$ | $(P_j(S))_{j \in S}$ |
--   |---|---|
--   | $\{3\}$ | $(0.5)$ |
--   | $\{2\}$ | $(0.5)$ |
--   | $\{1\}$ | $(0.5)$ |
--   | $\{1,2\}$ | $(0.0,\ 0.5)$ |
--   | $\{2,3\}$ | $(0.5,\ 0.5)$ |
--   | $\{1,3\}$ | $(0.5,\ 0.5)$ |
--   | $\{1,2,3\}$ | $(0.0,\ 0.5,\ 0.5)$ |
--
--   Products not offered are bought with probability $0$, and nothing is bought from the empty offer set.
--
--   The paper's footnote explains the model as a mixture of two customer types with probability $0.5$ each: type A buys product 2 if products 1 and 2 are both offered and product 1 if only product 1 is offered; type B buys only product 3.
--
--   The example shows that a choice model need not have the nesting-by-fare-order property.
--
--   **Formalization Note** Product $j$ is the element $j - 1$ of `Fin 3`, and each offer set is matched literally against the seven rows of Table 5; every other set (only $\emptyset$) gets the zero vector.
-- source:
--   Talluri, van Ryzin, Revenue management under a general discrete choice model of consumer behavior, working paper of October 21, 2001 (UPF Economics Working Paper 533; published Management Science 50(1), 2004, DOI 10.1287/mnsc.1030.0147), p. 18, Example 2; p. 19, Table 5 (called Table 3.2 on p. 18)

import Mathlib
import Definitions.Def_RevenueManagement_singleResource
import Definitions.Def_ChoiceRM_FareOrder_FareOrder

namespace ChoiceRM.FareOrder

/-- The choice model of Example 2 (p. 18), Table 5 (p. 19), on `N = {1, 2, 3}` (here `Fin 3`,
fare `j` is `j - 1`). Each row of Table 5 lists the purchase probabilities of the offered
fares in increasing index; fares not offered, and the empty offer set, have probability `0`. -/
noncomputable def example2Model : Finset (Fin 3) → Fin 3 → ℝ := fun S =>
  if S = {2} then ![0, 0, 1 / 2]
  else if S = {1} then ![0, 1 / 2, 0]
  else if S = {0} then ![1 / 2, 0, 0]
  else if S = {0, 1} then ![0, 1 / 2, 0]
  else if S = {1, 2} then ![0, 1 / 2, 1 / 2]
  else if S = {0, 2} then ![1 / 2, 0, 1 / 2]
  else if S = {0, 1, 2} then ![0, 1 / 2, 1 / 2]
  else ![0, 0, 0]

end ChoiceRM.FareOrder


