-- Prove2me | Definitions.Def_FarmerInfoProvision_totalWelfare
-- name    : FarmerInfoProvision_totalWelfare
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:33:12.123968+00:00
-- url     : https://prove2.me/theorems/f93fa954-c79a-4043-9069-ac28be110b96
-- title:
--   Total ex-ante farmer profit $W(n_1,\beta;\gamma)=n_1W^I+(n-n_1)W^J$ (closed form)
-- statement:
--   The farmers' total ex-ante expected profit when $n_1$ of the $n$ farmers are informed is
--
--   $$
--   W(n_1,\beta;\gamma)=n_1W^I(n_1,\beta;\gamma)+(n-n_1)W^J(n_1,\beta;\gamma),
--   $$
--
--   with $W^I$, $W^J$ Lemma 2's closed forms. It is the objective of the central planner's problem (5).
--
--   **Formalization Note** $n$ and $n_1$ are real so that the proof of Proposition 2 can treat $n_1$ as continuous; the policies themselves are the integers $0\le n_1\le n$.
-- source:
--   Zhou, Fan, Chen, Tang, Information Provision and Farmer Welfare in Developing Economies, SSRN 3369334 (June 27, 2019), §4.2, p. 14 (definition of W), and §3, problem (5), p. 11

import Mathlib
import Definitions.Def_FarmerInfoProvision_profitInformed
import Definitions.Def_FarmerInfoProvision_profitUninformed

namespace FarmerInfoProvision

/-- **The farmers' total ex-ante expected profit `W(n1, β; γ)` on Lemma 2's closed forms.**
Zhou, Fan, Chen, Tang, *Information Provision and Farmer Welfare in Developing Economies*,
SSRN 3369334 (June 27, 2019), §4.2, p. 14: "By applying Lemma 2, we can determine the farmers'
total (ex ante) expected profit `W(n1, β; γ) ≡ {n1 W^I(n1, β; γ) + (n − n1) W^J(n1, β; γ)}`";
also the objective of the central planner's problem (5), p. 11.

**Formalization Note.** `n` and `n1` are real numbers so that the proof of Proposition 2 can
treat `n1` as continuous (p. 35); the paper's policies are the integers `0 ≤ n1 ≤ n`. -/
noncomputable def totalWelfare (a b c n n1 α β γ : ℝ) : ℝ :=
  n1 * profitInformed a b c n n1 α β γ + (n - n1) * profitUninformed a b c n n1 α β γ

end FarmerInfoProvision


