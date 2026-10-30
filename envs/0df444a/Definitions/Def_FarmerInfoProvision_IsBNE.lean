-- Prove2me | Definitions.Def_FarmerInfoProvision_IsBNE
-- name    : FarmerInfoProvision_IsBNE
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:40:56.286332+00:00
-- url     : https://prove2.me/theorems/601f06bc-ef8b-4d3a-89d4-4d22f73639c1
-- title:
--   Bayesian Nash equilibrium of the production game with informed set $I$
-- statement:
--   A strategy profile $\sigma$ is a Bayesian Nash equilibrium of the game with informed set $I$ when every $\sigma_i$ is admissible and no farmer gains by a unilateral admissible deviation:
--
--   $$
--   \pi_i(\sigma_{-i},g)\le\pi_i(\sigma)\quad\text{for every farmer } i \text{ and every admissible } g.
--   $$
--
--   **Formalization Note** (1) Quantities are unrestricted real numbers: problems (2)–(3) print $\max_{q\ge0}$, but the paper's equilibrium (Proposition 1) is a nonconstant Gaussian and hence negative with positive probability; following footnote 6 and the literature cited there, the sign constraint is dropped. (2) Problems (2)–(3) maximize conditional expected profit given the farmer's signals; for square-integrable strategies this is equivalent to maximizing the ex-ante expected profit over all admissible functions of the same signals, which is the form used.
-- source:
--   Zhou, Fan, Chen, Tang, Information Provision and Farmer Welfare in Developing Economies, SSRN 3369334 (June 27, 2019), §3, problems (2)–(3), p. 10; §4.1, p. 12

import Mathlib
import Definitions.Def_FarmerInfoProvision_expectedProfit
import Definitions.Def_FarmerInfoProvision_Admissible

open MeasureTheory ProbabilityTheory

namespace FarmerInfoProvision

/-- **Bayesian Nash equilibrium of the production game when the set `I` is informed.**
Zhou, Fan, Chen, Tang, *Information Provision and Farmer Welfare in Developing Economies*,
SSRN 3369334 (June 27, 2019), §3, problems (2)–(3), p. 10, and §4.1, p. 12: "each farmer needs
to decide on his best response production quantity by maximizing his ex-post expected profit as
stated in (2) and (3) … by considering the best response functions that solve (2) and (3)
'simultaneously'".

`IsBNE M a b c α β γ I σ` holds when every `σ i` is admissible and, for every farmer `i` and
every admissible `g`, replacing `σ i` by `g` does not raise farmer `i`'s expected profit:
`expectedProfit … (Function.update σ i g) i ≤ expectedProfit … σ i`.

**Formalization Note.** (1) Quantities are unrestricted real numbers: problems (2)–(3) print
`max_{q ≥ 0}`, but the paper's own equilibrium (Proposition 1) is a nonconstant Gaussian and
hence negative with positive probability; following footnote 6 (p. 8) and the literature it
cites, the sign constraint is dropped. (2) Problems (2)–(3) are interim (conditional on the
farmer's signals); for square integrable strategies, maximizing the conditional expected profit
for almost every signal is equivalent to maximizing the ex-ante expected profit over all
admissible functions of the same signals, which is the form used here. -/
def IsBNE {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ}
    (M : GaussianPrimitives P n) (a b c α β γ : ℝ) (I : Finset (Fin n))
    (σ : Fin n → ℝ × ℝ → ℝ) : Prop :=
  (∀ i, Admissible M α β γ I i (σ i)) ∧
    ∀ i (g : ℝ × ℝ → ℝ), Admissible M α β γ I i g →
      expectedProfit M a b c α β γ I (Function.update σ i g) i ≤
        expectedProfit M a b c α β γ I σ i

end FarmerInfoProvision


