-- Prove2me | Definitions.Def_PrefDeals_aagTheta
-- name    : PrefDeals_aagTheta
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:20:16.063295+00:00
-- url     : https://prove2.me/theorems/016021ee-b2b8-4e36-a28b-a966f4418521
-- title:
--   Threshold $\theta_j$ of Auction-Adjusted Greedy
-- statement:
--   For a stream $A$, a set of buyers $S$ and $j\in S_1$, the **threshold** $\theta_j$ is the smallest real number with
--
--   $$
--   \Pr_A[v_j\ge\theta_j]=\Pr_A[v_j=v_{(1)}(S_1)] .
--   $$
--
--   With this threshold, buyer $j$ buys as many impressions as he would win in a second-price auction among $S_1$ without reserve, but he picks his highest-value impressions.
--
--   **Formalization Note** The smallest threshold is the infimum of the set of thresholds with the required mass (masses unnormalized, $P(A\cap\cdot)$). That the infimum is attained is not built into the definition; it is a conclusion of the cherry-picking milestone (eq. (3)) and of the goal (a run exists). The algorithm computes thresholds only when $|S_1|\ge2$.
-- source:
--   Kim, Mirrokni & Nazerzadeh, Deals or No Deals: Contract Design for Online Advertising, SSRN 2693037, Figure 1, p.11 ("Choose the smallest $\theta_j$ such that ...")

import Mathlib
import Definitions.Def_PrefDeals_aagS1

open MeasureTheory

namespace PrefDeals

/-- **The threshold `θⱼ` of Auction-Adjusted Greedy.**
Kim, Mirrokni & Nazerzadeh, *Deals or No Deals*, SSRN 2693037, Figure 1, p.11: "For each buyer
`j ∈ S₁`: Choose the smallest `θⱼ` such that `Pr_𝓘[vⱼ ≥ θⱼ] = Pr_𝓘[vⱼ = v₍₁₎(S₁)]`."

`aagTheta M A S j = inf {θ ∈ ℝ : P(A ∩ {vⱼ ≥ θ}) = P(A ∩ {vⱼ = v₍₁₎(S₁)})}` with `S₁ = aagS1 M A S`.

**Formalization Note.** The "smallest `θⱼ`" is the real `sInf` of the set of thresholds with the
required mass; probabilities are unnormalized (`P(A ∩ ·)` instead of `Pr_𝓘`, the same condition).
Whether the infimum belongs to the set (is attained) is not built in; the existence of a run of the
algorithm, asserted in the goal theorem, and milestone (3) assert it. The value is only used for
`j ∈ S₁` when `|S₁| ≥ 2`, where the set is nonempty and bounded below. -/
noncomputable def aagTheta {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ}
    (M : ValuationModel P n) (A : Set Ω) (S : Finset (Fin n)) (j : Fin n) : ℝ :=
  sInf {θ : ℝ | P (A ∩ {ω | θ ≤ M.v j ω}) = P (A ∩ {ω | M.v j ω = vmax M (aagS1 M A S) ω})}

end PrefDeals


