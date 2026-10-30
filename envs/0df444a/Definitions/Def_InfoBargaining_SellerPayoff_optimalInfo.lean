-- Prove2me | Definitions.Def_InfoBargaining_SellerPayoff_optimalInfo
-- name    : InfoBargaining_SellerPayoff_optimalInfo
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:15:18.893879+00:00
-- url     : https://prove2.me/theorems/722a31b2-0094-4027-8797-7351f478bdec
-- title:
--   Buyer's optimal information acquisition $\alpha^*$
-- statement:
--   The buyer's **optimal information acquisition** $\alpha^*$ solves (6) over $\alpha\in[\underline\alpha,\bar\alpha]$:
--
--   $$
--   \alpha^*=\min\Big\{\alpha\in[\underline\alpha,\bar\alpha]:\ U_b(\alpha)=\max_{\beta\in[\underline\alpha,\bar\alpha]}U_b(\beta)\Big\}.
--   $$
--
--   When several informativeness levels are optimal, $\alpha^*$ is the least of them. This is the tie-break printed in Corollary 1 ("$\alpha^*=\underline\alpha$ for $\theta_b\le\tilde\theta$", "$\alpha^*=\underline\alpha$ for $c\le c_l$ or $c\ge c_h$"). Ties do occur: for the uniform prior and $c=1/2$, $A(\alpha,1/2)=\alpha/8$ is linear in $\alpha$.
--
--   **Formalization Note** Defined as the infimum of the set of maximizers. Under the standing hypotheses ($0<\underline\alpha<\bar\alpha<1$, a prior with finite mean) the objective is convex in $\alpha$, so the set is nonempty and the infimum is attained; Lean's value $\inf\emptyset=0$ is never reached.
-- source:
--   Guo, Gathering Information before Negotiation, SSRN 3930651 (manuscript of 15 Feb 2022), §3.1, p. 10 ("Let α∗ be the optimal level of information acquisition as the solution to (6)"); tie-break of Corollary 1, p. 13

import Mathlib
import Definitions.Def_InfoBargaining_SellerPayoff_buyerObjective

open MeasureTheory

namespace InfoBargaining.SellerPayoff

/-- **The buyer's optimal information acquisition `α*`: the least maximizer of (6).**
Guo, *Gathering Information before Negotiation*, SSRN 3930651 (manuscript of 15 Feb 2022),
§3.1, p. 10: "Let α∗ be the optimal level of information acquisition as the solution to (6)",
where the buyer chooses "α ∈ [α̲, ᾱ] ⊆ (0, 1)" (§2, p. 8).

`optimalInfo μ α̲ ᾱ k̄ θ_b c` is the infimum of the set of maximizers of
`α ↦ buyerObjective μ α̲ ᾱ k̄ θ_b c α` over `[α̲, ᾱ]`.

**Formalization Note.** Ties are broken toward the least maximizer, the tie-break printed in
Corollary 1 (p. 13: "α∗ = α̲ for θ_b ≤ θ̃", "α∗ = α̲ for c ≤ c_l or c ≥ c_h"). Ties do occur
(uniform prior, `c = 1/2`: `A(α, 1/2) = α/8` is linear in `α`). Under the standing hypotheses
(`0 < α̲ < ᾱ < 1`, a prior with finite mean) the objective is convex in `α`, the maximizer set
is nonempty and the infimum is attained, so the value `sInf ∅ = 0` is never reached. -/
noncomputable def optimalInfo (μ : Measure ℝ) (αl αh kbar θb c : ℝ) : ℝ :=
  sInf {α | α ∈ Set.Icc αl αh ∧
    ∀ β ∈ Set.Icc αl αh, buyerObjective μ αl αh kbar θb c β ≤ buyerObjective μ αl αh kbar θb c α}

end InfoBargaining.SellerPayoff


