-- Prove2me | Definitions.Def_OpaquePricing_Dominance_Supplement_ExampleLaw
-- name    : OpaquePricing_Dominance_Supplement_ExampleLaw
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T23:35:13.767097+00:00
-- url     : https://prove2.me/theorems/1f7ba8f8-0b2a-4bac-a364-b09d9a122a58
-- title:
--   Example 4: the uniform-permutation separating distribution
-- statement:
--   For $N\ge2$ and each $k=1,\ldots,N$, put mass $2^{-(N-k+1)}$ on a uniformly chosen permutation of the vector having $k$ coordinates equal to $2^{N-k+1}$ and the rest zero. Add mass $2^{-N}$ at the all-ones vector:
--   $$F_N=\sum_{k=1}^N2^{-(N-k+1)}\operatorname{UnifPerm}(2^{N-k+1}\mathbf1_{[k]})+2^{-N}\delta_{\mathbf1}.$$
--   Uniform permutation averages over all $N!$ permutations, retaining repetitions. The final all-ones mass is retained, so the weights sum to one. This is the explicit, nonzero separating law used for Theorem 3(iii), rather than an arbitrary witness that could collapse to zero revenue.
-- source:
--   Elmachtoub & Hamilton, The Power of Opaque Products in Pricing, author's manuscript (2021; Manag. Sci. doi:10.1287/mnsc.2020.3750), Appendix H, p. 43, Example 4

import Mathlib
import Definitions.Def_OpaquePricing_Dominance_Setting

open MeasureTheory

namespace OpaquePricing.Dominance.Supplement

/-- Uniform pushforward over all permutations, with repetitions retained. -/
noncomputable def permutationLaw {N : ℕ} (v : Fin N → ℝ) : Measure (Fin N → ℝ) :=
  (Fintype.card (Equiv.Perm (Fin N)) : ENNReal)⁻¹ •
    ∑ σ : Equiv.Perm (Fin N), Measure.dirac (v ∘ σ)

/-- Example 4, including its final mass 2⁻ᴺ at the all-ones vector. -/
noncomputable def exampleLaw (N : ℕ) : Measure (Fin N → ℝ) :=
  (∑ k : Fin N, (ENNReal.ofReal ((2 : ℝ) ^ (N - k.val)))⁻¹ •
    permutationLaw (fun i : Fin N => if i.val ≤ k.val then (2 : ℝ) ^ (N - k.val) else 0)) +
  (ENNReal.ofReal ((2 : ℝ) ^ N))⁻¹ • Measure.dirac (fun _ => 1)

end OpaquePricing.Dominance.Supplement


