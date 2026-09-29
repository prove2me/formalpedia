-- Prove2me | Definitions.Def_HighDimProb_Deviations_SubgaussianVectorNorm
-- name    : HighDimProb_Deviations_SubgaussianVectorNorm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T23:06:41.394145+00:00
-- url     : https://prove2.me/theorems/e86805b1-68de-4363-b9f3-928fc1bebe74
-- title:
--   The sub-gaussian norm $\|X\|_{\psi_2}$ of a random vector
-- statement:
--   The **sub-gaussian norm** of a random vector $X$ in $\mathbb R^n$: $\|X\|_{\psi_2} :=
--   \sup_{x\in S^{n-1}}\|\langle X,x\rangle\|_{\psi_2}$, the supremum of the (scalar) sub-gaussian
--   norms of its one-dimensional marginals over the unit sphere. This is the quantity the constant
--   $K = \max_i\|A_i\|_{\psi_2}$ of Theorem 9.1.1 bounds each row of $A$ by.
--
--   **Formalization Note** Reuses the published scalar `subgaussianNorm` (Definition 2.5.6,
--   Chapter 2) applied to each marginal $\langle X,x\rangle$, per `CAPTAIN_BRIEF.md` Addendum 2
--   rule 5.
-- source:
--   Vershynin, High-Dimensional Probability (2018), p. 56, Definition 3.4.1

import Mathlib
import Definitions.Def_HighDimProb_Concentration_SubgaussianNorm

open MeasureTheory

namespace HighDimProb.Deviations

/-- The **sub-gaussian norm** `‖X‖_{ψ₂}` of a random vector `X : Ω → EuclideanSpace ℝ (Fin n)`.
Vershynin, *High-Dimensional Probability* (2018), Definition 3.4.1, p. 56 (PDF p. 64): "The
sub-gaussian norm of `X` is defined as `‖X‖_{ψ2} = sup_{x∈S^{n-1}} ‖⟨X,x⟩‖_{ψ2}`," reusing the
published scalar sub-gaussian (Orlicz `ψ₂`) norm `HighDimProb.Concentration.subgaussianNorm`
(Definition 2.5.6, per `CAPTAIN_BRIEF.md` Addendum 2 rule 5) applied to each one-dimensional
marginal `⟨X,x⟩`. The supremum ranges over the subtype of unit vectors `{v // ‖v‖ = 1}`, the
book's sphere `Sⁿ⁻¹`. -/
noncomputable def subgaussianVectorNorm {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) {n : ℕ}
    (X : Ω → EuclideanSpace ℝ (Fin n)) : ℝ :=
  ⨆ x : {v : EuclideanSpace ℝ (Fin n) // ‖v‖ = 1},
    HighDimProb.Concentration.subgaussianNorm P (fun ω => inner (𝕜 := ℝ) (X ω) x.1)

end HighDimProb.Deviations


