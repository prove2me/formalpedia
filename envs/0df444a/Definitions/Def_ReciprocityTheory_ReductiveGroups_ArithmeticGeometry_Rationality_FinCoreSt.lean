-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_FinCoreSt
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_FinCoreSt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:29:31.279982+00:00
-- url     : https://prove2.me/theorems/9c5daf2f-04a4-46a3-93a1-49db5a410aeb
-- title:
--   Fin Core St
-- statement:
--   Definitions and structural lemmas for Fin Core St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/Rationality/FinCoreSt.lean

import Definitions.Def_ReciprocityTheory_SemistableReduction_ComapInclusionIsLocalHom
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
def FinCoreStatement : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] (K₀ : Subfield K),
    ReciprocityTheory.MultiplicativeHeights.ResidueFieldInfiniteOn (K₀ : Set K) →
    ∀ S : Set K, (∀ t ∈ S, 0 < ‖t‖ ∧ ‖t‖ < 1) →
    (∀ r : ℝ, 0 < r → r < 1 → ∀ ε > (0 : ℝ), ∃ t ∈ S, |‖t‖ - r| < ε) →
    (∀ t ∈ S, ∀ τ ∈ K₀, ‖τ‖ = 1 → t * τ ∈ S) →
    ∀ (ι : Type) [Fintype ι] (δ : MvPolynomial ι K),
      (∀ μ, ‖MvPolynomial.coeff μ δ‖ ≤ 1) → (∃ μ, ‖MvPolynomial.coeff μ δ‖ = 1) →
    ∀ (P : ℤ → MvPolynomial ι K) (b : ℕ), (∀ n, n < -(b : ℤ) → P n = 0) →
      (∀ t ∈ S, ∀ x : ι → K, (∀ i, x i ∈ K₀ ∧ ‖x i‖ ≤ 1) → ‖MvPolynomial.eval x δ‖ = 1 →
        Filter.Tendsto (fun n => ‖MvPolynomial.eval x (P n) * t ^ n‖) Filter.cofinite (nhds 0) ∧
        ‖∑' n, MvPolynomial.eval x (P n) * t ^ n‖ ≤ 1) →
      ∀ n, (∀ μ, ‖MvPolynomial.coeff μ (P n)‖ ≤ 1) ∧ (n < 0 → P n = 0)
end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank


