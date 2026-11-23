-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CoveringRadiusStatement
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CoveringRadiusStatement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:17:12.35174+00:00
-- url     : https://prove2.me/theorems/baa79542-bebe-4403-97e9-f8106de1f3a2
-- title:
--   Covering Radius Statement
-- statement:
--   Definitions and structural lemmas for Covering Radius Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/CoveringRadiusStatement.lean

import Definitions.Def_ReciprocityTheory_SemistableReduction_TorsionNonvanishStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.FD
open NumberField Matrix ReciprocityTheory.MultiplicativeHeights
noncomputable def d5mu (f r : ℕ) (d laStar : ℝ) : ℝ := 4 * ((f : ℝ) * r) ^ 3 * d / laStar
def CoveringRadiusStatement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsCMField K] (ι : Type) [Fintype ι] [Nonempty ι]
    (r p : ℕ) (S : HermForm K r) (σ : ι → K →+* ℂ) (Q : ι → Matrix (Fin r) (Fin r) ℂ)
    (L : Submodule (𝓞 K) (Fin r → K)) (laStar : ℝ),
    Function.Injective σ →
    (∀ τ : K →+* ℂ, (∃ i, σ i = τ) ↔ ¬ ∃ i, σ i = ComplexEmbedding.conjugate τ) →
    p ≤ r → 0 < laStar → (∀ i, (Q i).det ≠ 0) →
    (∀ i x y, σ i (S.h x y) = jForm p (Q i *ᵥ embVec (σ i) x) (Q i *ᵥ embVec (σ i) y)) →
    IsLattice L → IsSelfDual S L →
    (∀ v ∈ L, v ≠ 0 → ∃ i, laStar ^ 2 ≤ normSq (Q i *ᵥ embVec (σ i) v)) →
    let μ := d5mu (Fintype.card ι) r |(NumberField.discr K : ℝ)| laStar
    (∀ w : ι → Fin r → ℂ, ∃ l ∈ L, ∑ i, normSq (Q i *ᵥ embVec (σ i) l - w i) ≤ μ ^ 2) ∧
    ∃ v : Fin r → Fin r → K, (∀ j, v j ∈ L) ∧ LinearIndependent K v ∧ ∀ j, majSq σ Q (v j) ≤ μ ^ 2
end ReciprocityTheory.ChartRestriction.G.FD


