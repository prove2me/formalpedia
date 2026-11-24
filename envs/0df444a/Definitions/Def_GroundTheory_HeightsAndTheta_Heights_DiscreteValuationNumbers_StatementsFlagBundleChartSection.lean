-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsFlagBundleChartSection
-- name    : GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsFlagBundleChartSection
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:48:19.452077+00:00
-- url     : https://prove2.me/theorems/f14a623c-fca8-4ad1-ad79-8bb0d569777f
-- title:
--   Statements Flag Bundle Chart Section
-- statement:
--   Definitions and structural lemmas for Statements Flag Bundle Chart Section, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/StatementsFlagBundleChartSection.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsFlagBundleSectionDiv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
def FlagBundleChartSection.Statement : Prop :=
  ∀ (F : Type) [Field F] (Ω : Type) [Field Ω] [Algebra F Ω]
    (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) (y : (Σ k, ι k) → Ω)
    (N : ℕ) (E : Type) [AddCommGroup E] [Module Ω E]
      (B : ChartBundle F (segreVec y) N E) (w : Module.Basis (Fin N) Ω E) (b : Fin N → K → ℤ),
      IsFlagFrame y B w b →
    ∀ (M : ℕ) (a : K → ℤ) (φ : Fin M → Module.Dual Ω E), IsTwistedDualGens y B a φ →
    ∀ (Φ : Type) [Field Φ] [Algebra Ω Φ] (t : Fin N → Φ), AlgebraicIndependent Ω t →
    ∀ (i : Fin N) (c : ∀ k, ι k), segreVec y c ≠ 0 →
      ∃ (dl dm : Option K → ℕ) (l μ : MRing (bundleIdx ι M) F) (m : K → ℕ),
        μ = ∏ k, (X ⟨some k, c k⟩ : MRing (bundleIdx ι M) F) ^ m k ∧
        IsMultiHomog l dl ∧ IsMultiHomog μ dm ∧
        (fun o => (dl o : ℤ) - dm o) = zetaDeg + liftDeg (b i - a) ∧
        eval₂ ((algebraMap Ω Φ).comp (algebraMap F Ω)) (projCoord y w φ (truncCoord t ((i : ℕ) + 1))) l =
          t i * eval₂ ((algebraMap Ω Φ).comp (algebraMap F Ω))
            (projCoord y w φ (truncCoord t ((i : ℕ) + 1))) μ ∧
        ∀ q ∈ projIdeal F y w φ (truncCoord t i), ∃ n : ℕ,
          (∏ k, (X ⟨some k, c k⟩ : MRing (bundleIdx ι M) F)) ^ n * q ∈
            projIdeal F y w φ (truncCoord t ((i : ℕ) + 1)) ⊔ Ideal.span {l}
end
end GroundTheory.Heights₂.Heights.NumbersDVR


