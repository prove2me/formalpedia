-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsBisBis
-- name    : GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsBisBis
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:58:13.138617+00:00
-- url     : https://prove2.me/theorems/f252b9e2-385c-4d11-86fb-31dce13fc618
-- title:
--   Imports Bis Bis
-- statement:
--   Definitions and structural lemmas for Imports Bis Bis, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/ImportsBisBis.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsSegreFlagCut
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
def SegreFlagDegreeZero.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (Ω : Type) [Field Ω] [Algebra O Ω]
      (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (y : (Σ k, ι k) → Ω) (d : ℕ), IsModelOver (pointIdeal O y) d →
    ∀ (N : ℕ) (E : Type) [AddCommGroup E] [Module Ω E]
      (B B' : ChartBundle O (segreVec y) N E), SameGenericFibre ϖ B B' →
    ∀ (w w' : Module.Basis (Fin N) Ω E) (x x' : Fin N → K → ℤ) (f g : Fin N → MRing ι O),
      IsFlagPair ϖ y B B' w w' x x' f g →
    ∀ (M M' : ℕ) (a₀ a₀' : K → ℤ) (φ : Fin M → Module.Dual Ω E) (φ' : Fin M' → Module.Dual Ω E),
      IsTwistedDualGens y B a₀ φ → IsTwistedDualGens y B' a₀' φ' →
    ∀ (Φ : Type) [Field Φ] [Algebra Ω Φ] [Algebra O Φ] [IsScalarTower O Ω Φ]
      (e : Module.Basis (Fin N) Ω E) (t : Fin N → Φ), AlgebraicIndependent Ω t →
    ∀ k : ℕ, k < N →
      ∃ f₃ g₃ : MRing (bundleIdx (bundleIdx ι M) M') O,
        IsVerticalDivisor (pointIdeal O (flagClosurePt y w e φ φ' t (k + 1))) ϖ (zetaFirst a₀ - zetaSecond a₀') f₃ g₃ ∧
        aeval (flagClosurePt y w e φ φ' t (k + 1)) f₃ = aeval (flagClosurePt y w e φ φ' t (k + 1)) g₃ ∧
        (0 < k → f₃ ∉ pointIdeal O (flagClosurePt y w e φ φ' t k) ∧ g₃ ∉ pointIdeal O (flagClosurePt y w e φ φ' t k) ∧
          aeval (flagClosurePt y w e φ φ' t k) f₃ = aeval (flagClosurePt y w e φ φ' t k) g₃)
end
end GroundTheory.Heights₂.Heights.NumbersDVR


