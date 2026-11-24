-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsBisRest
-- name    : GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsBisRest
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:33:08.723161+00:00
-- url     : https://prove2.me/theorems/e6da4294-8041-4fb6-9b42-02fbf5db68bc
-- title:
--   Imports Bis Rest
-- statement:
--   Definitions and structural lemmas for Imports Bis Rest, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/ImportsBisRest.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_BundleObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_InstFintypeSumElim
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
open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle)
universe u v w
def FlagPairCharacterisation.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type v) [Field Ω]
    [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (y : (Σ k, ι k) → Ω) (N : ℕ) (E : Type w) [AddCommGroup E] [Module Ω E]
    (B B' : ChartBundle O (segreVec y) N E) (ϖ : O), Irreducible ϖ →
    IsMultiProjPrime (pointIdeal O y) →
    (∀ (w w' : Module.Basis (Fin N) Ω E) (x x' : Fin N → K → ℤ) (f g : Fin N → MRing ι O),
      IsFlagPair ϖ y B B' w w' x x' f g ↔
        ∃ F : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.FlagPair O y B B', F.gen = w ∧ F.gen' = w' ∧ F.deg = x ∧
          F.deg' = x' ∧ F.f = f ∧ F.g = g) ∧
    ((∃ c, segreVec y c ≠ 0) → ∀ F : IndefiniteRowSideFullHecke.NumbersDVR.Bundles.FlagPair O y B B',
      LinearIndependent Ω F.gen ∧ LinearIndependent Ω F.gen')
end GroundTheory.Heights₂.Heights.NumbersDVR


