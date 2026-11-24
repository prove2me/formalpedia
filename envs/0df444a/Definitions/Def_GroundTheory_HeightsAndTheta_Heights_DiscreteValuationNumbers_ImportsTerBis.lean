-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsTerBis
-- name    : GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsTerBis
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:33:58.592638+00:00
-- url     : https://prove2.me/theorems/1190f092-7ddb-418e-8782-d275ee5dc6a2
-- title:
--   Imports Ter Bis
-- statement:
--   Definitions and structural lemmas for Imports Ter Bis, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/ImportsTerBis.lean

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
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle)
universe u v w
def GradedFrameCharacterisation.Statement : Prop :=
  ∀ (o : Type u) [CommRing o] (Ω : Type v) [Field Ω] [Algebra o Ω] (K : Type) [Fintype K]
    (ι : K → Type) [∀ k, Fintype (ι k)] (y : (Σ k, ι k) → Ω) (N : ℕ) (E : Type w)
    [AddCommGroup E] [Module Ω E] (B : ChartBundle o (segreVec y) N E)
    (w : Module.Basis (Fin N) Ω E) (b : Fin N → K → ℤ),
    IsFlagFrame y B w b ↔ IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsGradedFrame o y B
      (fun i => Submodule.span Ω (w '' {j | (j : ℕ) < i})) b w
end GroundTheory.Heights₂.Heights.NumbersDVR


