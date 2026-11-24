-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_ImportsSide
-- name    : GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_ImportsSide
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:05:29.859796+00:00
-- url     : https://prove2.me/theorems/c3a1272b-2b63-4cfe-be2a-6d8ee3e88e01
-- title:
--   Imports Side
-- statement:
--   Definitions and structural lemmas for Imports Side, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/ImportsSide.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_GeneratedModOfSubsingleton
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
noncomputable section
def H1GenerationDevissage.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type)
    [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] (V : Ideal (MRingOver S ι)) (N : K → ℤ),
    IsNoetherianRing S → (∀ P : Ideal (MRingOver S ι), IsMultiProjPrime P → V ≤ P → H1GenAmple S P N) →
    H1GenAmple S V N
end
end GroundTheory.Heights₂.Heights.HilbertSamuel


