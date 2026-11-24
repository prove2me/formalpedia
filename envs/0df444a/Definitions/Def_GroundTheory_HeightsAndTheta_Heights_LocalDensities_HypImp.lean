-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_HypImp
-- name    : GroundTheory_HeightsAndTheta_Heights_LocalDensities_HypImp
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:22:41.879802+00:00
-- url     : https://prove2.me/theorems/affa9a47-5c11-4094-9a58-cbc2330a982f
-- title:
--   Hyp Imp
-- statement:
--   Definitions and structural lemmas for Hyp Imp, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/HypImp.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_LeviFormGbPotOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB
open MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo
def CoverMass2.Hyp {D : ℕ} (M Z : Set (Fin D → ℂ)) (z : (Fin D → ℂ) → (Fin D → ℂ)) (δ : ℕ) :
    Prop :=
  IsOpen M ∧ volume Z = 0 ∧ DifferentiableOn ℂ z M ∧ Set.MapsTo z M Zᶜ ∧
    IsCoveringMapOn (fun x : M => z x) Zᶜ ∧ ∀ w ∉ Z, Set.encard {x | x ∈ M ∧ z x = w} = δ
def CoverMass2.Statement : Prop :=
  ∀ (D : ℕ) (M Z : Set (Fin D → ℂ)) (z : (Fin D → ℂ) → (Fin D → ℂ)) (δ : ℕ),
    CoverMass2.Hyp M Z z δ →
      ∫⁻ x in M, ENNReal.ofReal (topDens (fun y => Real.log (1 + ∑ i, ‖z y i‖ ^ 2)) x) = δ
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB


