-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsRootsNear
-- name    : GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsRootsNear
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:56:30.743358+00:00
-- url     : https://prove2.me/theorems/90d6ad97-a5bf-43ff-b045-a5b50608b809
-- title:
--   Statements Roots Near
-- statement:
--   Definitions and structural lemmas for Statements Roots Near, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/StatementsRootsNear.lean

import Mathlib
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
open MvPolynomial Filter Topology
def RootsNear.Statement : Prop :=
  ∀ (e : ℕ) (G : Polynomial (MvPolynomial (Fin e) ℚ)), G.Monic →
    ∀ (y₀ : Fin e → ℂ) (t₀ : ℂ), G.eval₂ (aeval y₀).toRingHom t₀ = 0 →
      ∀ ε > 0, ∀ᶠ y in 𝓝 y₀, ∃ t : ℂ, G.eval₂ (aeval y).toRingHom t = 0 ∧ dist t t₀ < ε
end GroundTheory.Heights₂.Heights.HilbertSamuel


