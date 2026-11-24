-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsRootsBounded
-- name    : GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsRootsBounded
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:57:03.183059+00:00
-- url     : https://prove2.me/theorems/3dcc4f10-748e-45fa-bd81-4fd4914bc574
-- title:
--   Statements Roots Bounded
-- statement:
--   Definitions and structural lemmas for Statements Roots Bounded, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/StatementsRootsBounded.lean

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
def RootsBounded.Statement : Prop :=
  ∀ (e : ℕ) (G : Polynomial (MvPolynomial (Fin e) ℚ)), G.Monic → ∀ y₀ : Fin e → ℂ,
    ∃ R : ℝ, ∀ᶠ y in 𝓝 y₀, ∀ t : ℂ, G.eval₂ (aeval y).toRingHom t = 0 → ‖t‖ ≤ R
end GroundTheory.Heights₂.Heights.HilbertSamuel


