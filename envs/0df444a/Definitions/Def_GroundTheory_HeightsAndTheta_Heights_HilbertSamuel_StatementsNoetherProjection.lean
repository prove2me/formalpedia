-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsNoetherProjection
-- name    : GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsNoetherProjection
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:55:52.498808+00:00
-- url     : https://prove2.me/theorems/add65d13-20db-40d8-80db-bf784c0f04b5
-- title:
--   Statements Noether Projection
-- statement:
--   Definitions and structural lemmas for Statements Noether Projection, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/StatementsNoetherProjection.lean

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
open MvPolynomial
def NoetherProjection.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (P : Ideal (MvPolynomial σ ℚ)), P ≠ ⊤ →
    ∃ (e : ℕ) (ℓ : Fin e → MvPolynomial σ ℚ),
      (∀ q : MvPolynomial (Fin e) ℚ, aeval ℓ q ∈ P → q = 0) ∧
      ∀ g : MvPolynomial σ ℚ, ∃ p : Polynomial (MvPolynomial (Fin e) ℚ),
        p.Monic ∧ p.eval₂ (aeval ℓ).toRingHom g ∈ P
end GroundTheory.Heights₂.Heights.HilbertSamuel


