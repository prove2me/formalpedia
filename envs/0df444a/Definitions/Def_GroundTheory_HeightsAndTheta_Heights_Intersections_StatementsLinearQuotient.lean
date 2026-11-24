-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsLinearQuotient
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsLinearQuotient
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:21:37.130566+00:00
-- url     : https://prove2.me/theorems/b59124da-6390-4840-a022-d1fa56689972
-- title:
--   Statements Linear Quotient
-- statement:
--   Definitions and structural lemmas for Statements Linear Quotient, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/StatementsLinearQuotient.lean

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
noncomputable section
namespace GroundTheory.Heights₂.Heights.Inter
open MvPolynomial
def LinearQuotient.Statement : Prop :=
  ∀ (F : Type) [Field F] (σ : Type) [Fintype σ] (S : Set (MvPolynomial σ F)),
    (∀ f ∈ S, f.IsHomogeneous 1) →
    ∃ (r : ℕ) (φ : MvPolynomial σ F →ₐ[F] MvPolynomial (Fin r) F), Function.Surjective φ ∧
      RingHom.ker φ = Ideal.span S ∧ ∀ s, (φ (X s)).IsHomogeneous 1
end GroundTheory.Heights₂.Heights.Inter


