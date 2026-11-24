-- Prove2me | Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_ConstantCodimension
-- name    : Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_ConstantCodimension
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:12:11.8104+00:00
-- url     : https://prove2.me/theorems/f666b4e8-1484-4951-9867-47c843795737
-- title:
--   Constant Codimension
-- statement:
--   Definitions and structural lemmas for Constant Codimension, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/ConstantCodimension.lean

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
noncomputable section
namespace FunctorialResolution.EmbeddedResolution
def HasEtaleCoordCodim {X X' : Scheme.{u}} {k : Type u} [Field k]
    (p : X' ⟶ Spec (CommRingCat.of k)) (τ : X ⟶ X') (c : ℕ) : Prop :=
  ∀ x : X, ∃ (U : X'.Opens) (_ : τ.base x ∈ U) (m : ℕ) (ch : EtaleChart p U m)
    (S : Finset (Fin m)), S.card = c ∧ restrictIdeal τ.ker U = ch.coordIdeal S
end FunctorialResolution.EmbeddedResolution


