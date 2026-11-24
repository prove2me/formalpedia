-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_IsVBOnDualAndBidual
-- name    : Development_AutomorphicSpectrum_Proofs_GeometryProofs_IsVBOnDualAndBidual
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:31:58.018124+00:00
-- url     : https://prove2.me/theorems/bd2a8e6a-834c-40c6-9054-5243668fc9e0
-- title:
--   Is VBOn Dual And Bidual
-- statement:
--   Definitions and structural lemmas for Is VBOn Dual And Bidual, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GeometryProofs/IsVBOnDualAndBidual.lean

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_EtaleLocalizationAtPrimeTensorOfLowHeight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar
namespace GlobalTheory.CompanionTheory.Ar.LatDual
variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {E : Type} [AddCommGroup E] [Module Ω E]
end GlobalTheory.CompanionTheory.Ar.LatDual
namespace GlobalTheory.CompanionTheory.Ar
open LatDual
end GlobalTheory.CompanionTheory.Ar


