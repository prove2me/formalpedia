-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_TwistedPieces_FiniteDimensionalDescent_ClosedOrbitPieces_FrobeniusSections_RqLift
-- name    : Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_TwistedPieces_FiniteDimensionalDescent_ClosedOrbitPieces_FrobeniusSections_RqLift
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:05:12.341521+00:00
-- url     : https://prove2.me/theorems/57e0ace8-ca63-4700-a9dc-edf35a118e01
-- title:
--   Rq Lift
-- statement:
--   Definitions and structural lemmas for Rq Lift, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/TwistedPieces/FiniteDimensionalDescent/ClosedOrbitPieces/FrobeniusSections/RqLift.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PositivityTheory.RgUd.TP.Desc.Piece.PSect
open Module Polynomial
variable {k A : Type*} [Field k] [CommRing A] [Algebra k A]
def Iq (A : Type*) [CommRing A] [Algebra k A] (χ : k[X]) (q : ℕ) : Ideal A[X] :=
  Ideal.span {χ.map (algebraMap k A)} ⊔
    Ideal.span {y | ∃ r ∈ (Ideal.span {χ.map (algebraMap k A)}).radical, y = r ^ q}
abbrev Rq (A : Type*) [CommRing A] [Algebra k A] (χ : k[X]) (q : ℕ) : Type _ := A[X] ⧸ Iq A χ q
end PositivityTheory.RgUd.TP.Desc.Piece.PSect


