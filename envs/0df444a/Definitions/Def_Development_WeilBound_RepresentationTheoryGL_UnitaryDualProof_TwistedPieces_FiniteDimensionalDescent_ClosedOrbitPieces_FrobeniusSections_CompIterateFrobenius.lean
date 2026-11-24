-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_TwistedPieces_FiniteDimensionalDescent_ClosedOrbitPieces_FrobeniusSections_CompIterateFrobenius
-- name    : Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_TwistedPieces_FiniteDimensionalDescent_ClosedOrbitPieces_FrobeniusSections_CompIterateFrobenius
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T03:56:06.759086+00:00
-- url     : https://prove2.me/theorems/1fd1e348-bb02-468e-ae0d-adba9d8a9188
-- title:
--   Comp Iterate Frobenius
-- statement:
--   Definitions and structural lemmas for Comp Iterate Frobenius, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/TwistedPieces/FiniteDimensionalDescent/ClosedOrbitPieces/FrobeniusSections/CompIterateFrobenius.lean

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
open Module Polynomial IntermediateField
def Pj (E : Type*) [Field E] (p : ℕ) [Fact p.Prime] [CharP E p] (j : ℕ) : Subfield E :=
  (iterateFrobenius E p j).fieldRange
section Frob
variable {E : Type*} [Field E] (p : ℕ) [hp : Fact p.Prime] [CharP E p]
end Frob
end PositivityTheory.RgUd.TP.Desc.Piece.PSect


