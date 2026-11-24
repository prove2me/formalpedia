-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_TwistedPieces_FiniteDimensionalDescent_ClosedOrbitPieces_FrobeniusSections_MemPw
-- name    : Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_TwistedPieces_FiniteDimensionalDescent_ClosedOrbitPieces_FrobeniusSections_MemPw
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:06:26.618493+00:00
-- url     : https://prove2.me/theorems/c42aaf8e-4520-4e05-b873-a15d72bd31bb
-- title:
--   Mem Pw
-- statement:
--   Definitions and structural lemmas for Mem Pw, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/TwistedPieces/FiniteDimensionalDescent/ClosedOrbitPieces/FrobeniusSections/MemPw.lean

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
open Module
def Tw (k : Type*) (_p _c : ℕ) : Type _ := k
variable {k : Type*} [Field k]
instance (p c : ℕ) : Field (Tw k p c) := inferInstanceAs (Field k)
instance (p c : ℕ) [Fact p.Prime] [CharP k p] : Algebra k (Tw k p c) :=
  RingHom.toAlgebra (show k →+* Tw k p c from iterateFrobenius k p c)
def Pw (k B : Type*) [Field k] [CommRing B] [Algebra k B] (q : ℕ) : Subalgebra k B :=
  Algebra.adjoin k (Set.range fun b : B => b ^ q)
end PositivityTheory.RgUd.TP.Desc.Piece.PSect


