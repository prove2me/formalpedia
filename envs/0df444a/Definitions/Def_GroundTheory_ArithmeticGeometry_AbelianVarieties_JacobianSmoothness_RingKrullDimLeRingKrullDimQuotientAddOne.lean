-- Prove2me | Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
-- name    : GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T01:43:49.920397+00:00
-- url     : https://prove2.me/theorems/90758278-39dd-43d7-b3e1-d7a97f6b3a08
-- title:
--   Ring Krull Dim Le Ring Krull Dim Quotient Add One
-- statement:
--   Definitions and structural lemmas for Ring Krull Dim Le Ring Krull Dim Quotient Add One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/JacobianSmoothness/RingKrullDimLeRingKrullDimQuotientAddOne.lean

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_Dimension
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Arith.Abelian.Jacobian
open Algebra Cardinal
universe u
section Normalization
variable (k : Type u) [Field k] {A : Type u} [CommRing A] [Algebra k A]
variable [Algebra.FiniteType k A]
end Normalization
section Drop
variable {A : Type u} [CommRing A] [IsDomain A]
end Drop
section Hypersurface
variable (k : Type u) [Field k]
end Hypersurface
section Formula
variable (k : Type u) [Field k] {A : Type u} [CommRing A] [IsDomain A] [Algebra k A]
  [Algebra.FiniteType k A]
end Formula
end GroundTheory.Arith.Abelian.Jacobian


