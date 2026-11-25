-- Prove2me | Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_Dimension
-- name    : GroundTheory_ArithmeticGeometry_ToricVarieties_Dimension
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T01:35:46.322779+00:00
-- url     : https://prove2.me/theorems/30f7648e-9398-4944-a123-e67d4fc6f1f3
-- title:
--   Dimension
-- statement:
--   Definitions and structural lemmas for Dimension, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/ToricVarieties/Dimension.lean

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_Normal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Arith.Toric
universe u
open Module PointedCone TensorProduct AddMonoidAlgebra AlgebraicGeometry Algebra
section IntegralDim
variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] [Algebra.IsIntegral R A]
end IntegralDim
section Trdeg
variable {k G : Type u} [CommRing k] [IsDomain k] [AddCommGroup G] [Module.Free ℤ G]
variable [Module.Finite ℤ G]
end Trdeg
section Dim
variable {k N : Type u} [Field k] [AddCommGroup N] [Module.Free ℤ N] [Module.Finite ℤ N]
end Dim
end GroundTheory.Arith.Toric


