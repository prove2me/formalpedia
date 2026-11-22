-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MemIntegralGlOfMiddleBlock
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_MemIntegralGlOfMiddleBlock
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:29:06.10702+00:00
-- url     : https://prove2.me/theorems/c91db176-1673-45ca-a7d1-619716a74626
-- title:
--   Mem Integral Gl Of Middle Block
-- statement:
--   Definitions and structural lemmas for Mem Integral Gl Of Middle Block, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MemIntegralGlOfMiddleBlock.lean

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.FourierDecayAlt.P.S3x3
open Matrix Formalism.FourierDecayAlt.S3
open Formalism.DoubleCosetMeasures (IsUpUni upUniG)
section Blocks
variable {A : Type} {r k : ℕ}
variable [CommRing A]
end Blocks
section Alg
variable {A : Type} [CommRing A] {r k : ℕ}
end Alg
section Integral
variable (o : Type) [CommRing o] {k0 : Type} [Field k0] [Algebra o k0]
variable [IsFractionRing o k0]
variable [IsLocalRing o]
end Integral
section Counting
variable {A : Type} [CommRing A] {r k : ℕ}
end Counting
section Levels
variable (o : Type) [CommRing o] [IsLocalRing o] {r k : ℕ} (L : Levels o r k)
end Levels
end Formalism.FourierDecayAlt.P.S3x3
namespace Formalism.FourierDecayAlt.P
end Formalism.FourierDecayAlt.P


