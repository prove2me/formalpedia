-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_WeightCongruences_NormRootOfUnityQuadraticSubfield
-- name    : Development_AutomorphicArithmetic_WeightCongruences_NormRootOfUnityQuadraticSubfield
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:33:46.091746+00:00
-- url     : https://prove2.me/theorems/a9f839a5-a41e-4bf2-b0d6-7c013f936d99
-- title:
--   Norm Root Of Unity Quadratic Subfield
-- statement:
--   Definitions and structural lemmas for Norm Root Of Unity Quadratic Subfield, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/WeightCongruences/NormRootOfUnityQuadraticSubfield.lean

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ReprMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField
namespace UpperTheory.RootOfUnityNormQuadraticSubfield
open Polynomial
section
variable {E : Type} [Field E] [NumberField E] (s : E) (d : ℕ) (hd : d.Prime) (h3 : 3 < d)
  (hs : s ^ 2 = -(d : E))
include hd h3 hs
end
end UpperTheory.RootOfUnityNormQuadraticSubfield


