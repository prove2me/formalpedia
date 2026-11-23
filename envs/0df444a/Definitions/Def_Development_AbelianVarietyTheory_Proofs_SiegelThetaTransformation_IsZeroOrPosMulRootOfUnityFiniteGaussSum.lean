-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_IsZeroOrPosMulRootOfUnityFiniteGaussSum
-- name    : Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_IsZeroOrPosMulRootOfUnityFiniteGaussSum
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T08:37:45.273921+00:00
-- url     : https://prove2.me/theorems/d65354cd-9ebd-461f-aa52-bbb85da06b86
-- title:
--   Is Zero Or Pos Mul Root Of Unity Finite Gauss Sum
-- statement:
--   Definitions and structural lemmas for Is Zero Or Pos Mul Root Of Unity Finite Gauss Sum, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/IsZeroOrPosMulRootOfUnityFiniteGaussSum.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IntMIffInt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW GlobalTheory.Phase
open scoped ComplexConjugate Real
namespace GlobalTheory.Phase.GaussSum
def quat {M : Type} [AddCommGroup M] (a b c d : ℤ) (x : Fin 4 → M) : Fin 4 → M :=
  ![a • x 0 + (-b) • x 1 + (-c) • x 2 + (-d) • x 3,
    b • x 0 + a • x 1 + (-d) • x 2 + c • x 3,
    c • x 0 + d • x 1 + a • x 2 + (-b) • x 3,
    d • x 0 + (-c) • x 1 + b • x 2 + a • x 3]
end GlobalTheory.Phase.GaussSum


