-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_NormSmulLeOneOfPrimitiveBoundedPowers
-- name    : Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_NormSmulLeOneOfPrimitiveBoundedPowers
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:05:41.492184+00:00
-- url     : https://prove2.me/theorems/a0f9414a-bb7b-4ae9-b934-a48f01d6e7be
-- title:
--   Norm Smul Le One Of Primitive Bounded Powers
-- statement:
--   Definitions and structural lemmas for Norm Smul Le One Of Primitive Bounded Powers, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/NormSmulLeOneOfPrimitiveBoundedPowers.lean

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
namespace GlobalTheory.NearlyPrimitive
open Finset Filter Topology
section Factorial
variable {C : Type} [NormedField C] [IsUltrametricDist C]
end Factorial
def dpow (C : Type) [Field C] {B : Type} [CommRing B] [Algebra C B] (n : ℕ) (x : B) : B :=
  ((n.factorial : C))⁻¹ • x ^ n
end GlobalTheory.NearlyPrimitive


