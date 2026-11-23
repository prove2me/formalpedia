-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoAppTopOfIsPullbackOfSurjective
-- name    : Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoAppTopOfIsPullbackOfSurjective
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:34:22.463374+00:00
-- url     : https://prove2.me/theorems/ccc131e7-b655-4209-ad1a-ee267b335418
-- title:
--   Is Iso App Top Of Is Pullback Of Surjective
-- statement:
--   Definitions and structural lemmas for Is Iso App Top Of Is Pullback Of Surjective, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoAppTopOfIsPullbackOfSurjective.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry TensorProduct Opposite
universe u
namespace GlobalTheory
namespace ProperFunctions
section Algebra
end Algebra
section BaseChange
variable {X Y S T : Scheme.{u}} {f : T ⟶ S} {g : Y ⟶ X} {p : X ⟶ S} {q : Y ⟶ T}
theorem le_preimage_top (p : X ⟶ S) (U : X.Opens) : U ≤ p ⁻¹ᵁ ⊤ := le_top
end BaseChange
section Field
variable {X S : Scheme.{u}}
end Field
section Section
variable {X S : Scheme.{u}}
end Section
section Main
variable {X Y S T : Scheme.{u}}
end Main
section Limit
variable {X Y S T : Scheme.{u}}
end Limit
section Summary
end Summary
end ProperFunctions
end GlobalTheory


