-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StIntClosureLocFinite
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_StIntClosureLocFinite
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:29:14.216394+00:00
-- url     : https://prove2.me/theorems/53dba331-463c-465d-ae1f-52657631d5ef
-- title:
--   St Int Closure Loc Finite
-- statement:
--   Definitions and structural lemmas for St Int Closure Loc Finite, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/StIntClosureLocFinite.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Heights₂.Heights.Inter
def IntClosureLocFinite.Statement : Prop :=
  ∀ (F L : Type) [Field F] [Field L] (φ : F →+* L) (S : Finset L), Subfield.closure (S : Set L) = ⊤ →
    ∀ (A : Subring F) (T : Finset F), Subring.closure (T : Set F) ≤ A →
    (∀ z ∈ A, ∃ b ∈ Subring.closure (T : Set F), ∃ c ∈ Subring.closure (T : Set F),
      c ≠ 0 ∧ c⁻¹ ∈ A ∧ z * c = b) →
    letI := (φ.comp A.subtype).toAlgebra
    letI : Module A L := Algebra.toModule
    ∃ t : Finset L, ∀ x : L, IsIntegral A x → x ∈ Submodule.span A (t : Set L)
end GroundTheory.Heights₂.Heights.Inter


