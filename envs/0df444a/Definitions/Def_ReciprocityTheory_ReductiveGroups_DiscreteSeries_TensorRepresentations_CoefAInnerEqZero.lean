-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CoefAInnerEqZero
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CoefAInnerEqZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:32:28.416171+00:00
-- url     : https://prove2.me/theorems/ae807243-c101-4046-9706-6f72a34a0647
-- title:
--   Coef AInner Eq Zero
-- statement:
--   Definitions and structural lemmas for Coef AInner Eq Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/CoefAInnerEqZero.lean

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
open Finset
namespace ReciprocityTheory.ChartRestriction.DS
section Spec
variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X]
end Spec
section Rep
variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X]
variable {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℂ Y]
def CoefLocFin (T : X →ₗ[ℂ] X) (M' : Submodule ℂ X) : Prop :=
  ∀ y ∈ M', ∃ F : Submodule ℂ X, FiniteDimensional ℂ F ∧ F ≤ M' ∧ (∀ x ∈ F, T x ∈ F) ∧ y ∈ F
end Rep
end ReciprocityTheory.ChartRestriction.DS


