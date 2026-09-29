-- Prove2me | solution 1 for AlgebraicGeometry.smoothOfRelativeDimension_of_smooth_of_forall_fiber
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/ad3a0d02-4933-5dc3-992c-1e5256dad615

import Mathlib
import Theorems.Thm_AlgebraicGeometry_eq_of_isStandardSmoothOfRelativeDimension_appLE_of_smoothOfRelativeDimension
import Theorems.Thm_AlgebraicGeometry_exists_isStandardSmoothOfRelativeDimension_appLE_fiberToSpecResidueField
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_smoothOfRelativeDimension_of_smooth_of_forall_fiber

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem solution
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Smooth f] (n : ℕ)
    (h : ∀ y : Y, SmoothOfRelativeDimension n (f.fiberToSpecResidueField y)) :
    SmoothOfRelativeDimension n f := by
  refine ⟨fun x => ?_⟩
  obtain ⟨U, hU, V, hV, hxV, e, hstd⟩ := Smooth.exists_isStandardSmooth f x

  obtain ⟨m, hm⟩ : ∃ m : ℕ, (f.appLE U V e).hom.IsStandardSmoothOfRelativeDimension m := by
    letI := (f.appLE U V e).hom.toAlgebra
    have : Algebra.IsStandardSmooth Γ(Y, U) Γ(X, V) := hstd
    obtain ⟨ι, σ, _, _, ⟨P⟩⟩ := this
    exact ⟨P.dimension, P.isStandardSmoothOfRelativeDimension rfl⟩

  obtain ⟨U', V', hV', hxV', e', hm'⟩ :=
    AlgebraicGeometry.exists_isStandardSmoothOfRelativeDimension_appLE_fiberToSpecResidueField f x m U hU V hV hxV e hm
  have hmn : m = n :=
    AlgebraicGeometry.eq_of_isStandardSmoothOfRelativeDimension_appLE_of_smoothOfRelativeDimension
      (f.fiberToSpecResidueField (f.base x)) n (h (f.base x)) m U' V' hV' (f.asFiber x) hxV' e' hm'
  subst hmn
  exact ⟨U, hU, V, hV, hxV, e, hm⟩

end S_AlgebraicGeometry_smoothOfRelativeDimension_of_smooth_of_forall_fiber
end P2MW
export P2MW.S_AlgebraicGeometry_smoothOfRelativeDimension_of_smooth_of_forall_fiber (solution)
