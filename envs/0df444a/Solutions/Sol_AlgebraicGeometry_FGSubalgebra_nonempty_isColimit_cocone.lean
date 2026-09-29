-- Prove2me | solution 1 for AlgebraicGeometry.FGSubalgebra.nonempty_isColimit_cocone
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/39fc82d5-432e-56ec-b5bc-099dcc7046e3

import Definitions.Def_AlgebraicGeometry_FGSubalgebra
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_FGSubalgebra_nonempty_isColimit_cocone

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem solution
    (R : Type u) [CommRing R] (A : Type u) [CommRing A] [Algebra R A] :
    Nonempty (IsColimit (FGSubalgebra.cocone R A)) := by
  have : ReflectsColimit (FGSubalgebra.diagram R A) (CategoryTheory.forget CommRingCat.{u}) :=
    reflectsColimit_of_reflectsIsomorphisms _ _
  refine ⟨isColimitOfReflects (CategoryTheory.forget CommRingCat.{u}) ?_⟩
  refine Types.FilteredColimit.isColimitOf _ _ ?_ ?_
  · rintro (x : A)
    exact ⟨⟨Algebra.adjoin R {x}, {x}, by rw [Finset.coe_singleton]⟩,
      (⟨x, Algebra.self_mem_adjoin_singleton R x⟩ : Algebra.adjoin R {x}), rfl⟩
  · rintro A₀ A₁ (x₀ : A₀.1) (x₁ : A₁.1) (h : (x₀ : A) = x₁)
    refine ⟨⟨A₀.1 ⊔ A₁.1, A₀.2.sup A₁.2⟩, homOfLE (le_sup_left : A₀.1 ≤ A₀.1 ⊔ A₁.1),
      homOfLE (le_sup_right : A₁.1 ≤ A₀.1 ⊔ A₁.1), ?_⟩
    change (Subalgebra.inclusion (le_sup_left : A₀.1 ≤ A₀.1 ⊔ A₁.1) x₀ : ↥(A₀.1 ⊔ A₁.1)) =
      Subalgebra.inclusion (le_sup_right : A₁.1 ≤ A₀.1 ⊔ A₁.1) x₁
    exact Subtype.ext h

end S_AlgebraicGeometry_FGSubalgebra_nonempty_isColimit_cocone
end P2MW
export P2MW.S_AlgebraicGeometry_FGSubalgebra_nonempty_isColimit_cocone (solution)
