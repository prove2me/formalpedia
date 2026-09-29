-- Prove2me | solution 1 for AlgebraicGeometry.isIso_and_adicThickening_comp_eq_of_comap_eq_ker_of_comp_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/502e0652-83ba-5ae0-9181-c1a513b6f966

import Mathlib
import Definitions.Def_AlgebraicGeometry_AdicThickening
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_isIso_and_adicThickening_comp_eq_of_comap_eq_ker_of_comp_eq

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

theorem solution
    {R : Type u} [CommRing R] (I : Ideal R) {X Y : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) (g : Y ⟶ Spec (CommRingCat.of R))
    (J : (pullback f g).IdealSheafData)
    (γ : ∀ n : ℕ, adicThickening f I n ⟶ adicThickening (pullback.fst f g ≫ f) I n)
    (hγ : ∀ n : ℕ, IsClosedImmersion (γ n))
    (hγJ : ∀ n : ℕ, J.comap (adicThickeningι (pullback.fst f g ≫ f) I n) = (γ n).ker)
    (hγX : ∀ n : ℕ, γ n ≫ adicThickeningι (pullback.fst f g ≫ f) I n ≫ pullback.fst f g = adicThickeningι f I n)
    (n : ℕ)
    (ζ : adicThickening (J.subschemeι ≫ pullback.fst f g ≫ f) I n ⟶ adicThickening f I n)
    (hζ : ζ ≫ adicThickeningι f I n = adicThickeningι (J.subschemeι ≫ pullback.fst f g ≫ f) I n ≫ J.subschemeι ≫ pullback.fst f g) :
    IsIso ζ ∧ adicThickeningι (J.subschemeι ≫ pullback.fst f g ≫ f) I n ≫ J.subschemeι =
      ζ ≫ γ n ≫ adicThickeningι (pullback.fst f g ≫ f) I n := by
  haveI := hγ n

  have hw : (adicThickeningι (J.subschemeι ≫ pullback.fst f g ≫ f) I n ≫ J.subschemeι) ≫ (pullback.fst f g ≫ f) =
      adicThickeningToBase (J.subschemeι ≫ pullback.fst f g ≫ f) I n ≫ adicThickeningBase I n := by
    rw [Category.assoc, adicThickeningι_comp]
  obtain ⟨θ, hθdef⟩ : ∃ θ : adicThickening (J.subschemeι ≫ pullback.fst f g ≫ f) I n ⟶ adicThickening (pullback.fst f g ≫ f) I n,
      θ = pullback.lift (adicThickeningι (J.subschemeι ≫ pullback.fst f g ≫ f) I n ≫ J.subschemeι)
        (adicThickeningToBase (J.subschemeι ≫ pullback.fst f g ≫ f) I n) hw := ⟨_, rfl⟩
  have hθ : θ ≫ adicThickeningι (pullback.fst f g ≫ f) I n = adicThickeningι (J.subschemeι ≫ pullback.fst f g ≫ f) I n ≫ J.subschemeι := by
    rw [hθdef]; exact pullback.lift_fst _ _ _

  have H2 : (γ n).ker ≤ θ.ker := by
    rw [← hγJ n]
    refine Scheme.IdealSheafData.le_map_iff_comap_le.mp ?_
    rw [Scheme.IdealSheafData.map_ker, hθ]
    conv_lhs => rw [← J.ker_subschemeι]
    exact Scheme.Hom.le_ker_comp _ _
  have hζ' : IsClosedImmersion.lift (γ n) θ H2 = ζ := by
    rw [← cancel_mono (adicThickeningι f I n), hζ, ← hγX n, IsClosedImmersion.lift_fac_assoc, reassoc_of% hθ]
  have hfac : adicThickeningι (J.subschemeι ≫ pullback.fst f g ≫ f) I n ≫ J.subschemeι =
      ζ ≫ γ n ≫ adicThickeningι (pullback.fst f g ≫ f) I n := by
    rw [← hθ, ← hζ', IsClosedImmersion.lift_fac_assoc]
  refine ⟨?_, hfac⟩

  have H6 : J.subschemeι.ker ≤ (γ n ≫ adicThickeningι (pullback.fst f g ≫ f) I n).ker := by
    rw [J.ker_subschemeι, ← Scheme.IdealSheafData.map_ker]
    exact Scheme.IdealSheafData.le_map_iff_comap_le.mpr (hγJ n).le
  have hwξ : IsClosedImmersion.lift J.subschemeι _ H6 ≫ (J.subschemeι ≫ pullback.fst f g ≫ f) =
      adicThickeningToBase f I n ≫ adicThickeningBase I n := by
    rw [IsClosedImmersion.lift_fac_assoc, Category.assoc, reassoc_of% (hγX n), adicThickeningι_comp]
  obtain ⟨ξ, hξdef⟩ : ∃ ξ : adicThickening f I n ⟶ adicThickening (J.subschemeι ≫ pullback.fst f g ≫ f) I n,
      ξ = pullback.lift (IsClosedImmersion.lift J.subschemeι _ H6) (adicThickeningToBase f I n) hwξ := ⟨_, rfl⟩
  have hξ : ξ ≫ adicThickeningι (J.subschemeι ≫ pullback.fst f g ≫ f) I n = IsClosedImmersion.lift J.subschemeι _ H6 := by
    rw [hξdef]; exact pullback.lift_fst _ _ _
  refine ⟨⟨ξ, ?_, ?_⟩⟩
  · rw [← cancel_mono (adicThickeningι (J.subschemeι ≫ pullback.fst f g ≫ f) I n), ← cancel_mono J.subschemeι, Category.id_comp,
      Category.assoc, Category.assoc, reassoc_of% hξ, IsClosedImmersion.lift_fac, ← hfac]
  · rw [← cancel_mono (adicThickeningι f I n), Category.id_comp, Category.assoc, hζ, reassoc_of% hξ,
      IsClosedImmersion.lift_fac_assoc, Category.assoc, hγX n]

end S_AlgebraicGeometry_isIso_and_adicThickening_comp_eq_of_comap_eq_ker_of_comp_eq
end P2MW
export P2MW.S_AlgebraicGeometry_isIso_and_adicThickening_comp_eq_of_comap_eq_ker_of_comp_eq (solution)
