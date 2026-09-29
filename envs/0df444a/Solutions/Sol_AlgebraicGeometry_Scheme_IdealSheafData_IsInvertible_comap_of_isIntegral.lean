-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible.comap_of_isIntegral
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/6af4422e-e4c0-565b-a0af-165c718d0826

import Mathlib
import Definitions.Def_AlgebraicCurve_RelCartier
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_ideal_comap_of_le
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_comap_of_isIntegral

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

theorem solution
    {X Y : Scheme.{u}} [IsIntegral X] {I : Y.IdealSheafData} (hI : I.IsInvertible) (g : X ⟶ Y)
    (h : ((I.comap g).support : Set X) ≠ Set.univ) : (I.comap g).IsInvertible := by
  intro x
  obtain ⟨U, f, hxf, a, ha, hIa⟩ := hI (g.base x)
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVle⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (show x ∈ (g ⁻¹ᵁ Y.basicOpen f : X.Opens) from hxf) (g ⁻¹ᵁ Y.basicOpen f).isOpen
  let V' : X.affineOpens := ⟨V, hV⟩
  have hx1 : x ∈ X.basicOpen (1 : Γ(X, V')) := by simpa using hxV
  refine ⟨V', 1, hx1, ?_⟩
  have hVle' : (V' : X.Opens) ≤ g ⁻¹ᵁ (Y.affineBasicOpen f : Y.Opens) := hVle
  have hle : (X.affineBasicOpen (1 : Γ(X, V')) : X.Opens) ≤ g ⁻¹ᵁ (Y.affineBasicOpen f : Y.Opens) :=
    (X.basicOpen_le (1 : Γ(X, V'))).trans hVle'
  have key := Scheme.IdealSheafData.ideal_comap_of_le I g (Y.affineBasicOpen f)
    (X.affineBasicOpen (1 : Γ(X, V'))) hle
  rw [hIa, Ideal.map_span, Set.image_singleton] at key
  set b : Γ(X, (X.affineBasicOpen (1 : Γ(X, V')) : X.Opens)) := (g.appLE _ _ hle).hom a with hb
  refine ⟨b, ?_, key⟩

  haveI : Nonempty (X.affineBasicOpen (1 : Γ(X, V')) : X.Opens) := ⟨⟨x, hx1⟩⟩
  refine mem_nonZeroDivisors_of_ne_zero fun hb0 => h ?_

  have hsub : ((X.affineBasicOpen (1 : Γ(X, V')) : X.Opens) : Set X) ⊆ (I.comap g).support := by
    intro y hy
    rw [SetLike.mem_coe, Scheme.IdealSheafData.mem_support_iff_of_mem (U := X.affineBasicOpen (1 : Γ(X, V'))) hy, key,
      hb0, Scheme.mem_zeroLocus_iff]
    intro c hc
    rw [SetLike.mem_coe, Ideal.span_singleton_eq_bot.mpr rfl, Ideal.mem_bot] at hc
    subst hc
    rw [Scheme.basicOpen_zero]
    exact fun h => h
  have hdense : Dense (((X.affineBasicOpen (1 : Γ(X, V')) : X.Opens) : Set X)) :=
    (X.affineBasicOpen (1 : Γ(X, V'))).1.isOpen.dense ⟨x, hx1⟩
  refine Set.eq_univ_of_univ_subset ?_
  rw [← dense_iff_closure_eq.mp hdense]
  exact closure_minimal hsub (I.comap g).support.isClosed

end S_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_comap_of_isIntegral
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_comap_of_isIntegral (solution)
