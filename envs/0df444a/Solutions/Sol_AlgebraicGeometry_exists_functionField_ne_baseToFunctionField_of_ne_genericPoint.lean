-- Prove2me | solution 1 for AlgebraicGeometry.exists_functionField_ne_baseToFunctionField_of_ne_genericPoint
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/4bb99cc9-0b89-5820-91f4-286eef2145a6

import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_functionField_ne_baseToFunctionField_of_ne_genericPoint

set_option autoImplicit false
open CategoryTheory AlgebraicGeometry

theorem solution
    {K : Type} [Field K] {X : Scheme.{0}} [IsIntegral X] (c : X ⟶ Spec (CommRingCat.of K))
    (x : X) (hx : x ≠ genericPoint X) :
    ∃ s : ↑X.functionField, ∀ a : K, s ≠ AlgebraicCurve.baseToFunctionField c a := by
  classical

  obtain ⟨y, hy⟩ := X.affineCover.covers x
  let U : X.Opens := (X.affineCover.f (X.affineCover.idx x)).opensRange
  have hU : IsAffineOpen U := isAffineOpen_opensRange _
  have hxU : x ∈ U := ⟨y, hy⟩
  haveI hne : Nonempty (U : Set X) := ⟨⟨x, hxU⟩⟩
  haveI hne' : Nonempty U := ⟨⟨x, hxU⟩⟩
  haveI : IsDomain Γ(X, U) := inferInstance
  have hηU : genericPoint X ∈ U := ((genericPoint_spec X).mem_open_set_iff U.isOpen).2 ⟨x, Set.mem_univ x, hxU⟩

  have h𝔭 : hU.primeIdealOf ⟨x, hxU⟩ ≠ genericPoint (Spec Γ(X, U)) := by
    intro h
    apply hx
    have h1 := hU.fromSpec_primeIdealOf ⟨x, hxU⟩
    rw [h, ← hU.primeIdealOf_genericPoint, hU.fromSpec_primeIdealOf] at h1
    exact h1.symm
  have hbot : (hU.primeIdealOf ⟨x, hxU⟩).asIdeal ≠ ⊥ := by
    intro hb
    apply h𝔭
    rw [genericPoint_eq_bot_of_affine]
    exact PrimeSpectrum.ext hb
  obtain ⟨g, hg𝔭, hg0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  refine ⟨(X.presheaf.germ U (genericPoint X) hηU).hom g, fun a ha => ?_⟩

  set t : Γ(X, U) := (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom (c.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom a)) with ht
  have hta : AlgebraicCurve.baseToFunctionField c a = (X.presheaf.germ U (genericPoint X) hηU).hom t := by
    show (X.presheaf.germ ⊤ (genericPoint X) trivial).hom (c.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom a)) = _
    rw [ht]
    exact (X.presheaf.germ_res_apply (homOfLE (le_top : U ≤ ⊤)) (genericPoint X) hηU _).symm
  have hgeq : g = t := germ_injective_of_isIntegral X (genericPoint X) hηU (ha.trans hta)
  by_cases ha0 : a = 0
  · apply hg0
    rw [hgeq, ht, ha0, map_zero, map_zero, map_zero]
  · have hunit : IsUnit t := by
      rw [ht]
      exact ((isUnit_iff_ne_zero.2 ha0).map _).map _ |>.map _
    exact (hU.primeIdealOf ⟨x, hxU⟩).2.ne_top (Ideal.eq_top_of_isUnit_mem _ hg𝔭 (hgeq ▸ hunit))

end S_AlgebraicGeometry_exists_functionField_ne_baseToFunctionField_of_ne_genericPoint
end P2MW
export P2MW.S_AlgebraicGeometry_exists_functionField_ne_baseToFunctionField_of_ne_genericPoint (solution)
