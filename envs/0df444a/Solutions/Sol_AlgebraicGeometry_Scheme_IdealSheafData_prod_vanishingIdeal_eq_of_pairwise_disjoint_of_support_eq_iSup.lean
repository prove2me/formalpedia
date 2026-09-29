-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.IdealSheafData.prod_vanishingIdeal_eq_of_pairwise_disjoint_of_support_eq_iSup
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/d0c281ad-10cf-5db0-9c55-781e5d7666fb

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_prod_vanishingIdeal_eq_of_pairwise_disjoint_of_support_eq_iSup

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

theorem solution
    {Y : Scheme.{u}} {ι : Type*} [Fintype ι] (Z : ι → Closeds Y)
    (hdisj : Pairwise fun i j => Disjoint (Z i) (Z j))
    (J : Y.IdealSheafData) (hrad : J.radical = J) (hsupp : J.support = ⨆ i, Z i) :
    ∏ i, Scheme.IdealSheafData.vanishingIdeal (Z i) = J := by
  classical

  have hmul : ∀ I K : Y.IdealSheafData, I ⊔ K = ⊤ → I * K = I ⊓ K := by
    intro I K h
    ext U : 2
    rw [Scheme.IdealSheafData.ideal_mul, Scheme.IdealSheafData.ideal_inf, Pi.mul_apply, Pi.inf_apply]
    apply Ideal.mul_eq_inf_of_coprime
    have := congrArg (fun L : Y.IdealSheafData => L.ideal U) h
    simpa [Scheme.IdealSheafData.ideal_sup, Scheme.IdealSheafData.ideal_top] using this

  have hcop : ∀ I K : Y.IdealSheafData, Disjoint I.support K.support → I ⊔ K = ⊤ := by
    intro I K h
    rw [← Scheme.IdealSheafData.support_eq_bot_iff, Scheme.IdealSheafData.support_sup]
    exact h.eq_bot
  have hsuppV : ∀ A : Closeds Y, (Scheme.IdealSheafData.vanishingIdeal A).support = A := fun A =>
    Closeds.ext (Scheme.IdealSheafData.coe_support_vanishingIdeal A)

  have key : ∀ s : Finset ι, ∏ i ∈ s, Scheme.IdealSheafData.vanishingIdeal (Z i) =
      Scheme.IdealSheafData.vanishingIdeal (s.sup Z) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.prod_insert ha, ih, Finset.sup_insert, Scheme.IdealSheafData.vanishingIdeal_sup]
      apply hmul
      apply hcop
      rw [hsuppV, hsuppV, Finset.disjoint_sup_right]
      intro i hi
      exact hdisj (fun h => ha (h ▸ hi))
  rw [key, Finset.sup_univ_eq_iSup, ← hsupp, Scheme.IdealSheafData.vanishingIdeal_support, hrad]

end S_AlgebraicGeometry_Scheme_IdealSheafData_prod_vanishingIdeal_eq_of_pairwise_disjoint_of_support_eq_iSup
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_prod_vanishingIdeal_eq_of_pairwise_disjoint_of_support_eq_iSup (solution)
