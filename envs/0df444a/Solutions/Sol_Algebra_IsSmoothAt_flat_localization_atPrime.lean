-- Prove2me | solution 1 for Algebra.IsSmoothAt.flat_localization_atPrime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/721bec0c-144c-547b-9328-962c65a70ce8

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_IsSmoothAt_flat_localization_atPrime

set_option autoImplicit false

open Algebra

theorem solution (R A : Type) [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.FinitePresentation R A] (p : Ideal A) [p.IsPrime] [Algebra.IsSmoothAt R p] :
    Module.Flat R (Localization.AtPrime p) := by
  obtain ⟨f, hf, hsm⟩ := Algebra.IsSmoothAt.exists_notMem_smooth R p
  haveI := hsm
  haveI : Module.Flat R (Localization.Away f) := Algebra.Smooth.flat R _
  have hle : Submonoid.powers f ≤ p.primeCompl := by
    rintro x ⟨n, rfl⟩
    exact fun h => hf (‹p.IsPrime›.mem_of_pow_mem n h)
  letI : Algebra (Localization.Away f) (Localization.AtPrime p) :=
    IsLocalization.localizationAlgebraOfSubmonoidLe _ _ (Submonoid.powers f) p.primeCompl hle
  haveI : IsScalarTower A (Localization.Away f) (Localization.AtPrime p) :=
    IsLocalization.localization_isScalarTower_of_submonoid_le _ _ (Submonoid.powers f) p.primeCompl hle
  haveI : IsLocalization ((p.primeCompl).map (algebraMap A (Localization.Away f))) (Localization.AtPrime p) :=
    IsLocalization.isLocalization_of_submonoid_le _ _ (Submonoid.powers f) p.primeCompl hle
  haveI : Module.Flat (Localization.Away f) (Localization.AtPrime p) :=
    IsLocalization.flat (Localization.AtPrime p) ((p.primeCompl).map (algebraMap A (Localization.Away f)))
  haveI : IsScalarTower R (Localization.Away f) (Localization.AtPrime p) :=
    IsScalarTower.of_algebraMap_eq (fun r => by
      rw [IsScalarTower.algebraMap_apply R A (Localization.AtPrime p) r,
        IsScalarTower.algebraMap_apply R A (Localization.Away f) r,
        ← IsScalarTower.algebraMap_apply A (Localization.Away f) (Localization.AtPrime p)])
  exact Module.Flat.trans R (Localization.Away f) (Localization.AtPrime p)

end S_Algebra_IsSmoothAt_flat_localization_atPrime
end P2MW
export P2MW.S_Algebra_IsSmoothAt_flat_localization_atPrime (solution)
