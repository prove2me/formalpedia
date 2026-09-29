-- Prove2me | solution 1 for Algebra.Etale.isIntegrallyClosed_tensorProduct_of_isDomain
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/5999306f-ccc9-5b36-b61b-8086e84bf498

import Mathlib
import Theorems.Thm_Algebra_Etale_isDomain_and_isIntegrallyClosed_of_isLocalization_atPrime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_Etale_isIntegrallyClosed_tensorProduct_of_isDomain

set_option autoImplicit false

universe u v w

open scoped TensorProduct
open IsLocalRing

namespace EtaleBCNormalAux

theorem etale_of_ringEquiv_base {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    (e : R ≃+* S) (he : ∀ r, e r = algebraMap R S r) [Algebra.Etale R T] : Algebra.Etale S T := by
  let e' : R ≃ₐ[R] S := AlgEquiv.ofRingEquiv (f := e) (fun r => by rw [he]; rfl)
  haveI : Algebra.FormallyUnramified R S := Algebra.FormallyUnramified.of_equiv e'
  haveI : Algebra.FiniteType R S := Algebra.FiniteType.equiv inferInstance e'
  haveI : Algebra.FormallyEtale S T := Algebra.FormallyEtale.of_restrictScalars (R := R)
  haveI : Algebra.FinitePresentation S T :=
    Algebra.FinitePresentation.of_restrict_scalars_finitePresentation R S T
  exact Algebra.Etale.mk

theorem isDomain_and_isIntegrallyClosed_of_isLocalization_atPrime'
    (P : Type v) [CommRing P] [IsDomain P] [IsIntegrallyClosed P]
    (A : Type (max v w)) [CommRing A] [Algebra P A] [Algebra.Etale P A]
    (q : Ideal A) [q.IsPrime] (A_q : Type (max v w)) [CommRing A_q] [Algebra A A_q] [IsLocalization.AtPrime A_q q] :
    IsDomain A_q ∧ IsIntegrallyClosed A_q := by
  letI : Algebra (ULift.{w} P) A := ULift.algebra' P A
  haveI : IsScalarTower P (ULift.{w} P) A :=
    IsScalarTower.of_algebraMap_eq (R := P) (S := ULift.{w} P) (A := A) (fun _ => rfl)
  let e : P ≃+* ULift.{w} P := ULift.ringEquiv.symm
  haveI : IsDomain (ULift.{w} P) := MulEquiv.isDomain P e.symm.toMulEquiv
  haveI : IsIntegrallyClosed (ULift.{w} P) := IsIntegrallyClosed.of_equiv e
  haveI : Algebra.Etale (ULift.{w} P) A := etale_of_ringEquiv_base e (fun _ => rfl)
  exact Algebra.Etale.isDomain_and_isIntegrallyClosed_of_isLocalization_atPrime (ULift.{w} P) A q A_q

end EtaleBCNormalAux

open EtaleBCNormalAux in
theorem solution
    {W : Type*} [CommRing W] (B W' : Type*) [CommRing B] [CommRing W'] [Algebra W B] [Algebra W W']
    [Algebra.Etale W W'] [IsDomain B] [IsIntegrallyClosed B] [IsDomain (B ⊗[W] W')] :
    IsIntegrallyClosed (B ⊗[W] W') := by
  apply IsIntegrallyClosed.of_localization_maximal
  intro q _ hq
  exact (isDomain_and_isIntegrallyClosed_of_isLocalization_atPrime' B (B ⊗[W] W') q (Localization.AtPrime q)).2

end S_Algebra_Etale_isIntegrallyClosed_tensorProduct_of_isDomain
end P2MW
export P2MW.S_Algebra_Etale_isIntegrallyClosed_tensorProduct_of_isDomain (solution)
