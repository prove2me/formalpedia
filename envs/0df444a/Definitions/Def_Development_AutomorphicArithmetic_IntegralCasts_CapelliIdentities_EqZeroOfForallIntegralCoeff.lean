-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_EqZeroOfForallIntegralCoeff
-- name    : Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_EqZeroOfForallIntegralCoeff
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:37:49.252556+00:00
-- url     : https://prove2.me/theorems/44625644-9bdc-4c98-99ed-712bd4e892f5
-- title:
--   Eq Zero Of Forall Integral Coeff
-- statement:
--   Definitions and structural lemmas for Eq Zero Of Forall Integral Coeff, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/EqZeroOfForallIntegralCoeff.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
@[reducible] noncomputable def UpperTheory.Reformulated.B.Gwa7.U2 :
    Type :=
    ↥(@Matrix.unitaryGroup (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (Fin.fintype (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex Complex.commRing
        Complex.instStarRing)
@[reducible] noncomputable def UpperTheory.Reformulated.B.Gwa7.instMeasurableSpaceU2 :
    MeasurableSpace UpperTheory.Reformulated.B.Gwa7.U2 :=
    @borel UpperTheory.Reformulated.B.Gwa7.U2
      (@instTopologicalSpaceSubtype
        (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
        (fun
            (x :
              Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex) ↦
          @Membership.mem
            (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
            (@Submonoid
              (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
              (@MulZeroOneClass.toMulOneClass
                (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                (@instMulZeroOneClassOfSemiring
                  (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                  (@Matrix.semiring (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex
                    (@CommSemiring.toSemiring Complex (@CommRing.toCommSemiring Complex Complex.commRing))
                    (Fin.fintype (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))
            (@SetLike.instMembership
              (@Submonoid
                (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                (@MulZeroOneClass.toMulOneClass
                  (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                  (@instMulZeroOneClassOfSemiring
                    (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                    (@Matrix.semiring (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex
                      (@CommSemiring.toSemiring Complex (@CommRing.toCommSemiring Complex Complex.commRing))
                      (Fin.fintype (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))
              (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
              (@Submonoid.instSetLike
                (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                (@MulZeroOneClass.toMulOneClass
                  (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                  (@instMulZeroOneClassOfSemiring
                    (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                    (@Matrix.semiring (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex
                      (@CommSemiring.toSemiring Complex (@CommRing.toCommSemiring Complex Complex.commRing))
                      (Fin.fintype (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))
            (@Matrix.unitaryGroup (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (Fin.fintype (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex Complex.commRing
              Complex.instStarRing)
            x)
        (@instTopologicalSpaceMatrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex
          (@UniformSpace.toTopologicalSpace Complex
            (@PseudoMetricSpace.toUniformSpace Complex
              (@SeminormedRing.toPseudoMetricSpace Complex
                (@SeminormedCommRing.toSeminormedRing Complex
                  (@NormedCommRing.toSeminormedCommRing Complex
                    (@CommCStarAlgebra.toNormedCommRing Complex instCommCStarAlgebraComplex))))))))
attribute [local instance] UpperTheory.Reformulated.B.Gwa7.instMeasurableSpaceU2
theorem UpperTheory.Reformulated.B.Gwa7.aux3 :
    @IsTopologicalGroup
      (↥(@unitary
          (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
          (@Semiring.toMonoid
            (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
            (@Matrix.semiring (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex
              (@CommSemiring.toSemiring Complex (@CommRing.toCommSemiring Complex Complex.commRing))
              (Fin.fintype (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
          (@StarRing.toStarMul
            (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
            (@NonUnitalSemiring.toNonUnitalNonAssocSemiring
              (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
              (@Matrix.nonUnitalSemiring (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex
                (@Semiring.toNonUnitalSemiring Complex
                  (@CommSemiring.toSemiring Complex (@CommRing.toCommSemiring Complex Complex.commRing)))
                (Fin.fintype (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
            (@Matrix.instStarRing (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex
              (Fin.fintype (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (@NonUnitalSemiring.toNonUnitalNonAssocSemiring Complex
                (@Semiring.toNonUnitalSemiring Complex
                  (@CommSemiring.toSemiring Complex (@CommRing.toCommSemiring Complex Complex.commRing))))
              Complex.instStarRing))))
      (@instTopologicalSpaceSubtype
        (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
        (fun
            (x :
              Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex) ↦
          @Membership.mem
            (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
            (@Submonoid
              (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
              (@Monoid.toMulOneClass
                (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                (@Semiring.toMonoid
                  (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                  (@Matrix.semiring (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex
                    (@CommSemiring.toSemiring Complex (@CommRing.toCommSemiring Complex Complex.commRing))
                    (Fin.fintype (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))
            (@SetLike.instMembership
              (@Submonoid
                (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                (@Monoid.toMulOneClass
                  (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                  (@Semiring.toMonoid
                    (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                    (@Matrix.semiring (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex
                      (@CommSemiring.toSemiring Complex (@CommRing.toCommSemiring Complex Complex.commRing))
                      (Fin.fintype (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))
              (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
              (@Submonoid.instSetLike
                (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                (@Monoid.toMulOneClass
                  (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                  (@Semiring.toMonoid
                    (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                    (@Matrix.semiring (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex
                      (@CommSemiring.toSemiring Complex (@CommRing.toCommSemiring Complex Complex.commRing))
                      (Fin.fintype (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))
            (@unitary
              (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
              (@Semiring.toMonoid
                (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                (@Matrix.semiring (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex
                  (@CommSemiring.toSemiring Complex (@CommRing.toCommSemiring Complex Complex.commRing))
                  (Fin.fintype (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
              (@StarRing.toStarMul
                (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                (@NonUnitalSemiring.toNonUnitalNonAssocSemiring
                  (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                  (@Matrix.nonUnitalSemiring (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex
                    (@Semiring.toNonUnitalSemiring Complex
                      (@CommSemiring.toSemiring Complex (@CommRing.toCommSemiring Complex Complex.commRing)))
                    (Fin.fintype (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
                (@Matrix.instStarRing (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex
                  (Fin.fintype (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (@NonUnitalSemiring.toNonUnitalNonAssocSemiring Complex
                    (@Semiring.toNonUnitalSemiring Complex
                      (@CommSemiring.toSemiring Complex (@CommRing.toCommSemiring Complex Complex.commRing))))
                  Complex.instStarRing)))
            x)
        (@instTopologicalSpaceMatrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex
          (@UniformSpace.toTopologicalSpace Complex
            (@PseudoMetricSpace.toUniformSpace Complex
              (@SeminormedRing.toPseudoMetricSpace Complex
                (@SeminormedCommRing.toSeminormedRing Complex
                  (@NormedCommRing.toSeminormedCommRing Complex
                    (@CommCStarAlgebra.toNormedCommRing Complex instCommCStarAlgebraComplex))))))))
      (@Unitary.instGroupSubtypeMemSubmonoidUnitary
        (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
        (@Semiring.toMonoid
          (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
          (@Matrix.semiring (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex
            (@CommSemiring.toSemiring Complex (@CommRing.toCommSemiring Complex Complex.commRing))
            (Fin.fintype (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
        (@StarRing.toStarMul
          (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
          (@NonUnitalSemiring.toNonUnitalNonAssocSemiring
            (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
            (@Matrix.nonUnitalSemiring (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex
              (@Semiring.toNonUnitalSemiring Complex
                (@CommSemiring.toSemiring Complex (@CommRing.toCommSemiring Complex Complex.commRing)))
              (Fin.fintype (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
          (@Matrix.instStarRing (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex
            (Fin.fintype (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (@NonUnitalSemiring.toNonUnitalNonAssocSemiring Complex
              (@Semiring.toNonUnitalSemiring Complex
                (@CommSemiring.toSemiring Complex (@CommRing.toCommSemiring Complex Complex.commRing))))
            Complex.instStarRing))) := by
  exact (inferInstance : IsTopologicalGroup (Matrix.unitaryGroup (Fin 2) ℂ))
theorem UpperTheory.Reformulated.B.Gwa7.aux4 :
    @BorelSpace UpperTheory.Reformulated.B.Gwa7.U2
      (@instTopologicalSpaceSubtype
        (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
        (fun
            (x :
              Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex) ↦
          @Membership.mem
            (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
            (@Submonoid
              (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
              (@MulZeroOneClass.toMulOneClass
                (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                (@instMulZeroOneClassOfSemiring
                  (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                  (@Matrix.semiring (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex
                    (@CommSemiring.toSemiring Complex (@CommRing.toCommSemiring Complex Complex.commRing))
                    (Fin.fintype (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))
            (@SetLike.instMembership
              (@Submonoid
                (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                (@MulZeroOneClass.toMulOneClass
                  (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                  (@instMulZeroOneClassOfSemiring
                    (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                    (@Matrix.semiring (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex
                      (@CommSemiring.toSemiring Complex (@CommRing.toCommSemiring Complex Complex.commRing))
                      (Fin.fintype (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))
              (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
              (@Submonoid.instSetLike
                (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                (@MulZeroOneClass.toMulOneClass
                  (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                  (@instMulZeroOneClassOfSemiring
                    (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                    (@Matrix.semiring (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex
                      (@CommSemiring.toSemiring Complex (@CommRing.toCommSemiring Complex Complex.commRing))
                      (Fin.fintype (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))
            (@Matrix.unitaryGroup (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (Fin.fintype (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex Complex.commRing
              Complex.instStarRing)
            x)
        (@instTopologicalSpaceMatrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex
          (@UniformSpace.toTopologicalSpace Complex
            (@PseudoMetricSpace.toUniformSpace Complex
              (@SeminormedRing.toPseudoMetricSpace Complex
                (@SeminormedCommRing.toSeminormedRing Complex
                  (@NormedCommRing.toSeminormedCommRing Complex
                    (@CommCStarAlgebra.toNormedCommRing Complex instCommCStarAlgebraComplex))))))))
      UpperTheory.Reformulated.B.Gwa7.instMeasurableSpaceU2 := by
  exact ⟨rfl⟩
theorem UpperTheory.Reformulated.B.Gwa7.compact_unitary :
    CompactSpace (Matrix.unitaryGroup (Fin 2) ℂ) := by
  refine isCompact_iff_compactSpace.1 ?_
  have hK : IsCompact (Set.pi Set.univ fun _ : Fin 2 => Set.pi Set.univ fun _ : Fin 2 =>
      Metric.closedBall (0 : ℂ) 1) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  refine IsCompact.of_isClosed_subset (X := Matrix (Fin 2) (Fin 2) ℂ) hK
    (isClosed_unitary (R := Matrix (Fin 2) (Fin 2) ℂ)) ?_
  intro U hU i _ j _
  simpa using entry_norm_bound_of_unitary hU i j
theorem UpperTheory.Reformulated.B.Gwa7.aux5 :
    @CompactSpace
      (↥(@Matrix.unitaryGroup (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (fun (a b : Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) ↦
            @LinearOrder.toDecidableEq (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (@Fin.instLinearOrder (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) a b)
          (Fin.fintype (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex
          (@Field.toCommRing Complex
            (@NormedField.toField Complex
              (@DenselyNormedField.toNormedField Complex (@RCLike.toDenselyNormedField Complex Complex.instRCLike))))
          (@RCLike.toStarRing Complex Complex.instRCLike)))
      (@instTopologicalSpaceSubtype
        (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
        (fun
            (x :
              Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex) ↦
          @Membership.mem
            (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
            (@Submonoid
              (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
              (@MulZeroOneClass.toMulOneClass
                (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                (@instMulZeroOneClassOfSemiring
                  (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                  (@Matrix.semiring (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex
                    (@CommSemiring.toSemiring Complex
                      (@CommRing.toCommSemiring Complex
                        (@Field.toCommRing Complex
                          (@NormedField.toField Complex
                            (@DenselyNormedField.toNormedField Complex
                              (@RCLike.toDenselyNormedField Complex Complex.instRCLike))))))
                    (Fin.fintype (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    fun (a b : Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) ↦
                    @LinearOrder.toDecidableEq (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (@Fin.instLinearOrder (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) a b))))
            (@SetLike.instMembership
              (@Submonoid
                (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                (@MulZeroOneClass.toMulOneClass
                  (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                  (@instMulZeroOneClassOfSemiring
                    (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                    (@Matrix.semiring (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex
                      (@CommSemiring.toSemiring Complex
                        (@CommRing.toCommSemiring Complex
                          (@Field.toCommRing Complex
                            (@NormedField.toField Complex
                              (@DenselyNormedField.toNormedField Complex
                                (@RCLike.toDenselyNormedField Complex Complex.instRCLike))))))
                      (Fin.fintype (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      fun (a b : Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) ↦
                      @LinearOrder.toDecidableEq (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        (@Fin.instLinearOrder (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) a b))))
              (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
              (@Submonoid.instSetLike
                (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                (@MulZeroOneClass.toMulOneClass
                  (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                  (@instMulZeroOneClassOfSemiring
                    (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                    (@Matrix.semiring (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex
                      (@CommSemiring.toSemiring Complex
                        (@CommRing.toCommSemiring Complex
                          (@Field.toCommRing Complex
                            (@NormedField.toField Complex
                              (@DenselyNormedField.toNormedField Complex
                                (@RCLike.toDenselyNormedField Complex Complex.instRCLike))))))
                      (Fin.fintype (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      fun (a b : Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) ↦
                      @LinearOrder.toDecidableEq (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        (@Fin.instLinearOrder (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) a b)))))
            (@Matrix.unitaryGroup (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (fun (a b : Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) ↦
                @LinearOrder.toDecidableEq (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (@Fin.instLinearOrder (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) a b)
              (Fin.fintype (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex
              (@Field.toCommRing Complex
                (@NormedField.toField Complex
                  (@DenselyNormedField.toNormedField Complex (@RCLike.toDenselyNormedField Complex Complex.instRCLike))))
              (@RCLike.toStarRing Complex Complex.instRCLike))
            x)
        (@instTopologicalSpaceMatrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex
          (@UniformSpace.toTopologicalSpace Complex
            (@PseudoMetricSpace.toUniformSpace Complex
              (@SeminormedRing.toPseudoMetricSpace Complex
                (@SeminormedCommRing.toSeminormedRing Complex
                  (@NormedCommRing.toSeminormedCommRing Complex
                    (@NormedField.toNormedCommRing Complex
                      (@DenselyNormedField.toNormedField Complex
                        (@RCLike.toDenselyNormedField Complex Complex.instRCLike)))))))))) := by
  exact UpperTheory.Reformulated.B.Gwa7.compact_unitary
theorem UpperTheory.Reformulated.B.Gwa7.aux6 :
    Nonempty UpperTheory.Reformulated.B.Gwa7.U2 := by
  exact ⟨1⟩
noncomputable def UpperTheory.Reformulated.B.Gwa7.μK :
    @MeasureTheory.Measure UpperTheory.Reformulated.B.Gwa7.U2 UpperTheory.Reformulated.B.Gwa7.instMeasurableSpaceU2 :=
    @MeasureTheory.Measure.haarMeasure UpperTheory.Reformulated.B.Gwa7.U2
      (@Unitary.instGroupSubtypeMemSubmonoidUnitary
        (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
        (@Semiring.toMonoid
          (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
          (@Matrix.semiring (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex
            (@CommSemiring.toSemiring Complex (@CommRing.toCommSemiring Complex Complex.commRing))
            (Fin.fintype (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
        (@StarRing.toStarMul
          (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
          (@NonUnitalSemiring.toNonUnitalNonAssocSemiring
            (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
            (@Matrix.nonUnitalSemiring (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex
              (@Semiring.toNonUnitalSemiring Complex
                (@CommSemiring.toSemiring Complex (@CommRing.toCommSemiring Complex Complex.commRing)))
              (Fin.fintype (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
          (@Matrix.instStarRing (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex
            (Fin.fintype (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (@NonUnitalSemiring.toNonUnitalNonAssocSemiring Complex
              (@Semiring.toNonUnitalSemiring Complex
                (@CommSemiring.toSemiring Complex (@CommRing.toCommSemiring Complex Complex.commRing))))
            Complex.instStarRing)))
      (@instTopologicalSpaceSubtype
        (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
        (fun
            (x :
              Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex) ↦
          @Membership.mem
            (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
            (@Submonoid
              (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
              (@MulZeroOneClass.toMulOneClass
                (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                (@instMulZeroOneClassOfSemiring
                  (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                  (@Matrix.semiring (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex
                    (@CommSemiring.toSemiring Complex (@CommRing.toCommSemiring Complex Complex.commRing))
                    (Fin.fintype (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))
            (@SetLike.instMembership
              (@Submonoid
                (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                (@MulZeroOneClass.toMulOneClass
                  (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                  (@instMulZeroOneClassOfSemiring
                    (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                    (@Matrix.semiring (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex
                      (@CommSemiring.toSemiring Complex (@CommRing.toCommSemiring Complex Complex.commRing))
                      (Fin.fintype (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))
              (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
              (@Submonoid.instSetLike
                (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                (@MulZeroOneClass.toMulOneClass
                  (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                  (@instMulZeroOneClassOfSemiring
                    (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                    (@Matrix.semiring (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex
                      (@CommSemiring.toSemiring Complex (@CommRing.toCommSemiring Complex Complex.commRing))
                      (Fin.fintype (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))
            (@Matrix.unitaryGroup (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (Fin.fintype (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex Complex.commRing
              Complex.instStarRing)
            x)
        (@instTopologicalSpaceMatrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex
          (@UniformSpace.toTopologicalSpace Complex
            (@PseudoMetricSpace.toUniformSpace Complex
              (@SeminormedRing.toPseudoMetricSpace Complex
                (@SeminormedCommRing.toSeminormedRing Complex
                  (@NormedCommRing.toSeminormedCommRing Complex
                    (@CommCStarAlgebra.toNormedCommRing Complex instCommCStarAlgebraComplex))))))))
      UpperTheory.Reformulated.B.Gwa7.aux3 UpperTheory.Reformulated.B.Gwa7.instMeasurableSpaceU2 UpperTheory.Reformulated.B.Gwa7.aux4
      (@Top.top
        (@TopologicalSpace.PositiveCompacts UpperTheory.Reformulated.B.Gwa7.U2
          (@instTopologicalSpaceSubtype
            (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
            (fun
                (x :
                  Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex) ↦
              @Membership.mem
                (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                (@Submonoid
                  (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                  (@MulZeroOneClass.toMulOneClass
                    (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                    (@instMulZeroOneClassOfSemiring
                      (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                      (@Matrix.semiring (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex
                        (@CommSemiring.toSemiring Complex (@CommRing.toCommSemiring Complex Complex.commRing))
                        (Fin.fintype (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))
                (@SetLike.instMembership
                  (@Submonoid
                    (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                    (@MulZeroOneClass.toMulOneClass
                      (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                      (@instMulZeroOneClassOfSemiring
                        (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                          (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                        (@Matrix.semiring (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex
                          (@CommSemiring.toSemiring Complex (@CommRing.toCommSemiring Complex Complex.commRing))
                          (Fin.fintype (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                          (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))
                  (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                  (@Submonoid.instSetLike
                    (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                    (@MulZeroOneClass.toMulOneClass
                      (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                      (@instMulZeroOneClassOfSemiring
                        (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                          (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                        (@Matrix.semiring (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex
                          (@CommSemiring.toSemiring Complex (@CommRing.toCommSemiring Complex Complex.commRing))
                          (Fin.fintype (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                          (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))
                (@Matrix.unitaryGroup (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (Fin.fintype (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex Complex.commRing
                  Complex.instStarRing)
                x)
            (@instTopologicalSpaceMatrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex
              (@UniformSpace.toTopologicalSpace Complex
                (@PseudoMetricSpace.toUniformSpace Complex
                  (@SeminormedRing.toPseudoMetricSpace Complex
                    (@SeminormedCommRing.toSeminormedRing Complex
                      (@NormedCommRing.toSeminormedCommRing Complex
                        (@CommCStarAlgebra.toNormedCommRing Complex instCommCStarAlgebraComplex)))))))))
        (@TopologicalSpace.PositiveCompacts.instTopOfCompactSpaceOfNonempty UpperTheory.Reformulated.B.Gwa7.U2
          (@instTopologicalSpaceSubtype
            (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
            (fun
                (x :
                  Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex) ↦
              @Membership.mem
                (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                (@Submonoid
                  (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                  (@MulZeroOneClass.toMulOneClass
                    (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                    (@instMulZeroOneClassOfSemiring
                      (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                      (@Matrix.semiring (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex
                        (@CommSemiring.toSemiring Complex (@CommRing.toCommSemiring Complex Complex.commRing))
                        (Fin.fintype (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))
                (@SetLike.instMembership
                  (@Submonoid
                    (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                    (@MulZeroOneClass.toMulOneClass
                      (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                      (@instMulZeroOneClassOfSemiring
                        (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                          (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                        (@Matrix.semiring (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex
                          (@CommSemiring.toSemiring Complex (@CommRing.toCommSemiring Complex Complex.commRing))
                          (Fin.fintype (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                          (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))
                  (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                  (@Submonoid.instSetLike
                    (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                    (@MulZeroOneClass.toMulOneClass
                      (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                      (@instMulZeroOneClassOfSemiring
                        (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                          (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                        (@Matrix.semiring (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex
                          (@CommSemiring.toSemiring Complex (@CommRing.toCommSemiring Complex Complex.commRing))
                          (Fin.fintype (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                          (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))
                (@Matrix.unitaryGroup (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (Fin.fintype (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex Complex.commRing
                  Complex.instStarRing)
                x)
            (@instTopologicalSpaceMatrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex
              (@UniformSpace.toTopologicalSpace Complex
                (@PseudoMetricSpace.toUniformSpace Complex
                  (@SeminormedRing.toPseudoMetricSpace Complex
                    (@SeminormedCommRing.toSeminormedRing Complex
                      (@NormedCommRing.toSeminormedCommRing Complex
                        (@CommCStarAlgebra.toNormedCommRing Complex instCommCStarAlgebraComplex))))))))
          UpperTheory.Reformulated.B.Gwa7.aux5 UpperTheory.Reformulated.B.Gwa7.aux6))
section Algebra
variable {A : Type*} [NormedCommRing A] [NormedAlgebra ℂ A]
def UpperTheory.Reformulated.B.Gwa7.lin (p q r s : A) (a b c d : ℂ) : A :=
  (a * c) • p + (a * d) • q + (b * c) • r + (b * d) • s
end Algebra
noncomputable def UpperTheory.Reformulated.B.Gwa7.entry (i j : Fin 2) : C(UpperTheory.Reformulated.B.Gwa7.U2, ℂ) :=
  ⟨fun k => k.1 i j, continuous_subtype_val.matrix_elem i j⟩
theorem UpperTheory.Reformulated.B.Gwa7.det_ne (k : UpperTheory.Reformulated.B.Gwa7.U2) : k.1.det ≠ 0 :=
  (Unitary.isUnit_coe (U := ⟨_, Matrix.det_of_mem_unitary k.2⟩)).ne_zero
noncomputable def UpperTheory.Reformulated.B.Gwa7.detPow (m : ℤ) : C(UpperTheory.Reformulated.B.Gwa7.U2, ℂ) :=
  ⟨fun k => k.1.det ^ m, continuous_subtype_val.matrix_det.zpow₀ m
    fun k => Or.inl (UpperTheory.Reformulated.B.Gwa7.det_ne k)⟩


