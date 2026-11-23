-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SquareOfApproximation
-- name    : Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SquareOfApproximation
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:37:56.621979+00:00
-- url     : https://prove2.me/theorems/47704771-8b5e-45bb-8471-44b1ff7bd943
-- title:
--   Square Of Approximation
-- statement:
--   Definitions and structural lemmas for Square Of Approximation, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/SquareOfApproximation.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace UpperTheory.Reformulated.B.SquareOfApproximation
end UpperTheory.Reformulated.B.SquareOfApproximation
noncomputable def UpperTheory.Reformulated.B.SquareOfApproximation.IsCMExt :
    (F E : Type) →
      [inst : Field F] →
        [@NumberField F inst] →
          [inst_2 : Field E] →
            [@NumberField E inst_2] →
              [inst_4 :
                  @Algebra F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2)))] →
                @AlgHom F E E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2)))
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))) inst_4
                    inst_4 →
                  Prop :=
    fun (F E : Type) [inst : Field F] [@NumberField F inst] [inst_2 : Field E] [@NumberField E inst_2]
        [inst_4 :
          @Algebra F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
            (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2)))]
        (σ :
          @AlgHom F E E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
            (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2)))
            (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))) inst_4
            inst_4) ↦
      And (@NumberField.IsTotallyReal F inst)
        (And (@NumberField.IsTotallyComplex E inst_2)
          (And
            (@Eq Nat
              (@Module.finrank F E
                (@DivisionSemiring.toSemiring F (@Semifield.toDivisionSemiring F (@Field.toSemifield F inst)))
                (@Semiring.toAddCommMonoid E
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))))
                (@Algebra.toModule F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                  (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))) inst_4))
              (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (∀
              (τ :
                @RingHom E Complex
                  (@Semiring.toNonAssocSemiring E
                    (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))))
                  (@Semiring.toNonAssocSemiring Complex Complex.instSemiring))
              (x : E),
              @Eq Complex
                (@DFunLike.coe
                  (@RingHom E Complex
                    (@Semiring.toNonAssocSemiring E
                      (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))))
                    (@Semiring.toNonAssocSemiring Complex Complex.instSemiring))
                  E (fun (x : E) ↦ Complex)
                  (@RingHom.instFunLike E Complex
                    (@Semiring.toNonAssocSemiring E
                      (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))))
                    (@Semiring.toNonAssocSemiring Complex Complex.instSemiring))
                  τ
                  (@DFunLike.coe
                    (@AlgHom F E E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                      (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2)))
                      (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2)))
                      inst_4 inst_4)
                    E (fun (x : E) ↦ E)
                    (@AlgHom.funLike F E E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                      (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2)))
                      (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2)))
                      inst_4 inst_4)
                    σ x))
                (@Star.star Complex
                  (@InvolutiveStar.toStar Complex
                    (@StarAddMonoid.toInvolutiveStar Complex
                      (@AddCommMonoid.toAddMonoid Complex
                        (@NonUnitalNonAssocSemiring.toAddCommMonoid Complex
                          (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring Complex
                            (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing Complex
                              (@NonUnitalCommRing.toNonUnitalNonAssocCommRing Complex Complex.instNonUnitalCommRing)))))
                      (@StarRing.toStarAddMonoid Complex
                        (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring Complex
                          (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing Complex
                            (@NonUnitalCommRing.toNonUnitalNonAssocCommRing Complex Complex.instNonUnitalCommRing)))
                        Complex.instStarRing)))
                  (@DFunLike.coe
                    (@RingHom E Complex
                      (@Semiring.toNonAssocSemiring E
                        (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))))
                      (@Semiring.toNonAssocSemiring Complex Complex.instSemiring))
                    E (fun (x : E) ↦ Complex)
                    (@RingHom.instFunLike E Complex
                      (@Semiring.toNonAssocSemiring E
                        (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_2))))
                      (@Semiring.toNonAssocSemiring Complex Complex.instSemiring))
                    τ x)))))
theorem UpperTheory.Reformulated.B.SquareOfApproximation.aux2 :
    ∀ {F E : Type} [inst : Field F] [inst_1 : Field E],
      @RingHomClass
        (@RingHom (@NumberField.RingOfIntegers F inst) (@NumberField.RingOfIntegers E inst_1)
          (@Semiring.toNonAssocSemiring (@NumberField.RingOfIntegers F inst)
            (@CommSemiring.toSemiring (@NumberField.RingOfIntegers F inst)
              (@CommRing.toCommSemiring (@NumberField.RingOfIntegers F inst)
                (@NumberField.instCommRingRingOfIntegers F inst))))
          (@Semiring.toNonAssocSemiring (@NumberField.RingOfIntegers E inst_1)
            (@CommSemiring.toSemiring (@NumberField.RingOfIntegers E inst_1)
              (@CommRing.toCommSemiring (@NumberField.RingOfIntegers E inst_1)
                (@NumberField.instCommRingRingOfIntegers E inst_1)))))
        (@NumberField.RingOfIntegers F inst) (@NumberField.RingOfIntegers E inst_1)
        (@Semiring.toNonAssocSemiring (@NumberField.RingOfIntegers F inst)
          (@CommSemiring.toSemiring (@NumberField.RingOfIntegers F inst)
            (@CommRing.toCommSemiring (@NumberField.RingOfIntegers F inst)
              (@NumberField.instCommRingRingOfIntegers F inst))))
        (@Semiring.toNonAssocSemiring (@NumberField.RingOfIntegers E inst_1)
          (@CommSemiring.toSemiring (@NumberField.RingOfIntegers E inst_1)
            (@CommRing.toCommSemiring (@NumberField.RingOfIntegers E inst_1)
              (@NumberField.instCommRingRingOfIntegers E inst_1))))
        (@RingHom.instFunLike (@NumberField.RingOfIntegers F inst) (@NumberField.RingOfIntegers E inst_1)
          (@Semiring.toNonAssocSemiring (@NumberField.RingOfIntegers F inst)
            (@CommSemiring.toSemiring (@NumberField.RingOfIntegers F inst)
              (@CommRing.toCommSemiring (@NumberField.RingOfIntegers F inst)
                (@NumberField.instCommRingRingOfIntegers F inst))))
          (@Semiring.toNonAssocSemiring (@NumberField.RingOfIntegers E inst_1)
            (@CommSemiring.toSemiring (@NumberField.RingOfIntegers E inst_1)
              (@CommRing.toCommSemiring (@NumberField.RingOfIntegers E inst_1)
                (@NumberField.instCommRingRingOfIntegers E inst_1))))) := by
  intro F E _ _
  infer_instance
noncomputable def UpperTheory.Reformulated.B.SquareOfApproximation.IsSplit :
    {F E : Type} →
      [inst : Field F] →
        [inst_1 : Field E] →
          [@Algebra F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1)))] →
            @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                (@NumberField.instCommRingRingOfIntegers F inst) →
              Prop :=
    fun {F E : Type} [inst : Field F] [inst_1 : Field E]
        [inst_2 :
          @Algebra F E (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
            (@DivisionSemiring.toSemiring E (@Semifield.toDivisionSemiring E (@Field.toSemifield E inst_1)))]
        (w :
          @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
            (@NumberField.instCommRingRingOfIntegers F inst)) ↦
      ∃ (P :
        @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers E inst_1)
          (@NumberField.instCommRingRingOfIntegers E inst_1))
        (Q :
        @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers E inst_1)
          (@NumberField.instCommRingRingOfIntegers E inst_1)),
        And
          (@Ne
            (@IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers E inst_1)
              (@NumberField.instCommRingRingOfIntegers E inst_1))
            P Q)
          (And
            (@Eq
              (@Ideal (@NumberField.RingOfIntegers F inst)
                (@CommSemiring.toSemiring (@NumberField.RingOfIntegers F inst)
                  (@CommRing.toCommSemiring (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst))))
              (@Ideal.comap (@NumberField.RingOfIntegers F inst) (@NumberField.RingOfIntegers E inst_1)
                (@RingHom (@NumberField.RingOfIntegers F inst) (@NumberField.RingOfIntegers E inst_1)
                  (@Semiring.toNonAssocSemiring (@NumberField.RingOfIntegers F inst)
                    (@CommSemiring.toSemiring (@NumberField.RingOfIntegers F inst)
                      (@CommRing.toCommSemiring (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst))))
                  (@Semiring.toNonAssocSemiring (@NumberField.RingOfIntegers E inst_1)
                    (@CommSemiring.toSemiring (@NumberField.RingOfIntegers E inst_1)
                      (@CommRing.toCommSemiring (@NumberField.RingOfIntegers E inst_1)
                        (@NumberField.instCommRingRingOfIntegers E inst_1)))))
                (@CommSemiring.toSemiring (@NumberField.RingOfIntegers F inst)
                  (@CommRing.toCommSemiring (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)))
                (@CommSemiring.toSemiring (@NumberField.RingOfIntegers E inst_1)
                  (@CommRing.toCommSemiring (@NumberField.RingOfIntegers E inst_1)
                    (@NumberField.instCommRingRingOfIntegers E inst_1)))
                (@RingHom.instFunLike (@NumberField.RingOfIntegers F inst) (@NumberField.RingOfIntegers E inst_1)
                  (@Semiring.toNonAssocSemiring (@NumberField.RingOfIntegers F inst)
                    (@CommSemiring.toSemiring (@NumberField.RingOfIntegers F inst)
                      (@CommRing.toCommSemiring (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst))))
                  (@Semiring.toNonAssocSemiring (@NumberField.RingOfIntegers E inst_1)
                    (@CommSemiring.toSemiring (@NumberField.RingOfIntegers E inst_1)
                      (@CommRing.toCommSemiring (@NumberField.RingOfIntegers E inst_1)
                        (@NumberField.instCommRingRingOfIntegers E inst_1)))))
                (@Algebra.algebraMap (@NumberField.RingOfIntegers F inst) (@NumberField.RingOfIntegers E inst_1)
                  (@CommRing.toCommSemiring (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst))
                  (@CommSemiring.toSemiring (@NumberField.RingOfIntegers E inst_1)
                    (@CommRing.toCommSemiring (@NumberField.RingOfIntegers E inst_1)
                      (@NumberField.instCommRingRingOfIntegers E inst_1)))
                  (@NumberField.inst_ringOfIntegersAlgebra F E inst inst_1 inst_2))
                (@UpperTheory.Reformulated.B.SquareOfApproximation.aux2 F E inst inst_1)
                (@IsDedekindDomain.HeightOneSpectrum.asIdeal (@NumberField.RingOfIntegers E inst_1)
                  (@NumberField.instCommRingRingOfIntegers E inst_1) P))
              (@IsDedekindDomain.HeightOneSpectrum.asIdeal (@NumberField.RingOfIntegers F inst)
                (@NumberField.instCommRingRingOfIntegers F inst) w))
            (@Eq
              (@Ideal (@NumberField.RingOfIntegers F inst)
                (@CommSemiring.toSemiring (@NumberField.RingOfIntegers F inst)
                  (@CommRing.toCommSemiring (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst))))
              (@Ideal.comap (@NumberField.RingOfIntegers F inst) (@NumberField.RingOfIntegers E inst_1)
                (@RingHom (@NumberField.RingOfIntegers F inst) (@NumberField.RingOfIntegers E inst_1)
                  (@Semiring.toNonAssocSemiring (@NumberField.RingOfIntegers F inst)
                    (@CommSemiring.toSemiring (@NumberField.RingOfIntegers F inst)
                      (@CommRing.toCommSemiring (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst))))
                  (@Semiring.toNonAssocSemiring (@NumberField.RingOfIntegers E inst_1)
                    (@CommSemiring.toSemiring (@NumberField.RingOfIntegers E inst_1)
                      (@CommRing.toCommSemiring (@NumberField.RingOfIntegers E inst_1)
                        (@NumberField.instCommRingRingOfIntegers E inst_1)))))
                (@CommSemiring.toSemiring (@NumberField.RingOfIntegers F inst)
                  (@CommRing.toCommSemiring (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)))
                (@CommSemiring.toSemiring (@NumberField.RingOfIntegers E inst_1)
                  (@CommRing.toCommSemiring (@NumberField.RingOfIntegers E inst_1)
                    (@NumberField.instCommRingRingOfIntegers E inst_1)))
                (@RingHom.instFunLike (@NumberField.RingOfIntegers F inst) (@NumberField.RingOfIntegers E inst_1)
                  (@Semiring.toNonAssocSemiring (@NumberField.RingOfIntegers F inst)
                    (@CommSemiring.toSemiring (@NumberField.RingOfIntegers F inst)
                      (@CommRing.toCommSemiring (@NumberField.RingOfIntegers F inst)
                        (@NumberField.instCommRingRingOfIntegers F inst))))
                  (@Semiring.toNonAssocSemiring (@NumberField.RingOfIntegers E inst_1)
                    (@CommSemiring.toSemiring (@NumberField.RingOfIntegers E inst_1)
                      (@CommRing.toCommSemiring (@NumberField.RingOfIntegers E inst_1)
                        (@NumberField.instCommRingRingOfIntegers E inst_1)))))
                (@Algebra.algebraMap (@NumberField.RingOfIntegers F inst) (@NumberField.RingOfIntegers E inst_1)
                  (@CommRing.toCommSemiring (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst))
                  (@CommSemiring.toSemiring (@NumberField.RingOfIntegers E inst_1)
                    (@CommRing.toCommSemiring (@NumberField.RingOfIntegers E inst_1)
                      (@NumberField.instCommRingRingOfIntegers E inst_1)))
                  (@NumberField.inst_ringOfIntegersAlgebra F E inst inst_1 inst_2))
                (@UpperTheory.Reformulated.B.SquareOfApproximation.aux2 F E inst inst_1)
                (@IsDedekindDomain.HeightOneSpectrum.asIdeal (@NumberField.RingOfIntegers E inst_1)
                  (@NumberField.instCommRingRingOfIntegers E inst_1) Q))
              (@IsDedekindDomain.HeightOneSpectrum.asIdeal (@NumberField.RingOfIntegers F inst)
                (@NumberField.instCommRingRingOfIntegers F inst) w)))
@[reducible] noncomputable def UpperTheory.Reformulated.B.SquareOfApproximation.Fv :
    (F : Type) →
      [inst : Field F] →
        [@NumberField F inst] →
          @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
              (@NumberField.instCommRingRingOfIntegers F inst) →
            Type :=
    fun (F : Type) [inst : Field F] [inst_1 : @NumberField F inst]
        (v :
          @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
            (@NumberField.instCommRingRingOfIntegers F inst)) ↦
      @IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
        (@NumberField.instCommRingRingOfIntegers F inst) (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F
        inst (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
        (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) v


