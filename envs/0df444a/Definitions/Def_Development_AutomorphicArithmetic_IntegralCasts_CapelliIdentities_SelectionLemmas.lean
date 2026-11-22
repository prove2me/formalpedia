-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SelectionLemmas
-- name    : Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SelectionLemmas
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:30:43.664869+00:00
-- url     : https://prove2.me/theorems/e4350888-4f4c-41e6-93ec-47a2d34a344b
-- title:
--   Selection Lemmas
-- statement:
--   Definitions and structural lemmas for Selection Lemmas, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/SelectionLemmas.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable def UpperTheory.Reformulated.B.SelectionLemmas.hdual.{u_1, u_2, u_3} :
    {S : Type u_1} →
      {K : Type u_2} →
        {V : Type u_3} →
          [inst : CommRing S] →
            [inst_1 : Field K] →
              [inst_2 :
                  @StarRing K
                    (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring K
                      (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing K
                        (@NonUnitalCommRing.toNonUnitalNonAssocCommRing K
                          (@CommRing.toNonUnitalCommRing K (@Field.toCommRing K inst_1)))))] →
                [inst_3 :
                    @Algebra S K (@CommRing.toCommSemiring S inst)
                      (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))] →
                  [inst_4 : AddCommGroup V] →
                    [inst_5 :
                        @_root_.Module K V
                          (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
                          (@AddCommGroup.toAddCommMonoid V inst_4)] →
                      [inst_6 :
                          @_root_.Module S V (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst))
                            (@AddCommGroup.toAddCommMonoid V inst_4)] →
                        [@IsScalarTower S K V
                              (@Algebra.toSMul S K (@CommRing.toCommSemiring S inst)
                                (@DivisionSemiring.toSemiring K
                                  (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
                                inst_3)
                              (@SMulZeroClass.toSMul K V
                                (@AddZero.toZero V
                                  (@AddZeroClass.toAddZero V
                                    (@AddMonoid.toAddZeroClass V
                                      (@SubNegMonoid.toAddMonoid V
                                        (@AddGroup.toSubNegMonoid V (@AddCommGroup.toAddGroup V inst_4))))))
                                (@DistribSMul.toSMulZeroClass K V
                                  (@AddMonoid.toAddZeroClass V
                                    (@SubNegMonoid.toAddMonoid V
                                      (@AddGroup.toSubNegMonoid V (@AddCommGroup.toAddGroup V inst_4))))
                                  (@DistribMulAction.toDistribSMul K V
                                    (@Semiring.toMonoid K
                                      (@DivisionSemiring.toSemiring K
                                        (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1))))
                                    (@SubNegMonoid.toAddMonoid V
                                      (@AddGroup.toSubNegMonoid V (@AddCommGroup.toAddGroup V inst_4)))
                                    (@Module.toDistribMulAction K V
                                      (@DivisionSemiring.toSemiring K
                                        (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
                                      (@AddCommGroup.toAddCommMonoid V inst_4) inst_5))))
                              (@SMulZeroClass.toSMul S V
                                (@AddZero.toZero V
                                  (@AddZeroClass.toAddZero V
                                    (@AddMonoid.toAddZeroClass V
                                      (@SubNegMonoid.toAddMonoid V
                                        (@AddGroup.toSubNegMonoid V (@AddCommGroup.toAddGroup V inst_4))))))
                                (@DistribSMul.toSMulZeroClass S V
                                  (@AddMonoid.toAddZeroClass V
                                    (@SubNegMonoid.toAddMonoid V
                                      (@AddGroup.toSubNegMonoid V (@AddCommGroup.toAddGroup V inst_4))))
                                  (@DistribMulAction.toDistribSMul S V
                                    (@Semiring.toMonoid S (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst)))
                                    (@SubNegMonoid.toAddMonoid V
                                      (@AddGroup.toSubNegMonoid V (@AddCommGroup.toAddGroup V inst_4)))
                                    (@Module.toDistribMulAction S V
                                      (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst))
                                      (@AddCommGroup.toAddCommMonoid V inst_4) inst_6))))] →
                          @LinearMap K K
                              (@DivisionSemiring.toSemiring K
                                (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
                              (@DivisionSemiring.toSemiring K
                                (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
                              (@starRingEnd K (@Semifield.toCommSemiring K (@Field.toSemifield K inst_1)) inst_2) V
                              (@LinearMap K K
                                (@DivisionSemiring.toSemiring K
                                  (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
                                (@DivisionSemiring.toSemiring K
                                  (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
                                (@RingHom.id K
                                  (@Semiring.toNonAssocSemiring K
                                    (@DivisionSemiring.toSemiring K
                                      (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))))
                                V K (@AddCommGroup.toAddCommMonoid V inst_4)
                                (@Semiring.toAddCommMonoid K
                                  (@DivisionSemiring.toSemiring K
                                    (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1))))
                                inst_5
                                (@Semiring.toModule K
                                  (@DivisionSemiring.toSemiring K
                                    (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))))
                              (@AddCommGroup.toAddCommMonoid V inst_4)
                              (@LinearMap.addCommMonoid K K V K
                                (@DivisionSemiring.toSemiring K
                                  (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
                                (@DivisionSemiring.toSemiring K
                                  (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
                                (@AddCommGroup.toAddCommMonoid V inst_4)
                                (@Semiring.toAddCommMonoid K
                                  (@DivisionSemiring.toSemiring K
                                    (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1))))
                                inst_5
                                (@Semiring.toModule K
                                  (@DivisionSemiring.toSemiring K
                                    (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1))))
                                (@RingHom.id K
                                  (@Semiring.toNonAssocSemiring K
                                    (@DivisionSemiring.toSemiring K
                                      (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1))))))
                              inst_5
                              (@LinearMap.module K K K V K
                                (@DivisionSemiring.toSemiring K
                                  (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
                                (@DivisionSemiring.toSemiring K
                                  (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
                                (@AddCommGroup.toAddCommMonoid V inst_4)
                                (@Semiring.toAddCommMonoid K
                                  (@DivisionSemiring.toSemiring K
                                    (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1))))
                                inst_5
                                (@Semiring.toModule K
                                  (@DivisionSemiring.toSemiring K
                                    (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1))))
                                (@RingHom.id K
                                  (@Semiring.toNonAssocSemiring K
                                    (@DivisionSemiring.toSemiring K
                                      (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))))
                                (@DivisionSemiring.toSemiring K
                                  (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
                                (@Semiring.toModule K
                                  (@DivisionSemiring.toSemiring K
                                    (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1))))
                                (@Algebra.to_smulCommClass K K (@Semifield.toCommSemiring K (@Field.toSemifield K inst_1))
                                  (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst_1)))
                                  (@Algebra.id K (@Semifield.toCommSemiring K (@Field.toSemifield K inst_1))))) →
                            @Submodule S V (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst))
                                (@AddCommGroup.toAddCommMonoid V inst_4) inst_6 →
                              @Submodule S V (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst))
                                (@AddCommGroup.toAddCommMonoid V inst_4) inst_6 :=
    fun {S : Type u_1} {K : Type u_2} {V : Type u_3} [inst : CommRing S] [inst_1 : Field K]
        [inst_2 :
          @StarRing K
            (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring K
              (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing K
                (@NonUnitalCommRing.toNonUnitalNonAssocCommRing K
                  (@CommRing.toNonUnitalCommRing K (@Field.toCommRing K inst_1)))))]
        [inst_3 :
          @Algebra S K (@CommRing.toCommSemiring S inst)
            (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))]
        [inst_4 : AddCommGroup V]
        [inst_5 :
          @_root_.Module K V
            (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
            (@AddCommGroup.toAddCommMonoid V inst_4)]
        [inst_6 :
          @_root_.Module S V (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst))
            (@AddCommGroup.toAddCommMonoid V inst_4)]
        [inst_7 :
          @IsScalarTower S K V
            (@Algebra.toSMul S K (@CommRing.toCommSemiring S inst)
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1))) inst_3)
            (@SMulZeroClass.toSMul K V
              (@AddZero.toZero V
                (@AddZeroClass.toAddZero V
                  (@AddMonoid.toAddZeroClass V
                    (@SubNegMonoid.toAddMonoid V (@AddGroup.toSubNegMonoid V (@AddCommGroup.toAddGroup V inst_4))))))
              (@DistribSMul.toSMulZeroClass K V
                (@AddMonoid.toAddZeroClass V
                  (@SubNegMonoid.toAddMonoid V (@AddGroup.toSubNegMonoid V (@AddCommGroup.toAddGroup V inst_4))))
                (@DistribMulAction.toDistribSMul K V
                  (@Semiring.toMonoid K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1))))
                  (@SubNegMonoid.toAddMonoid V (@AddGroup.toSubNegMonoid V (@AddCommGroup.toAddGroup V inst_4)))
                  (@Module.toDistribMulAction K V
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
                    (@AddCommGroup.toAddCommMonoid V inst_4) inst_5))))
            (@SMulZeroClass.toSMul S V
              (@AddZero.toZero V
                (@AddZeroClass.toAddZero V
                  (@AddMonoid.toAddZeroClass V
                    (@SubNegMonoid.toAddMonoid V (@AddGroup.toSubNegMonoid V (@AddCommGroup.toAddGroup V inst_4))))))
              (@DistribSMul.toSMulZeroClass S V
                (@AddMonoid.toAddZeroClass V
                  (@SubNegMonoid.toAddMonoid V (@AddGroup.toSubNegMonoid V (@AddCommGroup.toAddGroup V inst_4))))
                (@DistribMulAction.toDistribSMul S V
                  (@Semiring.toMonoid S (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst)))
                  (@SubNegMonoid.toAddMonoid V (@AddGroup.toSubNegMonoid V (@AddCommGroup.toAddGroup V inst_4)))
                  (@Module.toDistribMulAction S V (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst))
                    (@AddCommGroup.toAddCommMonoid V inst_4) inst_6))))]
        (B :
          @LinearMap K K (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
            (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
            (@starRingEnd K (@Semifield.toCommSemiring K (@Field.toSemifield K inst_1)) inst_2) V
            (@LinearMap K K (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
              (@RingHom.id K
                (@Semiring.toNonAssocSemiring K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))))
              V K (@AddCommGroup.toAddCommMonoid V inst_4)
              (@Semiring.toAddCommMonoid K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1))))
              inst_5
              (@Semiring.toModule K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))))
            (@AddCommGroup.toAddCommMonoid V inst_4)
            (@LinearMap.addCommMonoid K K V K
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
              (@AddCommGroup.toAddCommMonoid V inst_4)
              (@Semiring.toAddCommMonoid K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1))))
              inst_5
              (@Semiring.toModule K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1))))
              (@RingHom.id K
                (@Semiring.toNonAssocSemiring K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1))))))
            inst_5
            (@LinearMap.module K K K V K
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
              (@AddCommGroup.toAddCommMonoid V inst_4)
              (@Semiring.toAddCommMonoid K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1))))
              inst_5
              (@Semiring.toModule K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1))))
              (@RingHom.id K
                (@Semiring.toNonAssocSemiring K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))))
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
              (@Semiring.toModule K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1))))
              (let p2m_original_helper : (∀ {K : Type _} [inst : Field K],
      @SMulCommClass K K K
        (@Algebra.toSMul K K (@Semifield.toCommSemiring K (@Field.toSemifield K inst))
          (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst)))
          (@Algebra.id K (@Semifield.toCommSemiring K (@Field.toSemifield K inst))))
        (@instSMulOfMul K
          (@Distrib.toMul K
            (@instDistribOfSemiring K
              (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst))))))) := (by
  intros; infer_instance
); @p2m_original_helper K inst_1)))
        (L :
          @Submodule S V (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst))
            (@AddCommGroup.toAddCommMonoid V inst_4) inst_6) ↦
      ⨅ (y : V),
        ⨅ (_ :
          @Membership.mem V
            (@Submodule S V (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst))
              (@AddCommGroup.toAddCommMonoid V inst_4) inst_6)
            (@SetLike.instMembership
              (@Submodule S V (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst))
                (@AddCommGroup.toAddCommMonoid V inst_4) inst_6)
              V
              (@Submodule.setLike S V (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst))
                (@AddCommGroup.toAddCommMonoid V inst_4) inst_6))
            L y),
          @Submodule.comap S S V K (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst))
            (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst)) (@AddCommGroup.toAddCommMonoid V inst_4)
            (@Semiring.toAddCommMonoid K
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1))))
            inst_6
            (@Algebra.toModule S K (@CommRing.toCommSemiring S inst)
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1))) inst_3)
            (@RingHom.id S (@Semiring.toNonAssocSemiring S (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst))))
            (@LinearMap.restrictScalars S K V K (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst))
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
              (@AddCommGroup.toAddCommMonoid V inst_4)
              (@Semiring.toAddCommMonoid K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1))))
              inst_6
              (@Algebra.toModule S K (@CommRing.toCommSemiring S inst)
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1))) inst_3)
              inst_5
              (@Semiring.toModule K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1))))
              (let p2m_original_helper : (∀ {S : Type _} {K : Type _} {V : Type _} [inst : CommRing S] [inst_1 : Field K]
      [inst_2 :
        @Algebra S K (@CommRing.toCommSemiring S inst)
          (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))]
      [inst_3 : AddCommGroup V]
      [inst_4 :
        @_root_.Module K V (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
          (@AddCommGroup.toAddCommMonoid V inst_3)]
      [inst_5 :
        @_root_.Module S V (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst))
          (@AddCommGroup.toAddCommMonoid V inst_3)]
      [@IsScalarTower S K V
          (@Algebra.toSMul S K (@CommRing.toCommSemiring S inst)
            (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1))) inst_2)
          (@SMulZeroClass.toSMul K V
            (@AddZero.toZero V
              (@AddZeroClass.toAddZero V
                (@AddMonoid.toAddZeroClass V
                  (@SubNegMonoid.toAddMonoid V (@AddGroup.toSubNegMonoid V (@AddCommGroup.toAddGroup V inst_3))))))
            (@DistribSMul.toSMulZeroClass K V
              (@AddMonoid.toAddZeroClass V
                (@SubNegMonoid.toAddMonoid V (@AddGroup.toSubNegMonoid V (@AddCommGroup.toAddGroup V inst_3))))
              (@DistribMulAction.toDistribSMul K V
                (@Semiring.toMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1))))
                (@SubNegMonoid.toAddMonoid V (@AddGroup.toSubNegMonoid V (@AddCommGroup.toAddGroup V inst_3)))
                (@Module.toDistribMulAction K V
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
                  (@AddCommGroup.toAddCommMonoid V inst_3) inst_4))))
          (@SMulZeroClass.toSMul S V
            (@AddZero.toZero V
              (@AddZeroClass.toAddZero V
                (@AddMonoid.toAddZeroClass V
                  (@SubNegMonoid.toAddMonoid V (@AddGroup.toSubNegMonoid V (@AddCommGroup.toAddGroup V inst_3))))))
            (@DistribSMul.toSMulZeroClass S V
              (@AddMonoid.toAddZeroClass V
                (@SubNegMonoid.toAddMonoid V (@AddGroup.toSubNegMonoid V (@AddCommGroup.toAddGroup V inst_3))))
              (@DistribMulAction.toDistribSMul S V
                (@Semiring.toMonoid S (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst)))
                (@SubNegMonoid.toAddMonoid V (@AddGroup.toSubNegMonoid V (@AddCommGroup.toAddGroup V inst_3)))
                (@Module.toDistribMulAction S V (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst))
                  (@AddCommGroup.toAddCommMonoid V inst_3) inst_5))))],
      @LinearMap.CompatibleSMul V K (@AddCommGroup.toAddCommMonoid V inst_3)
        (@Semiring.toAddCommMonoid K
          (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1))))
        S K (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
        (@SMulZeroClass.toSMul S V
          (@AddZero.toZero V
            (@AddZeroClass.toAddZero V
              (@AddMonoid.toAddZeroClass V (@AddCommMonoid.toAddMonoid V (@AddCommGroup.toAddCommMonoid V inst_3)))))
          (@DistribSMul.toSMulZeroClass S V
            (@AddMonoid.toAddZeroClass V (@AddCommMonoid.toAddMonoid V (@AddCommGroup.toAddCommMonoid V inst_3)))
            (@DistribMulAction.toDistribSMul S V
              (@Semiring.toMonoid S (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst)))
              (@AddCommMonoid.toAddMonoid V (@AddCommGroup.toAddCommMonoid V inst_3))
              (@Module.toDistribMulAction S V (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst))
                (@AddCommGroup.toAddCommMonoid V inst_3) inst_5))))
        inst_4
        (@SMulZeroClass.toSMul S K
          (@AddZero.toZero K
            (@AddZeroClass.toAddZero K
              (@AddMonoid.toAddZeroClass K
                (@AddCommMonoid.toAddMonoid K
                  (@Semiring.toAddCommMonoid K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1))))))))
          (@DistribSMul.toSMulZeroClass S K
            (@AddMonoid.toAddZeroClass K
              (@AddCommMonoid.toAddMonoid K
                (@Semiring.toAddCommMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1))))))
            (@DistribMulAction.toDistribSMul S K
              (@Semiring.toMonoid S (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst)))
              (@AddCommMonoid.toAddMonoid K
                (@Semiring.toAddCommMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))))
              (@Module.toDistribMulAction S K (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst))
                (@Semiring.toAddCommMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1))))
                (@Algebra.toModule S K (@CommRing.toCommSemiring S inst)
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
                  inst_2)))))
        (@Semiring.toModule K
          (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1))))) := (by
  intros; infer_instance
); @p2m_original_helper S K V inst inst_1 inst_3 inst_4 inst_5 inst_6 inst_7)
              (@DFunLike.coe
                (@LinearMap K K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
                  (@starRingEnd K (@Semifield.toCommSemiring K (@Field.toSemifield K inst_1)) inst_2) V
                  (@LinearMap K K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
                    (@RingHom.id K
                      (@Semiring.toNonAssocSemiring K
                        (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))))
                    V K (@AddCommGroup.toAddCommMonoid V inst_4)
                    (@Semiring.toAddCommMonoid K
                      (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1))))
                    inst_5
                    (@Semiring.toModule K
                      (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))))
                  (@AddCommGroup.toAddCommMonoid V inst_4)
                  (@LinearMap.addCommMonoid K K V K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
                    (@AddCommGroup.toAddCommMonoid V inst_4)
                    (@Semiring.toAddCommMonoid K
                      (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1))))
                    inst_5
                    (@Semiring.toModule K
                      (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1))))
                    (@RingHom.id K
                      (@Semiring.toNonAssocSemiring K
                        (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1))))))
                  inst_5
                  (@LinearMap.module K K K V K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
                    (@AddCommGroup.toAddCommMonoid V inst_4)
                    (@Semiring.toAddCommMonoid K
                      (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1))))
                    inst_5
                    (@Semiring.toModule K
                      (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1))))
                    (@RingHom.id K
                      (@Semiring.toNonAssocSemiring K
                        (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))))
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
                    (@Semiring.toModule K
                      (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1))))
                    (let p2m_original_helper : (∀ {K : Type _} [inst : Field K],
      @SMulCommClass K K K
        (@Algebra.toSMul K K (@Semifield.toCommSemiring K (@Field.toSemifield K inst))
          (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst)))
          (@Algebra.id K (@Semifield.toCommSemiring K (@Field.toSemifield K inst))))
        (@instSMulOfMul K
          (@Distrib.toMul K
            (@instDistribOfSemiring K
              (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst))))))) := (by
  intros; infer_instance
); @p2m_original_helper K inst_1)))
                V
                (fun (x : V) ↦
                  @LinearMap K K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
                    (@RingHom.id K
                      (@Semiring.toNonAssocSemiring K
                        (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))))
                    V K (@AddCommGroup.toAddCommMonoid V inst_4)
                    (@Semiring.toAddCommMonoid K
                      (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1))))
                    inst_5
                    (@Semiring.toModule K
                      (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))))
                (@LinearMap.instFunLike K K V
                  (@LinearMap K K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
                    (@RingHom.id K
                      (@Semiring.toNonAssocSemiring K
                        (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))))
                    V K (@AddCommGroup.toAddCommMonoid V inst_4)
                    (@Semiring.toAddCommMonoid K
                      (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1))))
                    inst_5
                    (@Semiring.toModule K
                      (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))))
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
                  (@AddCommGroup.toAddCommMonoid V inst_4)
                  (@LinearMap.addCommMonoid K K V K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
                    (@AddCommGroup.toAddCommMonoid V inst_4)
                    (@Semiring.toAddCommMonoid K
                      (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1))))
                    inst_5
                    (@Semiring.toModule K
                      (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1))))
                    (@RingHom.id K
                      (@Semiring.toNonAssocSemiring K
                        (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1))))))
                  inst_5
                  (@LinearMap.module K K K V K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
                    (@AddCommGroup.toAddCommMonoid V inst_4)
                    (@Semiring.toAddCommMonoid K
                      (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1))))
                    inst_5
                    (@Semiring.toModule K
                      (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1))))
                    (@RingHom.id K
                      (@Semiring.toNonAssocSemiring K
                        (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))))
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
                    (@Semiring.toModule K
                      (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1))))
                    (let p2m_original_helper : (∀ {K : Type _} [inst : Field K],
      @SMulCommClass K K K
        (@Algebra.toSMul K K (@Semifield.toCommSemiring K (@Field.toSemifield K inst))
          (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst)))
          (@Algebra.id K (@Semifield.toCommSemiring K (@Field.toSemifield K inst))))
        (@instSMulOfMul K
          (@Distrib.toMul K
            (@instDistribOfSemiring K
              (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst))))))) := (by
  intros; infer_instance
); @p2m_original_helper K inst_1))
                  (@starRingEnd K (@Semifield.toCommSemiring K (@Field.toSemifield K inst_1)) inst_2))
                B y))
            (@OfNat.ofNat
              (@Submodule S K (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst))
                (@Semiring.toAddCommMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1))))
                (@Algebra.toModule S K (@CommRing.toCommSemiring S inst)
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1))) inst_3))
              (nat_lit 1)
              (@One.toOfNat1
                (@Submodule S K (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst))
                  (@Semiring.toAddCommMonoid K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1))))
                  (@Algebra.toModule S K (@CommRing.toCommSemiring S inst)
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
                    inst_3))
                (@Submodule.one S (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst)) K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
                  (@Algebra.toModule S K (@CommRing.toCommSemiring S inst)
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
                    inst_3))))
noncomputable def UpperTheory.Reformulated.B.SelectionLemmas.dual.{u_1, u_2, u_3} :
    {R : Type u_1} →
      {K : Type u_2} →
        {V : Type u_3} →
          [inst : CommRing R] →
            [inst_1 : Field K] →
              [inst_2 :
                  @StarRing K
                    (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring K
                      (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing K
                        (@NonUnitalCommRing.toNonUnitalNonAssocCommRing K
                          (@CommRing.toNonUnitalCommRing K (@Field.toCommRing K inst_1)))))] →
                [inst_3 :
                    @Algebra R K (@CommRing.toCommSemiring R inst)
                      (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))] →
                  [inst_4 : AddCommGroup V] →
                    [inst_5 :
                        @_root_.Module K V
                          (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
                          (@AddCommGroup.toAddCommMonoid V inst_4)] →
                      [inst_6 :
                          @_root_.Module R V (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                            (@AddCommGroup.toAddCommMonoid V inst_4)] →
                        [@IsScalarTower R K V
                              (@Algebra.toSMul R K (@CommRing.toCommSemiring R inst)
                                (@DivisionSemiring.toSemiring K
                                  (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
                                inst_3)
                              (@SMulZeroClass.toSMul K V
                                (@AddZero.toZero V
                                  (@AddZeroClass.toAddZero V
                                    (@AddMonoid.toAddZeroClass V
                                      (@SubNegMonoid.toAddMonoid V
                                        (@AddGroup.toSubNegMonoid V (@AddCommGroup.toAddGroup V inst_4))))))
                                (@DistribSMul.toSMulZeroClass K V
                                  (@AddMonoid.toAddZeroClass V
                                    (@SubNegMonoid.toAddMonoid V
                                      (@AddGroup.toSubNegMonoid V (@AddCommGroup.toAddGroup V inst_4))))
                                  (@DistribMulAction.toDistribSMul K V
                                    (@Semiring.toMonoid K
                                      (@DivisionSemiring.toSemiring K
                                        (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1))))
                                    (@SubNegMonoid.toAddMonoid V
                                      (@AddGroup.toSubNegMonoid V (@AddCommGroup.toAddGroup V inst_4)))
                                    (@Module.toDistribMulAction K V
                                      (@DivisionSemiring.toSemiring K
                                        (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
                                      (@AddCommGroup.toAddCommMonoid V inst_4) inst_5))))
                              (@SMulZeroClass.toSMul R V
                                (@AddZero.toZero V
                                  (@AddZeroClass.toAddZero V
                                    (@AddMonoid.toAddZeroClass V
                                      (@SubNegMonoid.toAddMonoid V
                                        (@AddGroup.toSubNegMonoid V (@AddCommGroup.toAddGroup V inst_4))))))
                                (@DistribSMul.toSMulZeroClass R V
                                  (@AddMonoid.toAddZeroClass V
                                    (@SubNegMonoid.toAddMonoid V
                                      (@AddGroup.toSubNegMonoid V (@AddCommGroup.toAddGroup V inst_4))))
                                  (@DistribMulAction.toDistribSMul R V
                                    (@Semiring.toMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                                    (@SubNegMonoid.toAddMonoid V
                                      (@AddGroup.toSubNegMonoid V (@AddCommGroup.toAddGroup V inst_4)))
                                    (@Module.toDistribMulAction R V
                                      (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                      (@AddCommGroup.toAddCommMonoid V inst_4) inst_6))))] →
                          @LinearMap K K
                              (@DivisionSemiring.toSemiring K
                                (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
                              (@DivisionSemiring.toSemiring K
                                (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
                              (@starRingEnd K (@Semifield.toCommSemiring K (@Field.toSemifield K inst_1)) inst_2) V
                              (@LinearMap K K
                                (@DivisionSemiring.toSemiring K
                                  (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
                                (@DivisionSemiring.toSemiring K
                                  (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
                                (@RingHom.id K
                                  (@Semiring.toNonAssocSemiring K
                                    (@DivisionSemiring.toSemiring K
                                      (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))))
                                V K (@AddCommGroup.toAddCommMonoid V inst_4)
                                (@Semiring.toAddCommMonoid K
                                  (@DivisionSemiring.toSemiring K
                                    (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1))))
                                inst_5
                                (@Semiring.toModule K
                                  (@DivisionSemiring.toSemiring K
                                    (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))))
                              (@AddCommGroup.toAddCommMonoid V inst_4)
                              (@LinearMap.addCommMonoid K K V K
                                (@DivisionSemiring.toSemiring K
                                  (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
                                (@DivisionSemiring.toSemiring K
                                  (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
                                (@AddCommGroup.toAddCommMonoid V inst_4)
                                (@Semiring.toAddCommMonoid K
                                  (@DivisionSemiring.toSemiring K
                                    (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1))))
                                inst_5
                                (@Semiring.toModule K
                                  (@DivisionSemiring.toSemiring K
                                    (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1))))
                                (@RingHom.id K
                                  (@Semiring.toNonAssocSemiring K
                                    (@DivisionSemiring.toSemiring K
                                      (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1))))))
                              inst_5
                              (@LinearMap.module K K K V K
                                (@DivisionSemiring.toSemiring K
                                  (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
                                (@DivisionSemiring.toSemiring K
                                  (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
                                (@AddCommGroup.toAddCommMonoid V inst_4)
                                (@Semiring.toAddCommMonoid K
                                  (@DivisionSemiring.toSemiring K
                                    (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1))))
                                inst_5
                                (@Semiring.toModule K
                                  (@DivisionSemiring.toSemiring K
                                    (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1))))
                                (@RingHom.id K
                                  (@Semiring.toNonAssocSemiring K
                                    (@DivisionSemiring.toSemiring K
                                      (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))))
                                (@DivisionSemiring.toSemiring K
                                  (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
                                (@Semiring.toModule K
                                  (@DivisionSemiring.toSemiring K
                                    (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1))))
                                (@Algebra.to_smulCommClass K K (@Semifield.toCommSemiring K (@Field.toSemifield K inst_1))
                                  (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst_1)))
                                  (@Algebra.id K (@Semifield.toCommSemiring K (@Field.toSemifield K inst_1))))) →
                            @Submodule R V (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                (@AddCommGroup.toAddCommMonoid V inst_4) inst_6 →
                              @Submodule R V (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                (@AddCommGroup.toAddCommMonoid V inst_4) inst_6 :=
    fun {R : Type u_1} {K : Type u_2} {V : Type u_3} [inst : CommRing R] [inst_1 : Field K]
        [inst_2 :
          @StarRing K
            (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring K
              (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing K
                (@NonUnitalCommRing.toNonUnitalNonAssocCommRing K
                  (@CommRing.toNonUnitalCommRing K (@Field.toCommRing K inst_1)))))]
        [inst_3 :
          @Algebra R K (@CommRing.toCommSemiring R inst)
            (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))]
        [inst_4 : AddCommGroup V]
        [inst_5 :
          @_root_.Module K V
            (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
            (@AddCommGroup.toAddCommMonoid V inst_4)]
        [inst_6 :
          @_root_.Module R V (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
            (@AddCommGroup.toAddCommMonoid V inst_4)]
        [inst_7 :
          @IsScalarTower R K V
            (@Algebra.toSMul R K (@CommRing.toCommSemiring R inst)
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1))) inst_3)
            (@SMulZeroClass.toSMul K V
              (@AddZero.toZero V
                (@AddZeroClass.toAddZero V
                  (@AddMonoid.toAddZeroClass V
                    (@SubNegMonoid.toAddMonoid V (@AddGroup.toSubNegMonoid V (@AddCommGroup.toAddGroup V inst_4))))))
              (@DistribSMul.toSMulZeroClass K V
                (@AddMonoid.toAddZeroClass V
                  (@SubNegMonoid.toAddMonoid V (@AddGroup.toSubNegMonoid V (@AddCommGroup.toAddGroup V inst_4))))
                (@DistribMulAction.toDistribSMul K V
                  (@Semiring.toMonoid K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1))))
                  (@SubNegMonoid.toAddMonoid V (@AddGroup.toSubNegMonoid V (@AddCommGroup.toAddGroup V inst_4)))
                  (@Module.toDistribMulAction K V
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
                    (@AddCommGroup.toAddCommMonoid V inst_4) inst_5))))
            (@SMulZeroClass.toSMul R V
              (@AddZero.toZero V
                (@AddZeroClass.toAddZero V
                  (@AddMonoid.toAddZeroClass V
                    (@SubNegMonoid.toAddMonoid V (@AddGroup.toSubNegMonoid V (@AddCommGroup.toAddGroup V inst_4))))))
              (@DistribSMul.toSMulZeroClass R V
                (@AddMonoid.toAddZeroClass V
                  (@SubNegMonoid.toAddMonoid V (@AddGroup.toSubNegMonoid V (@AddCommGroup.toAddGroup V inst_4))))
                (@DistribMulAction.toDistribSMul R V
                  (@Semiring.toMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                  (@SubNegMonoid.toAddMonoid V (@AddGroup.toSubNegMonoid V (@AddCommGroup.toAddGroup V inst_4)))
                  (@Module.toDistribMulAction R V (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                    (@AddCommGroup.toAddCommMonoid V inst_4) inst_6))))]
        (h :
          @LinearMap K K (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
            (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
            (@starRingEnd K (@Semifield.toCommSemiring K (@Field.toSemifield K inst_1)) inst_2) V
            (@LinearMap K K (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
              (@RingHom.id K
                (@Semiring.toNonAssocSemiring K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))))
              V K (@AddCommGroup.toAddCommMonoid V inst_4)
              (@Semiring.toAddCommMonoid K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1))))
              inst_5
              (@Semiring.toModule K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))))
            (@AddCommGroup.toAddCommMonoid V inst_4)
            (@LinearMap.addCommMonoid K K V K
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
              (@AddCommGroup.toAddCommMonoid V inst_4)
              (@Semiring.toAddCommMonoid K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1))))
              inst_5
              (@Semiring.toModule K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1))))
              (@RingHom.id K
                (@Semiring.toNonAssocSemiring K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1))))))
            inst_5
            (@LinearMap.module K K K V K
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
              (@AddCommGroup.toAddCommMonoid V inst_4)
              (@Semiring.toAddCommMonoid K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1))))
              inst_5
              (@Semiring.toModule K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1))))
              (@RingHom.id K
                (@Semiring.toNonAssocSemiring K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))))
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
              (@Semiring.toModule K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1))))
              (let p2m_original_helper : (∀ {K : Type _} [inst : Field K],
      @SMulCommClass K K K
        (@Algebra.toSMul K K (@Semifield.toCommSemiring K (@Field.toSemifield K inst))
          (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst)))
          (@Algebra.id K (@Semifield.toCommSemiring K (@Field.toSemifield K inst))))
        (@instSMulOfMul K
          (@Distrib.toMul K
            (@instDistribOfSemiring K
              (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst))))))) := (by
  intros; infer_instance
); @p2m_original_helper K inst_1)))
        (L :
          @Submodule R V (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
            (@AddCommGroup.toAddCommMonoid V inst_4) inst_6) ↦
      @UpperTheory.Reformulated.B.SelectionLemmas.hdual R K V inst inst_1 inst_2 inst_3 inst_4 inst_5 inst_6 inst_7 h L
theorem UpperTheory.Reformulated.B.SelectionLemmas.aux6 :
    ∀ {K : Type} [inst : Field K],
      @RingHomInvPair K K (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst)))
        (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst)))
        (@RingHom.id K
          (@Semiring.toNonAssocSemiring K
            (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst)))))
        (@RingHom.id K
          (@Semiring.toNonAssocSemiring K
            (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst))))) := by
  intros; infer_instance
theorem UpperTheory.Reformulated.B.SelectionLemmas.aux7 :
    ∀ {K : Type} [inst : Field K],
      @SMulCommClass K K K
        (@Algebra.toSMul K K (@Semifield.toCommSemiring K (@Field.toSemifield K inst))
          (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst)))
          (@Algebra.id K (@Semifield.toCommSemiring K (@Field.toSemifield K inst))))
        (@instSMulOfMul K
          (@Distrib.toMul K
            (@instDistribOfSemiring K
              (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst)))))) := by
  intros; infer_instance
theorem UpperTheory.Reformulated.B.SelectionLemmas.aux8 :
    ∀ {K : Type} [inst : Field K] {n : Nat},
      @SMulCommClass K K
        (@LinearMap K K (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
          (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
          (@RingHom.id K
            (@Semiring.toNonAssocSemiring K
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
          (Fin n → K) K
          (@Pi.addCommMonoid (Fin n) (fun (a : Fin n) ↦ K) fun (i : Fin n) ↦
            @Semiring.toAddCommMonoid K
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
          (@Semiring.toAddCommMonoid K
            (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
          (@Pi.Function.module (Fin n) K K
            (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
            (@Semiring.toAddCommMonoid K
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
            (@Semiring.toModule K
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
          (@Semiring.toModule K
            (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
        (@LinearMap.instSMul K K K (Fin n → K) K
          (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
          (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
          (@Pi.addCommMonoid (Fin n) (fun (a : Fin n) ↦ K) fun (i : Fin n) ↦
            @Semiring.toAddCommMonoid K
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
          (@Semiring.toAddCommMonoid K
            (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
          (@Pi.Function.module (Fin n) K K
            (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
            (@Semiring.toAddCommMonoid K
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
            (@Semiring.toModule K
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
          (@Semiring.toModule K
            (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
          (@RingHom.id K
            (@Semiring.toNonAssocSemiring K
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
          (@DistribMulAction.toDistribSMul K K
            (@Semiring.toMonoid K
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
            (@AddCommMonoid.toAddMonoid K
              (@Semiring.toAddCommMonoid K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
            (@Module.toDistribMulAction K K
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
              (@Semiring.toAddCommMonoid K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
              (@Semiring.toModule K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))))
          (@UpperTheory.Reformulated.B.SelectionLemmas.aux7 K inst))
        (@LinearMap.instSMul K K K (Fin n → K) K
          (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
          (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
          (@Pi.addCommMonoid (Fin n) (fun (a : Fin n) ↦ K) fun (i : Fin n) ↦
            @Semiring.toAddCommMonoid K
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
          (@Semiring.toAddCommMonoid K
            (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
          (@Pi.Function.module (Fin n) K K
            (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
            (@Semiring.toAddCommMonoid K
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
            (@Semiring.toModule K
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
          (@Semiring.toModule K
            (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
          (@RingHom.id K
            (@Semiring.toNonAssocSemiring K
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
          (@DistribMulAction.toDistribSMul K K
            (@Semiring.toMonoid K (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst))))
            (@AddCommMonoid.toAddMonoid K
              (@Semiring.toAddCommMonoid K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
            (@Module.toDistribMulAction K K
              (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst)))
              (@Semiring.toAddCommMonoid K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
              (@Semiring.toModule K
                (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst))))))
          (@UpperTheory.Reformulated.B.SelectionLemmas.aux7 K inst)) := by
  intros; infer_instance
noncomputable def UpperTheory.Reformulated.B.SelectionLemmas.hform :
    {K : Type} →
      [inst : Field K] →
        [inst_1 :
            @StarRing K
              (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring K
                (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing K
                  (@NonUnitalCommRing.toNonUnitalNonAssocCommRing K
                    (@CommRing.toNonUnitalCommRing K (@Field.toCommRing K inst)))))] →
          {n : Nat} →
            Matrix (Fin n) (Fin n) K →
              @LinearMap K K (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@starRingEnd K (@Semifield.toCommSemiring K (@Field.toSemifield K inst)) inst_1) (Fin n → K)
                (@LinearMap K K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                  (@RingHom.id K
                    (@Semiring.toNonAssocSemiring K
                      (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
                  (Fin n → K) K
                  (@Pi.addCommMonoid (Fin n) (fun (a : Fin n) ↦ K) fun (i : Fin n) ↦
                    @Semiring.toAddCommMonoid K
                      (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                  (@Semiring.toAddCommMonoid K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                  (@Pi.Function.module (Fin n) K K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                    (@Semiring.toAddCommMonoid K
                      (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                    (@Semiring.toModule K
                      (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
                  (@Semiring.toModule K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
                (@Pi.addCommMonoid (Fin n) (fun (a : Fin n) ↦ K) fun (i : Fin n) ↦
                  @Semiring.toAddCommMonoid K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@LinearMap.addCommMonoid K K (Fin n → K) K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                  (@Pi.addCommMonoid (Fin n) (fun (a : Fin n) ↦ K) fun (i : Fin n) ↦
                    @Semiring.toAddCommMonoid K
                      (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                  (@Semiring.toAddCommMonoid K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                  (@Pi.Function.module (Fin n) K K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                    (@Semiring.toAddCommMonoid K
                      (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                    (@Semiring.toModule K
                      (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
                  (@Semiring.toModule K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                  (@RingHom.id K
                    (@Semiring.toNonAssocSemiring K
                      (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))))
                (@Pi.Function.module (Fin n) K K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                  (@Semiring.toAddCommMonoid K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                  (@Semiring.toModule K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
                (@LinearMap.module K K K (Fin n → K) K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                  (@Pi.addCommMonoid (Fin n) (fun (a : Fin n) ↦ K) fun (i : Fin n) ↦
                    @Semiring.toAddCommMonoid K
                      (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                  (@Semiring.toAddCommMonoid K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                  (@Pi.Function.module (Fin n) K K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                    (@Semiring.toAddCommMonoid K
                      (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                    (@Semiring.toModule K
                      (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
                  (@Semiring.toModule K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                  (@RingHom.id K
                    (@Semiring.toNonAssocSemiring K
                      (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                  (@Semiring.toModule K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                  (@Algebra.to_smulCommClass K K (@Semifield.toCommSemiring K (@Field.toSemifield K inst))
                    (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst)))
                    (@Algebra.id K (@Semifield.toCommSemiring K (@Field.toSemifield K inst))))) :=
    fun {K : Type} [inst : Field K]
        [inst_1 :
          @StarRing K
            (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring K
              (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing K
                (@NonUnitalCommRing.toNonUnitalNonAssocCommRing K
                  (@CommRing.toNonUnitalCommRing K (@Field.toCommRing K inst)))))]
        {n : Nat} (H : Matrix (Fin n) (Fin n) K) ↦
      @DFunLike.coe
        (@LinearEquiv K K (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst)))
          (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst)))
          (@RingHom.id K
            (@Semiring.toNonAssocSemiring K
              (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst)))))
          (@RingHom.id K
            (@Semiring.toNonAssocSemiring K
              (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst)))))
          (@UpperTheory.Reformulated.B.SelectionLemmas.aux6 K inst) (@UpperTheory.Reformulated.B.SelectionLemmas.aux6 K inst) (Matrix (Fin n) (Fin n) K)
          (@LinearMap K K (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
            (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
            (@starRingEnd K (@Semifield.toCommSemiring K (@Field.toSemifield K inst)) inst_1) (Fin n → K)
            (@LinearMap K K (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
              (@RingHom.id K
                (@Semiring.toNonAssocSemiring K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
              (Fin n → K) K
              (@Pi.addCommMonoid (Fin n) (fun (a : Fin n) ↦ K) fun (i : Fin n) ↦
                @Semiring.toAddCommMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
              (@Semiring.toAddCommMonoid K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
              (@Pi.Function.module (Fin n) K K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@Semiring.toAddCommMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@Semiring.toModule K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
              (@Semiring.toModule K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
            (@Pi.addCommMonoid (Fin n) (fun (a : Fin n) ↦ K) fun (i : Fin n) ↦
              @Semiring.toAddCommMonoid K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
            (@LinearMap.addCommMonoid K K (Fin n → K) K
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
              (@Pi.addCommMonoid (Fin n) (fun (a : Fin n) ↦ K) fun (i : Fin n) ↦
                @Semiring.toAddCommMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
              (@Semiring.toAddCommMonoid K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
              (@Pi.Function.module (Fin n) K K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@Semiring.toAddCommMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@Semiring.toModule K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
              (@Semiring.toModule K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
              (@RingHom.id K
                (@Semiring.toNonAssocSemiring K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))))
            (@Pi.Function.module (Fin n) K K
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
              (@Semiring.toAddCommMonoid K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
              (@Semiring.toModule K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
            (@LinearMap.module K K K (Fin n → K) K
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
              (@Pi.addCommMonoid (Fin n) (fun (a : Fin n) ↦ K) fun (i : Fin n) ↦
                @Semiring.toAddCommMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
              (@Semiring.toAddCommMonoid K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
              (@Pi.Function.module (Fin n) K K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@Semiring.toAddCommMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@Semiring.toModule K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
              (@Semiring.toModule K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
              (@RingHom.id K
                (@Semiring.toNonAssocSemiring K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
              (@Semiring.toModule K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
              (@UpperTheory.Reformulated.B.SelectionLemmas.aux7 K inst)))
          (@Matrix.addCommMonoid (Fin n) (Fin n) K
            (@Semiring.toAddCommMonoid K
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
          (@LinearMap.addCommMonoid K K (Fin n → K)
            (@LinearMap K K (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
              (@RingHom.id K
                (@Semiring.toNonAssocSemiring K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
              (Fin n → K) K
              (@Pi.addCommMonoid (Fin n) (fun (a : Fin n) ↦ K) fun (i : Fin n) ↦
                @Semiring.toAddCommMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
              (@Semiring.toAddCommMonoid K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
              (@Pi.Function.module (Fin n) K K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@Semiring.toAddCommMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@Semiring.toModule K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
              (@Semiring.toModule K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
            (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
            (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
            (@Pi.addCommMonoid (Fin n) (fun (a : Fin n) ↦ K) fun (i : Fin n) ↦
              @Semiring.toAddCommMonoid K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
            (@LinearMap.addCommMonoid K K (Fin n → K) K
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
              (@Pi.addCommMonoid (Fin n) (fun (a : Fin n) ↦ K) fun (i : Fin n) ↦
                @Semiring.toAddCommMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
              (@Semiring.toAddCommMonoid K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
              (@Pi.Function.module (Fin n) K K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@Semiring.toAddCommMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@Semiring.toModule K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
              (@Semiring.toModule K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
              (@RingHom.id K
                (@Semiring.toNonAssocSemiring K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))))
            (@Pi.Function.module (Fin n) K K
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
              (@Semiring.toAddCommMonoid K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
              (@Semiring.toModule K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
            (@LinearMap.module K K K (Fin n → K) K
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
              (@Pi.addCommMonoid (Fin n) (fun (a : Fin n) ↦ K) fun (i : Fin n) ↦
                @Semiring.toAddCommMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
              (@Semiring.toAddCommMonoid K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
              (@Pi.Function.module (Fin n) K K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@Semiring.toAddCommMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@Semiring.toModule K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
              (@Semiring.toModule K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
              (@RingHom.id K
                (@Semiring.toNonAssocSemiring K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
              (@Semiring.toModule K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
              (@UpperTheory.Reformulated.B.SelectionLemmas.aux7 K inst))
            (@starRingEnd K (@Semifield.toCommSemiring K (@Field.toSemifield K inst)) inst_1))
          (@Matrix.module (Fin n) (Fin n) K K
            (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst)))
            (@Semiring.toAddCommMonoid K
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
            (@Semiring.toModule K (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst)))))
          (@LinearMap.module K K K (Fin n → K)
            (@LinearMap K K (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
              (@RingHom.id K
                (@Semiring.toNonAssocSemiring K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
              (Fin n → K) K
              (@Pi.addCommMonoid (Fin n) (fun (a : Fin n) ↦ K) fun (i : Fin n) ↦
                @Semiring.toAddCommMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
              (@Semiring.toAddCommMonoid K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
              (@Pi.Function.module (Fin n) K K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@Semiring.toAddCommMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@Semiring.toModule K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
              (@Semiring.toModule K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
            (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
            (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
            (@Pi.addCommMonoid (Fin n) (fun (a : Fin n) ↦ K) fun (i : Fin n) ↦
              @Semiring.toAddCommMonoid K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
            (@LinearMap.addCommMonoid K K (Fin n → K) K
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
              (@Pi.addCommMonoid (Fin n) (fun (a : Fin n) ↦ K) fun (i : Fin n) ↦
                @Semiring.toAddCommMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
              (@Semiring.toAddCommMonoid K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
              (@Pi.Function.module (Fin n) K K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@Semiring.toAddCommMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@Semiring.toModule K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
              (@Semiring.toModule K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
              (@RingHom.id K
                (@Semiring.toNonAssocSemiring K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))))
            (@Pi.Function.module (Fin n) K K
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
              (@Semiring.toAddCommMonoid K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
              (@Semiring.toModule K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
            (@LinearMap.module K K K (Fin n → K) K
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
              (@Pi.addCommMonoid (Fin n) (fun (a : Fin n) ↦ K) fun (i : Fin n) ↦
                @Semiring.toAddCommMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
              (@Semiring.toAddCommMonoid K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
              (@Pi.Function.module (Fin n) K K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@Semiring.toAddCommMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@Semiring.toModule K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
              (@Semiring.toModule K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
              (@RingHom.id K
                (@Semiring.toNonAssocSemiring K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
              (@Semiring.toModule K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
              (@UpperTheory.Reformulated.B.SelectionLemmas.aux7 K inst))
            (@starRingEnd K (@Semifield.toCommSemiring K (@Field.toSemifield K inst)) inst_1)
            (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst)))
            (@LinearMap.module K K K (Fin n → K) K
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
              (@Pi.addCommMonoid (Fin n) (fun (a : Fin n) ↦ K) fun (i : Fin n) ↦
                @Semiring.toAddCommMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
              (@Semiring.toAddCommMonoid K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
              (@Pi.Function.module (Fin n) K K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@Semiring.toAddCommMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@Semiring.toModule K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
              (@Semiring.toModule K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
              (@RingHom.id K
                (@Semiring.toNonAssocSemiring K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
              (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst)))
              (@Semiring.toModule K (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst))))
              (@UpperTheory.Reformulated.B.SelectionLemmas.aux7 K inst))
            (@UpperTheory.Reformulated.B.SelectionLemmas.aux8 K inst n)))
        (Matrix (Fin n) (Fin n) K)
        (fun (x : Matrix (Fin n) (Fin n) K) ↦
          @LinearMap K K (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
            (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
            (@starRingEnd K (@Semifield.toCommSemiring K (@Field.toSemifield K inst)) inst_1) (Fin n → K)
            (@LinearMap K K (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
              (@RingHom.id K
                (@Semiring.toNonAssocSemiring K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
              (Fin n → K) K
              (@Pi.addCommMonoid (Fin n) (fun (a : Fin n) ↦ K) fun (i : Fin n) ↦
                @Semiring.toAddCommMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
              (@Semiring.toAddCommMonoid K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
              (@Pi.Function.module (Fin n) K K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@Semiring.toAddCommMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@Semiring.toModule K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
              (@Semiring.toModule K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
            (@Pi.addCommMonoid (Fin n) (fun (a : Fin n) ↦ K) fun (i : Fin n) ↦
              @Semiring.toAddCommMonoid K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
            (@LinearMap.addCommMonoid K K (Fin n → K) K
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
              (@Pi.addCommMonoid (Fin n) (fun (a : Fin n) ↦ K) fun (i : Fin n) ↦
                @Semiring.toAddCommMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
              (@Semiring.toAddCommMonoid K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
              (@Pi.Function.module (Fin n) K K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@Semiring.toAddCommMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@Semiring.toModule K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
              (@Semiring.toModule K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
              (@RingHom.id K
                (@Semiring.toNonAssocSemiring K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))))
            (@Pi.Function.module (Fin n) K K
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
              (@Semiring.toAddCommMonoid K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
              (@Semiring.toModule K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
            (@LinearMap.module K K K (Fin n → K) K
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
              (@Pi.addCommMonoid (Fin n) (fun (a : Fin n) ↦ K) fun (i : Fin n) ↦
                @Semiring.toAddCommMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
              (@Semiring.toAddCommMonoid K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
              (@Pi.Function.module (Fin n) K K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@Semiring.toAddCommMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@Semiring.toModule K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
              (@Semiring.toModule K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
              (@RingHom.id K
                (@Semiring.toNonAssocSemiring K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
              (@Semiring.toModule K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
              (@UpperTheory.Reformulated.B.SelectionLemmas.aux7 K inst)))
        (@EquivLike.toFunLike
          (@LinearEquiv K K (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst)))
            (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst)))
            (@RingHom.id K
              (@Semiring.toNonAssocSemiring K
                (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst)))))
            (@RingHom.id K
              (@Semiring.toNonAssocSemiring K
                (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst)))))
            (@UpperTheory.Reformulated.B.SelectionLemmas.aux6 K inst) (@UpperTheory.Reformulated.B.SelectionLemmas.aux6 K inst) (Matrix (Fin n) (Fin n) K)
            (@LinearMap K K (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
              (@starRingEnd K (@Semifield.toCommSemiring K (@Field.toSemifield K inst)) inst_1) (Fin n → K)
              (@LinearMap K K (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@RingHom.id K
                  (@Semiring.toNonAssocSemiring K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
                (Fin n → K) K
                (@Pi.addCommMonoid (Fin n) (fun (a : Fin n) ↦ K) fun (i : Fin n) ↦
                  @Semiring.toAddCommMonoid K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@Semiring.toAddCommMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@Pi.Function.module (Fin n) K K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                  (@Semiring.toAddCommMonoid K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                  (@Semiring.toModule K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
                (@Semiring.toModule K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
              (@Pi.addCommMonoid (Fin n) (fun (a : Fin n) ↦ K) fun (i : Fin n) ↦
                @Semiring.toAddCommMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
              (@LinearMap.addCommMonoid K K (Fin n → K) K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@Pi.addCommMonoid (Fin n) (fun (a : Fin n) ↦ K) fun (i : Fin n) ↦
                  @Semiring.toAddCommMonoid K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@Semiring.toAddCommMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@Pi.Function.module (Fin n) K K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                  (@Semiring.toAddCommMonoid K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                  (@Semiring.toModule K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
                (@Semiring.toModule K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@RingHom.id K
                  (@Semiring.toNonAssocSemiring K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))))
              (@Pi.Function.module (Fin n) K K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@Semiring.toAddCommMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@Semiring.toModule K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
              (@LinearMap.module K K K (Fin n → K) K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@Pi.addCommMonoid (Fin n) (fun (a : Fin n) ↦ K) fun (i : Fin n) ↦
                  @Semiring.toAddCommMonoid K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@Semiring.toAddCommMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@Pi.Function.module (Fin n) K K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                  (@Semiring.toAddCommMonoid K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                  (@Semiring.toModule K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
                (@Semiring.toModule K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@RingHom.id K
                  (@Semiring.toNonAssocSemiring K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@Semiring.toModule K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@UpperTheory.Reformulated.B.SelectionLemmas.aux7 K inst)))
            (@Matrix.addCommMonoid (Fin n) (Fin n) K
              (@Semiring.toAddCommMonoid K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
            (@LinearMap.addCommMonoid K K (Fin n → K)
              (@LinearMap K K (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@RingHom.id K
                  (@Semiring.toNonAssocSemiring K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
                (Fin n → K) K
                (@Pi.addCommMonoid (Fin n) (fun (a : Fin n) ↦ K) fun (i : Fin n) ↦
                  @Semiring.toAddCommMonoid K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@Semiring.toAddCommMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@Pi.Function.module (Fin n) K K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                  (@Semiring.toAddCommMonoid K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                  (@Semiring.toModule K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
                (@Semiring.toModule K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
              (@Pi.addCommMonoid (Fin n) (fun (a : Fin n) ↦ K) fun (i : Fin n) ↦
                @Semiring.toAddCommMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
              (@LinearMap.addCommMonoid K K (Fin n → K) K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@Pi.addCommMonoid (Fin n) (fun (a : Fin n) ↦ K) fun (i : Fin n) ↦
                  @Semiring.toAddCommMonoid K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@Semiring.toAddCommMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@Pi.Function.module (Fin n) K K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                  (@Semiring.toAddCommMonoid K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                  (@Semiring.toModule K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
                (@Semiring.toModule K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@RingHom.id K
                  (@Semiring.toNonAssocSemiring K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))))
              (@Pi.Function.module (Fin n) K K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@Semiring.toAddCommMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@Semiring.toModule K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
              (@LinearMap.module K K K (Fin n → K) K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@Pi.addCommMonoid (Fin n) (fun (a : Fin n) ↦ K) fun (i : Fin n) ↦
                  @Semiring.toAddCommMonoid K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@Semiring.toAddCommMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@Pi.Function.module (Fin n) K K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                  (@Semiring.toAddCommMonoid K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                  (@Semiring.toModule K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
                (@Semiring.toModule K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@RingHom.id K
                  (@Semiring.toNonAssocSemiring K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@Semiring.toModule K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@UpperTheory.Reformulated.B.SelectionLemmas.aux7 K inst))
              (@starRingEnd K (@Semifield.toCommSemiring K (@Field.toSemifield K inst)) inst_1))
            (@Matrix.module (Fin n) (Fin n) K K
              (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst)))
              (@Semiring.toAddCommMonoid K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
              (@Semiring.toModule K (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst)))))
            (@LinearMap.module K K K (Fin n → K)
              (@LinearMap K K (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@RingHom.id K
                  (@Semiring.toNonAssocSemiring K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
                (Fin n → K) K
                (@Pi.addCommMonoid (Fin n) (fun (a : Fin n) ↦ K) fun (i : Fin n) ↦
                  @Semiring.toAddCommMonoid K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@Semiring.toAddCommMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@Pi.Function.module (Fin n) K K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                  (@Semiring.toAddCommMonoid K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                  (@Semiring.toModule K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
                (@Semiring.toModule K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
              (@Pi.addCommMonoid (Fin n) (fun (a : Fin n) ↦ K) fun (i : Fin n) ↦
                @Semiring.toAddCommMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
              (@LinearMap.addCommMonoid K K (Fin n → K) K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@Pi.addCommMonoid (Fin n) (fun (a : Fin n) ↦ K) fun (i : Fin n) ↦
                  @Semiring.toAddCommMonoid K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@Semiring.toAddCommMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@Pi.Function.module (Fin n) K K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                  (@Semiring.toAddCommMonoid K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                  (@Semiring.toModule K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
                (@Semiring.toModule K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@RingHom.id K
                  (@Semiring.toNonAssocSemiring K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))))
              (@Pi.Function.module (Fin n) K K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@Semiring.toAddCommMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@Semiring.toModule K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
              (@LinearMap.module K K K (Fin n → K) K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@Pi.addCommMonoid (Fin n) (fun (a : Fin n) ↦ K) fun (i : Fin n) ↦
                  @Semiring.toAddCommMonoid K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@Semiring.toAddCommMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@Pi.Function.module (Fin n) K K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                  (@Semiring.toAddCommMonoid K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                  (@Semiring.toModule K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
                (@Semiring.toModule K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@RingHom.id K
                  (@Semiring.toNonAssocSemiring K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@Semiring.toModule K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@UpperTheory.Reformulated.B.SelectionLemmas.aux7 K inst))
              (@starRingEnd K (@Semifield.toCommSemiring K (@Field.toSemifield K inst)) inst_1)
              (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst)))
              (@LinearMap.module K K K (Fin n → K) K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@Pi.addCommMonoid (Fin n) (fun (a : Fin n) ↦ K) fun (i : Fin n) ↦
                  @Semiring.toAddCommMonoid K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@Semiring.toAddCommMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@Pi.Function.module (Fin n) K K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                  (@Semiring.toAddCommMonoid K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                  (@Semiring.toModule K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
                (@Semiring.toModule K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@RingHom.id K
                  (@Semiring.toNonAssocSemiring K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
                (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst)))
                (@Semiring.toModule K
                  (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst))))
                (@UpperTheory.Reformulated.B.SelectionLemmas.aux7 K inst))
              (@UpperTheory.Reformulated.B.SelectionLemmas.aux8 K inst n)))
          (Matrix (Fin n) (Fin n) K)
          (@LinearMap K K (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
            (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
            (@starRingEnd K (@Semifield.toCommSemiring K (@Field.toSemifield K inst)) inst_1) (Fin n → K)
            (@LinearMap K K (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
              (@RingHom.id K
                (@Semiring.toNonAssocSemiring K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
              (Fin n → K) K
              (@Pi.addCommMonoid (Fin n) (fun (a : Fin n) ↦ K) fun (i : Fin n) ↦
                @Semiring.toAddCommMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
              (@Semiring.toAddCommMonoid K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
              (@Pi.Function.module (Fin n) K K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@Semiring.toAddCommMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@Semiring.toModule K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
              (@Semiring.toModule K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
            (@Pi.addCommMonoid (Fin n) (fun (a : Fin n) ↦ K) fun (i : Fin n) ↦
              @Semiring.toAddCommMonoid K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
            (@LinearMap.addCommMonoid K K (Fin n → K) K
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
              (@Pi.addCommMonoid (Fin n) (fun (a : Fin n) ↦ K) fun (i : Fin n) ↦
                @Semiring.toAddCommMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
              (@Semiring.toAddCommMonoid K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
              (@Pi.Function.module (Fin n) K K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@Semiring.toAddCommMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@Semiring.toModule K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
              (@Semiring.toModule K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
              (@RingHom.id K
                (@Semiring.toNonAssocSemiring K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))))
            (@Pi.Function.module (Fin n) K K
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
              (@Semiring.toAddCommMonoid K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
              (@Semiring.toModule K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
            (@LinearMap.module K K K (Fin n → K) K
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
              (@Pi.addCommMonoid (Fin n) (fun (a : Fin n) ↦ K) fun (i : Fin n) ↦
                @Semiring.toAddCommMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
              (@Semiring.toAddCommMonoid K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
              (@Pi.Function.module (Fin n) K K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@Semiring.toAddCommMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@Semiring.toModule K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
              (@Semiring.toModule K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
              (@RingHom.id K
                (@Semiring.toNonAssocSemiring K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
              (@Semiring.toModule K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
              (@UpperTheory.Reformulated.B.SelectionLemmas.aux7 K inst)))
          (@DFinsupp.instEquivLikeLinearEquiv K K
            (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst)))
            (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst)))
            (@RingHom.id K
              (@Semiring.toNonAssocSemiring K
                (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst)))))
            (@RingHom.id K
              (@Semiring.toNonAssocSemiring K
                (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst)))))
            (@UpperTheory.Reformulated.B.SelectionLemmas.aux6 K inst) (@UpperTheory.Reformulated.B.SelectionLemmas.aux6 K inst) (Matrix (Fin n) (Fin n) K)
            (@LinearMap K K (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
              (@starRingEnd K (@Semifield.toCommSemiring K (@Field.toSemifield K inst)) inst_1) (Fin n → K)
              (@LinearMap K K (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@RingHom.id K
                  (@Semiring.toNonAssocSemiring K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
                (Fin n → K) K
                (@Pi.addCommMonoid (Fin n) (fun (a : Fin n) ↦ K) fun (i : Fin n) ↦
                  @Semiring.toAddCommMonoid K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@Semiring.toAddCommMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@Pi.Function.module (Fin n) K K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                  (@Semiring.toAddCommMonoid K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                  (@Semiring.toModule K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
                (@Semiring.toModule K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
              (@Pi.addCommMonoid (Fin n) (fun (a : Fin n) ↦ K) fun (i : Fin n) ↦
                @Semiring.toAddCommMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
              (@LinearMap.addCommMonoid K K (Fin n → K) K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@Pi.addCommMonoid (Fin n) (fun (a : Fin n) ↦ K) fun (i : Fin n) ↦
                  @Semiring.toAddCommMonoid K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@Semiring.toAddCommMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@Pi.Function.module (Fin n) K K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                  (@Semiring.toAddCommMonoid K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                  (@Semiring.toModule K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
                (@Semiring.toModule K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@RingHom.id K
                  (@Semiring.toNonAssocSemiring K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))))
              (@Pi.Function.module (Fin n) K K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@Semiring.toAddCommMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@Semiring.toModule K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
              (@LinearMap.module K K K (Fin n → K) K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@Pi.addCommMonoid (Fin n) (fun (a : Fin n) ↦ K) fun (i : Fin n) ↦
                  @Semiring.toAddCommMonoid K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@Semiring.toAddCommMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@Pi.Function.module (Fin n) K K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                  (@Semiring.toAddCommMonoid K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                  (@Semiring.toModule K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
                (@Semiring.toModule K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@RingHom.id K
                  (@Semiring.toNonAssocSemiring K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@Semiring.toModule K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@UpperTheory.Reformulated.B.SelectionLemmas.aux7 K inst)))
            (@Matrix.addCommMonoid (Fin n) (Fin n) K
              (@Semiring.toAddCommMonoid K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
            (@LinearMap.addCommMonoid K K (Fin n → K)
              (@LinearMap K K (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@RingHom.id K
                  (@Semiring.toNonAssocSemiring K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
                (Fin n → K) K
                (@Pi.addCommMonoid (Fin n) (fun (a : Fin n) ↦ K) fun (i : Fin n) ↦
                  @Semiring.toAddCommMonoid K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@Semiring.toAddCommMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@Pi.Function.module (Fin n) K K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                  (@Semiring.toAddCommMonoid K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                  (@Semiring.toModule K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
                (@Semiring.toModule K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
              (@Pi.addCommMonoid (Fin n) (fun (a : Fin n) ↦ K) fun (i : Fin n) ↦
                @Semiring.toAddCommMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
              (@LinearMap.addCommMonoid K K (Fin n → K) K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@Pi.addCommMonoid (Fin n) (fun (a : Fin n) ↦ K) fun (i : Fin n) ↦
                  @Semiring.toAddCommMonoid K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@Semiring.toAddCommMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@Pi.Function.module (Fin n) K K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                  (@Semiring.toAddCommMonoid K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                  (@Semiring.toModule K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
                (@Semiring.toModule K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@RingHom.id K
                  (@Semiring.toNonAssocSemiring K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))))
              (@Pi.Function.module (Fin n) K K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@Semiring.toAddCommMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@Semiring.toModule K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
              (@LinearMap.module K K K (Fin n → K) K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@Pi.addCommMonoid (Fin n) (fun (a : Fin n) ↦ K) fun (i : Fin n) ↦
                  @Semiring.toAddCommMonoid K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@Semiring.toAddCommMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@Pi.Function.module (Fin n) K K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                  (@Semiring.toAddCommMonoid K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                  (@Semiring.toModule K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
                (@Semiring.toModule K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@RingHom.id K
                  (@Semiring.toNonAssocSemiring K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@Semiring.toModule K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@UpperTheory.Reformulated.B.SelectionLemmas.aux7 K inst))
              (@starRingEnd K (@Semifield.toCommSemiring K (@Field.toSemifield K inst)) inst_1))
            (@Matrix.module (Fin n) (Fin n) K K
              (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst)))
              (@Semiring.toAddCommMonoid K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
              (@Semiring.toModule K (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst)))))
            (@LinearMap.module K K K (Fin n → K)
              (@LinearMap K K (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@RingHom.id K
                  (@Semiring.toNonAssocSemiring K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
                (Fin n → K) K
                (@Pi.addCommMonoid (Fin n) (fun (a : Fin n) ↦ K) fun (i : Fin n) ↦
                  @Semiring.toAddCommMonoid K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@Semiring.toAddCommMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@Pi.Function.module (Fin n) K K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                  (@Semiring.toAddCommMonoid K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                  (@Semiring.toModule K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
                (@Semiring.toModule K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
              (@Pi.addCommMonoid (Fin n) (fun (a : Fin n) ↦ K) fun (i : Fin n) ↦
                @Semiring.toAddCommMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
              (@LinearMap.addCommMonoid K K (Fin n → K) K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@Pi.addCommMonoid (Fin n) (fun (a : Fin n) ↦ K) fun (i : Fin n) ↦
                  @Semiring.toAddCommMonoid K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@Semiring.toAddCommMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@Pi.Function.module (Fin n) K K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                  (@Semiring.toAddCommMonoid K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                  (@Semiring.toModule K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
                (@Semiring.toModule K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@RingHom.id K
                  (@Semiring.toNonAssocSemiring K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))))
              (@Pi.Function.module (Fin n) K K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@Semiring.toAddCommMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@Semiring.toModule K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
              (@LinearMap.module K K K (Fin n → K) K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@Pi.addCommMonoid (Fin n) (fun (a : Fin n) ↦ K) fun (i : Fin n) ↦
                  @Semiring.toAddCommMonoid K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@Semiring.toAddCommMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@Pi.Function.module (Fin n) K K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                  (@Semiring.toAddCommMonoid K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                  (@Semiring.toModule K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
                (@Semiring.toModule K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@RingHom.id K
                  (@Semiring.toNonAssocSemiring K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@Semiring.toModule K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@UpperTheory.Reformulated.B.SelectionLemmas.aux7 K inst))
              (@starRingEnd K (@Semifield.toCommSemiring K (@Field.toSemifield K inst)) inst_1)
              (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst)))
              (@LinearMap.module K K K (Fin n → K) K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@Pi.addCommMonoid (Fin n) (fun (a : Fin n) ↦ K) fun (i : Fin n) ↦
                  @Semiring.toAddCommMonoid K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@Semiring.toAddCommMonoid K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@Pi.Function.module (Fin n) K K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                  (@Semiring.toAddCommMonoid K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                  (@Semiring.toModule K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
                (@Semiring.toModule K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@RingHom.id K
                  (@Semiring.toNonAssocSemiring K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
                (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst)))
                (@Semiring.toModule K
                  (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst))))
                (@UpperTheory.Reformulated.B.SelectionLemmas.aux7 K inst))
              (@UpperTheory.Reformulated.B.SelectionLemmas.aux8 K inst n))))
        (@Matrix.toLinearMapₛₗ₂' K K K K K K (Fin n) (Fin n) (@Semifield.toCommSemiring K (@Field.toSemifield K inst))
          (@Semiring.toAddCommMonoid K
            (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
          (@Semiring.toModule K (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst))))
          (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
          (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
          (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
          (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
          (@Semiring.toModule K
            (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
          (@Semiring.toModule K
            (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
          (@UpperTheory.Reformulated.B.SelectionLemmas.aux7 K inst) (@UpperTheory.Reformulated.B.SelectionLemmas.aux7 K inst) (@UpperTheory.Reformulated.B.SelectionLemmas.aux7 K inst)
          (@starRingEnd K (@Semifield.toCommSemiring K (@Field.toSemifield K inst)) inst_1)
          (@RingHom.id K
            (@Semiring.toNonAssocSemiring K
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
          (Fin.fintype n) (Fin.fintype n) (instDecidableEqFin n) (instDecidableEqFin n))
        H
noncomputable def UpperTheory.Reformulated.B.SelectionLemmas.locS.{u_1, u_4} :
    {R : Type u_1} →
      [inst : CommRing R] →
        {W : Type u_4} →
          [inst_1 : AddCommGroup W] →
            [inst_2 :
                @_root_.Module R W (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                  (@AddCommGroup.toAddCommMonoid W inst_1)] →
              @Submonoid R
                  (@MulZeroOneClass.toMulOneClass R
                    (@instMulZeroOneClassOfSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))) →
                @Submodule R W (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                    (@AddCommGroup.toAddCommMonoid W inst_1) inst_2 →
                  @Submodule R W (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                    (@AddCommGroup.toAddCommMonoid W inst_1) inst_2 :=
    fun {R : Type u_1} [inst : CommRing R] {W : Type u_4} [inst_1 : AddCommGroup W]
        [inst_2 :
          @_root_.Module R W (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
            (@AddCommGroup.toAddCommMonoid W inst_1)]
        (S :
          @Submonoid R
            (@MulZeroOneClass.toMulOneClass R
              (@instMulZeroOneClassOfSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))))
        (L :
          @Submodule R W (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
            (@AddCommGroup.toAddCommMonoid W inst_1) inst_2) ↦
      @Submodule.mk R W (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
        (@AddCommGroup.toAddCommMonoid W inst_1) inst_2
        (@AddSubmonoid.mk W
          (@AddMonoid.toAddZeroClass W (@AddCommMonoid.toAddMonoid W (@AddCommGroup.toAddCommMonoid W inst_1)))
          (@AddSubsemigroup.mk W
            (@AddZero.toAdd W
              (@AddZeroClass.toAddZero W
                (@AddMonoid.toAddZeroClass W (@AddCommMonoid.toAddMonoid W (@AddCommGroup.toAddCommMonoid W inst_1)))))
            (@Set.ofPred W fun (x : W) ↦
              ∃ (s : R),
                And
                  (@Membership.mem R
                    (@Submonoid R
                      (@MulZeroOneClass.toMulOneClass R
                        (@instMulZeroOneClassOfSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))))
                    (@SetLike.instMembership
                      (@Submonoid R
                        (@MulZeroOneClass.toMulOneClass R
                          (@instMulZeroOneClassOfSemiring R
                            (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))))
                      R
                      (@Submonoid.instSetLike R
                        (@MulZeroOneClass.toMulOneClass R
                          (@instMulZeroOneClassOfSemiring R
                            (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))))
                    S s)
                  (@Membership.mem W
                    (@Submodule R W (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                      (@AddCommGroup.toAddCommMonoid W inst_1) inst_2)
                    (@SetLike.instMembership
                      (@Submodule R W (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                        (@AddCommGroup.toAddCommMonoid W inst_1) inst_2)
                      W
                      (@Submodule.setLike R W (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                        (@AddCommGroup.toAddCommMonoid W inst_1) inst_2))
                    L
                    (@HSMul.hSMul R W W
                      (@instHSMul R W
                        (@SMulZeroClass.toSMul R W
                          (@AddZero.toZero W
                            (@AddZeroClass.toAddZero W
                              (@AddMonoid.toAddZeroClass W
                                (@SubNegMonoid.toAddMonoid W
                                  (@AddGroup.toSubNegMonoid W (@AddCommGroup.toAddGroup W inst_1))))))
                          (@DistribSMul.toSMulZeroClass R W
                            (@AddMonoid.toAddZeroClass W
                              (@SubNegMonoid.toAddMonoid W
                                (@AddGroup.toSubNegMonoid W (@AddCommGroup.toAddGroup W inst_1))))
                            (@DistribMulAction.toDistribSMul R W
                              (@Semiring.toMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                              (@SubNegMonoid.toAddMonoid W (@AddGroup.toSubNegMonoid W (@AddCommGroup.toAddGroup W inst_1)))
                              (@Module.toDistribMulAction R W (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                (@AddCommGroup.toAddCommMonoid W inst_1) inst_2)))))
                      s x)))
            (let p2m_original_helper : (∀ {R : Type _} [inst : CommRing R] {W : Type _} [inst_1 : AddCommGroup W]
      [inst_2 :
        @_root_.Module R W (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
          (@AddCommGroup.toAddCommMonoid W inst_1)]
      (S :
        @Submonoid R
          (@MulZeroOneClass.toMulOneClass R
            (@instMulZeroOneClassOfSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))))
      (L :
        @Submodule R W (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
          (@AddCommGroup.toAddCommMonoid W inst_1) inst_2)
      {x y : W},
      @Membership.mem W (Set W) (@Set.instMembership W)
          (@Set.ofPred W fun (x : W) ↦
            ∃ (s : R),
              And
                (@Membership.mem R
                  (@Submonoid R
                    (@MulZeroOneClass.toMulOneClass R
                      (@instMulZeroOneClassOfSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))))
                  (@SetLike.instMembership
                    (@Submonoid R
                      (@MulZeroOneClass.toMulOneClass R
                        (@instMulZeroOneClassOfSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))))
                    R
                    (@Submonoid.instSetLike R
                      (@MulZeroOneClass.toMulOneClass R
                        (@instMulZeroOneClassOfSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))))
                  S s)
                (@Membership.mem W
                  (@Submodule R W (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                    (@AddCommGroup.toAddCommMonoid W inst_1) inst_2)
                  (@SetLike.instMembership
                    (@Submodule R W (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                      (@AddCommGroup.toAddCommMonoid W inst_1) inst_2)
                    W
                    (@Submodule.setLike R W (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                      (@AddCommGroup.toAddCommMonoid W inst_1) inst_2))
                  L
                  (@HSMul.hSMul R W W
                    (@instHSMul R W
                      (@SMulZeroClass.toSMul R W
                        (@AddZero.toZero W
                          (@AddZeroClass.toAddZero W
                            (@AddMonoid.toAddZeroClass W
                              (@SubNegMonoid.toAddMonoid W
                                (@AddGroup.toSubNegMonoid W (@AddCommGroup.toAddGroup W inst_1))))))
                        (@DistribSMul.toSMulZeroClass R W
                          (@AddMonoid.toAddZeroClass W
                            (@SubNegMonoid.toAddMonoid W (@AddGroup.toSubNegMonoid W (@AddCommGroup.toAddGroup W inst_1))))
                          (@DistribMulAction.toDistribSMul R W
                            (@Semiring.toMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                            (@SubNegMonoid.toAddMonoid W (@AddGroup.toSubNegMonoid W (@AddCommGroup.toAddGroup W inst_1)))
                            (@Module.toDistribMulAction R W (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                              (@AddCommGroup.toAddCommMonoid W inst_1) inst_2)))))
                    s x)))
          x →
        @Membership.mem W (Set W) (@Set.instMembership W)
            (@Set.ofPred W fun (x : W) ↦
              ∃ (s : R),
                And
                  (@Membership.mem R
                    (@Submonoid R
                      (@MulZeroOneClass.toMulOneClass R
                        (@instMulZeroOneClassOfSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))))
                    (@SetLike.instMembership
                      (@Submonoid R
                        (@MulZeroOneClass.toMulOneClass R
                          (@instMulZeroOneClassOfSemiring R
                            (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))))
                      R
                      (@Submonoid.instSetLike R
                        (@MulZeroOneClass.toMulOneClass R
                          (@instMulZeroOneClassOfSemiring R
                            (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))))
                    S s)
                  (@Membership.mem W
                    (@Submodule R W (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                      (@AddCommGroup.toAddCommMonoid W inst_1) inst_2)
                    (@SetLike.instMembership
                      (@Submodule R W (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                        (@AddCommGroup.toAddCommMonoid W inst_1) inst_2)
                      W
                      (@Submodule.setLike R W (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                        (@AddCommGroup.toAddCommMonoid W inst_1) inst_2))
                    L
                    (@HSMul.hSMul R W W
                      (@instHSMul R W
                        (@SMulZeroClass.toSMul R W
                          (@AddZero.toZero W
                            (@AddZeroClass.toAddZero W
                              (@AddMonoid.toAddZeroClass W
                                (@SubNegMonoid.toAddMonoid W
                                  (@AddGroup.toSubNegMonoid W (@AddCommGroup.toAddGroup W inst_1))))))
                          (@DistribSMul.toSMulZeroClass R W
                            (@AddMonoid.toAddZeroClass W
                              (@SubNegMonoid.toAddMonoid W
                                (@AddGroup.toSubNegMonoid W (@AddCommGroup.toAddGroup W inst_1))))
                            (@DistribMulAction.toDistribSMul R W
                              (@Semiring.toMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                              (@SubNegMonoid.toAddMonoid W (@AddGroup.toSubNegMonoid W (@AddCommGroup.toAddGroup W inst_1)))
                              (@Module.toDistribMulAction R W (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                (@AddCommGroup.toAddCommMonoid W inst_1) inst_2)))))
                      s x)))
            y →
          @Membership.mem W (Set W) (@Set.instMembership W)
            (@Set.ofPred W fun (x : W) ↦
              ∃ (s : R),
                And
                  (@Membership.mem R
                    (@Submonoid R
                      (@MulZeroOneClass.toMulOneClass R
                        (@instMulZeroOneClassOfSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))))
                    (@SetLike.instMembership
                      (@Submonoid R
                        (@MulZeroOneClass.toMulOneClass R
                          (@instMulZeroOneClassOfSemiring R
                            (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))))
                      R
                      (@Submonoid.instSetLike R
                        (@MulZeroOneClass.toMulOneClass R
                          (@instMulZeroOneClassOfSemiring R
                            (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))))
                    S s)
                  (@Membership.mem W
                    (@Submodule R W (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                      (@AddCommGroup.toAddCommMonoid W inst_1) inst_2)
                    (@SetLike.instMembership
                      (@Submodule R W (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                        (@AddCommGroup.toAddCommMonoid W inst_1) inst_2)
                      W
                      (@Submodule.setLike R W (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                        (@AddCommGroup.toAddCommMonoid W inst_1) inst_2))
                    L
                    (@HSMul.hSMul R W W
                      (@instHSMul R W
                        (@SMulZeroClass.toSMul R W
                          (@AddZero.toZero W
                            (@AddZeroClass.toAddZero W
                              (@AddMonoid.toAddZeroClass W
                                (@SubNegMonoid.toAddMonoid W
                                  (@AddGroup.toSubNegMonoid W (@AddCommGroup.toAddGroup W inst_1))))))
                          (@DistribSMul.toSMulZeroClass R W
                            (@AddMonoid.toAddZeroClass W
                              (@SubNegMonoid.toAddMonoid W
                                (@AddGroup.toSubNegMonoid W (@AddCommGroup.toAddGroup W inst_1))))
                            (@DistribMulAction.toDistribSMul R W
                              (@Semiring.toMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                              (@SubNegMonoid.toAddMonoid W (@AddGroup.toSubNegMonoid W (@AddCommGroup.toAddGroup W inst_1)))
                              (@Module.toDistribMulAction R W (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                (@AddCommGroup.toAddCommMonoid W inst_1) inst_2)))))
                      s x)))
            (@HAdd.hAdd W W W
              (@instHAdd W
                (@AddZero.toAdd W
                  (@AddZeroClass.toAddZero W
                    (@AddMonoid.toAddZeroClass W (@AddCommMonoid.toAddMonoid W (@AddCommGroup.toAddCommMonoid W inst_1))))))
              x y)) := (by
  intro R _ W _ _ S L x y hx hy
  obtain ⟨s, hs, hx⟩ := hx
  obtain ⟨t, ht, hy⟩ := hy
  refine ⟨s * t, S.mul_mem hs ht, ?_⟩
  rw [smul_add]
  refine L.add_mem ?_ ?_
  · rw [mul_comm, mul_smul]; exact L.smul_mem _ hx
  · rw [mul_smul]; exact L.smul_mem _ hy
); @p2m_original_helper R inst W inst_1 inst_2 S L _ _))
          (let p2m_original_helper : (∀ {R : Type _} [inst : CommRing R] {W : Type _} [inst_1 : AddCommGroup W]
      [inst_2 :
        @_root_.Module R W (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
          (@AddCommGroup.toAddCommMonoid W inst_1)]
      (S :
        @Submonoid R
          (@MulZeroOneClass.toMulOneClass R
            (@instMulZeroOneClassOfSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))))
      (L :
        @Submodule R W (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
          (@AddCommGroup.toAddCommMonoid W inst_1) inst_2),
      ∃ (s : R),
        And
          (@Membership.mem R
            (@Submonoid R
              (@MulZeroOneClass.toMulOneClass R
                (@instMulZeroOneClassOfSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))))
            (@SetLike.instMembership
              (@Submonoid R
                (@MulZeroOneClass.toMulOneClass R
                  (@instMulZeroOneClassOfSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))))
              R
              (@Submonoid.instSetLike R
                (@MulZeroOneClass.toMulOneClass R
                  (@instMulZeroOneClassOfSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))))
            S s)
          (@Membership.mem W
            (@Submodule R W (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
              (@AddCommGroup.toAddCommMonoid W inst_1) inst_2)
            (@SetLike.instMembership
              (@Submodule R W (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                (@AddCommGroup.toAddCommMonoid W inst_1) inst_2)
              W
              (@Submodule.setLike R W (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                (@AddCommGroup.toAddCommMonoid W inst_1) inst_2))
            L
            (@HSMul.hSMul R W W
              (@instHSMul R W
                (@SMulZeroClass.toSMul R W
                  (@AddZero.toZero W
                    (@AddZeroClass.toAddZero W
                      (@AddMonoid.toAddZeroClass W
                        (@SubNegMonoid.toAddMonoid W (@AddGroup.toSubNegMonoid W (@AddCommGroup.toAddGroup W inst_1))))))
                  (@DistribSMul.toSMulZeroClass R W
                    (@AddMonoid.toAddZeroClass W
                      (@SubNegMonoid.toAddMonoid W (@AddGroup.toSubNegMonoid W (@AddCommGroup.toAddGroup W inst_1))))
                    (@DistribMulAction.toDistribSMul R W
                      (@Semiring.toMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                      (@SubNegMonoid.toAddMonoid W (@AddGroup.toSubNegMonoid W (@AddCommGroup.toAddGroup W inst_1)))
                      (@Module.toDistribMulAction R W (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                        (@AddCommGroup.toAddCommMonoid W inst_1) inst_2)))))
              s
              (@OfNat.ofNat W (nat_lit 0)
                (@Zero.toOfNat0 W
                  (@AddZero.toZero W
                    (@AddZeroClass.toAddZero W
                      (@AddMonoid.toAddZeroClass W
                        (@AddCommMonoid.toAddMonoid W (@AddCommGroup.toAddCommMonoid W inst_1)))))))))) := (by
  intro R _ W _ _ S L
  exact ⟨1, S.one_mem, by rw [smul_zero]; exact L.zero_mem⟩
); @p2m_original_helper R inst W inst_1 inst_2 S L))
        (let p2m_original_helper : (∀ {R : Type _} [inst : CommRing R] {W : Type _} [inst_1 : AddCommGroup W]
      [inst_2 :
        @_root_.Module R W (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
          (@AddCommGroup.toAddCommMonoid W inst_1)]
      (S :
        @Submonoid R
          (@MulZeroOneClass.toMulOneClass R
            (@instMulZeroOneClassOfSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))))
      (L :
        @Submodule R W (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
          (@AddCommGroup.toAddCommMonoid W inst_1) inst_2)
      (r : R) {x : W},
      @Membership.mem W (Set W) (@Set.instMembership W)
          (@Set.ofPred W fun (x : W) ↦
            ∃ (s : R),
              And
                (@Membership.mem R
                  (@Submonoid R
                    (@MulZeroOneClass.toMulOneClass R
                      (@instMulZeroOneClassOfSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))))
                  (@SetLike.instMembership
                    (@Submonoid R
                      (@MulZeroOneClass.toMulOneClass R
                        (@instMulZeroOneClassOfSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))))
                    R
                    (@Submonoid.instSetLike R
                      (@MulZeroOneClass.toMulOneClass R
                        (@instMulZeroOneClassOfSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))))
                  S s)
                (@Membership.mem W
                  (@Submodule R W (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                    (@AddCommGroup.toAddCommMonoid W inst_1) inst_2)
                  (@SetLike.instMembership
                    (@Submodule R W (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                      (@AddCommGroup.toAddCommMonoid W inst_1) inst_2)
                    W
                    (@Submodule.setLike R W (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                      (@AddCommGroup.toAddCommMonoid W inst_1) inst_2))
                  L
                  (@HSMul.hSMul R W W
                    (@instHSMul R W
                      (@SMulZeroClass.toSMul R W
                        (@AddZero.toZero W
                          (@AddZeroClass.toAddZero W
                            (@AddMonoid.toAddZeroClass W
                              (@SubNegMonoid.toAddMonoid W
                                (@AddGroup.toSubNegMonoid W (@AddCommGroup.toAddGroup W inst_1))))))
                        (@DistribSMul.toSMulZeroClass R W
                          (@AddMonoid.toAddZeroClass W
                            (@SubNegMonoid.toAddMonoid W (@AddGroup.toSubNegMonoid W (@AddCommGroup.toAddGroup W inst_1))))
                          (@DistribMulAction.toDistribSMul R W
                            (@Semiring.toMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                            (@SubNegMonoid.toAddMonoid W (@AddGroup.toSubNegMonoid W (@AddCommGroup.toAddGroup W inst_1)))
                            (@Module.toDistribMulAction R W (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                              (@AddCommGroup.toAddCommMonoid W inst_1) inst_2)))))
                    s x)))
          x →
        @Membership.mem W (Set W) (@Set.instMembership W)
          (@Set.ofPred W fun (x : W) ↦
            ∃ (s : R),
              And
                (@Membership.mem R
                  (@Submonoid R
                    (@MulZeroOneClass.toMulOneClass R
                      (@instMulZeroOneClassOfSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))))
                  (@SetLike.instMembership
                    (@Submonoid R
                      (@MulZeroOneClass.toMulOneClass R
                        (@instMulZeroOneClassOfSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))))
                    R
                    (@Submonoid.instSetLike R
                      (@MulZeroOneClass.toMulOneClass R
                        (@instMulZeroOneClassOfSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))))
                  S s)
                (@Membership.mem W
                  (@Submodule R W (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                    (@AddCommGroup.toAddCommMonoid W inst_1) inst_2)
                  (@SetLike.instMembership
                    (@Submodule R W (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                      (@AddCommGroup.toAddCommMonoid W inst_1) inst_2)
                    W
                    (@Submodule.setLike R W (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                      (@AddCommGroup.toAddCommMonoid W inst_1) inst_2))
                  L
                  (@HSMul.hSMul R W W
                    (@instHSMul R W
                      (@SMulZeroClass.toSMul R W
                        (@AddZero.toZero W
                          (@AddZeroClass.toAddZero W
                            (@AddMonoid.toAddZeroClass W
                              (@SubNegMonoid.toAddMonoid W
                                (@AddGroup.toSubNegMonoid W (@AddCommGroup.toAddGroup W inst_1))))))
                        (@DistribSMul.toSMulZeroClass R W
                          (@AddMonoid.toAddZeroClass W
                            (@SubNegMonoid.toAddMonoid W (@AddGroup.toSubNegMonoid W (@AddCommGroup.toAddGroup W inst_1))))
                          (@DistribMulAction.toDistribSMul R W
                            (@Semiring.toMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                            (@SubNegMonoid.toAddMonoid W (@AddGroup.toSubNegMonoid W (@AddCommGroup.toAddGroup W inst_1)))
                            (@Module.toDistribMulAction R W (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                              (@AddCommGroup.toAddCommMonoid W inst_1) inst_2)))))
                    s x)))
          (@HSMul.hSMul R W W
            (@instHSMul R W
              (@SMulZeroClass.toSMul R W
                (@AddZero.toZero W
                  (@AddZeroClass.toAddZero W
                    (@AddMonoid.toAddZeroClass W (@AddCommMonoid.toAddMonoid W (@AddCommGroup.toAddCommMonoid W inst_1)))))
                (@DistribSMul.toSMulZeroClass R W
                  (@AddMonoid.toAddZeroClass W (@AddCommMonoid.toAddMonoid W (@AddCommGroup.toAddCommMonoid W inst_1)))
                  (@DistribMulAction.toDistribSMul R W
                    (@Semiring.toMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                    (@AddCommMonoid.toAddMonoid W (@AddCommGroup.toAddCommMonoid W inst_1))
                    (@Module.toDistribMulAction R W (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                      (@AddCommGroup.toAddCommMonoid W inst_1) inst_2)))))
            r x)) := (by
  intro R _ W _ _ S L r x hx
  obtain ⟨s, hs, hx⟩ := hx
  refine ⟨s, hs, ?_⟩
  rw [smul_comm]
  exact L.smul_mem _ hx
); @p2m_original_helper R inst W inst_1 inst_2 S L)
noncomputable def UpperTheory.Reformulated.B.SelectionLemmas.hcompl.{u_1, u_2} :
    {R : Type u_1} →
      {K : Type u_2} →
        [inst : CommRing R] →
          [inst_1 : Field K] →
            [@StarRing K
                  (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring K
                    (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing K
                      (@NonUnitalCommRing.toNonUnitalNonAssocCommRing K
                        (@CommRing.toNonUnitalCommRing K (@Field.toCommRing K inst_1)))))] →
              [@Algebra R K (@CommRing.toCommSemiring R inst)
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))] →
                @Ideal R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)) →
                  @Submonoid R
                    (@MulZeroOneClass.toMulOneClass R
                      (@instMulZeroOneClassOfSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))) :=
    fun {R : Type u_1} {K : Type u_2} [inst : CommRing R] [inst_1 : Field K]
        [inst_2 :
          @StarRing K
            (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring K
              (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing K
                (@NonUnitalCommRing.toNonUnitalNonAssocCommRing K
                  (@CommRing.toNonUnitalCommRing K (@Field.toCommRing K inst_1)))))]
        [inst_3 :
          @Algebra R K (@CommRing.toCommSemiring R inst)
            (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))]
        (p : @Ideal R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))) ↦
      @Submonoid.closure R
        (@MulZeroOneClass.toMulOneClass R
          (@instMulZeroOneClassOfSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
        (@Set.ofPred R fun (s : R) ↦
          And (s ∉ p)
            (∀ (t : R),
              @Eq K
                  (@DFunLike.coe
                    (@RingHom R K
                      (@Semiring.toNonAssocSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                      (@Semiring.toNonAssocSemiring K
                        (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))))
                    R (fun (x : R) ↦ K)
                    (@RingHom.instFunLike R K
                      (@Semiring.toNonAssocSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                      (@Semiring.toNonAssocSemiring K
                        (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))))
                    (@Algebra.algebraMap R K (@CommRing.toCommSemiring R inst)
                      (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
                      inst_3)
                    t)
                  (@Star.star K
                    (@InvolutiveStar.toStar K
                      (@StarAddMonoid.toInvolutiveStar K
                        (@AddCommMonoid.toAddMonoid K
                          (@NonUnitalNonAssocSemiring.toAddCommMonoid K
                            (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring K
                              (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing K
                                (@NonUnitalCommRing.toNonUnitalNonAssocCommRing K
                                  (@CommRing.toNonUnitalCommRing K (@Field.toCommRing K inst_1)))))))
                        (@StarRing.toStarAddMonoid K
                          (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring K
                            (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing K
                              (@NonUnitalCommRing.toNonUnitalNonAssocCommRing K
                                (@CommRing.toNonUnitalCommRing K (@Field.toCommRing K inst_1)))))
                          inst_2)))
                    (@DFunLike.coe
                      (@RingHom R K
                        (@Semiring.toNonAssocSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                        (@Semiring.toNonAssocSemiring K
                          (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))))
                      R (fun (x : R) ↦ K)
                      (@RingHom.instFunLike R K
                        (@Semiring.toNonAssocSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                        (@Semiring.toNonAssocSemiring K
                          (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))))
                      (@Algebra.algebraMap R K (@CommRing.toCommSemiring R inst)
                        (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))
                        inst_3)
                      s)) →
                t ∉ p))
noncomputable def UpperTheory.Reformulated.B.SelectionLemmas.loc.{u_1, u_2, u_4} :
    {R : Type u_1} →
      {K : Type u_2} →
        [inst : CommRing R] →
          [inst_1 : Field K] →
            [@StarRing K
                  (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring K
                    (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing K
                      (@NonUnitalCommRing.toNonUnitalNonAssocCommRing K
                        (@CommRing.toNonUnitalCommRing K (@Field.toCommRing K inst_1)))))] →
              [@Algebra R K (@CommRing.toCommSemiring R inst)
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))] →
                {W : Type u_4} →
                  [inst_4 : AddCommGroup W] →
                    [inst_5 :
                        @_root_.Module R W (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                          (@AddCommGroup.toAddCommMonoid W inst_4)] →
                      @Ideal R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)) →
                        @Submodule R W (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                            (@AddCommGroup.toAddCommMonoid W inst_4) inst_5 →
                          @Submodule R W (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                            (@AddCommGroup.toAddCommMonoid W inst_4) inst_5 :=
    fun {R : Type u_1} {K : Type u_2} [inst : CommRing R] [inst_1 : Field K]
        [inst_2 :
          @StarRing K
            (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring K
              (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing K
                (@NonUnitalCommRing.toNonUnitalNonAssocCommRing K
                  (@CommRing.toNonUnitalCommRing K (@Field.toCommRing K inst_1)))))]
        [inst_3 :
          @Algebra R K (@CommRing.toCommSemiring R inst)
            (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst_1)))]
        {W : Type u_4} [inst_4 : AddCommGroup W]
        [inst_5 :
          @_root_.Module R W (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
            (@AddCommGroup.toAddCommMonoid W inst_4)]
        (p : @Ideal R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
        (L :
          @Submodule R W (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
            (@AddCommGroup.toAddCommMonoid W inst_4) inst_5) ↦
      @UpperTheory.Reformulated.B.SelectionLemmas.locS R inst W inst_4 inst_5 (@UpperTheory.Reformulated.B.SelectionLemmas.hcompl R K inst inst_1 inst_2 inst_3 p) L
noncomputable def UpperTheory.Reformulated.B.SelectionLemmas.IsLocBasis :
    {K : Type} →
      [inst : Field K] →
        [@StarRing K
              (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring K
                (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing K
                  (@NonUnitalCommRing.toNonUnitalNonAssocCommRing K
                    (@CommRing.toNonUnitalCommRing K (@Field.toCommRing K inst)))))] →
          {D : Nat} →
            @Submodule (@NumberField.RingOfIntegers K inst) (Fin D → K)
                (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
                  (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                    (@NumberField.instCommRingRingOfIntegers K inst)))
                (@Pi.addCommMonoid (Fin D) (fun (a : Fin D) ↦ K) fun (i : Fin D) ↦
                  @Semiring.toAddCommMonoid K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@Pi.Function.module (Fin D) (@NumberField.RingOfIntegers K inst) K
                  (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
                    (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                      (@NumberField.instCommRingRingOfIntegers K inst)))
                  (@Semiring.toAddCommMonoid K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                  (@Algebra.toModule (@NumberField.RingOfIntegers K inst) K
                    (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                      (@NumberField.instCommRingRingOfIntegers K inst))
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                    (@NumberField.RingOfIntegers.instAlgebra_1 K inst))) →
              @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers K inst)
                  (@NumberField.instCommRingRingOfIntegers K inst) →
                (Fin D → Fin D → K) → Prop :=
    fun {K : Type} [inst : Field K]
        [inst_1 :
          @StarRing K
            (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring K
              (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing K
                (@NonUnitalCommRing.toNonUnitalNonAssocCommRing K
                  (@CommRing.toNonUnitalCommRing K (@Field.toCommRing K inst)))))]
        {D : Nat}
        (L :
          @Submodule (@NumberField.RingOfIntegers K inst) (Fin D → K)
            (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
              (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                (@NumberField.instCommRingRingOfIntegers K inst)))
            (@Pi.addCommMonoid (Fin D) (fun (a : Fin D) ↦ K) fun (i : Fin D) ↦
              @Semiring.toAddCommMonoid K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
            (@Pi.Function.module (Fin D) (@NumberField.RingOfIntegers K inst) K
              (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
                (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                  (@NumberField.instCommRingRingOfIntegers K inst)))
              (@Semiring.toAddCommMonoid K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
              (@Algebra.toModule (@NumberField.RingOfIntegers K inst) K
                (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                  (@NumberField.instCommRingRingOfIntegers K inst))
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@NumberField.RingOfIntegers.instAlgebra_1 K inst))))
        (w :
          @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers K inst)
            (@NumberField.instCommRingRingOfIntegers K inst))
        (e : Fin D → Fin D → K) ↦
      And
        (@LinearIndependent (Fin D) K (Fin D → K) e
          (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
          (@Pi.addCommMonoid (Fin D) (fun (a : Fin D) ↦ K) fun (i : Fin D) ↦
            @Semiring.toAddCommMonoid K
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
          (@Pi.Function.module (Fin D) K K
            (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
            (@Semiring.toAddCommMonoid K
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
            (@Semiring.toModule K
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))))
        (@Eq
          (@Submodule (@NumberField.RingOfIntegers K inst) (Fin D → K)
            (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
              (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                (@NumberField.instCommRingRingOfIntegers K inst)))
            (@AddCommGroup.toAddCommMonoid (Fin D → K)
              (@Pi.addCommGroup (Fin D) (fun (a : Fin D) ↦ K) fun (i : Fin D) ↦
                @Ring.toAddCommGroup K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))))
            (@Pi.Function.module (Fin D) (@NumberField.RingOfIntegers K inst) K
              (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
                (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                  (@NumberField.instCommRingRingOfIntegers K inst)))
              (@Semiring.toAddCommMonoid K (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))))
              (@Algebra.toModule (@NumberField.RingOfIntegers K inst) K
                (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                  (@NumberField.instCommRingRingOfIntegers K inst))
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@NumberField.RingOfIntegers.instAlgebra_1 K inst))))
          (@UpperTheory.Reformulated.B.SelectionLemmas.loc (@NumberField.RingOfIntegers K inst) K (@NumberField.instCommRingRingOfIntegers K inst) inst
            inst_1 (@NumberField.RingOfIntegers.instAlgebra_1 K inst) (Fin D → K)
            (@Pi.addCommGroup (Fin D) (fun (a : Fin D) ↦ K) fun (i : Fin D) ↦
              @Ring.toAddCommGroup K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)))
            (@Pi.Function.module (Fin D) (@NumberField.RingOfIntegers K inst) K
              (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
                (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                  (@NumberField.instCommRingRingOfIntegers K inst)))
              (@Semiring.toAddCommMonoid K (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))))
              (@Algebra.toModule (@NumberField.RingOfIntegers K inst) K
                (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                  (@NumberField.instCommRingRingOfIntegers K inst))
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@NumberField.RingOfIntegers.instAlgebra_1 K inst)))
            (@IsDedekindDomain.HeightOneSpectrum.asIdeal (@NumberField.RingOfIntegers K inst)
              (@NumberField.instCommRingRingOfIntegers K inst) w)
            (@Submodule.span (@NumberField.RingOfIntegers K inst) (Fin D → K)
              (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
                (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                  (@NumberField.instCommRingRingOfIntegers K inst)))
              (@AddCommGroup.toAddCommMonoid (Fin D → K)
                (@Pi.addCommGroup (Fin D) (fun (a : Fin D) ↦ K) fun (i : Fin D) ↦
                  @Ring.toAddCommGroup K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))))
              (@Pi.Function.module (Fin D) (@NumberField.RingOfIntegers K inst) K
                (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
                  (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                    (@NumberField.instCommRingRingOfIntegers K inst)))
                (@Semiring.toAddCommMonoid K (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))))
                (@Algebra.toModule (@NumberField.RingOfIntegers K inst) K
                  (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                    (@NumberField.instCommRingRingOfIntegers K inst))
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                  (@NumberField.RingOfIntegers.instAlgebra_1 K inst)))
              (@Set.range (Fin D → K) (Fin D) e)))
          (@UpperTheory.Reformulated.B.SelectionLemmas.loc (@NumberField.RingOfIntegers K inst) K (@NumberField.instCommRingRingOfIntegers K inst) inst
            inst_1 (@NumberField.RingOfIntegers.instAlgebra_1 K inst) (Fin D → K)
            (@Pi.addCommGroup (Fin D) (fun (a : Fin D) ↦ K) fun (i : Fin D) ↦
              @Ring.toAddCommGroup K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)))
            (@Pi.Function.module (Fin D) (@NumberField.RingOfIntegers K inst) K
              (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
                (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                  (@NumberField.instCommRingRingOfIntegers K inst)))
              (@Semiring.toAddCommMonoid K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
              (@Algebra.toModule (@NumberField.RingOfIntegers K inst) K
                (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                  (@NumberField.instCommRingRingOfIntegers K inst))
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@NumberField.RingOfIntegers.instAlgebra_1 K inst)))
            (@IsDedekindDomain.HeightOneSpectrum.asIdeal (@NumberField.RingOfIntegers K inst)
              (@NumberField.instCommRingRingOfIntegers K inst) w)
            L))
theorem UpperTheory.Reformulated.B.SelectionLemmas.complex_normed_instance_compat :
    ∀ {K : Type} [inst : Field K],
      @RingHomSurjective (@NumberField.RingOfIntegers K inst) (@NumberField.RingOfIntegers K inst)
        (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
          (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst) (@NumberField.instCommRingRingOfIntegers K inst)))
        (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
          (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst) (@NumberField.instCommRingRingOfIntegers K inst)))
        (@RingHom.id (@NumberField.RingOfIntegers K inst)
          (@Semiring.toNonAssocSemiring (@NumberField.RingOfIntegers K inst)
            (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
              (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                (@NumberField.instCommRingRingOfIntegers K inst))))) := by
  intros; infer_instance
theorem UpperTheory.Reformulated.B.SelectionLemmas.padic_embedding_algebra_compat :
    ∀ {K : Type} [inst : Field K] {d d' : Nat},
      @LinearMap.CompatibleSMul (Fin d → K) (Fin d' → K)
        (@Pi.addCommMonoid (Fin d) (fun (a : Fin d) ↦ K) fun (i : Fin d) ↦
          @Semiring.toAddCommMonoid K
            (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst))))
        (@Pi.addCommMonoid (Fin d') (fun (a : Fin d') ↦ K) fun (i : Fin d') ↦
          @Semiring.toAddCommMonoid K
            (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst))))
        (@NumberField.RingOfIntegers K inst) K
        (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst)))
        (@SMulZeroClass.toSMul (@NumberField.RingOfIntegers K inst) (Fin d → K)
          (@AddZero.toZero (Fin d → K)
            (@AddZeroClass.toAddZero (Fin d → K)
              (@AddMonoid.toAddZeroClass (Fin d → K)
                (@AddCommMonoid.toAddMonoid (Fin d → K)
                  (@Pi.addCommMonoid (Fin d) (fun (a : Fin d) ↦ K) fun (i : Fin d) ↦
                    @Semiring.toAddCommMonoid K
                      (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst))))))))
          (@DistribSMul.toSMulZeroClass (@NumberField.RingOfIntegers K inst) (Fin d → K)
            (@AddMonoid.toAddZeroClass (Fin d → K)
              (@AddCommMonoid.toAddMonoid (Fin d → K)
                (@Pi.addCommMonoid (Fin d) (fun (a : Fin d) ↦ K) fun (i : Fin d) ↦
                  @Semiring.toAddCommMonoid K
                    (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst))))))
            (@DistribMulAction.toDistribSMul (@NumberField.RingOfIntegers K inst) (Fin d → K)
              (@Semiring.toMonoid (@NumberField.RingOfIntegers K inst)
                (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
                  (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                    (@NumberField.instCommRingRingOfIntegers K inst))))
              (@AddCommMonoid.toAddMonoid (Fin d → K)
                (@Pi.addCommMonoid (Fin d) (fun (a : Fin d) ↦ K) fun (i : Fin d) ↦
                  @Semiring.toAddCommMonoid K
                    (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst)))))
              (@Module.toDistribMulAction (@NumberField.RingOfIntegers K inst) (Fin d → K)
                (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
                  (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                    (@NumberField.instCommRingRingOfIntegers K inst)))
                (@Pi.addCommMonoid (Fin d) (fun (a : Fin d) ↦ K) fun (i : Fin d) ↦
                  @Semiring.toAddCommMonoid K
                    (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst))))
                (@Pi.Function.module (Fin d) (@NumberField.RingOfIntegers K inst) K
                  (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
                    (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                      (@NumberField.instCommRingRingOfIntegers K inst)))
                  (@Semiring.toAddCommMonoid K
                    (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst))))
                  (@Algebra.toModule (@NumberField.RingOfIntegers K inst) K
                    (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                      (@NumberField.instCommRingRingOfIntegers K inst))
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                    (@NumberField.RingOfIntegers.instAlgebra_1 K inst)))))))
        (@Pi.Function.module (Fin d) K K
          (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst)))
          (@Semiring.toAddCommMonoid K
            (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst))))
          (@Semiring.toModule K (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst)))))
        (@Function.hasSMul (Fin d') (@NumberField.RingOfIntegers K inst) K
          (@SemigroupAction.toSMul (@NumberField.RingOfIntegers K inst) K
            (@Monoid.toSemigroup (@NumberField.RingOfIntegers K inst)
              (@Semiring.toMonoid (@NumberField.RingOfIntegers K inst)
                (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
                  (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                    (@NumberField.instCommRingRingOfIntegers K inst)))))
            (@MulAction.toSemigroupAction (@NumberField.RingOfIntegers K inst) K
              (@Semiring.toMonoid (@NumberField.RingOfIntegers K inst)
                (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
                  (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                    (@NumberField.instCommRingRingOfIntegers K inst))))
              (@DistribMulAction.toMulAction (@NumberField.RingOfIntegers K inst) K
                (@Semiring.toMonoid (@NumberField.RingOfIntegers K inst)
                  (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
                    (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                      (@NumberField.instCommRingRingOfIntegers K inst))))
                (@AddCommMonoid.toAddMonoid K
                  (@Semiring.toAddCommMonoid K
                    (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst)))))
                (@Module.toDistribMulAction (@NumberField.RingOfIntegers K inst) K
                  (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
                    (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                      (@NumberField.instCommRingRingOfIntegers K inst)))
                  (@Semiring.toAddCommMonoid K
                    (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst))))
                  (@Algebra.toModule (@NumberField.RingOfIntegers K inst) K
                    (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                      (@NumberField.instCommRingRingOfIntegers K inst))
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                    (@NumberField.RingOfIntegers.instAlgebra_1 K inst)))))))
        (@Pi.Function.module (Fin d') K K
          (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst)))
          (@Semiring.toAddCommMonoid K
            (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst))))
          (@Semiring.toModule K (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst))))) := by
  intros; infer_instance
noncomputable def UpperTheory.Reformulated.B.SelectionLemmas.matLat :
    {K : Type} →
      [inst : Field K] →
        {d d' : Nat} →
          Matrix (Fin d') (Fin d) K →
            @Submodule (@NumberField.RingOfIntegers K inst) (Fin d → K)
                (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
                  (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                    (@NumberField.instCommRingRingOfIntegers K inst)))
                (@Pi.addCommMonoid (Fin d) (fun (a : Fin d) ↦ K) fun (i : Fin d) ↦
                  @Semiring.toAddCommMonoid K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@Pi.Function.module (Fin d) (@NumberField.RingOfIntegers K inst) K
                  (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
                    (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                      (@NumberField.instCommRingRingOfIntegers K inst)))
                  (@Semiring.toAddCommMonoid K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                  (@Algebra.toModule (@NumberField.RingOfIntegers K inst) K
                    (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                      (@NumberField.instCommRingRingOfIntegers K inst))
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                    (@NumberField.RingOfIntegers.instAlgebra_1 K inst))) →
              @Submodule (@NumberField.RingOfIntegers K inst) (Fin d' → K)
                (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
                  (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                    (@NumberField.instCommRingRingOfIntegers K inst)))
                (@Pi.addCommMonoid (Fin d') (fun (a : Fin d') ↦ K) fun (i : Fin d') ↦
                  @Semiring.toAddCommMonoid K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                (@Pi.Function.module (Fin d') (@NumberField.RingOfIntegers K inst) K
                  (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
                    (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                      (@NumberField.instCommRingRingOfIntegers K inst)))
                  (@Semiring.toAddCommMonoid K
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
                  (@Algebra.toModule (@NumberField.RingOfIntegers K inst) K
                    (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                      (@NumberField.instCommRingRingOfIntegers K inst))
                    (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                    (@NumberField.RingOfIntegers.instAlgebra_1 K inst))) :=
    fun {K : Type} [inst : Field K] {d d' : Nat} (φ : Matrix (Fin d') (Fin d) K)
        (L :
          @Submodule (@NumberField.RingOfIntegers K inst) (Fin d → K)
            (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
              (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                (@NumberField.instCommRingRingOfIntegers K inst)))
            (@Pi.addCommMonoid (Fin d) (fun (a : Fin d) ↦ K) fun (i : Fin d) ↦
              @Semiring.toAddCommMonoid K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
            (@Pi.Function.module (Fin d) (@NumberField.RingOfIntegers K inst) K
              (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
                (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                  (@NumberField.instCommRingRingOfIntegers K inst)))
              (@Semiring.toAddCommMonoid K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
              (@Algebra.toModule (@NumberField.RingOfIntegers K inst) K
                (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                  (@NumberField.instCommRingRingOfIntegers K inst))
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                (@NumberField.RingOfIntegers.instAlgebra_1 K inst)))) ↦
      @Submodule.map (@NumberField.RingOfIntegers K inst) (@NumberField.RingOfIntegers K inst) (Fin d → K) (Fin d' → K)
        (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
          (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst) (@NumberField.instCommRingRingOfIntegers K inst)))
        (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
          (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst) (@NumberField.instCommRingRingOfIntegers K inst)))
        (@Pi.addCommMonoid (Fin d) (fun (a : Fin d) ↦ K) fun (i : Fin d) ↦
          @Semiring.toAddCommMonoid K
            (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst))))
        (@Pi.addCommMonoid (Fin d') (fun (a : Fin d') ↦ K) fun (i : Fin d') ↦
          @Semiring.toAddCommMonoid K
            (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
        (@Pi.Function.module (Fin d) (@NumberField.RingOfIntegers K inst) K
          (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
            (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
              (@NumberField.instCommRingRingOfIntegers K inst)))
          (@Semiring.toAddCommMonoid K
            (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst))))
          (@Algebra.toModule (@NumberField.RingOfIntegers K inst) K
            (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst) (@NumberField.instCommRingRingOfIntegers K inst))
            (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
            (@NumberField.RingOfIntegers.instAlgebra_1 K inst)))
        (@Pi.Function.module (Fin d') (@NumberField.RingOfIntegers K inst) K
          (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
            (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
              (@NumberField.instCommRingRingOfIntegers K inst)))
          (@Semiring.toAddCommMonoid K
            (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
          (@Algebra.toModule (@NumberField.RingOfIntegers K inst) K
            (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst) (@NumberField.instCommRingRingOfIntegers K inst))
            (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
            (@NumberField.RingOfIntegers.instAlgebra_1 K inst)))
        (@RingHom.id (@NumberField.RingOfIntegers K inst)
          (@Semiring.toNonAssocSemiring (@NumberField.RingOfIntegers K inst)
            (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
              (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                (@NumberField.instCommRingRingOfIntegers K inst)))))
        (@UpperTheory.Reformulated.B.SelectionLemmas.complex_normed_instance_compat K inst)
        (@LinearMap.restrictScalars (@NumberField.RingOfIntegers K inst) K (Fin d → K) (Fin d' → K)
          (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
            (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
              (@NumberField.instCommRingRingOfIntegers K inst)))
          (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst)))
          (@Pi.addCommMonoid (Fin d) (fun (a : Fin d) ↦ K) fun (i : Fin d) ↦
            @Semiring.toAddCommMonoid K
              (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst))))
          (@Pi.addCommMonoid (Fin d') (fun (a : Fin d') ↦ K) fun (i : Fin d') ↦
            @Semiring.toAddCommMonoid K
              (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst))))
          (@Pi.Function.module (Fin d) (@NumberField.RingOfIntegers K inst) K
            (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
              (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                (@NumberField.instCommRingRingOfIntegers K inst)))
            (@Semiring.toAddCommMonoid K
              (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst))))
            (@Algebra.toModule (@NumberField.RingOfIntegers K inst) K
              (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                (@NumberField.instCommRingRingOfIntegers K inst))
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
              (@NumberField.RingOfIntegers.instAlgebra_1 K inst)))
          (@Pi.Function.module (Fin d') (@NumberField.RingOfIntegers K inst) K
            (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
              (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                (@NumberField.instCommRingRingOfIntegers K inst)))
            (@Semiring.toAddCommMonoid K
              (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst))))
            (@Algebra.toModule (@NumberField.RingOfIntegers K inst) K
              (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                (@NumberField.instCommRingRingOfIntegers K inst))
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
              (@NumberField.RingOfIntegers.instAlgebra_1 K inst)))
          (@Pi.Function.module (Fin d) K K
            (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst)))
            (@Semiring.toAddCommMonoid K
              (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst))))
            (@Semiring.toModule K (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst)))))
          (@Pi.Function.module (Fin d') K K
            (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst)))
            (@Semiring.toAddCommMonoid K
              (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst))))
            (@Semiring.toModule K (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst)))))
          (@UpperTheory.Reformulated.B.SelectionLemmas.padic_embedding_algebra_compat K inst d d')
          (@Matrix.mulVecLin K (@Semifield.toCommSemiring K (@Field.toSemifield K inst)) (Fin d') (Fin d) (Fin.fintype d)
            φ))
        L
noncomputable def UpperTheory.Reformulated.B.SelectionLemmas.vw :
    {K : Type} →
      [inst : Field K] →
        [@NumberField K inst] →
          @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers K inst)
              (@NumberField.instCommRingRingOfIntegers K inst) →
            K → Int :=
    fun {K : Type} [inst : Field K] [inst_1 : @NumberField K inst]
        (w :
          @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers K inst)
            (@NumberField.instCommRingRingOfIntegers K inst))
        (a : K) ↦
      @FractionalIdeal.count (@NumberField.RingOfIntegers K inst) (@NumberField.instCommRingRingOfIntegers K inst) K inst
        (@NumberField.RingOfIntegers.instAlgebra_1 K inst) (@NumberField.RingOfIntegers.instIsFractionRing K inst inst_1)
        (@NumberField.RingOfIntegers.instIsDedekindDomain K inst inst_1) w
        (@FractionalIdeal.spanSingleton (@NumberField.RingOfIntegers K inst)
          (@NumberField.instCommRingRingOfIntegers K inst)
          (@nonZeroDivisors (@NumberField.RingOfIntegers K inst)
            (@Semiring.toMonoidWithZero (@NumberField.RingOfIntegers K inst)
              (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
                (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                  (@NumberField.instCommRingRingOfIntegers K inst)))))
          K (@Field.toCommRing K inst) (@NumberField.RingOfIntegers.instAlgebra_1 K inst)
          (@NumberField.RingOfIntegers.instIsFractionRing K inst inst_1) a)
noncomputable def UpperTheory.Reformulated.B.SelectionLemmas.gramR :
    {K : Type} →
      [inst : Field K] →
        [@StarRing K
              (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring K
                (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing K
                  (@NonUnitalCommRing.toNonUnitalNonAssocCommRing K
                    (@CommRing.toNonUnitalCommRing K (@Field.toCommRing K inst)))))] →
          {D m : Nat} → Matrix (Fin D) (Fin D) K → (Fin m → Fin D → K) → K :=
    fun {K : Type} [inst : Field K]
        [inst_1 :
          @StarRing K
            (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring K
              (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing K
                (@NonUnitalCommRing.toNonUnitalNonAssocCommRing K
                  (@CommRing.toNonUnitalCommRing K (@Field.toCommRing K inst)))))]
        {D m : Nat} (Γ : Matrix (Fin D) (Fin D) K) (e : Fin m → Fin D → K) ↦
      @Matrix.det (Fin m) (instDecidableEqFin m) (Fin.fintype m) K (@Field.toCommRing K inst)
        (@DFunLike.coe (Equiv (Fin m → Fin m → K) (Matrix (Fin m) (Fin m) K)) (Fin m → Fin m → K)
          (fun (x : Fin m → Fin m → K) ↦ Matrix (Fin m) (Fin m) K)
          (@EquivLike.toFunLike (Equiv (Fin m → Fin m → K) (Matrix (Fin m) (Fin m) K)) (Fin m → Fin m → K)
            (Matrix (Fin m) (Fin m) K) (@Equiv.instEquivLike (Fin m → Fin m → K) (Matrix (Fin m) (Fin m) K)))
          (@Matrix.of (Fin m) (Fin m) K) fun (a b : Fin m) ↦
          @dotProduct (Fin D) K (Fin.fintype D)
            (@Distrib.toMul K
              (@instDistribOfSemiring K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
            (@Semiring.toAddCommMonoid K
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))))
            (@Star.star (Fin D → K)
              (@Pi.instStarForall (Fin D) (fun (a : Fin D) ↦ K) fun (i : Fin D) ↦
                @InvolutiveStar.toStar K
                  (@StarAddMonoid.toInvolutiveStar K
                    (@AddCommMonoid.toAddMonoid K
                      (@NonUnitalNonAssocSemiring.toAddCommMonoid K
                        (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring K
                          (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing K
                            (@NonUnitalCommRing.toNonUnitalNonAssocCommRing K
                              (@CommRing.toNonUnitalCommRing K (@Field.toCommRing K inst)))))))
                    (@StarRing.toStarAddMonoid K
                      (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring K
                        (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing K
                          (@NonUnitalCommRing.toNonUnitalNonAssocCommRing K
                            (@CommRing.toNonUnitalCommRing K (@Field.toCommRing K inst)))))
                      inst_1)))
              (e a))
            (@Matrix.mulVec (Fin D) (Fin D) K
              (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring K
                (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing K
                  (@NonUnitalCommRing.toNonUnitalNonAssocCommRing K
                    (@CommRing.toNonUnitalCommRing K (@Field.toCommRing K inst)))))
              (Fin.fintype D) Γ (e b)))
noncomputable def UpperTheory.Reformulated.B.SelectionLemmas.quotGram :
    {K : Type} →
      [inst : Field K] →
        [@StarRing K
              (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring K
                (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing K
                  (@NonUnitalCommRing.toNonUnitalNonAssocCommRing K
                    (@CommRing.toNonUnitalCommRing K (@Field.toCommRing K inst)))))] →
          {n D : Nat} → Matrix (Fin D) (Fin n) K → Matrix (Fin n) (Fin n) K → Matrix (Fin D) (Fin D) K :=
    fun {K : Type} [inst : Field K]
        [inst_1 :
          @StarRing K
            (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring K
              (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing K
                (@NonUnitalCommRing.toNonUnitalNonAssocCommRing K
                  (@CommRing.toNonUnitalCommRing K (@Field.toCommRing K inst)))))]
        {n D : Nat} (P : Matrix (Fin D) (Fin n) K) (H : Matrix (Fin n) (Fin n) K) ↦
      @Inv.inv (Matrix (Fin D) (Fin D) K)
        (@Matrix.inv (Fin D) K (Fin.fintype D) (instDecidableEqFin D) (@Field.toCommRing K inst))
        (@HMul.hMul (Matrix (Fin D) (Fin n) K) (Matrix (Fin n) (Fin D) K) (Matrix (Fin D) (Fin D) K)
          (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid (Fin D) (Fin n) (Fin D) K (Fin.fintype n)
            (@Distrib.toMul K
              (@instDistribOfSemiring K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
            (@Semiring.toAddCommMonoid K
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
          (@HMul.hMul (Matrix (Fin D) (Fin n) K) (Matrix (Fin n) (Fin n) K) (Matrix (Fin D) (Fin n) K)
            (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid (Fin D) (Fin n) (Fin n) K (Fin.fintype n)
              (@Distrib.toMul K
                (@instDistribOfSemiring K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
              (@Semiring.toAddCommMonoid K
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
            P
            (@Inv.inv (Matrix (Fin n) (Fin n) K)
              (@Matrix.inv (Fin n) K (Fin.fintype n) (instDecidableEqFin n) (@Field.toCommRing K inst)) H))
          (@Matrix.conjTranspose (Fin D) (Fin n) K
            (@InvolutiveStar.toStar K
              (@StarAddMonoid.toInvolutiveStar K
                (@AddCommMonoid.toAddMonoid K
                  (@NonUnitalNonAssocSemiring.toAddCommMonoid K
                    (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring K
                      (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing K
                        (@NonUnitalCommRing.toNonUnitalNonAssocCommRing K
                          (@CommRing.toNonUnitalCommRing K (@Field.toCommRing K inst)))))))
                (@StarRing.toStarAddMonoid K
                  (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring K
                    (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing K
                      (@NonUnitalCommRing.toNonUnitalNonAssocCommRing K
                        (@CommRing.toNonUnitalCommRing K (@Field.toCommRing K inst)))))
                  inst_1)))
            P))
section Helpers
open NumberField IsDedekindDomain Matrix
namespace UpperTheory.Reformulated.B.SelectionLemmas
end UpperTheory.Reformulated.B.SelectionLemmas
end Helpers


