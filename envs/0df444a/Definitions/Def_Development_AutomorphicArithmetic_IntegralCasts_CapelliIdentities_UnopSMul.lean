-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_UnopSMul
-- name    : Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_UnopSMul
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:40:55.94546+00:00
-- url     : https://prove2.me/theorems/98b1c4f9-a162-4c6c-9a9c-72623bd13165
-- title:
--   Unop SMul
-- statement:
--   Definitions and structural lemmas for Unop SMul, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/UnopSMul.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
theorem UpperTheory.Reformulated.B.Qk3.aux1 :
    ∀ {A : Type} [inst : CommRing A],
      @RingHomInvPair A A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))
        (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))
        (@RingHom.id A (@Semiring.toNonAssocSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))))
        (@RingHom.id A (@Semiring.toNonAssocSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst)))) := by
  intro A _
  exact RingHomInvPair.ids
noncomputable def UpperTheory.Reformulated.B.Qk3.unopS :
    (A E S : Type) →
      [inst : CommRing A] →
        [inst_1 : Ring E] →
          [inst_2 : @Algebra A E (@CommRing.toCommSemiring A inst) (@Ring.toSemiring E inst_1)] →
            [inst_3 : CommRing S] →
              [inst_4 :
                  @Algebra A S (@CommRing.toCommSemiring A inst)
                    (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_3))] →
                @LinearMap S S (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_3))
                  (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_3))
                  (@RingHom.id S
                    (@Semiring.toNonAssocSemiring S (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_3))))
                  (@TensorProduct A (@CommRing.toCommSemiring A inst) S (MulOpposite E)
                    (@Semiring.toAddCommMonoid S (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_3)))
                    (@MulOpposite.instAddCommMonoid E (@Semiring.toAddCommMonoid E (@Ring.toSemiring E inst_1)))
                    (@Algebra.toModule A S (@CommRing.toCommSemiring A inst)
                      (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_3)) inst_4)
                    (@MulOpposite.instModule A E (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))
                      (@Semiring.toAddCommMonoid E (@Ring.toSemiring E inst_1))
                      (@Algebra.toModule A E (@CommRing.toCommSemiring A inst) (@Ring.toSemiring E inst_1) inst_2)))
                  (@TensorProduct A (@CommRing.toCommSemiring A inst) S E
                    (@Semiring.toAddCommMonoid S (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_3)))
                    (@Semiring.toAddCommMonoid E (@Ring.toSemiring E inst_1))
                    (@Algebra.toModule A S (@CommRing.toCommSemiring A inst)
                      (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_3)) inst_4)
                    (@Algebra.toModule A E (@CommRing.toCommSemiring A inst) (@Ring.toSemiring E inst_1) inst_2))
                  (@TensorProduct.addCommMonoid A (@CommRing.toCommSemiring A inst) S (MulOpposite E)
                    (@Semiring.toAddCommMonoid S (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_3)))
                    (@MulOpposite.instAddCommMonoid E (@Semiring.toAddCommMonoid E (@Ring.toSemiring E inst_1)))
                    (@Algebra.toModule A S (@CommRing.toCommSemiring A inst)
                      (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_3)) inst_4)
                    (@MulOpposite.instModule A E (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))
                      (@Semiring.toAddCommMonoid E (@Ring.toSemiring E inst_1))
                      (@Algebra.toModule A E (@CommRing.toCommSemiring A inst) (@Ring.toSemiring E inst_1) inst_2)))
                  (@TensorProduct.addCommMonoid A (@CommRing.toCommSemiring A inst) S E
                    (@Semiring.toAddCommMonoid S (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_3)))
                    (@Semiring.toAddCommMonoid E (@Ring.toSemiring E inst_1))
                    (@Algebra.toModule A S (@CommRing.toCommSemiring A inst)
                      (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_3)) inst_4)
                    (@Algebra.toModule A E (@CommRing.toCommSemiring A inst) (@Ring.toSemiring E inst_1) inst_2))
                  (@TensorProduct.leftModule A S (@CommRing.toCommSemiring A inst)
                    (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_3)) S (MulOpposite E)
                    (@Semiring.toAddCommMonoid S (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_3)))
                    (@MulOpposite.instAddCommMonoid E (@Semiring.toAddCommMonoid E (@Ring.toSemiring E inst_1)))
                    (@Semiring.toModule S (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_3)))
                    (@Algebra.toModule A S (@CommRing.toCommSemiring A inst)
                      (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_3)) inst_4)
                    (@MulOpposite.instModule A E (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))
                      (@Semiring.toAddCommMonoid E (@Ring.toSemiring E inst_1))
                      (@Algebra.toModule A E (@CommRing.toCommSemiring A inst) (@Ring.toSemiring E inst_1) inst_2))
                    (@Algebra.to_smulCommClass A S (@CommRing.toCommSemiring A inst)
                      (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_3)) inst_4))
                  (@TensorProduct.leftModule A S (@CommRing.toCommSemiring A inst)
                    (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_3)) S E
                    (@Semiring.toAddCommMonoid S (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_3)))
                    (@Semiring.toAddCommMonoid E (@Ring.toSemiring E inst_1))
                    (@Semiring.toModule S (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_3)))
                    (@Algebra.toModule A S (@CommRing.toCommSemiring A inst)
                      (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_3)) inst_4)
                    (@Algebra.toModule A E (@CommRing.toCommSemiring A inst) (@Ring.toSemiring E inst_1) inst_2)
                    (@Algebra.to_smulCommClass A S (@CommRing.toCommSemiring A inst)
                      (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_3)) inst_4)) :=
    fun (A E S : Type) [inst : CommRing A] [inst_1 : Ring E]
        [inst_2 : @Algebra A E (@CommRing.toCommSemiring A inst) (@Ring.toSemiring E inst_1)] [inst_3 : CommRing S]
        [inst_4 :
          @Algebra A S (@CommRing.toCommSemiring A inst) (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_3))] ↦
      @LinearMap.baseChange A S (MulOpposite E) E (@CommRing.toCommSemiring A inst)
        (@CommSemiring.toSemiring S (@CommRing.toCommSemiring S inst_3)) inst_4
        (@MulOpposite.instAddCommMonoid E (@Semiring.toAddCommMonoid E (@Ring.toSemiring E inst_1)))
        (@Semiring.toAddCommMonoid E (@Ring.toSemiring E inst_1))
        (@MulOpposite.instModule A E (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))
          (@Semiring.toAddCommMonoid E (@Ring.toSemiring E inst_1))
          (@Algebra.toModule A E (@CommRing.toCommSemiring A inst) (@Ring.toSemiring E inst_1) inst_2))
        (@Algebra.toModule A E (@CommRing.toCommSemiring A inst) (@Ring.toSemiring E inst_1) inst_2)
        (@LinearEquiv.toLinearMap A A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))
          (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))
          (@RingHom.id A (@Semiring.toNonAssocSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))))
          (@RingHom.id A (@Semiring.toNonAssocSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))))
          (@UpperTheory.Reformulated.B.Qk3.aux1 A inst) (@UpperTheory.Reformulated.B.Qk3.aux1 A inst) (MulOpposite E) E
          (@MulOpposite.instAddCommMonoid E (@Semiring.toAddCommMonoid E (@Ring.toSemiring E inst_1)))
          (@Semiring.toAddCommMonoid E (@Ring.toSemiring E inst_1))
          (@MulOpposite.instModule A E (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))
            (@Semiring.toAddCommMonoid E (@Ring.toSemiring E inst_1))
            (@Algebra.toModule A E (@CommRing.toCommSemiring A inst) (@Ring.toSemiring E inst_1) inst_2))
          (@Algebra.toModule A E (@CommRing.toCommSemiring A inst) (@Ring.toSemiring E inst_1) inst_2)
          (@LinearEquiv.symm A A E (MulOpposite E) (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))
            (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))
            (@Semiring.toAddCommMonoid E (@Ring.toSemiring E inst_1))
            (@MulOpposite.instAddCommMonoid E (@Semiring.toAddCommMonoid E (@Ring.toSemiring E inst_1)))
            (@Algebra.toModule A E (@CommRing.toCommSemiring A inst) (@Ring.toSemiring E inst_1) inst_2)
            (@MulOpposite.instModule A E (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))
              (@Semiring.toAddCommMonoid E (@Ring.toSemiring E inst_1))
              (@Algebra.toModule A E (@CommRing.toCommSemiring A inst) (@Ring.toSemiring E inst_1) inst_2))
            (@RingHom.id A (@Semiring.toNonAssocSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))))
            (@RingHom.id A (@Semiring.toNonAssocSemiring A (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))))
            (@UpperTheory.Reformulated.B.Qk3.aux1 A inst) (@UpperTheory.Reformulated.B.Qk3.aux1 A inst)
            (@MulOpposite.opLinearEquiv A E (@CommSemiring.toSemiring A (@CommRing.toCommSemiring A inst))
              (@Semiring.toAddCommMonoid E (@Ring.toSemiring E inst_1))
              (@Algebra.toModule A E (@CommRing.toCommSemiring A inst) (@Ring.toSemiring E inst_1) inst_2))))


