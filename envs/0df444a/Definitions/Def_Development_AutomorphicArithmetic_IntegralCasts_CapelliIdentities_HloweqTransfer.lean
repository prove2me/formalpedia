-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_HloweqTransfer
-- name    : Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_HloweqTransfer
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:07:11.528367+00:00
-- url     : https://prove2.me/theorems/8cfca934-4271-4075-8b6e-5ff818325008
-- title:
--   Hloweq Transfer
-- statement:
--   Definitions and structural lemmas for Hloweq Transfer, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/HloweqTransfer.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable def UpperTheory.Reformulated.B.Re4.Jm :
    {n : Nat} → (Fin n → Bool) → Matrix (Fin n) (Fin n) Complex :=
    fun {n : Nat} (ε : Fin n → Bool) ↦
      @Matrix.diagonal (Fin n) Complex (instDecidableEqFin n) Complex.instZero fun (a : Fin n) ↦
        @ite Complex (@Eq Bool (ε a) Bool.true) (instDecidableEqBool (ε a) Bool.true)
          (@OfNat.ofNat Complex (nat_lit 1) (@One.toOfNat1 Complex Complex.instOne))
          (@Neg.neg Complex Complex.instNeg (@OfNat.ofNat Complex (nat_lit 1) (@One.toOfNat1 Complex Complex.instOne)))
noncomputable def UpperTheory.Reformulated.B.Re4.inUJ :
    {n : Nat} → (Fin n → Bool) → Matrix (Fin n) (Fin n) Complex → Prop :=
    fun {n : Nat} (ε : Fin n → Bool) (g : Matrix (Fin n) (Fin n) Complex) ↦
      @Eq (Matrix (Fin n) (Fin n) Complex)
        (@HMul.hMul (Matrix (Fin n) (Fin n) Complex) (Matrix (Fin n) (Fin n) Complex) (Matrix (Fin n) (Fin n) Complex)
          (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid (Fin n) (Fin n) (Fin n) Complex (Fin.fintype n) Complex.instMul
            Complex.instAddCommMonoid)
          (@HMul.hMul (Matrix (Fin n) (Fin n) Complex) (Matrix (Fin n) (Fin n) Complex) (Matrix (Fin n) (Fin n) Complex)
            (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid (Fin n) (Fin n) (Fin n) Complex (Fin.fintype n) Complex.instMul
              Complex.instAddCommMonoid)
            (@Matrix.conjTranspose (Fin n) (Fin n) Complex
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
              g)
            (@UpperTheory.Reformulated.B.Re4.Jm n ε))
          g)
        (@UpperTheory.Reformulated.B.Re4.Jm n ε)
theorem UpperTheory.Reformulated.B.Re4.aux3 :
    ∀ {n : Nat} (ε : Fin n → Bool)
      {g h :
        @Units (Matrix (Fin n) (Fin n) Complex)
          (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
            (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n)))},
      @Membership.mem
          (@Units (Matrix (Fin n) (Fin n) Complex)
            (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
              (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
          (Set
            (@Units (Matrix (Fin n) (Fin n) Complex)
              (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n)))))
          (@Set.instMembership
            (@Units (Matrix (Fin n) (Fin n) Complex)
              (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n)))))
          (@Set.ofPred
            (@Units (Matrix (Fin n) (Fin n) Complex)
              (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
            fun
              (g :
                @Units (Matrix (Fin n) (Fin n) Complex)
                  (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                    (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n)))) ↦
            @UpperTheory.Reformulated.B.Re4.inUJ n ε
              (@Units.val (Matrix (Fin n) (Fin n) Complex)
                (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                  (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n)))
                g))
          g →
        @Membership.mem
            (@Units (Matrix (Fin n) (Fin n) Complex)
              (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
            (Set
              (@Units (Matrix (Fin n) (Fin n) Complex)
                (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                  (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n)))))
            (@Set.instMembership
              (@Units (Matrix (Fin n) (Fin n) Complex)
                (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                  (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n)))))
            (@Set.ofPred
              (@Units (Matrix (Fin n) (Fin n) Complex)
                (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                  (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
              fun
                (g :
                  @Units (Matrix (Fin n) (Fin n) Complex)
                    (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                      (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n)))) ↦
              @UpperTheory.Reformulated.B.Re4.inUJ n ε
                (@Units.val (Matrix (Fin n) (Fin n) Complex)
                  (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                    (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n)))
                  g))
            h →
          @Membership.mem
            (@Units (Matrix (Fin n) (Fin n) Complex)
              (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
            (Set
              (@Units (Matrix (Fin n) (Fin n) Complex)
                (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                  (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n)))))
            (@Set.instMembership
              (@Units (Matrix (Fin n) (Fin n) Complex)
                (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                  (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n)))))
            (@Set.ofPred
              (@Units (Matrix (Fin n) (Fin n) Complex)
                (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                  (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
              fun
                (g :
                  @Units (Matrix (Fin n) (Fin n) Complex)
                    (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                      (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n)))) ↦
              @UpperTheory.Reformulated.B.Re4.inUJ n ε
                (@Units.val (Matrix (Fin n) (Fin n) Complex)
                  (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                    (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n)))
                  g))
            (@HMul.hMul
              (@Units (Matrix (Fin n) (Fin n) Complex)
                (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                  (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
              (@Units (Matrix (Fin n) (Fin n) Complex)
                (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                  (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
              (@Units (Matrix (Fin n) (Fin n) Complex)
                (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                  (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
              (@instHMul
                (@Units (Matrix (Fin n) (Fin n) Complex)
                  (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                    (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
                (@MulOne.toMul
                  (@Units (Matrix (Fin n) (Fin n) Complex)
                    (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                      (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
                  (@MulOneClass.toMulOne
                    (@Units (Matrix (Fin n) (Fin n) Complex)
                      (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                        (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
                    (@Monoid.toMulOneClass
                      (@Units (Matrix (Fin n) (Fin n) Complex)
                        (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                          (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
                      (@DivInvMonoid.toMonoid
                        (@Units (Matrix (Fin n) (Fin n) Complex)
                          (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                            (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
                        (@Group.toDivInvMonoid
                          (@Units (Matrix (Fin n) (Fin n) Complex)
                            (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                              (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n)
                                (instDecidableEqFin n))))
                          (@Units.instGroup (Matrix (Fin n) (Fin n) Complex)
                            (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                              (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n)
                                (instDecidableEqFin n))))))))))
              g h) := by
  intro n ε g h hg hh
  simp only [Set.mem_setOf_eq, UpperTheory.Reformulated.B.Re4.inUJ, Units.val_mul] at hg hh ⊢
  rw [Matrix.conjTranspose_mul]
  calc h.val.conjTranspose * g.val.conjTranspose * UpperTheory.Reformulated.B.Re4.Jm ε * (g.val * h.val)
      = h.val.conjTranspose * (g.val.conjTranspose * UpperTheory.Reformulated.B.Re4.Jm ε * g.val) * h.val := by
        simp only [Matrix.mul_assoc]
    _ = UpperTheory.Reformulated.B.Re4.Jm ε := by rw [hg, hh]
theorem UpperTheory.Reformulated.B.Re4.aux4 :
    ∀ {n : Nat} (ε : Fin n → Bool),
      @Eq (Matrix (Fin n) (Fin n) Complex)
        (@HMul.hMul (Matrix (Fin n) (Fin n) Complex) (Matrix (Fin n) (Fin n) Complex) (Matrix (Fin n) (Fin n) Complex)
          (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid (Fin n) (Fin n) (Fin n) Complex (Fin.fintype n) Complex.instMul
            Complex.instAddCommMonoid)
          (@HMul.hMul (Matrix (Fin n) (Fin n) Complex) (Matrix (Fin n) (Fin n) Complex) (Matrix (Fin n) (Fin n) Complex)
            (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid (Fin n) (Fin n) (Fin n) Complex (Fin.fintype n) Complex.instMul
              Complex.instAddCommMonoid)
            (@Matrix.conjTranspose (Fin n) (Fin n) Complex
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
              (@Units.val (Matrix (Fin n) (Fin n) Complex)
                (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                  (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n)))
                (@OfNat.ofNat
                  (@Units (Matrix (Fin n) (Fin n) Complex)
                    (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                      (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
                  (nat_lit 1)
                  (@One.toOfNat1
                    (@Units (Matrix (Fin n) (Fin n) Complex)
                      (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                        (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
                    (@MulOne.toOne
                      (@Units (Matrix (Fin n) (Fin n) Complex)
                        (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                          (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
                      (@MulOneClass.toMulOne
                        (@Units (Matrix (Fin n) (Fin n) Complex)
                          (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                            (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
                        (@Monoid.toMulOneClass
                          (@Units (Matrix (Fin n) (Fin n) Complex)
                            (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                              (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n)
                                (instDecidableEqFin n))))
                          (@DivInvMonoid.toMonoid
                            (@Units (Matrix (Fin n) (Fin n) Complex)
                              (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                                (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n)
                                  (instDecidableEqFin n))))
                            (@Group.toDivInvMonoid
                              (@Units (Matrix (Fin n) (Fin n) Complex)
                                (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                                  (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n)
                                    (instDecidableEqFin n))))
                              (@Units.instGroup (Matrix (Fin n) (Fin n) Complex)
                                (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                                  (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n)
                                    (instDecidableEqFin n)))))))))))))
            (@UpperTheory.Reformulated.B.Re4.Jm n ε))
          (@Units.val (Matrix (Fin n) (Fin n) Complex)
            (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
              (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n)))
            (@OfNat.ofNat
              (@Units (Matrix (Fin n) (Fin n) Complex)
                (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                  (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
              (nat_lit 1)
              (@One.toOfNat1
                (@Units (Matrix (Fin n) (Fin n) Complex)
                  (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                    (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
                (@MulOne.toOne
                  (@Units (Matrix (Fin n) (Fin n) Complex)
                    (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                      (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
                  (@MulOneClass.toMulOne
                    (@Units (Matrix (Fin n) (Fin n) Complex)
                      (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                        (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
                    (@Monoid.toMulOneClass
                      (@Units (Matrix (Fin n) (Fin n) Complex)
                        (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                          (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
                      (@DivInvMonoid.toMonoid
                        (@Units (Matrix (Fin n) (Fin n) Complex)
                          (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                            (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
                        (@Group.toDivInvMonoid
                          (@Units (Matrix (Fin n) (Fin n) Complex)
                            (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                              (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n)
                                (instDecidableEqFin n))))
                          (@Units.instGroup (Matrix (Fin n) (Fin n) Complex)
                            (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                              (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n)
                                (instDecidableEqFin n)))))))))))))
        (@UpperTheory.Reformulated.B.Re4.Jm n ε) := by
  intro n ε
  simp
theorem UpperTheory.Reformulated.B.Re4.aux5 :
    ∀ {n : Nat} (ε : Fin n → Bool)
      {g :
        @Units (Matrix (Fin n) (Fin n) Complex)
          (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
            (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n)))},
      @Membership.mem
          (@Units (Matrix (Fin n) (Fin n) Complex)
            (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
              (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
          (Set
            (@Units (Matrix (Fin n) (Fin n) Complex)
              (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n)))))
          (@Set.instMembership
            (@Units (Matrix (Fin n) (Fin n) Complex)
              (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n)))))
          (@Set.ofPred
            (@Units (Matrix (Fin n) (Fin n) Complex)
              (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
            fun
              (g :
                @Units (Matrix (Fin n) (Fin n) Complex)
                  (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                    (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n)))) ↦
            @UpperTheory.Reformulated.B.Re4.inUJ n ε
              (@Units.val (Matrix (Fin n) (Fin n) Complex)
                (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                  (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n)))
                g))
          g →
        @Membership.mem
          (@Units (Matrix (Fin n) (Fin n) Complex)
            (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
              (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
          (Set
            (@Units (Matrix (Fin n) (Fin n) Complex)
              (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n)))))
          (@Set.instMembership
            (@Units (Matrix (Fin n) (Fin n) Complex)
              (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n)))))
          (@Set.ofPred
            (@Units (Matrix (Fin n) (Fin n) Complex)
              (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
            fun
              (g :
                @Units (Matrix (Fin n) (Fin n) Complex)
                  (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                    (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n)))) ↦
            @UpperTheory.Reformulated.B.Re4.inUJ n ε
              (@Units.val (Matrix (Fin n) (Fin n) Complex)
                (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                  (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n)))
                g))
          (@Inv.inv
            (@Units (Matrix (Fin n) (Fin n) Complex)
              (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
            (@InvOneClass.toInv
              (@Units (Matrix (Fin n) (Fin n) Complex)
                (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                  (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
              (@DivInvOneMonoid.toInvOneClass
                (@Units (Matrix (Fin n) (Fin n) Complex)
                  (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                    (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
                (@DivisionMonoid.toDivInvOneMonoid
                  (@Units (Matrix (Fin n) (Fin n) Complex)
                    (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                      (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
                  (@Group.toDivisionMonoid
                    (@Units (Matrix (Fin n) (Fin n) Complex)
                      (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                        (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
                    (@Units.instGroup (Matrix (Fin n) (Fin n) Complex)
                      (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                        (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))))))
            g) := by
  intro n ε g hg
  simp only [Set.mem_setOf_eq, UpperTheory.Reformulated.B.Re4.inUJ] at hg ⊢
  have h1 : g.val * (g⁻¹).val = 1 := Units.mul_inv g
  calc (g⁻¹).val.conjTranspose * UpperTheory.Reformulated.B.Re4.Jm ε * (g⁻¹).val
      = (g⁻¹).val.conjTranspose * (g.val.conjTranspose * UpperTheory.Reformulated.B.Re4.Jm ε * g.val) * (g⁻¹).val := by
        rw [hg]
    _ = (g.val * (g⁻¹).val).conjTranspose * UpperTheory.Reformulated.B.Re4.Jm ε * (g.val * (g⁻¹).val) := by
        rw [Matrix.conjTranspose_mul]
        simp only [Matrix.mul_assoc]
    _ = UpperTheory.Reformulated.B.Re4.Jm ε := by
        rw [h1, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
noncomputable def UpperTheory.Reformulated.B.Re4.UJ :
    {n : Nat} →
      (Fin n → Bool) →
        @Subgroup
          (@Units (Matrix (Fin n) (Fin n) Complex)
            (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
              (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
          (@Units.instGroup (Matrix (Fin n) (Fin n) Complex)
            (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
              (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n)))) :=
    fun {n : Nat} (ε : Fin n → Bool) ↦
      @Subgroup.mk
        (@Units (Matrix (Fin n) (Fin n) Complex)
          (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
            (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
        (@Units.instGroup (Matrix (Fin n) (Fin n) Complex)
          (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
            (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
        (@Submonoid.mk
          (@Units (Matrix (Fin n) (Fin n) Complex)
            (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
              (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
          (@Monoid.toMulOneClass
            (@Units (Matrix (Fin n) (Fin n) Complex)
              (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
            (@DivInvMonoid.toMonoid
              (@Units (Matrix (Fin n) (Fin n) Complex)
                (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                  (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
              (@Group.toDivInvMonoid
                (@Units (Matrix (Fin n) (Fin n) Complex)
                  (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                    (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
                (@Units.instGroup (Matrix (Fin n) (Fin n) Complex)
                  (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                    (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n)))))))
          (@Subsemigroup.mk
            (@Units (Matrix (Fin n) (Fin n) Complex)
              (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
            (@MulOne.toMul
              (@Units (Matrix (Fin n) (Fin n) Complex)
                (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                  (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
              (@MulOneClass.toMulOne
                (@Units (Matrix (Fin n) (Fin n) Complex)
                  (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                    (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
                (@Monoid.toMulOneClass
                  (@Units (Matrix (Fin n) (Fin n) Complex)
                    (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                      (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
                  (@DivInvMonoid.toMonoid
                    (@Units (Matrix (Fin n) (Fin n) Complex)
                      (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                        (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
                    (@Group.toDivInvMonoid
                      (@Units (Matrix (Fin n) (Fin n) Complex)
                        (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                          (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
                      (@Units.instGroup (Matrix (Fin n) (Fin n) Complex)
                        (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                          (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n)
                            (instDecidableEqFin n)))))))))
            (@Set.ofPred
              (@Units (Matrix (Fin n) (Fin n) Complex)
                (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                  (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
              fun
                (g :
                  @Units (Matrix (Fin n) (Fin n) Complex)
                    (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                      (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n)))) ↦
              @UpperTheory.Reformulated.B.Re4.inUJ n ε
                (@Units.val (Matrix (Fin n) (Fin n) Complex)
                  (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                    (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n)))
                  g))
            (@UpperTheory.Reformulated.B.Re4.aux3 n ε))
          (@UpperTheory.Reformulated.B.Re4.aux4 n ε))
        (@UpperTheory.Reformulated.B.Re4.aux5 n ε)
@[reducible] noncomputable def UpperTheory.Reformulated.B.Re4.instMeasurableSpaceUJ :
    (n : Nat) → (ε : Fin n → Bool) → MeasurableSpace ↥(@UpperTheory.Reformulated.B.Re4.UJ n ε) :=
    fun (n : Nat) (ε : Fin n → Bool) ↦
      @borel (↥(@UpperTheory.Reformulated.B.Re4.UJ n ε))
        (@instTopologicalSpaceSubtype
          (@Units (Matrix (Fin n) (Fin n) Complex)
            (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
              (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
          (fun
              (x :
                @Units (Matrix (Fin n) (Fin n) Complex)
                  (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                    (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n)))) ↦
            @Membership.mem
              (@Units (Matrix (Fin n) (Fin n) Complex)
                (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                  (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
              (@Subgroup
                (@Units (Matrix (Fin n) (Fin n) Complex)
                  (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                    (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
                (@Units.instGroup (Matrix (Fin n) (Fin n) Complex)
                  (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                    (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n)))))
              (@SetLike.instMembership
                (@Subgroup
                  (@Units (Matrix (Fin n) (Fin n) Complex)
                    (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                      (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
                  (@Units.instGroup (Matrix (Fin n) (Fin n) Complex)
                    (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                      (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n)))))
                (@Units (Matrix (Fin n) (Fin n) Complex)
                  (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                    (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
                (@Subgroup.instSetLike
                  (@Units (Matrix (Fin n) (Fin n) Complex)
                    (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                      (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
                  (@Units.instGroup (Matrix (Fin n) (Fin n) Complex)
                    (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                      (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))))
              (@UpperTheory.Reformulated.B.Re4.UJ n ε) x)
          (@Units.instTopologicalSpaceUnits (Matrix (Fin n) (Fin n) Complex)
            (@instTopologicalSpaceMatrix (Fin n) (Fin n) Complex
              (@UniformSpace.toTopologicalSpace Complex
                (@PseudoMetricSpace.toUniformSpace Complex
                  (@SeminormedRing.toPseudoMetricSpace Complex
                    (@SeminormedCommRing.toSeminormedRing Complex
                      (@NormedCommRing.toSeminormedCommRing Complex
                        (@CommCStarAlgebra.toNormedCommRing Complex instCommCStarAlgebraComplex)))))))
            (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
              (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n)))))
attribute [local instance] UpperTheory.Reformulated.B.Re4.instMeasurableSpaceUJ
theorem UpperTheory.Reformulated.B.Re4.aux8 :
    ∀ {n : Nat} (ε : Fin n → Bool),
      @IsTopologicalGroup (↥(@UpperTheory.Reformulated.B.Re4.UJ n ε))
        (@instTopologicalSpaceSubtype
          (@Units (Matrix (Fin n) (Fin n) Complex)
            (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
              (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
          (fun
              (x :
                @Units (Matrix (Fin n) (Fin n) Complex)
                  (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                    (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n)))) ↦
            @Membership.mem
              (@Units (Matrix (Fin n) (Fin n) Complex)
                (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                  (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
              (@Subgroup
                (@Units (Matrix (Fin n) (Fin n) Complex)
                  (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                    (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
                (@Units.instGroup (Matrix (Fin n) (Fin n) Complex)
                  (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                    (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n)))))
              (@SetLike.instMembership
                (@Subgroup
                  (@Units (Matrix (Fin n) (Fin n) Complex)
                    (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                      (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
                  (@Units.instGroup (Matrix (Fin n) (Fin n) Complex)
                    (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                      (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n)))))
                (@Units (Matrix (Fin n) (Fin n) Complex)
                  (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                    (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
                (@Subgroup.instSetLike
                  (@Units (Matrix (Fin n) (Fin n) Complex)
                    (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                      (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
                  (@Units.instGroup (Matrix (Fin n) (Fin n) Complex)
                    (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                      (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))))
              (@UpperTheory.Reformulated.B.Re4.UJ n ε) x)
          (@Units.instTopologicalSpaceUnits (Matrix (Fin n) (Fin n) Complex)
            (@instTopologicalSpaceMatrix (Fin n) (Fin n) Complex
              (@UniformSpace.toTopologicalSpace Complex
                (@PseudoMetricSpace.toUniformSpace Complex
                  (@SeminormedRing.toPseudoMetricSpace Complex
                    (@SeminormedCommRing.toSeminormedRing Complex
                      (@NormedCommRing.toSeminormedCommRing Complex
                        (@CommCStarAlgebra.toNormedCommRing Complex instCommCStarAlgebraComplex)))))))
            (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
              (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n)))))
        (@Subgroup.toGroup
          (@Units (Matrix (Fin n) (Fin n) Complex)
            (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
              (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
          (@Units.instGroup (Matrix (Fin n) (Fin n) Complex)
            (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
              (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
          (@UpperTheory.Reformulated.B.Re4.UJ n ε)) := by
  intro n ε
  infer_instance
theorem UpperTheory.Reformulated.B.Re4.aux9 :
    ∀ (n : Nat) (ε : Fin n → Bool),
      @BorelSpace (↥(@UpperTheory.Reformulated.B.Re4.UJ n ε))
        (@instTopologicalSpaceSubtype
          (@Units (Matrix (Fin n) (Fin n) Complex)
            (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
              (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
          (fun
              (x :
                @Units (Matrix (Fin n) (Fin n) Complex)
                  (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                    (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n)))) ↦
            @Membership.mem
              (@Units (Matrix (Fin n) (Fin n) Complex)
                (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                  (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
              (@Subgroup
                (@Units (Matrix (Fin n) (Fin n) Complex)
                  (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                    (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
                (@Units.instGroup (Matrix (Fin n) (Fin n) Complex)
                  (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                    (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n)))))
              (@SetLike.instMembership
                (@Subgroup
                  (@Units (Matrix (Fin n) (Fin n) Complex)
                    (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                      (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
                  (@Units.instGroup (Matrix (Fin n) (Fin n) Complex)
                    (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                      (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n)))))
                (@Units (Matrix (Fin n) (Fin n) Complex)
                  (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                    (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
                (@Subgroup.instSetLike
                  (@Units (Matrix (Fin n) (Fin n) Complex)
                    (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                      (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
                  (@Units.instGroup (Matrix (Fin n) (Fin n) Complex)
                    (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                      (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))))
              (@UpperTheory.Reformulated.B.Re4.UJ n ε) x)
          (@Units.instTopologicalSpaceUnits (Matrix (Fin n) (Fin n) Complex)
            (@instTopologicalSpaceMatrix (Fin n) (Fin n) Complex
              (@UniformSpace.toTopologicalSpace Complex
                (@PseudoMetricSpace.toUniformSpace Complex
                  (@SeminormedRing.toPseudoMetricSpace Complex
                    (@SeminormedCommRing.toSeminormedRing Complex
                      (@NormedCommRing.toSeminormedCommRing Complex
                        (@CommCStarAlgebra.toNormedCommRing Complex instCommCStarAlgebraComplex)))))))
            (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
              (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n)))))
        (UpperTheory.Reformulated.B.Re4.instMeasurableSpaceUJ n ε) := by
  intro n ε
  exact @BorelSpace.mk _ _ (UpperTheory.Reformulated.B.Re4.instMeasurableSpaceUJ n ε) rfl
theorem UpperTheory.Reformulated.B.Re4.laurent_T_neg_one_mul_T_one :
    ∀ (n : Nat) (ε : Fin n → Bool),
      @LocallyCompactSpace (↥(@UpperTheory.Reformulated.B.Re4.UJ n ε))
        (@instTopologicalSpaceSubtype
          (@Units (Matrix (Fin n) (Fin n) Complex)
            (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
              (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
          (fun
              (x :
                @Units (Matrix (Fin n) (Fin n) Complex)
                  (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                    (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n)))) ↦
            @Membership.mem
              (@Units (Matrix (Fin n) (Fin n) Complex)
                (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                  (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
              (@Subgroup
                (@Units (Matrix (Fin n) (Fin n) Complex)
                  (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                    (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
                (@Units.instGroup (Matrix (Fin n) (Fin n) Complex)
                  (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                    (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n)))))
              (@SetLike.instMembership
                (@Subgroup
                  (@Units (Matrix (Fin n) (Fin n) Complex)
                    (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                      (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
                  (@Units.instGroup (Matrix (Fin n) (Fin n) Complex)
                    (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                      (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n)))))
                (@Units (Matrix (Fin n) (Fin n) Complex)
                  (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                    (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
                (@Subgroup.instSetLike
                  (@Units (Matrix (Fin n) (Fin n) Complex)
                    (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                      (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
                  (@Units.instGroup (Matrix (Fin n) (Fin n) Complex)
                    (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                      (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))))
              (@UpperTheory.Reformulated.B.Re4.UJ n ε) x)
          (@Units.instTopologicalSpaceUnits (Matrix (Fin n) (Fin n) Complex)
            (@instTopologicalSpaceMatrix (Fin n) (Fin n) Complex
              (@UniformSpace.toTopologicalSpace Complex
                (@PseudoMetricSpace.toUniformSpace Complex
                  (@SeminormedRing.toPseudoMetricSpace Complex
                    (@SeminormedCommRing.toSeminormedRing Complex
                      (@NormedCommRing.toSeminormedCommRing Complex
                        (@CommCStarAlgebra.toNormedCommRing Complex instCommCStarAlgebraComplex)))))))
            (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
              (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))) := by
  intro n ε
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → ℂ))
  have hv : Continuous (fun g : (Matrix (Fin n) (Fin n) ℂ)ˣ => g.val) := Units.continuous_val
  have hc : IsClosed {g : (Matrix (Fin n) (Fin n) ℂ)ˣ |
      g.val.conjTranspose * UpperTheory.Reformulated.B.Re4.Jm ε * g.val = UpperTheory.Reformulated.B.Re4.Jm ε} :=
    isClosed_eq ((hv.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul hv) continuous_const
  exact hc.locallyCompactSpace
noncomputable def UpperTheory.Reformulated.B.Re4.muG :
    {n : Nat} →
      (ε : Fin n → Bool) → @MeasureTheory.Measure (↥(@UpperTheory.Reformulated.B.Re4.UJ n ε)) (UpperTheory.Reformulated.B.Re4.instMeasurableSpaceUJ n ε) :=
    fun {n : Nat} (ε : Fin n → Bool) ↦
      @MeasureTheory.Measure.haar (↥(@UpperTheory.Reformulated.B.Re4.UJ n ε))
        (@Subgroup.toGroup
          (@Units (Matrix (Fin n) (Fin n) Complex)
            (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
              (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
          (@Units.instGroup (Matrix (Fin n) (Fin n) Complex)
            (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
              (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
          (@UpperTheory.Reformulated.B.Re4.UJ n ε))
        (@instTopologicalSpaceSubtype
          (@Units (Matrix (Fin n) (Fin n) Complex)
            (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
              (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
          (fun
              (x :
                @Units (Matrix (Fin n) (Fin n) Complex)
                  (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                    (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n)))) ↦
            @Membership.mem
              (@Units (Matrix (Fin n) (Fin n) Complex)
                (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                  (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
              (@Subgroup
                (@Units (Matrix (Fin n) (Fin n) Complex)
                  (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                    (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
                (@Units.instGroup (Matrix (Fin n) (Fin n) Complex)
                  (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                    (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n)))))
              (@SetLike.instMembership
                (@Subgroup
                  (@Units (Matrix (Fin n) (Fin n) Complex)
                    (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                      (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
                  (@Units.instGroup (Matrix (Fin n) (Fin n) Complex)
                    (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                      (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n)))))
                (@Units (Matrix (Fin n) (Fin n) Complex)
                  (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                    (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
                (@Subgroup.instSetLike
                  (@Units (Matrix (Fin n) (Fin n) Complex)
                    (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                      (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
                  (@Units.instGroup (Matrix (Fin n) (Fin n) Complex)
                    (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                      (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))))
              (@UpperTheory.Reformulated.B.Re4.UJ n ε) x)
          (@Units.instTopologicalSpaceUnits (Matrix (Fin n) (Fin n) Complex)
            (@instTopologicalSpaceMatrix (Fin n) (Fin n) Complex
              (@UniformSpace.toTopologicalSpace Complex
                (@PseudoMetricSpace.toUniformSpace Complex
                  (@SeminormedRing.toPseudoMetricSpace Complex
                    (@SeminormedCommRing.toSeminormedRing Complex
                      (@NormedCommRing.toSeminormedCommRing Complex
                        (@CommCStarAlgebra.toNormedCommRing Complex instCommCStarAlgebraComplex)))))))
            (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
              (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n)))))
        (@UpperTheory.Reformulated.B.Re4.aux8 n ε) (UpperTheory.Reformulated.B.Re4.instMeasurableSpaceUJ n ε) (UpperTheory.Reformulated.B.Re4.aux9 n ε)
        (UpperTheory.Reformulated.B.Re4.laurent_T_neg_one_mul_T_one n ε)
theorem UpperTheory.Reformulated.B.Re4.algebra_smulCommClass_complex :
    (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).AtLeastTwo := by
  infer_instance
@[reducible] noncomputable def UpperTheory.Reformulated.B.Re4.L2 :
    {n : Nat} → (Fin n → Bool) → Type :=
    fun {n : Nat} (ε : Fin n → Bool) ↦
      ↥(@MeasureTheory.Lp (↥(@UpperTheory.Reformulated.B.Re4.UJ n ε)) Complex (UpperTheory.Reformulated.B.Re4.instMeasurableSpaceUJ n ε)
          Complex.instNormedAddCommGroup
          (@OfNat.ofNat ENNReal (nat_lit 2)
            (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
              (@AddMonoidWithOne.toNatCast ENNReal
                (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
              UpperTheory.Reformulated.B.Re4.algebra_smulCommClass_complex))
          (@UpperTheory.Reformulated.B.Re4.muG n ε))
noncomputable def UpperTheory.Reformulated.B.Re4.d15 :
    {n : Nat} → (Fin n → Bool) → Matrix (Fin n) (Fin n) Complex :=
    fun {n : Nat} (ε : Fin n → Bool) ↦
      @Matrix.diagonal (Fin n) Complex (instDecidableEqFin n) Complex.instZero fun (a : Fin n) ↦
        @ite Complex (@Eq Bool (ε a) Bool.true) (instDecidableEqBool (ε a) Bool.true)
          (@OfNat.ofNat Complex (nat_lit 1) (@One.toOfNat1 Complex Complex.instOne))
          (@Neg.neg Complex Complex.instNeg (@OfNat.ofNat Complex (nat_lit 1) (@One.toOfNat1 Complex Complex.instOne)))
noncomputable def UpperTheory.Reformulated.B.Re4.Kset :
    {n : Nat} → (Fin n → Bool) → Set (Matrix (Fin n) (Fin n) Complex) :=
    fun {n : Nat} (ε : Fin n → Bool) ↦
      @Set.ofPred (Matrix (Fin n) (Fin n) Complex) fun (g : Matrix (Fin n) (Fin n) Complex) ↦
        And
          (@Membership.mem (Matrix (Fin n) (Fin n) Complex)
            (@Submonoid (Matrix (Fin n) (Fin n) Complex)
              (@MulZeroOneClass.toMulOneClass (Matrix (Fin n) (Fin n) Complex)
                (@instMulZeroOneClassOfSemiring (Matrix (Fin n) (Fin n) Complex)
                  (@Matrix.semiring (Fin n) Complex
                    (@CommSemiring.toSemiring Complex (@CommRing.toCommSemiring Complex Complex.commRing)) (Fin.fintype n)
                    (instDecidableEqFin n)))))
            (@SetLike.instMembership
              (@Submonoid (Matrix (Fin n) (Fin n) Complex)
                (@MulZeroOneClass.toMulOneClass (Matrix (Fin n) (Fin n) Complex)
                  (@instMulZeroOneClassOfSemiring (Matrix (Fin n) (Fin n) Complex)
                    (@Matrix.semiring (Fin n) Complex
                      (@CommSemiring.toSemiring Complex (@CommRing.toCommSemiring Complex Complex.commRing)) (Fin.fintype n)
                      (instDecidableEqFin n)))))
              (Matrix (Fin n) (Fin n) Complex)
              (@Submonoid.instSetLike (Matrix (Fin n) (Fin n) Complex)
                (@MulZeroOneClass.toMulOneClass (Matrix (Fin n) (Fin n) Complex)
                  (@instMulZeroOneClassOfSemiring (Matrix (Fin n) (Fin n) Complex)
                    (@Matrix.semiring (Fin n) Complex
                      (@CommSemiring.toSemiring Complex (@CommRing.toCommSemiring Complex Complex.commRing)) (Fin.fintype n)
                      (instDecidableEqFin n))))))
            (@Matrix.unitaryGroup (Fin n) (instDecidableEqFin n) (Fin.fintype n) Complex Complex.commRing
              Complex.instStarRing)
            g)
          (@Eq (Matrix (Fin n) (Fin n) Complex)
            (@HMul.hMul (Matrix (Fin n) (Fin n) Complex) (Matrix (Fin n) (Fin n) Complex) (Matrix (Fin n) (Fin n) Complex)
              (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid (Fin n) (Fin n) (Fin n) Complex (Fin.fintype n) Complex.instMul
                Complex.instAddCommMonoid)
              g (@UpperTheory.Reformulated.B.Re4.d15 n ε))
            (@HMul.hMul (Matrix (Fin n) (Fin n) Complex) (Matrix (Fin n) (Fin n) Complex) (Matrix (Fin n) (Fin n) Complex)
              (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid (Fin n) (Fin n) (Fin n) Complex (Fin.fintype n) Complex.instMul
                Complex.instAddCommMonoid)
              (@UpperTheory.Reformulated.B.Re4.d15 n ε) g))
theorem UpperTheory.Reformulated.B.Re4.complex_normed_instance_compat :
    @IsBoundedSMul Complex Complex
      (@SeminormedRing.toPseudoMetricSpace Complex
        (@SeminormedCommRing.toSeminormedRing Complex
          (@NormedCommRing.toSeminormedCommRing Complex (@NormedField.toNormedCommRing Complex Complex.instNormedField))))
      (@SeminormedAddCommGroup.toPseudoMetricSpace Complex
        (@NonUnitalSeminormedRing.toSeminormedAddCommGroup Complex
          (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing Complex
            (@SeminormedCommRing.toNonUnitalSeminormedCommRing Complex
              (@NormedCommRing.toSeminormedCommRing Complex
                (@CommCStarAlgebra.toNormedCommRing Complex instCommCStarAlgebraComplex))))))
      (@MulZeroClass.toZero Complex
        (@instMulZeroClassOfSemiring Complex
          (@DivisionSemiring.toSemiring Complex
            (@Semifield.toDivisionSemiring Complex
              (@Field.toSemifield Complex (@NormedField.toField Complex Complex.instNormedField))))))
      (@NegZeroClass.toZero Complex
        (@SubNegZeroMonoid.toNegZeroClass Complex
          (@SubtractionMonoid.toSubNegZeroMonoid Complex
            (@SubtractionCommMonoid.toSubtractionMonoid Complex
              (@AddCommGroup.toDivisionAddCommMonoid Complex
                (@SeminormedAddCommGroup.toAddCommGroup Complex
                  (@NonUnitalSeminormedRing.toSeminormedAddCommGroup Complex
                    (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing Complex
                      (@SeminormedCommRing.toNonUnitalSeminormedCommRing Complex
                        (@NormedCommRing.toSeminormedCommRing Complex
                          (@CommCStarAlgebra.toNormedCommRing Complex instCommCStarAlgebraComplex)))))))))))
      (@SMulZeroClass.toSMul Complex Complex
        (@AddZero.toZero Complex
          (@AddZeroClass.toAddZero Complex
            (@AddMonoid.toAddZeroClass Complex
              (@SubNegMonoid.toAddMonoid Complex
                (@AddGroup.toSubNegMonoid Complex
                  (@AddCommGroup.toAddGroup Complex
                    (@SeminormedAddCommGroup.toAddCommGroup Complex
                      (@NonUnitalSeminormedRing.toSeminormedAddCommGroup Complex
                        (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing Complex
                          (@SeminormedCommRing.toNonUnitalSeminormedCommRing Complex
                            (@NormedCommRing.toSeminormedCommRing Complex
                              (@CommCStarAlgebra.toNormedCommRing Complex instCommCStarAlgebraComplex))))))))))))
        (@DistribSMul.toSMulZeroClass Complex Complex
          (@AddMonoid.toAddZeroClass Complex
            (@SubNegMonoid.toAddMonoid Complex
              (@AddGroup.toSubNegMonoid Complex
                (@AddCommGroup.toAddGroup Complex
                  (@SeminormedAddCommGroup.toAddCommGroup Complex
                    (@NonUnitalSeminormedRing.toSeminormedAddCommGroup Complex
                      (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing Complex
                        (@SeminormedCommRing.toNonUnitalSeminormedCommRing Complex
                          (@NormedCommRing.toSeminormedCommRing Complex
                            (@CommCStarAlgebra.toNormedCommRing Complex instCommCStarAlgebraComplex))))))))))
          (@DistribMulAction.toDistribSMul Complex Complex
            (@Semiring.toMonoid Complex
              (@DivisionSemiring.toSemiring Complex
                (@Semifield.toDivisionSemiring Complex
                  (@Field.toSemifield Complex (@NormedField.toField Complex Complex.instNormedField)))))
            (@SubNegMonoid.toAddMonoid Complex
              (@AddGroup.toSubNegMonoid Complex
                (@AddCommGroup.toAddGroup Complex
                  (@SeminormedAddCommGroup.toAddCommGroup Complex
                    (@NonUnitalSeminormedRing.toSeminormedAddCommGroup Complex
                      (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing Complex
                        (@SeminormedCommRing.toNonUnitalSeminormedCommRing Complex
                          (@NormedCommRing.toSeminormedCommRing Complex
                            (@CommCStarAlgebra.toNormedCommRing Complex instCommCStarAlgebraComplex)))))))))
            (@Module.toDistribMulAction Complex Complex
              (@DivisionSemiring.toSemiring Complex
                (@Semifield.toDivisionSemiring Complex
                  (@Field.toSemifield Complex (@NormedField.toField Complex Complex.instNormedField))))
              (@AddCommGroup.toAddCommMonoid Complex
                (@SeminormedAddCommGroup.toAddCommGroup Complex
                  (@NonUnitalSeminormedRing.toSeminormedAddCommGroup Complex
                    (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing Complex
                      (@SeminormedCommRing.toNonUnitalSeminormedCommRing Complex
                        (@NormedCommRing.toSeminormedCommRing Complex
                          (@CommCStarAlgebra.toNormedCommRing Complex instCommCStarAlgebraComplex)))))))
              (@NormedSpace.toModule Complex Complex Complex.instNormedField
                (@NonUnitalSeminormedRing.toSeminormedAddCommGroup Complex
                  (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing Complex
                    (@SeminormedCommRing.toNonUnitalSeminormedCommRing Complex
                      (@NormedCommRing.toSeminormedCommRing Complex
                        (@CommCStarAlgebra.toNormedCommRing Complex instCommCStarAlgebraComplex)))))
                (@NonUnitalCStarAlgebra.toNormedSpace Complex
                  (@NonUnitalCommCStarAlgebra.toNonUnitalCStarAlgebra Complex
                    (@CommCStarAlgebra.toNonUnitalCommCStarAlgebra Complex instCommCStarAlgebraComplex)))))))) := by
  infer_instance
@[reducible] noncomputable def UpperTheory.Reformulated.B.Re4.umat :
    {n : Nat} → {ε : Fin n → Bool} → ↥(@UpperTheory.Reformulated.B.Re4.UJ n ε) → Matrix (Fin n) (Fin n) Complex :=
    fun {n : Nat} {ε : Fin n → Bool} (g : ↥(@UpperTheory.Reformulated.B.Re4.UJ n ε)) ↦
      @Units.val (Matrix (Fin n) (Fin n) Complex)
        (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
          (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n)))
        (@Subtype.val
          (@Units (Matrix (Fin n) (Fin n) Complex)
            (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
              (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
          (fun
              (x :
                @Units (Matrix (Fin n) (Fin n) Complex)
                  (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                    (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n)))) ↦
            @Membership.mem
              (@Units (Matrix (Fin n) (Fin n) Complex)
                (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                  (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
              (@Subgroup
                (@Units (Matrix (Fin n) (Fin n) Complex)
                  (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                    (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
                (@Units.instGroup (Matrix (Fin n) (Fin n) Complex)
                  (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                    (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n)))))
              (@SetLike.instMembership
                (@Subgroup
                  (@Units (Matrix (Fin n) (Fin n) Complex)
                    (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                      (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
                  (@Units.instGroup (Matrix (Fin n) (Fin n) Complex)
                    (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                      (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n)))))
                (@Units (Matrix (Fin n) (Fin n) Complex)
                  (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                    (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
                (@Subgroup.instSetLike
                  (@Units (Matrix (Fin n) (Fin n) Complex)
                    (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                      (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
                  (@Units.instGroup (Matrix (Fin n) (Fin n) Complex)
                    (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                      (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))))
              (@UpperTheory.Reformulated.B.Re4.UJ n ε) x)
          g)
noncomputable def UpperTheory.Reformulated.B.Re4.rregG :
    {n : Nat} →
      (ε : Fin n → Bool) →
        ↥(@UpperTheory.Reformulated.B.Re4.UJ n ε) →
          @ContinuousLinearMap Complex Complex Complex.instSemiring Complex.instSemiring
            (@RingHom.id Complex (@Semiring.toNonAssocSemiring Complex Complex.instSemiring)) (@UpperTheory.Reformulated.B.Re4.L2 n ε)
            (@UniformSpace.toTopologicalSpace (@UpperTheory.Reformulated.B.Re4.L2 n ε)
              (@PseudoMetricSpace.toUniformSpace (@UpperTheory.Reformulated.B.Re4.L2 n ε)
                (@SeminormedAddCommGroup.toPseudoMetricSpace (@UpperTheory.Reformulated.B.Re4.L2 n ε)
                  (@NormedAddCommGroup.toSeminormedAddCommGroup (@UpperTheory.Reformulated.B.Re4.L2 n ε)
                    (@MeasureTheory.Lp.instNormedAddCommGroup (↥(@UpperTheory.Reformulated.B.Re4.UJ n ε)) Complex
                      (UpperTheory.Reformulated.B.Re4.instMeasurableSpaceUJ n ε)
                      (@OfNat.ofNat ENNReal (nat_lit 2)
                        (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                          (@AddMonoidWithOne.toNatCast ENNReal
                            (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                          UpperTheory.Reformulated.B.Re4.algebra_smulCommClass_complex))
                      (@UpperTheory.Reformulated.B.Re4.muG n ε) Complex.instNormedAddCommGroup fact_one_le_two_ennreal)))))
            (@AddCommGroup.toAddCommMonoid (@UpperTheory.Reformulated.B.Re4.L2 n ε)
              (@MeasureTheory.Lp.instAddCommGroup (↥(@UpperTheory.Reformulated.B.Re4.UJ n ε)) Complex
                (UpperTheory.Reformulated.B.Re4.instMeasurableSpaceUJ n ε)
                (@OfNat.ofNat ENNReal (nat_lit 2)
                  (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                    (@AddMonoidWithOne.toNatCast ENNReal
                      (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                    UpperTheory.Reformulated.B.Re4.algebra_smulCommClass_complex))
                (@UpperTheory.Reformulated.B.Re4.muG n ε) Complex.instNormedAddCommGroup))
            (@UpperTheory.Reformulated.B.Re4.L2 n ε)
            (@UniformSpace.toTopologicalSpace (@UpperTheory.Reformulated.B.Re4.L2 n ε)
              (@PseudoMetricSpace.toUniformSpace (@UpperTheory.Reformulated.B.Re4.L2 n ε)
                (@SeminormedAddCommGroup.toPseudoMetricSpace (@UpperTheory.Reformulated.B.Re4.L2 n ε)
                  (@NormedAddCommGroup.toSeminormedAddCommGroup (@UpperTheory.Reformulated.B.Re4.L2 n ε)
                    (@MeasureTheory.Lp.instNormedAddCommGroup (↥(@UpperTheory.Reformulated.B.Re4.UJ n ε)) Complex
                      (UpperTheory.Reformulated.B.Re4.instMeasurableSpaceUJ n ε)
                      (@OfNat.ofNat ENNReal (nat_lit 2)
                        (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                          (@AddMonoidWithOne.toNatCast ENNReal
                            (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                          UpperTheory.Reformulated.B.Re4.algebra_smulCommClass_complex))
                      (@UpperTheory.Reformulated.B.Re4.muG n ε) Complex.instNormedAddCommGroup fact_one_le_two_ennreal)))))
            (@AddCommGroup.toAddCommMonoid (@UpperTheory.Reformulated.B.Re4.L2 n ε)
              (@MeasureTheory.Lp.instAddCommGroup (↥(@UpperTheory.Reformulated.B.Re4.UJ n ε)) Complex
                (UpperTheory.Reformulated.B.Re4.instMeasurableSpaceUJ n ε)
                (@OfNat.ofNat ENNReal (nat_lit 2)
                  (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                    (@AddMonoidWithOne.toNatCast ENNReal
                      (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                    UpperTheory.Reformulated.B.Re4.algebra_smulCommClass_complex))
                (@UpperTheory.Reformulated.B.Re4.muG n ε) Complex.instNormedAddCommGroup))
            (@MeasureTheory.Lp.instModule (↥(@UpperTheory.Reformulated.B.Re4.UJ n ε)) Complex Complex
              (UpperTheory.Reformulated.B.Re4.instMeasurableSpaceUJ n ε)
              (@OfNat.ofNat ENNReal (nat_lit 2)
                (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                  (@AddMonoidWithOne.toNatCast ENNReal
                    (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                  UpperTheory.Reformulated.B.Re4.algebra_smulCommClass_complex))
              (@UpperTheory.Reformulated.B.Re4.muG n ε) Complex.instNormedAddCommGroup
              (@CStarAlgebra.toNormedRing Complex (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex))
              (@Semiring.toModule Complex
                (@Ring.toSemiring Complex
                  (@NormedRing.toRing Complex
                    (@CStarAlgebra.toNormedRing Complex
                      (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex)))))
              (@NormedSpace.toIsBoundedSMul Complex Complex Complex.instNormedField
                (@NonUnitalSeminormedRing.toSeminormedAddCommGroup Complex
                  (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing Complex
                    (@SeminormedCommRing.toNonUnitalSeminormedCommRing Complex
                      (@NormedCommRing.toSeminormedCommRing Complex
                        (@CommCStarAlgebra.toNormedCommRing Complex instCommCStarAlgebraComplex)))))
                (@NonUnitalCStarAlgebra.toNormedSpace Complex
                  (@NonUnitalCommCStarAlgebra.toNonUnitalCStarAlgebra Complex
                    (@CommCStarAlgebra.toNonUnitalCommCStarAlgebra Complex instCommCStarAlgebraComplex)))))
            (@MeasureTheory.Lp.instModule (↥(@UpperTheory.Reformulated.B.Re4.UJ n ε)) Complex Complex
              (UpperTheory.Reformulated.B.Re4.instMeasurableSpaceUJ n ε)
              (@OfNat.ofNat ENNReal (nat_lit 2)
                (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                  (@AddMonoidWithOne.toNatCast ENNReal
                    (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                  UpperTheory.Reformulated.B.Re4.algebra_smulCommClass_complex))
              (@UpperTheory.Reformulated.B.Re4.muG n ε) Complex.instNormedAddCommGroup
              (@CStarAlgebra.toNormedRing Complex (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex))
              (@Semiring.toModule Complex
                (@Ring.toSemiring Complex
                  (@NormedRing.toRing Complex
                    (@CStarAlgebra.toNormedRing Complex
                      (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex)))))
              (@NormedSpace.toIsBoundedSMul Complex Complex Complex.instNormedField
                (@NonUnitalSeminormedRing.toSeminormedAddCommGroup Complex
                  (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing Complex
                    (@SeminormedCommRing.toNonUnitalSeminormedCommRing Complex
                      (@NormedCommRing.toSeminormedCommRing Complex
                        (@CommCStarAlgebra.toNormedCommRing Complex instCommCStarAlgebraComplex)))))
                (@NonUnitalCStarAlgebra.toNormedSpace Complex
                  (@NonUnitalCommCStarAlgebra.toNonUnitalCStarAlgebra Complex
                    (@CommCStarAlgebra.toNonUnitalCommCStarAlgebra Complex instCommCStarAlgebraComplex))))) :=
    fun {n : Nat} (ε : Fin n → Bool) (y : ↥(@UpperTheory.Reformulated.B.Re4.UJ n ε)) ↦
      @dite
        (@ContinuousLinearMap Complex Complex Complex.instSemiring Complex.instSemiring
          (@RingHom.id Complex (@Semiring.toNonAssocSemiring Complex Complex.instSemiring)) (@UpperTheory.Reformulated.B.Re4.L2 n ε)
          (@UniformSpace.toTopologicalSpace (@UpperTheory.Reformulated.B.Re4.L2 n ε)
            (@PseudoMetricSpace.toUniformSpace (@UpperTheory.Reformulated.B.Re4.L2 n ε)
              (@SeminormedAddCommGroup.toPseudoMetricSpace (@UpperTheory.Reformulated.B.Re4.L2 n ε)
                (@NormedAddCommGroup.toSeminormedAddCommGroup (@UpperTheory.Reformulated.B.Re4.L2 n ε)
                  (@MeasureTheory.Lp.instNormedAddCommGroup (↥(@UpperTheory.Reformulated.B.Re4.UJ n ε)) Complex
                    (UpperTheory.Reformulated.B.Re4.instMeasurableSpaceUJ n ε)
                    (@OfNat.ofNat ENNReal (nat_lit 2)
                      (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                        (@AddMonoidWithOne.toNatCast ENNReal
                          (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                        UpperTheory.Reformulated.B.Re4.algebra_smulCommClass_complex))
                    (@UpperTheory.Reformulated.B.Re4.muG n ε) Complex.instNormedAddCommGroup fact_one_le_two_ennreal)))))
          (@AddCommGroup.toAddCommMonoid (@UpperTheory.Reformulated.B.Re4.L2 n ε)
            (@MeasureTheory.Lp.instAddCommGroup (↥(@UpperTheory.Reformulated.B.Re4.UJ n ε)) Complex
              (UpperTheory.Reformulated.B.Re4.instMeasurableSpaceUJ n ε)
              (@OfNat.ofNat ENNReal (nat_lit 2)
                (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                  (@AddMonoidWithOne.toNatCast ENNReal
                    (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                  UpperTheory.Reformulated.B.Re4.algebra_smulCommClass_complex))
              (@UpperTheory.Reformulated.B.Re4.muG n ε) Complex.instNormedAddCommGroup))
          (@UpperTheory.Reformulated.B.Re4.L2 n ε)
          (@UniformSpace.toTopologicalSpace (@UpperTheory.Reformulated.B.Re4.L2 n ε)
            (@PseudoMetricSpace.toUniformSpace (@UpperTheory.Reformulated.B.Re4.L2 n ε)
              (@SeminormedAddCommGroup.toPseudoMetricSpace (@UpperTheory.Reformulated.B.Re4.L2 n ε)
                (@NormedAddCommGroup.toSeminormedAddCommGroup (@UpperTheory.Reformulated.B.Re4.L2 n ε)
                  (@MeasureTheory.Lp.instNormedAddCommGroup (↥(@UpperTheory.Reformulated.B.Re4.UJ n ε)) Complex
                    (UpperTheory.Reformulated.B.Re4.instMeasurableSpaceUJ n ε)
                    (@OfNat.ofNat ENNReal (nat_lit 2)
                      (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                        (@AddMonoidWithOne.toNatCast ENNReal
                          (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                        UpperTheory.Reformulated.B.Re4.algebra_smulCommClass_complex))
                    (@UpperTheory.Reformulated.B.Re4.muG n ε) Complex.instNormedAddCommGroup fact_one_le_two_ennreal)))))
          (@AddCommGroup.toAddCommMonoid (@UpperTheory.Reformulated.B.Re4.L2 n ε)
            (@MeasureTheory.Lp.instAddCommGroup (↥(@UpperTheory.Reformulated.B.Re4.UJ n ε)) Complex
              (UpperTheory.Reformulated.B.Re4.instMeasurableSpaceUJ n ε)
              (@OfNat.ofNat ENNReal (nat_lit 2)
                (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                  (@AddMonoidWithOne.toNatCast ENNReal
                    (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                  UpperTheory.Reformulated.B.Re4.algebra_smulCommClass_complex))
              (@UpperTheory.Reformulated.B.Re4.muG n ε) Complex.instNormedAddCommGroup))
          (@MeasureTheory.Lp.instModule (↥(@UpperTheory.Reformulated.B.Re4.UJ n ε)) Complex Complex
            (UpperTheory.Reformulated.B.Re4.instMeasurableSpaceUJ n ε)
            (@OfNat.ofNat ENNReal (nat_lit 2)
              (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                (@AddMonoidWithOne.toNatCast ENNReal
                  (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                UpperTheory.Reformulated.B.Re4.algebra_smulCommClass_complex))
            (@UpperTheory.Reformulated.B.Re4.muG n ε) Complex.instNormedAddCommGroup
            (@CStarAlgebra.toNormedRing Complex (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex))
            (@Semiring.toModule Complex
              (@Ring.toSemiring Complex
                (@NormedRing.toRing Complex
                  (@CStarAlgebra.toNormedRing Complex
                    (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex)))))
            UpperTheory.Reformulated.B.Re4.complex_normed_instance_compat)
          (@MeasureTheory.Lp.instModule (↥(@UpperTheory.Reformulated.B.Re4.UJ n ε)) Complex Complex
            (UpperTheory.Reformulated.B.Re4.instMeasurableSpaceUJ n ε)
            (@OfNat.ofNat ENNReal (nat_lit 2)
              (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                (@AddMonoidWithOne.toNatCast ENNReal
                  (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                UpperTheory.Reformulated.B.Re4.algebra_smulCommClass_complex))
            (@UpperTheory.Reformulated.B.Re4.muG n ε) Complex.instNormedAddCommGroup
            (@CStarAlgebra.toNormedRing Complex (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex))
            (@Semiring.toModule Complex
              (@Ring.toSemiring Complex
                (@NormedRing.toRing Complex
                  (@CStarAlgebra.toNormedRing Complex
                    (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex)))))
            UpperTheory.Reformulated.B.Re4.complex_normed_instance_compat))
        (@MeasureTheory.MeasurePreserving (↥(@UpperTheory.Reformulated.B.Re4.UJ n ε)) (↥(@UpperTheory.Reformulated.B.Re4.UJ n ε))
          (UpperTheory.Reformulated.B.Re4.instMeasurableSpaceUJ n ε) (UpperTheory.Reformulated.B.Re4.instMeasurableSpaceUJ n ε)
          (fun (x : ↥(@UpperTheory.Reformulated.B.Re4.UJ n ε)) ↦
            @HMul.hMul (↥(@UpperTheory.Reformulated.B.Re4.UJ n ε)) (↥(@UpperTheory.Reformulated.B.Re4.UJ n ε)) (↥(@UpperTheory.Reformulated.B.Re4.UJ n ε))
              (@instHMul (↥(@UpperTheory.Reformulated.B.Re4.UJ n ε))
                (@Subgroup.mul
                  (@Units (Matrix (Fin n) (Fin n) Complex)
                    (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                      (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
                  (@Units.instGroup (Matrix (Fin n) (Fin n) Complex)
                    (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                      (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
                  (@UpperTheory.Reformulated.B.Re4.UJ n ε)))
              x y)
          (@UpperTheory.Reformulated.B.Re4.muG n ε) (@UpperTheory.Reformulated.B.Re4.muG n ε))
        (Classical.propDecidable
          (@MeasureTheory.MeasurePreserving (↥(@UpperTheory.Reformulated.B.Re4.UJ n ε)) (↥(@UpperTheory.Reformulated.B.Re4.UJ n ε))
            (UpperTheory.Reformulated.B.Re4.instMeasurableSpaceUJ n ε) (UpperTheory.Reformulated.B.Re4.instMeasurableSpaceUJ n ε)
            (fun (x : ↥(@UpperTheory.Reformulated.B.Re4.UJ n ε)) ↦
              @HMul.hMul (↥(@UpperTheory.Reformulated.B.Re4.UJ n ε)) (↥(@UpperTheory.Reformulated.B.Re4.UJ n ε)) (↥(@UpperTheory.Reformulated.B.Re4.UJ n ε))
                (@instHMul (↥(@UpperTheory.Reformulated.B.Re4.UJ n ε))
                  (@Subgroup.mul
                    (@Units (Matrix (Fin n) (Fin n) Complex)
                      (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                        (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
                    (@Units.instGroup (Matrix (Fin n) (Fin n) Complex)
                      (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                        (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
                    (@UpperTheory.Reformulated.B.Re4.UJ n ε)))
                x y)
            (@UpperTheory.Reformulated.B.Re4.muG n ε) (@UpperTheory.Reformulated.B.Re4.muG n ε)))
        (fun
            (hm :
              @MeasureTheory.MeasurePreserving (↥(@UpperTheory.Reformulated.B.Re4.UJ n ε)) (↥(@UpperTheory.Reformulated.B.Re4.UJ n ε))
                (UpperTheory.Reformulated.B.Re4.instMeasurableSpaceUJ n ε) (UpperTheory.Reformulated.B.Re4.instMeasurableSpaceUJ n ε)
                (fun (x : ↥(@UpperTheory.Reformulated.B.Re4.UJ n ε)) ↦
                  @HMul.hMul (↥(@UpperTheory.Reformulated.B.Re4.UJ n ε)) (↥(@UpperTheory.Reformulated.B.Re4.UJ n ε)) (↥(@UpperTheory.Reformulated.B.Re4.UJ n ε))
                    (@instHMul (↥(@UpperTheory.Reformulated.B.Re4.UJ n ε))
                      (@Subgroup.mul
                        (@Units (Matrix (Fin n) (Fin n) Complex)
                          (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                            (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
                        (@Units.instGroup (Matrix (Fin n) (Fin n) Complex)
                          (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                            (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
                        (@UpperTheory.Reformulated.B.Re4.UJ n ε)))
                    x y)
                (@UpperTheory.Reformulated.B.Re4.muG n ε) (@UpperTheory.Reformulated.B.Re4.muG n ε)) ↦
          @LinearIsometry.toContinuousLinearMap Complex Complex
            (↥(@MeasureTheory.Lp (↥(@UpperTheory.Reformulated.B.Re4.UJ n ε)) Complex (UpperTheory.Reformulated.B.Re4.instMeasurableSpaceUJ n ε)
                Complex.instNormedAddCommGroup
                (@OfNat.ofNat ENNReal (nat_lit 2)
                  (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                    (@AddMonoidWithOne.toNatCast ENNReal
                      (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                    UpperTheory.Reformulated.B.Re4.algebra_smulCommClass_complex))
                (@UpperTheory.Reformulated.B.Re4.muG n ε)))
            (↥(@MeasureTheory.Lp (↥(@UpperTheory.Reformulated.B.Re4.UJ n ε)) Complex (UpperTheory.Reformulated.B.Re4.instMeasurableSpaceUJ n ε)
                Complex.instNormedAddCommGroup
                (@OfNat.ofNat ENNReal (nat_lit 2)
                  (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                    (@AddMonoidWithOne.toNatCast ENNReal
                      (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                    UpperTheory.Reformulated.B.Re4.algebra_smulCommClass_complex))
                (@UpperTheory.Reformulated.B.Re4.muG n ε)))
            (@Ring.toSemiring Complex
              (@NormedRing.toRing Complex
                (@CStarAlgebra.toNormedRing Complex
                  (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex))))
            (@Ring.toSemiring Complex
              (@NormedRing.toRing Complex
                (@CStarAlgebra.toNormedRing Complex
                  (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex))))
            (@RingHom.id Complex
              (@Semiring.toNonAssocSemiring Complex
                (@Ring.toSemiring Complex
                  (@NormedRing.toRing Complex
                    (@CStarAlgebra.toNormedRing Complex
                      (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex))))))
            (@NormedAddCommGroup.toSeminormedAddCommGroup
              (↥(@MeasureTheory.Lp (↥(@UpperTheory.Reformulated.B.Re4.UJ n ε)) Complex (UpperTheory.Reformulated.B.Re4.instMeasurableSpaceUJ n ε)
                  Complex.instNormedAddCommGroup
                  (@OfNat.ofNat ENNReal (nat_lit 2)
                    (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                      (@AddMonoidWithOne.toNatCast ENNReal
                        (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                      UpperTheory.Reformulated.B.Re4.algebra_smulCommClass_complex))
                  (@UpperTheory.Reformulated.B.Re4.muG n ε)))
              (@MeasureTheory.Lp.instNormedAddCommGroup (↥(@UpperTheory.Reformulated.B.Re4.UJ n ε)) Complex
                (UpperTheory.Reformulated.B.Re4.instMeasurableSpaceUJ n ε)
                (@OfNat.ofNat ENNReal (nat_lit 2)
                  (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                    (@AddMonoidWithOne.toNatCast ENNReal
                      (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                    UpperTheory.Reformulated.B.Re4.algebra_smulCommClass_complex))
                (@UpperTheory.Reformulated.B.Re4.muG n ε) Complex.instNormedAddCommGroup fact_one_le_two_ennreal))
            (@NormedAddCommGroup.toSeminormedAddCommGroup
              (↥(@MeasureTheory.Lp (↥(@UpperTheory.Reformulated.B.Re4.UJ n ε)) Complex (UpperTheory.Reformulated.B.Re4.instMeasurableSpaceUJ n ε)
                  Complex.instNormedAddCommGroup
                  (@OfNat.ofNat ENNReal (nat_lit 2)
                    (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                      (@AddMonoidWithOne.toNatCast ENNReal
                        (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                      UpperTheory.Reformulated.B.Re4.algebra_smulCommClass_complex))
                  (@UpperTheory.Reformulated.B.Re4.muG n ε)))
              (@MeasureTheory.Lp.instNormedAddCommGroup (↥(@UpperTheory.Reformulated.B.Re4.UJ n ε)) Complex
                (UpperTheory.Reformulated.B.Re4.instMeasurableSpaceUJ n ε)
                (@OfNat.ofNat ENNReal (nat_lit 2)
                  (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                    (@AddMonoidWithOne.toNatCast ENNReal
                      (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                    UpperTheory.Reformulated.B.Re4.algebra_smulCommClass_complex))
                (@UpperTheory.Reformulated.B.Re4.muG n ε) Complex.instNormedAddCommGroup fact_one_le_two_ennreal))
            (@MeasureTheory.Lp.instModule (↥(@UpperTheory.Reformulated.B.Re4.UJ n ε)) Complex Complex
              (UpperTheory.Reformulated.B.Re4.instMeasurableSpaceUJ n ε)
              (@OfNat.ofNat ENNReal (nat_lit 2)
                (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                  (@AddMonoidWithOne.toNatCast ENNReal
                    (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                  UpperTheory.Reformulated.B.Re4.algebra_smulCommClass_complex))
              (@UpperTheory.Reformulated.B.Re4.muG n ε) Complex.instNormedAddCommGroup
              (@CStarAlgebra.toNormedRing Complex (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex))
              (@Semiring.toModule Complex
                (@Ring.toSemiring Complex
                  (@NormedRing.toRing Complex
                    (@CStarAlgebra.toNormedRing Complex
                      (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex)))))
              UpperTheory.Reformulated.B.Re4.complex_normed_instance_compat)
            (@MeasureTheory.Lp.instModule (↥(@UpperTheory.Reformulated.B.Re4.UJ n ε)) Complex Complex
              (UpperTheory.Reformulated.B.Re4.instMeasurableSpaceUJ n ε)
              (@OfNat.ofNat ENNReal (nat_lit 2)
                (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                  (@AddMonoidWithOne.toNatCast ENNReal
                    (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                  UpperTheory.Reformulated.B.Re4.algebra_smulCommClass_complex))
              (@UpperTheory.Reformulated.B.Re4.muG n ε) Complex.instNormedAddCommGroup
              (@CStarAlgebra.toNormedRing Complex (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex))
              (@Semiring.toModule Complex
                (@Ring.toSemiring Complex
                  (@NormedRing.toRing Complex
                    (@CStarAlgebra.toNormedRing Complex
                      (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex)))))
              UpperTheory.Reformulated.B.Re4.complex_normed_instance_compat)
            (@MeasureTheory.Lp.compMeasurePreservingₗᵢ (↥(@UpperTheory.Reformulated.B.Re4.UJ n ε)) Complex
              (UpperTheory.Reformulated.B.Re4.instMeasurableSpaceUJ n ε)
              (@OfNat.ofNat ENNReal (nat_lit 2)
                (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                  (@AddMonoidWithOne.toNatCast ENNReal
                    (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                  UpperTheory.Reformulated.B.Re4.algebra_smulCommClass_complex))
              (@UpperTheory.Reformulated.B.Re4.muG n ε) Complex.instNormedAddCommGroup (↥(@UpperTheory.Reformulated.B.Re4.UJ n ε))
              (UpperTheory.Reformulated.B.Re4.instMeasurableSpaceUJ n ε) (@UpperTheory.Reformulated.B.Re4.muG n ε) Complex
              (@CStarAlgebra.toNormedRing Complex (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex))
              (@Semiring.toModule Complex
                (@Ring.toSemiring Complex
                  (@NormedRing.toRing Complex
                    (@CStarAlgebra.toNormedRing Complex
                      (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex)))))
              UpperTheory.Reformulated.B.Re4.complex_normed_instance_compat fact_one_le_two_ennreal
              (fun (x : ↥(@UpperTheory.Reformulated.B.Re4.UJ n ε)) ↦
                @HMul.hMul (↥(@UpperTheory.Reformulated.B.Re4.UJ n ε)) (↥(@UpperTheory.Reformulated.B.Re4.UJ n ε)) (↥(@UpperTheory.Reformulated.B.Re4.UJ n ε))
                  (@instHMul (↥(@UpperTheory.Reformulated.B.Re4.UJ n ε))
                    (@Subgroup.mul
                      (@Units (Matrix (Fin n) (Fin n) Complex)
                        (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                          (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
                      (@Units.instGroup (Matrix (Fin n) (Fin n) Complex)
                        (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                          (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
                      (@UpperTheory.Reformulated.B.Re4.UJ n ε)))
                  x y)
              hm))
        fun
          (hm :
            Not
              (@MeasureTheory.MeasurePreserving (↥(@UpperTheory.Reformulated.B.Re4.UJ n ε)) (↥(@UpperTheory.Reformulated.B.Re4.UJ n ε))
                (UpperTheory.Reformulated.B.Re4.instMeasurableSpaceUJ n ε) (UpperTheory.Reformulated.B.Re4.instMeasurableSpaceUJ n ε)
                (fun (x : ↥(@UpperTheory.Reformulated.B.Re4.UJ n ε)) ↦
                  @HMul.hMul (↥(@UpperTheory.Reformulated.B.Re4.UJ n ε)) (↥(@UpperTheory.Reformulated.B.Re4.UJ n ε)) (↥(@UpperTheory.Reformulated.B.Re4.UJ n ε))
                    (@instHMul (↥(@UpperTheory.Reformulated.B.Re4.UJ n ε))
                      (@Subgroup.mul
                        (@Units (Matrix (Fin n) (Fin n) Complex)
                          (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                            (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
                        (@Units.instGroup (Matrix (Fin n) (Fin n) Complex)
                          (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                            (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
                        (@UpperTheory.Reformulated.B.Re4.UJ n ε)))
                    x y)
                (@UpperTheory.Reformulated.B.Re4.muG n ε) (@UpperTheory.Reformulated.B.Re4.muG n ε))) ↦
        @OfNat.ofNat
          (@ContinuousLinearMap Complex Complex Complex.instSemiring Complex.instSemiring
            (@RingHom.id Complex (@Semiring.toNonAssocSemiring Complex Complex.instSemiring)) (@UpperTheory.Reformulated.B.Re4.L2 n ε)
            (@UniformSpace.toTopologicalSpace (@UpperTheory.Reformulated.B.Re4.L2 n ε)
              (@PseudoMetricSpace.toUniformSpace (@UpperTheory.Reformulated.B.Re4.L2 n ε)
                (@SeminormedAddCommGroup.toPseudoMetricSpace (@UpperTheory.Reformulated.B.Re4.L2 n ε)
                  (@NormedAddCommGroup.toSeminormedAddCommGroup (@UpperTheory.Reformulated.B.Re4.L2 n ε)
                    (@MeasureTheory.Lp.instNormedAddCommGroup (↥(@UpperTheory.Reformulated.B.Re4.UJ n ε)) Complex
                      (UpperTheory.Reformulated.B.Re4.instMeasurableSpaceUJ n ε)
                      (@OfNat.ofNat ENNReal (nat_lit 2)
                        (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                          (@AddMonoidWithOne.toNatCast ENNReal
                            (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                          UpperTheory.Reformulated.B.Re4.algebra_smulCommClass_complex))
                      (@UpperTheory.Reformulated.B.Re4.muG n ε) Complex.instNormedAddCommGroup fact_one_le_two_ennreal)))))
            (@AddCommGroup.toAddCommMonoid (@UpperTheory.Reformulated.B.Re4.L2 n ε)
              (@MeasureTheory.Lp.instAddCommGroup (↥(@UpperTheory.Reformulated.B.Re4.UJ n ε)) Complex
                (UpperTheory.Reformulated.B.Re4.instMeasurableSpaceUJ n ε)
                (@OfNat.ofNat ENNReal (nat_lit 2)
                  (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                    (@AddMonoidWithOne.toNatCast ENNReal
                      (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                    UpperTheory.Reformulated.B.Re4.algebra_smulCommClass_complex))
                (@UpperTheory.Reformulated.B.Re4.muG n ε) Complex.instNormedAddCommGroup))
            (@UpperTheory.Reformulated.B.Re4.L2 n ε)
            (@UniformSpace.toTopologicalSpace (@UpperTheory.Reformulated.B.Re4.L2 n ε)
              (@PseudoMetricSpace.toUniformSpace (@UpperTheory.Reformulated.B.Re4.L2 n ε)
                (@SeminormedAddCommGroup.toPseudoMetricSpace (@UpperTheory.Reformulated.B.Re4.L2 n ε)
                  (@NormedAddCommGroup.toSeminormedAddCommGroup (@UpperTheory.Reformulated.B.Re4.L2 n ε)
                    (@MeasureTheory.Lp.instNormedAddCommGroup (↥(@UpperTheory.Reformulated.B.Re4.UJ n ε)) Complex
                      (UpperTheory.Reformulated.B.Re4.instMeasurableSpaceUJ n ε)
                      (@OfNat.ofNat ENNReal (nat_lit 2)
                        (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                          (@AddMonoidWithOne.toNatCast ENNReal
                            (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                          UpperTheory.Reformulated.B.Re4.algebra_smulCommClass_complex))
                      (@UpperTheory.Reformulated.B.Re4.muG n ε) Complex.instNormedAddCommGroup fact_one_le_two_ennreal)))))
            (@AddCommGroup.toAddCommMonoid (@UpperTheory.Reformulated.B.Re4.L2 n ε)
              (@MeasureTheory.Lp.instAddCommGroup (↥(@UpperTheory.Reformulated.B.Re4.UJ n ε)) Complex
                (UpperTheory.Reformulated.B.Re4.instMeasurableSpaceUJ n ε)
                (@OfNat.ofNat ENNReal (nat_lit 2)
                  (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                    (@AddMonoidWithOne.toNatCast ENNReal
                      (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                    UpperTheory.Reformulated.B.Re4.algebra_smulCommClass_complex))
                (@UpperTheory.Reformulated.B.Re4.muG n ε) Complex.instNormedAddCommGroup))
            (@MeasureTheory.Lp.instModule (↥(@UpperTheory.Reformulated.B.Re4.UJ n ε)) Complex Complex
              (UpperTheory.Reformulated.B.Re4.instMeasurableSpaceUJ n ε)
              (@OfNat.ofNat ENNReal (nat_lit 2)
                (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                  (@AddMonoidWithOne.toNatCast ENNReal
                    (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                  UpperTheory.Reformulated.B.Re4.algebra_smulCommClass_complex))
              (@UpperTheory.Reformulated.B.Re4.muG n ε) Complex.instNormedAddCommGroup
              (@CStarAlgebra.toNormedRing Complex (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex))
              (@Semiring.toModule Complex
                (@Ring.toSemiring Complex
                  (@NormedRing.toRing Complex
                    (@CStarAlgebra.toNormedRing Complex
                      (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex)))))
              UpperTheory.Reformulated.B.Re4.complex_normed_instance_compat)
            (@MeasureTheory.Lp.instModule (↥(@UpperTheory.Reformulated.B.Re4.UJ n ε)) Complex Complex
              (UpperTheory.Reformulated.B.Re4.instMeasurableSpaceUJ n ε)
              (@OfNat.ofNat ENNReal (nat_lit 2)
                (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                  (@AddMonoidWithOne.toNatCast ENNReal
                    (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                  UpperTheory.Reformulated.B.Re4.algebra_smulCommClass_complex))
              (@UpperTheory.Reformulated.B.Re4.muG n ε) Complex.instNormedAddCommGroup
              (@CStarAlgebra.toNormedRing Complex (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex))
              (@Semiring.toModule Complex
                (@Ring.toSemiring Complex
                  (@NormedRing.toRing Complex
                    (@CStarAlgebra.toNormedRing Complex
                      (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex)))))
              UpperTheory.Reformulated.B.Re4.complex_normed_instance_compat))
          (nat_lit 1)
          (@One.toOfNat1
            (@ContinuousLinearMap Complex Complex Complex.instSemiring Complex.instSemiring
              (@RingHom.id Complex (@Semiring.toNonAssocSemiring Complex Complex.instSemiring)) (@UpperTheory.Reformulated.B.Re4.L2 n ε)
              (@UniformSpace.toTopologicalSpace (@UpperTheory.Reformulated.B.Re4.L2 n ε)
                (@PseudoMetricSpace.toUniformSpace (@UpperTheory.Reformulated.B.Re4.L2 n ε)
                  (@SeminormedAddCommGroup.toPseudoMetricSpace (@UpperTheory.Reformulated.B.Re4.L2 n ε)
                    (@NormedAddCommGroup.toSeminormedAddCommGroup (@UpperTheory.Reformulated.B.Re4.L2 n ε)
                      (@MeasureTheory.Lp.instNormedAddCommGroup (↥(@UpperTheory.Reformulated.B.Re4.UJ n ε)) Complex
                        (UpperTheory.Reformulated.B.Re4.instMeasurableSpaceUJ n ε)
                        (@OfNat.ofNat ENNReal (nat_lit 2)
                          (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                            (@AddMonoidWithOne.toNatCast ENNReal
                              (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                            UpperTheory.Reformulated.B.Re4.algebra_smulCommClass_complex))
                        (@UpperTheory.Reformulated.B.Re4.muG n ε) Complex.instNormedAddCommGroup fact_one_le_two_ennreal)))))
              (@AddCommGroup.toAddCommMonoid (@UpperTheory.Reformulated.B.Re4.L2 n ε)
                (@MeasureTheory.Lp.instAddCommGroup (↥(@UpperTheory.Reformulated.B.Re4.UJ n ε)) Complex
                  (UpperTheory.Reformulated.B.Re4.instMeasurableSpaceUJ n ε)
                  (@OfNat.ofNat ENNReal (nat_lit 2)
                    (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                      (@AddMonoidWithOne.toNatCast ENNReal
                        (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                      UpperTheory.Reformulated.B.Re4.algebra_smulCommClass_complex))
                  (@UpperTheory.Reformulated.B.Re4.muG n ε) Complex.instNormedAddCommGroup))
              (@UpperTheory.Reformulated.B.Re4.L2 n ε)
              (@UniformSpace.toTopologicalSpace (@UpperTheory.Reformulated.B.Re4.L2 n ε)
                (@PseudoMetricSpace.toUniformSpace (@UpperTheory.Reformulated.B.Re4.L2 n ε)
                  (@SeminormedAddCommGroup.toPseudoMetricSpace (@UpperTheory.Reformulated.B.Re4.L2 n ε)
                    (@NormedAddCommGroup.toSeminormedAddCommGroup (@UpperTheory.Reformulated.B.Re4.L2 n ε)
                      (@MeasureTheory.Lp.instNormedAddCommGroup (↥(@UpperTheory.Reformulated.B.Re4.UJ n ε)) Complex
                        (UpperTheory.Reformulated.B.Re4.instMeasurableSpaceUJ n ε)
                        (@OfNat.ofNat ENNReal (nat_lit 2)
                          (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                            (@AddMonoidWithOne.toNatCast ENNReal
                              (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                            UpperTheory.Reformulated.B.Re4.algebra_smulCommClass_complex))
                        (@UpperTheory.Reformulated.B.Re4.muG n ε) Complex.instNormedAddCommGroup fact_one_le_two_ennreal)))))
              (@AddCommGroup.toAddCommMonoid (@UpperTheory.Reformulated.B.Re4.L2 n ε)
                (@MeasureTheory.Lp.instAddCommGroup (↥(@UpperTheory.Reformulated.B.Re4.UJ n ε)) Complex
                  (UpperTheory.Reformulated.B.Re4.instMeasurableSpaceUJ n ε)
                  (@OfNat.ofNat ENNReal (nat_lit 2)
                    (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                      (@AddMonoidWithOne.toNatCast ENNReal
                        (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                      UpperTheory.Reformulated.B.Re4.algebra_smulCommClass_complex))
                  (@UpperTheory.Reformulated.B.Re4.muG n ε) Complex.instNormedAddCommGroup))
              (@MeasureTheory.Lp.instModule (↥(@UpperTheory.Reformulated.B.Re4.UJ n ε)) Complex Complex
                (UpperTheory.Reformulated.B.Re4.instMeasurableSpaceUJ n ε)
                (@OfNat.ofNat ENNReal (nat_lit 2)
                  (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                    (@AddMonoidWithOne.toNatCast ENNReal
                      (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                    UpperTheory.Reformulated.B.Re4.algebra_smulCommClass_complex))
                (@UpperTheory.Reformulated.B.Re4.muG n ε) Complex.instNormedAddCommGroup
                (@CStarAlgebra.toNormedRing Complex (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex))
                (@Semiring.toModule Complex
                  (@Ring.toSemiring Complex
                    (@NormedRing.toRing Complex
                      (@CStarAlgebra.toNormedRing Complex
                        (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex)))))
                UpperTheory.Reformulated.B.Re4.complex_normed_instance_compat)
              (@MeasureTheory.Lp.instModule (↥(@UpperTheory.Reformulated.B.Re4.UJ n ε)) Complex Complex
                (UpperTheory.Reformulated.B.Re4.instMeasurableSpaceUJ n ε)
                (@OfNat.ofNat ENNReal (nat_lit 2)
                  (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                    (@AddMonoidWithOne.toNatCast ENNReal
                      (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                    UpperTheory.Reformulated.B.Re4.algebra_smulCommClass_complex))
                (@UpperTheory.Reformulated.B.Re4.muG n ε) Complex.instNormedAddCommGroup
                (@CStarAlgebra.toNormedRing Complex (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex))
                (@Semiring.toModule Complex
                  (@Ring.toSemiring Complex
                    (@NormedRing.toRing Complex
                      (@CStarAlgebra.toNormedRing Complex
                        (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex)))))
                UpperTheory.Reformulated.B.Re4.complex_normed_instance_compat))
            (@ContinuousLinearMap.one Complex Complex.instSemiring (@UpperTheory.Reformulated.B.Re4.L2 n ε)
              (@UniformSpace.toTopologicalSpace (@UpperTheory.Reformulated.B.Re4.L2 n ε)
                (@PseudoMetricSpace.toUniformSpace (@UpperTheory.Reformulated.B.Re4.L2 n ε)
                  (@SeminormedAddCommGroup.toPseudoMetricSpace (@UpperTheory.Reformulated.B.Re4.L2 n ε)
                    (@NormedAddCommGroup.toSeminormedAddCommGroup (@UpperTheory.Reformulated.B.Re4.L2 n ε)
                      (@MeasureTheory.Lp.instNormedAddCommGroup (↥(@UpperTheory.Reformulated.B.Re4.UJ n ε)) Complex
                        (UpperTheory.Reformulated.B.Re4.instMeasurableSpaceUJ n ε)
                        (@OfNat.ofNat ENNReal (nat_lit 2)
                          (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                            (@AddMonoidWithOne.toNatCast ENNReal
                              (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                            UpperTheory.Reformulated.B.Re4.algebra_smulCommClass_complex))
                        (@UpperTheory.Reformulated.B.Re4.muG n ε) Complex.instNormedAddCommGroup fact_one_le_two_ennreal)))))
              (@AddCommGroup.toAddCommMonoid (@UpperTheory.Reformulated.B.Re4.L2 n ε)
                (@MeasureTheory.Lp.instAddCommGroup (↥(@UpperTheory.Reformulated.B.Re4.UJ n ε)) Complex
                  (UpperTheory.Reformulated.B.Re4.instMeasurableSpaceUJ n ε)
                  (@OfNat.ofNat ENNReal (nat_lit 2)
                    (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                      (@AddMonoidWithOne.toNatCast ENNReal
                        (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                      UpperTheory.Reformulated.B.Re4.algebra_smulCommClass_complex))
                  (@UpperTheory.Reformulated.B.Re4.muG n ε) Complex.instNormedAddCommGroup))
              (@MeasureTheory.Lp.instModule (↥(@UpperTheory.Reformulated.B.Re4.UJ n ε)) Complex Complex
                (UpperTheory.Reformulated.B.Re4.instMeasurableSpaceUJ n ε)
                (@OfNat.ofNat ENNReal (nat_lit 2)
                  (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                    (@AddMonoidWithOne.toNatCast ENNReal
                      (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                    UpperTheory.Reformulated.B.Re4.algebra_smulCommClass_complex))
                (@UpperTheory.Reformulated.B.Re4.muG n ε) Complex.instNormedAddCommGroup
                (@CStarAlgebra.toNormedRing Complex (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex))
                (@Semiring.toModule Complex
                  (@Ring.toSemiring Complex
                    (@NormedRing.toRing Complex
                      (@CStarAlgebra.toNormedRing Complex
                        (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex)))))
                UpperTheory.Reformulated.B.Re4.complex_normed_instance_compat)))
noncomputable def UpperTheory.Reformulated.B.Re4.rreg :
    {n : Nat} →
      (ε : Fin n → Bool) →
        Matrix (Fin n) (Fin n) Complex →
          @ContinuousLinearMap Complex Complex Complex.instSemiring Complex.instSemiring
            (@RingHom.id Complex (@Semiring.toNonAssocSemiring Complex Complex.instSemiring)) (@UpperTheory.Reformulated.B.Re4.L2 n ε)
            (@UniformSpace.toTopologicalSpace (@UpperTheory.Reformulated.B.Re4.L2 n ε)
              (@PseudoMetricSpace.toUniformSpace (@UpperTheory.Reformulated.B.Re4.L2 n ε)
                (@SeminormedAddCommGroup.toPseudoMetricSpace (@UpperTheory.Reformulated.B.Re4.L2 n ε)
                  (@NormedAddCommGroup.toSeminormedAddCommGroup (@UpperTheory.Reformulated.B.Re4.L2 n ε)
                    (@MeasureTheory.Lp.instNormedAddCommGroup (↥(@UpperTheory.Reformulated.B.Re4.UJ n ε)) Complex
                      (UpperTheory.Reformulated.B.Re4.instMeasurableSpaceUJ n ε)
                      (@OfNat.ofNat ENNReal (nat_lit 2)
                        (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                          (@AddMonoidWithOne.toNatCast ENNReal
                            (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                          UpperTheory.Reformulated.B.Re4.algebra_smulCommClass_complex))
                      (@UpperTheory.Reformulated.B.Re4.muG n ε) Complex.instNormedAddCommGroup fact_one_le_two_ennreal)))))
            (@AddCommGroup.toAddCommMonoid (@UpperTheory.Reformulated.B.Re4.L2 n ε)
              (@MeasureTheory.Lp.instAddCommGroup (↥(@UpperTheory.Reformulated.B.Re4.UJ n ε)) Complex
                (UpperTheory.Reformulated.B.Re4.instMeasurableSpaceUJ n ε)
                (@OfNat.ofNat ENNReal (nat_lit 2)
                  (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                    (@AddMonoidWithOne.toNatCast ENNReal
                      (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                    UpperTheory.Reformulated.B.Re4.algebra_smulCommClass_complex))
                (@UpperTheory.Reformulated.B.Re4.muG n ε) Complex.instNormedAddCommGroup))
            (@UpperTheory.Reformulated.B.Re4.L2 n ε)
            (@UniformSpace.toTopologicalSpace (@UpperTheory.Reformulated.B.Re4.L2 n ε)
              (@PseudoMetricSpace.toUniformSpace (@UpperTheory.Reformulated.B.Re4.L2 n ε)
                (@SeminormedAddCommGroup.toPseudoMetricSpace (@UpperTheory.Reformulated.B.Re4.L2 n ε)
                  (@NormedAddCommGroup.toSeminormedAddCommGroup (@UpperTheory.Reformulated.B.Re4.L2 n ε)
                    (@MeasureTheory.Lp.instNormedAddCommGroup (↥(@UpperTheory.Reformulated.B.Re4.UJ n ε)) Complex
                      (UpperTheory.Reformulated.B.Re4.instMeasurableSpaceUJ n ε)
                      (@OfNat.ofNat ENNReal (nat_lit 2)
                        (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                          (@AddMonoidWithOne.toNatCast ENNReal
                            (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                          UpperTheory.Reformulated.B.Re4.algebra_smulCommClass_complex))
                      (@UpperTheory.Reformulated.B.Re4.muG n ε) Complex.instNormedAddCommGroup fact_one_le_two_ennreal)))))
            (@AddCommGroup.toAddCommMonoid (@UpperTheory.Reformulated.B.Re4.L2 n ε)
              (@MeasureTheory.Lp.instAddCommGroup (↥(@UpperTheory.Reformulated.B.Re4.UJ n ε)) Complex
                (UpperTheory.Reformulated.B.Re4.instMeasurableSpaceUJ n ε)
                (@OfNat.ofNat ENNReal (nat_lit 2)
                  (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                    (@AddMonoidWithOne.toNatCast ENNReal
                      (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                    UpperTheory.Reformulated.B.Re4.algebra_smulCommClass_complex))
                (@UpperTheory.Reformulated.B.Re4.muG n ε) Complex.instNormedAddCommGroup))
            (@MeasureTheory.Lp.instModule (↥(@UpperTheory.Reformulated.B.Re4.UJ n ε)) Complex Complex
              (UpperTheory.Reformulated.B.Re4.instMeasurableSpaceUJ n ε)
              (@OfNat.ofNat ENNReal (nat_lit 2)
                (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                  (@AddMonoidWithOne.toNatCast ENNReal
                    (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                  UpperTheory.Reformulated.B.Re4.algebra_smulCommClass_complex))
              (@UpperTheory.Reformulated.B.Re4.muG n ε) Complex.instNormedAddCommGroup
              (@CStarAlgebra.toNormedRing Complex (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex))
              (@Semiring.toModule Complex
                (@Ring.toSemiring Complex
                  (@NormedRing.toRing Complex
                    (@CStarAlgebra.toNormedRing Complex
                      (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex)))))
              (@NormedSpace.toIsBoundedSMul Complex Complex Complex.instNormedField
                (@NonUnitalSeminormedRing.toSeminormedAddCommGroup Complex
                  (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing Complex
                    (@SeminormedCommRing.toNonUnitalSeminormedCommRing Complex
                      (@NormedCommRing.toSeminormedCommRing Complex
                        (@CommCStarAlgebra.toNormedCommRing Complex instCommCStarAlgebraComplex)))))
                (@NonUnitalCStarAlgebra.toNormedSpace Complex
                  (@NonUnitalCommCStarAlgebra.toNonUnitalCStarAlgebra Complex
                    (@CommCStarAlgebra.toNonUnitalCommCStarAlgebra Complex instCommCStarAlgebraComplex)))))
            (@MeasureTheory.Lp.instModule (↥(@UpperTheory.Reformulated.B.Re4.UJ n ε)) Complex Complex
              (UpperTheory.Reformulated.B.Re4.instMeasurableSpaceUJ n ε)
              (@OfNat.ofNat ENNReal (nat_lit 2)
                (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                  (@AddMonoidWithOne.toNatCast ENNReal
                    (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                  UpperTheory.Reformulated.B.Re4.algebra_smulCommClass_complex))
              (@UpperTheory.Reformulated.B.Re4.muG n ε) Complex.instNormedAddCommGroup
              (@CStarAlgebra.toNormedRing Complex (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex))
              (@Semiring.toModule Complex
                (@Ring.toSemiring Complex
                  (@NormedRing.toRing Complex
                    (@CStarAlgebra.toNormedRing Complex
                      (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex)))))
              (@NormedSpace.toIsBoundedSMul Complex Complex Complex.instNormedField
                (@NonUnitalSeminormedRing.toSeminormedAddCommGroup Complex
                  (@NonUnitalSeminormedCommRing.toNonUnitalSeminormedRing Complex
                    (@SeminormedCommRing.toNonUnitalSeminormedCommRing Complex
                      (@NormedCommRing.toSeminormedCommRing Complex
                        (@CommCStarAlgebra.toNormedCommRing Complex instCommCStarAlgebraComplex)))))
                (@NonUnitalCStarAlgebra.toNormedSpace Complex
                  (@NonUnitalCommCStarAlgebra.toNonUnitalCStarAlgebra Complex
                    (@CommCStarAlgebra.toNonUnitalCommCStarAlgebra Complex instCommCStarAlgebraComplex))))) :=
    fun {n : Nat} (ε : Fin n → Bool) (g : Matrix (Fin n) (Fin n) Complex) ↦
      @dite
        (@ContinuousLinearMap Complex Complex Complex.instSemiring Complex.instSemiring
          (@RingHom.id Complex (@Semiring.toNonAssocSemiring Complex Complex.instSemiring)) (@UpperTheory.Reformulated.B.Re4.L2 n ε)
          (@UniformSpace.toTopologicalSpace (@UpperTheory.Reformulated.B.Re4.L2 n ε)
            (@PseudoMetricSpace.toUniformSpace (@UpperTheory.Reformulated.B.Re4.L2 n ε)
              (@SeminormedAddCommGroup.toPseudoMetricSpace (@UpperTheory.Reformulated.B.Re4.L2 n ε)
                (@NormedAddCommGroup.toSeminormedAddCommGroup (@UpperTheory.Reformulated.B.Re4.L2 n ε)
                  (@MeasureTheory.Lp.instNormedAddCommGroup (↥(@UpperTheory.Reformulated.B.Re4.UJ n ε)) Complex
                    (UpperTheory.Reformulated.B.Re4.instMeasurableSpaceUJ n ε)
                    (@OfNat.ofNat ENNReal (nat_lit 2)
                      (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                        (@AddMonoidWithOne.toNatCast ENNReal
                          (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                        UpperTheory.Reformulated.B.Re4.algebra_smulCommClass_complex))
                    (@UpperTheory.Reformulated.B.Re4.muG n ε) Complex.instNormedAddCommGroup fact_one_le_two_ennreal)))))
          (@AddCommGroup.toAddCommMonoid (@UpperTheory.Reformulated.B.Re4.L2 n ε)
            (@MeasureTheory.Lp.instAddCommGroup (↥(@UpperTheory.Reformulated.B.Re4.UJ n ε)) Complex
              (UpperTheory.Reformulated.B.Re4.instMeasurableSpaceUJ n ε)
              (@OfNat.ofNat ENNReal (nat_lit 2)
                (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                  (@AddMonoidWithOne.toNatCast ENNReal
                    (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                  UpperTheory.Reformulated.B.Re4.algebra_smulCommClass_complex))
              (@UpperTheory.Reformulated.B.Re4.muG n ε) Complex.instNormedAddCommGroup))
          (@UpperTheory.Reformulated.B.Re4.L2 n ε)
          (@UniformSpace.toTopologicalSpace (@UpperTheory.Reformulated.B.Re4.L2 n ε)
            (@PseudoMetricSpace.toUniformSpace (@UpperTheory.Reformulated.B.Re4.L2 n ε)
              (@SeminormedAddCommGroup.toPseudoMetricSpace (@UpperTheory.Reformulated.B.Re4.L2 n ε)
                (@NormedAddCommGroup.toSeminormedAddCommGroup (@UpperTheory.Reformulated.B.Re4.L2 n ε)
                  (@MeasureTheory.Lp.instNormedAddCommGroup (↥(@UpperTheory.Reformulated.B.Re4.UJ n ε)) Complex
                    (UpperTheory.Reformulated.B.Re4.instMeasurableSpaceUJ n ε)
                    (@OfNat.ofNat ENNReal (nat_lit 2)
                      (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                        (@AddMonoidWithOne.toNatCast ENNReal
                          (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                        UpperTheory.Reformulated.B.Re4.algebra_smulCommClass_complex))
                    (@UpperTheory.Reformulated.B.Re4.muG n ε) Complex.instNormedAddCommGroup fact_one_le_two_ennreal)))))
          (@AddCommGroup.toAddCommMonoid (@UpperTheory.Reformulated.B.Re4.L2 n ε)
            (@MeasureTheory.Lp.instAddCommGroup (↥(@UpperTheory.Reformulated.B.Re4.UJ n ε)) Complex
              (UpperTheory.Reformulated.B.Re4.instMeasurableSpaceUJ n ε)
              (@OfNat.ofNat ENNReal (nat_lit 2)
                (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                  (@AddMonoidWithOne.toNatCast ENNReal
                    (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                  UpperTheory.Reformulated.B.Re4.algebra_smulCommClass_complex))
              (@UpperTheory.Reformulated.B.Re4.muG n ε) Complex.instNormedAddCommGroup))
          (@MeasureTheory.Lp.instModule (↥(@UpperTheory.Reformulated.B.Re4.UJ n ε)) Complex Complex
            (UpperTheory.Reformulated.B.Re4.instMeasurableSpaceUJ n ε)
            (@OfNat.ofNat ENNReal (nat_lit 2)
              (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                (@AddMonoidWithOne.toNatCast ENNReal
                  (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                UpperTheory.Reformulated.B.Re4.algebra_smulCommClass_complex))
            (@UpperTheory.Reformulated.B.Re4.muG n ε) Complex.instNormedAddCommGroup
            (@CStarAlgebra.toNormedRing Complex (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex))
            (@Semiring.toModule Complex
              (@Ring.toSemiring Complex
                (@NormedRing.toRing Complex
                  (@CStarAlgebra.toNormedRing Complex
                    (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex)))))
            UpperTheory.Reformulated.B.Re4.complex_normed_instance_compat)
          (@MeasureTheory.Lp.instModule (↥(@UpperTheory.Reformulated.B.Re4.UJ n ε)) Complex Complex
            (UpperTheory.Reformulated.B.Re4.instMeasurableSpaceUJ n ε)
            (@OfNat.ofNat ENNReal (nat_lit 2)
              (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                (@AddMonoidWithOne.toNatCast ENNReal
                  (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                UpperTheory.Reformulated.B.Re4.algebra_smulCommClass_complex))
            (@UpperTheory.Reformulated.B.Re4.muG n ε) Complex.instNormedAddCommGroup
            (@CStarAlgebra.toNormedRing Complex (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex))
            (@Semiring.toModule Complex
              (@Ring.toSemiring Complex
                (@NormedRing.toRing Complex
                  (@CStarAlgebra.toNormedRing Complex
                    (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex)))))
            UpperTheory.Reformulated.B.Re4.complex_normed_instance_compat))
        (∃ (y : ↥(@UpperTheory.Reformulated.B.Re4.UJ n ε)), @Eq (Matrix (Fin n) (Fin n) Complex) (@UpperTheory.Reformulated.B.Re4.umat n ε y) g)
        (Classical.propDecidable
          (∃ (y : ↥(@UpperTheory.Reformulated.B.Re4.UJ n ε)), @Eq (Matrix (Fin n) (Fin n) Complex) (@UpperTheory.Reformulated.B.Re4.umat n ε y) g))
        (fun
            (h : ∃ (y : ↥(@UpperTheory.Reformulated.B.Re4.UJ n ε)), @Eq (Matrix (Fin n) (Fin n) Complex) (@UpperTheory.Reformulated.B.Re4.umat n ε y) g) ↦
          @UpperTheory.Reformulated.B.Re4.rregG n ε
            (@Exists.choose (↥(@UpperTheory.Reformulated.B.Re4.UJ n ε))
              (fun (y : ↥(@UpperTheory.Reformulated.B.Re4.UJ n ε)) ↦ @Eq (Matrix (Fin n) (Fin n) Complex) (@UpperTheory.Reformulated.B.Re4.umat n ε y) g)
              h))
        fun
          (h :
            Not
              (∃ (y : ↥(@UpperTheory.Reformulated.B.Re4.UJ n ε)), @Eq (Matrix (Fin n) (Fin n) Complex) (@UpperTheory.Reformulated.B.Re4.umat n ε y) g)) ↦
        @OfNat.ofNat
          (@ContinuousLinearMap Complex Complex Complex.instSemiring Complex.instSemiring
            (@RingHom.id Complex (@Semiring.toNonAssocSemiring Complex Complex.instSemiring)) (@UpperTheory.Reformulated.B.Re4.L2 n ε)
            (@UniformSpace.toTopologicalSpace (@UpperTheory.Reformulated.B.Re4.L2 n ε)
              (@PseudoMetricSpace.toUniformSpace (@UpperTheory.Reformulated.B.Re4.L2 n ε)
                (@SeminormedAddCommGroup.toPseudoMetricSpace (@UpperTheory.Reformulated.B.Re4.L2 n ε)
                  (@NormedAddCommGroup.toSeminormedAddCommGroup (@UpperTheory.Reformulated.B.Re4.L2 n ε)
                    (@MeasureTheory.Lp.instNormedAddCommGroup (↥(@UpperTheory.Reformulated.B.Re4.UJ n ε)) Complex
                      (UpperTheory.Reformulated.B.Re4.instMeasurableSpaceUJ n ε)
                      (@OfNat.ofNat ENNReal (nat_lit 2)
                        (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                          (@AddMonoidWithOne.toNatCast ENNReal
                            (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                          UpperTheory.Reformulated.B.Re4.algebra_smulCommClass_complex))
                      (@UpperTheory.Reformulated.B.Re4.muG n ε) Complex.instNormedAddCommGroup fact_one_le_two_ennreal)))))
            (@AddCommGroup.toAddCommMonoid (@UpperTheory.Reformulated.B.Re4.L2 n ε)
              (@MeasureTheory.Lp.instAddCommGroup (↥(@UpperTheory.Reformulated.B.Re4.UJ n ε)) Complex
                (UpperTheory.Reformulated.B.Re4.instMeasurableSpaceUJ n ε)
                (@OfNat.ofNat ENNReal (nat_lit 2)
                  (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                    (@AddMonoidWithOne.toNatCast ENNReal
                      (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                    UpperTheory.Reformulated.B.Re4.algebra_smulCommClass_complex))
                (@UpperTheory.Reformulated.B.Re4.muG n ε) Complex.instNormedAddCommGroup))
            (@UpperTheory.Reformulated.B.Re4.L2 n ε)
            (@UniformSpace.toTopologicalSpace (@UpperTheory.Reformulated.B.Re4.L2 n ε)
              (@PseudoMetricSpace.toUniformSpace (@UpperTheory.Reformulated.B.Re4.L2 n ε)
                (@SeminormedAddCommGroup.toPseudoMetricSpace (@UpperTheory.Reformulated.B.Re4.L2 n ε)
                  (@NormedAddCommGroup.toSeminormedAddCommGroup (@UpperTheory.Reformulated.B.Re4.L2 n ε)
                    (@MeasureTheory.Lp.instNormedAddCommGroup (↥(@UpperTheory.Reformulated.B.Re4.UJ n ε)) Complex
                      (UpperTheory.Reformulated.B.Re4.instMeasurableSpaceUJ n ε)
                      (@OfNat.ofNat ENNReal (nat_lit 2)
                        (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                          (@AddMonoidWithOne.toNatCast ENNReal
                            (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                          UpperTheory.Reformulated.B.Re4.algebra_smulCommClass_complex))
                      (@UpperTheory.Reformulated.B.Re4.muG n ε) Complex.instNormedAddCommGroup fact_one_le_two_ennreal)))))
            (@AddCommGroup.toAddCommMonoid (@UpperTheory.Reformulated.B.Re4.L2 n ε)
              (@MeasureTheory.Lp.instAddCommGroup (↥(@UpperTheory.Reformulated.B.Re4.UJ n ε)) Complex
                (UpperTheory.Reformulated.B.Re4.instMeasurableSpaceUJ n ε)
                (@OfNat.ofNat ENNReal (nat_lit 2)
                  (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                    (@AddMonoidWithOne.toNatCast ENNReal
                      (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                    UpperTheory.Reformulated.B.Re4.algebra_smulCommClass_complex))
                (@UpperTheory.Reformulated.B.Re4.muG n ε) Complex.instNormedAddCommGroup))
            (@MeasureTheory.Lp.instModule (↥(@UpperTheory.Reformulated.B.Re4.UJ n ε)) Complex Complex
              (UpperTheory.Reformulated.B.Re4.instMeasurableSpaceUJ n ε)
              (@OfNat.ofNat ENNReal (nat_lit 2)
                (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                  (@AddMonoidWithOne.toNatCast ENNReal
                    (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                  UpperTheory.Reformulated.B.Re4.algebra_smulCommClass_complex))
              (@UpperTheory.Reformulated.B.Re4.muG n ε) Complex.instNormedAddCommGroup
              (@CStarAlgebra.toNormedRing Complex (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex))
              (@Semiring.toModule Complex
                (@Ring.toSemiring Complex
                  (@NormedRing.toRing Complex
                    (@CStarAlgebra.toNormedRing Complex
                      (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex)))))
              UpperTheory.Reformulated.B.Re4.complex_normed_instance_compat)
            (@MeasureTheory.Lp.instModule (↥(@UpperTheory.Reformulated.B.Re4.UJ n ε)) Complex Complex
              (UpperTheory.Reformulated.B.Re4.instMeasurableSpaceUJ n ε)
              (@OfNat.ofNat ENNReal (nat_lit 2)
                (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                  (@AddMonoidWithOne.toNatCast ENNReal
                    (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                  UpperTheory.Reformulated.B.Re4.algebra_smulCommClass_complex))
              (@UpperTheory.Reformulated.B.Re4.muG n ε) Complex.instNormedAddCommGroup
              (@CStarAlgebra.toNormedRing Complex (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex))
              (@Semiring.toModule Complex
                (@Ring.toSemiring Complex
                  (@NormedRing.toRing Complex
                    (@CStarAlgebra.toNormedRing Complex
                      (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex)))))
              UpperTheory.Reformulated.B.Re4.complex_normed_instance_compat))
          (nat_lit 1)
          (@One.toOfNat1
            (@ContinuousLinearMap Complex Complex Complex.instSemiring Complex.instSemiring
              (@RingHom.id Complex (@Semiring.toNonAssocSemiring Complex Complex.instSemiring)) (@UpperTheory.Reformulated.B.Re4.L2 n ε)
              (@UniformSpace.toTopologicalSpace (@UpperTheory.Reformulated.B.Re4.L2 n ε)
                (@PseudoMetricSpace.toUniformSpace (@UpperTheory.Reformulated.B.Re4.L2 n ε)
                  (@SeminormedAddCommGroup.toPseudoMetricSpace (@UpperTheory.Reformulated.B.Re4.L2 n ε)
                    (@NormedAddCommGroup.toSeminormedAddCommGroup (@UpperTheory.Reformulated.B.Re4.L2 n ε)
                      (@MeasureTheory.Lp.instNormedAddCommGroup (↥(@UpperTheory.Reformulated.B.Re4.UJ n ε)) Complex
                        (UpperTheory.Reformulated.B.Re4.instMeasurableSpaceUJ n ε)
                        (@OfNat.ofNat ENNReal (nat_lit 2)
                          (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                            (@AddMonoidWithOne.toNatCast ENNReal
                              (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                            UpperTheory.Reformulated.B.Re4.algebra_smulCommClass_complex))
                        (@UpperTheory.Reformulated.B.Re4.muG n ε) Complex.instNormedAddCommGroup fact_one_le_two_ennreal)))))
              (@AddCommGroup.toAddCommMonoid (@UpperTheory.Reformulated.B.Re4.L2 n ε)
                (@MeasureTheory.Lp.instAddCommGroup (↥(@UpperTheory.Reformulated.B.Re4.UJ n ε)) Complex
                  (UpperTheory.Reformulated.B.Re4.instMeasurableSpaceUJ n ε)
                  (@OfNat.ofNat ENNReal (nat_lit 2)
                    (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                      (@AddMonoidWithOne.toNatCast ENNReal
                        (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                      UpperTheory.Reformulated.B.Re4.algebra_smulCommClass_complex))
                  (@UpperTheory.Reformulated.B.Re4.muG n ε) Complex.instNormedAddCommGroup))
              (@UpperTheory.Reformulated.B.Re4.L2 n ε)
              (@UniformSpace.toTopologicalSpace (@UpperTheory.Reformulated.B.Re4.L2 n ε)
                (@PseudoMetricSpace.toUniformSpace (@UpperTheory.Reformulated.B.Re4.L2 n ε)
                  (@SeminormedAddCommGroup.toPseudoMetricSpace (@UpperTheory.Reformulated.B.Re4.L2 n ε)
                    (@NormedAddCommGroup.toSeminormedAddCommGroup (@UpperTheory.Reformulated.B.Re4.L2 n ε)
                      (@MeasureTheory.Lp.instNormedAddCommGroup (↥(@UpperTheory.Reformulated.B.Re4.UJ n ε)) Complex
                        (UpperTheory.Reformulated.B.Re4.instMeasurableSpaceUJ n ε)
                        (@OfNat.ofNat ENNReal (nat_lit 2)
                          (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                            (@AddMonoidWithOne.toNatCast ENNReal
                              (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                            UpperTheory.Reformulated.B.Re4.algebra_smulCommClass_complex))
                        (@UpperTheory.Reformulated.B.Re4.muG n ε) Complex.instNormedAddCommGroup fact_one_le_two_ennreal)))))
              (@AddCommGroup.toAddCommMonoid (@UpperTheory.Reformulated.B.Re4.L2 n ε)
                (@MeasureTheory.Lp.instAddCommGroup (↥(@UpperTheory.Reformulated.B.Re4.UJ n ε)) Complex
                  (UpperTheory.Reformulated.B.Re4.instMeasurableSpaceUJ n ε)
                  (@OfNat.ofNat ENNReal (nat_lit 2)
                    (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                      (@AddMonoidWithOne.toNatCast ENNReal
                        (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                      UpperTheory.Reformulated.B.Re4.algebra_smulCommClass_complex))
                  (@UpperTheory.Reformulated.B.Re4.muG n ε) Complex.instNormedAddCommGroup))
              (@MeasureTheory.Lp.instModule (↥(@UpperTheory.Reformulated.B.Re4.UJ n ε)) Complex Complex
                (UpperTheory.Reformulated.B.Re4.instMeasurableSpaceUJ n ε)
                (@OfNat.ofNat ENNReal (nat_lit 2)
                  (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                    (@AddMonoidWithOne.toNatCast ENNReal
                      (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                    UpperTheory.Reformulated.B.Re4.algebra_smulCommClass_complex))
                (@UpperTheory.Reformulated.B.Re4.muG n ε) Complex.instNormedAddCommGroup
                (@CStarAlgebra.toNormedRing Complex (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex))
                (@Semiring.toModule Complex
                  (@Ring.toSemiring Complex
                    (@NormedRing.toRing Complex
                      (@CStarAlgebra.toNormedRing Complex
                        (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex)))))
                UpperTheory.Reformulated.B.Re4.complex_normed_instance_compat)
              (@MeasureTheory.Lp.instModule (↥(@UpperTheory.Reformulated.B.Re4.UJ n ε)) Complex Complex
                (UpperTheory.Reformulated.B.Re4.instMeasurableSpaceUJ n ε)
                (@OfNat.ofNat ENNReal (nat_lit 2)
                  (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                    (@AddMonoidWithOne.toNatCast ENNReal
                      (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                    UpperTheory.Reformulated.B.Re4.algebra_smulCommClass_complex))
                (@UpperTheory.Reformulated.B.Re4.muG n ε) Complex.instNormedAddCommGroup
                (@CStarAlgebra.toNormedRing Complex (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex))
                (@Semiring.toModule Complex
                  (@Ring.toSemiring Complex
                    (@NormedRing.toRing Complex
                      (@CStarAlgebra.toNormedRing Complex
                        (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex)))))
                UpperTheory.Reformulated.B.Re4.complex_normed_instance_compat))
            (@ContinuousLinearMap.one Complex Complex.instSemiring (@UpperTheory.Reformulated.B.Re4.L2 n ε)
              (@UniformSpace.toTopologicalSpace (@UpperTheory.Reformulated.B.Re4.L2 n ε)
                (@PseudoMetricSpace.toUniformSpace (@UpperTheory.Reformulated.B.Re4.L2 n ε)
                  (@SeminormedAddCommGroup.toPseudoMetricSpace (@UpperTheory.Reformulated.B.Re4.L2 n ε)
                    (@NormedAddCommGroup.toSeminormedAddCommGroup (@UpperTheory.Reformulated.B.Re4.L2 n ε)
                      (@MeasureTheory.Lp.instNormedAddCommGroup (↥(@UpperTheory.Reformulated.B.Re4.UJ n ε)) Complex
                        (UpperTheory.Reformulated.B.Re4.instMeasurableSpaceUJ n ε)
                        (@OfNat.ofNat ENNReal (nat_lit 2)
                          (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                            (@AddMonoidWithOne.toNatCast ENNReal
                              (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                            UpperTheory.Reformulated.B.Re4.algebra_smulCommClass_complex))
                        (@UpperTheory.Reformulated.B.Re4.muG n ε) Complex.instNormedAddCommGroup fact_one_le_two_ennreal)))))
              (@AddCommGroup.toAddCommMonoid (@UpperTheory.Reformulated.B.Re4.L2 n ε)
                (@MeasureTheory.Lp.instAddCommGroup (↥(@UpperTheory.Reformulated.B.Re4.UJ n ε)) Complex
                  (UpperTheory.Reformulated.B.Re4.instMeasurableSpaceUJ n ε)
                  (@OfNat.ofNat ENNReal (nat_lit 2)
                    (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                      (@AddMonoidWithOne.toNatCast ENNReal
                        (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                      UpperTheory.Reformulated.B.Re4.algebra_smulCommClass_complex))
                  (@UpperTheory.Reformulated.B.Re4.muG n ε) Complex.instNormedAddCommGroup))
              (@MeasureTheory.Lp.instModule (↥(@UpperTheory.Reformulated.B.Re4.UJ n ε)) Complex Complex
                (UpperTheory.Reformulated.B.Re4.instMeasurableSpaceUJ n ε)
                (@OfNat.ofNat ENNReal (nat_lit 2)
                  (@instOfNatAtLeastTwo ENNReal (nat_lit 2)
                    (@AddMonoidWithOne.toNatCast ENNReal
                      (@AddCommMonoidWithOne.toAddMonoidWithOne ENNReal ENNReal.instAddCommMonoidWithOne))
                    UpperTheory.Reformulated.B.Re4.algebra_smulCommClass_complex))
                (@UpperTheory.Reformulated.B.Re4.muG n ε) Complex.instNormedAddCommGroup
                (@CStarAlgebra.toNormedRing Complex (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex))
                (@Semiring.toModule Complex
                  (@Ring.toSemiring Complex
                    (@NormedRing.toRing Complex
                      (@CStarAlgebra.toNormedRing Complex
                        (@CommCStarAlgebra.toCStarAlgebra Complex instCommCStarAlgebraComplex)))))
                UpperTheory.Reformulated.B.Re4.complex_normed_instance_compat)))
noncomputable def UpperTheory.Reformulated.B.Re4.d21 :
    {n : Nat} → (Fin n → Bool) → Set (Matrix (Fin n) (Fin n) Complex) :=
    fun {n : Nat} (ε : Fin n → Bool) ↦
      @Set.ofPred (Matrix (Fin n) (Fin n) Complex) fun (g : Matrix (Fin n) (Fin n) Complex) ↦
        And
          (@Membership.mem (Matrix (Fin n) (Fin n) Complex)
            (@Submonoid (Matrix (Fin n) (Fin n) Complex)
              (@MulZeroOneClass.toMulOneClass (Matrix (Fin n) (Fin n) Complex)
                (@instMulZeroOneClassOfSemiring (Matrix (Fin n) (Fin n) Complex)
                  (@Matrix.semiring (Fin n) Complex
                    (@CommSemiring.toSemiring Complex (@CommRing.toCommSemiring Complex Complex.commRing)) (Fin.fintype n)
                    (instDecidableEqFin n)))))
            (@SetLike.instMembership
              (@Submonoid (Matrix (Fin n) (Fin n) Complex)
                (@MulZeroOneClass.toMulOneClass (Matrix (Fin n) (Fin n) Complex)
                  (@instMulZeroOneClassOfSemiring (Matrix (Fin n) (Fin n) Complex)
                    (@Matrix.semiring (Fin n) Complex
                      (@CommSemiring.toSemiring Complex (@CommRing.toCommSemiring Complex Complex.commRing)) (Fin.fintype n)
                      (instDecidableEqFin n)))))
              (Matrix (Fin n) (Fin n) Complex)
              (@Submonoid.instSetLike (Matrix (Fin n) (Fin n) Complex)
                (@MulZeroOneClass.toMulOneClass (Matrix (Fin n) (Fin n) Complex)
                  (@instMulZeroOneClassOfSemiring (Matrix (Fin n) (Fin n) Complex)
                    (@Matrix.semiring (Fin n) Complex
                      (@CommSemiring.toSemiring Complex (@CommRing.toCommSemiring Complex Complex.commRing)) (Fin.fintype n)
                      (instDecidableEqFin n))))))
            (@Matrix.unitaryGroup (Fin n) (instDecidableEqFin n) (Fin.fintype n) Complex Complex.commRing
              Complex.instStarRing)
            g)
          (@Eq (Matrix (Fin n) (Fin n) Complex)
            (@HMul.hMul (Matrix (Fin n) (Fin n) Complex) (Matrix (Fin n) (Fin n) Complex) (Matrix (Fin n) (Fin n) Complex)
              (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid (Fin n) (Fin n) (Fin n) Complex (Fin.fintype n) Complex.instMul
                Complex.instAddCommMonoid)
              g (@UpperTheory.Reformulated.B.Re4.Jm n ε))
            (@HMul.hMul (Matrix (Fin n) (Fin n) Complex) (Matrix (Fin n) (Fin n) Complex) (Matrix (Fin n) (Fin n) Complex)
              (@Matrix.instHMulOfFintypeOfMulOfAddCommMonoid (Fin n) (Fin n) (Fin n) Complex (Fin.fintype n) Complex.instMul
                Complex.instAddCommMonoid)
              (@UpperTheory.Reformulated.B.Re4.Jm n ε) g))
noncomputable def UpperTheory.Reformulated.B.Re4.IsKStableOn.{u_1} :
    {n : Nat} →
      {H : Type u_1} →
        [inst : NormedAddCommGroup H] →
          [inst_1 : @InnerProductSpace Complex H Complex.instRCLike (@NormedAddCommGroup.toSeminormedAddCommGroup H inst)] →
            (Fin n → Bool) →
              (Matrix (Fin n) (Fin n) Complex →
                  @ContinuousLinearMap Complex Complex Complex.instSemiring Complex.instSemiring
                    (@RingHom.id Complex (@Semiring.toNonAssocSemiring Complex Complex.instSemiring)) H
                    (@UniformSpace.toTopologicalSpace H
                      (@PseudoMetricSpace.toUniformSpace H
                        (@SeminormedAddCommGroup.toPseudoMetricSpace H
                          (@NormedAddCommGroup.toSeminormedAddCommGroup H inst))))
                    (@AddCommGroup.toAddCommMonoid H (@NormedAddCommGroup.toAddCommGroup H inst)) H
                    (@UniformSpace.toTopologicalSpace H
                      (@PseudoMetricSpace.toUniformSpace H
                        (@SeminormedAddCommGroup.toPseudoMetricSpace H
                          (@NormedAddCommGroup.toSeminormedAddCommGroup H inst))))
                    (@AddCommGroup.toAddCommMonoid H (@NormedAddCommGroup.toAddCommGroup H inst))
                    (@NormedSpace.toModule Complex H Complex.instNormedField
                      (@NormedAddCommGroup.toSeminormedAddCommGroup H inst)
                      (@InnerProductSpace.toNormedSpace Complex H Complex.instRCLike
                        (@NormedAddCommGroup.toSeminormedAddCommGroup H inst) inst_1))
                    (@NormedSpace.toModule Complex H Complex.instNormedField
                      (@NormedAddCommGroup.toSeminormedAddCommGroup H inst)
                      (@InnerProductSpace.toNormedSpace Complex H Complex.instRCLike
                        (@NormedAddCommGroup.toSeminormedAddCommGroup H inst) inst_1))) →
                @Submodule Complex H Complex.instSemiring
                    (@AddCommGroup.toAddCommMonoid H (@NormedAddCommGroup.toAddCommGroup H inst))
                    (@NormedSpace.toModule Complex H Complex.instNormedField
                      (@NormedAddCommGroup.toSeminormedAddCommGroup H inst)
                      (@InnerProductSpace.toNormedSpace Complex H Complex.instRCLike
                        (@NormedAddCommGroup.toSeminormedAddCommGroup H inst) inst_1)) →
                  Prop :=
    fun {n : Nat} {H : Type u_1} [inst : NormedAddCommGroup H]
        [inst_1 : @InnerProductSpace Complex H Complex.instRCLike (@NormedAddCommGroup.toSeminormedAddCommGroup H inst)]
        (ε : Fin n → Bool)
        (σ :
          Matrix (Fin n) (Fin n) Complex →
            @ContinuousLinearMap Complex Complex Complex.instSemiring Complex.instSemiring
              (@RingHom.id Complex (@Semiring.toNonAssocSemiring Complex Complex.instSemiring)) H
              (@UniformSpace.toTopologicalSpace H
                (@PseudoMetricSpace.toUniformSpace H
                  (@SeminormedAddCommGroup.toPseudoMetricSpace H (@NormedAddCommGroup.toSeminormedAddCommGroup H inst))))
              (@AddCommGroup.toAddCommMonoid H (@NormedAddCommGroup.toAddCommGroup H inst)) H
              (@UniformSpace.toTopologicalSpace H
                (@PseudoMetricSpace.toUniformSpace H
                  (@SeminormedAddCommGroup.toPseudoMetricSpace H (@NormedAddCommGroup.toSeminormedAddCommGroup H inst))))
              (@AddCommGroup.toAddCommMonoid H (@NormedAddCommGroup.toAddCommGroup H inst))
              (@NormedSpace.toModule Complex H Complex.instNormedField (@NormedAddCommGroup.toSeminormedAddCommGroup H inst)
                (@InnerProductSpace.toNormedSpace Complex H Complex.instRCLike
                  (@NormedAddCommGroup.toSeminormedAddCommGroup H inst) inst_1))
              (@NormedSpace.toModule Complex H Complex.instNormedField (@NormedAddCommGroup.toSeminormedAddCommGroup H inst)
                (@InnerProductSpace.toNormedSpace Complex H Complex.instRCLike
                  (@NormedAddCommGroup.toSeminormedAddCommGroup H inst) inst_1)))
        (S :
          @Submodule Complex H Complex.instSemiring
            (@AddCommGroup.toAddCommMonoid H (@NormedAddCommGroup.toAddCommGroup H inst))
            (@NormedSpace.toModule Complex H Complex.instNormedField (@NormedAddCommGroup.toSeminormedAddCommGroup H inst)
              (@InnerProductSpace.toNormedSpace Complex H Complex.instRCLike
                (@NormedAddCommGroup.toSeminormedAddCommGroup H inst) inst_1))) ↦
      ∀ (g : Matrix (Fin n) (Fin n) Complex),
        @Membership.mem (Matrix (Fin n) (Fin n) Complex) (Set (Matrix (Fin n) (Fin n) Complex))
            (@Set.instMembership (Matrix (Fin n) (Fin n) Complex)) (@UpperTheory.Reformulated.B.Re4.d21 n ε) g →
          ∀ (v : H),
            @Membership.mem H
                (@Submodule Complex H Complex.instSemiring
                  (@AddCommGroup.toAddCommMonoid H (@NormedAddCommGroup.toAddCommGroup H inst))
                  (@NormedSpace.toModule Complex H Complex.instNormedField
                    (@NormedAddCommGroup.toSeminormedAddCommGroup H inst)
                    (@InnerProductSpace.toNormedSpace Complex H Complex.instRCLike
                      (@NormedAddCommGroup.toSeminormedAddCommGroup H inst) inst_1)))
                (@SetLike.instMembership
                  (@Submodule Complex H Complex.instSemiring
                    (@AddCommGroup.toAddCommMonoid H (@NormedAddCommGroup.toAddCommGroup H inst))
                    (@NormedSpace.toModule Complex H Complex.instNormedField
                      (@NormedAddCommGroup.toSeminormedAddCommGroup H inst)
                      (@InnerProductSpace.toNormedSpace Complex H Complex.instRCLike
                        (@NormedAddCommGroup.toSeminormedAddCommGroup H inst) inst_1)))
                  H
                  (@Submodule.setLike Complex H Complex.instSemiring
                    (@AddCommGroup.toAddCommMonoid H (@NormedAddCommGroup.toAddCommGroup H inst))
                    (@NormedSpace.toModule Complex H Complex.instNormedField
                      (@NormedAddCommGroup.toSeminormedAddCommGroup H inst)
                      (@InnerProductSpace.toNormedSpace Complex H Complex.instRCLike
                        (@NormedAddCommGroup.toSeminormedAddCommGroup H inst) inst_1))))
                S v →
              @Membership.mem H
                (@Submodule Complex H Complex.instSemiring
                  (@AddCommGroup.toAddCommMonoid H (@NormedAddCommGroup.toAddCommGroup H inst))
                  (@NormedSpace.toModule Complex H Complex.instNormedField
                    (@NormedAddCommGroup.toSeminormedAddCommGroup H inst)
                    (@InnerProductSpace.toNormedSpace Complex H Complex.instRCLike
                      (@NormedAddCommGroup.toSeminormedAddCommGroup H inst) inst_1)))
                (@SetLike.instMembership
                  (@Submodule Complex H Complex.instSemiring
                    (@AddCommGroup.toAddCommMonoid H (@NormedAddCommGroup.toAddCommGroup H inst))
                    (@NormedSpace.toModule Complex H Complex.instNormedField
                      (@NormedAddCommGroup.toSeminormedAddCommGroup H inst)
                      (@InnerProductSpace.toNormedSpace Complex H Complex.instRCLike
                        (@NormedAddCommGroup.toSeminormedAddCommGroup H inst) inst_1)))
                  H
                  (@Submodule.setLike Complex H Complex.instSemiring
                    (@AddCommGroup.toAddCommMonoid H (@NormedAddCommGroup.toAddCommGroup H inst))
                    (@NormedSpace.toModule Complex H Complex.instNormedField
                      (@NormedAddCommGroup.toSeminormedAddCommGroup H inst)
                      (@InnerProductSpace.toNormedSpace Complex H Complex.instRCLike
                        (@NormedAddCommGroup.toSeminormedAddCommGroup H inst) inst_1))))
                S
                (@DFunLike.coe
                  (@ContinuousLinearMap Complex Complex Complex.instSemiring Complex.instSemiring
                    (@RingHom.id Complex (@Semiring.toNonAssocSemiring Complex Complex.instSemiring)) H
                    (@UniformSpace.toTopologicalSpace H
                      (@PseudoMetricSpace.toUniformSpace H
                        (@SeminormedAddCommGroup.toPseudoMetricSpace H
                          (@NormedAddCommGroup.toSeminormedAddCommGroup H inst))))
                    (@AddCommGroup.toAddCommMonoid H (@NormedAddCommGroup.toAddCommGroup H inst)) H
                    (@UniformSpace.toTopologicalSpace H
                      (@PseudoMetricSpace.toUniformSpace H
                        (@SeminormedAddCommGroup.toPseudoMetricSpace H
                          (@NormedAddCommGroup.toSeminormedAddCommGroup H inst))))
                    (@AddCommGroup.toAddCommMonoid H (@NormedAddCommGroup.toAddCommGroup H inst))
                    (@NormedSpace.toModule Complex H Complex.instNormedField
                      (@NormedAddCommGroup.toSeminormedAddCommGroup H inst)
                      (@InnerProductSpace.toNormedSpace Complex H Complex.instRCLike
                        (@NormedAddCommGroup.toSeminormedAddCommGroup H inst) inst_1))
                    (@NormedSpace.toModule Complex H Complex.instNormedField
                      (@NormedAddCommGroup.toSeminormedAddCommGroup H inst)
                      (@InnerProductSpace.toNormedSpace Complex H Complex.instRCLike
                        (@NormedAddCommGroup.toSeminormedAddCommGroup H inst) inst_1)))
                  H (fun (x : H) ↦ H)
                  (@ContinuousLinearMap.funLike Complex Complex Complex.instSemiring Complex.instSemiring
                    (@RingHom.id Complex (@Semiring.toNonAssocSemiring Complex Complex.instSemiring)) H
                    (@UniformSpace.toTopologicalSpace H
                      (@PseudoMetricSpace.toUniformSpace H
                        (@SeminormedAddCommGroup.toPseudoMetricSpace H
                          (@NormedAddCommGroup.toSeminormedAddCommGroup H inst))))
                    (@AddCommGroup.toAddCommMonoid H (@NormedAddCommGroup.toAddCommGroup H inst)) H
                    (@UniformSpace.toTopologicalSpace H
                      (@PseudoMetricSpace.toUniformSpace H
                        (@SeminormedAddCommGroup.toPseudoMetricSpace H
                          (@NormedAddCommGroup.toSeminormedAddCommGroup H inst))))
                    (@AddCommGroup.toAddCommMonoid H (@NormedAddCommGroup.toAddCommGroup H inst))
                    (@NormedSpace.toModule Complex H Complex.instNormedField
                      (@NormedAddCommGroup.toSeminormedAddCommGroup H inst)
                      (@InnerProductSpace.toNormedSpace Complex H Complex.instRCLike
                        (@NormedAddCommGroup.toSeminormedAddCommGroup H inst) inst_1))
                    (@NormedSpace.toModule Complex H Complex.instNormedField
                      (@NormedAddCommGroup.toSeminormedAddCommGroup H inst)
                      (@InnerProductSpace.toNormedSpace Complex H Complex.instRCLike
                        (@NormedAddCommGroup.toSeminormedAddCommGroup H inst) inst_1)))
                  (σ g) v)
noncomputable def UpperTheory.Reformulated.B.Re4.IsWtOn.{u_1} :
    {n : Nat} →
      {H : Type u_1} →
        [inst : NormedAddCommGroup H] →
          [inst_1 : @InnerProductSpace Complex H Complex.instRCLike (@NormedAddCommGroup.toSeminormedAddCommGroup H inst)] →
            Set (Matrix (Fin n) (Fin n) Complex) →
              (Matrix (Fin n) (Fin n) Complex →
                  @ContinuousLinearMap Complex Complex Complex.instSemiring Complex.instSemiring
                    (@RingHom.id Complex (@Semiring.toNonAssocSemiring Complex Complex.instSemiring)) H
                    (@UniformSpace.toTopologicalSpace H
                      (@PseudoMetricSpace.toUniformSpace H
                        (@SeminormedAddCommGroup.toPseudoMetricSpace H
                          (@NormedAddCommGroup.toSeminormedAddCommGroup H inst))))
                    (@AddCommGroup.toAddCommMonoid H (@NormedAddCommGroup.toAddCommGroup H inst)) H
                    (@UniformSpace.toTopologicalSpace H
                      (@PseudoMetricSpace.toUniformSpace H
                        (@SeminormedAddCommGroup.toPseudoMetricSpace H
                          (@NormedAddCommGroup.toSeminormedAddCommGroup H inst))))
                    (@AddCommGroup.toAddCommMonoid H (@NormedAddCommGroup.toAddCommGroup H inst))
                    (@NormedSpace.toModule Complex H Complex.instNormedField
                      (@NormedAddCommGroup.toSeminormedAddCommGroup H inst)
                      (@InnerProductSpace.toNormedSpace Complex H Complex.instRCLike
                        (@NormedAddCommGroup.toSeminormedAddCommGroup H inst) inst_1))
                    (@NormedSpace.toModule Complex H Complex.instNormedField
                      (@NormedAddCommGroup.toSeminormedAddCommGroup H inst)
                      (@InnerProductSpace.toNormedSpace Complex H Complex.instRCLike
                        (@NormedAddCommGroup.toSeminormedAddCommGroup H inst) inst_1))) →
                (Fin n → Real) → H → Prop :=
    fun {n : Nat} {H : Type u_1} [inst : NormedAddCommGroup H]
        [inst_1 : @InnerProductSpace Complex H Complex.instRCLike (@NormedAddCommGroup.toSeminormedAddCommGroup H inst)]
        (G : Set (Matrix (Fin n) (Fin n) Complex))
        (σ :
          Matrix (Fin n) (Fin n) Complex →
            @ContinuousLinearMap Complex Complex Complex.instSemiring Complex.instSemiring
              (@RingHom.id Complex (@Semiring.toNonAssocSemiring Complex Complex.instSemiring)) H
              (@UniformSpace.toTopologicalSpace H
                (@PseudoMetricSpace.toUniformSpace H
                  (@SeminormedAddCommGroup.toPseudoMetricSpace H (@NormedAddCommGroup.toSeminormedAddCommGroup H inst))))
              (@AddCommGroup.toAddCommMonoid H (@NormedAddCommGroup.toAddCommGroup H inst)) H
              (@UniformSpace.toTopologicalSpace H
                (@PseudoMetricSpace.toUniformSpace H
                  (@SeminormedAddCommGroup.toPseudoMetricSpace H (@NormedAddCommGroup.toSeminormedAddCommGroup H inst))))
              (@AddCommGroup.toAddCommMonoid H (@NormedAddCommGroup.toAddCommGroup H inst))
              (@NormedSpace.toModule Complex H Complex.instNormedField (@NormedAddCommGroup.toSeminormedAddCommGroup H inst)
                (@InnerProductSpace.toNormedSpace Complex H Complex.instRCLike
                  (@NormedAddCommGroup.toSeminormedAddCommGroup H inst) inst_1))
              (@NormedSpace.toModule Complex H Complex.instNormedField (@NormedAddCommGroup.toSeminormedAddCommGroup H inst)
                (@InnerProductSpace.toNormedSpace Complex H Complex.instRCLike
                  (@NormedAddCommGroup.toSeminormedAddCommGroup H inst) inst_1)))
        (μ : Fin n → Real) (v : H) ↦
      ∀ (θ : Fin n → Real),
        @Membership.mem (Matrix (Fin n) (Fin n) Complex) (Set (Matrix (Fin n) (Fin n) Complex))
            (@Set.instMembership (Matrix (Fin n) (Fin n) Complex)) G
            (@Matrix.diagonal (Fin n) Complex (instDecidableEqFin n) Complex.instZero fun (a : Fin n) ↦
              Complex.exp
                (@HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul) (↑(θ a) : Complex) Complex.I)) →
          @Eq H
            (@DFunLike.coe
              (@ContinuousLinearMap Complex Complex Complex.instSemiring Complex.instSemiring
                (@RingHom.id Complex (@Semiring.toNonAssocSemiring Complex Complex.instSemiring)) H
                (@UniformSpace.toTopologicalSpace H
                  (@PseudoMetricSpace.toUniformSpace H
                    (@SeminormedAddCommGroup.toPseudoMetricSpace H (@NormedAddCommGroup.toSeminormedAddCommGroup H inst))))
                (@AddCommGroup.toAddCommMonoid H (@NormedAddCommGroup.toAddCommGroup H inst)) H
                (@UniformSpace.toTopologicalSpace H
                  (@PseudoMetricSpace.toUniformSpace H
                    (@SeminormedAddCommGroup.toPseudoMetricSpace H (@NormedAddCommGroup.toSeminormedAddCommGroup H inst))))
                (@AddCommGroup.toAddCommMonoid H (@NormedAddCommGroup.toAddCommGroup H inst))
                (@NormedSpace.toModule Complex H Complex.instNormedField
                  (@NormedAddCommGroup.toSeminormedAddCommGroup H inst)
                  (@InnerProductSpace.toNormedSpace Complex H Complex.instRCLike
                    (@NormedAddCommGroup.toSeminormedAddCommGroup H inst) inst_1))
                (@NormedSpace.toModule Complex H Complex.instNormedField
                  (@NormedAddCommGroup.toSeminormedAddCommGroup H inst)
                  (@InnerProductSpace.toNormedSpace Complex H Complex.instRCLike
                    (@NormedAddCommGroup.toSeminormedAddCommGroup H inst) inst_1)))
              H (fun (x : H) ↦ H)
              (@ContinuousLinearMap.funLike Complex Complex Complex.instSemiring Complex.instSemiring
                (@RingHom.id Complex (@Semiring.toNonAssocSemiring Complex Complex.instSemiring)) H
                (@UniformSpace.toTopologicalSpace H
                  (@PseudoMetricSpace.toUniformSpace H
                    (@SeminormedAddCommGroup.toPseudoMetricSpace H (@NormedAddCommGroup.toSeminormedAddCommGroup H inst))))
                (@AddCommGroup.toAddCommMonoid H (@NormedAddCommGroup.toAddCommGroup H inst)) H
                (@UniformSpace.toTopologicalSpace H
                  (@PseudoMetricSpace.toUniformSpace H
                    (@SeminormedAddCommGroup.toPseudoMetricSpace H (@NormedAddCommGroup.toSeminormedAddCommGroup H inst))))
                (@AddCommGroup.toAddCommMonoid H (@NormedAddCommGroup.toAddCommGroup H inst))
                (@NormedSpace.toModule Complex H Complex.instNormedField
                  (@NormedAddCommGroup.toSeminormedAddCommGroup H inst)
                  (@InnerProductSpace.toNormedSpace Complex H Complex.instRCLike
                    (@NormedAddCommGroup.toSeminormedAddCommGroup H inst) inst_1))
                (@NormedSpace.toModule Complex H Complex.instNormedField
                  (@NormedAddCommGroup.toSeminormedAddCommGroup H inst)
                  (@InnerProductSpace.toNormedSpace Complex H Complex.instRCLike
                    (@NormedAddCommGroup.toSeminormedAddCommGroup H inst) inst_1)))
              (σ
                (@Matrix.diagonal (Fin n) Complex (instDecidableEqFin n) Complex.instZero fun (a : Fin n) ↦
                  Complex.exp
                    (@HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul) (↑(θ a) : Complex) Complex.I)))
              v)
            (@HSMul.hSMul Complex H H
              (@instHSMul Complex H
                (@SMulZeroClass.toSMul Complex H
                  (@AddZero.toZero H
                    (@AddZeroClass.toAddZero H
                      (@AddMonoid.toAddZeroClass H
                        (@SubNegMonoid.toAddMonoid H
                          (@AddGroup.toSubNegMonoid H
                            (@AddCommGroup.toAddGroup H (@NormedAddCommGroup.toAddCommGroup H inst)))))))
                  (@DistribSMul.toSMulZeroClass Complex H
                    (@AddMonoid.toAddZeroClass H
                      (@SubNegMonoid.toAddMonoid H
                        (@AddGroup.toSubNegMonoid H
                          (@AddCommGroup.toAddGroup H (@NormedAddCommGroup.toAddCommGroup H inst)))))
                    (@DistribMulAction.toDistribSMul Complex H (@Semiring.toMonoid Complex Complex.instSemiring)
                      (@SubNegMonoid.toAddMonoid H
                        (@AddGroup.toSubNegMonoid H
                          (@AddCommGroup.toAddGroup H (@NormedAddCommGroup.toAddCommGroup H inst))))
                      (@Module.toDistribMulAction Complex H Complex.instSemiring
                        (@AddCommGroup.toAddCommMonoid H (@NormedAddCommGroup.toAddCommGroup H inst))
                        (@NormedSpace.toModule Complex H Complex.instNormedField
                          (@NormedAddCommGroup.toSeminormedAddCommGroup H inst)
                          (@InnerProductSpace.toNormedSpace Complex H Complex.instRCLike
                            (@NormedAddCommGroup.toSeminormedAddCommGroup H inst) inst_1)))))))
              (Complex.exp
                (@HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul)
                  (↑(∑ a : Fin n, @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (μ a) (θ a)) : Complex)
                  Complex.I))
              v)
noncomputable def UpperTheory.Reformulated.B.Re4.root :
    {n : Nat} → Fin n → Fin n → Fin n → Real :=
    fun {n : Nat} (a b : Fin n) ↦
      @HSub.hSub (Fin n → Real) (Fin n → Real) (Fin n → Real)
        (@instHSub (Fin n → Real) (@Pi.instSub (Fin n) (fun (j : Fin n) ↦ Real) fun (i : Fin n) ↦ Real.instSub))
        (@Pi.single (Fin n) (fun (a : Fin n) ↦ Real) (fun (i : Fin n) ↦ Real.instZero) (instDecidableEqFin n) a
          (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne)))
        (@Pi.single (Fin n) (fun (a : Fin n) ↦ Real) (fun (i : Fin n) ↦ Real.instZero) (instDecidableEqFin n) b
          (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne)))
noncomputable def UpperTheory.Reformulated.B.Re4.CDom :
    {n : Nat} → (Fin n → Bool) → (Fin n → Real) → (Fin n → Real) → Prop :=
    fun {n : Nat} (ε : Fin n → Bool) (μ Λ : Fin n → Real) ↦
      ∃ (c : Fin n → Fin n → Nat),
        And
          (∀ (a b : Fin n),
            @Ne Nat (c a b) (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
              And (@LT.lt (Fin n) (@instLTFin n) a b) (@Eq Bool (ε a) (ε b)))
          (@Eq (Fin n → Real)
            (@HSub.hSub (Fin n → Real) (Fin n → Real) (Fin n → Real)
              (@instHSub (Fin n → Real) (@Pi.instSub (Fin n) (fun (a : Fin n) ↦ Real) fun (i : Fin n) ↦ Real.instSub)) Λ μ)
            (∑ a : Fin n,
              ∑ b : Fin n,
                @HSMul.hSMul Real (Fin n → Real) (Fin n → Real)
                  (@instHSMul Real (Fin n → Real) (@Function.hasSMul (Fin n) Real Real (@instSMulOfMul Real Real.instMul)))
                  (@Nat.cast Real Real.instNatCast (c a b)) (@UpperTheory.Reformulated.B.Re4.root n a b)))
noncomputable def UpperTheory.Reformulated.B.Re4.IsKTypeOf.{u_1} :
    {n : Nat} →
      {H : Type u_1} →
        [inst : NormedAddCommGroup H] →
          [inst_1 : @InnerProductSpace Complex H Complex.instRCLike (@NormedAddCommGroup.toSeminormedAddCommGroup H inst)] →
            (Fin n → Bool) →
              (Matrix (Fin n) (Fin n) Complex →
                  @ContinuousLinearMap Complex Complex Complex.instSemiring Complex.instSemiring
                    (@RingHom.id Complex (@Semiring.toNonAssocSemiring Complex Complex.instSemiring)) H
                    (@UniformSpace.toTopologicalSpace H
                      (@PseudoMetricSpace.toUniformSpace H
                        (@SeminormedAddCommGroup.toPseudoMetricSpace H
                          (@NormedAddCommGroup.toSeminormedAddCommGroup H inst))))
                    (@AddCommGroup.toAddCommMonoid H (@NormedAddCommGroup.toAddCommGroup H inst)) H
                    (@UniformSpace.toTopologicalSpace H
                      (@PseudoMetricSpace.toUniformSpace H
                        (@SeminormedAddCommGroup.toPseudoMetricSpace H
                          (@NormedAddCommGroup.toSeminormedAddCommGroup H inst))))
                    (@AddCommGroup.toAddCommMonoid H (@NormedAddCommGroup.toAddCommGroup H inst))
                    (@NormedSpace.toModule Complex H Complex.instNormedField
                      (@NormedAddCommGroup.toSeminormedAddCommGroup H inst)
                      (@InnerProductSpace.toNormedSpace Complex H Complex.instRCLike
                        (@NormedAddCommGroup.toSeminormedAddCommGroup H inst) inst_1))
                    (@NormedSpace.toModule Complex H Complex.instNormedField
                      (@NormedAddCommGroup.toSeminormedAddCommGroup H inst)
                      (@InnerProductSpace.toNormedSpace Complex H Complex.instRCLike
                        (@NormedAddCommGroup.toSeminormedAddCommGroup H inst) inst_1))) →
                (Fin n → Real) →
                  @Submodule Complex H Complex.instSemiring
                      (@AddCommGroup.toAddCommMonoid H (@NormedAddCommGroup.toAddCommGroup H inst))
                      (@NormedSpace.toModule Complex H Complex.instNormedField
                        (@NormedAddCommGroup.toSeminormedAddCommGroup H inst)
                        (@InnerProductSpace.toNormedSpace Complex H Complex.instRCLike
                          (@NormedAddCommGroup.toSeminormedAddCommGroup H inst) inst_1)) →
                    Prop :=
    fun {n : Nat} {H : Type u_1} [inst : NormedAddCommGroup H]
        [inst_1 : @InnerProductSpace Complex H Complex.instRCLike (@NormedAddCommGroup.toSeminormedAddCommGroup H inst)]
        (ε : Fin n → Bool)
        (σ :
          Matrix (Fin n) (Fin n) Complex →
            @ContinuousLinearMap Complex Complex Complex.instSemiring Complex.instSemiring
              (@RingHom.id Complex (@Semiring.toNonAssocSemiring Complex Complex.instSemiring)) H
              (@UniformSpace.toTopologicalSpace H
                (@PseudoMetricSpace.toUniformSpace H
                  (@SeminormedAddCommGroup.toPseudoMetricSpace H (@NormedAddCommGroup.toSeminormedAddCommGroup H inst))))
              (@AddCommGroup.toAddCommMonoid H (@NormedAddCommGroup.toAddCommGroup H inst)) H
              (@UniformSpace.toTopologicalSpace H
                (@PseudoMetricSpace.toUniformSpace H
                  (@SeminormedAddCommGroup.toPseudoMetricSpace H (@NormedAddCommGroup.toSeminormedAddCommGroup H inst))))
              (@AddCommGroup.toAddCommMonoid H (@NormedAddCommGroup.toAddCommGroup H inst))
              (@NormedSpace.toModule Complex H Complex.instNormedField (@NormedAddCommGroup.toSeminormedAddCommGroup H inst)
                (@InnerProductSpace.toNormedSpace Complex H Complex.instRCLike
                  (@NormedAddCommGroup.toSeminormedAddCommGroup H inst) inst_1))
              (@NormedSpace.toModule Complex H Complex.instNormedField (@NormedAddCommGroup.toSeminormedAddCommGroup H inst)
                (@InnerProductSpace.toNormedSpace Complex H Complex.instRCLike
                  (@NormedAddCommGroup.toSeminormedAddCommGroup H inst) inst_1)))
        (Λ : Fin n → Real)
        (S :
          @Submodule Complex H Complex.instSemiring
            (@AddCommGroup.toAddCommMonoid H (@NormedAddCommGroup.toAddCommGroup H inst))
            (@NormedSpace.toModule Complex H Complex.instNormedField (@NormedAddCommGroup.toSeminormedAddCommGroup H inst)
              (@InnerProductSpace.toNormedSpace Complex H Complex.instRCLike
                (@NormedAddCommGroup.toSeminormedAddCommGroup H inst) inst_1))) ↦
      And
        (@FiniteDimensional Complex (↥S) (@Field.toDivisionRing Complex Complex.instField)
          (@Submodule.addCommGroup Complex H Complex.instRing (@NormedAddCommGroup.toAddCommGroup H inst)
            (@NormedSpace.toModule Complex H Complex.instNormedField (@NormedAddCommGroup.toSeminormedAddCommGroup H inst)
              (@InnerProductSpace.toNormedSpace Complex H Complex.instRCLike
                (@NormedAddCommGroup.toSeminormedAddCommGroup H inst) inst_1))
            S)
          (@Submodule.module Complex H Complex.instSemiring
            (@AddCommGroup.toAddCommMonoid H (@NormedAddCommGroup.toAddCommGroup H inst))
            (@NormedSpace.toModule Complex H Complex.instNormedField (@NormedAddCommGroup.toSeminormedAddCommGroup H inst)
              (@InnerProductSpace.toNormedSpace Complex H Complex.instRCLike
                (@NormedAddCommGroup.toSeminormedAddCommGroup H inst) inst_1))
            S))
        (And (@UpperTheory.Reformulated.B.Re4.IsKStableOn n H inst inst_1 ε σ S)
          (And
            (∀
              (S' :
                @Submodule Complex H Complex.instSemiring
                  (@AddCommGroup.toAddCommMonoid H (@NormedAddCommGroup.toAddCommGroup H inst))
                  (@NormedSpace.toModule Complex H Complex.instNormedField
                    (@NormedAddCommGroup.toSeminormedAddCommGroup H inst)
                    (@InnerProductSpace.toNormedSpace Complex H Complex.instRCLike
                      (@NormedAddCommGroup.toSeminormedAddCommGroup H inst) inst_1))),
              @LE.le
                  (@Submodule Complex H Complex.instSemiring
                    (@AddCommGroup.toAddCommMonoid H (@NormedAddCommGroup.toAddCommGroup H inst))
                    (@NormedSpace.toModule Complex H Complex.instNormedField
                      (@NormedAddCommGroup.toSeminormedAddCommGroup H inst)
                      (@InnerProductSpace.toNormedSpace Complex H Complex.instRCLike
                        (@NormedAddCommGroup.toSeminormedAddCommGroup H inst) inst_1)))
                  (@Preorder.toLE
                    (@Submodule Complex H Complex.instSemiring
                      (@AddCommGroup.toAddCommMonoid H (@NormedAddCommGroup.toAddCommGroup H inst))
                      (@NormedSpace.toModule Complex H Complex.instNormedField
                        (@NormedAddCommGroup.toSeminormedAddCommGroup H inst)
                        (@InnerProductSpace.toNormedSpace Complex H Complex.instRCLike
                          (@NormedAddCommGroup.toSeminormedAddCommGroup H inst) inst_1)))
                    (@PartialOrder.toPreorder
                      (@Submodule Complex H Complex.instSemiring
                        (@AddCommGroup.toAddCommMonoid H (@NormedAddCommGroup.toAddCommGroup H inst))
                        (@NormedSpace.toModule Complex H Complex.instNormedField
                          (@NormedAddCommGroup.toSeminormedAddCommGroup H inst)
                          (@InnerProductSpace.toNormedSpace Complex H Complex.instRCLike
                            (@NormedAddCommGroup.toSeminormedAddCommGroup H inst) inst_1)))
                      (@Submodule.instPartialOrder Complex H Complex.instSemiring
                        (@AddCommGroup.toAddCommMonoid H (@NormedAddCommGroup.toAddCommGroup H inst))
                        (@NormedSpace.toModule Complex H Complex.instNormedField
                          (@NormedAddCommGroup.toSeminormedAddCommGroup H inst)
                          (@InnerProductSpace.toNormedSpace Complex H Complex.instRCLike
                            (@NormedAddCommGroup.toSeminormedAddCommGroup H inst) inst_1)))))
                  S' S →
                @UpperTheory.Reformulated.B.Re4.IsKStableOn n H inst inst_1 ε σ S' →
                  Or
                    (@Eq
                      (@Submodule Complex H Complex.instSemiring
                        (@AddCommGroup.toAddCommMonoid H (@NormedAddCommGroup.toAddCommGroup H inst))
                        (@NormedSpace.toModule Complex H Complex.instNormedField
                          (@NormedAddCommGroup.toSeminormedAddCommGroup H inst)
                          (@InnerProductSpace.toNormedSpace Complex H Complex.instRCLike
                            (@NormedAddCommGroup.toSeminormedAddCommGroup H inst) inst_1)))
                      S'
                      (@Bot.bot
                        (@Submodule Complex H Complex.instSemiring
                          (@AddCommGroup.toAddCommMonoid H (@NormedAddCommGroup.toAddCommGroup H inst))
                          (@NormedSpace.toModule Complex H Complex.instNormedField
                            (@NormedAddCommGroup.toSeminormedAddCommGroup H inst)
                            (@InnerProductSpace.toNormedSpace Complex H Complex.instRCLike
                              (@NormedAddCommGroup.toSeminormedAddCommGroup H inst) inst_1)))
                        (@Submodule.instBot Complex H Complex.instSemiring
                          (@AddCommGroup.toAddCommMonoid H (@NormedAddCommGroup.toAddCommGroup H inst))
                          (@NormedSpace.toModule Complex H Complex.instNormedField
                            (@NormedAddCommGroup.toSeminormedAddCommGroup H inst)
                            (@InnerProductSpace.toNormedSpace Complex H Complex.instRCLike
                              (@NormedAddCommGroup.toSeminormedAddCommGroup H inst) inst_1)))))
                    (@Eq
                      (@Submodule Complex H Complex.instSemiring
                        (@AddCommGroup.toAddCommMonoid H (@NormedAddCommGroup.toAddCommGroup H inst))
                        (@NormedSpace.toModule Complex H Complex.instNormedField
                          (@NormedAddCommGroup.toSeminormedAddCommGroup H inst)
                          (@InnerProductSpace.toNormedSpace Complex H Complex.instRCLike
                            (@NormedAddCommGroup.toSeminormedAddCommGroup H inst) inst_1)))
                      S' S))
            (And
              (∃ (v : H),
                And
                  (@Membership.mem H
                    (@Submodule Complex H Complex.instSemiring
                      (@AddCommGroup.toAddCommMonoid H (@NormedAddCommGroup.toAddCommGroup H inst))
                      (@NormedSpace.toModule Complex H Complex.instNormedField
                        (@NormedAddCommGroup.toSeminormedAddCommGroup H inst)
                        (@InnerProductSpace.toNormedSpace Complex H Complex.instRCLike
                          (@NormedAddCommGroup.toSeminormedAddCommGroup H inst) inst_1)))
                    (@SetLike.instMembership
                      (@Submodule Complex H Complex.instSemiring
                        (@AddCommGroup.toAddCommMonoid H (@NormedAddCommGroup.toAddCommGroup H inst))
                        (@NormedSpace.toModule Complex H Complex.instNormedField
                          (@NormedAddCommGroup.toSeminormedAddCommGroup H inst)
                          (@InnerProductSpace.toNormedSpace Complex H Complex.instRCLike
                            (@NormedAddCommGroup.toSeminormedAddCommGroup H inst) inst_1)))
                      H
                      (@Submodule.setLike Complex H Complex.instSemiring
                        (@AddCommGroup.toAddCommMonoid H (@NormedAddCommGroup.toAddCommGroup H inst))
                        (@NormedSpace.toModule Complex H Complex.instNormedField
                          (@NormedAddCommGroup.toSeminormedAddCommGroup H inst)
                          (@InnerProductSpace.toNormedSpace Complex H Complex.instRCLike
                            (@NormedAddCommGroup.toSeminormedAddCommGroup H inst) inst_1))))
                    S v)
                  (And
                    (@Ne H v
                      (@OfNat.ofNat H (nat_lit 0)
                        (@Zero.toOfNat0 H
                          (@NegZeroClass.toZero H
                            (@SubNegZeroMonoid.toNegZeroClass H
                              (@SubtractionMonoid.toSubNegZeroMonoid H
                                (@SubtractionCommMonoid.toSubtractionMonoid H
                                  (@AddCommGroup.toDivisionAddCommMonoid H
                                    (@NormedAddCommGroup.toAddCommGroup H inst)))))))))
                    (@UpperTheory.Reformulated.B.Re4.IsWtOn n H inst inst_1 (@UpperTheory.Reformulated.B.Re4.d21 n ε) σ Λ v)))
              (∀ (μ : Fin n → Real) (v : H),
                @Membership.mem H
                    (@Submodule Complex H Complex.instSemiring
                      (@AddCommGroup.toAddCommMonoid H (@NormedAddCommGroup.toAddCommGroup H inst))
                      (@NormedSpace.toModule Complex H Complex.instNormedField
                        (@NormedAddCommGroup.toSeminormedAddCommGroup H inst)
                        (@InnerProductSpace.toNormedSpace Complex H Complex.instRCLike
                          (@NormedAddCommGroup.toSeminormedAddCommGroup H inst) inst_1)))
                    (@SetLike.instMembership
                      (@Submodule Complex H Complex.instSemiring
                        (@AddCommGroup.toAddCommMonoid H (@NormedAddCommGroup.toAddCommGroup H inst))
                        (@NormedSpace.toModule Complex H Complex.instNormedField
                          (@NormedAddCommGroup.toSeminormedAddCommGroup H inst)
                          (@InnerProductSpace.toNormedSpace Complex H Complex.instRCLike
                            (@NormedAddCommGroup.toSeminormedAddCommGroup H inst) inst_1)))
                      H
                      (@Submodule.setLike Complex H Complex.instSemiring
                        (@AddCommGroup.toAddCommMonoid H (@NormedAddCommGroup.toAddCommGroup H inst))
                        (@NormedSpace.toModule Complex H Complex.instNormedField
                          (@NormedAddCommGroup.toSeminormedAddCommGroup H inst)
                          (@InnerProductSpace.toNormedSpace Complex H Complex.instRCLike
                            (@NormedAddCommGroup.toSeminormedAddCommGroup H inst) inst_1))))
                    S v →
                  @Ne H v
                      (@OfNat.ofNat H (nat_lit 0)
                        (@Zero.toOfNat0 H
                          (@NegZeroClass.toZero H
                            (@SubNegZeroMonoid.toNegZeroClass H
                              (@SubtractionMonoid.toSubNegZeroMonoid H
                                (@SubtractionCommMonoid.toSubtractionMonoid H
                                  (@AddCommGroup.toDivisionAddCommMonoid H
                                    (@NormedAddCommGroup.toAddCommGroup H inst)))))))) →
                    @UpperTheory.Reformulated.B.Re4.IsWtOn n H inst inst_1 (@UpperTheory.Reformulated.B.Re4.d21 n ε) σ μ v →
                      @UpperTheory.Reformulated.B.Re4.CDom n ε μ Λ))))


