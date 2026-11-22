-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_InvolutionInvariants
-- name    : Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_InvolutionInvariants
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T16:46:04.925006+00:00
-- url     : https://prove2.me/theorems/6a2e1cdd-7080-4929-b627-3af86e74c670
-- title:
--   Involution Invariants
-- statement:
--   Definitions and structural lemmas for Involution Invariants, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/InvolutionInvariants.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable def UpperTheory.Reformulated.B.InvolutionInvariants.Jm :
    {n : Nat} → (Fin n → Bool) → Matrix (Fin n) (Fin n) Complex :=
    fun {n : Nat} (ε : Fin n → Bool) ↦
      @Matrix.diagonal (Fin n) Complex (instDecidableEqFin n) Complex.instZero fun (a : Fin n) ↦
        @ite Complex (@Eq Bool (ε a) Bool.true) (instDecidableEqBool (ε a) Bool.true)
          (@OfNat.ofNat Complex (nat_lit 1) (@One.toOfNat1 Complex Complex.instOne))
          (@Neg.neg Complex Complex.instNeg (@OfNat.ofNat Complex (nat_lit 1) (@One.toOfNat1 Complex Complex.instOne)))
noncomputable def UpperTheory.Reformulated.B.InvolutionInvariants.inUJ :
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
            (@UpperTheory.Reformulated.B.InvolutionInvariants.Jm n ε))
          g)
        (@UpperTheory.Reformulated.B.InvolutionInvariants.Jm n ε)
theorem UpperTheory.Reformulated.B.InvolutionInvariants.aux3 :
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
            @UpperTheory.Reformulated.B.InvolutionInvariants.inUJ n ε
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
              @UpperTheory.Reformulated.B.InvolutionInvariants.inUJ n ε
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
              @UpperTheory.Reformulated.B.InvolutionInvariants.inUJ n ε
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
  change UpperTheory.Reformulated.B.InvolutionInvariants.inUJ ε _ at hg hh ⊢
  unfold UpperTheory.Reformulated.B.InvolutionInvariants.inUJ at hg hh ⊢
  rw [Units.val_mul, Matrix.conjTranspose_mul]
  calc _ = (h.val).conjTranspose * ((g.val).conjTranspose * UpperTheory.Reformulated.B.InvolutionInvariants.Jm ε * g.val) * h.val := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [hg, hh]
theorem UpperTheory.Reformulated.B.InvolutionInvariants.aux4 :
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
            (@UpperTheory.Reformulated.B.InvolutionInvariants.Jm n ε))
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
        (@UpperTheory.Reformulated.B.InvolutionInvariants.Jm n ε) := by
  intro n ε
  simp
theorem UpperTheory.Reformulated.B.InvolutionInvariants.aux5 :
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
            @UpperTheory.Reformulated.B.InvolutionInvariants.inUJ n ε
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
            @UpperTheory.Reformulated.B.InvolutionInvariants.inUJ n ε
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
  change UpperTheory.Reformulated.B.InvolutionInvariants.inUJ ε _ at hg ⊢
  unfold UpperTheory.Reformulated.B.InvolutionInvariants.inUJ at hg ⊢
  have h1 : g.val * (g⁻¹).val = 1 := Units.mul_inv g
  calc _ = ((g⁻¹).val).conjTranspose * ((g.val).conjTranspose * UpperTheory.Reformulated.B.InvolutionInvariants.Jm ε * g.val)
          * (g⁻¹).val := by rw [hg]
    _ = (g.val * (g⁻¹).val).conjTranspose * UpperTheory.Reformulated.B.InvolutionInvariants.Jm ε * (g.val * (g⁻¹).val) := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = _ := by rw [h1, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
noncomputable def UpperTheory.Reformulated.B.InvolutionInvariants.UJ :
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
              @UpperTheory.Reformulated.B.InvolutionInvariants.inUJ n ε
                (@Units.val (Matrix (Fin n) (Fin n) Complex)
                  (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                    (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n)))
                  g))
            (@UpperTheory.Reformulated.B.InvolutionInvariants.aux3 n ε))
          (@UpperTheory.Reformulated.B.InvolutionInvariants.aux4 n ε))
        (@UpperTheory.Reformulated.B.InvolutionInvariants.aux5 n ε)
@[reducible] noncomputable def UpperTheory.Reformulated.B.InvolutionInvariants.instMeasurableSpaceUJ :
    (n : Nat) → (ε : Fin n → Bool) → MeasurableSpace ↥(@UpperTheory.Reformulated.B.InvolutionInvariants.UJ n ε) :=
    fun (n : Nat) (ε : Fin n → Bool) ↦
      @borel (↥(@UpperTheory.Reformulated.B.InvolutionInvariants.UJ n ε))
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
              (@UpperTheory.Reformulated.B.InvolutionInvariants.UJ n ε) x)
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
attribute [local instance] UpperTheory.Reformulated.B.InvolutionInvariants.instMeasurableSpaceUJ
theorem UpperTheory.Reformulated.B.InvolutionInvariants.aux8 :
    ∀ {n : Nat} (ε : Fin n → Bool),
      @IsTopologicalGroup (↥(@UpperTheory.Reformulated.B.InvolutionInvariants.UJ n ε))
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
              (@UpperTheory.Reformulated.B.InvolutionInvariants.UJ n ε) x)
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
          (@UpperTheory.Reformulated.B.InvolutionInvariants.UJ n ε)) := by
  intro n ε
  infer_instance
theorem UpperTheory.Reformulated.B.InvolutionInvariants.aux9 :
    ∀ (n : Nat) (ε : Fin n → Bool),
      @BorelSpace (↥(@UpperTheory.Reformulated.B.InvolutionInvariants.UJ n ε))
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
              (@UpperTheory.Reformulated.B.InvolutionInvariants.UJ n ε) x)
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
        (UpperTheory.Reformulated.B.InvolutionInvariants.instMeasurableSpaceUJ n ε) := by
  intro n ε
  exact ⟨rfl⟩
theorem UpperTheory.Reformulated.B.InvolutionInvariants.laurent_T_neg_one_mul_T_one :
    ∀ (n : Nat) (ε : Fin n → Bool),
      @LocallyCompactSpace (↥(@UpperTheory.Reformulated.B.InvolutionInvariants.UJ n ε))
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
              (@UpperTheory.Reformulated.B.InvolutionInvariants.UJ n ε) x)
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
  have hc : IsClosed {g : (Matrix (Fin n) (Fin n) ℂ)ˣ |
      (g.val).conjTranspose * UpperTheory.Reformulated.B.InvolutionInvariants.Jm ε * g.val = UpperTheory.Reformulated.B.InvolutionInvariants.Jm ε} :=
    isClosed_eq ((Units.continuous_val.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul
      Units.continuous_val) continuous_const
  exact hc.locallyCompactSpace
noncomputable def UpperTheory.Reformulated.B.InvolutionInvariants.muG :
    {n : Nat} →
      (ε : Fin n → Bool) → @MeasureTheory.Measure (↥(@UpperTheory.Reformulated.B.InvolutionInvariants.UJ n ε)) (UpperTheory.Reformulated.B.InvolutionInvariants.instMeasurableSpaceUJ n ε) :=
    fun {n : Nat} (ε : Fin n → Bool) ↦
      @MeasureTheory.Measure.haar (↥(@UpperTheory.Reformulated.B.InvolutionInvariants.UJ n ε))
        (@Subgroup.toGroup
          (@Units (Matrix (Fin n) (Fin n) Complex)
            (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
              (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
          (@Units.instGroup (Matrix (Fin n) (Fin n) Complex)
            (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
              (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
          (@UpperTheory.Reformulated.B.InvolutionInvariants.UJ n ε))
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
              (@UpperTheory.Reformulated.B.InvolutionInvariants.UJ n ε) x)
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
        (@UpperTheory.Reformulated.B.InvolutionInvariants.aux8 n ε) (UpperTheory.Reformulated.B.InvolutionInvariants.instMeasurableSpaceUJ n ε) (UpperTheory.Reformulated.B.InvolutionInvariants.aux9 n ε)
        (UpperTheory.Reformulated.B.InvolutionInvariants.laurent_T_neg_one_mul_T_one n ε)
noncomputable def UpperTheory.Reformulated.B.InvolutionInvariants.Unimodular :
    Prop :=
    ∀ (n : Nat) (ε : Fin n → Bool) (g : ↥(@UpperTheory.Reformulated.B.InvolutionInvariants.UJ n ε)),
      @Eq (@MeasureTheory.Measure (↥(@UpperTheory.Reformulated.B.InvolutionInvariants.UJ n ε)) (UpperTheory.Reformulated.B.InvolutionInvariants.instMeasurableSpaceUJ n ε))
        (@MeasureTheory.Measure.map (↥(@UpperTheory.Reformulated.B.InvolutionInvariants.UJ n ε)) (↥(@UpperTheory.Reformulated.B.InvolutionInvariants.UJ n ε))
          (UpperTheory.Reformulated.B.InvolutionInvariants.instMeasurableSpaceUJ n ε) (UpperTheory.Reformulated.B.InvolutionInvariants.instMeasurableSpaceUJ n ε)
          (fun (x : ↥(@UpperTheory.Reformulated.B.InvolutionInvariants.UJ n ε)) ↦
            @HMul.hMul (↥(@UpperTheory.Reformulated.B.InvolutionInvariants.UJ n ε)) (↥(@UpperTheory.Reformulated.B.InvolutionInvariants.UJ n ε)) (↥(@UpperTheory.Reformulated.B.InvolutionInvariants.UJ n ε))
              (@instHMul (↥(@UpperTheory.Reformulated.B.InvolutionInvariants.UJ n ε))
                (@Subgroup.mul
                  (@Units (Matrix (Fin n) (Fin n) Complex)
                    (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                      (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
                  (@Units.instGroup (Matrix (Fin n) (Fin n) Complex)
                    (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                      (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
                  (@UpperTheory.Reformulated.B.InvolutionInvariants.UJ n ε)))
              x g)
          (@UpperTheory.Reformulated.B.InvolutionInvariants.muG n ε))
        (@UpperTheory.Reformulated.B.InvolutionInvariants.muG n ε)
noncomputable def UpperTheory.Reformulated.B.InvolutionInvariants.InvInvariant :
    Prop :=
    ∀ (n : Nat) (ε : Fin n → Bool),
      @Eq (@MeasureTheory.Measure (↥(@UpperTheory.Reformulated.B.InvolutionInvariants.UJ n ε)) (UpperTheory.Reformulated.B.InvolutionInvariants.instMeasurableSpaceUJ n ε))
        (@MeasureTheory.Measure.map (↥(@UpperTheory.Reformulated.B.InvolutionInvariants.UJ n ε)) (↥(@UpperTheory.Reformulated.B.InvolutionInvariants.UJ n ε))
          (UpperTheory.Reformulated.B.InvolutionInvariants.instMeasurableSpaceUJ n ε) (UpperTheory.Reformulated.B.InvolutionInvariants.instMeasurableSpaceUJ n ε)
          (fun (x : ↥(@UpperTheory.Reformulated.B.InvolutionInvariants.UJ n ε)) ↦
            @Inv.inv (↥(@UpperTheory.Reformulated.B.InvolutionInvariants.UJ n ε))
              (@Subgroup.inv
                (@Units (Matrix (Fin n) (Fin n) Complex)
                  (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                    (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
                (@Units.instGroup (Matrix (Fin n) (Fin n) Complex)
                  (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                    (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
                (@UpperTheory.Reformulated.B.InvolutionInvariants.UJ n ε))
              x)
          (@UpperTheory.Reformulated.B.InvolutionInvariants.muG n ε))
        (@UpperTheory.Reformulated.B.InvolutionInvariants.muG n ε)


