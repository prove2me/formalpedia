-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_PlaceRankTwoOne
-- name    : Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_PlaceRankTwoOne
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:08:10.462806+00:00
-- url     : https://prove2.me/theorems/19450237-ae44-43cc-94f3-75589a89a997
-- title:
--   Place Rank Two One
-- statement:
--   Definitions and structural lemmas for Place Rank Two One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/PlaceRankTwoOne.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable def UpperTheory.Reformulated.B.placeRankTwoOne.Jm :
    {n : Nat} → (Fin n → Bool) → Matrix (Fin n) (Fin n) Complex :=
    fun {n : Nat} (ε : Fin n → Bool) ↦
      @Matrix.diagonal (Fin n) Complex (instDecidableEqFin n) Complex.instZero fun (a : Fin n) ↦
        @ite Complex (@Eq Bool (ε a) Bool.true) (instDecidableEqBool (ε a) Bool.true)
          (@OfNat.ofNat Complex (nat_lit 1) (@One.toOfNat1 Complex Complex.instOne))
          (@Neg.neg Complex Complex.instNeg (@OfNat.ofNat Complex (nat_lit 1) (@One.toOfNat1 Complex Complex.instOne)))
noncomputable def UpperTheory.Reformulated.B.placeRankTwoOne.inUJ :
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
            (@UpperTheory.Reformulated.B.placeRankTwoOne.Jm n ε))
          g)
        (@UpperTheory.Reformulated.B.placeRankTwoOne.Jm n ε)
theorem UpperTheory.Reformulated.B.placeRankTwoOne.aux3 :
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
            @UpperTheory.Reformulated.B.placeRankTwoOne.inUJ n ε
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
              @UpperTheory.Reformulated.B.placeRankTwoOne.inUJ n ε
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
              @UpperTheory.Reformulated.B.placeRankTwoOne.inUJ n ε
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
  have hg' : g.val.conjTranspose * Jm ε * g.val = Jm ε := hg
  have hh' : h.val.conjTranspose * Jm ε * h.val = Jm ε := hh
  change (g.val * h.val).conjTranspose * Jm ε * (g.val * h.val) = Jm ε
  calc (g.val * h.val).conjTranspose * Jm ε * (g.val * h.val)
      = h.val.conjTranspose * (g.val.conjTranspose * Jm ε * g.val) * h.val := by
        simp only [Matrix.conjTranspose_mul, mul_assoc]
    _ = Jm ε := by rw [hg', hh']
theorem UpperTheory.Reformulated.B.placeRankTwoOne.aux4 :
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
            (@UpperTheory.Reformulated.B.placeRankTwoOne.Jm n ε))
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
        (@UpperTheory.Reformulated.B.placeRankTwoOne.Jm n ε) := by
  intro n ε
  change (1 : Matrix (Fin n) (Fin n) ℂ).conjTranspose * Jm ε * 1 = Jm ε
  simp
theorem UpperTheory.Reformulated.B.placeRankTwoOne.aux5 :
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
            @UpperTheory.Reformulated.B.placeRankTwoOne.inUJ n ε
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
            @UpperTheory.Reformulated.B.placeRankTwoOne.inUJ n ε
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
  have hg' : g.val.conjTranspose * Jm ε * g.val = Jm ε := hg
  change (g⁻¹).val.conjTranspose * Jm ε * (g⁻¹).val = Jm ε
  calc (g⁻¹).val.conjTranspose * Jm ε * (g⁻¹).val
      = (g⁻¹).val.conjTranspose * (g.val.conjTranspose * Jm ε * g.val) * (g⁻¹).val := by rw [hg']
    _ = (g.val * (g⁻¹).val).conjTranspose * Jm ε * (g.val * (g⁻¹).val) := by
        simp only [Matrix.conjTranspose_mul, mul_assoc]
    _ = Jm ε := by rw [Units.mul_inv]; simp
noncomputable def UpperTheory.Reformulated.B.placeRankTwoOne.UJ :
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
              @UpperTheory.Reformulated.B.placeRankTwoOne.inUJ n ε
                (@Units.val (Matrix (Fin n) (Fin n) Complex)
                  (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
                    (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n)))
                  g))
            (@UpperTheory.Reformulated.B.placeRankTwoOne.aux3 n ε))
          (@UpperTheory.Reformulated.B.placeRankTwoOne.aux4 n ε))
        (@UpperTheory.Reformulated.B.placeRankTwoOne.aux5 n ε)
@[reducible] noncomputable def UpperTheory.Reformulated.B.placeRankTwoOne.instMeasurableSpaceUJ :
    (n : Nat) → (ε : Fin n → Bool) → MeasurableSpace ↥(@UpperTheory.Reformulated.B.placeRankTwoOne.UJ n ε) :=
    fun (n : Nat) (ε : Fin n → Bool) ↦
      @borel (↥(@UpperTheory.Reformulated.B.placeRankTwoOne.UJ n ε))
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
              (@UpperTheory.Reformulated.B.placeRankTwoOne.UJ n ε) x)
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
attribute [local instance] UpperTheory.Reformulated.B.placeRankTwoOne.instMeasurableSpaceUJ
theorem UpperTheory.Reformulated.B.placeRankTwoOne.aux8 :
    ∀ {n : Nat} (ε : Fin n → Bool),
      @IsTopologicalGroup (↥(@UpperTheory.Reformulated.B.placeRankTwoOne.UJ n ε))
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
              (@UpperTheory.Reformulated.B.placeRankTwoOne.UJ n ε) x)
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
          (@UpperTheory.Reformulated.B.placeRankTwoOne.UJ n ε)) := by
  intro n ε
  infer_instance
theorem UpperTheory.Reformulated.B.placeRankTwoOne.aux9 :
    ∀ (n : Nat) (ε : Fin n → Bool),
      @BorelSpace (↥(@UpperTheory.Reformulated.B.placeRankTwoOne.UJ n ε))
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
              (@UpperTheory.Reformulated.B.placeRankTwoOne.UJ n ε) x)
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
        (UpperTheory.Reformulated.B.placeRankTwoOne.instMeasurableSpaceUJ n ε) := by
  intro n ε
  exact ⟨rfl⟩
section JLemmas
open Matrix
end JLemmas
theorem UpperTheory.Reformulated.B.placeRankTwoOne.isClosed_UJ {n : ℕ} (ε : Fin n → Bool) :
    IsClosed (UJ ε : Set (Matrix (Fin n) (Fin n) ℂ)ˣ) :=
  isClosed_eq (f := fun g : (Matrix (Fin n) (Fin n) ℂ)ˣ => g.val.conjTranspose * Jm ε * g.val)
    ((Units.continuous_val.matrix_conjTranspose.mul continuous_const).mul Units.continuous_val)
    continuous_const
theorem UpperTheory.Reformulated.B.placeRankTwoOne.laurent_T_neg_one_mul_T_one :
    ∀ (n : Nat) (ε : Fin n → Bool),
      @LocallyCompactSpace (↥(@UpperTheory.Reformulated.B.placeRankTwoOne.UJ n ε))
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
              (@UpperTheory.Reformulated.B.placeRankTwoOne.UJ n ε) x)
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
  exact (isClosed_UJ ε).locallyCompactSpace
noncomputable def UpperTheory.Reformulated.B.placeRankTwoOne.muG :
    {n : Nat} →
      (ε : Fin n → Bool) → @MeasureTheory.Measure (↥(@UpperTheory.Reformulated.B.placeRankTwoOne.UJ n ε)) (UpperTheory.Reformulated.B.placeRankTwoOne.instMeasurableSpaceUJ n ε) :=
    fun {n : Nat} (ε : Fin n → Bool) ↦
      @MeasureTheory.Measure.haar (↥(@UpperTheory.Reformulated.B.placeRankTwoOne.UJ n ε))
        (@Subgroup.toGroup
          (@Units (Matrix (Fin n) (Fin n) Complex)
            (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
              (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
          (@Units.instGroup (Matrix (Fin n) (Fin n) Complex)
            (@Semiring.toMonoid (Matrix (Fin n) (Fin n) Complex)
              (@Matrix.semiring (Fin n) Complex Complex.instSemiring (Fin.fintype n) (instDecidableEqFin n))))
          (@UpperTheory.Reformulated.B.placeRankTwoOne.UJ n ε))
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
              (@UpperTheory.Reformulated.B.placeRankTwoOne.UJ n ε) x)
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
        (@UpperTheory.Reformulated.B.placeRankTwoOne.aux8 n ε) (UpperTheory.Reformulated.B.placeRankTwoOne.instMeasurableSpaceUJ n ε) (UpperTheory.Reformulated.B.placeRankTwoOne.aux9 n ε)
        (UpperTheory.Reformulated.B.placeRankTwoOne.laurent_T_neg_one_mul_T_one n ε)
noncomputable def UpperTheory.Reformulated.B.placeRankTwoOne.hs :
    {n : Nat} → Matrix (Fin n) (Fin n) Complex → Real :=
    fun {n : Nat} (g : Matrix (Fin n) (Fin n) Complex) ↦
      ∑ i : Fin n,
        ∑ j : Fin n,
          @HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid)))
            (@Norm.norm Complex Complex.instNorm (g i j)) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
noncomputable def UpperTheory.Reformulated.B.placeRankTwoOne.hsG :
    {n : Nat} → {ε : Fin n → Bool} → ↥(@UpperTheory.Reformulated.B.placeRankTwoOne.UJ n ε) → Real :=
    fun {n : Nat} {ε : Fin n → Bool} (g : ↥(@UpperTheory.Reformulated.B.placeRankTwoOne.UJ n ε)) ↦
      @UpperTheory.Reformulated.B.placeRankTwoOne.hs n
        (@Units.val (Matrix (Fin n) (Fin n) Complex)
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
                (@UpperTheory.Reformulated.B.placeRankTwoOne.UJ n ε) x)
            g))
noncomputable def UpperTheory.Reformulated.B.placeRankTwoOne.VolGrowth :
    Prop :=
    ∀ (n : Nat) (ε : Fin n → Bool),
      ∃ (C : Real),
        ∀ (R : Real),
          @LE.le Real Real.instLE (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne)) R →
            @LE.le ENNReal ENNReal.instLE
              (@DFunLike.coe
                (@MeasureTheory.Measure (↥(@UpperTheory.Reformulated.B.placeRankTwoOne.UJ n ε)) (UpperTheory.Reformulated.B.placeRankTwoOne.instMeasurableSpaceUJ n ε))
                (Set ↥(@UpperTheory.Reformulated.B.placeRankTwoOne.UJ n ε)) (fun (x : Set ↥(@UpperTheory.Reformulated.B.placeRankTwoOne.UJ n ε)) ↦ ENNReal)
                (@MeasureTheory.Measure.instFunLike (↥(@UpperTheory.Reformulated.B.placeRankTwoOne.UJ n ε))
                  (UpperTheory.Reformulated.B.placeRankTwoOne.instMeasurableSpaceUJ n ε))
                (@UpperTheory.Reformulated.B.placeRankTwoOne.muG n ε)
                (@Set.ofPred ↥(@UpperTheory.Reformulated.B.placeRankTwoOne.UJ n ε) fun (g : ↥(@UpperTheory.Reformulated.B.placeRankTwoOne.UJ n ε)) ↦
                  @LE.le Real Real.instLE (@UpperTheory.Reformulated.B.placeRankTwoOne.hsG n ε g)
                    (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid)))
                      R (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
              (ENNReal.ofReal
                (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) C
                  (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) R
                    (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                      (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                      (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) n
                        (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))
section Helpers
open MeasureTheory Matrix
def UpperTheory.Reformulated.B.placeRankTwoOne.act {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → Fin n → ℂ) :
    Fin n → Fin n → ℂ := fun j => g *ᵥ x j
end Helpers


