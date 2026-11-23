-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_StandardLattice
-- name    : Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_StandardLattice
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:38:35.415942+00:00
-- url     : https://prove2.me/theorems/2a030ead-a143-46d5-abba-7bebe431daa4
-- title:
--   Standard Lattice
-- statement:
--   Definitions and structural lemmas for Standard Lattice, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/StandardLattice.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable def UpperTheory.Reformulated.B.StandardLattice.pZ :
    Nat → @Ideal Int Int.instSemiring :=
    fun (l : Nat) ↦
      @Ideal.span Int Int.instSemiring
        (@Singleton.singleton Int (Set Int) (@Set.instSingletonSet Int) (@Nat.cast Int instNatCastInt l))
theorem UpperTheory.Reformulated.B.StandardLattice.aux2 :
    ∀ (l : Nat) [hl : Fact (Nat.Prime l)], @Ideal.IsPrime Int Int.instSemiring (UpperTheory.Reformulated.B.StandardLattice.pZ l) := by
  intro l hl
  have hp : Prime (l : ℤ) := Nat.prime_iff_prime_int.mp hl.out
  exact (Ideal.span_singleton_prime hp.ne_zero).mpr hp
@[reducible] noncomputable def UpperTheory.Reformulated.B.StandardLattice.Ml :
    (l : Nat) →
      [hl : Fact (Nat.Prime l)] →
        (K : Type) →
          [inst : Field K] →
            @Submonoid (@NumberField.RingOfIntegers K inst)
              (@MulZeroOneClass.toMulOneClass (@NumberField.RingOfIntegers K inst)
                (@instMulZeroOneClassOfSemiring (@NumberField.RingOfIntegers K inst)
                  (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
                    (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                      (@NumberField.instCommRingRingOfIntegers K inst))))) :=
    fun (l : Nat) [hl : Fact (Nat.Prime l)] (K : Type) [inst : Field K] ↦
      @Algebra.algebraMapSubmonoid Int Int.instCommSemiring (@NumberField.RingOfIntegers K inst)
        (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
          (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst) (@NumberField.instCommRingRingOfIntegers K inst)))
        (@Ring.toIntAlgebra (@NumberField.RingOfIntegers K inst)
          (@CommRing.toRing (@NumberField.RingOfIntegers K inst) (@NumberField.instCommRingRingOfIntegers K inst)))
        (@Ideal.primeCompl Int Int.instSemiring (UpperTheory.Reformulated.B.StandardLattice.pZ l) (@UpperTheory.Reformulated.B.StandardLattice.aux2 l hl))
@[reducible] noncomputable def UpperTheory.Reformulated.B.StandardLattice.Rl :
    (l : Nat) → [hl : Fact (Nat.Prime l)] → (K : Type) → [Field K] → Type :=
    fun (l : Nat) [hl : Fact (Nat.Prime l)] (K : Type) [inst : Field K] ↦
      @Localization (@NumberField.RingOfIntegers K inst)
        (@CommRing.toCommMonoid (@NumberField.RingOfIntegers K inst) (@NumberField.instCommRingRingOfIntegers K inst))
        (@UpperTheory.Reformulated.B.StandardLattice.Ml l hl K inst)
theorem UpperTheory.Reformulated.B.StandardLattice.aux5 :
    ∀ (l : Nat) [hl : Fact (Nat.Prime l)] (K : Type) [inst : Field K],
      @IsLocalization (@NumberField.RingOfIntegers K inst)
        (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst) (@NumberField.instCommRingRingOfIntegers K inst))
        (@UpperTheory.Reformulated.B.StandardLattice.Ml l hl K inst)
        (@Localization (@NumberField.RingOfIntegers K inst)
          (@CommSemiring.toCommMonoid (@NumberField.RingOfIntegers K inst)
            (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
              (@NumberField.instCommRingRingOfIntegers K inst)))
          (@UpperTheory.Reformulated.B.StandardLattice.Ml l hl K inst))
        (@OreLocalization.instCommSemiring (@NumberField.RingOfIntegers K inst)
          (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst) (@NumberField.instCommRingRingOfIntegers K inst))
          (@UpperTheory.Reformulated.B.StandardLattice.Ml l hl K inst)
          (@OreLocalization.oreSetComm (@NumberField.RingOfIntegers K inst)
            (@CommSemiring.toCommMonoid (@NumberField.RingOfIntegers K inst)
              (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                (@NumberField.instCommRingRingOfIntegers K inst)))
            (@UpperTheory.Reformulated.B.StandardLattice.Ml l hl K inst)))
        (@OreLocalization.instAlgebra (@NumberField.RingOfIntegers K inst)
          (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
            (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
              (@NumberField.instCommRingRingOfIntegers K inst)))
          (@UpperTheory.Reformulated.B.StandardLattice.Ml l hl K inst)
          (@OreLocalization.oreSetComm (@NumberField.RingOfIntegers K inst)
            (@CommSemiring.toCommMonoid (@NumberField.RingOfIntegers K inst)
              (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                (@NumberField.instCommRingRingOfIntegers K inst)))
            (@UpperTheory.Reformulated.B.StandardLattice.Ml l hl K inst))
          (@NumberField.RingOfIntegers K inst)
          (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst) (@NumberField.instCommRingRingOfIntegers K inst))
          (@Algebra.id (@NumberField.RingOfIntegers K inst)
            (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
              (@NumberField.instCommRingRingOfIntegers K inst)))) := by
  intro l hl K inst
  exact Localization.isLocalization
theorem UpperTheory.Reformulated.B.StandardLattice.aux6 :
    ∀ (l : Nat) [hl : Fact (Nat.Prime l)] (K : Type) [inst : Field K] [@NumberField K inst]
      (y : ↥(@UpperTheory.Reformulated.B.StandardLattice.Ml l hl K inst)),
      @IsUnit K
        (@MonoidWithZero.toMonoid K
          (@GroupWithZero.toMonoidWithZero K
            (@DivisionSemiring.toGroupWithZero K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))))
        (@DFunLike.coe
          (@RingHom (@NumberField.RingOfIntegers K inst) K
            (@Semiring.toNonAssocSemiring (@NumberField.RingOfIntegers K inst)
              (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
                (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                  (@NumberField.instCommRingRingOfIntegers K inst))))
            (@Semiring.toNonAssocSemiring K
              (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst)))))
          (@NumberField.RingOfIntegers K inst) (fun (x : @NumberField.RingOfIntegers K inst) ↦ K)
          (@RingHom.instFunLike (@NumberField.RingOfIntegers K inst) K
            (@Semiring.toNonAssocSemiring (@NumberField.RingOfIntegers K inst)
              (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
                (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                  (@NumberField.instCommRingRingOfIntegers K inst))))
            (@Semiring.toNonAssocSemiring K
              (@CommSemiring.toSemiring K (@Semifield.toCommSemiring K (@Field.toSemifield K inst)))))
          (@Algebra.algebraMap (@NumberField.RingOfIntegers K inst) K
            (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst) (@NumberField.instCommRingRingOfIntegers K inst))
            (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
            (@NumberField.RingOfIntegers.instAlgebra_1 K inst))
          (@Subtype.val (@NumberField.RingOfIntegers K inst)
            (fun (x : @NumberField.RingOfIntegers K inst) ↦
              @Membership.mem (@NumberField.RingOfIntegers K inst)
                (@Submonoid (@NumberField.RingOfIntegers K inst)
                  (@MulZeroOneClass.toMulOneClass (@NumberField.RingOfIntegers K inst)
                    (@instMulZeroOneClassOfSemiring (@NumberField.RingOfIntegers K inst)
                      (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
                        (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                          (@NumberField.instCommRingRingOfIntegers K inst))))))
                (@SetLike.instMembership
                  (@Submonoid (@NumberField.RingOfIntegers K inst)
                    (@MulZeroOneClass.toMulOneClass (@NumberField.RingOfIntegers K inst)
                      (@instMulZeroOneClassOfSemiring (@NumberField.RingOfIntegers K inst)
                        (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
                          (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                            (@NumberField.instCommRingRingOfIntegers K inst))))))
                  (@NumberField.RingOfIntegers K inst)
                  (@Submonoid.instSetLike (@NumberField.RingOfIntegers K inst)
                    (@MulZeroOneClass.toMulOneClass (@NumberField.RingOfIntegers K inst)
                      (@instMulZeroOneClassOfSemiring (@NumberField.RingOfIntegers K inst)
                        (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
                          (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                            (@NumberField.instCommRingRingOfIntegers K inst)))))))
                (@UpperTheory.Reformulated.B.StandardLattice.Ml l hl K inst) x)
            y)) := by
  intro l hl K inst _ y
  obtain ⟨y, n, hn, rfl⟩ := y
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hn (Ideal.zero_mem _)
  refine isUnit_iff_ne_zero.mpr ?_
  simpa using hn0
noncomputable def UpperTheory.Reformulated.B.StandardLattice.rlToK :
    (l : Nat) →
      [hl : Fact (Nat.Prime l)] →
        (K : Type) →
          [inst : Field K] →
            [@NumberField K inst] →
              @RingHom (@UpperTheory.Reformulated.B.StandardLattice.Rl l hl K inst) K
                (@Semiring.toNonAssocSemiring (@UpperTheory.Reformulated.B.StandardLattice.Rl l hl K inst)
                  (@OreLocalization.instSemiring (@NumberField.RingOfIntegers K inst)
                    (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
                      (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                        (@NumberField.instCommRingRingOfIntegers K inst)))
                    (@UpperTheory.Reformulated.B.StandardLattice.Ml l hl K inst)
                    (@OreLocalization.oreSetComm (@NumberField.RingOfIntegers K inst)
                      (@CommRing.toCommMonoid (@NumberField.RingOfIntegers K inst)
                        (@NumberField.instCommRingRingOfIntegers K inst))
                      (@UpperTheory.Reformulated.B.StandardLattice.Ml l hl K inst))))
                (@Semiring.toNonAssocSemiring K
                  (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))) :=
    fun (l : Nat) [hl : Fact (Nat.Prime l)] (K : Type) [inst : Field K] [inst_1 : @NumberField K inst] ↦
      @IsLocalization.lift (@NumberField.RingOfIntegers K inst)
        (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst) (@NumberField.instCommRingRingOfIntegers K inst))
        (@UpperTheory.Reformulated.B.StandardLattice.Ml l hl K inst) (@UpperTheory.Reformulated.B.StandardLattice.Rl l hl K inst)
        (@OreLocalization.instCommSemiring (@NumberField.RingOfIntegers K inst)
          (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst) (@NumberField.instCommRingRingOfIntegers K inst))
          (@UpperTheory.Reformulated.B.StandardLattice.Ml l hl K inst)
          (@OreLocalization.oreSetComm (@NumberField.RingOfIntegers K inst)
            (@CommRing.toCommMonoid (@NumberField.RingOfIntegers K inst) (@NumberField.instCommRingRingOfIntegers K inst))
            (@UpperTheory.Reformulated.B.StandardLattice.Ml l hl K inst)))
        (@OreLocalization.instAlgebra (@NumberField.RingOfIntegers K inst)
          (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
            (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
              (@NumberField.instCommRingRingOfIntegers K inst)))
          (@UpperTheory.Reformulated.B.StandardLattice.Ml l hl K inst)
          (@OreLocalization.oreSetComm (@NumberField.RingOfIntegers K inst)
            (@CommRing.toCommMonoid (@NumberField.RingOfIntegers K inst) (@NumberField.instCommRingRingOfIntegers K inst))
            (@UpperTheory.Reformulated.B.StandardLattice.Ml l hl K inst))
          (@NumberField.RingOfIntegers K inst)
          (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst) (@NumberField.instCommRingRingOfIntegers K inst))
          (@Algebra.id (@NumberField.RingOfIntegers K inst)
            (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
              (@NumberField.instCommRingRingOfIntegers K inst))))
        K (@Semifield.toCommSemiring K (@Field.toSemifield K inst)) (@UpperTheory.Reformulated.B.StandardLattice.aux5 l hl K inst)
        (@Algebra.algebraMap (@NumberField.RingOfIntegers K inst) K
          (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst) (@NumberField.instCommRingRingOfIntegers K inst))
          (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
          (@NumberField.RingOfIntegers.instAlgebra_1 K inst))
        (@UpperTheory.Reformulated.B.StandardLattice.aux6 l hl K inst inst_1)
@[reducible] noncomputable def UpperTheory.Reformulated.B.StandardLattice.rlAlgebra :
    (l : Nat) →
      [hl : Fact (Nat.Prime l)] →
        (K : Type) →
          [inst : Field K] →
            [@NumberField K inst] →
              @Algebra (@UpperTheory.Reformulated.B.StandardLattice.Rl l hl K inst) K
                (@OreLocalization.instCommSemiring (@NumberField.RingOfIntegers K inst)
                  (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                    (@NumberField.instCommRingRingOfIntegers K inst))
                  (@UpperTheory.Reformulated.B.StandardLattice.Ml l hl K inst)
                  (@OreLocalization.oreSetComm (@NumberField.RingOfIntegers K inst)
                    (@CommRing.toCommMonoid (@NumberField.RingOfIntegers K inst)
                      (@NumberField.instCommRingRingOfIntegers K inst))
                    (@UpperTheory.Reformulated.B.StandardLattice.Ml l hl K inst)))
                (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst))) :=
    fun (l : Nat) [hl : Fact (Nat.Prime l)] (K : Type) [inst : Field K] [inst_1 : @NumberField K inst] ↦
      @RingHom.toAlgebra (@UpperTheory.Reformulated.B.StandardLattice.Rl l hl K inst) K
        (@OreLocalization.instCommSemiring (@NumberField.RingOfIntegers K inst)
          (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst) (@NumberField.instCommRingRingOfIntegers K inst))
          (@UpperTheory.Reformulated.B.StandardLattice.Ml l hl K inst)
          (@OreLocalization.oreSetComm (@NumberField.RingOfIntegers K inst)
            (@CommRing.toCommMonoid (@NumberField.RingOfIntegers K inst) (@NumberField.instCommRingRingOfIntegers K inst))
            (@UpperTheory.Reformulated.B.StandardLattice.Ml l hl K inst)))
        (@Semifield.toCommSemiring K (@Field.toSemifield K inst)) (@UpperTheory.Reformulated.B.StandardLattice.rlToK l hl K inst inst_1)
attribute [local instance] UpperTheory.Reformulated.B.StandardLattice.rlAlgebra
@[reducible] noncomputable def UpperTheory.Reformulated.B.StandardLattice.rlModule :
    (l : Nat) →
      [hl : Fact (Nat.Prime l)] →
        (K : Type) →
          [inst : Field K] →
            [@NumberField K inst] →
              (V : Type) →
                [inst_2 : AddCommGroup V] →
                  [@_root_.Module K V
                        (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                        (@AddCommGroup.toAddCommMonoid V inst_2)] →
                    @_root_.Module (@UpperTheory.Reformulated.B.StandardLattice.Rl l hl K inst) V
                      (@OreLocalization.instSemiring (@NumberField.RingOfIntegers K inst)
                        (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
                          (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                            (@NumberField.instCommRingRingOfIntegers K inst)))
                        (@UpperTheory.Reformulated.B.StandardLattice.Ml l hl K inst)
                        (@OreLocalization.oreSetComm (@NumberField.RingOfIntegers K inst)
                          (@CommRing.toCommMonoid (@NumberField.RingOfIntegers K inst)
                            (@NumberField.instCommRingRingOfIntegers K inst))
                          (@UpperTheory.Reformulated.B.StandardLattice.Ml l hl K inst)))
                      (@AddCommGroup.toAddCommMonoid V inst_2) :=
    fun (l : Nat) [hl : Fact (Nat.Prime l)] (K : Type) [inst : Field K] [inst_1 : @NumberField K inst] (V : Type)
        [inst_2 : AddCommGroup V]
        [inst_3 :
          @_root_.Module K V (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
            (@AddCommGroup.toAddCommMonoid V inst_2)] ↦
      @Module.compHom K (@UpperTheory.Reformulated.B.StandardLattice.Rl l hl K inst) V
        (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
        (@AddCommGroup.toAddCommMonoid V inst_2) inst_3
        (@OreLocalization.instSemiring (@NumberField.RingOfIntegers K inst)
          (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
            (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
              (@NumberField.instCommRingRingOfIntegers K inst)))
          (@UpperTheory.Reformulated.B.StandardLattice.Ml l hl K inst)
          (@OreLocalization.oreSetComm (@NumberField.RingOfIntegers K inst)
            (@CommRing.toCommMonoid (@NumberField.RingOfIntegers K inst) (@NumberField.instCommRingRingOfIntegers K inst))
            (@UpperTheory.Reformulated.B.StandardLattice.Ml l hl K inst)))
        (@Algebra.algebraMap (@UpperTheory.Reformulated.B.StandardLattice.Rl l hl K inst) K
          (@OreLocalization.instCommSemiring (@NumberField.RingOfIntegers K inst)
            (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst) (@NumberField.instCommRingRingOfIntegers K inst))
            (@UpperTheory.Reformulated.B.StandardLattice.Ml l hl K inst)
            (@OreLocalization.oreSetComm (@NumberField.RingOfIntegers K inst)
              (@CommRing.toCommMonoid (@NumberField.RingOfIntegers K inst) (@NumberField.instCommRingRingOfIntegers K inst))
              (@UpperTheory.Reformulated.B.StandardLattice.Ml l hl K inst)))
          (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
          (@UpperTheory.Reformulated.B.StandardLattice.rlAlgebra l hl K inst inst_1))
noncomputable def UpperTheory.Reformulated.B.StandardLattice.atL :
    (l : Nat) →
      [hl : Fact (Nat.Prime l)] →
        (K : Type) →
          [inst : Field K] →
            [inst_1 : @NumberField K inst] →
              {V : Type} →
                [inst_2 : AddCommGroup V] →
                  [inst_3 :
                      @_root_.Module K V
                        (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
                        (@AddCommGroup.toAddCommMonoid V inst_2)] →
                    [inst_4 :
                        @_root_.Module (@NumberField.RingOfIntegers K inst) V
                          (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
                            (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                              (@NumberField.instCommRingRingOfIntegers K inst)))
                          (@AddCommGroup.toAddCommMonoid V inst_2)] →
                      @Submodule (@NumberField.RingOfIntegers K inst) V
                          (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
                            (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                              (@NumberField.instCommRingRingOfIntegers K inst)))
                          (@AddCommGroup.toAddCommMonoid V inst_2) inst_4 →
                        @Submodule (@UpperTheory.Reformulated.B.StandardLattice.Rl l hl K inst) V
                          (@OreLocalization.instSemiring (@NumberField.RingOfIntegers K inst)
                            (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
                              (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                                (@NumberField.instCommRingRingOfIntegers K inst)))
                            (@UpperTheory.Reformulated.B.StandardLattice.Ml l hl K inst)
                            (@OreLocalization.oreSetComm (@NumberField.RingOfIntegers K inst)
                              (@CommRing.toCommMonoid (@NumberField.RingOfIntegers K inst)
                                (@NumberField.instCommRingRingOfIntegers K inst))
                              (@UpperTheory.Reformulated.B.StandardLattice.Ml l hl K inst)))
                          (@AddCommGroup.toAddCommMonoid V inst_2)
                          (@UpperTheory.Reformulated.B.StandardLattice.rlModule l hl K inst inst_1 V inst_2 inst_3) :=
    fun (l : Nat) [hl : Fact (Nat.Prime l)] (K : Type) [inst : Field K] [inst_1 : @NumberField K inst] {V : Type}
        [inst_2 : AddCommGroup V]
        [inst_3 :
          @_root_.Module K V (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))
            (@AddCommGroup.toAddCommMonoid V inst_2)]
        [inst_4 :
          @_root_.Module (@NumberField.RingOfIntegers K inst) V
            (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
              (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                (@NumberField.instCommRingRingOfIntegers K inst)))
            (@AddCommGroup.toAddCommMonoid V inst_2)]
        (L :
          @Submodule (@NumberField.RingOfIntegers K inst) V
            (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
              (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                (@NumberField.instCommRingRingOfIntegers K inst)))
            (@AddCommGroup.toAddCommMonoid V inst_2) inst_4) ↦
      @Submodule.span (@UpperTheory.Reformulated.B.StandardLattice.Rl l hl K inst) V
        (@OreLocalization.instSemiring (@NumberField.RingOfIntegers K inst)
          (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
            (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
              (@NumberField.instCommRingRingOfIntegers K inst)))
          (@UpperTheory.Reformulated.B.StandardLattice.Ml l hl K inst)
          (@OreLocalization.oreSetComm (@NumberField.RingOfIntegers K inst)
            (@CommRing.toCommMonoid (@NumberField.RingOfIntegers K inst) (@NumberField.instCommRingRingOfIntegers K inst))
            (@UpperTheory.Reformulated.B.StandardLattice.Ml l hl K inst)))
        (@AddCommGroup.toAddCommMonoid V inst_2) (@UpperTheory.Reformulated.B.StandardLattice.rlModule l hl K inst inst_1 V inst_2 inst_3)
        (@SetLike.coe
          (@Submodule (@NumberField.RingOfIntegers K inst) V
            (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
              (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                (@NumberField.instCommRingRingOfIntegers K inst)))
            (@AddCommGroup.toAddCommMonoid V inst_2) inst_4)
          V
          (@Submodule.setLike (@NumberField.RingOfIntegers K inst) V
            (@CommSemiring.toSemiring (@NumberField.RingOfIntegers K inst)
              (@CommRing.toCommSemiring (@NumberField.RingOfIntegers K inst)
                (@NumberField.instCommRingRingOfIntegers K inst)))
            (@AddCommGroup.toAddCommMonoid V inst_2) inst_4)
          L)


