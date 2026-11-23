-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_BlockHomomorphism
-- name    : Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_BlockHomomorphism
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:06:56.972001+00:00
-- url     : https://prove2.me/theorems/aa693551-bba8-467f-a467-be360b151037
-- title:
--   Block Homomorphism
-- statement:
--   Definitions and structural lemmas for Block Homomorphism, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/BlockHomomorphism.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable def UpperTheory.Reformulated.B.BlockHomomorphism.IsSmooth :
    {k G V : Type} →
      [inst : Field k] →
        [inst_1 : Group G] →
          [inst_2 : AddCommGroup V] →
            [inst_3 :
                @_root_.Module k V
                  (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst)))
                  (@AddCommGroup.toAddCommMonoid V inst_2)] →
              [TopologicalSpace G] →
                @Representation k G V
                    (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst)))
                    (@DivInvMonoid.toMonoid G (@Group.toDivInvMonoid G inst_1)) (@AddCommGroup.toAddCommMonoid V inst_2)
                    inst_3 →
                  Prop :=
    fun {k G V : Type} [inst : Field k] [inst_1 : Group G] [inst_2 : AddCommGroup V]
        [inst_3 :
          @_root_.Module k V (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst)))
            (@AddCommGroup.toAddCommMonoid V inst_2)]
        [inst_4 : TopologicalSpace G]
        (ρ :
          @Representation k G V
            (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst)))
            (@DivInvMonoid.toMonoid G (@Group.toDivInvMonoid G inst_1)) (@AddCommGroup.toAddCommMonoid V inst_2) inst_3) ↦
      ∀ (v : V),
        @IsOpen G inst_4
          (@Set.ofPred G fun (g : G) ↦
            @Eq V
              (@DFunLike.coe
                (@LinearMap k k
                  (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst)))
                  (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst)))
                  (@RingHom.id k
                    (@Semiring.toNonAssocSemiring k
                      (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst)))))
                  V V (@AddCommGroup.toAddCommMonoid V inst_2) (@AddCommGroup.toAddCommMonoid V inst_2) inst_3 inst_3)
                V (fun (x : V) ↦ V)
                (@LinearMap.instFunLike k k V V
                  (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst)))
                  (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst)))
                  (@AddCommGroup.toAddCommMonoid V inst_2) (@AddCommGroup.toAddCommMonoid V inst_2) inst_3 inst_3
                  (@RingHom.id k
                    (@Semiring.toNonAssocSemiring k
                      (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst))))))
                (@DFunLike.coe
                  (@Representation k G V
                    (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst)))
                    (@DivInvMonoid.toMonoid G (@Group.toDivInvMonoid G inst_1)) (@AddCommGroup.toAddCommMonoid V inst_2)
                    inst_3)
                  G
                  (fun (x : G) ↦
                    @LinearMap k k
                      (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst)))
                      (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst)))
                      (@RingHom.id k
                        (@Semiring.toNonAssocSemiring k
                          (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst)))))
                      V V (@AddCommGroup.toAddCommMonoid V inst_2) (@AddCommGroup.toAddCommMonoid V inst_2) inst_3 inst_3)
                  (@MonoidHom.instFunLike G
                    (@LinearMap k k
                      (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst)))
                      (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst)))
                      (@RingHom.id k
                        (@Semiring.toNonAssocSemiring k
                          (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst)))))
                      V V (@AddCommGroup.toAddCommMonoid V inst_2) (@AddCommGroup.toAddCommMonoid V inst_2) inst_3 inst_3)
                    (@MulOneClass.toMulOne G
                      (@Monoid.toMulOneClass G (@DivInvMonoid.toMonoid G (@Group.toDivInvMonoid G inst_1))))
                    (@MulOneClass.toMulOne
                      (@LinearMap k k
                        (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst)))
                        (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst)))
                        (@RingHom.id k
                          (@Semiring.toNonAssocSemiring k
                            (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst)))))
                        V V (@AddCommGroup.toAddCommMonoid V inst_2) (@AddCommGroup.toAddCommMonoid V inst_2) inst_3 inst_3)
                      (@MulZeroOneClass.toMulOneClass
                        (@LinearMap k k
                          (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst)))
                          (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst)))
                          (@RingHom.id k
                            (@Semiring.toNonAssocSemiring k
                              (@DivisionSemiring.toSemiring k
                                (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst)))))
                          V V (@AddCommGroup.toAddCommMonoid V inst_2) (@AddCommGroup.toAddCommMonoid V inst_2) inst_3
                          inst_3)
                        (@instMulZeroOneClassOfSemiring
                          (@LinearMap k k
                            (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst)))
                            (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst)))
                            (@RingHom.id k
                              (@Semiring.toNonAssocSemiring k
                                (@DivisionSemiring.toSemiring k
                                  (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst)))))
                            V V (@AddCommGroup.toAddCommMonoid V inst_2) (@AddCommGroup.toAddCommMonoid V inst_2) inst_3
                            inst_3)
                          (@Module.End.instSemiring k V
                            (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst)))
                            (@AddCommGroup.toAddCommMonoid V inst_2) inst_3)))))
                  ρ g)
                v)
              v)
noncomputable def UpperTheory.Reformulated.B.BlockHomomorphism.glCongr :
    (k : Type) →
      [inst : Field k] →
        {a b : Nat} →
          @Eq Nat a b →
            @MonoidHom
              (@Matrix.GeneralLinearGroup (Fin a) k (instDecidableEqFin a) (Fin.fintype a)
                (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst))))
              (@Matrix.GeneralLinearGroup (Fin b) k (instDecidableEqFin b) (Fin.fintype b)
                (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst))))
              (@MulOneClass.toMulOne
                (@Matrix.GeneralLinearGroup (Fin a) k (instDecidableEqFin a) (Fin.fintype a)
                  (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst))))
                (@Units.instMulOneClass (Matrix (Fin a) (Fin a) k)
                  (@Semiring.toMonoid (Matrix (Fin a) (Fin a) k)
                    (@Matrix.semiring (Fin a) k
                      (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst)))
                      (Fin.fintype a) (instDecidableEqFin a)))))
              (@MulOneClass.toMulOne
                (@Matrix.GeneralLinearGroup (Fin b) k (instDecidableEqFin b) (Fin.fintype b)
                  (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst))))
                (@Units.instMulOneClass (Matrix (Fin b) (Fin b) k)
                  (@Semiring.toMonoid (Matrix (Fin b) (Fin b) k)
                    (@Matrix.semiring (Fin b) k
                      (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst)))
                      (Fin.fintype b) (instDecidableEqFin b))))) :=
    fun (k : Type) [inst : Field k] {a b : Nat} (h : @Eq Nat a b) ↦
      @Units.map (Matrix (Fin a) (Fin a) k) (Matrix (Fin b) (Fin b) k)
        (@Semiring.toMonoid (Matrix (Fin a) (Fin a) k)
          (@Matrix.semiring (Fin a) k
            (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst))) (Fin.fintype a)
            (instDecidableEqFin a)))
        (@Semiring.toMonoid (Matrix (Fin b) (Fin b) k)
          (@Matrix.semiring (Fin b) k
            (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst))) (Fin.fintype b)
            (instDecidableEqFin b)))
        (@MulEquiv.toMonoidHom (Matrix (Fin a) (Fin a) k) (Matrix (Fin b) (Fin b) k)
          (@MulZeroOneClass.toMulOneClass (Matrix (Fin a) (Fin a) k)
            (@instMulZeroOneClassOfSemiring (Matrix (Fin a) (Fin a) k)
              (@Matrix.semiring (Fin a) k
                (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst)))
                (Fin.fintype a) (instDecidableEqFin a))))
          (@MulZeroOneClass.toMulOneClass (Matrix (Fin b) (Fin b) k)
            (@instMulZeroOneClassOfSemiring (Matrix (Fin b) (Fin b) k)
              (@Matrix.semiring (Fin b) k
                (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst)))
                (Fin.fintype b) (instDecidableEqFin b))))
          (@AlgEquiv.toMulEquiv k (Matrix (Fin a) (Fin a) k) (Matrix (Fin b) (Fin b) k)
            (@Semifield.toCommSemiring k (@Field.toSemifield k inst))
            (@Matrix.semiring (Fin a) k
              (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst))) (Fin.fintype a)
              (instDecidableEqFin a))
            (@Matrix.semiring (Fin b) k
              (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst))) (Fin.fintype b)
              (instDecidableEqFin b))
            (@Matrix.instAlgebra (Fin a) k k (Fin.fintype a) (instDecidableEqFin a)
              (@Semifield.toCommSemiring k (@Field.toSemifield k inst))
              (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst)))
              (@Algebra.id k (@Semifield.toCommSemiring k (@Field.toSemifield k inst))))
            (@Matrix.instAlgebra (Fin b) k k (Fin.fintype b) (instDecidableEqFin b)
              (@Semifield.toCommSemiring k (@Field.toSemifield k inst))
              (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst)))
              (@Algebra.id k (@Semifield.toCommSemiring k (@Field.toSemifield k inst))))
            (@Matrix.reindexAlgEquiv (Fin a) (Fin b) k k (@Semifield.toCommSemiring k (@Field.toSemifield k inst))
              (Fin.fintype b) (Fin.fintype a) (instDecidableEqFin a) (instDecidableEqFin b)
              (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst)))
              (@Algebra.id k (@Semifield.toCommSemiring k (@Field.toSemifield k inst))) (@finCongr a b h))))
theorem UpperTheory.Reformulated.B.BlockHomomorphism.aux3 :
    ∀ (k : Type) [inst : Field k] (n r : Nat),
      @Eq (Matrix (Sum (Fin n) (Fin r)) (Sum (Fin n) (Fin r)) k)
        (@Matrix.fromBlocks (Fin n) (Fin r) (Fin n) (Fin r) k
          (@OfNat.ofNat (Matrix (Fin n) (Fin n) k) (nat_lit 1)
            (@One.toOfNat1 (Matrix (Fin n) (Fin n) k)
              (@MulOne.toOne (Matrix (Fin n) (Fin n) k)
                (@Matrix.instMulOneOfFintypeOfDecidableEqOfAddCommMonoid (Fin n) k (Fin.fintype n) (instDecidableEqFin n)
                  (@MulOneClass.toMulOne k
                    (@MulZeroOneClass.toMulOneClass k
                      (@instMulZeroOneClassOfSemiring k
                        (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst))))))
                  (@Semiring.toAddCommMonoid k
                    (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst))))))))
          (@OfNat.ofNat (Matrix (Fin n) (Fin r) k) (nat_lit 0)
            (@Zero.toOfNat0 (Matrix (Fin n) (Fin r) k)
              (@Matrix.zero (Fin n) (Fin r) k
                (@MulZeroClass.toZero k
                  (@instMulZeroClassOfSemiring k
                    (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst))))))))
          (@OfNat.ofNat (Matrix (Fin r) (Fin n) k) (nat_lit 0)
            (@Zero.toOfNat0 (Matrix (Fin r) (Fin n) k)
              (@Matrix.zero (Fin r) (Fin n) k
                (@MulZeroClass.toZero k
                  (@instMulZeroClassOfSemiring k
                    (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst))))))))
          (@OfNat.ofNat (Matrix (Fin r) (Fin r) k) (nat_lit 1)
            (@One.toOfNat1 (Matrix (Fin r) (Fin r) k)
              (@Matrix.one (Fin r) k (instDecidableEqFin r)
                (@MulZeroClass.toZero k
                  (@instMulZeroClassOfSemiring k
                    (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst)))))
                (@AddMonoidWithOne.toOne k
                  (@AddGroupWithOne.toAddMonoidWithOne k
                    (@Ring.toAddGroupWithOne k (@DivisionRing.toRing k (@Field.toDivisionRing k inst)))))))))
        (@OfNat.ofNat (Matrix (Sum (Fin n) (Fin r)) (Sum (Fin n) (Fin r)) k) (nat_lit 1)
          (@One.toOfNat1 (Matrix (Sum (Fin n) (Fin r)) (Sum (Fin n) (Fin r)) k)
            (@MulOne.toOne (Matrix (Sum (Fin n) (Fin r)) (Sum (Fin n) (Fin r)) k)
              (@Matrix.instMulOneOfFintypeOfDecidableEqOfAddCommMonoid (Sum (Fin n) (Fin r)) k
                (@instFintypeSum (Fin n) (Fin r) (Fin.fintype n) (Fin.fintype r))
                (fun (a b : Sum (Fin n) (Fin r)) ↦
                  @instDecidableEqSum (Fin n) (Fin r) (instDecidableEqFin n) (instDecidableEqFin r) a b)
                (@MulOneClass.toMulOne k
                  (@MulZeroOneClass.toMulOneClass k
                    (@instMulZeroOneClassOfSemiring k
                      (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst))))))
                (@Semiring.toAddCommMonoid k
                  (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst)))))))) := by
  intro k _ n r
  exact Matrix.fromBlocks_one
theorem UpperTheory.Reformulated.B.BlockHomomorphism.aux4 :
    ∀ (k : Type) [inst : Field k] (n r : Nat) (A B : Matrix (Fin n) (Fin n) k),
      @Eq (Matrix (Sum (Fin n) (Fin r)) (Sum (Fin n) (Fin r)) k)
        (@Matrix.fromBlocks (Fin n) (Fin r) (Fin n) (Fin r) k
          (@HMul.hMul (Matrix (Fin n) (Fin n) k) (Matrix (Fin n) (Fin n) k) (Matrix (Fin n) (Fin n) k)
            (@instHMul (Matrix (Fin n) (Fin n) k)
              (@MulOne.toMul (Matrix (Fin n) (Fin n) k)
                (@Matrix.instMulOneOfFintypeOfDecidableEqOfAddCommMonoid (Fin n) k (Fin.fintype n) (instDecidableEqFin n)
                  (@MulOneClass.toMulOne k
                    (@MulZeroOneClass.toMulOneClass k
                      (@instMulZeroOneClassOfSemiring k
                        (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst))))))
                  (@Semiring.toAddCommMonoid k
                    (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst)))))))
            A B)
          (@OfNat.ofNat (Matrix (Fin n) (Fin r) k) (nat_lit 0)
            (@Zero.toOfNat0 (Matrix (Fin n) (Fin r) k)
              (@Matrix.zero (Fin n) (Fin r) k
                (@MulZeroClass.toZero k
                  (@instMulZeroClassOfSemiring k
                    (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst))))))))
          (@OfNat.ofNat (Matrix (Fin r) (Fin n) k) (nat_lit 0)
            (@Zero.toOfNat0 (Matrix (Fin r) (Fin n) k)
              (@Matrix.zero (Fin r) (Fin n) k
                (@MulZeroClass.toZero k
                  (@instMulZeroClassOfSemiring k
                    (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst))))))))
          (@OfNat.ofNat (Matrix (Fin r) (Fin r) k) (nat_lit 1)
            (@One.toOfNat1 (Matrix (Fin r) (Fin r) k)
              (@Matrix.one (Fin r) k (instDecidableEqFin r)
                (@MulZeroClass.toZero k
                  (@instMulZeroClassOfSemiring k
                    (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst)))))
                (@AddMonoidWithOne.toOne k
                  (@AddGroupWithOne.toAddMonoidWithOne k
                    (@Ring.toAddGroupWithOne k (@DivisionRing.toRing k (@Field.toDivisionRing k inst)))))))))
        (@HMul.hMul (Matrix (Sum (Fin n) (Fin r)) (Sum (Fin n) (Fin r)) k)
          (Matrix (Sum (Fin n) (Fin r)) (Sum (Fin n) (Fin r)) k) (Matrix (Sum (Fin n) (Fin r)) (Sum (Fin n) (Fin r)) k)
          (@instHMul (Matrix (Sum (Fin n) (Fin r)) (Sum (Fin n) (Fin r)) k)
            (@MulOne.toMul (Matrix (Sum (Fin n) (Fin r)) (Sum (Fin n) (Fin r)) k)
              (@Matrix.instMulOneOfFintypeOfDecidableEqOfAddCommMonoid (Sum (Fin n) (Fin r)) k
                (@instFintypeSum (Fin n) (Fin r) (Fin.fintype n) (Fin.fintype r))
                (fun (a b : Sum (Fin n) (Fin r)) ↦
                  @instDecidableEqSum (Fin n) (Fin r) (instDecidableEqFin n) (instDecidableEqFin r) a b)
                (@MulOneClass.toMulOne k
                  (@MulZeroOneClass.toMulOneClass k
                    (@instMulZeroOneClassOfSemiring k
                      (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst))))))
                (@Semiring.toAddCommMonoid k
                  (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst)))))))
          (@Matrix.fromBlocks (Fin n) (Fin r) (Fin n) (Fin r) k A
            (@OfNat.ofNat (Matrix (Fin n) (Fin r) k) (nat_lit 0)
              (@Zero.toOfNat0 (Matrix (Fin n) (Fin r) k)
                (@Matrix.zero (Fin n) (Fin r) k
                  (@MulZeroClass.toZero k
                    (@instMulZeroClassOfSemiring k
                      (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst))))))))
            (@OfNat.ofNat (Matrix (Fin r) (Fin n) k) (nat_lit 0)
              (@Zero.toOfNat0 (Matrix (Fin r) (Fin n) k)
                (@Matrix.zero (Fin r) (Fin n) k
                  (@MulZeroClass.toZero k
                    (@instMulZeroClassOfSemiring k
                      (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst))))))))
            (@OfNat.ofNat (Matrix (Fin r) (Fin r) k) (nat_lit 1)
              (@One.toOfNat1 (Matrix (Fin r) (Fin r) k)
                (@Matrix.one (Fin r) k (instDecidableEqFin r)
                  (@MulZeroClass.toZero k
                    (@instMulZeroClassOfSemiring k
                      (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst)))))
                  (@AddMonoidWithOne.toOne k
                    (@AddGroupWithOne.toAddMonoidWithOne k
                      (@Ring.toAddGroupWithOne k (@DivisionRing.toRing k (@Field.toDivisionRing k inst)))))))))
          (@Matrix.fromBlocks (Fin n) (Fin r) (Fin n) (Fin r) k B
            (@OfNat.ofNat (Matrix (Fin n) (Fin r) k) (nat_lit 0)
              (@Zero.toOfNat0 (Matrix (Fin n) (Fin r) k)
                (@Matrix.zero (Fin n) (Fin r) k
                  (@MulZeroClass.toZero k
                    (@instMulZeroClassOfSemiring k
                      (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst))))))))
            (@OfNat.ofNat (Matrix (Fin r) (Fin n) k) (nat_lit 0)
              (@Zero.toOfNat0 (Matrix (Fin r) (Fin n) k)
                (@Matrix.zero (Fin r) (Fin n) k
                  (@MulZeroClass.toZero k
                    (@instMulZeroClassOfSemiring k
                      (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst))))))))
            (@OfNat.ofNat (Matrix (Fin r) (Fin r) k) (nat_lit 1)
              (@One.toOfNat1 (Matrix (Fin r) (Fin r) k)
                (@Matrix.one (Fin r) k (instDecidableEqFin r)
                  (@MulZeroClass.toZero k
                    (@instMulZeroClassOfSemiring k
                      (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst)))))
                  (@AddMonoidWithOne.toOne k
                    (@AddGroupWithOne.toAddMonoidWithOne k
                      (@Ring.toAddGroupWithOne k (@DivisionRing.toRing k (@Field.toDivisionRing k inst)))))))))) := by
  intro k _ n r A B
  simp [Matrix.fromBlocks_multiply]
noncomputable def UpperTheory.Reformulated.B.BlockHomomorphism.blkHom :
    (k : Type) →
      [inst : Field k] →
        (n r : Nat) →
          @MonoidHom (Matrix (Fin n) (Fin n) k) (Matrix (Sum (Fin n) (Fin r)) (Sum (Fin n) (Fin r)) k)
            (@Matrix.instMulOneOfFintypeOfDecidableEqOfAddCommMonoid (Fin n) k (Fin.fintype n) (instDecidableEqFin n)
              (@MulOneClass.toMulOne k
                (@MulZeroOneClass.toMulOneClass k
                  (@instMulZeroOneClassOfSemiring k
                    (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst))))))
              (@Semiring.toAddCommMonoid k
                (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst)))))
            (@Matrix.instMulOneOfFintypeOfDecidableEqOfAddCommMonoid (Sum (Fin n) (Fin r)) k
              (@instFintypeSum (Fin n) (Fin r) (Fin.fintype n) (Fin.fintype r))
              (fun (a b : Sum (Fin n) (Fin r)) ↦
                @instDecidableEqSum (Fin n) (Fin r) (instDecidableEqFin n) (instDecidableEqFin r) a b)
              (@MulOneClass.toMulOne k
                (@MulZeroOneClass.toMulOneClass k
                  (@instMulZeroOneClassOfSemiring k
                    (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst))))))
              (@Semiring.toAddCommMonoid k
                (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst))))) :=
    fun (k : Type) [inst : Field k] (n r : Nat) ↦
      @MonoidHom.mk (Matrix (Fin n) (Fin n) k) (Matrix (Sum (Fin n) (Fin r)) (Sum (Fin n) (Fin r)) k)
        (@Matrix.instMulOneOfFintypeOfDecidableEqOfAddCommMonoid (Fin n) k (Fin.fintype n) (instDecidableEqFin n)
          (@MulOneClass.toMulOne k
            (@MulZeroOneClass.toMulOneClass k
              (@instMulZeroOneClassOfSemiring k
                (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst))))))
          (@Semiring.toAddCommMonoid k
            (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst)))))
        (@Matrix.instMulOneOfFintypeOfDecidableEqOfAddCommMonoid (Sum (Fin n) (Fin r)) k
          (@instFintypeSum (Fin n) (Fin r) (Fin.fintype n) (Fin.fintype r))
          (fun (a b : Sum (Fin n) (Fin r)) ↦
            @instDecidableEqSum (Fin n) (Fin r) (instDecidableEqFin n) (instDecidableEqFin r) a b)
          (@MulOneClass.toMulOne k
            (@MulZeroOneClass.toMulOneClass k
              (@instMulZeroOneClassOfSemiring k
                (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst))))))
          (@Semiring.toAddCommMonoid k
            (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst)))))
        (@OneHom.mk (Matrix (Fin n) (Fin n) k) (Matrix (Sum (Fin n) (Fin r)) (Sum (Fin n) (Fin r)) k)
          (@MulOne.toOne (Matrix (Fin n) (Fin n) k)
            (@Matrix.instMulOneOfFintypeOfDecidableEqOfAddCommMonoid (Fin n) k (Fin.fintype n) (instDecidableEqFin n)
              (@MulOneClass.toMulOne k
                (@MulZeroOneClass.toMulOneClass k
                  (@instMulZeroOneClassOfSemiring k
                    (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst))))))
              (@Semiring.toAddCommMonoid k
                (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst))))))
          (@MulOne.toOne (Matrix (Sum (Fin n) (Fin r)) (Sum (Fin n) (Fin r)) k)
            (@Matrix.instMulOneOfFintypeOfDecidableEqOfAddCommMonoid (Sum (Fin n) (Fin r)) k
              (@instFintypeSum (Fin n) (Fin r) (Fin.fintype n) (Fin.fintype r))
              (fun (a b : Sum (Fin n) (Fin r)) ↦
                @instDecidableEqSum (Fin n) (Fin r) (instDecidableEqFin n) (instDecidableEqFin r) a b)
              (@MulOneClass.toMulOne k
                (@MulZeroOneClass.toMulOneClass k
                  (@instMulZeroOneClassOfSemiring k
                    (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst))))))
              (@Semiring.toAddCommMonoid k
                (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst))))))
          (fun (A : Matrix (Fin n) (Fin n) k) ↦
            @Matrix.fromBlocks (Fin n) (Fin r) (Fin n) (Fin r) k A
              (@OfNat.ofNat (Matrix (Fin n) (Fin r) k) (nat_lit 0)
                (@Zero.toOfNat0 (Matrix (Fin n) (Fin r) k)
                  (@Matrix.zero (Fin n) (Fin r) k
                    (@MulZeroClass.toZero k
                      (@instMulZeroClassOfSemiring k
                        (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst))))))))
              (@OfNat.ofNat (Matrix (Fin r) (Fin n) k) (nat_lit 0)
                (@Zero.toOfNat0 (Matrix (Fin r) (Fin n) k)
                  (@Matrix.zero (Fin r) (Fin n) k
                    (@MulZeroClass.toZero k
                      (@instMulZeroClassOfSemiring k
                        (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst))))))))
              (@OfNat.ofNat (Matrix (Fin r) (Fin r) k) (nat_lit 1)
                (@One.toOfNat1 (Matrix (Fin r) (Fin r) k)
                  (@Matrix.one (Fin r) k (instDecidableEqFin r)
                    (@MulZeroClass.toZero k
                      (@instMulZeroClassOfSemiring k
                        (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst)))))
                    (@AddMonoidWithOne.toOne k
                      (@AddGroupWithOne.toAddMonoidWithOne k
                        (@Ring.toAddGroupWithOne k (@DivisionRing.toRing k (@Field.toDivisionRing k inst)))))))))
          (@UpperTheory.Reformulated.B.BlockHomomorphism.aux3 k inst n r))
        (@UpperTheory.Reformulated.B.BlockHomomorphism.aux4 k inst n r)
noncomputable def UpperTheory.Reformulated.B.BlockHomomorphism.blkGL :
    (k : Type) →
      [inst : Field k] →
        (n r : Nat) →
          @MonoidHom
            (@Matrix.GeneralLinearGroup (Fin n) k (instDecidableEqFin n) (Fin.fintype n)
              (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst))))
            (@Matrix.GeneralLinearGroup (Fin (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n r)) k
              (instDecidableEqFin (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n r))
              (Fin.fintype (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n r))
              (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst))))
            (@MulOneClass.toMulOne
              (@Matrix.GeneralLinearGroup (Fin n) k (instDecidableEqFin n) (Fin.fintype n)
                (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst))))
              (@Units.instMulOneClass (Matrix (Fin n) (Fin n) k)
                (@Semiring.toMonoid (Matrix (Fin n) (Fin n) k)
                  (@Matrix.semiring (Fin n) k
                    (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst)))
                    (Fin.fintype n) (instDecidableEqFin n)))))
            (@MulOneClass.toMulOne
              (@Matrix.GeneralLinearGroup (Fin (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n r)) k
                (instDecidableEqFin (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n r))
                (Fin.fintype (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n r))
                (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst))))
              (@Units.instMulOneClass
                (Matrix (Fin (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n r))
                  (Fin (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n r)) k)
                (@Semiring.toMonoid
                  (Matrix (Fin (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n r))
                    (Fin (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n r)) k)
                  (@Matrix.semiring (Fin (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n r)) k
                    (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst)))
                    (Fin.fintype (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n r))
                    (instDecidableEqFin (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n r)))))) :=
    fun (k : Type) [inst : Field k] (n r : Nat) ↦
      @Units.map (Matrix (Fin n) (Fin n) k)
        (Matrix (Fin (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n r))
          (Fin (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n r)) k)
        (@Semiring.toMonoid (Matrix (Fin n) (Fin n) k)
          (@Matrix.semiring (Fin n) k
            (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst))) (Fin.fintype n)
            (instDecidableEqFin n)))
        (@Semiring.toMonoid
          (Matrix (Fin (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n r))
            (Fin (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n r)) k)
          (@Matrix.semiring (Fin (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n r)) k
            (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst)))
            (Fin.fintype (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n r))
            (instDecidableEqFin (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n r))))
        (@MonoidHom.comp (Matrix (Fin n) (Fin n) k) (Matrix (Sum (Fin n) (Fin r)) (Sum (Fin n) (Fin r)) k)
          (Matrix (Fin (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n r))
            (Fin (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n r)) k)
          (@MulOneClass.toMulOne (Matrix (Fin n) (Fin n) k)
            (@Monoid.toMulOneClass (Matrix (Fin n) (Fin n) k)
              (@Semiring.toMonoid (Matrix (Fin n) (Fin n) k)
                (@Matrix.semiring (Fin n) k
                  (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst)))
                  (Fin.fintype n) (instDecidableEqFin n)))))
          (@MulOneClass.toMulOne (Matrix (Sum (Fin n) (Fin r)) (Sum (Fin n) (Fin r)) k)
            (@MulZeroOneClass.toMulOneClass (Matrix (Sum (Fin n) (Fin r)) (Sum (Fin n) (Fin r)) k)
              (@instMulZeroOneClassOfSemiring (Matrix (Sum (Fin n) (Fin r)) (Sum (Fin n) (Fin r)) k)
                (@Matrix.semiring (Sum (Fin n) (Fin r)) k
                  (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst)))
                  (@instFintypeSum (Fin n) (Fin r) (Fin.fintype n) (Fin.fintype r)) fun (a b : Sum (Fin n) (Fin r)) ↦
                  @instDecidableEqSum (Fin n) (Fin r) (instDecidableEqFin n) (instDecidableEqFin r) a b))))
          (@MulOneClass.toMulOne
            (Matrix (Fin (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n r))
              (Fin (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n r)) k)
            (@MulZeroOneClass.toMulOneClass
              (Matrix (Fin (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n r))
                (Fin (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n r)) k)
              (@instMulZeroOneClassOfSemiring
                (Matrix (Fin (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n r))
                  (Fin (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n r)) k)
                (@Matrix.semiring (Fin (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n r)) k
                  (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst)))
                  (Fin.fintype (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n r))
                  (instDecidableEqFin (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n r))))))
          (@MulEquiv.toMonoidHom (Matrix (Sum (Fin n) (Fin r)) (Sum (Fin n) (Fin r)) k)
            (Matrix (Fin (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n r))
              (Fin (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n r)) k)
            (@MulZeroOneClass.toMulOneClass (Matrix (Sum (Fin n) (Fin r)) (Sum (Fin n) (Fin r)) k)
              (@instMulZeroOneClassOfSemiring (Matrix (Sum (Fin n) (Fin r)) (Sum (Fin n) (Fin r)) k)
                (@Matrix.semiring (Sum (Fin n) (Fin r)) k
                  (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst)))
                  (@instFintypeSum (Fin n) (Fin r) (Fin.fintype n) (Fin.fintype r)) fun (a b : Sum (Fin n) (Fin r)) ↦
                  @instDecidableEqSum (Fin n) (Fin r) (instDecidableEqFin n) (instDecidableEqFin r) a b)))
            (@MulZeroOneClass.toMulOneClass
              (Matrix (Fin (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n r))
                (Fin (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n r)) k)
              (@instMulZeroOneClassOfSemiring
                (Matrix (Fin (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n r))
                  (Fin (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n r)) k)
                (@Matrix.semiring (Fin (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n r)) k
                  (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst)))
                  (Fin.fintype (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n r))
                  (instDecidableEqFin (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n r)))))
            (@AlgEquiv.toMulEquiv k (Matrix (Sum (Fin n) (Fin r)) (Sum (Fin n) (Fin r)) k)
              (Matrix (Fin (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n r))
                (Fin (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n r)) k)
              (@Semifield.toCommSemiring k (@Field.toSemifield k inst))
              (@Matrix.semiring (Sum (Fin n) (Fin r)) k
                (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst)))
                (@instFintypeSum (Fin n) (Fin r) (Fin.fintype n) (Fin.fintype r)) fun (a b : Sum (Fin n) (Fin r)) ↦
                @instDecidableEqSum (Fin n) (Fin r) (instDecidableEqFin n) (instDecidableEqFin r) a b)
              (@Matrix.semiring (Fin (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n r)) k
                (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst)))
                (Fin.fintype (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n r))
                (instDecidableEqFin (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n r)))
              (@Matrix.instAlgebra (Sum (Fin n) (Fin r)) k k
                (@instFintypeSum (Fin n) (Fin r) (Fin.fintype n) (Fin.fintype r))
                (fun (a b : Sum (Fin n) (Fin r)) ↦
                  @instDecidableEqSum (Fin n) (Fin r) (instDecidableEqFin n) (instDecidableEqFin r) a b)
                (@Semifield.toCommSemiring k (@Field.toSemifield k inst))
                (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst)))
                (@Algebra.id k (@Semifield.toCommSemiring k (@Field.toSemifield k inst))))
              (@Matrix.instAlgebra (Fin (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n r)) k k
                (Fin.fintype (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n r))
                (instDecidableEqFin (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n r))
                (@Semifield.toCommSemiring k (@Field.toSemifield k inst))
                (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst)))
                (@Algebra.id k (@Semifield.toCommSemiring k (@Field.toSemifield k inst))))
              (@Matrix.reindexAlgEquiv (Sum (Fin n) (Fin r)) (Fin (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n r)) k
                k (@Semifield.toCommSemiring k (@Field.toSemifield k inst))
                (Fin.fintype (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n r))
                (@instFintypeSum (Fin n) (Fin r) (Fin.fintype n) (Fin.fintype r))
                (fun (a b : Sum (Fin n) (Fin r)) ↦
                  @instDecidableEqSum (Fin n) (Fin r) (instDecidableEqFin n) (instDecidableEqFin r) a b)
                (instDecidableEqFin (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n r))
                (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst)))
                (@Algebra.id k (@Semifield.toCommSemiring k (@Field.toSemifield k inst))) (@finSumFinEquiv n r))))
          (@UpperTheory.Reformulated.B.BlockHomomorphism.blkHom k inst n r))
noncomputable def UpperTheory.Reformulated.B.BlockHomomorphism.blkAt :
    (k : Type) →
      [inst : Field k] →
        (n N : Nat) →
          @LE.le Nat instLENat n N →
            @MonoidHom
              (@Matrix.GeneralLinearGroup (Fin n) k (instDecidableEqFin n) (Fin.fintype n)
                (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst))))
              (@Matrix.GeneralLinearGroup (Fin N) k (instDecidableEqFin N) (Fin.fintype N)
                (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst))))
              (@MulOneClass.toMulOne
                (@Matrix.GeneralLinearGroup (Fin n) k (instDecidableEqFin n) (Fin.fintype n)
                  (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst))))
                (@Units.instMulOneClass (Matrix (Fin n) (Fin n) k)
                  (@Semiring.toMonoid (Matrix (Fin n) (Fin n) k)
                    (@Matrix.semiring (Fin n) k
                      (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst)))
                      (Fin.fintype n) (instDecidableEqFin n)))))
              (@MulOneClass.toMulOne
                (@Matrix.GeneralLinearGroup (Fin N) k (instDecidableEqFin N) (Fin.fintype N)
                  (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst))))
                (@Units.instMulOneClass (Matrix (Fin N) (Fin N) k)
                  (@Semiring.toMonoid (Matrix (Fin N) (Fin N) k)
                    (@Matrix.semiring (Fin N) k
                      (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst)))
                      (Fin.fintype N) (instDecidableEqFin N))))) :=
    fun (k : Type) [inst : Field k] (n N : Nat) (h : @LE.le Nat instLENat n N) ↦
      @MonoidHom.comp
        (@Matrix.GeneralLinearGroup (Fin n) k (instDecidableEqFin n) (Fin.fintype n)
          (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst))))
        (@Matrix.GeneralLinearGroup
          (Fin
            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n (@HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) N n)))
          k
          (instDecidableEqFin
            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n (@HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) N n)))
          (Fin.fintype
            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n (@HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) N n)))
          (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst))))
        (@Matrix.GeneralLinearGroup (Fin N) k (instDecidableEqFin N) (Fin.fintype N)
          (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst))))
        (@MulOneClass.toMulOne
          (@Matrix.GeneralLinearGroup (Fin n) k (instDecidableEqFin n) (Fin.fintype n)
            (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst))))
          (@Units.instMulOneClass (Matrix (Fin n) (Fin n) k)
            (@Semiring.toMonoid (Matrix (Fin n) (Fin n) k)
              (@Matrix.semiring (Fin n) k
                (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst)))
                (Fin.fintype n) (instDecidableEqFin n)))))
        (@MulOneClass.toMulOne
          (@Matrix.GeneralLinearGroup
            (Fin
              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n (@HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) N n)))
            k
            (instDecidableEqFin
              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n (@HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) N n)))
            (Fin.fintype
              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n (@HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) N n)))
            (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst))))
          (@Units.instMulOneClass
            (Matrix
              (Fin
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                  (@HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) N n)))
              (Fin
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                  (@HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) N n)))
              k)
            (@Semiring.toMonoid
              (Matrix
                (Fin
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                    (@HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) N n)))
                (Fin
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                    (@HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) N n)))
                k)
              (@Matrix.semiring
                (Fin
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                    (@HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) N n)))
                k (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst)))
                (Fin.fintype
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                    (@HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) N n)))
                (instDecidableEqFin
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                    (@HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) N n)))))))
        (@MulOneClass.toMulOne
          (@Matrix.GeneralLinearGroup (Fin N) k (instDecidableEqFin N) (Fin.fintype N)
            (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst))))
          (@Units.instMulOneClass (Matrix (Fin N) (Fin N) k)
            (@Semiring.toMonoid (Matrix (Fin N) (Fin N) k)
              (@Matrix.semiring (Fin N) k
                (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst)))
                (Fin.fintype N) (instDecidableEqFin N)))))
        (@UpperTheory.Reformulated.B.BlockHomomorphism.glCongr k inst
          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n (@HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) N n)) N
          (@Nat.add_sub_cancel' N n h))
        (@UpperTheory.Reformulated.B.BlockHomomorphism.blkGL k inst n (@HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) N n))
noncomputable def UpperTheory.Reformulated.B.BlockHomomorphism.FixK :
    {k : Type} →
      [inst : Field k] →
        {m N : Nat} →
          @LE.le Nat instLENat
              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              N →
            {V : Type} →
              [inst_1 : AddCommGroup V] →
                [inst_2 : @_root_.Module Complex V Complex.instSemiring (@AddCommGroup.toAddCommMonoid V inst_1)] →
                  @Representation Complex
                      (@Matrix.GeneralLinearGroup (Fin N) k (instDecidableEqFin N) (Fin.fintype N)
                        (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst))))
                      V Complex.instSemiring
                      (@Units.instMonoid (Matrix (Fin N) (Fin N) k)
                        (@Semiring.toMonoid (Matrix (Fin N) (Fin N) k)
                          (@Matrix.semiring (Fin N) k
                            (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst)))
                            (Fin.fintype N) (instDecidableEqFin N))))
                      (@AddCommGroup.toAddCommMonoid V inst_1) inst_2 →
                    @Subgroup
                        (@Matrix.GeneralLinearGroup
                          (Fin
                            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                          k
                          (instDecidableEqFin
                            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                          (Fin.fintype
                            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                          (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst))))
                        (@Units.instGroup
                          (Matrix
                            (Fin
                              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                                (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                            (Fin
                              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                                (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                            k)
                          (@Semiring.toMonoid
                            (Matrix
                              (Fin
                                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                              (Fin
                                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                              k)
                            (@Matrix.semiring
                              (Fin
                                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                              k
                              (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst)))
                              (Fin.fintype
                                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                              (instDecidableEqFin
                                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))) →
                      V → Prop :=
    fun {k : Type} [inst : Field k] {m N : Nat}
        (h :
          @LE.le Nat instLENat
            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            N)
        {V : Type} [inst_1 : AddCommGroup V]
        [inst_2 : @_root_.Module Complex V Complex.instSemiring (@AddCommGroup.toAddCommMonoid V inst_1)]
        (π :
          @Representation Complex
            (@Matrix.GeneralLinearGroup (Fin N) k (instDecidableEqFin N) (Fin.fintype N)
              (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst))))
            V Complex.instSemiring
            (@Units.instMonoid (Matrix (Fin N) (Fin N) k)
              (@Semiring.toMonoid (Matrix (Fin N) (Fin N) k)
                (@Matrix.semiring (Fin N) k
                  (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst)))
                  (Fin.fintype N) (instDecidableEqFin N))))
            (@AddCommGroup.toAddCommMonoid V inst_1) inst_2)
        (K :
          @Subgroup
            (@Matrix.GeneralLinearGroup
              (Fin
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              k
              (instDecidableEqFin
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (Fin.fintype
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst))))
            (@Units.instGroup
              (Matrix
                (Fin
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (Fin
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                k)
              (@Semiring.toMonoid
                (Matrix
                  (Fin
                    (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  (Fin
                    (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  k)
                (@Matrix.semiring
                  (Fin
                    (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  k (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst)))
                  (Fin.fintype
                    (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  (instDecidableEqFin
                    (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))))
        (v : V) ↦
      ∀
        (g :
          @Matrix.GeneralLinearGroup
            (Fin
              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            k
            (instDecidableEqFin
              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (Fin.fintype
              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst)))),
        @Membership.mem
            (@Matrix.GeneralLinearGroup
              (Fin
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              k
              (instDecidableEqFin
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (Fin.fintype
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst))))
            (@Subgroup
              (@Matrix.GeneralLinearGroup
                (Fin
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                k
                (instDecidableEqFin
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (Fin.fintype
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst))))
              (@Units.instGroup
                (Matrix
                  (Fin
                    (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  (Fin
                    (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  k)
                (@Semiring.toMonoid
                  (Matrix
                    (Fin
                      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                    (Fin
                      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                    k)
                  (@Matrix.semiring
                    (Fin
                      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                    k (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst)))
                    (Fin.fintype
                      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                    (instDecidableEqFin
                      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))))
            (@SetLike.instMembership
              (@Subgroup
                (@Matrix.GeneralLinearGroup
                  (Fin
                    (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  k
                  (instDecidableEqFin
                    (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  (Fin.fintype
                    (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst))))
                (@Units.instGroup
                  (Matrix
                    (Fin
                      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                    (Fin
                      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                    k)
                  (@Semiring.toMonoid
                    (Matrix
                      (Fin
                        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                      (Fin
                        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                      k)
                    (@Matrix.semiring
                      (Fin
                        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                      k (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst)))
                      (Fin.fintype
                        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                      (instDecidableEqFin
                        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))))
              (@Matrix.GeneralLinearGroup
                (Fin
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                k
                (instDecidableEqFin
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (Fin.fintype
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst))))
              (@Subgroup.instSetLike
                (@Matrix.GeneralLinearGroup
                  (Fin
                    (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  k
                  (instDecidableEqFin
                    (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  (Fin.fintype
                    (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst))))
                (@Units.instGroup
                  (Matrix
                    (Fin
                      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                    (Fin
                      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                    k)
                  (@Semiring.toMonoid
                    (Matrix
                      (Fin
                        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                      (Fin
                        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                      k)
                    (@Matrix.semiring
                      (Fin
                        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                      k (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst)))
                      (Fin.fintype
                        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                      (instDecidableEqFin
                        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))))))
            K g →
          @Eq V
            (@DFunLike.coe
              (@LinearMap Complex Complex Complex.instSemiring Complex.instSemiring
                (@RingHom.id Complex (@Semiring.toNonAssocSemiring Complex Complex.instSemiring)) V V
                (@AddCommGroup.toAddCommMonoid V inst_1) (@AddCommGroup.toAddCommMonoid V inst_1) inst_2 inst_2)
              V (fun (x : V) ↦ V)
              (@LinearMap.instFunLike Complex Complex V V Complex.instSemiring Complex.instSemiring
                (@AddCommGroup.toAddCommMonoid V inst_1) (@AddCommGroup.toAddCommMonoid V inst_1) inst_2 inst_2
                (@RingHom.id Complex (@Semiring.toNonAssocSemiring Complex Complex.instSemiring)))
              (@DFunLike.coe
                (@Representation Complex
                  (@Matrix.GeneralLinearGroup (Fin N) k (instDecidableEqFin N) (Fin.fintype N)
                    (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst))))
                  V Complex.instSemiring
                  (@Units.instMonoid (Matrix (Fin N) (Fin N) k)
                    (@Semiring.toMonoid (Matrix (Fin N) (Fin N) k)
                      (@Matrix.semiring (Fin N) k
                        (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst)))
                        (Fin.fintype N) (instDecidableEqFin N))))
                  (@AddCommGroup.toAddCommMonoid V inst_1) inst_2)
                (@Matrix.GeneralLinearGroup (Fin N) k (instDecidableEqFin N) (Fin.fintype N)
                  (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst))))
                (fun
                    (x :
                      @Matrix.GeneralLinearGroup (Fin N) k (instDecidableEqFin N) (Fin.fintype N)
                        (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst)))) ↦
                  @LinearMap Complex Complex Complex.instSemiring Complex.instSemiring
                    (@RingHom.id Complex (@Semiring.toNonAssocSemiring Complex Complex.instSemiring)) V V
                    (@AddCommGroup.toAddCommMonoid V inst_1) (@AddCommGroup.toAddCommMonoid V inst_1) inst_2 inst_2)
                (@MonoidHom.instFunLike
                  (@Matrix.GeneralLinearGroup (Fin N) k (instDecidableEqFin N) (Fin.fintype N)
                    (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst))))
                  (@LinearMap Complex Complex Complex.instSemiring Complex.instSemiring
                    (@RingHom.id Complex (@Semiring.toNonAssocSemiring Complex Complex.instSemiring)) V V
                    (@AddCommGroup.toAddCommMonoid V inst_1) (@AddCommGroup.toAddCommMonoid V inst_1) inst_2 inst_2)
                  (@MulOneClass.toMulOne
                    (@Matrix.GeneralLinearGroup (Fin N) k (instDecidableEqFin N) (Fin.fintype N)
                      (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst))))
                    (@Monoid.toMulOneClass
                      (@Matrix.GeneralLinearGroup (Fin N) k (instDecidableEqFin N) (Fin.fintype N)
                        (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst))))
                      (@Units.instMonoid (Matrix (Fin N) (Fin N) k)
                        (@Semiring.toMonoid (Matrix (Fin N) (Fin N) k)
                          (@Matrix.semiring (Fin N) k
                            (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst)))
                            (Fin.fintype N) (instDecidableEqFin N))))))
                  (@MulOneClass.toMulOne
                    (@LinearMap Complex Complex Complex.instSemiring Complex.instSemiring
                      (@RingHom.id Complex (@Semiring.toNonAssocSemiring Complex Complex.instSemiring)) V V
                      (@AddCommGroup.toAddCommMonoid V inst_1) (@AddCommGroup.toAddCommMonoid V inst_1) inst_2 inst_2)
                    (@MulZeroOneClass.toMulOneClass
                      (@LinearMap Complex Complex Complex.instSemiring Complex.instSemiring
                        (@RingHom.id Complex (@Semiring.toNonAssocSemiring Complex Complex.instSemiring)) V V
                        (@AddCommGroup.toAddCommMonoid V inst_1) (@AddCommGroup.toAddCommMonoid V inst_1) inst_2 inst_2)
                      (@instMulZeroOneClassOfSemiring
                        (@LinearMap Complex Complex Complex.instSemiring Complex.instSemiring
                          (@RingHom.id Complex (@Semiring.toNonAssocSemiring Complex Complex.instSemiring)) V V
                          (@AddCommGroup.toAddCommMonoid V inst_1) (@AddCommGroup.toAddCommMonoid V inst_1) inst_2 inst_2)
                        (@Module.End.instSemiring Complex V Complex.instSemiring (@AddCommGroup.toAddCommMonoid V inst_1)
                          inst_2)))))
                π
                (@DFunLike.coe
                  (@MonoidHom
                    (@Matrix.GeneralLinearGroup
                      (Fin
                        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                      k
                      (instDecidableEqFin
                        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                      (Fin.fintype
                        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                      (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst))))
                    (@Matrix.GeneralLinearGroup (Fin N) k (instDecidableEqFin N) (Fin.fintype N)
                      (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst))))
                    (@MulOneClass.toMulOne
                      (@Matrix.GeneralLinearGroup
                        (Fin
                          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                        k
                        (instDecidableEqFin
                          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                        (Fin.fintype
                          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                        (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst))))
                      (@Units.instMulOneClass
                        (Matrix
                          (Fin
                            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                          (Fin
                            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                          k)
                        (@Semiring.toMonoid
                          (Matrix
                            (Fin
                              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                                (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                            (Fin
                              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                                (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                            k)
                          (@Matrix.semiring
                            (Fin
                              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                                (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                            k (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst)))
                            (Fin.fintype
                              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                                (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                            (instDecidableEqFin
                              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                                (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))))
                    (@MulOneClass.toMulOne
                      (@Matrix.GeneralLinearGroup (Fin N) k (instDecidableEqFin N) (Fin.fintype N)
                        (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst))))
                      (@Units.instMulOneClass (Matrix (Fin N) (Fin N) k)
                        (@Semiring.toMonoid (Matrix (Fin N) (Fin N) k)
                          (@Matrix.semiring (Fin N) k
                            (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst)))
                            (Fin.fintype N) (instDecidableEqFin N))))))
                  (@Matrix.GeneralLinearGroup
                    (Fin
                      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                    k
                    (instDecidableEqFin
                      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                    (Fin.fintype
                      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                    (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst))))
                  (fun
                      (x :
                        @Matrix.GeneralLinearGroup
                          (Fin
                            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                          k
                          (instDecidableEqFin
                            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                          (Fin.fintype
                            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                          (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst)))) ↦
                    @Matrix.GeneralLinearGroup (Fin N) k (instDecidableEqFin N) (Fin.fintype N)
                      (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst))))
                  (@MonoidHom.instFunLike
                    (@Matrix.GeneralLinearGroup
                      (Fin
                        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                      k
                      (instDecidableEqFin
                        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                      (Fin.fintype
                        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                      (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst))))
                    (@Matrix.GeneralLinearGroup (Fin N) k (instDecidableEqFin N) (Fin.fintype N)
                      (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst))))
                    (@MulOneClass.toMulOne
                      (@Matrix.GeneralLinearGroup
                        (Fin
                          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                        k
                        (instDecidableEqFin
                          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                        (Fin.fintype
                          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                        (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst))))
                      (@Units.instMulOneClass
                        (Matrix
                          (Fin
                            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                          (Fin
                            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                          k)
                        (@Semiring.toMonoid
                          (Matrix
                            (Fin
                              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                                (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                            (Fin
                              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                                (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                            k)
                          (@Matrix.semiring
                            (Fin
                              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                                (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                            k (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst)))
                            (Fin.fintype
                              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                                (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                            (instDecidableEqFin
                              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                                (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))))
                    (@MulOneClass.toMulOne
                      (@Matrix.GeneralLinearGroup (Fin N) k (instDecidableEqFin N) (Fin.fintype N)
                        (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst))))
                      (@Units.instMulOneClass (Matrix (Fin N) (Fin N) k)
                        (@Semiring.toMonoid (Matrix (Fin N) (Fin N) k)
                          (@Matrix.semiring (Fin N) k
                            (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst)))
                            (Fin.fintype N) (instDecidableEqFin N))))))
                  (@UpperTheory.Reformulated.B.BlockHomomorphism.blkAt k inst
                    (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                      (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                    N h)
                  g))
              v)
            v
theorem UpperTheory.Reformulated.B.BlockHomomorphism.aux9 :
    ∀ {m N : Nat}
      {h :
        @LE.le Nat instLENat
          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          N},
      Not
          (@LE.le Nat instLENat
            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            N) →
        False := by
  intro m N h a
  omega
def UpperTheory.Reformulated.B.BlockHomomorphism.fixer {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ G V) (v : V) : Subgroup G where
  carrier := {g | π g v = v}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [map_mul, Module.End.mul_apply, hb, ha]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    calc π a⁻¹ v = π a⁻¹ (π a v) := by rw [ha]
      _ = v := by rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]


