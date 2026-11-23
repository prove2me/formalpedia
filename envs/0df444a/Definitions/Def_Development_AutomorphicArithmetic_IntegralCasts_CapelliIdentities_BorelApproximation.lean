-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_BorelApproximation
-- name    : Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_BorelApproximation
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:24:46.690649+00:00
-- url     : https://prove2.me/theorems/5d0c9304-ddcd-4eb5-ae27-8be9b524fa37
-- title:
--   Borel Approximation
-- statement:
--   Definitions and structural lemmas for Borel Approximation, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/BorelApproximation.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
@[reducible] noncomputable def UpperTheory.Reformulated.B.BorelApproximation.Pl :
    (E : Type) → [inst : Field E] → [@NumberField E inst] → Type :=
    fun (E : Type) [inst : Field E] [@NumberField E inst] ↦
      @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers E inst)
        (@NumberField.instCommRingRingOfIntegers E inst)
@[reducible] noncomputable def UpperTheory.Reformulated.B.BorelApproximation.GLw :
    {E : Type} → [inst : Field E] → [inst_1 : @NumberField E inst] → Nat → @UpperTheory.Reformulated.B.BorelApproximation.Pl E inst inst_1 → Type :=
    fun {E : Type} [inst : Field E] [inst_1 : @NumberField E inst] (n : Nat) (w : @UpperTheory.Reformulated.B.BorelApproximation.Pl E inst inst_1) ↦
      @Matrix.GeneralLinearGroup (Fin n)
        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
          (@NumberField.instCommRingRingOfIntegers E inst) (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1)
          E inst (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
          (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
        (instDecidableEqFin n) (Fin.fintype n)
        (@DivisionSemiring.toSemiring
          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
            (@NumberField.instCommRingRingOfIntegers E inst)
            (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
            (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
            (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
          (@Semifield.toDivisionSemiring
            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
              (@NumberField.instCommRingRingOfIntegers E inst)
              (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
              (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
              (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
            (@Field.toSemifield
              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                (@NumberField.instCommRingRingOfIntegers E inst)
                (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers E inst)
                (@NumberField.instCommRingRingOfIntegers E inst)
                (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w))))
theorem UpperTheory.Reformulated.B.BorelApproximation.aux3 :
    ∀ (k : Type) [inst : Field k],
      @SubsemiringClass (@Subring k (@Ring.toNonAssocRing k (@CommRing.toRing k (@Field.toCommRing k inst)))) k
        (@NonAssocRing.toNonAssocSemiring k
          (@NonAssocCommRing.toNonAssocRing k (@CommRing.toNonAssocCommRing k (@Field.toCommRing k inst))))
        (@Subring.instSetLike k (@Ring.toNonAssocRing k (@CommRing.toRing k (@Field.toCommRing k inst)))) := by
  intro k _
  infer_instance
theorem UpperTheory.Reformulated.B.BorelApproximation.aux4 :
    ∀ (k : Type) [inst : Field k]
      [inst_1 :
        @ValuativeRel k (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst)))]
      [inst_2 : TopologicalSpace k] [@IsNonarchimedeanLocalField k inst inst_1 inst_2],
      @IsLocalRing
        (↥(@Valuation.integer k
            (@ValuativeRel.ValueGroupWithZero k (@Ring.toSemiring k (@DivisionRing.toRing k (@Field.toDivisionRing k inst)))
              inst_1)
            (@DivisionRing.toRing k (@Field.toDivisionRing k inst))
            (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero k
              (@Ring.toSemiring k (@DivisionRing.toRing k (@Field.toDivisionRing k inst))) inst_1)
            (@ValuativeRel.valuation k (@DivisionRing.toRing k (@Field.toDivisionRing k inst)) inst_1)))
        (@CommSemiring.toSemiring
          (↥(@Valuation.integer k
              (@ValuativeRel.ValueGroupWithZero k
                (@Ring.toSemiring k (@DivisionRing.toRing k (@Field.toDivisionRing k inst))) inst_1)
              (@DivisionRing.toRing k (@Field.toDivisionRing k inst))
              (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero k
                (@Ring.toSemiring k (@DivisionRing.toRing k (@Field.toDivisionRing k inst))) inst_1)
              (@ValuativeRel.valuation k (@DivisionRing.toRing k (@Field.toDivisionRing k inst)) inst_1)))
          (@CommRing.toCommSemiring
            (↥(@Valuation.integer k
                (@ValuativeRel.ValueGroupWithZero k
                  (@Ring.toSemiring k (@DivisionRing.toRing k (@Field.toDivisionRing k inst))) inst_1)
                (@DivisionRing.toRing k (@Field.toDivisionRing k inst))
                (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero k
                  (@Ring.toSemiring k (@DivisionRing.toRing k (@Field.toDivisionRing k inst))) inst_1)
                (@ValuativeRel.valuation k (@DivisionRing.toRing k (@Field.toDivisionRing k inst)) inst_1)))
            (@Subring.toCommRing k (@Field.toCommRing k inst)
              (@Valuation.integer k
                (@ValuativeRel.ValueGroupWithZero k
                  (@Ring.toSemiring k (@DivisionRing.toRing k (@Field.toDivisionRing k inst))) inst_1)
                (@DivisionRing.toRing k (@Field.toDivisionRing k inst))
                (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero k
                  (@Ring.toSemiring k (@DivisionRing.toRing k (@Field.toDivisionRing k inst))) inst_1)
                (@ValuativeRel.valuation k (@DivisionRing.toRing k (@Field.toDivisionRing k inst)) inst_1))))) := by
  intro k _ _ _ _
  infer_instance
noncomputable def UpperTheory.Reformulated.B.BorelApproximation.blk :
    {α n : Type} → {m : α → Type} → Equiv (@Sigma α fun (a : α) ↦ m a) n → n → α :=
    fun {α n : Type} {m : α → Type} (e : Equiv (@Sigma α fun (a : α) ↦ m a) n) (i : n) ↦
      @Sigma.fst α (fun (a : α) ↦ m a)
        (@DFunLike.coe (Equiv n (@Sigma α fun (a : α) ↦ m a)) n (fun (x : n) ↦ @Sigma α fun (a : α) ↦ m a)
          (@EquivLike.toFunLike (Equiv n (@Sigma α fun (a : α) ↦ m a)) n (@Sigma α fun (a : α) ↦ m a)
            (@Equiv.instEquivLike n (@Sigma α fun (a : α) ↦ m a)))
          (@Equiv.symm (@Sigma α fun (a : α) ↦ m a) n e) i)
theorem UpperTheory.Reformulated.B.BorelApproximation.aux6 :
    ∀ (R : Type) [inst : CommRing R] {α n : Type} {m : α → Type} [inst_1 : LinearOrder α] [inst_2 : Fintype n]
      [inst_3 : DecidableEq n] (e : Equiv (@Sigma α fun (a : α) ↦ m a) n)
      {x y : @Matrix.GeneralLinearGroup n R inst_3 inst_2 (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))},
      @Membership.mem
          (@Matrix.GeneralLinearGroup n R inst_3 inst_2 (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
          (Set
            (@Matrix.GeneralLinearGroup n R inst_3 inst_2 (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
          (@Set.instMembership
            (@Matrix.GeneralLinearGroup n R inst_3 inst_2 (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
          (@Set.ofPred
            (@Matrix.GeneralLinearGroup n R inst_3 inst_2 (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
            fun
              (g :
                @Matrix.GeneralLinearGroup n R inst_3 inst_2
                  (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))) ↦
            @Matrix.BlockTriangular α n R
              (@Preorder.toLT α
                (@PartialOrder.toPreorder α
                  (@SemilatticeInf.toPartialOrder α
                    (@Lattice.toSemilatticeInf α
                      (@DistribLattice.toLattice α (@instDistribLatticeOfLinearOrder α inst_1))))))
              (@MulZeroClass.toZero R
                (@instMulZeroClassOfSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
              (@Units.val (Matrix n n R)
                (@Semiring.toMonoid (Matrix n n R)
                  (@Matrix.semiring n R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)) inst_2 inst_3))
                g)
              (@UpperTheory.Reformulated.B.BorelApproximation.blk α n m e))
          x →
        @Membership.mem
            (@Matrix.GeneralLinearGroup n R inst_3 inst_2 (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
            (Set
              (@Matrix.GeneralLinearGroup n R inst_3 inst_2 (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
            (@Set.instMembership
              (@Matrix.GeneralLinearGroup n R inst_3 inst_2 (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
            (@Set.ofPred
              (@Matrix.GeneralLinearGroup n R inst_3 inst_2 (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
              fun
                (g :
                  @Matrix.GeneralLinearGroup n R inst_3 inst_2
                    (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))) ↦
              @Matrix.BlockTriangular α n R
                (@Preorder.toLT α
                  (@PartialOrder.toPreorder α
                    (@SemilatticeInf.toPartialOrder α
                      (@Lattice.toSemilatticeInf α
                        (@DistribLattice.toLattice α (@instDistribLatticeOfLinearOrder α inst_1))))))
                (@MulZeroClass.toZero R
                  (@instMulZeroClassOfSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                (@Units.val (Matrix n n R)
                  (@Semiring.toMonoid (Matrix n n R)
                    (@Matrix.semiring n R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)) inst_2 inst_3))
                  g)
                (@UpperTheory.Reformulated.B.BorelApproximation.blk α n m e))
            y →
          @Membership.mem
            (@Matrix.GeneralLinearGroup n R inst_3 inst_2 (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
            (Set
              (@Matrix.GeneralLinearGroup n R inst_3 inst_2 (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
            (@Set.instMembership
              (@Matrix.GeneralLinearGroup n R inst_3 inst_2 (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
            (@Set.ofPred
              (@Matrix.GeneralLinearGroup n R inst_3 inst_2 (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
              fun
                (g :
                  @Matrix.GeneralLinearGroup n R inst_3 inst_2
                    (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))) ↦
              @Matrix.BlockTriangular α n R
                (@Preorder.toLT α
                  (@PartialOrder.toPreorder α
                    (@SemilatticeInf.toPartialOrder α
                      (@Lattice.toSemilatticeInf α
                        (@DistribLattice.toLattice α (@instDistribLatticeOfLinearOrder α inst_1))))))
                (@MulZeroClass.toZero R
                  (@instMulZeroClassOfSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                (@Units.val (Matrix n n R)
                  (@Semiring.toMonoid (Matrix n n R)
                    (@Matrix.semiring n R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)) inst_2 inst_3))
                  g)
                (@UpperTheory.Reformulated.B.BorelApproximation.blk α n m e))
            (@HMul.hMul
              (@Matrix.GeneralLinearGroup n R inst_3 inst_2 (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
              (@Matrix.GeneralLinearGroup n R inst_3 inst_2 (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
              (@Matrix.GeneralLinearGroup n R inst_3 inst_2 (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
              (@instHMul
                (@Matrix.GeneralLinearGroup n R inst_3 inst_2
                  (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                (@MulOne.toMul
                  (@Matrix.GeneralLinearGroup n R inst_3 inst_2
                    (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                  (@MulOneClass.toMulOne
                    (@Matrix.GeneralLinearGroup n R inst_3 inst_2
                      (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                    (@Monoid.toMulOneClass
                      (@Matrix.GeneralLinearGroup n R inst_3 inst_2
                        (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                      (@DivInvMonoid.toMonoid
                        (@Matrix.GeneralLinearGroup n R inst_3 inst_2
                          (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                        (@Group.toDivInvMonoid
                          (@Matrix.GeneralLinearGroup n R inst_3 inst_2
                            (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                          (@Units.instGroup (Matrix n n R)
                            (@Semiring.toMonoid (Matrix n n R)
                              (@Matrix.semiring n R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)) inst_2
                                inst_3)))))))))
              x y) := by
  intro R _ α n m _ _ _ e x y hx hy
  exact Matrix.BlockTriangular.mul hx hy
theorem UpperTheory.Reformulated.B.BorelApproximation.aux7 :
    ∀ (R : Type) [inst : CommRing R] {α n : Type} {m : α → Type} [inst_1 : LinearOrder α] [inst_2 : Fintype n]
      [inst_3 : DecidableEq n] (e : Equiv (@Sigma α fun (a : α) ↦ m a) n),
      @Membership.mem
        (@Matrix.GeneralLinearGroup n R inst_3 inst_2 (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
        (Set (@Matrix.GeneralLinearGroup n R inst_3 inst_2 (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
        (@Set.instMembership
          (@Matrix.GeneralLinearGroup n R inst_3 inst_2 (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
        (@Set.ofPred
          (@Matrix.GeneralLinearGroup n R inst_3 inst_2 (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
          fun
            (g :
              @Matrix.GeneralLinearGroup n R inst_3 inst_2 (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))) ↦
          @Matrix.BlockTriangular α n R
            (@Preorder.toLT α
              (@PartialOrder.toPreorder α
                (@SemilatticeInf.toPartialOrder α
                  (@Lattice.toSemilatticeInf α (@DistribLattice.toLattice α (@instDistribLatticeOfLinearOrder α inst_1))))))
            (@MulZeroClass.toZero R
              (@instMulZeroClassOfSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
            (@Units.val (Matrix n n R)
              (@Semiring.toMonoid (Matrix n n R)
                (@Matrix.semiring n R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)) inst_2 inst_3))
              g)
            (@UpperTheory.Reformulated.B.BorelApproximation.blk α n m e))
        (@OfNat.ofNat
          (@Matrix.GeneralLinearGroup n R inst_3 inst_2 (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
          (nat_lit 1)
          (@One.toOfNat1
            (@Matrix.GeneralLinearGroup n R inst_3 inst_2 (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
            (@MulOne.toOne
              (@Matrix.GeneralLinearGroup n R inst_3 inst_2 (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
              (@MulOneClass.toMulOne
                (@Matrix.GeneralLinearGroup n R inst_3 inst_2
                  (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                (@Monoid.toMulOneClass
                  (@Matrix.GeneralLinearGroup n R inst_3 inst_2
                    (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                  (@DivInvMonoid.toMonoid
                    (@Matrix.GeneralLinearGroup n R inst_3 inst_2
                      (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                    (@Group.toDivInvMonoid
                      (@Matrix.GeneralLinearGroup n R inst_3 inst_2
                        (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                      (@Units.instGroup (Matrix n n R)
                        (@Semiring.toMonoid (Matrix n n R)
                          (@Matrix.semiring n R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)) inst_2
                            inst_3)))))))))) := by
  intro R _ α n m _ _ _ e
  exact Matrix.blockTriangular_one
theorem UpperTheory.Reformulated.B.BorelApproximation.aux8 :
    ∀ (R : Type) [inst : CommRing R] {α n : Type} {m : α → Type} [inst_1 : LinearOrder α] [inst_2 : Fintype n]
      [inst_3 : DecidableEq n] (e : Equiv (@Sigma α fun (a : α) ↦ m a) n)
      {x : @Matrix.GeneralLinearGroup n R inst_3 inst_2 (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))},
      @Membership.mem
          (@Matrix.GeneralLinearGroup n R inst_3 inst_2 (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
          (Set
            (@Matrix.GeneralLinearGroup n R inst_3 inst_2 (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
          (@Set.instMembership
            (@Matrix.GeneralLinearGroup n R inst_3 inst_2 (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
          (@Set.ofPred
            (@Matrix.GeneralLinearGroup n R inst_3 inst_2 (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
            fun
              (g :
                @Matrix.GeneralLinearGroup n R inst_3 inst_2
                  (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))) ↦
            @Matrix.BlockTriangular α n R
              (@Preorder.toLT α
                (@PartialOrder.toPreorder α
                  (@SemilatticeInf.toPartialOrder α
                    (@Lattice.toSemilatticeInf α
                      (@DistribLattice.toLattice α (@instDistribLatticeOfLinearOrder α inst_1))))))
              (@MulZeroClass.toZero R
                (@instMulZeroClassOfSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
              (@Units.val (Matrix n n R)
                (@Semiring.toMonoid (Matrix n n R)
                  (@Matrix.semiring n R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)) inst_2 inst_3))
                g)
              (@UpperTheory.Reformulated.B.BorelApproximation.blk α n m e))
          x →
        @Membership.mem
          (@Matrix.GeneralLinearGroup n R inst_3 inst_2 (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
          (Set
            (@Matrix.GeneralLinearGroup n R inst_3 inst_2 (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
          (@Set.instMembership
            (@Matrix.GeneralLinearGroup n R inst_3 inst_2 (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
          (@Set.ofPred
            (@Matrix.GeneralLinearGroup n R inst_3 inst_2 (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
            fun
              (g :
                @Matrix.GeneralLinearGroup n R inst_3 inst_2
                  (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))) ↦
            @Matrix.BlockTriangular α n R
              (@Preorder.toLT α
                (@PartialOrder.toPreorder α
                  (@SemilatticeInf.toPartialOrder α
                    (@Lattice.toSemilatticeInf α
                      (@DistribLattice.toLattice α (@instDistribLatticeOfLinearOrder α inst_1))))))
              (@MulZeroClass.toZero R
                (@instMulZeroClassOfSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
              (@Units.val (Matrix n n R)
                (@Semiring.toMonoid (Matrix n n R)
                  (@Matrix.semiring n R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)) inst_2 inst_3))
                g)
              (@UpperTheory.Reformulated.B.BorelApproximation.blk α n m e))
          (@Inv.inv
            (@Matrix.GeneralLinearGroup n R inst_3 inst_2 (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
            (@InvOneClass.toInv
              (@Matrix.GeneralLinearGroup n R inst_3 inst_2 (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
              (@DivInvOneMonoid.toInvOneClass
                (@Matrix.GeneralLinearGroup n R inst_3 inst_2
                  (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                (@DivisionMonoid.toDivInvOneMonoid
                  (@Matrix.GeneralLinearGroup n R inst_3 inst_2
                    (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                  (@Group.toDivisionMonoid
                    (@Matrix.GeneralLinearGroup n R inst_3 inst_2
                      (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                    (@Units.instGroup (Matrix n n R)
                      (@Semiring.toMonoid (Matrix n n R)
                        (@Matrix.semiring n R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)) inst_2
                          inst_3)))))))
            x) := by
  intro R _ α n m _ _ _ e x hx
  have hx : Matrix.BlockTriangular (x : Matrix n n R) (UpperTheory.Reformulated.B.BorelApproximation.blk e) := hx
  letI := x.invertible
  change Matrix.BlockTriangular ((x⁻¹ : GL n R) : Matrix n n R) (UpperTheory.Reformulated.B.BorelApproximation.blk e)
  rw [Matrix.coe_units_inv]
  exact Matrix.blockTriangular_inv_of_blockTriangular hx
noncomputable def UpperTheory.Reformulated.B.BorelApproximation.parab :
    (R : Type) →
      [inst : CommRing R] →
        {α n : Type} →
          {m : α → Type} →
            [LinearOrder α] →
              [inst_2 : Fintype n] →
                [inst_3 : DecidableEq n] →
                  Equiv (@Sigma α fun (a : α) ↦ m a) n →
                    @Subgroup
                      (@Matrix.GeneralLinearGroup n R inst_3 inst_2
                        (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                      (@Units.instGroup (Matrix n n R)
                        (@Semiring.toMonoid (Matrix n n R)
                          (@Matrix.semiring n R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)) inst_2
                            inst_3))) :=
    fun (R : Type) [inst : CommRing R] {α n : Type} {m : α → Type} [inst_1 : LinearOrder α] [inst_2 : Fintype n]
        [inst_3 : DecidableEq n] (e : Equiv (@Sigma α fun (a : α) ↦ m a) n) ↦
      @Subgroup.mk
        (@Matrix.GeneralLinearGroup n R inst_3 inst_2 (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
        (@Units.instGroup (Matrix n n R)
          (@Semiring.toMonoid (Matrix n n R)
            (@Matrix.semiring n R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)) inst_2 inst_3)))
        (@Submonoid.mk
          (@Matrix.GeneralLinearGroup n R inst_3 inst_2 (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
          (@Monoid.toMulOneClass
            (@Matrix.GeneralLinearGroup n R inst_3 inst_2 (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
            (@DivInvMonoid.toMonoid
              (@Matrix.GeneralLinearGroup n R inst_3 inst_2 (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
              (@Group.toDivInvMonoid
                (@Matrix.GeneralLinearGroup n R inst_3 inst_2
                  (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                (@Units.instGroup (Matrix n n R)
                  (@Semiring.toMonoid (Matrix n n R)
                    (@Matrix.semiring n R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)) inst_2 inst_3))))))
          (@Subsemigroup.mk
            (@Matrix.GeneralLinearGroup n R inst_3 inst_2 (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
            (@MulOne.toMul
              (@Matrix.GeneralLinearGroup n R inst_3 inst_2 (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
              (@MulOneClass.toMulOne
                (@Matrix.GeneralLinearGroup n R inst_3 inst_2
                  (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                (@Monoid.toMulOneClass
                  (@Matrix.GeneralLinearGroup n R inst_3 inst_2
                    (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                  (@DivInvMonoid.toMonoid
                    (@Matrix.GeneralLinearGroup n R inst_3 inst_2
                      (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                    (@Group.toDivInvMonoid
                      (@Matrix.GeneralLinearGroup n R inst_3 inst_2
                        (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                      (@Units.instGroup (Matrix n n R)
                        (@Semiring.toMonoid (Matrix n n R)
                          (@Matrix.semiring n R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)) inst_2
                            inst_3))))))))
            (@Set.ofPred
              (@Matrix.GeneralLinearGroup n R inst_3 inst_2 (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
              fun
                (g :
                  @Matrix.GeneralLinearGroup n R inst_3 inst_2
                    (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))) ↦
              @Matrix.BlockTriangular α n R
                (@Preorder.toLT α
                  (@PartialOrder.toPreorder α
                    (@SemilatticeInf.toPartialOrder α
                      (@Lattice.toSemilatticeInf α
                        (@DistribLattice.toLattice α (@instDistribLatticeOfLinearOrder α inst_1))))))
                (@MulZeroClass.toZero R
                  (@instMulZeroClassOfSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                (@Units.val (Matrix n n R)
                  (@Semiring.toMonoid (Matrix n n R)
                    (@Matrix.semiring n R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)) inst_2 inst_3))
                  g)
                (@UpperTheory.Reformulated.B.BorelApproximation.blk α n m e))
            (@UpperTheory.Reformulated.B.BorelApproximation.aux6 R inst α n m inst_1 inst_2 inst_3 e))
          (@UpperTheory.Reformulated.B.BorelApproximation.aux7 R inst α n m inst_1 inst_2 inst_3 e))
        (@UpperTheory.Reformulated.B.BorelApproximation.aux8 R inst α n m inst_1 inst_2 inst_3 e)
noncomputable def UpperTheory.Reformulated.B.BorelApproximation.points :
    (n : Type) → Equiv (@Sigma n fun (x : n) ↦ Unit) n :=
    fun (n : Type) ↦ @Equiv.sigmaUnique n (fun (x : n) ↦ Unit) fun (a : n) ↦ PUnit.instUnique
noncomputable def UpperTheory.Reformulated.B.BorelApproximation.borel :
    (R : Type) →
      [inst : CommRing R] →
        (n : Type) →
          [inst_1 : Fintype n] →
            [inst_2 : DecidableEq n] →
              [LinearOrder n] →
                @Subgroup
                  (@Matrix.GeneralLinearGroup n R inst_2 inst_1
                    (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                  (@Units.instGroup (Matrix n n R)
                    (@Semiring.toMonoid (Matrix n n R)
                      (@Matrix.semiring n R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)) inst_1 inst_2))) :=
    fun (R : Type) [inst : CommRing R] (n : Type) [inst_1 : Fintype n] [inst_2 : DecidableEq n] [inst_3 : LinearOrder n] ↦
      @UpperTheory.Reformulated.B.BorelApproximation.parab R inst n n (fun (a : n) ↦ Unit) inst_3 inst_1 inst_2 (UpperTheory.Reformulated.B.BorelApproximation.points n)
noncomputable def UpperTheory.Reformulated.B.BorelApproximation.iwahori :
    (k : Type) →
      [inst : Field k] →
        [inst_1 :
            @ValuativeRel k
              (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst)))] →
          [inst_2 : TopologicalSpace k] →
            [@IsNonarchimedeanLocalField k inst inst_1 inst_2] →
              (n : Type) →
                [inst_4 : Fintype n] →
                  [inst_5 : DecidableEq n] →
                    [LinearOrder n] →
                      @Subgroup
                        (@Matrix.GeneralLinearGroup n k inst_5 inst_4
                          (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst))))
                        (@Units.instGroup (Matrix n n k)
                          (@Semiring.toMonoid (Matrix n n k)
                            (@Matrix.semiring n k
                              (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst)))
                              inst_4 inst_5))) :=
    fun (k : Type) [inst : Field k]
        [inst_1 :
          @ValuativeRel k (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst)))]
        [inst_2 : TopologicalSpace k] [inst_3 : @IsNonarchimedeanLocalField k inst inst_1 inst_2] (n : Type)
        [inst_4 : Fintype n] [inst_5 : DecidableEq n] [inst_6 : LinearOrder n] ↦
      @Subgroup.map
        (@Matrix.GeneralLinearGroup n
          (↥(@Valuation.integer k
              (@ValuativeRel.ValueGroupWithZero k
                (@Ring.toSemiring k (@DivisionRing.toRing k (@Field.toDivisionRing k inst))) inst_1)
              (@DivisionRing.toRing k (@Field.toDivisionRing k inst))
              (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero k
                (@Ring.toSemiring k (@DivisionRing.toRing k (@Field.toDivisionRing k inst))) inst_1)
              (@ValuativeRel.valuation k (@DivisionRing.toRing k (@Field.toDivisionRing k inst)) inst_1)))
          inst_5 inst_4
          (@CommSemiring.toSemiring
            (↥(@Valuation.integer k
                (@ValuativeRel.ValueGroupWithZero k
                  (@Ring.toSemiring k (@DivisionRing.toRing k (@Field.toDivisionRing k inst))) inst_1)
                (@DivisionRing.toRing k (@Field.toDivisionRing k inst))
                (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero k
                  (@Ring.toSemiring k (@DivisionRing.toRing k (@Field.toDivisionRing k inst))) inst_1)
                (@ValuativeRel.valuation k (@DivisionRing.toRing k (@Field.toDivisionRing k inst)) inst_1)))
            (@CommRing.toCommSemiring
              (↥(@Valuation.integer k
                  (@ValuativeRel.ValueGroupWithZero k
                    (@Ring.toSemiring k (@DivisionRing.toRing k (@Field.toDivisionRing k inst))) inst_1)
                  (@DivisionRing.toRing k (@Field.toDivisionRing k inst))
                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero k
                    (@Ring.toSemiring k (@DivisionRing.toRing k (@Field.toDivisionRing k inst))) inst_1)
                  (@ValuativeRel.valuation k (@DivisionRing.toRing k (@Field.toDivisionRing k inst)) inst_1)))
              (@Subring.toCommRing k (@Field.toCommRing k inst)
                (@Valuation.integer k
                  (@ValuativeRel.ValueGroupWithZero k
                    (@Ring.toSemiring k (@DivisionRing.toRing k (@Field.toDivisionRing k inst))) inst_1)
                  (@DivisionRing.toRing k (@Field.toDivisionRing k inst))
                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero k
                    (@Ring.toSemiring k (@DivisionRing.toRing k (@Field.toDivisionRing k inst))) inst_1)
                  (@ValuativeRel.valuation k (@DivisionRing.toRing k (@Field.toDivisionRing k inst)) inst_1))))))
        (@Units.instGroup
          (Matrix n n
            ↥(@Valuation.integer k
                (@ValuativeRel.ValueGroupWithZero k
                  (@Ring.toSemiring k (@DivisionRing.toRing k (@Field.toDivisionRing k inst))) inst_1)
                (@DivisionRing.toRing k (@Field.toDivisionRing k inst))
                (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero k
                  (@Ring.toSemiring k (@DivisionRing.toRing k (@Field.toDivisionRing k inst))) inst_1)
                (@ValuativeRel.valuation k (@DivisionRing.toRing k (@Field.toDivisionRing k inst)) inst_1)))
          (@Semiring.toMonoid
            (Matrix n n
              ↥(@Valuation.integer k
                  (@ValuativeRel.ValueGroupWithZero k
                    (@Ring.toSemiring k (@DivisionRing.toRing k (@Field.toDivisionRing k inst))) inst_1)
                  (@DivisionRing.toRing k (@Field.toDivisionRing k inst))
                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero k
                    (@Ring.toSemiring k (@DivisionRing.toRing k (@Field.toDivisionRing k inst))) inst_1)
                  (@ValuativeRel.valuation k (@DivisionRing.toRing k (@Field.toDivisionRing k inst)) inst_1)))
            (@Matrix.semiring n
              (↥(@Valuation.integer k
                  (@ValuativeRel.ValueGroupWithZero k
                    (@Ring.toSemiring k (@DivisionRing.toRing k (@Field.toDivisionRing k inst))) inst_1)
                  (@DivisionRing.toRing k (@Field.toDivisionRing k inst))
                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero k
                    (@Ring.toSemiring k (@DivisionRing.toRing k (@Field.toDivisionRing k inst))) inst_1)
                  (@ValuativeRel.valuation k (@DivisionRing.toRing k (@Field.toDivisionRing k inst)) inst_1)))
              (@CommSemiring.toSemiring
                (↥(@Valuation.integer k
                    (@ValuativeRel.ValueGroupWithZero k
                      (@Ring.toSemiring k (@DivisionRing.toRing k (@Field.toDivisionRing k inst))) inst_1)
                    (@DivisionRing.toRing k (@Field.toDivisionRing k inst))
                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero k
                      (@Ring.toSemiring k (@DivisionRing.toRing k (@Field.toDivisionRing k inst))) inst_1)
                    (@ValuativeRel.valuation k (@DivisionRing.toRing k (@Field.toDivisionRing k inst)) inst_1)))
                (@CommRing.toCommSemiring
                  (↥(@Valuation.integer k
                      (@ValuativeRel.ValueGroupWithZero k
                        (@Ring.toSemiring k (@DivisionRing.toRing k (@Field.toDivisionRing k inst))) inst_1)
                      (@DivisionRing.toRing k (@Field.toDivisionRing k inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero k
                        (@Ring.toSemiring k (@DivisionRing.toRing k (@Field.toDivisionRing k inst))) inst_1)
                      (@ValuativeRel.valuation k (@DivisionRing.toRing k (@Field.toDivisionRing k inst)) inst_1)))
                  (@Subring.toCommRing k (@Field.toCommRing k inst)
                    (@Valuation.integer k
                      (@ValuativeRel.ValueGroupWithZero k
                        (@Ring.toSemiring k (@DivisionRing.toRing k (@Field.toDivisionRing k inst))) inst_1)
                      (@DivisionRing.toRing k (@Field.toDivisionRing k inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero k
                        (@Ring.toSemiring k (@DivisionRing.toRing k (@Field.toDivisionRing k inst))) inst_1)
                      (@ValuativeRel.valuation k (@DivisionRing.toRing k (@Field.toDivisionRing k inst)) inst_1)))))
              inst_4 inst_5)))
        (@Matrix.GeneralLinearGroup n k inst_5 inst_4
          (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst))))
        (@Units.instGroup (Matrix n n k)
          (@Semiring.toMonoid (Matrix n n k)
            (@Matrix.semiring n k
              (@DivisionSemiring.toSemiring k (@Semifield.toDivisionSemiring k (@Field.toSemifield k inst))) inst_4
              inst_5)))
        (@Matrix.GeneralLinearGroup.map n inst_5 inst_4
          (↥(@Valuation.integer k
              (@ValuativeRel.ValueGroupWithZero k
                (@Ring.toSemiring k (@DivisionRing.toRing k (@Field.toDivisionRing k inst))) inst_1)
              (@DivisionRing.toRing k (@Field.toDivisionRing k inst))
              (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero k
                (@Ring.toSemiring k (@DivisionRing.toRing k (@Field.toDivisionRing k inst))) inst_1)
              (@ValuativeRel.valuation k (@DivisionRing.toRing k (@Field.toDivisionRing k inst)) inst_1)))
          (@Subring.toCommRing k (@Field.toCommRing k inst)
            (@Valuation.integer k
              (@ValuativeRel.ValueGroupWithZero k
                (@Ring.toSemiring k (@DivisionRing.toRing k (@Field.toDivisionRing k inst))) inst_1)
              (@DivisionRing.toRing k (@Field.toDivisionRing k inst))
              (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero k
                (@Ring.toSemiring k (@DivisionRing.toRing k (@Field.toDivisionRing k inst))) inst_1)
              (@ValuativeRel.valuation k (@DivisionRing.toRing k (@Field.toDivisionRing k inst)) inst_1)))
          k (@Field.toCommRing k inst)
          (@Algebra.algebraMap
            (↥(@Valuation.integer k
                (@ValuativeRel.ValueGroupWithZero k
                  (@Ring.toSemiring k (@DivisionRing.toRing k (@Field.toDivisionRing k inst))) inst_1)
                (@DivisionRing.toRing k (@Field.toDivisionRing k inst))
                (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero k
                  (@Ring.toSemiring k (@DivisionRing.toRing k (@Field.toDivisionRing k inst))) inst_1)
                (@ValuativeRel.valuation k (@DivisionRing.toRing k (@Field.toDivisionRing k inst)) inst_1)))
            k
            (@SubsemiringClass.toCommSemiring
              (@Subring k (@Ring.toNonAssocRing k (@CommRing.toRing k (@Field.toCommRing k inst))))
              (@Valuation.integer k
                (@ValuativeRel.ValueGroupWithZero k
                  (@Ring.toSemiring k (@DivisionRing.toRing k (@Field.toDivisionRing k inst))) inst_1)
                (@CommRing.toRing k (@Field.toCommRing k inst))
                (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero k
                  (@Ring.toSemiring k (@DivisionRing.toRing k (@Field.toDivisionRing k inst))) inst_1)
                (@ValuativeRel.valuation k (@DivisionRing.toRing k (@Field.toDivisionRing k inst)) inst_1))
              k (@CommRing.toCommSemiring k (@Field.toCommRing k inst))
              (@Subring.instSetLike k (@Ring.toNonAssocRing k (@CommRing.toRing k (@Field.toCommRing k inst))))
              (@UpperTheory.Reformulated.B.BorelApproximation.aux3 k inst))
            (@CommSemiring.toSemiring k (@CommRing.toCommSemiring k (@Field.toCommRing k inst)))
            (@Valuation.instAlgebraSubtypeMemSubringInteger k
              (@ValuativeRel.ValueGroupWithZero k
                (@Ring.toSemiring k (@DivisionRing.toRing k (@Field.toDivisionRing k inst))) inst_1)
              (@Field.toCommRing k inst)
              (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero k
                (@Ring.toSemiring k (@DivisionRing.toRing k (@Field.toDivisionRing k inst))) inst_1)
              (@ValuativeRel.valuation k (@DivisionRing.toRing k (@Field.toDivisionRing k inst)) inst_1))))
        (@Subgroup.comap
          (@Matrix.GeneralLinearGroup n
            (↥(@Valuation.integer k
                (@ValuativeRel.ValueGroupWithZero k
                  (@Ring.toSemiring k (@DivisionRing.toRing k (@Field.toDivisionRing k inst))) inst_1)
                (@DivisionRing.toRing k (@Field.toDivisionRing k inst))
                (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero k
                  (@Ring.toSemiring k (@DivisionRing.toRing k (@Field.toDivisionRing k inst))) inst_1)
                (@ValuativeRel.valuation k (@DivisionRing.toRing k (@Field.toDivisionRing k inst)) inst_1)))
            inst_5 inst_4
            (@CommSemiring.toSemiring
              (↥(@Valuation.integer k
                  (@ValuativeRel.ValueGroupWithZero k
                    (@Ring.toSemiring k (@DivisionRing.toRing k (@Field.toDivisionRing k inst))) inst_1)
                  (@DivisionRing.toRing k (@Field.toDivisionRing k inst))
                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero k
                    (@Ring.toSemiring k (@DivisionRing.toRing k (@Field.toDivisionRing k inst))) inst_1)
                  (@ValuativeRel.valuation k (@DivisionRing.toRing k (@Field.toDivisionRing k inst)) inst_1)))
              (@CommRing.toCommSemiring
                (↥(@Valuation.integer k
                    (@ValuativeRel.ValueGroupWithZero k
                      (@Ring.toSemiring k (@DivisionRing.toRing k (@Field.toDivisionRing k inst))) inst_1)
                    (@DivisionRing.toRing k (@Field.toDivisionRing k inst))
                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero k
                      (@Ring.toSemiring k (@DivisionRing.toRing k (@Field.toDivisionRing k inst))) inst_1)
                    (@ValuativeRel.valuation k (@DivisionRing.toRing k (@Field.toDivisionRing k inst)) inst_1)))
                (@Subring.toCommRing k (@Field.toCommRing k inst)
                  (@Valuation.integer k
                    (@ValuativeRel.ValueGroupWithZero k
                      (@Ring.toSemiring k (@DivisionRing.toRing k (@Field.toDivisionRing k inst))) inst_1)
                    (@DivisionRing.toRing k (@Field.toDivisionRing k inst))
                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero k
                      (@Ring.toSemiring k (@DivisionRing.toRing k (@Field.toDivisionRing k inst))) inst_1)
                    (@ValuativeRel.valuation k (@DivisionRing.toRing k (@Field.toDivisionRing k inst)) inst_1))))))
          (@Units.instGroup
            (Matrix n n
              ↥(@Valuation.integer k
                  (@ValuativeRel.ValueGroupWithZero k
                    (@Ring.toSemiring k (@DivisionRing.toRing k (@Field.toDivisionRing k inst))) inst_1)
                  (@DivisionRing.toRing k (@Field.toDivisionRing k inst))
                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero k
                    (@Ring.toSemiring k (@DivisionRing.toRing k (@Field.toDivisionRing k inst))) inst_1)
                  (@ValuativeRel.valuation k (@DivisionRing.toRing k (@Field.toDivisionRing k inst)) inst_1)))
            (@Semiring.toMonoid
              (Matrix n n
                ↥(@Valuation.integer k
                    (@ValuativeRel.ValueGroupWithZero k
                      (@Ring.toSemiring k (@DivisionRing.toRing k (@Field.toDivisionRing k inst))) inst_1)
                    (@DivisionRing.toRing k (@Field.toDivisionRing k inst))
                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero k
                      (@Ring.toSemiring k (@DivisionRing.toRing k (@Field.toDivisionRing k inst))) inst_1)
                    (@ValuativeRel.valuation k (@DivisionRing.toRing k (@Field.toDivisionRing k inst)) inst_1)))
              (@Matrix.semiring n
                (↥(@Valuation.integer k
                    (@ValuativeRel.ValueGroupWithZero k
                      (@Ring.toSemiring k (@DivisionRing.toRing k (@Field.toDivisionRing k inst))) inst_1)
                    (@DivisionRing.toRing k (@Field.toDivisionRing k inst))
                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero k
                      (@Ring.toSemiring k (@DivisionRing.toRing k (@Field.toDivisionRing k inst))) inst_1)
                    (@ValuativeRel.valuation k (@DivisionRing.toRing k (@Field.toDivisionRing k inst)) inst_1)))
                (@CommSemiring.toSemiring
                  (↥(@Valuation.integer k
                      (@ValuativeRel.ValueGroupWithZero k
                        (@Ring.toSemiring k (@DivisionRing.toRing k (@Field.toDivisionRing k inst))) inst_1)
                      (@DivisionRing.toRing k (@Field.toDivisionRing k inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero k
                        (@Ring.toSemiring k (@DivisionRing.toRing k (@Field.toDivisionRing k inst))) inst_1)
                      (@ValuativeRel.valuation k (@DivisionRing.toRing k (@Field.toDivisionRing k inst)) inst_1)))
                  (@CommRing.toCommSemiring
                    (↥(@Valuation.integer k
                        (@ValuativeRel.ValueGroupWithZero k
                          (@Ring.toSemiring k (@DivisionRing.toRing k (@Field.toDivisionRing k inst))) inst_1)
                        (@DivisionRing.toRing k (@Field.toDivisionRing k inst))
                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero k
                          (@Ring.toSemiring k (@DivisionRing.toRing k (@Field.toDivisionRing k inst))) inst_1)
                        (@ValuativeRel.valuation k (@DivisionRing.toRing k (@Field.toDivisionRing k inst)) inst_1)))
                    (@Subring.toCommRing k (@Field.toCommRing k inst)
                      (@Valuation.integer k
                        (@ValuativeRel.ValueGroupWithZero k
                          (@Ring.toSemiring k (@DivisionRing.toRing k (@Field.toDivisionRing k inst))) inst_1)
                        (@DivisionRing.toRing k (@Field.toDivisionRing k inst))
                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero k
                          (@Ring.toSemiring k (@DivisionRing.toRing k (@Field.toDivisionRing k inst))) inst_1)
                        (@ValuativeRel.valuation k (@DivisionRing.toRing k (@Field.toDivisionRing k inst)) inst_1)))))
                inst_4 inst_5)))
          (@Matrix.GeneralLinearGroup n
            (@IsLocalRing.ResidueField
              (↥(@Valuation.integer k
                  (@ValuativeRel.ValueGroupWithZero k
                    (@Ring.toSemiring k (@DivisionRing.toRing k (@Field.toDivisionRing k inst))) inst_1)
                  (@DivisionRing.toRing k (@Field.toDivisionRing k inst))
                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero k
                    (@Ring.toSemiring k (@DivisionRing.toRing k (@Field.toDivisionRing k inst))) inst_1)
                  (@ValuativeRel.valuation k (@DivisionRing.toRing k (@Field.toDivisionRing k inst)) inst_1)))
              (@Subring.toCommRing k (@Field.toCommRing k inst)
                (@Valuation.integer k
                  (@ValuativeRel.ValueGroupWithZero k
                    (@Ring.toSemiring k (@DivisionRing.toRing k (@Field.toDivisionRing k inst))) inst_1)
                  (@DivisionRing.toRing k (@Field.toDivisionRing k inst))
                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero k
                    (@Ring.toSemiring k (@DivisionRing.toRing k (@Field.toDivisionRing k inst))) inst_1)
                  (@ValuativeRel.valuation k (@DivisionRing.toRing k (@Field.toDivisionRing k inst)) inst_1)))
              (@UpperTheory.Reformulated.B.BorelApproximation.aux4 k inst inst_1 inst_2 inst_3))
            inst_5 inst_4
            (@CommSemiring.toSemiring
              (@IsLocalRing.ResidueField
                (↥(@Valuation.integer k
                    (@ValuativeRel.ValueGroupWithZero k
                      (@Ring.toSemiring k (@DivisionRing.toRing k (@Field.toDivisionRing k inst))) inst_1)
                    (@DivisionRing.toRing k (@Field.toDivisionRing k inst))
                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero k
                      (@Ring.toSemiring k (@DivisionRing.toRing k (@Field.toDivisionRing k inst))) inst_1)
                    (@ValuativeRel.valuation k (@DivisionRing.toRing k (@Field.toDivisionRing k inst)) inst_1)))
                (@Subring.toCommRing k (@Field.toCommRing k inst)
                  (@Valuation.integer k
                    (@ValuativeRel.ValueGroupWithZero k
                      (@Ring.toSemiring k (@DivisionRing.toRing k (@Field.toDivisionRing k inst))) inst_1)
                    (@DivisionRing.toRing k (@Field.toDivisionRing k inst))
                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero k
                      (@Ring.toSemiring k (@DivisionRing.toRing k (@Field.toDivisionRing k inst))) inst_1)
                    (@ValuativeRel.valuation k (@DivisionRing.toRing k (@Field.toDivisionRing k inst)) inst_1)))
                (@UpperTheory.Reformulated.B.BorelApproximation.aux4 k inst inst_1 inst_2 inst_3))
              (@CommRing.toCommSemiring
                (@IsLocalRing.ResidueField
                  (↥(@Valuation.integer k
                      (@ValuativeRel.ValueGroupWithZero k
                        (@Ring.toSemiring k (@DivisionRing.toRing k (@Field.toDivisionRing k inst))) inst_1)
                      (@DivisionRing.toRing k (@Field.toDivisionRing k inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero k
                        (@Ring.toSemiring k (@DivisionRing.toRing k (@Field.toDivisionRing k inst))) inst_1)
                      (@ValuativeRel.valuation k (@DivisionRing.toRing k (@Field.toDivisionRing k inst)) inst_1)))
                  (@Subring.toCommRing k (@Field.toCommRing k inst)
                    (@Valuation.integer k
                      (@ValuativeRel.ValueGroupWithZero k
                        (@Ring.toSemiring k (@DivisionRing.toRing k (@Field.toDivisionRing k inst))) inst_1)
                      (@DivisionRing.toRing k (@Field.toDivisionRing k inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero k
                        (@Ring.toSemiring k (@DivisionRing.toRing k (@Field.toDivisionRing k inst))) inst_1)
                      (@ValuativeRel.valuation k (@DivisionRing.toRing k (@Field.toDivisionRing k inst)) inst_1)))
                  (@UpperTheory.Reformulated.B.BorelApproximation.aux4 k inst inst_1 inst_2 inst_3))
                (@IsLocalRing.instCommRingResidueField
                  (↥(@Valuation.integer k
                      (@ValuativeRel.ValueGroupWithZero k
                        (@Ring.toSemiring k (@DivisionRing.toRing k (@Field.toDivisionRing k inst))) inst_1)
                      (@DivisionRing.toRing k (@Field.toDivisionRing k inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero k
                        (@Ring.toSemiring k (@DivisionRing.toRing k (@Field.toDivisionRing k inst))) inst_1)
                      (@ValuativeRel.valuation k (@DivisionRing.toRing k (@Field.toDivisionRing k inst)) inst_1)))
                  (@Subring.toCommRing k (@Field.toCommRing k inst)
                    (@Valuation.integer k
                      (@ValuativeRel.ValueGroupWithZero k
                        (@Ring.toSemiring k (@DivisionRing.toRing k (@Field.toDivisionRing k inst))) inst_1)
                      (@DivisionRing.toRing k (@Field.toDivisionRing k inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero k
                        (@Ring.toSemiring k (@DivisionRing.toRing k (@Field.toDivisionRing k inst))) inst_1)
                      (@ValuativeRel.valuation k (@DivisionRing.toRing k (@Field.toDivisionRing k inst)) inst_1)))
                  (@UpperTheory.Reformulated.B.BorelApproximation.aux4 k inst inst_1 inst_2 inst_3)))))
          (@Units.instGroup
            (Matrix n n
              (@IsLocalRing.ResidueField
                (↥(@Valuation.integer k
                    (@ValuativeRel.ValueGroupWithZero k
                      (@Ring.toSemiring k (@DivisionRing.toRing k (@Field.toDivisionRing k inst))) inst_1)
                    (@DivisionRing.toRing k (@Field.toDivisionRing k inst))
                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero k
                      (@Ring.toSemiring k (@DivisionRing.toRing k (@Field.toDivisionRing k inst))) inst_1)
                    (@ValuativeRel.valuation k (@DivisionRing.toRing k (@Field.toDivisionRing k inst)) inst_1)))
                (@Subring.toCommRing k (@Field.toCommRing k inst)
                  (@Valuation.integer k
                    (@ValuativeRel.ValueGroupWithZero k
                      (@Ring.toSemiring k (@DivisionRing.toRing k (@Field.toDivisionRing k inst))) inst_1)
                    (@DivisionRing.toRing k (@Field.toDivisionRing k inst))
                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero k
                      (@Ring.toSemiring k (@DivisionRing.toRing k (@Field.toDivisionRing k inst))) inst_1)
                    (@ValuativeRel.valuation k (@DivisionRing.toRing k (@Field.toDivisionRing k inst)) inst_1)))
                (@UpperTheory.Reformulated.B.BorelApproximation.aux4 k inst inst_1 inst_2 inst_3)))
            (@Semiring.toMonoid
              (Matrix n n
                (@IsLocalRing.ResidueField
                  (↥(@Valuation.integer k
                      (@ValuativeRel.ValueGroupWithZero k
                        (@Ring.toSemiring k (@DivisionRing.toRing k (@Field.toDivisionRing k inst))) inst_1)
                      (@DivisionRing.toRing k (@Field.toDivisionRing k inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero k
                        (@Ring.toSemiring k (@DivisionRing.toRing k (@Field.toDivisionRing k inst))) inst_1)
                      (@ValuativeRel.valuation k (@DivisionRing.toRing k (@Field.toDivisionRing k inst)) inst_1)))
                  (@Subring.toCommRing k (@Field.toCommRing k inst)
                    (@Valuation.integer k
                      (@ValuativeRel.ValueGroupWithZero k
                        (@Ring.toSemiring k (@DivisionRing.toRing k (@Field.toDivisionRing k inst))) inst_1)
                      (@DivisionRing.toRing k (@Field.toDivisionRing k inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero k
                        (@Ring.toSemiring k (@DivisionRing.toRing k (@Field.toDivisionRing k inst))) inst_1)
                      (@ValuativeRel.valuation k (@DivisionRing.toRing k (@Field.toDivisionRing k inst)) inst_1)))
                  (@UpperTheory.Reformulated.B.BorelApproximation.aux4 k inst inst_1 inst_2 inst_3)))
              (@Matrix.semiring n
                (@IsLocalRing.ResidueField
                  (↥(@Valuation.integer k
                      (@ValuativeRel.ValueGroupWithZero k
                        (@Ring.toSemiring k (@DivisionRing.toRing k (@Field.toDivisionRing k inst))) inst_1)
                      (@DivisionRing.toRing k (@Field.toDivisionRing k inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero k
                        (@Ring.toSemiring k (@DivisionRing.toRing k (@Field.toDivisionRing k inst))) inst_1)
                      (@ValuativeRel.valuation k (@DivisionRing.toRing k (@Field.toDivisionRing k inst)) inst_1)))
                  (@Subring.toCommRing k (@Field.toCommRing k inst)
                    (@Valuation.integer k
                      (@ValuativeRel.ValueGroupWithZero k
                        (@Ring.toSemiring k (@DivisionRing.toRing k (@Field.toDivisionRing k inst))) inst_1)
                      (@DivisionRing.toRing k (@Field.toDivisionRing k inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero k
                        (@Ring.toSemiring k (@DivisionRing.toRing k (@Field.toDivisionRing k inst))) inst_1)
                      (@ValuativeRel.valuation k (@DivisionRing.toRing k (@Field.toDivisionRing k inst)) inst_1)))
                  (@UpperTheory.Reformulated.B.BorelApproximation.aux4 k inst inst_1 inst_2 inst_3))
                (@CommSemiring.toSemiring
                  (@IsLocalRing.ResidueField
                    (↥(@Valuation.integer k
                        (@ValuativeRel.ValueGroupWithZero k
                          (@Ring.toSemiring k (@DivisionRing.toRing k (@Field.toDivisionRing k inst))) inst_1)
                        (@DivisionRing.toRing k (@Field.toDivisionRing k inst))
                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero k
                          (@Ring.toSemiring k (@DivisionRing.toRing k (@Field.toDivisionRing k inst))) inst_1)
                        (@ValuativeRel.valuation k (@DivisionRing.toRing k (@Field.toDivisionRing k inst)) inst_1)))
                    (@Subring.toCommRing k (@Field.toCommRing k inst)
                      (@Valuation.integer k
                        (@ValuativeRel.ValueGroupWithZero k
                          (@Ring.toSemiring k (@DivisionRing.toRing k (@Field.toDivisionRing k inst))) inst_1)
                        (@DivisionRing.toRing k (@Field.toDivisionRing k inst))
                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero k
                          (@Ring.toSemiring k (@DivisionRing.toRing k (@Field.toDivisionRing k inst))) inst_1)
                        (@ValuativeRel.valuation k (@DivisionRing.toRing k (@Field.toDivisionRing k inst)) inst_1)))
                    (@UpperTheory.Reformulated.B.BorelApproximation.aux4 k inst inst_1 inst_2 inst_3))
                  (@CommRing.toCommSemiring
                    (@IsLocalRing.ResidueField
                      (↥(@Valuation.integer k
                          (@ValuativeRel.ValueGroupWithZero k
                            (@Ring.toSemiring k (@DivisionRing.toRing k (@Field.toDivisionRing k inst))) inst_1)
                          (@DivisionRing.toRing k (@Field.toDivisionRing k inst))
                          (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero k
                            (@Ring.toSemiring k (@DivisionRing.toRing k (@Field.toDivisionRing k inst))) inst_1)
                          (@ValuativeRel.valuation k (@DivisionRing.toRing k (@Field.toDivisionRing k inst)) inst_1)))
                      (@Subring.toCommRing k (@Field.toCommRing k inst)
                        (@Valuation.integer k
                          (@ValuativeRel.ValueGroupWithZero k
                            (@Ring.toSemiring k (@DivisionRing.toRing k (@Field.toDivisionRing k inst))) inst_1)
                          (@DivisionRing.toRing k (@Field.toDivisionRing k inst))
                          (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero k
                            (@Ring.toSemiring k (@DivisionRing.toRing k (@Field.toDivisionRing k inst))) inst_1)
                          (@ValuativeRel.valuation k (@DivisionRing.toRing k (@Field.toDivisionRing k inst)) inst_1)))
                      (@UpperTheory.Reformulated.B.BorelApproximation.aux4 k inst inst_1 inst_2 inst_3))
                    (@IsLocalRing.instCommRingResidueField
                      (↥(@Valuation.integer k
                          (@ValuativeRel.ValueGroupWithZero k
                            (@Ring.toSemiring k (@DivisionRing.toRing k (@Field.toDivisionRing k inst))) inst_1)
                          (@DivisionRing.toRing k (@Field.toDivisionRing k inst))
                          (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero k
                            (@Ring.toSemiring k (@DivisionRing.toRing k (@Field.toDivisionRing k inst))) inst_1)
                          (@ValuativeRel.valuation k (@DivisionRing.toRing k (@Field.toDivisionRing k inst)) inst_1)))
                      (@Subring.toCommRing k (@Field.toCommRing k inst)
                        (@Valuation.integer k
                          (@ValuativeRel.ValueGroupWithZero k
                            (@Ring.toSemiring k (@DivisionRing.toRing k (@Field.toDivisionRing k inst))) inst_1)
                          (@DivisionRing.toRing k (@Field.toDivisionRing k inst))
                          (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero k
                            (@Ring.toSemiring k (@DivisionRing.toRing k (@Field.toDivisionRing k inst))) inst_1)
                          (@ValuativeRel.valuation k (@DivisionRing.toRing k (@Field.toDivisionRing k inst)) inst_1)))
                      (@UpperTheory.Reformulated.B.BorelApproximation.aux4 k inst inst_1 inst_2 inst_3))))
                inst_4 inst_5)))
          (@Matrix.GeneralLinearGroup.map n inst_5 inst_4
            (↥(@Valuation.integer k
                (@ValuativeRel.ValueGroupWithZero k
                  (@Ring.toSemiring k (@DivisionRing.toRing k (@Field.toDivisionRing k inst))) inst_1)
                (@DivisionRing.toRing k (@Field.toDivisionRing k inst))
                (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero k
                  (@Ring.toSemiring k (@DivisionRing.toRing k (@Field.toDivisionRing k inst))) inst_1)
                (@ValuativeRel.valuation k (@DivisionRing.toRing k (@Field.toDivisionRing k inst)) inst_1)))
            (@Subring.toCommRing k (@Field.toCommRing k inst)
              (@Valuation.integer k
                (@ValuativeRel.ValueGroupWithZero k
                  (@Ring.toSemiring k (@DivisionRing.toRing k (@Field.toDivisionRing k inst))) inst_1)
                (@DivisionRing.toRing k (@Field.toDivisionRing k inst))
                (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero k
                  (@Ring.toSemiring k (@DivisionRing.toRing k (@Field.toDivisionRing k inst))) inst_1)
                (@ValuativeRel.valuation k (@DivisionRing.toRing k (@Field.toDivisionRing k inst)) inst_1)))
            (@IsLocalRing.ResidueField
              (↥(@Valuation.integer k
                  (@ValuativeRel.ValueGroupWithZero k
                    (@Ring.toSemiring k (@DivisionRing.toRing k (@Field.toDivisionRing k inst))) inst_1)
                  (@DivisionRing.toRing k (@Field.toDivisionRing k inst))
                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero k
                    (@Ring.toSemiring k (@DivisionRing.toRing k (@Field.toDivisionRing k inst))) inst_1)
                  (@ValuativeRel.valuation k (@DivisionRing.toRing k (@Field.toDivisionRing k inst)) inst_1)))
              (@Subring.toCommRing k (@Field.toCommRing k inst)
                (@Valuation.integer k
                  (@ValuativeRel.ValueGroupWithZero k
                    (@Ring.toSemiring k (@DivisionRing.toRing k (@Field.toDivisionRing k inst))) inst_1)
                  (@DivisionRing.toRing k (@Field.toDivisionRing k inst))
                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero k
                    (@Ring.toSemiring k (@DivisionRing.toRing k (@Field.toDivisionRing k inst))) inst_1)
                  (@ValuativeRel.valuation k (@DivisionRing.toRing k (@Field.toDivisionRing k inst)) inst_1)))
              (@UpperTheory.Reformulated.B.BorelApproximation.aux4 k inst inst_1 inst_2 inst_3))
            (@IsLocalRing.instCommRingResidueField
              (↥(@Valuation.integer k
                  (@ValuativeRel.ValueGroupWithZero k
                    (@Ring.toSemiring k (@DivisionRing.toRing k (@Field.toDivisionRing k inst))) inst_1)
                  (@DivisionRing.toRing k (@Field.toDivisionRing k inst))
                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero k
                    (@Ring.toSemiring k (@DivisionRing.toRing k (@Field.toDivisionRing k inst))) inst_1)
                  (@ValuativeRel.valuation k (@DivisionRing.toRing k (@Field.toDivisionRing k inst)) inst_1)))
              (@Subring.toCommRing k (@Field.toCommRing k inst)
                (@Valuation.integer k
                  (@ValuativeRel.ValueGroupWithZero k
                    (@Ring.toSemiring k (@DivisionRing.toRing k (@Field.toDivisionRing k inst))) inst_1)
                  (@DivisionRing.toRing k (@Field.toDivisionRing k inst))
                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero k
                    (@Ring.toSemiring k (@DivisionRing.toRing k (@Field.toDivisionRing k inst))) inst_1)
                  (@ValuativeRel.valuation k (@DivisionRing.toRing k (@Field.toDivisionRing k inst)) inst_1)))
              (@UpperTheory.Reformulated.B.BorelApproximation.aux4 k inst inst_1 inst_2 inst_3))
            (@IsLocalRing.residue
              (↥(@Valuation.integer k
                  (@ValuativeRel.ValueGroupWithZero k
                    (@Ring.toSemiring k (@DivisionRing.toRing k (@Field.toDivisionRing k inst))) inst_1)
                  (@DivisionRing.toRing k (@Field.toDivisionRing k inst))
                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero k
                    (@Ring.toSemiring k (@DivisionRing.toRing k (@Field.toDivisionRing k inst))) inst_1)
                  (@ValuativeRel.valuation k (@DivisionRing.toRing k (@Field.toDivisionRing k inst)) inst_1)))
              (@Subring.toCommRing k (@Field.toCommRing k inst)
                (@Valuation.integer k
                  (@ValuativeRel.ValueGroupWithZero k
                    (@Ring.toSemiring k (@DivisionRing.toRing k (@Field.toDivisionRing k inst))) inst_1)
                  (@DivisionRing.toRing k (@Field.toDivisionRing k inst))
                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero k
                    (@Ring.toSemiring k (@DivisionRing.toRing k (@Field.toDivisionRing k inst))) inst_1)
                  (@ValuativeRel.valuation k (@DivisionRing.toRing k (@Field.toDivisionRing k inst)) inst_1)))
              (@UpperTheory.Reformulated.B.BorelApproximation.aux4 k inst inst_1 inst_2 inst_3)))
          (@UpperTheory.Reformulated.B.BorelApproximation.borel
            (@IsLocalRing.ResidueField
              (↥(@Valuation.integer k
                  (@ValuativeRel.ValueGroupWithZero k
                    (@Ring.toSemiring k (@DivisionRing.toRing k (@Field.toDivisionRing k inst))) inst_1)
                  (@DivisionRing.toRing k (@Field.toDivisionRing k inst))
                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero k
                    (@Ring.toSemiring k (@DivisionRing.toRing k (@Field.toDivisionRing k inst))) inst_1)
                  (@ValuativeRel.valuation k (@DivisionRing.toRing k (@Field.toDivisionRing k inst)) inst_1)))
              (@Subring.toCommRing k (@Field.toCommRing k inst)
                (@Valuation.integer k
                  (@ValuativeRel.ValueGroupWithZero k
                    (@Ring.toSemiring k (@DivisionRing.toRing k (@Field.toDivisionRing k inst))) inst_1)
                  (@DivisionRing.toRing k (@Field.toDivisionRing k inst))
                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero k
                    (@Ring.toSemiring k (@DivisionRing.toRing k (@Field.toDivisionRing k inst))) inst_1)
                  (@ValuativeRel.valuation k (@DivisionRing.toRing k (@Field.toDivisionRing k inst)) inst_1)))
              (@UpperTheory.Reformulated.B.BorelApproximation.aux4 k inst inst_1 inst_2 inst_3))
            (@IsLocalRing.instCommRingResidueField
              (↥(@Valuation.integer k
                  (@ValuativeRel.ValueGroupWithZero k
                    (@Ring.toSemiring k (@DivisionRing.toRing k (@Field.toDivisionRing k inst))) inst_1)
                  (@DivisionRing.toRing k (@Field.toDivisionRing k inst))
                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero k
                    (@Ring.toSemiring k (@DivisionRing.toRing k (@Field.toDivisionRing k inst))) inst_1)
                  (@ValuativeRel.valuation k (@DivisionRing.toRing k (@Field.toDivisionRing k inst)) inst_1)))
              (@Subring.toCommRing k (@Field.toCommRing k inst)
                (@Valuation.integer k
                  (@ValuativeRel.ValueGroupWithZero k
                    (@Ring.toSemiring k (@DivisionRing.toRing k (@Field.toDivisionRing k inst))) inst_1)
                  (@DivisionRing.toRing k (@Field.toDivisionRing k inst))
                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero k
                    (@Ring.toSemiring k (@DivisionRing.toRing k (@Field.toDivisionRing k inst))) inst_1)
                  (@ValuativeRel.valuation k (@DivisionRing.toRing k (@Field.toDivisionRing k inst)) inst_1)))
              (@UpperTheory.Reformulated.B.BorelApproximation.aux4 k inst inst_1 inst_2 inst_3))
            n inst_4 inst_5 inst_6))
@[reducible] noncomputable def UpperTheory.Reformulated.B.BorelApproximation.complRel :
    {F : Type} →
      [inst : Field F] →
        [inst_1 : @NumberField F inst] →
          (p :
              @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                (@NumberField.instCommRingRingOfIntegers F inst)) →
            @ValuativeRel
              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                (@NumberField.instCommRingRingOfIntegers F inst)
                (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) p)
              (@DivisionSemiring.toSemiring
                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                  (@NumberField.instCommRingRingOfIntegers F inst)
                  (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                  (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                  (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) p)
                (@Semifield.toDivisionSemiring
                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst)
                    (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                    (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                    (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) p)
                  (@Field.toSemifield
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) p)
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) p)))) :=
    fun {F : Type} [inst : Field F] [inst_1 : @NumberField F inst]
        (p :
          @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
            (@NumberField.instCommRingRingOfIntegers F inst)) ↦
      @ValuativeRel.ofValuation
        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
          (@NumberField.instCommRingRingOfIntegers F inst) (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1)
          F inst (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) p)
        (WithZero (Multiplicative Int))
        (@DivisionRing.toRing
          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
            (@NumberField.instCommRingRingOfIntegers F inst)
            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) p)
          (@Field.toDivisionRing
            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
              (@NumberField.instCommRingRingOfIntegers F inst)
              (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
              (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
              (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) p)
            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
              (@NumberField.instCommRingRingOfIntegers F inst)
              (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
              (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
              (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) p)))
        WithZero.instLinearOrderedCommGroupWithZeroMultiplicativeInt
        (@Valued.v
          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
            (@NumberField.instCommRingRingOfIntegers F inst)
            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) p)
          (@DivisionRing.toRing
            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
              (@NumberField.instCommRingRingOfIntegers F inst)
              (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
              (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
              (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) p)
            (@Field.toDivisionRing
              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
                (@NumberField.instCommRingRingOfIntegers F inst)
                (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) p)
              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
                (@NumberField.instCommRingRingOfIntegers F inst)
                (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
                (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
                (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) p)))
          (WithZero (Multiplicative Int)) WithZero.instLinearOrderedCommGroupWithZeroMultiplicativeInt
          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instValuedWithZeroMultiplicativeInt
            (@NumberField.RingOfIntegers F inst) (@NumberField.instCommRingRingOfIntegers F inst)
            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) p))
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum in
theorem UpperTheory.Reformulated.B.BorelApproximation.exists_near {F : Type} [Field F] [NumberField F]
    (p : HeightOneSpectrum (NumberField.RingOfIntegers F)) (x : adicCompletion F p)
    (hx : Valued.v x ≤ 1) :
    ∃ a : NumberField.RingOfIntegers F, Valued.v (x - algebraMap _ (adicCompletion F p) a) < 1 := by
  have hb : {y : adicCompletion F p | Valued.v (y - x) < 1} ∈ nhds x := by
    rw [Valued.mem_nhds]
    refine ⟨1, fun y hy => ?_⟩
    simpa using hy
  obtain ⟨k, hk⟩ := (denseRange_algebraMap F p).mem_nhds hb
  have hk : Valued.v (algebraMap F (adicCompletion F p) k - x) < 1 := hk
  have hv : ∀ y : F, Valued.v (algebraMap F (adicCompletion F p) y) = p.valuation F y :=
    fun y => valuedAdicCompletion_eq_valuation' p y
  have hk1 : p.valuation F k ≤ 1 := by
    rw [← hv, ← sub_add_cancel (algebraMap F (adicCompletion F p) k) x]
    exact Valuation.map_add_le _ hk.le hx
  obtain ⟨a, ha⟩ := exists_valuation_sub_lt_of_integer p hk1 1
  refine ⟨a, ?_⟩
  rw [← hv, map_sub, ← IsScalarTower.algebraMap_apply, Units.val_one] at ha
  rw [Valuation.map_sub_swap, ← sub_add_sub_cancel _ (algebraMap F (adicCompletion F p) k)]
  exact Valuation.map_add_lt _ ha hk
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum in
theorem UpperTheory.Reformulated.B.BorelApproximation.finite_residue {F : Type} [Field F] [NumberField F]
    (p : HeightOneSpectrum (NumberField.RingOfIntegers F)) :
    Finite (IsLocalRing.ResidueField (adicCompletionIntegers F p)) := by
  have hfin : Finite (NumberField.RingOfIntegers F ⧸ p.asIdeal) :=
    p.asIdeal.finiteQuotientOfFreeOfNeBot p.ne_bot
  have hmax : ∀ y : adicCompletionIntegers F p, Valued.v y.1 < 1 →
      IsLocalRing.residue _ y = 0 := fun y hy => by
    rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      adicCompletionIntegers.isUnit_iff_valued_eq_one]
    exact hy.ne
  let φ : NumberField.RingOfIntegers F →+* IsLocalRing.ResidueField (adicCompletionIntegers F p) :=
    (IsLocalRing.residue _).comp (algebraMap _ _)
  have hker : ∀ a ∈ p.asIdeal, φ a = 0 := fun a ha => by
    refine hmax _ ?_
    rw [algebraMap_adicCompletionIntegers_apply, valuedAdicCompletion_eq_valuation']
    exact (valuation_lt_one_iff_mem p a).2 ha
  refine Finite.of_surjective (Ideal.Quotient.lift p.asIdeal φ hker) fun z => ?_
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective z
  obtain ⟨a, ha⟩ := UpperTheory.Reformulated.B.BorelApproximation.exists_near p x.1 x.2
  refine ⟨Ideal.Quotient.mk _ a, ?_⟩
  rw [Ideal.Quotient.lift_mk, eq_comm, ← sub_eq_zero]
  have := hmax (x - algebraMap _ _ a) ha
  rwa [map_sub] at this
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum in
theorem UpperTheory.Reformulated.B.BorelApproximation.locCompact {F : Type} [Field F] [NumberField F]
    (p : HeightOneSpectrum (NumberField.RingOfIntegers F)) :
    LocallyCompactSpace (adicCompletion F p) := by
  have h := (Valued.integer.properSpace_iff_completeSpace_and_isDiscreteValuationRing_integer_and_finite_residueField
    (K := adicCompletion F p)).2
    ⟨inferInstance, inferInstanceAs (IsDiscreteValuationRing (adicCompletionIntegers F p)),
      UpperTheory.Reformulated.B.BorelApproximation.finite_residue p⟩
  exact locallyCompact_of_proper
theorem UpperTheory.Reformulated.B.BorelApproximation.zero_contDiffOn_supported :
    ∀ {F : Type} [inst : Field F] [inst_1 : @NumberField F inst]
      (p :
        @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
          (@NumberField.instCommRingRingOfIntegers F inst)),
      @IsNonarchimedeanLocalField
        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
          (@NumberField.instCommRingRingOfIntegers F inst) (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1)
          F inst (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) p)
        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers F inst)
          (@NumberField.instCommRingRingOfIntegers F inst) (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1)
          F inst (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
          (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) p)
        (@UpperTheory.Reformulated.B.BorelApproximation.complRel F inst inst_1 p)
        (@UniformSpace.toTopologicalSpace
          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers F inst)
            (@NumberField.instCommRingRingOfIntegers F inst)
            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) p)
          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instUniformSpace (@NumberField.RingOfIntegers F inst)
            (@NumberField.instCommRingRingOfIntegers F inst)
            (@NumberField.RingOfIntegers.instIsDedekindDomain F inst inst_1) F inst
            (@NumberField.RingOfIntegers.instAlgebra_1 F inst)
            (@NumberField.RingOfIntegers.instIsFractionRing F inst inst_1) p)) := by
  intro F _ _ p
  letI := UpperTheory.Reformulated.B.BorelApproximation.complRel p
  haveI : (Valued.v : Valuation (p.adicCompletion F) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  haveI : IsValuativeTopology (p.adicCompletion F) :=
    IsValuativeTopology.of_mem_nhds_zero_iff_vle
      (Valued.v : Valuation (p.adicCompletion F) (WithZero (Multiplicative ℤ)))
      (fun {s} => Valued.is_topological_valuation s)
  haveI := UpperTheory.Reformulated.B.BorelApproximation.locCompact p
  haveI : ValuativeRel.IsNontrivial (p.adicCompletion F) :=
    (ValuativeRel.isNontrivial_iff_isNontrivial
      (Valued.v : Valuation (p.adicCompletion F) (WithZero (Multiplicative ℤ)))).2 inferInstance
  exact {}
noncomputable def UpperTheory.Reformulated.B.BorelApproximation.iwGL :
    {E : Type} →
      [inst : Field E] →
        [inst_1 : @NumberField E inst] →
          (n : Nat) →
            (w : @UpperTheory.Reformulated.B.BorelApproximation.Pl E inst inst_1) →
              @Subgroup (@UpperTheory.Reformulated.B.BorelApproximation.GLw E inst inst_1 n w)
                (@Units.instGroup
                  (Matrix (Fin n) (Fin n)
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                      (@NumberField.instCommRingRingOfIntegers E inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w))
                  (@Semiring.toMonoid
                    (Matrix (Fin n) (Fin n)
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                        (@NumberField.instCommRingRingOfIntegers E inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w))
                    (@Matrix.semiring (Fin n)
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                        (@NumberField.instCommRingRingOfIntegers E inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                      (@DivisionSemiring.toSemiring
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                          (@NumberField.instCommRingRingOfIntegers E inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                        (@Semifield.toDivisionSemiring
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                            (@NumberField.instCommRingRingOfIntegers E inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                          (@Field.toSemifield
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                              (@NumberField.instCommRingRingOfIntegers E inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                              (@NumberField.RingOfIntegers E inst) (@NumberField.instCommRingRingOfIntegers E inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w))))
                      (Fin.fintype n) (instDecidableEqFin n)))) :=
    fun {E : Type} [inst : Field E] [inst_1 : @NumberField E inst] (n : Nat) (w : @UpperTheory.Reformulated.B.BorelApproximation.Pl E inst inst_1) ↦
      @UpperTheory.Reformulated.B.BorelApproximation.iwahori
        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
          (@NumberField.instCommRingRingOfIntegers E inst) (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1)
          E inst (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
          (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField (@NumberField.RingOfIntegers E inst)
          (@NumberField.instCommRingRingOfIntegers E inst) (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1)
          E inst (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
          (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
        (@UpperTheory.Reformulated.B.BorelApproximation.complRel E inst inst_1 w)
        (@UniformSpace.toTopologicalSpace
          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
            (@NumberField.instCommRingRingOfIntegers E inst)
            (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
            (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
            (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instUniformSpace (@NumberField.RingOfIntegers E inst)
            (@NumberField.instCommRingRingOfIntegers E inst)
            (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
            (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
            (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w))
        (@UpperTheory.Reformulated.B.BorelApproximation.zero_contDiffOn_supported E inst inst_1 w) (Fin n) (Fin.fintype n) (instDecidableEqFin n) (@Fin.instLinearOrder n)
noncomputable def UpperTheory.Reformulated.B.BorelApproximation.dcos :
    {E : Type} →
      [inst : Field E] →
        [inst_1 : @NumberField E inst] →
          (n : Nat) →
            (w : @UpperTheory.Reformulated.B.BorelApproximation.Pl E inst inst_1) →
              @UpperTheory.Reformulated.B.BorelApproximation.GLw E inst inst_1 n w → @UpperTheory.Reformulated.B.BorelApproximation.GLw E inst inst_1 n w → Complex :=
    fun {E : Type} [inst : Field E] [inst_1 : @NumberField E inst] (n : Nat) (w : @UpperTheory.Reformulated.B.BorelApproximation.Pl E inst inst_1)
        (t y : @UpperTheory.Reformulated.B.BorelApproximation.GLw E inst inst_1 n w) ↦
      @ite Complex
        (∃ (x : @UpperTheory.Reformulated.B.BorelApproximation.GLw E inst inst_1 n w),
          And
            (@Membership.mem (@UpperTheory.Reformulated.B.BorelApproximation.GLw E inst inst_1 n w)
              (@Subgroup (@UpperTheory.Reformulated.B.BorelApproximation.GLw E inst inst_1 n w)
                (@Units.instGroup
                  (Matrix (Fin n) (Fin n)
                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                      (@NumberField.instCommRingRingOfIntegers E inst)
                      (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                      (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                      (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w))
                  (@Semiring.toMonoid
                    (Matrix (Fin n) (Fin n)
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                        (@NumberField.instCommRingRingOfIntegers E inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w))
                    (@Matrix.semiring (Fin n)
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                        (@NumberField.instCommRingRingOfIntegers E inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                      (@DivisionSemiring.toSemiring
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                          (@NumberField.instCommRingRingOfIntegers E inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                        (@Semifield.toDivisionSemiring
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                            (@NumberField.instCommRingRingOfIntegers E inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                          (@Field.toSemifield
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                              (@NumberField.instCommRingRingOfIntegers E inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                              (@NumberField.RingOfIntegers E inst) (@NumberField.instCommRingRingOfIntegers E inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w))))
                      (Fin.fintype n) (instDecidableEqFin n)))))
              (@SetLike.instMembership
                (@Subgroup (@UpperTheory.Reformulated.B.BorelApproximation.GLw E inst inst_1 n w)
                  (@Units.instGroup
                    (Matrix (Fin n) (Fin n)
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                        (@NumberField.instCommRingRingOfIntegers E inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w))
                    (@Semiring.toMonoid
                      (Matrix (Fin n) (Fin n)
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                          (@NumberField.instCommRingRingOfIntegers E inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w))
                      (@Matrix.semiring (Fin n)
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                          (@NumberField.instCommRingRingOfIntegers E inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                        (@DivisionSemiring.toSemiring
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                            (@NumberField.instCommRingRingOfIntegers E inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                          (@Semifield.toDivisionSemiring
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                              (@NumberField.instCommRingRingOfIntegers E inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                            (@Field.toSemifield
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                                (@NumberField.instCommRingRingOfIntegers E inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                (@NumberField.RingOfIntegers E inst) (@NumberField.instCommRingRingOfIntegers E inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w))))
                        (Fin.fintype n) (instDecidableEqFin n)))))
                (@UpperTheory.Reformulated.B.BorelApproximation.GLw E inst inst_1 n w)
                (@Subgroup.instSetLike (@UpperTheory.Reformulated.B.BorelApproximation.GLw E inst inst_1 n w)
                  (@Units.instGroup
                    (Matrix (Fin n) (Fin n)
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                        (@NumberField.instCommRingRingOfIntegers E inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w))
                    (@Semiring.toMonoid
                      (Matrix (Fin n) (Fin n)
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                          (@NumberField.instCommRingRingOfIntegers E inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w))
                      (@Matrix.semiring (Fin n)
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                          (@NumberField.instCommRingRingOfIntegers E inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                        (@DivisionSemiring.toSemiring
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                            (@NumberField.instCommRingRingOfIntegers E inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                          (@Semifield.toDivisionSemiring
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                              (@NumberField.instCommRingRingOfIntegers E inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                            (@Field.toSemifield
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                                (@NumberField.instCommRingRingOfIntegers E inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                (@NumberField.RingOfIntegers E inst) (@NumberField.instCommRingRingOfIntegers E inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w))))
                        (Fin.fintype n) (instDecidableEqFin n))))))
              (@UpperTheory.Reformulated.B.BorelApproximation.iwGL E inst inst_1 n w) x)
            (∃ (z : @UpperTheory.Reformulated.B.BorelApproximation.GLw E inst inst_1 n w),
              And
                (@Membership.mem (@UpperTheory.Reformulated.B.BorelApproximation.GLw E inst inst_1 n w)
                  (@Subgroup (@UpperTheory.Reformulated.B.BorelApproximation.GLw E inst inst_1 n w)
                    (@Units.instGroup
                      (Matrix (Fin n) (Fin n)
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                          (@NumberField.instCommRingRingOfIntegers E inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w))
                      (@Semiring.toMonoid
                        (Matrix (Fin n) (Fin n)
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                            (@NumberField.instCommRingRingOfIntegers E inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w))
                        (@Matrix.semiring (Fin n)
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                            (@NumberField.instCommRingRingOfIntegers E inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                          (@DivisionSemiring.toSemiring
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                              (@NumberField.instCommRingRingOfIntegers E inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                            (@Semifield.toDivisionSemiring
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                                (@NumberField.instCommRingRingOfIntegers E inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                              (@Field.toSemifield
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                                  (@NumberField.instCommRingRingOfIntegers E inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                  (@NumberField.RingOfIntegers E inst) (@NumberField.instCommRingRingOfIntegers E inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w))))
                          (Fin.fintype n) (instDecidableEqFin n)))))
                  (@SetLike.instMembership
                    (@Subgroup (@UpperTheory.Reformulated.B.BorelApproximation.GLw E inst inst_1 n w)
                      (@Units.instGroup
                        (Matrix (Fin n) (Fin n)
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                            (@NumberField.instCommRingRingOfIntegers E inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w))
                        (@Semiring.toMonoid
                          (Matrix (Fin n) (Fin n)
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                              (@NumberField.instCommRingRingOfIntegers E inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w))
                          (@Matrix.semiring (Fin n)
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                              (@NumberField.instCommRingRingOfIntegers E inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                            (@DivisionSemiring.toSemiring
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                                (@NumberField.instCommRingRingOfIntegers E inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                              (@Semifield.toDivisionSemiring
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                                  (@NumberField.instCommRingRingOfIntegers E inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                                (@Field.toSemifield
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                                    (@NumberField.instCommRingRingOfIntegers E inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                    (@NumberField.RingOfIntegers E inst) (@NumberField.instCommRingRingOfIntegers E inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w))))
                            (Fin.fintype n) (instDecidableEqFin n)))))
                    (@UpperTheory.Reformulated.B.BorelApproximation.GLw E inst inst_1 n w)
                    (@Subgroup.instSetLike (@UpperTheory.Reformulated.B.BorelApproximation.GLw E inst inst_1 n w)
                      (@Units.instGroup
                        (Matrix (Fin n) (Fin n)
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                            (@NumberField.instCommRingRingOfIntegers E inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w))
                        (@Semiring.toMonoid
                          (Matrix (Fin n) (Fin n)
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                              (@NumberField.instCommRingRingOfIntegers E inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w))
                          (@Matrix.semiring (Fin n)
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                              (@NumberField.instCommRingRingOfIntegers E inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                            (@DivisionSemiring.toSemiring
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                                (@NumberField.instCommRingRingOfIntegers E inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                              (@Semifield.toDivisionSemiring
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                                  (@NumberField.instCommRingRingOfIntegers E inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                                (@Field.toSemifield
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                                    (@NumberField.instCommRingRingOfIntegers E inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                    (@NumberField.RingOfIntegers E inst) (@NumberField.instCommRingRingOfIntegers E inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w))))
                            (Fin.fintype n) (instDecidableEqFin n))))))
                  (@UpperTheory.Reformulated.B.BorelApproximation.iwGL E inst inst_1 n w) z)
                (@Eq (@UpperTheory.Reformulated.B.BorelApproximation.GLw E inst inst_1 n w) y
                  (@HMul.hMul (@UpperTheory.Reformulated.B.BorelApproximation.GLw E inst inst_1 n w) (@UpperTheory.Reformulated.B.BorelApproximation.GLw E inst inst_1 n w)
                    (@UpperTheory.Reformulated.B.BorelApproximation.GLw E inst inst_1 n w)
                    (@instHMul (@UpperTheory.Reformulated.B.BorelApproximation.GLw E inst inst_1 n w)
                      (@Units.instMul
                        (Matrix (Fin n) (Fin n)
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                            (@NumberField.instCommRingRingOfIntegers E inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w))
                        (@Semiring.toMonoid
                          (Matrix (Fin n) (Fin n)
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                              (@NumberField.instCommRingRingOfIntegers E inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w))
                          (@Matrix.semiring (Fin n)
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                              (@NumberField.instCommRingRingOfIntegers E inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                            (@DivisionSemiring.toSemiring
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                                (@NumberField.instCommRingRingOfIntegers E inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                              (@Semifield.toDivisionSemiring
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                                  (@NumberField.instCommRingRingOfIntegers E inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                                (@Field.toSemifield
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                                    (@NumberField.instCommRingRingOfIntegers E inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                    (@NumberField.RingOfIntegers E inst) (@NumberField.instCommRingRingOfIntegers E inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w))))
                            (Fin.fintype n) (instDecidableEqFin n)))))
                    (@HMul.hMul (@UpperTheory.Reformulated.B.BorelApproximation.GLw E inst inst_1 n w) (@UpperTheory.Reformulated.B.BorelApproximation.GLw E inst inst_1 n w)
                      (@UpperTheory.Reformulated.B.BorelApproximation.GLw E inst inst_1 n w)
                      (@instHMul (@UpperTheory.Reformulated.B.BorelApproximation.GLw E inst inst_1 n w)
                        (@Units.instMul
                          (Matrix (Fin n) (Fin n)
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                              (@NumberField.instCommRingRingOfIntegers E inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w))
                          (@Semiring.toMonoid
                            (Matrix (Fin n) (Fin n)
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                                (@NumberField.instCommRingRingOfIntegers E inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w))
                            (@Matrix.semiring (Fin n)
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                                (@NumberField.instCommRingRingOfIntegers E inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                              (@DivisionSemiring.toSemiring
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                                  (@NumberField.instCommRingRingOfIntegers E inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                                (@Semifield.toDivisionSemiring
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                                    (@NumberField.instCommRingRingOfIntegers E inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                                  (@Field.toSemifield
                                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                                      (@NumberField.instCommRingRingOfIntegers E inst)
                                      (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                                      (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                                      (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                      (@NumberField.RingOfIntegers E inst) (@NumberField.instCommRingRingOfIntegers E inst)
                                      (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                                      (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                                      (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w))))
                              (Fin.fintype n) (instDecidableEqFin n)))))
                      x t)
                    z))))
        (Classical.propDecidable
          (∃ (x : @UpperTheory.Reformulated.B.BorelApproximation.GLw E inst inst_1 n w),
            And
              (@Membership.mem (@UpperTheory.Reformulated.B.BorelApproximation.GLw E inst inst_1 n w)
                (@Subgroup (@UpperTheory.Reformulated.B.BorelApproximation.GLw E inst inst_1 n w)
                  (@Units.instGroup
                    (Matrix (Fin n) (Fin n)
                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                        (@NumberField.instCommRingRingOfIntegers E inst)
                        (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                        (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                        (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w))
                    (@Semiring.toMonoid
                      (Matrix (Fin n) (Fin n)
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                          (@NumberField.instCommRingRingOfIntegers E inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w))
                      (@Matrix.semiring (Fin n)
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                          (@NumberField.instCommRingRingOfIntegers E inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                        (@DivisionSemiring.toSemiring
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                            (@NumberField.instCommRingRingOfIntegers E inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                          (@Semifield.toDivisionSemiring
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                              (@NumberField.instCommRingRingOfIntegers E inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                            (@Field.toSemifield
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                                (@NumberField.instCommRingRingOfIntegers E inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                (@NumberField.RingOfIntegers E inst) (@NumberField.instCommRingRingOfIntegers E inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w))))
                        (Fin.fintype n) (instDecidableEqFin n)))))
                (@SetLike.instMembership
                  (@Subgroup (@UpperTheory.Reformulated.B.BorelApproximation.GLw E inst inst_1 n w)
                    (@Units.instGroup
                      (Matrix (Fin n) (Fin n)
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                          (@NumberField.instCommRingRingOfIntegers E inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w))
                      (@Semiring.toMonoid
                        (Matrix (Fin n) (Fin n)
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                            (@NumberField.instCommRingRingOfIntegers E inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w))
                        (@Matrix.semiring (Fin n)
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                            (@NumberField.instCommRingRingOfIntegers E inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                          (@DivisionSemiring.toSemiring
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                              (@NumberField.instCommRingRingOfIntegers E inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                            (@Semifield.toDivisionSemiring
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                                (@NumberField.instCommRingRingOfIntegers E inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                              (@Field.toSemifield
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                                  (@NumberField.instCommRingRingOfIntegers E inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                  (@NumberField.RingOfIntegers E inst) (@NumberField.instCommRingRingOfIntegers E inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w))))
                          (Fin.fintype n) (instDecidableEqFin n)))))
                  (@UpperTheory.Reformulated.B.BorelApproximation.GLw E inst inst_1 n w)
                  (@Subgroup.instSetLike (@UpperTheory.Reformulated.B.BorelApproximation.GLw E inst inst_1 n w)
                    (@Units.instGroup
                      (Matrix (Fin n) (Fin n)
                        (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                          (@NumberField.instCommRingRingOfIntegers E inst)
                          (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                          (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                          (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w))
                      (@Semiring.toMonoid
                        (Matrix (Fin n) (Fin n)
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                            (@NumberField.instCommRingRingOfIntegers E inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w))
                        (@Matrix.semiring (Fin n)
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                            (@NumberField.instCommRingRingOfIntegers E inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                          (@DivisionSemiring.toSemiring
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                              (@NumberField.instCommRingRingOfIntegers E inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                            (@Semifield.toDivisionSemiring
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                                (@NumberField.instCommRingRingOfIntegers E inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                              (@Field.toSemifield
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                                  (@NumberField.instCommRingRingOfIntegers E inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                  (@NumberField.RingOfIntegers E inst) (@NumberField.instCommRingRingOfIntegers E inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w))))
                          (Fin.fintype n) (instDecidableEqFin n))))))
                (@UpperTheory.Reformulated.B.BorelApproximation.iwGL E inst inst_1 n w) x)
              (∃ (z : @UpperTheory.Reformulated.B.BorelApproximation.GLw E inst inst_1 n w),
                And
                  (@Membership.mem (@UpperTheory.Reformulated.B.BorelApproximation.GLw E inst inst_1 n w)
                    (@Subgroup (@UpperTheory.Reformulated.B.BorelApproximation.GLw E inst inst_1 n w)
                      (@Units.instGroup
                        (Matrix (Fin n) (Fin n)
                          (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                            (@NumberField.instCommRingRingOfIntegers E inst)
                            (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                            (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                            (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w))
                        (@Semiring.toMonoid
                          (Matrix (Fin n) (Fin n)
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                              (@NumberField.instCommRingRingOfIntegers E inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w))
                          (@Matrix.semiring (Fin n)
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                              (@NumberField.instCommRingRingOfIntegers E inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                            (@DivisionSemiring.toSemiring
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                                (@NumberField.instCommRingRingOfIntegers E inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                              (@Semifield.toDivisionSemiring
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                                  (@NumberField.instCommRingRingOfIntegers E inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                                (@Field.toSemifield
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                                    (@NumberField.instCommRingRingOfIntegers E inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                    (@NumberField.RingOfIntegers E inst) (@NumberField.instCommRingRingOfIntegers E inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w))))
                            (Fin.fintype n) (instDecidableEqFin n)))))
                    (@SetLike.instMembership
                      (@Subgroup (@UpperTheory.Reformulated.B.BorelApproximation.GLw E inst inst_1 n w)
                        (@Units.instGroup
                          (Matrix (Fin n) (Fin n)
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                              (@NumberField.instCommRingRingOfIntegers E inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w))
                          (@Semiring.toMonoid
                            (Matrix (Fin n) (Fin n)
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                                (@NumberField.instCommRingRingOfIntegers E inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w))
                            (@Matrix.semiring (Fin n)
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                                (@NumberField.instCommRingRingOfIntegers E inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                              (@DivisionSemiring.toSemiring
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                                  (@NumberField.instCommRingRingOfIntegers E inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                                (@Semifield.toDivisionSemiring
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                                    (@NumberField.instCommRingRingOfIntegers E inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                                  (@Field.toSemifield
                                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                                      (@NumberField.instCommRingRingOfIntegers E inst)
                                      (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                                      (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                                      (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                      (@NumberField.RingOfIntegers E inst) (@NumberField.instCommRingRingOfIntegers E inst)
                                      (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                                      (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                                      (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w))))
                              (Fin.fintype n) (instDecidableEqFin n)))))
                      (@UpperTheory.Reformulated.B.BorelApproximation.GLw E inst inst_1 n w)
                      (@Subgroup.instSetLike (@UpperTheory.Reformulated.B.BorelApproximation.GLw E inst inst_1 n w)
                        (@Units.instGroup
                          (Matrix (Fin n) (Fin n)
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                              (@NumberField.instCommRingRingOfIntegers E inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w))
                          (@Semiring.toMonoid
                            (Matrix (Fin n) (Fin n)
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                                (@NumberField.instCommRingRingOfIntegers E inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w))
                            (@Matrix.semiring (Fin n)
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                                (@NumberField.instCommRingRingOfIntegers E inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                              (@DivisionSemiring.toSemiring
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                                  (@NumberField.instCommRingRingOfIntegers E inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                                (@Semifield.toDivisionSemiring
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                                    (@NumberField.instCommRingRingOfIntegers E inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                                  (@Field.toSemifield
                                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                                      (@NumberField.instCommRingRingOfIntegers E inst)
                                      (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                                      (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                                      (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                      (@NumberField.RingOfIntegers E inst) (@NumberField.instCommRingRingOfIntegers E inst)
                                      (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                                      (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                                      (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w))))
                              (Fin.fintype n) (instDecidableEqFin n))))))
                    (@UpperTheory.Reformulated.B.BorelApproximation.iwGL E inst inst_1 n w) z)
                  (@Eq (@UpperTheory.Reformulated.B.BorelApproximation.GLw E inst inst_1 n w) y
                    (@HMul.hMul (@UpperTheory.Reformulated.B.BorelApproximation.GLw E inst inst_1 n w) (@UpperTheory.Reformulated.B.BorelApproximation.GLw E inst inst_1 n w)
                      (@UpperTheory.Reformulated.B.BorelApproximation.GLw E inst inst_1 n w)
                      (@instHMul (@UpperTheory.Reformulated.B.BorelApproximation.GLw E inst inst_1 n w)
                        (@Units.instMul
                          (Matrix (Fin n) (Fin n)
                            (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                              (@NumberField.instCommRingRingOfIntegers E inst)
                              (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                              (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                              (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w))
                          (@Semiring.toMonoid
                            (Matrix (Fin n) (Fin n)
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                                (@NumberField.instCommRingRingOfIntegers E inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w))
                            (@Matrix.semiring (Fin n)
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                                (@NumberField.instCommRingRingOfIntegers E inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                              (@DivisionSemiring.toSemiring
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                                  (@NumberField.instCommRingRingOfIntegers E inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                                (@Semifield.toDivisionSemiring
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                                    (@NumberField.instCommRingRingOfIntegers E inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                                  (@Field.toSemifield
                                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                                      (@NumberField.instCommRingRingOfIntegers E inst)
                                      (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                                      (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                                      (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                      (@NumberField.RingOfIntegers E inst) (@NumberField.instCommRingRingOfIntegers E inst)
                                      (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                                      (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                                      (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w))))
                              (Fin.fintype n) (instDecidableEqFin n)))))
                      (@HMul.hMul (@UpperTheory.Reformulated.B.BorelApproximation.GLw E inst inst_1 n w) (@UpperTheory.Reformulated.B.BorelApproximation.GLw E inst inst_1 n w)
                        (@UpperTheory.Reformulated.B.BorelApproximation.GLw E inst inst_1 n w)
                        (@instHMul (@UpperTheory.Reformulated.B.BorelApproximation.GLw E inst inst_1 n w)
                          (@Units.instMul
                            (Matrix (Fin n) (Fin n)
                              (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                                (@NumberField.instCommRingRingOfIntegers E inst)
                                (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                                (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                                (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w))
                            (@Semiring.toMonoid
                              (Matrix (Fin n) (Fin n)
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                                  (@NumberField.instCommRingRingOfIntegers E inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w))
                              (@Matrix.semiring (Fin n)
                                (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                                  (@NumberField.instCommRingRingOfIntegers E inst)
                                  (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                                  (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                                  (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                                (@DivisionSemiring.toSemiring
                                  (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                                    (@NumberField.instCommRingRingOfIntegers E inst)
                                    (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                                    (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                                    (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                                  (@Semifield.toDivisionSemiring
                                    (@IsDedekindDomain.HeightOneSpectrum.adicCompletion (@NumberField.RingOfIntegers E inst)
                                      (@NumberField.instCommRingRingOfIntegers E inst)
                                      (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                                      (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                                      (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                                    (@Field.toSemifield
                                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion
                                        (@NumberField.RingOfIntegers E inst)
                                        (@NumberField.instCommRingRingOfIntegers E inst)
                                        (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                                        (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                                        (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w)
                                      (@IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
                                        (@NumberField.RingOfIntegers E inst)
                                        (@NumberField.instCommRingRingOfIntegers E inst)
                                        (@NumberField.RingOfIntegers.instIsDedekindDomain E inst inst_1) E inst
                                        (@NumberField.RingOfIntegers.instAlgebra_1 E inst)
                                        (@NumberField.RingOfIntegers.instIsFractionRing E inst inst_1) w))))
                                (Fin.fintype n) (instDecidableEqFin n)))))
                        x t)
                      z)))))
        (@OfNat.ofNat Complex (nat_lit 1) (@One.toOfNat1 Complex Complex.instOne))
        (@OfNat.ofNat Complex (nat_lit 0) (@Zero.toOfNat0 Complex Complex.instZero))


