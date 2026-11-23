-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_MemOfClosed
-- name    : Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_MemOfClosed
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:56:34.749092+00:00
-- url     : https://prove2.me/theorems/68e27ef1-6298-46f6-94d3-2b989ef7cedb
-- title:
--   Mem Of Closed
-- statement:
--   Definitions and structural lemmas for Mem Of Closed, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/MemOfClosed.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
theorem UpperTheory.Reformulated.B.Qi13.aux1 :
    ∀ (K : Type) [inst : Field K]
      [inst_1 :
        @ValuativeRel K (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))]
      [inst_2 : TopologicalSpace K] [@IsNonarchimedeanLocalField K inst inst_1 inst_2],
      @IsLocalRing
        (↥(@Valuation.integer K
            (@ValuativeRel.ValueGroupWithZero K (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)))
              inst_1)
            (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
            (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
            (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
        (@CommSemiring.toSemiring
          (↥(@Valuation.integer K
              (@ValuativeRel.ValueGroupWithZero K
                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
              (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
              (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
              (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
          (@CommRing.toCommSemiring
            (↥(@Valuation.integer K
                (@ValuativeRel.ValueGroupWithZero K
                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
            (@Subring.toCommRing K (@Field.toCommRing K inst)
              (@Valuation.integer K
                (@ValuativeRel.ValueGroupWithZero K
                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1))))) := by
  intro K _ _ _ _
  infer_instance
@[reducible] noncomputable def UpperTheory.Reformulated.B.Qi13.algRes :
    (K : Type) →
      [inst : Field K] →
        [inst_1 :
            @ValuativeRel K
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))] →
          [inst_2 : TopologicalSpace K] →
            [inst_3 : @IsNonarchimedeanLocalField K inst inst_1 inst_2] →
              (l : Nat) →
                [inst_4 : Fact (Nat.Prime l)] →
                  [@CharP
                        (@IsLocalRing.ResidueField
                          (↥(@Valuation.integer K
                              (@ValuativeRel.ValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                              (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                          (@Subring.toCommRing K (@Field.toCommRing K inst)
                            (@Valuation.integer K
                              (@ValuativeRel.ValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                              (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                          (@IsDiscreteValuationRing.toIsLocalRing
                            (↥(@Valuation.integer K
                                (@ValuativeRel.ValueGroupWithZero K
                                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                            (@Subring.toCommRing K (@Field.toCommRing K inst)
                              (@Valuation.integer K
                                (@ValuativeRel.ValueGroupWithZero K
                                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                            (@Subring.instIsDomainSubtypeMem K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                              (@instIsDomain K (@Field.toSemifield K inst))
                              (@Valuation.integer K
                                (@ValuativeRel.ValueGroupWithZero K
                                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                            (@IsNonarchimedeanLocalField.instIsDiscreteValuationRingSubtypeMemSubringIntegerValueGroupWithZeroValuation
                              K inst inst_1 inst_2 inst_3)))
                        (@AddGroupWithOne.toAddMonoidWithOne
                          (@IsLocalRing.ResidueField
                            (↥(@Valuation.integer K
                                (@ValuativeRel.ValueGroupWithZero K
                                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                            (@Subring.toCommRing K (@Field.toCommRing K inst)
                              (@Valuation.integer K
                                (@ValuativeRel.ValueGroupWithZero K
                                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                            (@IsDiscreteValuationRing.toIsLocalRing
                              (↥(@Valuation.integer K
                                  (@ValuativeRel.ValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    inst_1)))
                              (@Subring.toCommRing K (@Field.toCommRing K inst)
                                (@Valuation.integer K
                                  (@ValuativeRel.ValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    inst_1)))
                              (@Subring.instIsDomainSubtypeMem K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                (@instIsDomain K (@Field.toSemifield K inst))
                                (@Valuation.integer K
                                  (@ValuativeRel.ValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    inst_1)))
                              (@IsNonarchimedeanLocalField.instIsDiscreteValuationRingSubtypeMemSubringIntegerValueGroupWithZeroValuation
                                K inst inst_1 inst_2 inst_3)))
                          (@Ring.toAddGroupWithOne
                            (@IsLocalRing.ResidueField
                              (↥(@Valuation.integer K
                                  (@ValuativeRel.ValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    inst_1)))
                              (@Subring.toCommRing K (@Field.toCommRing K inst)
                                (@Valuation.integer K
                                  (@ValuativeRel.ValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    inst_1)))
                              (@IsDiscreteValuationRing.toIsLocalRing
                                (↥(@Valuation.integer K
                                    (@ValuativeRel.ValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      inst_1)))
                                (@Subring.toCommRing K (@Field.toCommRing K inst)
                                  (@Valuation.integer K
                                    (@ValuativeRel.ValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      inst_1)))
                                (@Subring.instIsDomainSubtypeMem K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                  (@instIsDomain K (@Field.toSemifield K inst))
                                  (@Valuation.integer K
                                    (@ValuativeRel.ValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      inst_1)))
                                (@IsNonarchimedeanLocalField.instIsDiscreteValuationRingSubtypeMemSubringIntegerValueGroupWithZeroValuation
                                  K inst inst_1 inst_2 inst_3)))
                            (@DivisionRing.toRing
                              (@IsLocalRing.ResidueField
                                (↥(@Valuation.integer K
                                    (@ValuativeRel.ValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      inst_1)))
                                (@Subring.toCommRing K (@Field.toCommRing K inst)
                                  (@Valuation.integer K
                                    (@ValuativeRel.ValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      inst_1)))
                                (@IsDiscreteValuationRing.toIsLocalRing
                                  (↥(@Valuation.integer K
                                      (@ValuativeRel.ValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                        inst_1)))
                                  (@Subring.toCommRing K (@Field.toCommRing K inst)
                                    (@Valuation.integer K
                                      (@ValuativeRel.ValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                        inst_1)))
                                  (@Subring.instIsDomainSubtypeMem K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    (@instIsDomain K (@Field.toSemifield K inst))
                                    (@Valuation.integer K
                                      (@ValuativeRel.ValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                        inst_1)))
                                  (@IsNonarchimedeanLocalField.instIsDiscreteValuationRingSubtypeMemSubringIntegerValueGroupWithZeroValuation
                                    K inst inst_1 inst_2 inst_3)))
                              (@Field.toDivisionRing
                                (@IsLocalRing.ResidueField
                                  (↥(@Valuation.integer K
                                      (@ValuativeRel.ValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                        inst_1)))
                                  (@Subring.toCommRing K (@Field.toCommRing K inst)
                                    (@Valuation.integer K
                                      (@ValuativeRel.ValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                        inst_1)))
                                  (@IsDiscreteValuationRing.toIsLocalRing
                                    (↥(@Valuation.integer K
                                        (@ValuativeRel.ValueGroupWithZero K
                                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)))
                                          inst_1)
                                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)))
                                          inst_1)
                                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                          inst_1)))
                                    (@Subring.toCommRing K (@Field.toCommRing K inst)
                                      (@Valuation.integer K
                                        (@ValuativeRel.ValueGroupWithZero K
                                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)))
                                          inst_1)
                                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)))
                                          inst_1)
                                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                          inst_1)))
                                    (@Subring.instIsDomainSubtypeMem K
                                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      (@instIsDomain K (@Field.toSemifield K inst))
                                      (@Valuation.integer K
                                        (@ValuativeRel.ValueGroupWithZero K
                                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)))
                                          inst_1)
                                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)))
                                          inst_1)
                                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                          inst_1)))
                                    (@IsNonarchimedeanLocalField.instIsDiscreteValuationRingSubtypeMemSubringIntegerValueGroupWithZeroValuation
                                      K inst inst_1 inst_2 inst_3)))
                                (@IsLocalRing.ResidueField.field
                                  (↥(@Valuation.integer K
                                      (@ValuativeRel.ValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                        inst_1)))
                                  (@Subring.toCommRing K (@Field.toCommRing K inst)
                                    (@Valuation.integer K
                                      (@ValuativeRel.ValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                        inst_1)))
                                  (@IsDiscreteValuationRing.toIsLocalRing
                                    (↥(@Valuation.integer K
                                        (@ValuativeRel.ValueGroupWithZero K
                                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)))
                                          inst_1)
                                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)))
                                          inst_1)
                                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                          inst_1)))
                                    (@Subring.toCommRing K (@Field.toCommRing K inst)
                                      (@Valuation.integer K
                                        (@ValuativeRel.ValueGroupWithZero K
                                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)))
                                          inst_1)
                                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)))
                                          inst_1)
                                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                          inst_1)))
                                    (@Subring.instIsDomainSubtypeMem K
                                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      (@instIsDomain K (@Field.toSemifield K inst))
                                      (@Valuation.integer K
                                        (@ValuativeRel.ValueGroupWithZero K
                                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)))
                                          inst_1)
                                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)))
                                          inst_1)
                                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                          inst_1)))
                                    (@IsNonarchimedeanLocalField.instIsDiscreteValuationRingSubtypeMemSubringIntegerValueGroupWithZeroValuation
                                      K inst inst_1 inst_2 inst_3)))))))
                        l] →
                    @Algebra (ZMod l)
                      (@IsLocalRing.ResidueField
                        (↥(@Valuation.integer K
                            (@ValuativeRel.ValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                            (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                        (@Subring.toCommRing K (@Field.toCommRing K inst)
                          (@Valuation.integer K
                            (@ValuativeRel.ValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                            (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                        (@IsDiscreteValuationRing.toIsLocalRing
                          (↥(@Valuation.integer K
                              (@ValuativeRel.ValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                              (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                          (@Subring.toCommRing K (@Field.toCommRing K inst)
                            (@Valuation.integer K
                              (@ValuativeRel.ValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                              (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                          (@Subring.instIsDomainSubtypeMem K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                            (@instIsDomain K (@Field.toSemifield K inst))
                            (@Valuation.integer K
                              (@ValuativeRel.ValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                              (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                          (@IsNonarchimedeanLocalField.instIsDiscreteValuationRingSubtypeMemSubringIntegerValueGroupWithZeroValuation
                            K inst inst_1 inst_2 inst_3)))
                      (@Semifield.toCommSemiring (ZMod l) (@Field.toSemifield (ZMod l) (@ZMod.instField l inst_4)))
                      (@DivisionSemiring.toSemiring
                        (@IsLocalRing.ResidueField
                          (↥(@Valuation.integer K
                              (@ValuativeRel.ValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                              (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                          (@Subring.toCommRing K (@Field.toCommRing K inst)
                            (@Valuation.integer K
                              (@ValuativeRel.ValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                              (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                          (@IsDiscreteValuationRing.toIsLocalRing
                            (↥(@Valuation.integer K
                                (@ValuativeRel.ValueGroupWithZero K
                                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                            (@Subring.toCommRing K (@Field.toCommRing K inst)
                              (@Valuation.integer K
                                (@ValuativeRel.ValueGroupWithZero K
                                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                            (@Subring.instIsDomainSubtypeMem K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                              (@instIsDomain K (@Field.toSemifield K inst))
                              (@Valuation.integer K
                                (@ValuativeRel.ValueGroupWithZero K
                                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                            (@IsNonarchimedeanLocalField.instIsDiscreteValuationRingSubtypeMemSubringIntegerValueGroupWithZeroValuation
                              K inst inst_1 inst_2 inst_3)))
                        (@Semifield.toDivisionSemiring
                          (@IsLocalRing.ResidueField
                            (↥(@Valuation.integer K
                                (@ValuativeRel.ValueGroupWithZero K
                                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                            (@Subring.toCommRing K (@Field.toCommRing K inst)
                              (@Valuation.integer K
                                (@ValuativeRel.ValueGroupWithZero K
                                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                            (@IsDiscreteValuationRing.toIsLocalRing
                              (↥(@Valuation.integer K
                                  (@ValuativeRel.ValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    inst_1)))
                              (@Subring.toCommRing K (@Field.toCommRing K inst)
                                (@Valuation.integer K
                                  (@ValuativeRel.ValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    inst_1)))
                              (@Subring.instIsDomainSubtypeMem K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                (@instIsDomain K (@Field.toSemifield K inst))
                                (@Valuation.integer K
                                  (@ValuativeRel.ValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    inst_1)))
                              (@IsNonarchimedeanLocalField.instIsDiscreteValuationRingSubtypeMemSubringIntegerValueGroupWithZeroValuation
                                K inst inst_1 inst_2 inst_3)))
                          (@Field.toSemifield
                            (@IsLocalRing.ResidueField
                              (↥(@Valuation.integer K
                                  (@ValuativeRel.ValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    inst_1)))
                              (@Subring.toCommRing K (@Field.toCommRing K inst)
                                (@Valuation.integer K
                                  (@ValuativeRel.ValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    inst_1)))
                              (@IsDiscreteValuationRing.toIsLocalRing
                                (↥(@Valuation.integer K
                                    (@ValuativeRel.ValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      inst_1)))
                                (@Subring.toCommRing K (@Field.toCommRing K inst)
                                  (@Valuation.integer K
                                    (@ValuativeRel.ValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      inst_1)))
                                (@Subring.instIsDomainSubtypeMem K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                  (@instIsDomain K (@Field.toSemifield K inst))
                                  (@Valuation.integer K
                                    (@ValuativeRel.ValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      inst_1)))
                                (@IsNonarchimedeanLocalField.instIsDiscreteValuationRingSubtypeMemSubringIntegerValueGroupWithZeroValuation
                                  K inst inst_1 inst_2 inst_3)))
                            (@IsLocalRing.ResidueField.field
                              (↥(@Valuation.integer K
                                  (@ValuativeRel.ValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    inst_1)))
                              (@Subring.toCommRing K (@Field.toCommRing K inst)
                                (@Valuation.integer K
                                  (@ValuativeRel.ValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    inst_1)))
                              (@IsDiscreteValuationRing.toIsLocalRing
                                (↥(@Valuation.integer K
                                    (@ValuativeRel.ValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      inst_1)))
                                (@Subring.toCommRing K (@Field.toCommRing K inst)
                                  (@Valuation.integer K
                                    (@ValuativeRel.ValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      inst_1)))
                                (@Subring.instIsDomainSubtypeMem K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                  (@instIsDomain K (@Field.toSemifield K inst))
                                  (@Valuation.integer K
                                    (@ValuativeRel.ValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      inst_1)))
                                (@IsNonarchimedeanLocalField.instIsDiscreteValuationRingSubtypeMemSubringIntegerValueGroupWithZeroValuation
                                  K inst inst_1 inst_2 inst_3)))))) :=
    fun (K : Type) [inst : Field K]
        [inst_1 :
          @ValuativeRel K (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))]
        [inst_2 : TopologicalSpace K] [inst_3 : @IsNonarchimedeanLocalField K inst inst_1 inst_2] (l : Nat)
        [Fact (Nat.Prime l)]
        [inst_5 :
          @CharP
            (@IsLocalRing.ResidueField
              (↥(@Valuation.integer K
                  (@ValuativeRel.ValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
              (@Subring.toCommRing K (@Field.toCommRing K inst)
                (@Valuation.integer K
                  (@ValuativeRel.ValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
              (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
            (@AddGroupWithOne.toAddMonoidWithOne
              (@IsLocalRing.ResidueField
                (↥(@Valuation.integer K
                    (@ValuativeRel.ValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                (@Subring.toCommRing K (@Field.toCommRing K inst)
                  (@Valuation.integer K
                    (@ValuativeRel.ValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
              (@Ring.toAddGroupWithOne
                (@IsLocalRing.ResidueField
                  (↥(@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@Subring.toCommRing K (@Field.toCommRing K inst)
                    (@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                (@DivisionRing.toRing
                  (@IsLocalRing.ResidueField
                    (↥(@Valuation.integer K
                        (@ValuativeRel.ValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                    (@Subring.toCommRing K (@Field.toCommRing K inst)
                      (@Valuation.integer K
                        (@ValuativeRel.ValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                    (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                  (@Field.toDivisionRing
                    (@IsLocalRing.ResidueField
                      (↥(@Valuation.integer K
                          (@ValuativeRel.ValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                          (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                      (@Subring.toCommRing K (@Field.toCommRing K inst)
                        (@Valuation.integer K
                          (@ValuativeRel.ValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                          (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                      (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                    (@IsLocalRing.ResidueField.field
                      (↥(@Valuation.integer K
                          (@ValuativeRel.ValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                          (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                      (@Subring.toCommRing K (@Field.toCommRing K inst)
                        (@Valuation.integer K
                          (@ValuativeRel.ValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                          (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                      (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))))))
            l] ↦
      @ZMod.algebra
        (@IsLocalRing.ResidueField
          (↥(@Valuation.integer K
              (@ValuativeRel.ValueGroupWithZero K
                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
              (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
              (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
              (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
          (@Subring.toCommRing K (@Field.toCommRing K inst)
            (@Valuation.integer K
              (@ValuativeRel.ValueGroupWithZero K
                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
              (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
              (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
              (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
          (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
        (@DivisionRing.toRing
          (@IsLocalRing.ResidueField
            (↥(@Valuation.integer K
                (@ValuativeRel.ValueGroupWithZero K
                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
            (@Subring.toCommRing K (@Field.toCommRing K inst)
              (@Valuation.integer K
                (@ValuativeRel.ValueGroupWithZero K
                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
            (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
          (@Field.toDivisionRing
            (@IsLocalRing.ResidueField
              (↥(@Valuation.integer K
                  (@ValuativeRel.ValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
              (@Subring.toCommRing K (@Field.toCommRing K inst)
                (@Valuation.integer K
                  (@ValuativeRel.ValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
              (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
            (@IsLocalRing.ResidueField.field
              (↥(@Valuation.integer K
                  (@ValuativeRel.ValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
              (@Subring.toCommRing K (@Field.toCommRing K inst)
                (@Valuation.integer K
                  (@ValuativeRel.ValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
              (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))))
        l inst_5
@[reducible] noncomputable def UpperTheory.Reformulated.B.Qi13.fdim :
    (K : Type) →
      [inst : Field K] →
        [inst_1 :
            @ValuativeRel K
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))] →
          [inst_2 : TopologicalSpace K] →
            [inst_3 : @IsNonarchimedeanLocalField K inst inst_1 inst_2] →
              (l : Nat) →
                [Fact (Nat.Prime l)] →
                  [@CharP
                        (@IsLocalRing.ResidueField
                          (↥(@Valuation.integer K
                              (@ValuativeRel.ValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                              (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                          (@Subring.toCommRing K (@Field.toCommRing K inst)
                            (@Valuation.integer K
                              (@ValuativeRel.ValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                              (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                          (@IsDiscreteValuationRing.toIsLocalRing
                            (↥(@Valuation.integer K
                                (@ValuativeRel.ValueGroupWithZero K
                                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                            (@Subring.toCommRing K (@Field.toCommRing K inst)
                              (@Valuation.integer K
                                (@ValuativeRel.ValueGroupWithZero K
                                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                            (@Subring.instIsDomainSubtypeMem K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                              (@instIsDomain K (@Field.toSemifield K inst))
                              (@Valuation.integer K
                                (@ValuativeRel.ValueGroupWithZero K
                                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                            (@IsNonarchimedeanLocalField.instIsDiscreteValuationRingSubtypeMemSubringIntegerValueGroupWithZeroValuation
                              K inst inst_1 inst_2 inst_3)))
                        (@AddGroupWithOne.toAddMonoidWithOne
                          (@IsLocalRing.ResidueField
                            (↥(@Valuation.integer K
                                (@ValuativeRel.ValueGroupWithZero K
                                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                            (@Subring.toCommRing K (@Field.toCommRing K inst)
                              (@Valuation.integer K
                                (@ValuativeRel.ValueGroupWithZero K
                                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                            (@IsDiscreteValuationRing.toIsLocalRing
                              (↥(@Valuation.integer K
                                  (@ValuativeRel.ValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    inst_1)))
                              (@Subring.toCommRing K (@Field.toCommRing K inst)
                                (@Valuation.integer K
                                  (@ValuativeRel.ValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    inst_1)))
                              (@Subring.instIsDomainSubtypeMem K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                (@instIsDomain K (@Field.toSemifield K inst))
                                (@Valuation.integer K
                                  (@ValuativeRel.ValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    inst_1)))
                              (@IsNonarchimedeanLocalField.instIsDiscreteValuationRingSubtypeMemSubringIntegerValueGroupWithZeroValuation
                                K inst inst_1 inst_2 inst_3)))
                          (@Ring.toAddGroupWithOne
                            (@IsLocalRing.ResidueField
                              (↥(@Valuation.integer K
                                  (@ValuativeRel.ValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    inst_1)))
                              (@Subring.toCommRing K (@Field.toCommRing K inst)
                                (@Valuation.integer K
                                  (@ValuativeRel.ValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    inst_1)))
                              (@IsDiscreteValuationRing.toIsLocalRing
                                (↥(@Valuation.integer K
                                    (@ValuativeRel.ValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      inst_1)))
                                (@Subring.toCommRing K (@Field.toCommRing K inst)
                                  (@Valuation.integer K
                                    (@ValuativeRel.ValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      inst_1)))
                                (@Subring.instIsDomainSubtypeMem K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                  (@instIsDomain K (@Field.toSemifield K inst))
                                  (@Valuation.integer K
                                    (@ValuativeRel.ValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      inst_1)))
                                (@IsNonarchimedeanLocalField.instIsDiscreteValuationRingSubtypeMemSubringIntegerValueGroupWithZeroValuation
                                  K inst inst_1 inst_2 inst_3)))
                            (@DivisionRing.toRing
                              (@IsLocalRing.ResidueField
                                (↥(@Valuation.integer K
                                    (@ValuativeRel.ValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      inst_1)))
                                (@Subring.toCommRing K (@Field.toCommRing K inst)
                                  (@Valuation.integer K
                                    (@ValuativeRel.ValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      inst_1)))
                                (@IsDiscreteValuationRing.toIsLocalRing
                                  (↥(@Valuation.integer K
                                      (@ValuativeRel.ValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                        inst_1)))
                                  (@Subring.toCommRing K (@Field.toCommRing K inst)
                                    (@Valuation.integer K
                                      (@ValuativeRel.ValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                        inst_1)))
                                  (@Subring.instIsDomainSubtypeMem K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    (@instIsDomain K (@Field.toSemifield K inst))
                                    (@Valuation.integer K
                                      (@ValuativeRel.ValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                        inst_1)))
                                  (@IsNonarchimedeanLocalField.instIsDiscreteValuationRingSubtypeMemSubringIntegerValueGroupWithZeroValuation
                                    K inst inst_1 inst_2 inst_3)))
                              (@Field.toDivisionRing
                                (@IsLocalRing.ResidueField
                                  (↥(@Valuation.integer K
                                      (@ValuativeRel.ValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                        inst_1)))
                                  (@Subring.toCommRing K (@Field.toCommRing K inst)
                                    (@Valuation.integer K
                                      (@ValuativeRel.ValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                        inst_1)))
                                  (@IsDiscreteValuationRing.toIsLocalRing
                                    (↥(@Valuation.integer K
                                        (@ValuativeRel.ValueGroupWithZero K
                                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)))
                                          inst_1)
                                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)))
                                          inst_1)
                                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                          inst_1)))
                                    (@Subring.toCommRing K (@Field.toCommRing K inst)
                                      (@Valuation.integer K
                                        (@ValuativeRel.ValueGroupWithZero K
                                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)))
                                          inst_1)
                                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)))
                                          inst_1)
                                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                          inst_1)))
                                    (@Subring.instIsDomainSubtypeMem K
                                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      (@instIsDomain K (@Field.toSemifield K inst))
                                      (@Valuation.integer K
                                        (@ValuativeRel.ValueGroupWithZero K
                                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)))
                                          inst_1)
                                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)))
                                          inst_1)
                                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                          inst_1)))
                                    (@IsNonarchimedeanLocalField.instIsDiscreteValuationRingSubtypeMemSubringIntegerValueGroupWithZeroValuation
                                      K inst inst_1 inst_2 inst_3)))
                                (@IsLocalRing.ResidueField.field
                                  (↥(@Valuation.integer K
                                      (@ValuativeRel.ValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                        inst_1)))
                                  (@Subring.toCommRing K (@Field.toCommRing K inst)
                                    (@Valuation.integer K
                                      (@ValuativeRel.ValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                        inst_1)))
                                  (@IsDiscreteValuationRing.toIsLocalRing
                                    (↥(@Valuation.integer K
                                        (@ValuativeRel.ValueGroupWithZero K
                                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)))
                                          inst_1)
                                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)))
                                          inst_1)
                                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                          inst_1)))
                                    (@Subring.toCommRing K (@Field.toCommRing K inst)
                                      (@Valuation.integer K
                                        (@ValuativeRel.ValueGroupWithZero K
                                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)))
                                          inst_1)
                                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)))
                                          inst_1)
                                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                          inst_1)))
                                    (@Subring.instIsDomainSubtypeMem K
                                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      (@instIsDomain K (@Field.toSemifield K inst))
                                      (@Valuation.integer K
                                        (@ValuativeRel.ValueGroupWithZero K
                                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)))
                                          inst_1)
                                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)))
                                          inst_1)
                                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                          inst_1)))
                                    (@IsNonarchimedeanLocalField.instIsDiscreteValuationRingSubtypeMemSubringIntegerValueGroupWithZeroValuation
                                      K inst inst_1 inst_2 inst_3)))))))
                        l] →
                    Nat :=
    fun (K : Type) [inst : Field K]
        [inst_1 :
          @ValuativeRel K (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))]
        [inst_2 : TopologicalSpace K] [inst_3 : @IsNonarchimedeanLocalField K inst inst_1 inst_2] (l : Nat)
        [inst_4 : Fact (Nat.Prime l)]
        [inst_5 :
          @CharP
            (@IsLocalRing.ResidueField
              (↥(@Valuation.integer K
                  (@ValuativeRel.ValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
              (@Subring.toCommRing K (@Field.toCommRing K inst)
                (@Valuation.integer K
                  (@ValuativeRel.ValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
              (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
            (@AddGroupWithOne.toAddMonoidWithOne
              (@IsLocalRing.ResidueField
                (↥(@Valuation.integer K
                    (@ValuativeRel.ValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                (@Subring.toCommRing K (@Field.toCommRing K inst)
                  (@Valuation.integer K
                    (@ValuativeRel.ValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
              (@Ring.toAddGroupWithOne
                (@IsLocalRing.ResidueField
                  (↥(@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@Subring.toCommRing K (@Field.toCommRing K inst)
                    (@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                (@DivisionRing.toRing
                  (@IsLocalRing.ResidueField
                    (↥(@Valuation.integer K
                        (@ValuativeRel.ValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                    (@Subring.toCommRing K (@Field.toCommRing K inst)
                      (@Valuation.integer K
                        (@ValuativeRel.ValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                    (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                  (@Field.toDivisionRing
                    (@IsLocalRing.ResidueField
                      (↥(@Valuation.integer K
                          (@ValuativeRel.ValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                          (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                      (@Subring.toCommRing K (@Field.toCommRing K inst)
                        (@Valuation.integer K
                          (@ValuativeRel.ValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                          (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                      (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                    (@IsLocalRing.ResidueField.field
                      (↥(@Valuation.integer K
                          (@ValuativeRel.ValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                          (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                      (@Subring.toCommRing K (@Field.toCommRing K inst)
                        (@Valuation.integer K
                          (@ValuativeRel.ValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                          (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                      (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))))))
            l] ↦
      @Module.finrank (ZMod l)
        (@IsLocalRing.ResidueField
          (↥(@Valuation.integer K
              (@ValuativeRel.ValueGroupWithZero K
                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
              (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
              (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
              (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
          (@Subring.toCommRing K (@Field.toCommRing K inst)
            (@Valuation.integer K
              (@ValuativeRel.ValueGroupWithZero K
                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
              (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
              (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
              (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
          (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
        (@DivisionSemiring.toSemiring (ZMod l)
          (@Semifield.toDivisionSemiring (ZMod l) (@Field.toSemifield (ZMod l) (@ZMod.instField l inst_4))))
        (@Semiring.toAddCommMonoid
          (@IsLocalRing.ResidueField
            (↥(@Valuation.integer K
                (@ValuativeRel.ValueGroupWithZero K
                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
            (@Subring.toCommRing K (@Field.toCommRing K inst)
              (@Valuation.integer K
                (@ValuativeRel.ValueGroupWithZero K
                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
            (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
          (@DivisionSemiring.toSemiring
            (@IsLocalRing.ResidueField
              (↥(@Valuation.integer K
                  (@ValuativeRel.ValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
              (@Subring.toCommRing K (@Field.toCommRing K inst)
                (@Valuation.integer K
                  (@ValuativeRel.ValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
              (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
            (@Semifield.toDivisionSemiring
              (@IsLocalRing.ResidueField
                (↥(@Valuation.integer K
                    (@ValuativeRel.ValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                (@Subring.toCommRing K (@Field.toCommRing K inst)
                  (@Valuation.integer K
                    (@ValuativeRel.ValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
              (@Field.toSemifield
                (@IsLocalRing.ResidueField
                  (↥(@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@Subring.toCommRing K (@Field.toCommRing K inst)
                    (@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                (@IsLocalRing.ResidueField.field
                  (↥(@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@Subring.toCommRing K (@Field.toCommRing K inst)
                    (@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))))))
        (@Algebra.toModule (ZMod l)
          (@IsLocalRing.ResidueField
            (↥(@Valuation.integer K
                (@ValuativeRel.ValueGroupWithZero K
                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
            (@Subring.toCommRing K (@Field.toCommRing K inst)
              (@Valuation.integer K
                (@ValuativeRel.ValueGroupWithZero K
                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
            (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
          (@Semifield.toCommSemiring (ZMod l) (@Field.toSemifield (ZMod l) (@ZMod.instField l inst_4)))
          (@DivisionSemiring.toSemiring
            (@IsLocalRing.ResidueField
              (↥(@Valuation.integer K
                  (@ValuativeRel.ValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
              (@Subring.toCommRing K (@Field.toCommRing K inst)
                (@Valuation.integer K
                  (@ValuativeRel.ValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
              (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
            (@Semifield.toDivisionSemiring
              (@IsLocalRing.ResidueField
                (↥(@Valuation.integer K
                    (@ValuativeRel.ValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                (@Subring.toCommRing K (@Field.toCommRing K inst)
                  (@Valuation.integer K
                    (@ValuativeRel.ValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
              (@Field.toSemifield
                (@IsLocalRing.ResidueField
                  (↥(@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@Subring.toCommRing K (@Field.toCommRing K inst)
                    (@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                (@IsLocalRing.ResidueField.field
                  (↥(@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@Subring.toCommRing K (@Field.toCommRing K inst)
                    (@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3)))))
          (@UpperTheory.Reformulated.B.Qi13.algRes K inst inst_1 inst_2 inst_3 l inst_4 inst_5))
theorem UpperTheory.Reformulated.B.Qi13.aux4 :
    ∀ (K : Type) [inst : Field K]
      [inst_1 :
        @ValuativeRel K (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))]
      [inst_2 : TopologicalSpace K] [inst_3 : @IsNonarchimedeanLocalField K inst inst_1 inst_2] (l : Nat)
      [inst_4 : Fact (Nat.Prime l)]
      [inst_5 :
        @CharP
          (@IsLocalRing.ResidueField
            (↥(@Valuation.integer K
                (@ValuativeRel.ValueGroupWithZero K
                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
            (@Subring.toCommRing K (@Field.toCommRing K inst)
              (@Valuation.integer K
                (@ValuativeRel.ValueGroupWithZero K
                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
            (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
          (@AddGroupWithOne.toAddMonoidWithOne
            (@IsLocalRing.ResidueField
              (↥(@Valuation.integer K
                  (@ValuativeRel.ValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
              (@Subring.toCommRing K (@Field.toCommRing K inst)
                (@Valuation.integer K
                  (@ValuativeRel.ValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
              (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
            (@Ring.toAddGroupWithOne
              (@IsLocalRing.ResidueField
                (↥(@Valuation.integer K
                    (@ValuativeRel.ValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                (@Subring.toCommRing K (@Field.toCommRing K inst)
                  (@Valuation.integer K
                    (@ValuativeRel.ValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
              (@DivisionRing.toRing
                (@IsLocalRing.ResidueField
                  (↥(@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@Subring.toCommRing K (@Field.toCommRing K inst)
                    (@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                (@Field.toDivisionRing
                  (@IsLocalRing.ResidueField
                    (↥(@Valuation.integer K
                        (@ValuativeRel.ValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                    (@Subring.toCommRing K (@Field.toCommRing K inst)
                      (@Valuation.integer K
                        (@ValuativeRel.ValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                    (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                  (@IsLocalRing.ResidueField.field
                    (↥(@Valuation.integer K
                        (@ValuativeRel.ValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                    (@Subring.toCommRing K (@Field.toCommRing K inst)
                      (@Valuation.integer K
                        (@ValuativeRel.ValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                    (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))))))
          l],
      @Module.Free (ZMod l)
        (@IsLocalRing.ResidueField
          (↥(@Valuation.integer K
              (@ValuativeRel.ValueGroupWithZero K
                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
              (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
              (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
              (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
          (@Subring.toCommRing K (@Field.toCommRing K inst)
            (@Valuation.integer K
              (@ValuativeRel.ValueGroupWithZero K
                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
              (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
              (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
              (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
          (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
        (@CommSemiring.toSemiring (ZMod l) (@CommRing.toCommSemiring (ZMod l) (ZMod.commRing l)))
        (@AddCommGroup.toAddCommMonoid
          (@IsLocalRing.ResidueField
            (↥(@Valuation.integer K
                (@ValuativeRel.ValueGroupWithZero K
                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
            (@Subring.toCommRing K (@Field.toCommRing K inst)
              (@Valuation.integer K
                (@ValuativeRel.ValueGroupWithZero K
                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
            (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
          (@Ring.toAddCommGroup
            (@IsLocalRing.ResidueField
              (↥(@Valuation.integer K
                  (@ValuativeRel.ValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
              (@Subring.toCommRing K (@Field.toCommRing K inst)
                (@Valuation.integer K
                  (@ValuativeRel.ValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
              (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
            (@DivisionRing.toRing
              (@IsLocalRing.ResidueField
                (↥(@Valuation.integer K
                    (@ValuativeRel.ValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                (@Subring.toCommRing K (@Field.toCommRing K inst)
                  (@Valuation.integer K
                    (@ValuativeRel.ValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
              (@Field.toDivisionRing
                (@IsLocalRing.ResidueField
                  (↥(@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@Subring.toCommRing K (@Field.toCommRing K inst)
                    (@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                (@IsLocalRing.ResidueField.field
                  (↥(@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@Subring.toCommRing K (@Field.toCommRing K inst)
                    (@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))))))
        (@Algebra.toModule (ZMod l)
          (@IsLocalRing.ResidueField
            (↥(@Valuation.integer K
                (@ValuativeRel.ValueGroupWithZero K
                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
            (@Subring.toCommRing K (@Field.toCommRing K inst)
              (@Valuation.integer K
                (@ValuativeRel.ValueGroupWithZero K
                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
            (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
          (@Semifield.toCommSemiring (ZMod l) (@Field.toSemifield (ZMod l) (@ZMod.instField l inst_4)))
          (@DivisionSemiring.toSemiring
            (@IsLocalRing.ResidueField
              (↥(@Valuation.integer K
                  (@ValuativeRel.ValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
              (@Subring.toCommRing K (@Field.toCommRing K inst)
                (@Valuation.integer K
                  (@ValuativeRel.ValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
              (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
            (@Semifield.toDivisionSemiring
              (@IsLocalRing.ResidueField
                (↥(@Valuation.integer K
                    (@ValuativeRel.ValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                (@Subring.toCommRing K (@Field.toCommRing K inst)
                  (@Valuation.integer K
                    (@ValuativeRel.ValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
              (@Field.toSemifield
                (@IsLocalRing.ResidueField
                  (↥(@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@Subring.toCommRing K (@Field.toCommRing K inst)
                    (@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                (@IsLocalRing.ResidueField.field
                  (↥(@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@Subring.toCommRing K (@Field.toCommRing K inst)
                    (@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3)))))
          (@UpperTheory.Reformulated.B.Qi13.algRes K inst inst_1 inst_2 inst_3 l inst_4 inst_5)) := by
  intro K _ _ _ _ l _ _
  letI := UpperTheory.Reformulated.B.Qi13.algRes K l
  exact Module.Free.of_divisionRing (ZMod l) _
theorem UpperTheory.Reformulated.B.Qi13.aux5 :
    ∀ (l : Nat) [Fact (Nat.Prime l)],
      @StrongRankCondition (ZMod l)
        (@CommSemiring.toSemiring (ZMod l) (@CommRing.toCommSemiring (ZMod l) (ZMod.commRing l))) := by
  intro l _
  infer_instance
theorem UpperTheory.Reformulated.B.Qi13.aux6 :
    ∀ (K : Type) [inst : Field K]
      [inst_1 :
        @ValuativeRel K (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))]
      [inst_2 : TopologicalSpace K] [inst_3 : @IsNonarchimedeanLocalField K inst inst_1 inst_2] (l : Nat)
      [inst_4 : Fact (Nat.Prime l)]
      [inst_5 :
        @CharP
          (@IsLocalRing.ResidueField
            (↥(@Valuation.integer K
                (@ValuativeRel.ValueGroupWithZero K
                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
            (@Subring.toCommRing K (@Field.toCommRing K inst)
              (@Valuation.integer K
                (@ValuativeRel.ValueGroupWithZero K
                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
            (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
          (@AddGroupWithOne.toAddMonoidWithOne
            (@IsLocalRing.ResidueField
              (↥(@Valuation.integer K
                  (@ValuativeRel.ValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
              (@Subring.toCommRing K (@Field.toCommRing K inst)
                (@Valuation.integer K
                  (@ValuativeRel.ValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
              (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
            (@Ring.toAddGroupWithOne
              (@IsLocalRing.ResidueField
                (↥(@Valuation.integer K
                    (@ValuativeRel.ValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                (@Subring.toCommRing K (@Field.toCommRing K inst)
                  (@Valuation.integer K
                    (@ValuativeRel.ValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
              (@DivisionRing.toRing
                (@IsLocalRing.ResidueField
                  (↥(@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@Subring.toCommRing K (@Field.toCommRing K inst)
                    (@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                (@Field.toDivisionRing
                  (@IsLocalRing.ResidueField
                    (↥(@Valuation.integer K
                        (@ValuativeRel.ValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                    (@Subring.toCommRing K (@Field.toCommRing K inst)
                      (@Valuation.integer K
                        (@ValuativeRel.ValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                    (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                  (@IsLocalRing.ResidueField.field
                    (↥(@Valuation.integer K
                        (@ValuativeRel.ValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                    (@Subring.toCommRing K (@Field.toCommRing K inst)
                      (@Valuation.integer K
                        (@ValuativeRel.ValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                    (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))))))
          l],
      @Module.Finite (ZMod l)
        (@IsLocalRing.ResidueField
          (↥(@Valuation.integer K
              (@ValuativeRel.ValueGroupWithZero K
                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
              (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
              (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
              (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
          (@Subring.toCommRing K (@Field.toCommRing K inst)
            (@Valuation.integer K
              (@ValuativeRel.ValueGroupWithZero K
                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
              (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
              (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
              (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
          (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
        (@DivisionSemiring.toSemiring (ZMod l)
          (@Semifield.toDivisionSemiring (ZMod l) (@Field.toSemifield (ZMod l) (@ZMod.instField l inst_4))))
        (@Semiring.toAddCommMonoid
          (@IsLocalRing.ResidueField
            (↥(@Valuation.integer K
                (@ValuativeRel.ValueGroupWithZero K
                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
            (@Subring.toCommRing K (@Field.toCommRing K inst)
              (@Valuation.integer K
                (@ValuativeRel.ValueGroupWithZero K
                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
            (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
          (@DivisionSemiring.toSemiring
            (@IsLocalRing.ResidueField
              (↥(@Valuation.integer K
                  (@ValuativeRel.ValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
              (@Subring.toCommRing K (@Field.toCommRing K inst)
                (@Valuation.integer K
                  (@ValuativeRel.ValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
              (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
            (@Semifield.toDivisionSemiring
              (@IsLocalRing.ResidueField
                (↥(@Valuation.integer K
                    (@ValuativeRel.ValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                (@Subring.toCommRing K (@Field.toCommRing K inst)
                  (@Valuation.integer K
                    (@ValuativeRel.ValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
              (@Field.toSemifield
                (@IsLocalRing.ResidueField
                  (↥(@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@Subring.toCommRing K (@Field.toCommRing K inst)
                    (@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                (@IsLocalRing.ResidueField.field
                  (↥(@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@Subring.toCommRing K (@Field.toCommRing K inst)
                    (@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))))))
        (@Algebra.toModule (ZMod l)
          (@IsLocalRing.ResidueField
            (↥(@Valuation.integer K
                (@ValuativeRel.ValueGroupWithZero K
                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
            (@Subring.toCommRing K (@Field.toCommRing K inst)
              (@Valuation.integer K
                (@ValuativeRel.ValueGroupWithZero K
                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
            (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
          (@Semifield.toCommSemiring (ZMod l) (@Field.toSemifield (ZMod l) (@ZMod.instField l inst_4)))
          (@DivisionSemiring.toSemiring
            (@IsLocalRing.ResidueField
              (↥(@Valuation.integer K
                  (@ValuativeRel.ValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
              (@Subring.toCommRing K (@Field.toCommRing K inst)
                (@Valuation.integer K
                  (@ValuativeRel.ValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
              (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
            (@Semifield.toDivisionSemiring
              (@IsLocalRing.ResidueField
                (↥(@Valuation.integer K
                    (@ValuativeRel.ValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                (@Subring.toCommRing K (@Field.toCommRing K inst)
                  (@Valuation.integer K
                    (@ValuativeRel.ValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
              (@Field.toSemifield
                (@IsLocalRing.ResidueField
                  (↥(@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@Subring.toCommRing K (@Field.toCommRing K inst)
                    (@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                (@IsLocalRing.ResidueField.field
                  (↥(@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@Subring.toCommRing K (@Field.toCommRing K inst)
                    (@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3)))))
          (@UpperTheory.Reformulated.B.Qi13.algRes K inst inst_1 inst_2 inst_3 l inst_4 inst_5)) := by
  intro K _ _ _ _ l _ _
  letI := UpperTheory.Reformulated.B.Qi13.algRes K l
  haveI : Finite (IsLocalRing.ResidueField (ValuativeRel.valuation K).integer) := inferInstance
  exact Module.Finite.of_finite
noncomputable def UpperTheory.Reformulated.B.Qi13.bb :
    (K : Type) →
      [inst : Field K] →
        [inst_1 :
            @ValuativeRel K
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))] →
          [inst_2 : TopologicalSpace K] →
            [inst_3 : @IsNonarchimedeanLocalField K inst inst_1 inst_2] →
              (l : Nat) →
                [inst_4 : Fact (Nat.Prime l)] →
                  [inst_5 :
                      @CharP
                        (@IsLocalRing.ResidueField
                          (↥(@Valuation.integer K
                              (@ValuativeRel.ValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                              (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                          (@Subring.toCommRing K (@Field.toCommRing K inst)
                            (@Valuation.integer K
                              (@ValuativeRel.ValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                              (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                          (@IsDiscreteValuationRing.toIsLocalRing
                            (↥(@Valuation.integer K
                                (@ValuativeRel.ValueGroupWithZero K
                                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                            (@Subring.toCommRing K (@Field.toCommRing K inst)
                              (@Valuation.integer K
                                (@ValuativeRel.ValueGroupWithZero K
                                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                            (@Subring.instIsDomainSubtypeMem K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                              (@instIsDomain K (@Field.toSemifield K inst))
                              (@Valuation.integer K
                                (@ValuativeRel.ValueGroupWithZero K
                                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                            (@IsNonarchimedeanLocalField.instIsDiscreteValuationRingSubtypeMemSubringIntegerValueGroupWithZeroValuation
                              K inst inst_1 inst_2 inst_3)))
                        (@AddGroupWithOne.toAddMonoidWithOne
                          (@IsLocalRing.ResidueField
                            (↥(@Valuation.integer K
                                (@ValuativeRel.ValueGroupWithZero K
                                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                            (@Subring.toCommRing K (@Field.toCommRing K inst)
                              (@Valuation.integer K
                                (@ValuativeRel.ValueGroupWithZero K
                                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                            (@IsDiscreteValuationRing.toIsLocalRing
                              (↥(@Valuation.integer K
                                  (@ValuativeRel.ValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    inst_1)))
                              (@Subring.toCommRing K (@Field.toCommRing K inst)
                                (@Valuation.integer K
                                  (@ValuativeRel.ValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    inst_1)))
                              (@Subring.instIsDomainSubtypeMem K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                (@instIsDomain K (@Field.toSemifield K inst))
                                (@Valuation.integer K
                                  (@ValuativeRel.ValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    inst_1)))
                              (@IsNonarchimedeanLocalField.instIsDiscreteValuationRingSubtypeMemSubringIntegerValueGroupWithZeroValuation
                                K inst inst_1 inst_2 inst_3)))
                          (@Ring.toAddGroupWithOne
                            (@IsLocalRing.ResidueField
                              (↥(@Valuation.integer K
                                  (@ValuativeRel.ValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    inst_1)))
                              (@Subring.toCommRing K (@Field.toCommRing K inst)
                                (@Valuation.integer K
                                  (@ValuativeRel.ValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    inst_1)))
                              (@IsDiscreteValuationRing.toIsLocalRing
                                (↥(@Valuation.integer K
                                    (@ValuativeRel.ValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      inst_1)))
                                (@Subring.toCommRing K (@Field.toCommRing K inst)
                                  (@Valuation.integer K
                                    (@ValuativeRel.ValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      inst_1)))
                                (@Subring.instIsDomainSubtypeMem K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                  (@instIsDomain K (@Field.toSemifield K inst))
                                  (@Valuation.integer K
                                    (@ValuativeRel.ValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      inst_1)))
                                (@IsNonarchimedeanLocalField.instIsDiscreteValuationRingSubtypeMemSubringIntegerValueGroupWithZeroValuation
                                  K inst inst_1 inst_2 inst_3)))
                            (@DivisionRing.toRing
                              (@IsLocalRing.ResidueField
                                (↥(@Valuation.integer K
                                    (@ValuativeRel.ValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      inst_1)))
                                (@Subring.toCommRing K (@Field.toCommRing K inst)
                                  (@Valuation.integer K
                                    (@ValuativeRel.ValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      inst_1)))
                                (@IsDiscreteValuationRing.toIsLocalRing
                                  (↥(@Valuation.integer K
                                      (@ValuativeRel.ValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                        inst_1)))
                                  (@Subring.toCommRing K (@Field.toCommRing K inst)
                                    (@Valuation.integer K
                                      (@ValuativeRel.ValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                        inst_1)))
                                  (@Subring.instIsDomainSubtypeMem K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    (@instIsDomain K (@Field.toSemifield K inst))
                                    (@Valuation.integer K
                                      (@ValuativeRel.ValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                        inst_1)))
                                  (@IsNonarchimedeanLocalField.instIsDiscreteValuationRingSubtypeMemSubringIntegerValueGroupWithZeroValuation
                                    K inst inst_1 inst_2 inst_3)))
                              (@Field.toDivisionRing
                                (@IsLocalRing.ResidueField
                                  (↥(@Valuation.integer K
                                      (@ValuativeRel.ValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                        inst_1)))
                                  (@Subring.toCommRing K (@Field.toCommRing K inst)
                                    (@Valuation.integer K
                                      (@ValuativeRel.ValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                        inst_1)))
                                  (@IsDiscreteValuationRing.toIsLocalRing
                                    (↥(@Valuation.integer K
                                        (@ValuativeRel.ValueGroupWithZero K
                                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)))
                                          inst_1)
                                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)))
                                          inst_1)
                                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                          inst_1)))
                                    (@Subring.toCommRing K (@Field.toCommRing K inst)
                                      (@Valuation.integer K
                                        (@ValuativeRel.ValueGroupWithZero K
                                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)))
                                          inst_1)
                                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)))
                                          inst_1)
                                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                          inst_1)))
                                    (@Subring.instIsDomainSubtypeMem K
                                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      (@instIsDomain K (@Field.toSemifield K inst))
                                      (@Valuation.integer K
                                        (@ValuativeRel.ValueGroupWithZero K
                                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)))
                                          inst_1)
                                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)))
                                          inst_1)
                                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                          inst_1)))
                                    (@IsNonarchimedeanLocalField.instIsDiscreteValuationRingSubtypeMemSubringIntegerValueGroupWithZeroValuation
                                      K inst inst_1 inst_2 inst_3)))
                                (@IsLocalRing.ResidueField.field
                                  (↥(@Valuation.integer K
                                      (@ValuativeRel.ValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                        inst_1)))
                                  (@Subring.toCommRing K (@Field.toCommRing K inst)
                                    (@Valuation.integer K
                                      (@ValuativeRel.ValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                        inst_1)))
                                  (@IsDiscreteValuationRing.toIsLocalRing
                                    (↥(@Valuation.integer K
                                        (@ValuativeRel.ValueGroupWithZero K
                                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)))
                                          inst_1)
                                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)))
                                          inst_1)
                                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                          inst_1)))
                                    (@Subring.toCommRing K (@Field.toCommRing K inst)
                                      (@Valuation.integer K
                                        (@ValuativeRel.ValueGroupWithZero K
                                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)))
                                          inst_1)
                                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)))
                                          inst_1)
                                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                          inst_1)))
                                    (@Subring.instIsDomainSubtypeMem K
                                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      (@instIsDomain K (@Field.toSemifield K inst))
                                      (@Valuation.integer K
                                        (@ValuativeRel.ValueGroupWithZero K
                                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)))
                                          inst_1)
                                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)))
                                          inst_1)
                                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                          inst_1)))
                                    (@IsNonarchimedeanLocalField.instIsDiscreteValuationRingSubtypeMemSubringIntegerValueGroupWithZeroValuation
                                      K inst inst_1 inst_2 inst_3)))))))
                        l] →
                    @Module.Basis (Fin (@UpperTheory.Reformulated.B.Qi13.fdim K inst inst_1 inst_2 inst_3 l inst_4 inst_5)) (ZMod l)
                      (@IsLocalRing.ResidueField
                        (↥(@Valuation.integer K
                            (@ValuativeRel.ValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                            (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                        (@Subring.toCommRing K (@Field.toCommRing K inst)
                          (@Valuation.integer K
                            (@ValuativeRel.ValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                            (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                        (@IsDiscreteValuationRing.toIsLocalRing
                          (↥(@Valuation.integer K
                              (@ValuativeRel.ValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                              (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                          (@Subring.toCommRing K (@Field.toCommRing K inst)
                            (@Valuation.integer K
                              (@ValuativeRel.ValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                              (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                          (@Subring.instIsDomainSubtypeMem K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                            (@instIsDomain K (@Field.toSemifield K inst))
                            (@Valuation.integer K
                              (@ValuativeRel.ValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                              (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                          (@IsNonarchimedeanLocalField.instIsDiscreteValuationRingSubtypeMemSubringIntegerValueGroupWithZeroValuation
                            K inst inst_1 inst_2 inst_3)))
                      (@DivisionSemiring.toSemiring (ZMod l)
                        (@Semifield.toDivisionSemiring (ZMod l) (@Field.toSemifield (ZMod l) (@ZMod.instField l inst_4))))
                      (@Semiring.toAddCommMonoid
                        (@IsLocalRing.ResidueField
                          (↥(@Valuation.integer K
                              (@ValuativeRel.ValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                              (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                          (@Subring.toCommRing K (@Field.toCommRing K inst)
                            (@Valuation.integer K
                              (@ValuativeRel.ValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                              (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                          (@IsDiscreteValuationRing.toIsLocalRing
                            (↥(@Valuation.integer K
                                (@ValuativeRel.ValueGroupWithZero K
                                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                            (@Subring.toCommRing K (@Field.toCommRing K inst)
                              (@Valuation.integer K
                                (@ValuativeRel.ValueGroupWithZero K
                                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                            (@Subring.instIsDomainSubtypeMem K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                              (@instIsDomain K (@Field.toSemifield K inst))
                              (@Valuation.integer K
                                (@ValuativeRel.ValueGroupWithZero K
                                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                            (@IsNonarchimedeanLocalField.instIsDiscreteValuationRingSubtypeMemSubringIntegerValueGroupWithZeroValuation
                              K inst inst_1 inst_2 inst_3)))
                        (@DivisionSemiring.toSemiring
                          (@IsLocalRing.ResidueField
                            (↥(@Valuation.integer K
                                (@ValuativeRel.ValueGroupWithZero K
                                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                            (@Subring.toCommRing K (@Field.toCommRing K inst)
                              (@Valuation.integer K
                                (@ValuativeRel.ValueGroupWithZero K
                                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                            (@IsDiscreteValuationRing.toIsLocalRing
                              (↥(@Valuation.integer K
                                  (@ValuativeRel.ValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    inst_1)))
                              (@Subring.toCommRing K (@Field.toCommRing K inst)
                                (@Valuation.integer K
                                  (@ValuativeRel.ValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    inst_1)))
                              (@Subring.instIsDomainSubtypeMem K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                (@instIsDomain K (@Field.toSemifield K inst))
                                (@Valuation.integer K
                                  (@ValuativeRel.ValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    inst_1)))
                              (@IsNonarchimedeanLocalField.instIsDiscreteValuationRingSubtypeMemSubringIntegerValueGroupWithZeroValuation
                                K inst inst_1 inst_2 inst_3)))
                          (@Semifield.toDivisionSemiring
                            (@IsLocalRing.ResidueField
                              (↥(@Valuation.integer K
                                  (@ValuativeRel.ValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    inst_1)))
                              (@Subring.toCommRing K (@Field.toCommRing K inst)
                                (@Valuation.integer K
                                  (@ValuativeRel.ValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    inst_1)))
                              (@IsDiscreteValuationRing.toIsLocalRing
                                (↥(@Valuation.integer K
                                    (@ValuativeRel.ValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      inst_1)))
                                (@Subring.toCommRing K (@Field.toCommRing K inst)
                                  (@Valuation.integer K
                                    (@ValuativeRel.ValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      inst_1)))
                                (@Subring.instIsDomainSubtypeMem K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                  (@instIsDomain K (@Field.toSemifield K inst))
                                  (@Valuation.integer K
                                    (@ValuativeRel.ValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      inst_1)))
                                (@IsNonarchimedeanLocalField.instIsDiscreteValuationRingSubtypeMemSubringIntegerValueGroupWithZeroValuation
                                  K inst inst_1 inst_2 inst_3)))
                            (@Field.toSemifield
                              (@IsLocalRing.ResidueField
                                (↥(@Valuation.integer K
                                    (@ValuativeRel.ValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      inst_1)))
                                (@Subring.toCommRing K (@Field.toCommRing K inst)
                                  (@Valuation.integer K
                                    (@ValuativeRel.ValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      inst_1)))
                                (@IsDiscreteValuationRing.toIsLocalRing
                                  (↥(@Valuation.integer K
                                      (@ValuativeRel.ValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                        inst_1)))
                                  (@Subring.toCommRing K (@Field.toCommRing K inst)
                                    (@Valuation.integer K
                                      (@ValuativeRel.ValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                        inst_1)))
                                  (@Subring.instIsDomainSubtypeMem K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    (@instIsDomain K (@Field.toSemifield K inst))
                                    (@Valuation.integer K
                                      (@ValuativeRel.ValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                        inst_1)))
                                  (@IsNonarchimedeanLocalField.instIsDiscreteValuationRingSubtypeMemSubringIntegerValueGroupWithZeroValuation
                                    K inst inst_1 inst_2 inst_3)))
                              (@IsLocalRing.ResidueField.field
                                (↥(@Valuation.integer K
                                    (@ValuativeRel.ValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      inst_1)))
                                (@Subring.toCommRing K (@Field.toCommRing K inst)
                                  (@Valuation.integer K
                                    (@ValuativeRel.ValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      inst_1)))
                                (@IsDiscreteValuationRing.toIsLocalRing
                                  (↥(@Valuation.integer K
                                      (@ValuativeRel.ValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                        inst_1)))
                                  (@Subring.toCommRing K (@Field.toCommRing K inst)
                                    (@Valuation.integer K
                                      (@ValuativeRel.ValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                        inst_1)))
                                  (@Subring.instIsDomainSubtypeMem K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    (@instIsDomain K (@Field.toSemifield K inst))
                                    (@Valuation.integer K
                                      (@ValuativeRel.ValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                        inst_1)))
                                  (@IsNonarchimedeanLocalField.instIsDiscreteValuationRingSubtypeMemSubringIntegerValueGroupWithZeroValuation
                                    K inst inst_1 inst_2 inst_3)))))))
                      (@Algebra.toModule (ZMod l)
                        (@IsLocalRing.ResidueField
                          (↥(@Valuation.integer K
                              (@ValuativeRel.ValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                              (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                          (@Subring.toCommRing K (@Field.toCommRing K inst)
                            (@Valuation.integer K
                              (@ValuativeRel.ValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                              (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                          (@IsDiscreteValuationRing.toIsLocalRing
                            (↥(@Valuation.integer K
                                (@ValuativeRel.ValueGroupWithZero K
                                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                            (@Subring.toCommRing K (@Field.toCommRing K inst)
                              (@Valuation.integer K
                                (@ValuativeRel.ValueGroupWithZero K
                                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                            (@Subring.instIsDomainSubtypeMem K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                              (@instIsDomain K (@Field.toSemifield K inst))
                              (@Valuation.integer K
                                (@ValuativeRel.ValueGroupWithZero K
                                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                            (@IsNonarchimedeanLocalField.instIsDiscreteValuationRingSubtypeMemSubringIntegerValueGroupWithZeroValuation
                              K inst inst_1 inst_2 inst_3)))
                        (@Semifield.toCommSemiring (ZMod l) (@Field.toSemifield (ZMod l) (@ZMod.instField l inst_4)))
                        (@DivisionSemiring.toSemiring
                          (@IsLocalRing.ResidueField
                            (↥(@Valuation.integer K
                                (@ValuativeRel.ValueGroupWithZero K
                                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                            (@Subring.toCommRing K (@Field.toCommRing K inst)
                              (@Valuation.integer K
                                (@ValuativeRel.ValueGroupWithZero K
                                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                            (@IsDiscreteValuationRing.toIsLocalRing
                              (↥(@Valuation.integer K
                                  (@ValuativeRel.ValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    inst_1)))
                              (@Subring.toCommRing K (@Field.toCommRing K inst)
                                (@Valuation.integer K
                                  (@ValuativeRel.ValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    inst_1)))
                              (@Subring.instIsDomainSubtypeMem K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                (@instIsDomain K (@Field.toSemifield K inst))
                                (@Valuation.integer K
                                  (@ValuativeRel.ValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    inst_1)))
                              (@IsNonarchimedeanLocalField.instIsDiscreteValuationRingSubtypeMemSubringIntegerValueGroupWithZeroValuation
                                K inst inst_1 inst_2 inst_3)))
                          (@Semifield.toDivisionSemiring
                            (@IsLocalRing.ResidueField
                              (↥(@Valuation.integer K
                                  (@ValuativeRel.ValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    inst_1)))
                              (@Subring.toCommRing K (@Field.toCommRing K inst)
                                (@Valuation.integer K
                                  (@ValuativeRel.ValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    inst_1)))
                              (@IsDiscreteValuationRing.toIsLocalRing
                                (↥(@Valuation.integer K
                                    (@ValuativeRel.ValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      inst_1)))
                                (@Subring.toCommRing K (@Field.toCommRing K inst)
                                  (@Valuation.integer K
                                    (@ValuativeRel.ValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      inst_1)))
                                (@Subring.instIsDomainSubtypeMem K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                  (@instIsDomain K (@Field.toSemifield K inst))
                                  (@Valuation.integer K
                                    (@ValuativeRel.ValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      inst_1)))
                                (@IsNonarchimedeanLocalField.instIsDiscreteValuationRingSubtypeMemSubringIntegerValueGroupWithZeroValuation
                                  K inst inst_1 inst_2 inst_3)))
                            (@Field.toSemifield
                              (@IsLocalRing.ResidueField
                                (↥(@Valuation.integer K
                                    (@ValuativeRel.ValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      inst_1)))
                                (@Subring.toCommRing K (@Field.toCommRing K inst)
                                  (@Valuation.integer K
                                    (@ValuativeRel.ValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      inst_1)))
                                (@IsDiscreteValuationRing.toIsLocalRing
                                  (↥(@Valuation.integer K
                                      (@ValuativeRel.ValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                        inst_1)))
                                  (@Subring.toCommRing K (@Field.toCommRing K inst)
                                    (@Valuation.integer K
                                      (@ValuativeRel.ValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                        inst_1)))
                                  (@Subring.instIsDomainSubtypeMem K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    (@instIsDomain K (@Field.toSemifield K inst))
                                    (@Valuation.integer K
                                      (@ValuativeRel.ValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                        inst_1)))
                                  (@IsNonarchimedeanLocalField.instIsDiscreteValuationRingSubtypeMemSubringIntegerValueGroupWithZeroValuation
                                    K inst inst_1 inst_2 inst_3)))
                              (@IsLocalRing.ResidueField.field
                                (↥(@Valuation.integer K
                                    (@ValuativeRel.ValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      inst_1)))
                                (@Subring.toCommRing K (@Field.toCommRing K inst)
                                  (@Valuation.integer K
                                    (@ValuativeRel.ValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      inst_1)))
                                (@IsDiscreteValuationRing.toIsLocalRing
                                  (↥(@Valuation.integer K
                                      (@ValuativeRel.ValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                        inst_1)))
                                  (@Subring.toCommRing K (@Field.toCommRing K inst)
                                    (@Valuation.integer K
                                      (@ValuativeRel.ValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                        inst_1)))
                                  (@Subring.instIsDomainSubtypeMem K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    (@instIsDomain K (@Field.toSemifield K inst))
                                    (@Valuation.integer K
                                      (@ValuativeRel.ValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                        inst_1)))
                                  (@IsNonarchimedeanLocalField.instIsDiscreteValuationRingSubtypeMemSubringIntegerValueGroupWithZeroValuation
                                    K inst inst_1 inst_2 inst_3))))))
                        (@UpperTheory.Reformulated.B.Qi13.algRes K inst inst_1 inst_2 inst_3 l inst_4 inst_5)) :=
    fun (K : Type) [inst : Field K]
        [inst_1 :
          @ValuativeRel K (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))]
        [inst_2 : TopologicalSpace K] [inst_3 : @IsNonarchimedeanLocalField K inst inst_1 inst_2] (l : Nat)
        [inst_4 : Fact (Nat.Prime l)]
        [inst_5 :
          @CharP
            (@IsLocalRing.ResidueField
              (↥(@Valuation.integer K
                  (@ValuativeRel.ValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
              (@Subring.toCommRing K (@Field.toCommRing K inst)
                (@Valuation.integer K
                  (@ValuativeRel.ValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
              (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
            (@AddGroupWithOne.toAddMonoidWithOne
              (@IsLocalRing.ResidueField
                (↥(@Valuation.integer K
                    (@ValuativeRel.ValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                (@Subring.toCommRing K (@Field.toCommRing K inst)
                  (@Valuation.integer K
                    (@ValuativeRel.ValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
              (@Ring.toAddGroupWithOne
                (@IsLocalRing.ResidueField
                  (↥(@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@Subring.toCommRing K (@Field.toCommRing K inst)
                    (@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                (@DivisionRing.toRing
                  (@IsLocalRing.ResidueField
                    (↥(@Valuation.integer K
                        (@ValuativeRel.ValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                    (@Subring.toCommRing K (@Field.toCommRing K inst)
                      (@Valuation.integer K
                        (@ValuativeRel.ValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                    (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                  (@Field.toDivisionRing
                    (@IsLocalRing.ResidueField
                      (↥(@Valuation.integer K
                          (@ValuativeRel.ValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                          (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                      (@Subring.toCommRing K (@Field.toCommRing K inst)
                        (@Valuation.integer K
                          (@ValuativeRel.ValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                          (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                      (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                    (@IsLocalRing.ResidueField.field
                      (↥(@Valuation.integer K
                          (@ValuativeRel.ValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                          (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                      (@Subring.toCommRing K (@Field.toCommRing K inst)
                        (@Valuation.integer K
                          (@ValuativeRel.ValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                          (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                      (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))))))
            l] ↦
      @Module.finBasis (ZMod l)
        (@IsLocalRing.ResidueField
          (↥(@Valuation.integer K
              (@ValuativeRel.ValueGroupWithZero K
                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
              (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
              (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
              (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
          (@Subring.toCommRing K (@Field.toCommRing K inst)
            (@Valuation.integer K
              (@ValuativeRel.ValueGroupWithZero K
                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
              (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
              (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
              (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
          (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
        (@DivisionSemiring.toSemiring (ZMod l)
          (@Semifield.toDivisionSemiring (ZMod l) (@Field.toSemifield (ZMod l) (@ZMod.instField l inst_4))))
        (@Semiring.toAddCommMonoid
          (@IsLocalRing.ResidueField
            (↥(@Valuation.integer K
                (@ValuativeRel.ValueGroupWithZero K
                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
            (@Subring.toCommRing K (@Field.toCommRing K inst)
              (@Valuation.integer K
                (@ValuativeRel.ValueGroupWithZero K
                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
            (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
          (@DivisionSemiring.toSemiring
            (@IsLocalRing.ResidueField
              (↥(@Valuation.integer K
                  (@ValuativeRel.ValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
              (@Subring.toCommRing K (@Field.toCommRing K inst)
                (@Valuation.integer K
                  (@ValuativeRel.ValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
              (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
            (@Semifield.toDivisionSemiring
              (@IsLocalRing.ResidueField
                (↥(@Valuation.integer K
                    (@ValuativeRel.ValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                (@Subring.toCommRing K (@Field.toCommRing K inst)
                  (@Valuation.integer K
                    (@ValuativeRel.ValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
              (@Field.toSemifield
                (@IsLocalRing.ResidueField
                  (↥(@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@Subring.toCommRing K (@Field.toCommRing K inst)
                    (@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                (@IsLocalRing.ResidueField.field
                  (↥(@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@Subring.toCommRing K (@Field.toCommRing K inst)
                    (@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))))))
        (@Algebra.toModule (ZMod l)
          (@IsLocalRing.ResidueField
            (↥(@Valuation.integer K
                (@ValuativeRel.ValueGroupWithZero K
                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
            (@Subring.toCommRing K (@Field.toCommRing K inst)
              (@Valuation.integer K
                (@ValuativeRel.ValueGroupWithZero K
                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
            (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
          (@Semifield.toCommSemiring (ZMod l) (@Field.toSemifield (ZMod l) (@ZMod.instField l inst_4)))
          (@DivisionSemiring.toSemiring
            (@IsLocalRing.ResidueField
              (↥(@Valuation.integer K
                  (@ValuativeRel.ValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
              (@Subring.toCommRing K (@Field.toCommRing K inst)
                (@Valuation.integer K
                  (@ValuativeRel.ValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
              (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
            (@Semifield.toDivisionSemiring
              (@IsLocalRing.ResidueField
                (↥(@Valuation.integer K
                    (@ValuativeRel.ValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                (@Subring.toCommRing K (@Field.toCommRing K inst)
                  (@Valuation.integer K
                    (@ValuativeRel.ValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
              (@Field.toSemifield
                (@IsLocalRing.ResidueField
                  (↥(@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@Subring.toCommRing K (@Field.toCommRing K inst)
                    (@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                (@IsLocalRing.ResidueField.field
                  (↥(@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@Subring.toCommRing K (@Field.toCommRing K inst)
                    (@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3)))))
          (@UpperTheory.Reformulated.B.Qi13.algRes K inst inst_1 inst_2 inst_3 l inst_4 inst_5))
        (@UpperTheory.Reformulated.B.Qi13.aux4 K inst inst_1 inst_2 inst_3 l inst_4 inst_5) (@UpperTheory.Reformulated.B.Qi13.aux5 l inst_4)
        (@UpperTheory.Reformulated.B.Qi13.aux6 K inst inst_1 inst_2 inst_3 l inst_4 inst_5)
theorem UpperTheory.Reformulated.B.Qi13.aux8 :
    ∀ (K : Type) [inst : Field K]
      [inst_1 :
        @ValuativeRel K (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))]
      [inst_2 : TopologicalSpace K] [inst_3 : @IsNonarchimedeanLocalField K inst inst_1 inst_2] (l : Nat)
      [inst_4 : Fact (Nat.Prime l)]
      [inst_5 :
        @CharP
          (@IsLocalRing.ResidueField
            (↥(@Valuation.integer K
                (@ValuativeRel.ValueGroupWithZero K
                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
            (@Subring.toCommRing K (@Field.toCommRing K inst)
              (@Valuation.integer K
                (@ValuativeRel.ValueGroupWithZero K
                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
            (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
          (@AddGroupWithOne.toAddMonoidWithOne
            (@IsLocalRing.ResidueField
              (↥(@Valuation.integer K
                  (@ValuativeRel.ValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
              (@Subring.toCommRing K (@Field.toCommRing K inst)
                (@Valuation.integer K
                  (@ValuativeRel.ValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
              (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
            (@Ring.toAddGroupWithOne
              (@IsLocalRing.ResidueField
                (↥(@Valuation.integer K
                    (@ValuativeRel.ValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                (@Subring.toCommRing K (@Field.toCommRing K inst)
                  (@Valuation.integer K
                    (@ValuativeRel.ValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
              (@DivisionRing.toRing
                (@IsLocalRing.ResidueField
                  (↥(@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@Subring.toCommRing K (@Field.toCommRing K inst)
                    (@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                (@Field.toDivisionRing
                  (@IsLocalRing.ResidueField
                    (↥(@Valuation.integer K
                        (@ValuativeRel.ValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                    (@Subring.toCommRing K (@Field.toCommRing K inst)
                      (@Valuation.integer K
                        (@ValuativeRel.ValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                    (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                  (@IsLocalRing.ResidueField.field
                    (↥(@Valuation.integer K
                        (@ValuativeRel.ValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                    (@Subring.toCommRing K (@Field.toCommRing K inst)
                      (@Valuation.integer K
                        (@ValuativeRel.ValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                    (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))))))
          l]
      (i : Fin (@UpperTheory.Reformulated.B.Qi13.fdim K inst inst_1 inst_2 inst_3 l inst_4 inst_5)),
      ∃ (a :
        ↥(@Valuation.integer K
            (@ValuativeRel.ValueGroupWithZero K (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)))
              inst_1)
            (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
            (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
            (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1))),
        @Eq
          (@IsLocalRing.ResidueField
            (↥(@Valuation.integer K
                (@ValuativeRel.ValueGroupWithZero K
                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
            (@Subring.toCommRing K (@Field.toCommRing K inst)
              (@Valuation.integer K
                (@ValuativeRel.ValueGroupWithZero K
                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
            (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
          (@DFunLike.coe
            (@RingHom
              (↥(@Valuation.integer K
                  (@ValuativeRel.ValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
              (@IsLocalRing.ResidueField
                (↥(@Valuation.integer K
                    (@ValuativeRel.ValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                (@Subring.toCommRing K (@Field.toCommRing K inst)
                  (@Valuation.integer K
                    (@ValuativeRel.ValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
              (@Semiring.toNonAssocSemiring
                (↥(@Valuation.integer K
                    (@ValuativeRel.ValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                (@CommSemiring.toSemiring
                  (↥(@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@CommRing.toCommSemiring
                    (↥(@Valuation.integer K
                        (@ValuativeRel.ValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                    (@Subring.toCommRing K (@Field.toCommRing K inst)
                      (@Valuation.integer K
                        (@ValuativeRel.ValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1))))))
              (@Semiring.toNonAssocSemiring
                (@IsLocalRing.ResidueField
                  (↥(@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@Subring.toCommRing K (@Field.toCommRing K inst)
                    (@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                (@DivisionSemiring.toSemiring
                  (@IsLocalRing.ResidueField
                    (↥(@Valuation.integer K
                        (@ValuativeRel.ValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                    (@Subring.toCommRing K (@Field.toCommRing K inst)
                      (@Valuation.integer K
                        (@ValuativeRel.ValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                    (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                  (@Semifield.toDivisionSemiring
                    (@IsLocalRing.ResidueField
                      (↥(@Valuation.integer K
                          (@ValuativeRel.ValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                          (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                      (@Subring.toCommRing K (@Field.toCommRing K inst)
                        (@Valuation.integer K
                          (@ValuativeRel.ValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                          (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                      (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                    (@Field.toSemifield
                      (@IsLocalRing.ResidueField
                        (↥(@Valuation.integer K
                            (@ValuativeRel.ValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                            (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                        (@Subring.toCommRing K (@Field.toCommRing K inst)
                          (@Valuation.integer K
                            (@ValuativeRel.ValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                            (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                        (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                      (@IsLocalRing.ResidueField.field
                        (↥(@Valuation.integer K
                            (@ValuativeRel.ValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                            (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                        (@Subring.toCommRing K (@Field.toCommRing K inst)
                          (@Valuation.integer K
                            (@ValuativeRel.ValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                            (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                        (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3)))))))
            (↥(@Valuation.integer K
                (@ValuativeRel.ValueGroupWithZero K
                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
            (fun
                (x :
                  ↥(@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1))) ↦
              @IsLocalRing.ResidueField
                (↥(@Valuation.integer K
                    (@ValuativeRel.ValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                (@Subring.toCommRing K (@Field.toCommRing K inst)
                  (@Valuation.integer K
                    (@ValuativeRel.ValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
            (@RingHom.instFunLike
              (↥(@Valuation.integer K
                  (@ValuativeRel.ValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
              (@IsLocalRing.ResidueField
                (↥(@Valuation.integer K
                    (@ValuativeRel.ValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                (@Subring.toCommRing K (@Field.toCommRing K inst)
                  (@Valuation.integer K
                    (@ValuativeRel.ValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
              (@Semiring.toNonAssocSemiring
                (↥(@Valuation.integer K
                    (@ValuativeRel.ValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                (@CommSemiring.toSemiring
                  (↥(@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@CommRing.toCommSemiring
                    (↥(@Valuation.integer K
                        (@ValuativeRel.ValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                    (@Subring.toCommRing K (@Field.toCommRing K inst)
                      (@Valuation.integer K
                        (@ValuativeRel.ValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1))))))
              (@Semiring.toNonAssocSemiring
                (@IsLocalRing.ResidueField
                  (↥(@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@Subring.toCommRing K (@Field.toCommRing K inst)
                    (@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                (@DivisionSemiring.toSemiring
                  (@IsLocalRing.ResidueField
                    (↥(@Valuation.integer K
                        (@ValuativeRel.ValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                    (@Subring.toCommRing K (@Field.toCommRing K inst)
                      (@Valuation.integer K
                        (@ValuativeRel.ValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                    (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                  (@Semifield.toDivisionSemiring
                    (@IsLocalRing.ResidueField
                      (↥(@Valuation.integer K
                          (@ValuativeRel.ValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                          (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                      (@Subring.toCommRing K (@Field.toCommRing K inst)
                        (@Valuation.integer K
                          (@ValuativeRel.ValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                          (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                      (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                    (@Field.toSemifield
                      (@IsLocalRing.ResidueField
                        (↥(@Valuation.integer K
                            (@ValuativeRel.ValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                            (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                        (@Subring.toCommRing K (@Field.toCommRing K inst)
                          (@Valuation.integer K
                            (@ValuativeRel.ValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                            (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                        (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                      (@IsLocalRing.ResidueField.field
                        (↥(@Valuation.integer K
                            (@ValuativeRel.ValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                            (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                        (@Subring.toCommRing K (@Field.toCommRing K inst)
                          (@Valuation.integer K
                            (@ValuativeRel.ValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                            (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                        (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3)))))))
            (@IsLocalRing.residue
              (↥(@Valuation.integer K
                  (@ValuativeRel.ValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
              (@Subring.toCommRing K (@Field.toCommRing K inst)
                (@Valuation.integer K
                  (@ValuativeRel.ValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
              (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
            a)
          (@DFunLike.coe
            (@Module.Basis (Fin (@UpperTheory.Reformulated.B.Qi13.fdim K inst inst_1 inst_2 inst_3 l inst_4 inst_5)) (ZMod l)
              (@IsLocalRing.ResidueField
                (↥(@Valuation.integer K
                    (@ValuativeRel.ValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                (@Subring.toCommRing K (@Field.toCommRing K inst)
                  (@Valuation.integer K
                    (@ValuativeRel.ValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
              (@DivisionSemiring.toSemiring (ZMod l)
                (@Semifield.toDivisionSemiring (ZMod l) (@Field.toSemifield (ZMod l) (@ZMod.instField l inst_4))))
              (@Semiring.toAddCommMonoid
                (@IsLocalRing.ResidueField
                  (↥(@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@Subring.toCommRing K (@Field.toCommRing K inst)
                    (@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                (@DivisionSemiring.toSemiring
                  (@IsLocalRing.ResidueField
                    (↥(@Valuation.integer K
                        (@ValuativeRel.ValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                    (@Subring.toCommRing K (@Field.toCommRing K inst)
                      (@Valuation.integer K
                        (@ValuativeRel.ValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                    (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                  (@Semifield.toDivisionSemiring
                    (@IsLocalRing.ResidueField
                      (↥(@Valuation.integer K
                          (@ValuativeRel.ValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                          (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                      (@Subring.toCommRing K (@Field.toCommRing K inst)
                        (@Valuation.integer K
                          (@ValuativeRel.ValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                          (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                      (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                    (@Field.toSemifield
                      (@IsLocalRing.ResidueField
                        (↥(@Valuation.integer K
                            (@ValuativeRel.ValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                            (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                        (@Subring.toCommRing K (@Field.toCommRing K inst)
                          (@Valuation.integer K
                            (@ValuativeRel.ValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                            (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                        (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                      (@IsLocalRing.ResidueField.field
                        (↥(@Valuation.integer K
                            (@ValuativeRel.ValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                            (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                        (@Subring.toCommRing K (@Field.toCommRing K inst)
                          (@Valuation.integer K
                            (@ValuativeRel.ValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                            (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                        (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))))))
              (@Algebra.toModule (ZMod l)
                (@IsLocalRing.ResidueField
                  (↥(@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@Subring.toCommRing K (@Field.toCommRing K inst)
                    (@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                (@Semifield.toCommSemiring (ZMod l) (@Field.toSemifield (ZMod l) (@ZMod.instField l inst_4)))
                (@DivisionSemiring.toSemiring
                  (@IsLocalRing.ResidueField
                    (↥(@Valuation.integer K
                        (@ValuativeRel.ValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                    (@Subring.toCommRing K (@Field.toCommRing K inst)
                      (@Valuation.integer K
                        (@ValuativeRel.ValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                    (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                  (@Semifield.toDivisionSemiring
                    (@IsLocalRing.ResidueField
                      (↥(@Valuation.integer K
                          (@ValuativeRel.ValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                          (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                      (@Subring.toCommRing K (@Field.toCommRing K inst)
                        (@Valuation.integer K
                          (@ValuativeRel.ValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                          (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                      (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                    (@Field.toSemifield
                      (@IsLocalRing.ResidueField
                        (↥(@Valuation.integer K
                            (@ValuativeRel.ValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                            (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                        (@Subring.toCommRing K (@Field.toCommRing K inst)
                          (@Valuation.integer K
                            (@ValuativeRel.ValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                            (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                        (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                      (@IsLocalRing.ResidueField.field
                        (↥(@Valuation.integer K
                            (@ValuativeRel.ValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                            (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                        (@Subring.toCommRing K (@Field.toCommRing K inst)
                          (@Valuation.integer K
                            (@ValuativeRel.ValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                            (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                        (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3)))))
                (@UpperTheory.Reformulated.B.Qi13.algRes K inst inst_1 inst_2 inst_3 l inst_4 inst_5)))
            (Fin (@UpperTheory.Reformulated.B.Qi13.fdim K inst inst_1 inst_2 inst_3 l inst_4 inst_5))
            (fun (x : Fin (@UpperTheory.Reformulated.B.Qi13.fdim K inst inst_1 inst_2 inst_3 l inst_4 inst_5)) ↦
              @IsLocalRing.ResidueField
                (↥(@Valuation.integer K
                    (@ValuativeRel.ValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                (@Subring.toCommRing K (@Field.toCommRing K inst)
                  (@Valuation.integer K
                    (@ValuativeRel.ValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
            (@Module.Basis.instFunLike (Fin (@UpperTheory.Reformulated.B.Qi13.fdim K inst inst_1 inst_2 inst_3 l inst_4 inst_5)) (ZMod l)
              (@IsLocalRing.ResidueField
                (↥(@Valuation.integer K
                    (@ValuativeRel.ValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                (@Subring.toCommRing K (@Field.toCommRing K inst)
                  (@Valuation.integer K
                    (@ValuativeRel.ValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
              (@DivisionSemiring.toSemiring (ZMod l)
                (@Semifield.toDivisionSemiring (ZMod l) (@Field.toSemifield (ZMod l) (@ZMod.instField l inst_4))))
              (@Semiring.toAddCommMonoid
                (@IsLocalRing.ResidueField
                  (↥(@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@Subring.toCommRing K (@Field.toCommRing K inst)
                    (@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                (@DivisionSemiring.toSemiring
                  (@IsLocalRing.ResidueField
                    (↥(@Valuation.integer K
                        (@ValuativeRel.ValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                    (@Subring.toCommRing K (@Field.toCommRing K inst)
                      (@Valuation.integer K
                        (@ValuativeRel.ValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                    (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                  (@Semifield.toDivisionSemiring
                    (@IsLocalRing.ResidueField
                      (↥(@Valuation.integer K
                          (@ValuativeRel.ValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                          (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                      (@Subring.toCommRing K (@Field.toCommRing K inst)
                        (@Valuation.integer K
                          (@ValuativeRel.ValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                          (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                      (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                    (@Field.toSemifield
                      (@IsLocalRing.ResidueField
                        (↥(@Valuation.integer K
                            (@ValuativeRel.ValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                            (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                        (@Subring.toCommRing K (@Field.toCommRing K inst)
                          (@Valuation.integer K
                            (@ValuativeRel.ValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                            (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                        (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                      (@IsLocalRing.ResidueField.field
                        (↥(@Valuation.integer K
                            (@ValuativeRel.ValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                            (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                        (@Subring.toCommRing K (@Field.toCommRing K inst)
                          (@Valuation.integer K
                            (@ValuativeRel.ValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                            (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                        (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))))))
              (@Algebra.toModule (ZMod l)
                (@IsLocalRing.ResidueField
                  (↥(@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@Subring.toCommRing K (@Field.toCommRing K inst)
                    (@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                (@Semifield.toCommSemiring (ZMod l) (@Field.toSemifield (ZMod l) (@ZMod.instField l inst_4)))
                (@DivisionSemiring.toSemiring
                  (@IsLocalRing.ResidueField
                    (↥(@Valuation.integer K
                        (@ValuativeRel.ValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                    (@Subring.toCommRing K (@Field.toCommRing K inst)
                      (@Valuation.integer K
                        (@ValuativeRel.ValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                    (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                  (@Semifield.toDivisionSemiring
                    (@IsLocalRing.ResidueField
                      (↥(@Valuation.integer K
                          (@ValuativeRel.ValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                          (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                      (@Subring.toCommRing K (@Field.toCommRing K inst)
                        (@Valuation.integer K
                          (@ValuativeRel.ValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                          (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                      (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                    (@Field.toSemifield
                      (@IsLocalRing.ResidueField
                        (↥(@Valuation.integer K
                            (@ValuativeRel.ValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                            (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                        (@Subring.toCommRing K (@Field.toCommRing K inst)
                          (@Valuation.integer K
                            (@ValuativeRel.ValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                            (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                        (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                      (@IsLocalRing.ResidueField.field
                        (↥(@Valuation.integer K
                            (@ValuativeRel.ValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                            (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                        (@Subring.toCommRing K (@Field.toCommRing K inst)
                          (@Valuation.integer K
                            (@ValuativeRel.ValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                            (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                        (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3)))))
                (@UpperTheory.Reformulated.B.Qi13.algRes K inst inst_1 inst_2 inst_3 l inst_4 inst_5)))
            (@UpperTheory.Reformulated.B.Qi13.bb K inst inst_1 inst_2 inst_3 l inst_4 inst_5) i) := by
  intro K _ _ _ _ l _ _ i
  exact IsLocalRing.residue_surjective _
noncomputable def UpperTheory.Reformulated.B.Qi13.blift :
    (K : Type) →
      [inst : Field K] →
        [inst_1 :
            @ValuativeRel K
              (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))] →
          [inst_2 : TopologicalSpace K] →
            [inst_3 : @IsNonarchimedeanLocalField K inst inst_1 inst_2] →
              (l : Nat) →
                [inst_4 : Fact (Nat.Prime l)] →
                  [inst_5 :
                      @CharP
                        (@IsLocalRing.ResidueField
                          (↥(@Valuation.integer K
                              (@ValuativeRel.ValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                              (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                          (@Subring.toCommRing K (@Field.toCommRing K inst)
                            (@Valuation.integer K
                              (@ValuativeRel.ValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                              (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                          (@IsDiscreteValuationRing.toIsLocalRing
                            (↥(@Valuation.integer K
                                (@ValuativeRel.ValueGroupWithZero K
                                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                            (@Subring.toCommRing K (@Field.toCommRing K inst)
                              (@Valuation.integer K
                                (@ValuativeRel.ValueGroupWithZero K
                                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                            (@Subring.instIsDomainSubtypeMem K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                              (@instIsDomain K (@Field.toSemifield K inst))
                              (@Valuation.integer K
                                (@ValuativeRel.ValueGroupWithZero K
                                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                            (@IsNonarchimedeanLocalField.instIsDiscreteValuationRingSubtypeMemSubringIntegerValueGroupWithZeroValuation
                              K inst inst_1 inst_2 inst_3)))
                        (@AddGroupWithOne.toAddMonoidWithOne
                          (@IsLocalRing.ResidueField
                            (↥(@Valuation.integer K
                                (@ValuativeRel.ValueGroupWithZero K
                                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                            (@Subring.toCommRing K (@Field.toCommRing K inst)
                              (@Valuation.integer K
                                (@ValuativeRel.ValueGroupWithZero K
                                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                  (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                            (@IsDiscreteValuationRing.toIsLocalRing
                              (↥(@Valuation.integer K
                                  (@ValuativeRel.ValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    inst_1)))
                              (@Subring.toCommRing K (@Field.toCommRing K inst)
                                (@Valuation.integer K
                                  (@ValuativeRel.ValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    inst_1)))
                              (@Subring.instIsDomainSubtypeMem K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                (@instIsDomain K (@Field.toSemifield K inst))
                                (@Valuation.integer K
                                  (@ValuativeRel.ValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    inst_1)))
                              (@IsNonarchimedeanLocalField.instIsDiscreteValuationRingSubtypeMemSubringIntegerValueGroupWithZeroValuation
                                K inst inst_1 inst_2 inst_3)))
                          (@Ring.toAddGroupWithOne
                            (@IsLocalRing.ResidueField
                              (↥(@Valuation.integer K
                                  (@ValuativeRel.ValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    inst_1)))
                              (@Subring.toCommRing K (@Field.toCommRing K inst)
                                (@Valuation.integer K
                                  (@ValuativeRel.ValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    inst_1)))
                              (@IsDiscreteValuationRing.toIsLocalRing
                                (↥(@Valuation.integer K
                                    (@ValuativeRel.ValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      inst_1)))
                                (@Subring.toCommRing K (@Field.toCommRing K inst)
                                  (@Valuation.integer K
                                    (@ValuativeRel.ValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      inst_1)))
                                (@Subring.instIsDomainSubtypeMem K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                  (@instIsDomain K (@Field.toSemifield K inst))
                                  (@Valuation.integer K
                                    (@ValuativeRel.ValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      inst_1)))
                                (@IsNonarchimedeanLocalField.instIsDiscreteValuationRingSubtypeMemSubringIntegerValueGroupWithZeroValuation
                                  K inst inst_1 inst_2 inst_3)))
                            (@DivisionRing.toRing
                              (@IsLocalRing.ResidueField
                                (↥(@Valuation.integer K
                                    (@ValuativeRel.ValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      inst_1)))
                                (@Subring.toCommRing K (@Field.toCommRing K inst)
                                  (@Valuation.integer K
                                    (@ValuativeRel.ValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      inst_1)))
                                (@IsDiscreteValuationRing.toIsLocalRing
                                  (↥(@Valuation.integer K
                                      (@ValuativeRel.ValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                        inst_1)))
                                  (@Subring.toCommRing K (@Field.toCommRing K inst)
                                    (@Valuation.integer K
                                      (@ValuativeRel.ValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                        inst_1)))
                                  (@Subring.instIsDomainSubtypeMem K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                    (@instIsDomain K (@Field.toSemifield K inst))
                                    (@Valuation.integer K
                                      (@ValuativeRel.ValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                        inst_1)))
                                  (@IsNonarchimedeanLocalField.instIsDiscreteValuationRingSubtypeMemSubringIntegerValueGroupWithZeroValuation
                                    K inst inst_1 inst_2 inst_3)))
                              (@Field.toDivisionRing
                                (@IsLocalRing.ResidueField
                                  (↥(@Valuation.integer K
                                      (@ValuativeRel.ValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                        inst_1)))
                                  (@Subring.toCommRing K (@Field.toCommRing K inst)
                                    (@Valuation.integer K
                                      (@ValuativeRel.ValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                        inst_1)))
                                  (@IsDiscreteValuationRing.toIsLocalRing
                                    (↥(@Valuation.integer K
                                        (@ValuativeRel.ValueGroupWithZero K
                                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)))
                                          inst_1)
                                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)))
                                          inst_1)
                                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                          inst_1)))
                                    (@Subring.toCommRing K (@Field.toCommRing K inst)
                                      (@Valuation.integer K
                                        (@ValuativeRel.ValueGroupWithZero K
                                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)))
                                          inst_1)
                                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)))
                                          inst_1)
                                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                          inst_1)))
                                    (@Subring.instIsDomainSubtypeMem K
                                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      (@instIsDomain K (@Field.toSemifield K inst))
                                      (@Valuation.integer K
                                        (@ValuativeRel.ValueGroupWithZero K
                                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)))
                                          inst_1)
                                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)))
                                          inst_1)
                                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                          inst_1)))
                                    (@IsNonarchimedeanLocalField.instIsDiscreteValuationRingSubtypeMemSubringIntegerValueGroupWithZeroValuation
                                      K inst inst_1 inst_2 inst_3)))
                                (@IsLocalRing.ResidueField.field
                                  (↥(@Valuation.integer K
                                      (@ValuativeRel.ValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                        inst_1)))
                                  (@Subring.toCommRing K (@Field.toCommRing K inst)
                                    (@Valuation.integer K
                                      (@ValuativeRel.ValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                        inst_1)))
                                  (@IsDiscreteValuationRing.toIsLocalRing
                                    (↥(@Valuation.integer K
                                        (@ValuativeRel.ValueGroupWithZero K
                                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)))
                                          inst_1)
                                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)))
                                          inst_1)
                                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                          inst_1)))
                                    (@Subring.toCommRing K (@Field.toCommRing K inst)
                                      (@Valuation.integer K
                                        (@ValuativeRel.ValueGroupWithZero K
                                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)))
                                          inst_1)
                                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)))
                                          inst_1)
                                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                          inst_1)))
                                    (@Subring.instIsDomainSubtypeMem K
                                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                      (@instIsDomain K (@Field.toSemifield K inst))
                                      (@Valuation.integer K
                                        (@ValuativeRel.ValueGroupWithZero K
                                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)))
                                          inst_1)
                                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)))
                                          inst_1)
                                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                                          inst_1)))
                                    (@IsNonarchimedeanLocalField.instIsDiscreteValuationRingSubtypeMemSubringIntegerValueGroupWithZeroValuation
                                      K inst inst_1 inst_2 inst_3)))))))
                        l] →
                    Fin (@UpperTheory.Reformulated.B.Qi13.fdim K inst inst_1 inst_2 inst_3 l inst_4 inst_5) →
                      ↥(@Valuation.integer K
                          (@ValuativeRel.ValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                          (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)) :=
    fun (K : Type) [inst : Field K]
        [inst_1 :
          @ValuativeRel K (@DivisionSemiring.toSemiring K (@Semifield.toDivisionSemiring K (@Field.toSemifield K inst)))]
        [inst_2 : TopologicalSpace K] [inst_3 : @IsNonarchimedeanLocalField K inst inst_1 inst_2] (l : Nat)
        [inst_4 : Fact (Nat.Prime l)]
        [inst_5 :
          @CharP
            (@IsLocalRing.ResidueField
              (↥(@Valuation.integer K
                  (@ValuativeRel.ValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
              (@Subring.toCommRing K (@Field.toCommRing K inst)
                (@Valuation.integer K
                  (@ValuativeRel.ValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
              (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
            (@AddGroupWithOne.toAddMonoidWithOne
              (@IsLocalRing.ResidueField
                (↥(@Valuation.integer K
                    (@ValuativeRel.ValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                (@Subring.toCommRing K (@Field.toCommRing K inst)
                  (@Valuation.integer K
                    (@ValuativeRel.ValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
              (@Ring.toAddGroupWithOne
                (@IsLocalRing.ResidueField
                  (↥(@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@Subring.toCommRing K (@Field.toCommRing K inst)
                    (@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                (@DivisionRing.toRing
                  (@IsLocalRing.ResidueField
                    (↥(@Valuation.integer K
                        (@ValuativeRel.ValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                    (@Subring.toCommRing K (@Field.toCommRing K inst)
                      (@Valuation.integer K
                        (@ValuativeRel.ValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                    (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                  (@Field.toDivisionRing
                    (@IsLocalRing.ResidueField
                      (↥(@Valuation.integer K
                          (@ValuativeRel.ValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                          (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                      (@Subring.toCommRing K (@Field.toCommRing K inst)
                        (@Valuation.integer K
                          (@ValuativeRel.ValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                          (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                      (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                    (@IsLocalRing.ResidueField.field
                      (↥(@Valuation.integer K
                          (@ValuativeRel.ValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                          (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                      (@Subring.toCommRing K (@Field.toCommRing K inst)
                        (@Valuation.integer K
                          (@ValuativeRel.ValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                          (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                      (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))))))
            l]
        (i : Fin (@UpperTheory.Reformulated.B.Qi13.fdim K inst inst_1 inst_2 inst_3 l inst_4 inst_5)) ↦
      @Exists.choose
        (↥(@Valuation.integer K
            (@ValuativeRel.ValueGroupWithZero K (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)))
              inst_1)
            (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
            (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
            (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
        (fun
            (a :
              ↥(@Valuation.integer K
                  (@ValuativeRel.ValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1))) ↦
          @Eq
            (@IsLocalRing.ResidueField
              (↥(@Valuation.integer K
                  (@ValuativeRel.ValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
              (@Subring.toCommRing K (@Field.toCommRing K inst)
                (@Valuation.integer K
                  (@ValuativeRel.ValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
              (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
            (@DFunLike.coe
              (@RingHom
                (↥(@Valuation.integer K
                    (@ValuativeRel.ValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                (@IsLocalRing.ResidueField
                  (↥(@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@Subring.toCommRing K (@Field.toCommRing K inst)
                    (@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                (@Semiring.toNonAssocSemiring
                  (↥(@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@CommSemiring.toSemiring
                    (↥(@Valuation.integer K
                        (@ValuativeRel.ValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                    (@CommRing.toCommSemiring
                      (↥(@Valuation.integer K
                          (@ValuativeRel.ValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                          (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                      (@Subring.toCommRing K (@Field.toCommRing K inst)
                        (@Valuation.integer K
                          (@ValuativeRel.ValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                          (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1))))))
                (@Semiring.toNonAssocSemiring
                  (@IsLocalRing.ResidueField
                    (↥(@Valuation.integer K
                        (@ValuativeRel.ValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                    (@Subring.toCommRing K (@Field.toCommRing K inst)
                      (@Valuation.integer K
                        (@ValuativeRel.ValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                    (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                  (@DivisionSemiring.toSemiring
                    (@IsLocalRing.ResidueField
                      (↥(@Valuation.integer K
                          (@ValuativeRel.ValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                          (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                      (@Subring.toCommRing K (@Field.toCommRing K inst)
                        (@Valuation.integer K
                          (@ValuativeRel.ValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                          (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                      (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                    (@Semifield.toDivisionSemiring
                      (@IsLocalRing.ResidueField
                        (↥(@Valuation.integer K
                            (@ValuativeRel.ValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                            (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                        (@Subring.toCommRing K (@Field.toCommRing K inst)
                          (@Valuation.integer K
                            (@ValuativeRel.ValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                            (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                        (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                      (@Field.toSemifield
                        (@IsLocalRing.ResidueField
                          (↥(@Valuation.integer K
                              (@ValuativeRel.ValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                              (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                          (@Subring.toCommRing K (@Field.toCommRing K inst)
                            (@Valuation.integer K
                              (@ValuativeRel.ValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                              (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                          (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                        (@IsLocalRing.ResidueField.field
                          (↥(@Valuation.integer K
                              (@ValuativeRel.ValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                              (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                          (@Subring.toCommRing K (@Field.toCommRing K inst)
                            (@Valuation.integer K
                              (@ValuativeRel.ValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                              (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                          (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3)))))))
              (↥(@Valuation.integer K
                  (@ValuativeRel.ValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                  (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                    (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                  (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
              (fun
                  (x :
                    ↥(@Valuation.integer K
                        (@ValuativeRel.ValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1))) ↦
                @IsLocalRing.ResidueField
                  (↥(@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@Subring.toCommRing K (@Field.toCommRing K inst)
                    (@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
              (@RingHom.instFunLike
                (↥(@Valuation.integer K
                    (@ValuativeRel.ValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                (@IsLocalRing.ResidueField
                  (↥(@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@Subring.toCommRing K (@Field.toCommRing K inst)
                    (@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                (@Semiring.toNonAssocSemiring
                  (↥(@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@CommSemiring.toSemiring
                    (↥(@Valuation.integer K
                        (@ValuativeRel.ValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                    (@CommRing.toCommSemiring
                      (↥(@Valuation.integer K
                          (@ValuativeRel.ValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                          (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                      (@Subring.toCommRing K (@Field.toCommRing K inst)
                        (@Valuation.integer K
                          (@ValuativeRel.ValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                          (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1))))))
                (@Semiring.toNonAssocSemiring
                  (@IsLocalRing.ResidueField
                    (↥(@Valuation.integer K
                        (@ValuativeRel.ValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                    (@Subring.toCommRing K (@Field.toCommRing K inst)
                      (@Valuation.integer K
                        (@ValuativeRel.ValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                    (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                  (@DivisionSemiring.toSemiring
                    (@IsLocalRing.ResidueField
                      (↥(@Valuation.integer K
                          (@ValuativeRel.ValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                          (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                      (@Subring.toCommRing K (@Field.toCommRing K inst)
                        (@Valuation.integer K
                          (@ValuativeRel.ValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                          (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                      (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                    (@Semifield.toDivisionSemiring
                      (@IsLocalRing.ResidueField
                        (↥(@Valuation.integer K
                            (@ValuativeRel.ValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                            (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                        (@Subring.toCommRing K (@Field.toCommRing K inst)
                          (@Valuation.integer K
                            (@ValuativeRel.ValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                            (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                        (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                      (@Field.toSemifield
                        (@IsLocalRing.ResidueField
                          (↥(@Valuation.integer K
                              (@ValuativeRel.ValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                              (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                          (@Subring.toCommRing K (@Field.toCommRing K inst)
                            (@Valuation.integer K
                              (@ValuativeRel.ValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                              (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                          (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                        (@IsLocalRing.ResidueField.field
                          (↥(@Valuation.integer K
                              (@ValuativeRel.ValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                              (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                          (@Subring.toCommRing K (@Field.toCommRing K inst)
                            (@Valuation.integer K
                              (@ValuativeRel.ValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                              (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                          (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3)))))))
              (@IsLocalRing.residue
                (↥(@Valuation.integer K
                    (@ValuativeRel.ValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                (@Subring.toCommRing K (@Field.toCommRing K inst)
                  (@Valuation.integer K
                    (@ValuativeRel.ValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                    (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                      (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                    (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
              a)
            (@DFunLike.coe
              (@Module.Basis (Fin (@UpperTheory.Reformulated.B.Qi13.fdim K inst inst_1 inst_2 inst_3 l inst_4 inst_5)) (ZMod l)
                (@IsLocalRing.ResidueField
                  (↥(@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@Subring.toCommRing K (@Field.toCommRing K inst)
                    (@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                (@DivisionSemiring.toSemiring (ZMod l)
                  (@Semifield.toDivisionSemiring (ZMod l) (@Field.toSemifield (ZMod l) (@ZMod.instField l inst_4))))
                (@Semiring.toAddCommMonoid
                  (@IsLocalRing.ResidueField
                    (↥(@Valuation.integer K
                        (@ValuativeRel.ValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                    (@Subring.toCommRing K (@Field.toCommRing K inst)
                      (@Valuation.integer K
                        (@ValuativeRel.ValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                    (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                  (@DivisionSemiring.toSemiring
                    (@IsLocalRing.ResidueField
                      (↥(@Valuation.integer K
                          (@ValuativeRel.ValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                          (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                      (@Subring.toCommRing K (@Field.toCommRing K inst)
                        (@Valuation.integer K
                          (@ValuativeRel.ValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                          (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                      (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                    (@Semifield.toDivisionSemiring
                      (@IsLocalRing.ResidueField
                        (↥(@Valuation.integer K
                            (@ValuativeRel.ValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                            (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                        (@Subring.toCommRing K (@Field.toCommRing K inst)
                          (@Valuation.integer K
                            (@ValuativeRel.ValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                            (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                        (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                      (@Field.toSemifield
                        (@IsLocalRing.ResidueField
                          (↥(@Valuation.integer K
                              (@ValuativeRel.ValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                              (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                          (@Subring.toCommRing K (@Field.toCommRing K inst)
                            (@Valuation.integer K
                              (@ValuativeRel.ValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                              (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                          (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                        (@IsLocalRing.ResidueField.field
                          (↥(@Valuation.integer K
                              (@ValuativeRel.ValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                              (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                          (@Subring.toCommRing K (@Field.toCommRing K inst)
                            (@Valuation.integer K
                              (@ValuativeRel.ValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                              (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                          (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))))))
                (@Algebra.toModule (ZMod l)
                  (@IsLocalRing.ResidueField
                    (↥(@Valuation.integer K
                        (@ValuativeRel.ValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                    (@Subring.toCommRing K (@Field.toCommRing K inst)
                      (@Valuation.integer K
                        (@ValuativeRel.ValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                    (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                  (@Semifield.toCommSemiring (ZMod l) (@Field.toSemifield (ZMod l) (@ZMod.instField l inst_4)))
                  (@DivisionSemiring.toSemiring
                    (@IsLocalRing.ResidueField
                      (↥(@Valuation.integer K
                          (@ValuativeRel.ValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                          (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                      (@Subring.toCommRing K (@Field.toCommRing K inst)
                        (@Valuation.integer K
                          (@ValuativeRel.ValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                          (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                      (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                    (@Semifield.toDivisionSemiring
                      (@IsLocalRing.ResidueField
                        (↥(@Valuation.integer K
                            (@ValuativeRel.ValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                            (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                        (@Subring.toCommRing K (@Field.toCommRing K inst)
                          (@Valuation.integer K
                            (@ValuativeRel.ValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                            (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                        (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                      (@Field.toSemifield
                        (@IsLocalRing.ResidueField
                          (↥(@Valuation.integer K
                              (@ValuativeRel.ValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                              (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                          (@Subring.toCommRing K (@Field.toCommRing K inst)
                            (@Valuation.integer K
                              (@ValuativeRel.ValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                              (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                          (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                        (@IsLocalRing.ResidueField.field
                          (↥(@Valuation.integer K
                              (@ValuativeRel.ValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                              (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                          (@Subring.toCommRing K (@Field.toCommRing K inst)
                            (@Valuation.integer K
                              (@ValuativeRel.ValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                              (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                          (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3)))))
                  (@UpperTheory.Reformulated.B.Qi13.algRes K inst inst_1 inst_2 inst_3 l inst_4 inst_5)))
              (Fin (@UpperTheory.Reformulated.B.Qi13.fdim K inst inst_1 inst_2 inst_3 l inst_4 inst_5))
              (fun (x : Fin (@UpperTheory.Reformulated.B.Qi13.fdim K inst inst_1 inst_2 inst_3 l inst_4 inst_5)) ↦
                @IsLocalRing.ResidueField
                  (↥(@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@Subring.toCommRing K (@Field.toCommRing K inst)
                    (@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
              (@Module.Basis.instFunLike (Fin (@UpperTheory.Reformulated.B.Qi13.fdim K inst inst_1 inst_2 inst_3 l inst_4 inst_5)) (ZMod l)
                (@IsLocalRing.ResidueField
                  (↥(@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@Subring.toCommRing K (@Field.toCommRing K inst)
                    (@Valuation.integer K
                      (@ValuativeRel.ValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                      (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                        (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                      (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                  (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                (@DivisionSemiring.toSemiring (ZMod l)
                  (@Semifield.toDivisionSemiring (ZMod l) (@Field.toSemifield (ZMod l) (@ZMod.instField l inst_4))))
                (@Semiring.toAddCommMonoid
                  (@IsLocalRing.ResidueField
                    (↥(@Valuation.integer K
                        (@ValuativeRel.ValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                    (@Subring.toCommRing K (@Field.toCommRing K inst)
                      (@Valuation.integer K
                        (@ValuativeRel.ValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                    (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                  (@DivisionSemiring.toSemiring
                    (@IsLocalRing.ResidueField
                      (↥(@Valuation.integer K
                          (@ValuativeRel.ValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                          (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                      (@Subring.toCommRing K (@Field.toCommRing K inst)
                        (@Valuation.integer K
                          (@ValuativeRel.ValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                          (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                      (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                    (@Semifield.toDivisionSemiring
                      (@IsLocalRing.ResidueField
                        (↥(@Valuation.integer K
                            (@ValuativeRel.ValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                            (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                        (@Subring.toCommRing K (@Field.toCommRing K inst)
                          (@Valuation.integer K
                            (@ValuativeRel.ValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                            (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                        (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                      (@Field.toSemifield
                        (@IsLocalRing.ResidueField
                          (↥(@Valuation.integer K
                              (@ValuativeRel.ValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                              (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                          (@Subring.toCommRing K (@Field.toCommRing K inst)
                            (@Valuation.integer K
                              (@ValuativeRel.ValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                              (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                          (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                        (@IsLocalRing.ResidueField.field
                          (↥(@Valuation.integer K
                              (@ValuativeRel.ValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                              (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                          (@Subring.toCommRing K (@Field.toCommRing K inst)
                            (@Valuation.integer K
                              (@ValuativeRel.ValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                              (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                          (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))))))
                (@Algebra.toModule (ZMod l)
                  (@IsLocalRing.ResidueField
                    (↥(@Valuation.integer K
                        (@ValuativeRel.ValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                    (@Subring.toCommRing K (@Field.toCommRing K inst)
                      (@Valuation.integer K
                        (@ValuativeRel.ValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                        (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                          (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                        (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                    (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                  (@Semifield.toCommSemiring (ZMod l) (@Field.toSemifield (ZMod l) (@ZMod.instField l inst_4)))
                  (@DivisionSemiring.toSemiring
                    (@IsLocalRing.ResidueField
                      (↥(@Valuation.integer K
                          (@ValuativeRel.ValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                          (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                      (@Subring.toCommRing K (@Field.toCommRing K inst)
                        (@Valuation.integer K
                          (@ValuativeRel.ValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                          (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                            (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                          (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                      (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                    (@Semifield.toDivisionSemiring
                      (@IsLocalRing.ResidueField
                        (↥(@Valuation.integer K
                            (@ValuativeRel.ValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                            (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                        (@Subring.toCommRing K (@Field.toCommRing K inst)
                          (@Valuation.integer K
                            (@ValuativeRel.ValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                            (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                              (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                            (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                        (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                      (@Field.toSemifield
                        (@IsLocalRing.ResidueField
                          (↥(@Valuation.integer K
                              (@ValuativeRel.ValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                              (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                          (@Subring.toCommRing K (@Field.toCommRing K inst)
                            (@Valuation.integer K
                              (@ValuativeRel.ValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                              (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                          (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3))
                        (@IsLocalRing.ResidueField.field
                          (↥(@Valuation.integer K
                              (@ValuativeRel.ValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                              (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                          (@Subring.toCommRing K (@Field.toCommRing K inst)
                            (@Valuation.integer K
                              (@ValuativeRel.ValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@DivisionRing.toRing K (@Field.toDivisionRing K inst))
                              (@ValuativeRel.instLinearOrderedCommGroupWithZeroValueGroupWithZero K
                                (@Ring.toSemiring K (@DivisionRing.toRing K (@Field.toDivisionRing K inst))) inst_1)
                              (@ValuativeRel.valuation K (@DivisionRing.toRing K (@Field.toDivisionRing K inst)) inst_1)))
                          (@UpperTheory.Reformulated.B.Qi13.aux1 K inst inst_1 inst_2 inst_3)))))
                  (@UpperTheory.Reformulated.B.Qi13.algRes K inst inst_1 inst_2 inst_3 l inst_4 inst_5)))
              (@UpperTheory.Reformulated.B.Qi13.bb K inst inst_1 inst_2 inst_3 l inst_4 inst_5) i))
        (@UpperTheory.Reformulated.B.Qi13.aux8 K inst inst_1 inst_2 inst_3 l inst_4 inst_5 i)


