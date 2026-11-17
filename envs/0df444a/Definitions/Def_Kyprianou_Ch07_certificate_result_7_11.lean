-- Prove2me | Definitions.Def_Kyprianou_Ch07_certificate_result_7_11
-- name    : Kyprianou_Ch07_certificate_result_7_11
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-16T14:57:27.365629+00:00
-- url     : https://prove2.me/theorems/cfb93fd8-dff7-4061-a2a6-cdde23591f50
-- title:
--   Full quantified certificate for upwardCreepingLevyTripletCriterion
-- statement:
--   Source-exact closed quantified proposition obtained from the canonical parent theorem without dropping any binders or clauses.
-- source:
--   Kyprianou (2006), Theorem 7.11(i)–(iii), printed pp.198–199, original PDF physical pp.207–208, Windows Ky.pdf sheets 104–105.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_RealLevyLawAndRegularityIntegrals
import Definitions.Def_Kyprianou_Ch06_LevyKhintchineTriple
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch07

/-- Source-quantified full proposition of upwardCreepingLevyTripletCriterion. -/
def certificate_result_7_11 : Prop :=
  ∀ {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → Real)
    (b : Real) (sigma2 : NNReal) (Pi : Measure Real)
    (hX : Kyprianou.Ch06.IsRealLevyProcess P X)
    (hNonCompound : ¬ Kyprianou.Ch06.IsCompoundPoissonProcess P X)
    (hTriplet : Kyprianou.Ch06.IsLevyKhintchineTriplet P X b sigma2 Pi),
    let finiteVariationJumpMass : Prop :=
      (∫⁻ x : Real in {x | |x| < 1},
        ENNReal.ofReal |x| ∂Pi) < ⊤
    let canonicalDrift : Real :=
      b - ∫ x : Real in {x | |x| < 1}, x ∂Pi
    let unboundedPureJump : Prop :=
      sigma2 = 0 ∧ ¬ finiteVariationJumpMass
    let mixedJumpCriterion : Prop :=
      (∫⁻ x : Real in Set.Ioo 0 1,
         (ENNReal.ofReal x * Pi (Set.Ioi x)) /
         (∫⁻ u : Real in Set.Ioo 0 x,
            Pi (Set.Ioo (-1) (-u)) ∂volume) ∂volume) < ⊤
    (0 < Kyprianou.Ch05.creepingProbability
        P X (fun _ => (⊤ : WithTop NNReal)) 1 ↔
      ((sigma2 = 0 ∧ finiteVariationJumpMass ∧ 0 < canonicalDrift) ∨
       (0 < sigma2) ∨
       (unboundedPureJump ∧ mixedJumpCriterion)))

end Kyprianou.Ch07


