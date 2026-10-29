-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_CommutativityPoints_SharedHelpers_SharedLine
-- name    : LIDT_MIPStarRE_LDT_CommutativityPoints_SharedHelpers_SharedLine
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T11:46:07.492999+00:00
-- url     : https://prove2.me/theorems/ef38e410-2998-4545-afb1-0839bbad6d55
-- title:
--   LIDT definitions: LDT / CommutativityPoints / SharedHelpers / SharedLine
-- statement:
--   This bundle supplies the shared-diagonal-line reindexings used by the commutativity point comparisons. It turns a sampled pair of points and a parameter into a line question and gives the two equivalences needed when either point coordinate is ignored.
--
--   Principal definitions:
--   - `sharedDiagonalLineQuestionOfPointPair_sampledPointPair`: the sampled point pair recovered from the shared diagonal-line question.
--   - `sharedDiagonalLineQuestionOfPointPair_of_line`: the shared-line construction evaluated on two consecutive points of a given diagonal line.
--   - `pointPairSharedDiagonalLine_ignore_first_equiv`: the equivalence from a point pair plus parameter to a diagonal-line question when the first point coordinate is omitted.
--   - `pointPairSharedDiagonalLine_ignore_second_equiv`: the corresponding equivalence when the second point coordinate is omitted.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/CommutativityPoints/SharedHelpers/SharedLine.lean#L27-L137

-- Generated from MIPStarRE/LDT/CommutativityPoints/SharedHelpers/SharedLine.lean by skeleton subtraction.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionAvg
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionUniformSums
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LinePolynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LowDegreePolynomial
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_MeasurementLift
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OpFamily
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OperatorExpectations
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_PMFAverages
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_PMFUniformAverages
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersFiniteAnswers
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_QuantumState
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SubMeasurementCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SubMeasurementFamilies
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_TensorPlacement
import Definitions.Def_LIDT_MIPStarRE_LDT_CommutativityPoints_Approximation
import Definitions.Def_LIDT_MIPStarRE_LDT_CommutativityPoints_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_ComparisonCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_QuantumNonneg
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyFailures
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyRole_Algebra
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyRole_Core
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad

namespace LIDT

namespace MIPStarRE.LDT
end MIPStarRE.LDT
namespace MIPStarRE.LDT.CommutativityPoints
end MIPStarRE.LDT.CommutativityPoints

/-!
# Section 10 commutativity points: shared-line helpers

Compatibility lemmas between sampled point pairs and shared-diagonal line
questions, used by both the lift and drop comparisons.

## References

- `references/ldt-paper/commutativity-points.tex`
- `blueprint/src/chapter/ch08_commutativity.tex`
-/

@[expose] public section

namespace MIPStarRE.LDT.CommutativityPoints

open MIPStarRE.LDT.GlobalVariance (PointPairQuestion)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

open scoped _root_.Matrix MatrixOrder ComplexOrder BigOperators
 theorem sharedDiagonalLineQuestionOfPointPair_sampledPointPair
    (params : Parameters)
    [FieldModel params.q]
    (s : PointPairQuestion params × Fq params) :
    sampledPointPairFromSharedDiagonalQuestion params
      (sharedDiagonalLineQuestionOfPointPair params s) = s.1 := by
  rcases s with ⟨⟨u, v⟩, t⟩
  refine Prod.ext ?_ ?_
  · funext i
    simp [sampledPointPairFromSharedDiagonalQuestion, sharedDiagonalLineQuestionOfPointPair,
      DiagonalLine.pointAt, addPoint, smulPoint, addCoord, subCoord, mulCoord]
  · funext i
    suffices h :
        encodeScalar
            (decodeScalar (u i) - decodeScalar t * (decodeScalar (v i) - decodeScalar (u i)) +
              (decodeScalar t + 1) * (decodeScalar (v i) - decodeScalar (u i))) =
          v i by
      simpa [sampledPointPairFromSharedDiagonalQuestion, sharedDiagonalLineQuestionOfPointPair,
        DiagonalLine.pointAt, addPoint, smulPoint, addCoord, subCoord, mulCoord] using h
    rw [← encode_decodeScalar (v i)]
    congr 1
    ring_nf
    simp

private theorem sharedDiagonalLineQuestionOfPointPair_of_line
    (params : Parameters)
    [FieldModel params.q]
    (ℓ : DiagonalLine params)
    (t : Fq params) :
    sharedDiagonalLineQuestionOfPointPair params
      (((ℓ.pointAt t, ℓ.pointAt (addCoord t (encodeScalar 1))), t)) =
      (ℓ, (t, addCoord t (encodeScalar 1))) := by
  cases ℓ with
  | mk base direction =>
      change
        (({ base := fun i => _, direction := fun i => _ } : DiagonalLine params),
          (t, addCoord t (encodeScalar 1))) =
        ({ base := base, direction := direction }, (t, addCoord t (encodeScalar 1)))
      congr
      · funext i
        suffices h :
            encodeScalar
                (decodeScalar (base i) + decodeScalar t * decodeScalar (direction i) -
                  decodeScalar t *
                    ((decodeScalar t + 1) * decodeScalar (direction i) -
                      decodeScalar t * decodeScalar (direction i))) =
              base i by
          simpa [DiagonalLine.pointAt, addPoint, smulPoint, addCoord, subCoord,
            mulCoord] using h
        rw [← encode_decodeScalar (base i)]
        congr 1
        ring_nf
        simp
      · funext i
        suffices h :
            encodeScalar
                ((decodeScalar t + 1) * decodeScalar (direction i) -
                  decodeScalar t * decodeScalar (direction i)) =
              direction i by
          simpa [DiagonalLine.pointAt, addPoint, smulPoint, addCoord, subCoord,
            mulCoord] using h
        rw [← encode_decodeScalar (direction i)]
        congr 1
        ring_nf
        simp

 noncomputable def pointPairSharedDiagonalLine_ignore_first_equiv
    (params : Parameters)
    [FieldModel params.q] :
    (PointPairQuestion params × Fq params) ≃ PointDiagonalLineQuestion params where
  toFun := fun s =>
    let q := sharedDiagonalLineQuestionOfPointPair params s
    (q.1, q.2.2)
  invFun := fun r =>
    let ℓ := r.1
    let tv := r.2
    (((ℓ.pointAt (subCoord tv (encodeScalar 1)), ℓ.pointAt tv)),
      subCoord tv (encodeScalar 1))
  left_inv := fun ⟨⟨u, v⟩, t⟩ => by
    refine Prod.ext ?_ ?_
    · simpa [Prod.ext_iff, sampledPointPairFromSharedDiagonalQuestion,
        sharedDiagonalLineQuestionOfPointPair, addCoord, subCoord] using
        sharedDiagonalLineQuestionOfPointPair_sampledPointPair params ((u, v), t)
    · simp [sharedDiagonalLineQuestionOfPointPair, addCoord, subCoord]
  right_inv := fun ⟨ℓ, tv⟩ => by
    simpa [addCoord, subCoord] using
      congrArg (fun q => (q.1, q.2.2))
        (sharedDiagonalLineQuestionOfPointPair_of_line params ℓ
          (subCoord tv (encodeScalar 1)))

 noncomputable def pointPairSharedDiagonalLine_ignore_second_equiv
    (params : Parameters)
    [FieldModel params.q] :
    (PointPairQuestion params × Fq params) ≃ PointDiagonalLineQuestion params where
  toFun := fun s =>
    let q := sharedDiagonalLineQuestionOfPointPair params s
    (q.1, q.2.1)
  invFun := fun r =>
    let ℓ := r.1
    let t := r.2
    (((ℓ.pointAt t, ℓ.pointAt (addCoord t (encodeScalar 1))), t))
  left_inv := fun ⟨⟨u, v⟩, t⟩ => by
    refine Prod.ext ?_ ?_
    · simpa [Prod.ext_iff, sampledPointPairFromSharedDiagonalQuestion,
        sharedDiagonalLineQuestionOfPointPair] using
        sharedDiagonalLineQuestionOfPointPair_sampledPointPair params ((u, v), t)
    · simp [sharedDiagonalLineQuestionOfPointPair]
  right_inv := fun ⟨ℓ, t⟩ => by
    simpa using
      congrArg (fun q => (q.1, q.2.1))
        (sharedDiagonalLineQuestionOfPointPair_of_line params ℓ t)























end MIPStarRE.LDT.CommutativityPoints

end

end LIDT


