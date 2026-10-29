-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Core
-- name    : LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Core
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T11:33:10.329521+00:00
-- url     : https://prove2.me/theorems/a46fd417-c8de-4b9c-8009-4e94d02cd0f8
-- title:
--   LIDT definitions: LDT / GlobalVariance / Defs / Core
-- statement:
--   This bundle defines the finite sample spaces and polynomial answer types used by the global-variance comparison.
--
--   Principal definitions:
--   - `AxisParallelLineQuestion`: an incident axis-line and point question.
--   - `PointPairQuestion`: a pair of points used in local and global variance.
--   - `DegreeBoundedPolynomialAnswer`: a polynomial answer with the individual-degree bound.
--   - `pointOnLine`: the incidence predicate for a queried point and line.
--   - `axisParallelLineQuestionParameter`: recovers the affine line parameter.
--   - `axisParallelLineQuestionDistribution`: the uniform incident line-point distribution.
--   - `polynomialDistribution`: the uniform distribution on bounded polynomial answers.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/GlobalVariance/Defs/Core.lean#L32-L150

-- Generated from MIPStarRE/LDT/GlobalVariance/Defs/Core.lean by skeleton subtraction.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionAvg
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionUniformSums
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LinePolynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LowDegreePolynomial
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_PMFAverages
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_PMFUniformAverages
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersFiniteAnswers
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_QuantumState
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SubMeasurementCore
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
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

/-!
# Section 8 global variance: core definitions

Basic question and answer types (axis-parallel line questions, point-pair
questions) underlying the Section 8 global-variance construction.

## References

- `references/ldt-paper/expansion.tex`
- `blueprint/src/chapter/ch06_variance.tex`
-/

@[expose] public section

namespace MIPStarRE.LDT.GlobalVariance

open MIPStarRE.LDT
open MIPStarRE.LDT.MakingMeasurementsProjective
open MIPStarRE.LDT.ExpansionHypercubeGraph
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (params : Parameters) [FieldModel params.q]

/-! ## Basic question and answer types -/

/-- An axis-parallel line together with a point queried on that line. -/
abbrev AxisParallelLineQuestion (params : Parameters) :=
  AxisParallelLine params × Point params

/-- A pair of points used for local or global variance comparisons. -/
abbrev PointPairQuestion (params : Parameters) :=
  Point params × Point params

/-- Degree-bounded polynomial answers: global low-individual-degree polynomials over the
chosen field model, i.e. pairs of a multivariate polynomial and a proof that each
individual degree is at most `params.d`. Coerces to a raw function `Point params → Fq params`
via `Polynomial.toFun`, so downstream callers may still write `g u` to evaluate. -/
abbrev DegreeBoundedPolynomialAnswer (params : Parameters) [FieldModel params.q] :=
  Polynomial params



/-- Axis-parallel lines are finitely enumerable via their base point and direction. -/
noncomputable instance (params : Parameters) : Fintype (AxisParallelLine params) :=
  Fintype.ofInjective
    (fun ℓ : AxisParallelLine params => (ℓ.base, ℓ.direction))
    fun _ _ h => congrArg₂ AxisParallelLine.mk (congrArg Prod.fst h) (congrArg Prod.snd h)

/-- A default low-degree polynomial witnessing nonemptiness of the finite
polynomial answer type. -/
instance (params : Parameters) [FieldModel params.q] : Nonempty (Polynomial params) := by
  exact ⟨⟨0, by
    intro i
    -- Sound because each individual degree of the zero polynomial is `0`.
    simp [MvPolynomial.degreeOf_zero]⟩⟩

/-- A valid axis-parallel line question pairs a line with a point lying on it. -/
def pointOnLine {params : Parameters} [FieldModel params.q]
    (qu : AxisParallelLineQuestion params) : Prop :=
  ∃ t : Fq params, qu.1.pointAt t = qu.2

/-- The affine line parameter of the sampled point in an axis-parallel line question.

For a line `ℓ(t) = base + t e_i`, the sampled point `u` has affine parameter
`u_i - base_i`. This is the parameter used by the axis-parallel line-test API;
it is not the raw coordinate `u_i` unless the line base has zero in direction `i`. -/
def axisParallelLineQuestionParameter {params : Parameters} [FieldModel params.q]
    (qu : AxisParallelLineQuestion params) : Fq params :=
  subCoord (qu.2 qu.1.direction) (qu.1.base qu.1.direction)

/-- The recovered parameter of `ℓ.pointAt t` is exactly `t`. -/
@[simp] theorem axisParallelLineQuestionParameter_pointAt {params : Parameters}
    [FieldModel params.q] (ℓ : AxisParallelLine params) (t : Fq params) :
    axisParallelLineQuestionParameter (ℓ, ℓ.pointAt t) = t := by
  simp only [axisParallelLineQuestionParameter, AxisParallelLine.pointAt, if_pos]
  simp [subCoord, addCoord]

/-- The distribution of an axis-parallel line together with a point queried on it.

The paper samples `u ∈ F_q^m` uniformly, then samples a direction `i` uniformly,
and finally takes the axis-parallel line through `u` in direction `i`. Since
`AxisParallelLineQuestion params` is represented as a pair `(ℓ, u)`, we realize
this as the normalized uniform distribution on the finite set of incident pairs,
i.e. those with `u ∈ ℓ`. -/
noncomputable def axisParallelLineQuestionDistribution (params : Parameters) [FieldModel params.q] :
    Distribution (AxisParallelLineQuestion params) := by
  classical
  let support : Finset (AxisParallelLineQuestion params) :=
    Finset.univ.filter (pointOnLine (params := params))
  exact Distribution.uniformOnFinset support







/-- The uniform distribution over bundled low-individual-degree polynomials. -/
noncomputable def polynomialDistribution (params : Parameters) [FieldModel params.q] :
    Distribution (Polynomial params) :=
  uniformDistribution (Polynomial params)





end MIPStarRE.LDT.GlobalVariance

end

end LIDT


