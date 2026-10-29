-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Scaffold_Products
-- name    : LIDT_MIPStarRE_LDT_Commutativity_Scaffold_Products
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T11:48:52.433097+00:00
-- url     : https://prove2.me/theorems/57f335ab-5733-455c-bb2a-59983379c68d
-- title:
--   LIDT definitions: LDT / Commutativity / Scaffold / Products
-- statement:
--   This bundle names the operator products in the evaluated-slice commutator expansion and packages the factors needed for its full-slice comparison. The projective-family views allow later state-dependent-distance lemmas to apply directly to the factors.
--
--   Principal definitions:
--   - `evaluatedSliceBABTerm`: the evaluated-slice B-A-B product term.
--   - `evaluatedSliceABATerm`: the evaluated-slice A-B-A product term.
--   - `evaluatedSliceBABATerm`: the evaluated-slice B-A-B-A product term.
--   - `evaluatedSliceABABTerm`: the evaluated-slice A-B-A-B product term.
--   - `evaluatedSliceFirstProj`: the first evaluated-slice factor represented as a projective family.
--   - `evaluatedSliceSecondProj`: the second evaluated-slice factor represented as a projective family.
--   - `fullSliceFirstProj`: the first full-slice factor represented as a projective family.
--   - `fullSliceSecondProj`: the second full-slice factor represented as a projective family.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/Commutativity/Scaffold/Products.lean#L29-L424

-- Generated from MIPStarRE/LDT/Commutativity/Scaffold/Products.lean by skeleton subtraction.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionAvg
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionUniformSums
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LinePolynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LowDegreePolynomial
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
import Definitions.Def_LIDT_MIPStarRE_LDT_CommutativityPoints_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Defs_Normalization
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Defs_Stability
import Definitions.Def_LIDT_MIPStarRE_LDT_Commutativity_Scaffold_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyPolynomialFamilies
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

namespace MIPStarRE.LDT.Commutativity
end MIPStarRE.LDT.Commutativity

/-!
# Section 11 commutativity: product estimates

Basic product-style lemmas on projective submeasurement outcomes — in
particular orthogonality of distinct outcomes — reused throughout the
Section 11 commutativity argument.

## References

- `references/ldt-paper/commutativity-G.tex`
- `blueprint/src/chapter/ch08_commutativity.tex`
-/

@[expose] public section

namespace MIPStarRE.LDT.Commutativity

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Postprocessing a projective submeasurement preserves outcome projectivity. -/
lemma postprocess_proj_outcome
    {α β : Type*} [Fintype α] [Fintype β]
    (P : ProjSubMeas α ι) (f : α → β) (b : β) :
    (postprocess P.toSubMeas f).outcome b * (postprocess P.toSubMeas f).outcome b =
      (postprocess P.toSubMeas f).outcome b := by
  simpa using ProjSubMeas.postprocess_outcome_proj P f b

/-- Evaluating a projective polynomial family at a point preserves outcome projectivity. -/
lemma evaluatedPointFamily_outcome_proj
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (u : Point params.next) (a : Fq params) :
    (evaluatedPointFamily params family u).outcome a *
        (evaluatedPointFamily params family u).outcome a =
      (evaluatedPointFamily params family u).outcome a := by
  simpa [evaluatedPointFamily, IdxPolyFamily.evaluatedAtNextPoint, evaluateAt] using
    postprocess_proj_outcome (family.meas (pointHeight params u))
      (fun g => g (truncatePoint params u)) a







/-- The `BAB` term in the evaluated-slice commutator expansion. -/
noncomputable def evaluatedSliceBABTerm
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (q : EvaluatedSliceQuestion params) (ab : EvaluatedSliceOutcome params) : Error :=
  let A := (evaluatedPointFamily params family q.1).outcome ab.1
  let B := (evaluatedPointFamily params family q.2).outcome ab.2
  ev strategy.state <| leftTensor (ι₂ := ι) (B * A * B)

/-- The `ABA` term in the evaluated-slice commutator expansion. -/
noncomputable def evaluatedSliceABATerm
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (q : EvaluatedSliceQuestion params) (ab : EvaluatedSliceOutcome params) : Error :=
  let A := (evaluatedPointFamily params family q.1).outcome ab.1
  let B := (evaluatedPointFamily params family q.2).outcome ab.2
  ev strategy.state <| leftTensor (ι₂ := ι) (A * B * A)

/-- The `BABA` term in the evaluated-slice commutator expansion. -/
noncomputable def evaluatedSliceBABATerm
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (q : EvaluatedSliceQuestion params) (ab : EvaluatedSliceOutcome params) : Error :=
  let A := (evaluatedPointFamily params family q.1).outcome ab.1
  let B := (evaluatedPointFamily params family q.2).outcome ab.2
  ev strategy.state <| leftTensor (ι₂ := ι) (B * A * B * A)

/-- The `ABAB` term in the evaluated-slice commutator expansion. -/
noncomputable def evaluatedSliceABABTerm
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (q : EvaluatedSliceQuestion params) (ab : EvaluatedSliceOutcome params) : Error :=
  let A := (evaluatedPointFamily params family q.1).outcome ab.1
  let B := (evaluatedPointFamily params family q.2).outcome ab.2
  ev strategy.state <| leftTensor (ι₂ := ι) (A * B * A * B)

/-- The first evaluated-slice factor viewed as a projective family. -/
noncomputable def evaluatedSliceFirstProj
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    IdxProjSubMeas (EvaluatedSliceQuestion params) (Fq params) ι :=
  fun q =>
    { toSubMeas := evaluatedSliceFirstFactor params family q
      proj := evaluatedPointFamily_outcome_proj params family q.1 }

/-- The second evaluated-slice factor viewed as a projective family. -/
noncomputable def evaluatedSliceSecondProj
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    IdxProjSubMeas (EvaluatedSliceQuestion params) (Fq params) ι :=
  fun q =>
    { toSubMeas := evaluatedSliceSecondFactor params family q
      proj := evaluatedPointFamily_outcome_proj params family q.2 }

/-- The first full-slice factor viewed as a projective family. -/
noncomputable def fullSliceFirstProj
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    IdxProjSubMeas (FullSliceQuestion params) (Polynomial params) ι :=
  fun q => family.meas q.1

/-- The second full-slice factor viewed as a projective family. -/
noncomputable def fullSliceSecondProj
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    IdxProjSubMeas (FullSliceQuestion params) (Polynomial params) ι :=
  fun q => family.meas q.2

/-- The `BAB` term in the full-slice commutator expansion. -/
noncomputable def fullSliceBABTerm
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (q : FullSliceQuestion params) (gh : FullSliceOutcome params) : Error :=
  let A := (fullSliceFirstFactor params family q).outcome gh.1
  let B := (fullSliceSecondFactor params family q).outcome gh.2
  ev strategy.state <| leftTensor (ι₂ := ι) (B * A * B)

/-- The `ABA` term in the full-slice commutator expansion. -/
noncomputable def fullSliceABATerm
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (q : FullSliceQuestion params) (gh : FullSliceOutcome params) : Error :=
  let A := (fullSliceFirstFactor params family q).outcome gh.1
  let B := (fullSliceSecondFactor params family q).outcome gh.2
  ev strategy.state <| leftTensor (ι₂ := ι) (A * B * A)

/-- The `BABA` term in the full-slice commutator expansion. -/
noncomputable def fullSliceBABATerm
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (q : FullSliceQuestion params) (gh : FullSliceOutcome params) : Error :=
  let A := (fullSliceFirstFactor params family q).outcome gh.1
  let B := (fullSliceSecondFactor params family q).outcome gh.2
  ev strategy.state <| leftTensor (ι₂ := ι) (B * A * B * A)

/-- The `ABAB` term in the full-slice commutator expansion. -/
noncomputable def fullSliceABABTerm
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (q : FullSliceQuestion params) (gh : FullSliceOutcome params) : Error :=
  let A := (fullSliceFirstFactor params family q).outcome gh.1
  let B := (fullSliceSecondFactor params family q).outcome gh.2
  ev strategy.state <| leftTensor (ι₂ := ι) (A * B * A * B)



end MIPStarRE.LDT.Commutativity

end

end LIDT


