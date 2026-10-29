-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_Test_MainTheorem_SourceScalars
-- name    : LIDT_MIPStarRE_LDT_Test_MainTheorem_SourceScalars
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T12:37:02.915327+00:00
-- url     : https://prove2.me/theorems/00dd6353-d2d9-44ec-9b93-5382b5c9e486
-- title:
--   LIDT definitions: LDT / Test / MainTheorem / SourceScalars
-- statement:
--   This bundle defines the scalar bookkeeping for the two-space main formal theorem. It specializes the main-induction quantity to the symmetrized strategy, packages the cascade hypotheses, and names the successive quantities $\sigma,\zeta_1,\zeta_2,\zeta_3,\zeta_4$ together with the repaired line-169 expression.
--
--   Principal definitions:
--   - `mainFormalInductionNu`: The main-induction quantity at the three input errors $3\varepsilon$.
--   - `MainFormalScalarBounds`: The package of cascade hypotheses and bounds used to absorb the scalar errors.
--   - `cascadeSigma`: The first scalar error formed from the induction quantity.
--   - `cascadeZeta1`: The point and collision error after the first cascade step.
--   - `cascadeZeta2`: The orthonormalization and completion error.
--   - `cascadeZeta3`: The projective self-consistency error.
--   - `cascadeZeta4`: The final point-consistency error.
--   - `cascadeZeta4Repaired`: The fourth-stage error using the checked repaired line-169 transport.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/Test/MainTheorem/SourceScalars.lean#L56-L325

-- Generated from MIPStarRE/LDT/Test/MainTheorem/SourceScalars.lean by skeleton subtraction.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SqrtBounds
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SubMeasurementCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SubMeasurementFamilies
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_TensorPlacement
import Definitions.Def_LIDT_MIPStarRE_LDT_MainInductionStep_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Projectivization
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_ProjectivizationChain_Basic
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayerIdentities_LayerAlgebra
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayerIdentities_PositiveGram_Completion
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayerIdentities_PositiveGram_Rows
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayerIdentities_PositiveGram_Sigma
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayerIdentities_ProjectorApprox
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayer_AlmostProjective
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayer_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayer_QCompleteness
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayer_RankReduction_LowRank
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayer_RankReduction_Sigma
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayer_TruncationCombinatorics
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Statements
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Completion
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Local
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_CauchySchwarz
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_ComparisonCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Completion
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_CompletionTransfer
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_DistanceBounds
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichMain_Completeness
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_ApproxDelta
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_InnerProduct
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Triangles_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_LdtSimp
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_LdtSimpAttr
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_QuantumNonneg
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_MainTheorem_ScalarBounds_Definitions
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_MainTheorem_ScalarBounds_EnvelopeBounds
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteHilbert
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_LIDT_MIPStarRE_Quantum_ProjectorONB
import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Tactic.Attr.Register

namespace LIDT

namespace MIPStarRE.LDT
end MIPStarRE.LDT
namespace MIPStarRE.LDT.MakingMeasurementsProjective
end MIPStarRE.LDT.MakingMeasurementsProjective
namespace MIPStarRE.LDT.Preliminaries
end MIPStarRE.LDT.Preliminaries
namespace MIPStarRE.LDT.Test
end MIPStarRE.LDT.Test

/-!
# Main-formal scalar bounds

Scalar estimates for the two-space `mainFormal` theorem.  This module defines
the five scalars that appear in the paper's error calculation:

* `σ` — the symmetrized induction consistency error
* `ζ₁` — the cross-consistency error after unsymmetrization
* `ζ₂` — the orthonormalize-and-complete closeness error
* `ζ₃` — the projective self-consistency error
* `ζ₄` — the final point-consistency error

The core structure `MainFormalScalarBounds` (Prop) bundles the three
hypotheses needed to invoke the checked Step 8 bound
`errorCascade_le_mainFormalError`:

* `cascadeHypotheses` — the standing scalar regime (`q > 0`, `k ≥ 1`,
  `m ≥ 1`, `0 ≤ ε ≤ 1`, `d ≤ q`).
* `inductionNu_nonneg` — nonnegativity of the symmetrized main-induction
  `ν` at `(3ε, 3ε, 3ε)`.
* `inductionNu_bound` — the paper line 71–73 coarsening
  `ν ≤ 10000 k² m² (ε^{1/1024} + (d/q)^{1/1024})`.

The cascade comparisons `ζ₁ ≤ …`, `ζ₃ ≤ 2·mainFormalError`, etc. are then
derived in the private theorem `cascadeBounds` via
`errorCascade_le_mainFormalError`, which calls the already-formalized
scalar cascade estimates from `LDT.Test.MainTheorem.ScalarBounds`.  The module also
provides the vacuous-branch analysis (`mainFormalError_ge_one_of_*`) and
the coarsening lemma that absorbs `orthonormalizeAndCompleteError` into
`ζ₂` (`orthonormalizeAndCompleteError_zeta1_le_zeta2`).

## References

* Paper: `references/ldt-paper/inductive_step.tex`,
  error computations (lines 68–75, 186–234).
* Blueprint: `blueprint/src/chapter/ch10_induction.tex`,
  `\label{def:main-formal-error-cascade}`,
  `\label{thm:sigma-bound-main-formal}`, and
  `\label{thm:zeta-bounds-main-formal}`.
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

namespace MIPStarRE.LDT

namespace Test

/-- The Section 3 specialization of the main-induction `ν` after Step 1
symmetrization.

Paper lines 68--75 apply `thm:main-induction` to the symmetrized strategy with
errors `(3ε, 3ε, 3ε)` and then coarsen its `ν` to the Section 3 scalar cascade.
This definition keeps the pre-coarsened main-induction quantity available for the
main theorem conclusion. -/
noncomputable def mainFormalInductionNu (params : Parameters) (k : ℕ) (eps : Error) : Error :=
  MainInductionStep.mainInductionNu params k (3 * eps) (3 * eps) (3 * eps)















/-- Scalar hypotheses for the Section 3 error cascade of `mainFormal`.

This record is intentionally scalar-only. It does not assert any measurement
transport. Its fields are precisely the hypotheses needed to invoke the already
formalized Step 8 bound `errorCascade_le_mainFormalError` on the
main-induction `ν` produced after symmetrization (paper lines 68--75). The
corrected source route derives these scalar side conditions in the non-vacuous
branch and otherwise uses the saturated-error witness. -/
structure MainFormalScalarBounds (params : Parameters) (eps : Error) (k : ℕ) : Prop where
  /-- Standing scalar regime for the paper's cascade estimates. -/
  cascadeHypotheses : CascadeHypotheses params k eps
  /-- Nonnegativity of the main-induction `ν` at `(3ε, 3ε, 3ε)`. -/
  inductionNu_nonneg : 0 ≤ mainFormalInductionNu params k eps
  /-- Paper line 71--73 coarsening of the main-induction `ν`. -/
  inductionNu_bound :
    mainFormalInductionNu params k eps ≤
      10000 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (2 : ℕ)) *
        (Real.rpow eps (1 / (1024 : Error)) +
          Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (1024 : Error)))

namespace MainFormalScalarBounds





/-- The paper's `σ`, built from the symmetrized main-induction `ν`. -/
noncomputable def sigma {params : Parameters} {eps : Error} {k : ℕ}
    (_scalars : MainFormalScalarBounds params eps k) : Error :=
  cascadeSigma params k (mainFormalInductionNu params k eps)

/-- The paper's `ζ₁ = 2σ + 2√(3ε + 2σ) + md/q`. -/
noncomputable def zeta1 {params : Parameters} {eps : Error} {k : ℕ}
    (scalars : MainFormalScalarBounds params eps k) : Error :=
  cascadeZeta1 params eps scalars.sigma

/-- The formal Step 6 scalar
`ζ₂ = 200ζ₁^(1/4) + 42ζ₁^(1/8)`, widening the paper's printed coefficient
`40` to absorb the extra completion term. -/
noncomputable def zeta2 {params : Parameters} {eps : Error} {k : ℕ}
    (scalars : MainFormalScalarBounds params eps k) : Error :=
  cascadeZeta2 scalars.zeta1

/-- The paper's self-consistency scalar `ζ₃ = 6ζ₁ + 6ζ₂`. -/
noncomputable def zeta3 {params : Parameters} {eps : Error} {k : ℕ}
    (scalars : MainFormalScalarBounds params eps k) : Error :=
  cascadeZeta3 scalars.zeta1 scalars.zeta2

/-- The paper's point-consistency scalar `ζ₄ = 2σ + 2√(ζ₁ + ζ₃/2)`. -/
noncomputable def zeta4 {params : Parameters} {eps : Error} {k : ℕ}
    (scalars : MainFormalScalarBounds params eps k) : Error :=
  cascadeZeta4 scalars.sigma scalars.zeta1 scalars.zeta3

/-- The repaired line-169 error `ζ₁ + 10·ζ₁^(1/8)` coming from the checked local
pre-completion transport. -/
noncomputable def line169Error {params : Parameters} {eps : Error} {k : ℕ}
    (scalars : MainFormalScalarBounds params eps k) : Error :=
  cascadeLine169RepairError scalars.zeta1

/-- The repaired point-consistency scalar obtained by substituting the checked
line-169 repair error into the final point-transport triangle.

**Source:** This is source-faithful scalar bookkeeping for the repaired
line-169 route documented in `docs/paper-gaps/issue-1099-sharper-local-fix.tex`
and absorbed by the paper's final cascade estimate in
`references/ldt-paper/inductive_step.tex:186-234`. -/
noncomputable def zeta4Repaired {params : Parameters} {eps : Error} {k : ℕ}
    (scalars : MainFormalScalarBounds params eps k) : Error :=
  cascadeZeta4Repaired scalars.sigma scalars.zeta1 scalars.zeta3

















end MainFormalScalarBounds

end Test

end MIPStarRE.LDT

end

end LIDT


