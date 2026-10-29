-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Operators
-- name    : LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Operators
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T11:36:49.989828+00:00
-- url     : https://prove2.me/theorems/e751f2aa-6736-41bd-bec3-37af7b06fe7f
-- title:
--   LIDT definitions: LDT / GlobalVariance / Defs / Operators
-- statement:
--   This bundle defines the weighted state and conditioned operators used in the global-variance expansion. A polynomial outcome supplies a positive square-root weight, which produces a generally unnormalized state and weighted point and line events on the two registers.
--
--   Principal definitions:
--   - `polynomialWeightSqrtOperator`: The positive square root $(G_g)^{1/2}$ of a polynomial outcome effect.
--   - `weightedPolynomialState`: The weighted density $W_g\rho W_g^\dagger$ with the weight placed on the designated register.
--   - `pointConditionedOutcomeOperatorAtPolynomial`: The point effect selecting the answer $g(u)$.
--   - `pointConditionedEventSubMeasAtPolynomial`: The two-outcome submeasurement for the event that the point answer equals $g(u)$.
--   - `weightedPointConditionedOperatorAtPolynomial` and `weightedPointConditionedRightOperatorAtPolynomial`: The left and right weighted point-event operators.
--   - `pointConditionedLocalVarianceAtPolynomial` and `pointConditionedGlobalVarianceAtPolynomial`: Local and global variance for a fixed polynomial in the weighted state.
--   - `generalizeBLeftOperatorAtPolynomial` and `generalizeBRightOperatorAtPolynomial`: The point-match and line-restriction operators used in the generalize-B comparison.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/GlobalVariance/Defs/Operators.lean#L20-L252

-- Generated from MIPStarRE/LDT/GlobalVariance/Defs/Operators.lean by skeleton subtraction.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
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

open scoped _root_.Matrix

namespace LIDT

/-! ## Weighted operators and variance families -/

@[expose] public section

namespace MIPStarRE.LDT.GlobalVariance

open MIPStarRE.LDT
open MIPStarRE.LDT.MakingMeasurementsProjective
open MIPStarRE.LDT.ExpansionHypercubeGraph
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (params : Parameters) [FieldModel params.q]

/-- The operator `(G_g)^{1/2}` used throughout `expansion.tex`.
Uses `CFC.sqrt` (continuous functional calculus) to compute the matrix
square root of the PSD operator `G.outcome g`. -/
noncomputable def polynomialWeightSqrtOperator (params : Parameters) [FieldModel params.q]
    (G : SubMeas (Polynomial params) ι) (g : Polynomial params) : MIPStarRE.Quantum.Op ι :=
  CFC.sqrt (G.outcome g)

/-- The weighted state `|ψ_g⟩ = (I ⊗ √G_g)|ψ⟩`, modeled as a density-matrix
transformation: `ρ_g = W_g ρ W_g†` where `W_g = I ⊗ √(G_g)`.

This is not necessarily normalized — normalization would require dividing by
`Tr(G_g ρ_B)`. We keep it unnormalized since the variance quantities in the
paper use unnormalized weighted expectations. -/
noncomputable def weightedPolynomialState (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι) (g : Polynomial params) :
    QuantumState (ι × ι) :=
  let sqrtG := polynomialWeightSqrtOperator params G g
  let W := rightTensor (ι₁ := ι) sqrtG
  { density := W * strategy.state.density * Wᴴ
    density_psd :=
      by
        simpa [Matrix.star_eq_conjTranspose] using
          star_right_conjugate_nonneg strategy.state.density_psd W }

/-- The concrete operator `A^u_{g(u)}` for a fixed polynomial `g`. -/
noncomputable def pointConditionedOutcomeOperatorAtPolynomial (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (g : Polynomial params) (u : Point params) : MIPStarRE.Quantum.Op ι :=
  (strategy.pointMeasurement u).toSubMeas.outcome (g u)

/-- The two-outcome point event selecting the answer `g(u)`.

This is the submeasurement form of the point operator used in the first and last
steps of `lem:local-variance-of-points` (`expansion.tex`, lines 305 and 311).
Its `some ()` outcome is exactly `A^u_{g(u)}`; the `none` outcome is the
complementary point-answer mass. -/
noncomputable def pointConditionedEventSubMeasAtPolynomial (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (g : Polynomial params) (u : Point params) : SubMeas (Option Unit) ι :=
  postprocess ((strategy.pointMeasurement u).toSubMeas)
    (fun a : Fq params => if a = g u then some () else none)

/-- The selected outcome of `pointConditionedEventSubMeasAtPolynomial` is
`A^u_{g(u)}`. -/
@[simp] lemma pointConditionedEventSubMeasAtPolynomial_some (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (g : Polynomial params) (u : Point params) :
    (pointConditionedEventSubMeasAtPolynomial params strategy g u).outcome (some ()) =
      pointConditionedOutcomeOperatorAtPolynomial params strategy g u := by
  classical
  unfold pointConditionedEventSubMeasAtPolynomial pointConditionedOutcomeOperatorAtPolynomial
  simp only [postprocess]
  refine Finset.sum_eq_single (g u) ?_ ?_
  · intro a ha hne
    simp [hne] at ha
  · simp

/-- The paper's weighted operator `A^u_{g(u)} ⊗ (G_g)^{1/2}`
on the bipartite space `d * d`. -/
noncomputable def weightedPointConditionedOperatorAtPolynomial (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι)
    (g : Polynomial params) (u : Point params) : MIPStarRE.Quantum.Op (ι × ι) :=
  opTensor
    (pointConditionedOutcomeOperatorAtPolynomial params strategy g u)
    (polynomialWeightSqrtOperator params G g)

/-- The right-register intermediate `I ⊗ (G_g)^{1/2} A^u_{g(u)}`
from the first and last self-consistency moves of
`lem:local-variance-of-points` (`expansion.tex`, lines 306 and 310). -/
noncomputable def weightedPointConditionedRightOperatorAtPolynomial (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι)
    (g : Polynomial params) (u : Point params) : MIPStarRE.Quantum.Op (ι × ι) :=
  rightTensor (ι₁ := ι)
    (polynomialWeightSqrtOperator params G g *
      pointConditionedOutcomeOperatorAtPolynomial params strategy g u)

/-- The local variance of `A(g)` on the weighted state `|ψ_g⟩`.
Operators are lifted to the left tensor factor of the bipartite state. -/
noncomputable def pointConditionedLocalVarianceAtPolynomial (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι)
    (g : Polynomial params) : Error :=
  localVariance params
    (fun u => leftTensor (ι₂ := ι)
      (pointConditionedOutcomeOperatorAtPolynomial params strategy g u))
    (weightedPolynomialState params strategy G g)

/-- The global variance of `A(g)` on the weighted state `|ψ_g⟩`.
Operators are lifted to the left tensor factor of the bipartite state. -/
noncomputable def pointConditionedGlobalVarianceAtPolynomial (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι)
    (g : Polynomial params) : Error :=
  globalVariance params
    (fun u => leftTensor (ι₂ := ι)
      (pointConditionedOutcomeOperatorAtPolynomial params strategy g u))
    (weightedPolynomialState params strategy G g)

/-- The polynomial-averaged local variance of the conditioned points family. -/
noncomputable def pointConditionedLocalVariance (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι) : Error :=
  avgOver (polynomialDistribution params)
    (fun g => pointConditionedLocalVarianceAtPolynomial params strategy G g)

/-- The polynomial-averaged global variance of the conditioned points family. -/
noncomputable def pointConditionedGlobalVariance (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι) : Error :=
  avgOver (polynomialDistribution params)
    (fun g => pointConditionedGlobalVarianceAtPolynomial params strategy G g)

/-- The `Option Unit` event submeasurement selecting axis-line answers that
match `g(u)` at the queried point `u` on the left side of `lem:generalize-b`. -/
noncomputable def generalizeBLeftEventSubMeasAtPolynomial (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (g : Polynomial params)
    (qu : AxisParallelLineQuestion params) : SubMeas (Option Unit) ι :=
  let (ℓ, u) := qu
  postprocess
    ((strategy.axisParallelMeasurement ℓ).toSubMeas)
    (fun f : AxisLinePolynomial params =>
      if f (axisParallelLineQuestionParameter qu) = g u then
        some ()
      else
        none)

/-- The `Option Unit` event submeasurement selecting axis-line answers that
match the restriction of `g` to `ℓ` on the right side of `lem:generalize-b`. -/
noncomputable def generalizeBRightEventSubMeasAtPolynomial (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (g : Polynomial params)
    (qu : AxisParallelLineQuestion params) : SubMeas (Option Unit) ι :=
  let ℓ := qu.1
  let gRestricted := Polynomial.restrictToAxisParallelLine params g ℓ
  postprocess
    ((strategy.axisParallelMeasurement ℓ).toSubMeas)
    (fun f : AxisLinePolynomial params =>
      if f.poly = gRestricted.poly then
        some ()
      else
        none)

/-- The residual projective `Option Unit` event from the proof of
`lem:generalize-b`: axis-line answers that collide with `g` at the sampled point
`u`, but are not the restricted polynomial `g|_ℓ`.  After the
projective-measurement expansion, the squared difference is controlled by this
collision event. -/
noncomputable def generalizeBCollisionEventProjMeasAtPolynomial (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (g : Polynomial params)
    (qu : AxisParallelLineQuestion params) : ProjMeas (Option Unit) ι :=
  let (ℓ, u) := qu
  let gRestricted := Polynomial.restrictToAxisParallelLine params g ℓ
  ProjMeas.postprocess (strategy.axisParallelMeasurement ℓ)
    (fun f : AxisLinePolynomial params =>
      if f (axisParallelLineQuestionParameter qu) = g u ∧ f.poly ≠ gRestricted.poly then
        some ()
      else
        none)

/-- The residual event above, forgetting projectivity to a submeasurement.  Keeping
this definition as the `toSubMeas` of `generalizeBCollisionEventProjMeasAtPolynomial`
prevents the projective and submeasurement views from drifting apart. -/
noncomputable def generalizeBCollisionEventSubMeasAtPolynomial (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (g : Polynomial params)
    (qu : AxisParallelLineQuestion params) : SubMeas (Option Unit) ι :=
  (generalizeBCollisionEventProjMeasAtPolynomial params strategy g qu).toSubMeas

/-- The event operator for the residual line-collision event in `lem:generalize-b`. -/
noncomputable def generalizeBCollisionOperatorAtPolynomial (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (g : Polynomial params)
    (qu : AxisParallelLineQuestion params) : MIPStarRE.Quantum.Op ι :=
  (generalizeBCollisionEventSubMeasAtPolynomial params strategy g qu).outcome (some ())

/-- The event operator `B^ℓ_{[f(u)=g(u)]}`: sum of axis-line measurement
outcomes `f` that evaluate to the same value as `g` at point `u`. -/
noncomputable def generalizeBLeftOperatorAtPolynomial (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (g : Polynomial params)
    (qu : AxisParallelLineQuestion params) : MIPStarRE.Quantum.Op ι :=
  (generalizeBLeftEventSubMeasAtPolynomial params strategy g qu).outcome (some ())

/-- The event operator `B^ℓ_{[f = g|_ℓ]}`: sum of axis-line measurement
outcomes `f` that agree with `g` restricted to line `ℓ`. -/
noncomputable def generalizeBRightOperatorAtPolynomial (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (g : Polynomial params)
    (qu : AxisParallelLineQuestion params) : MIPStarRE.Quantum.Op ι :=
  (generalizeBRightEventSubMeasAtPolynomial params strategy g qu).outcome (some ())

/-- The weighted left operator in `lem:generalize-b`
on the bipartite space `d * d`. -/
noncomputable def weightedGeneralizeBLeftOperatorAtPolynomial (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι)
    (g : Polynomial params)
    (qu : AxisParallelLineQuestion params) : MIPStarRE.Quantum.Op (ι × ι) :=
  opTensor
    (generalizeBLeftOperatorAtPolynomial params strategy g qu)
    (polynomialWeightSqrtOperator params G g)

/-- The weighted right operator in `lem:generalize-b`
on the bipartite space `d * d`. -/
noncomputable def weightedGeneralizeBRightOperatorAtPolynomial (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι)
    (g : Polynomial params)
    (qu : AxisParallelLineQuestion params) : MIPStarRE.Quantum.Op (ι × ι) :=
  opTensor
    (generalizeBRightOperatorAtPolynomial params strategy g qu)
    (polynomialWeightSqrtOperator params G g)

end MIPStarRE.LDT.GlobalVariance

end

end LIDT


