-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_TransportChain_Core
-- name    : LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_TransportChain_Core
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T12:05:40.003044+00:00
-- url     : https://prove2.me/theorems/b93850c8-d4f1-4527-b6e3-42a1bf411a72
-- title:
--   LIDT definitions: LDT / GlobalVariance / Theorems / TransportChain / Core
-- statement:
--   This bundle supplies the data and estimates for the six-step transport chain in the local-variance argument. It reindexes transport questions and singleton operator families, then absorbs the accumulated edge error into the stated local-variance slack.
--
--   Principal definitions:
--   - `TransportQuestion`: the question type used for one transport edge.
--   - `singletonOpFamily`: an operator family with one indexed outcome.
--   - `sddOpRel_singleton_of_bound`: a pointwise bound packaged as a singleton operator-family state-dependent-distance relation.
--   - `avgOver_transport_leftQuestion`: the averaging identity for the left transport question.
--   - `avgOver_transport_rightQuestion`: the corresponding right transport averaging identity.
--   - `addCoordLeftEquiv`: the equivalence that inserts a coordinate on the left side of a transport question.
--   - `localVarianceTransportChainBound`: the native six-step edge transport estimate.
--   - `localVarianceTransportChainError_le_localVarianceOfPointsError`: the post-triangle transport error bounded by the `24 (eps + delta + m d / q)` local-variance slack.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/GlobalVariance/Theorems/TransportChain/Core.lean#L26-L505

-- Generated from MIPStarRE/LDT/GlobalVariance/Theorems/TransportChain/Core.lean by skeleton subtraction.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Fourier
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_MatrixRealization_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_MatrixRealization_TraceForms
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Theorems_Foundations
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Theorems_Matrix
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Theorems_Results
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Families
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Operators
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_AlgebraicIdentity
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_Averaging
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_CollisionExpansion
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_SelfConsistencyTransport_Point
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_SelfConsistencyTransport_PointLine
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_SelfConsistencyTransport_Utilities
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_Statements
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Completion
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Local
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_CauchySchwarz
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_ComparisonCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_CompletionTransfer
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_DistanceBounds
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_PolynomialAgreement
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Polynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SelfConsistency_Extensions
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichMain_Completeness
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_ApproxDelta
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_InnerProduct
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
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.RingTheory.MvPolynomial.Basic

open scoped _root_.Matrix

namespace LIDT

namespace MIPStarRE.LDT.Preliminaries
end MIPStarRE.LDT.Preliminaries

/-! # Six-step local-variance transport-chain assembly

This module assembles the six steps of `lem:local-variance-of-points`
(`expansion.tex`, lines 305--311) into a single triangle-inequality bound
on the hypercube-edge distribution, producing the main transport estimate
`localVarianceTransportChainBound`.
-/

namespace MIPStarRE.LDT.GlobalVariance

open MIPStarRE.LDT
open MIPStarRE.LDT.Preliminaries
open MIPStarRE.LDT.MakingMeasurementsProjective
open MIPStarRE.LDT.ExpansionHypercubeGraph
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

@[expose] public section

abbrev TransportQuestion (params : Parameters) [FieldModel params.q] :=
  (AxisParallelLine params × Fq params) × Fq params

private noncomputable def singletonOpFamily {Question κ : Type*}
    [Fintype κ] [DecidableEq κ]
    (X : Question → MIPStarRE.Quantum.Op κ) :
    IdxOpFamily Question Unit κ :=
  fun q => { outcome := fun _ => X q, total := X q }

private lemma sddOpRel_singleton_of_bound {Question κ : Type*}
    [Fintype κ] [DecidableEq κ]
    (ψ : QuantumState κ) (𝒟 : Distribution Question)
    (X Y : Question → MIPStarRE.Quantum.Op κ) (δ : Error)
    (h :
      avgOver 𝒟 (fun q => ev ψ (((X q - Y q)ᴴ) * (X q - Y q))) ≤ δ) :
    SDDOpRel ψ 𝒟 (singletonOpFamily X) (singletonOpFamily Y) δ := by
  refine ⟨?_⟩
  simpa [sddErrorOp, qSDDOp, qSDDCore, singletonOpFamily] using h

lemma avgOver_transport_leftQuestion
    (params : Parameters) [FieldModel params.q]
    (f : AxisParallelLineQuestion params → Error) :
    avgOver (uniformDistribution (TransportQuestion params))
      (fun q => f (q.1.1, q.1.1.pointAt q.1.2)) =
    avgOver (axisParallelLineQuestionDistribution params) f := by
  calc
    avgOver (uniformDistribution (TransportQuestion params))
        (fun q => f (q.1.1, q.1.1.pointAt q.1.2))
      = avgOver (uniformDistribution (AxisParallelLine params × Fq params))
          (fun ℓt => f (ℓt.1, ℓt.1.pointAt ℓt.2)) := by
          exact avgOver_uniform_fst
            (α := AxisParallelLine params × Fq params) (β := Fq params)
            (fun ℓt => f (ℓt.1, ℓt.1.pointAt ℓt.2))
    _ = avgOver (axisParallelLineQuestionDistribution params) f :=
        (avgOver_axisParallelLineQuestionDistribution params f).symm

lemma avgOver_transport_rightQuestion
    (params : Parameters) [FieldModel params.q]
    (f : AxisParallelLineQuestion params → Error) :
    avgOver (uniformDistribution (TransportQuestion params))
      (fun q => f (q.1.1, q.1.1.pointAt q.2)) =
    avgOver (axisParallelLineQuestionDistribution params) f := by
  calc
    avgOver (uniformDistribution (TransportQuestion params))
        (fun q => f (q.1.1, q.1.1.pointAt q.2))
      = avgOver (uniformDistribution (AxisParallelLine params × Fq params))
          (fun ℓt =>
            avgOver (uniformDistribution (Fq params))
              (fun t => f (ℓt.1, ℓt.1.pointAt t))) := by
          exact avgOver_uniform_prod
            (α := AxisParallelLine params × Fq params) (β := Fq params)
            (f := fun ℓt t => f (ℓt.1, ℓt.1.pointAt t))
    _ = avgOver (uniformDistribution (AxisParallelLine params))
          (fun ℓ =>
            avgOver (uniformDistribution (Fq params))
              (fun t => f (ℓ, ℓ.pointAt t))) := by
          exact avgOver_uniform_fst
            (α := AxisParallelLine params) (β := Fq params)
            (fun ℓ =>
              avgOver (uniformDistribution (Fq params))
                (fun t => f (ℓ, ℓ.pointAt t)))
    _ = avgOver (uniformDistribution (AxisParallelLine params × Fq params))
          (fun ℓt => f (ℓt.1, ℓt.1.pointAt ℓt.2)) := by
          exact (avgOver_uniform_prod
            (α := AxisParallelLine params) (β := Fq params)
            (f := fun ℓ t => f (ℓ, ℓ.pointAt t))).symm
    _ = avgOver (axisParallelLineQuestionDistribution params) f :=
        (avgOver_axisParallelLineQuestionDistribution params f).symm

lemma avgOver_transport_leftPoint
    (params : Parameters) [FieldModel params.q]
    (f : Point params → Error) :
    avgOver (uniformDistribution (TransportQuestion params))
      (fun q => f (q.1.1.pointAt q.1.2)) =
    avgOver (uniformDistribution (Point params)) f := by
  calc
    avgOver (uniformDistribution (TransportQuestion params))
        (fun q => f (q.1.1.pointAt q.1.2))
      = avgOver (axisParallelLineQuestionDistribution params)
          (fun qu => f qu.2) := by
          exact avgOver_transport_leftQuestion params (fun qu => f qu.2)
    _ = avgOver (uniformDistribution (AxisParallelTestSample params))
          (fun s => f s.1) := by
          exact avgOver_axisParallelLineQuestionDistribution_to_axisParallelTestSample
            params (fun s => f s.1)
    _ = avgOver (uniformDistribution (Point params)) f := by
          exact avgOver_uniform_fst (α := Point params) (β := Fin params.m) f

lemma avgOver_transport_rightPoint
    (params : Parameters) [FieldModel params.q]
    (f : Point params → Error) :
    avgOver (uniformDistribution (TransportQuestion params))
      (fun q => f (q.1.1.pointAt q.2)) =
    avgOver (uniformDistribution (Point params)) f := by
  calc
    avgOver (uniformDistribution (TransportQuestion params))
        (fun q => f (q.1.1.pointAt q.2))
      = avgOver (axisParallelLineQuestionDistribution params)
          (fun qu => f qu.2) := by
          exact avgOver_transport_rightQuestion params (fun qu => f qu.2)
    _ = avgOver (uniformDistribution (AxisParallelTestSample params))
          (fun s => f s.1) := by
          exact avgOver_axisParallelLineQuestionDistribution_to_axisParallelTestSample
            params (fun s => f s.1)
    _ = avgOver (uniformDistribution (Point params)) f := by
          exact avgOver_uniform_fst (α := Point params) (β := Fin params.m) f

private noncomputable def addCoordLeftEquiv (params : Parameters) [FieldModel params.q]
    (c : Fq params) : Fq params ≃ Fq params where
  toFun := fun x => addCoord c x
  invFun := fun y => subCoord y c
  left_inv := fun x => by
    simp [addCoord, subCoord, decode_encodeScalar]
  right_inv := fun y => addCoord_subCoord_right y c

private lemma transportQuestionEquiv_symm_pair
    (params : Parameters) [FieldModel params.q]
    (stx : (AxisParallelTestSample params × Fq params) × Fq params) :
    let e : TransportQuestion params ≃
        (AxisParallelTestSample params × Fq params) × Fq params :=
      Equiv.prodCongr (axisParallelLinePointParamEquiv params) (Equiv.refl (Fq params))
    (((e.symm stx).1.1).pointAt ((e.symm stx).1.2),
        ((e.symm stx).1.1).pointAt (e.symm stx).2) =
      (stx.1.1.1,
        Function.update stx.1.1.1 stx.1.1.2
          (addCoord (subCoord (stx.1.1.1 stx.1.1.2) stx.1.2) stx.2)) := by
  cases stx with
  | mk st x =>
      cases st with
      | mk s t0 =>
          cases s with
          | mk u direction =>
              dsimp [axisParallelLinePointParamEquiv]
              apply Prod.ext
              · ext j
                by_cases hj : j = direction <;>
                  simp [AxisParallelLine.pointAt, hj]
              · ext j
                by_cases hj : j = direction <;>
                  simp [AxisParallelLine.pointAt, Function.update, hj]

lemma avgOver_transport_pointPair
    (params : Parameters) [FieldModel params.q]
    (f : Point params × Point params → Error) :
    avgOver (uniformDistribution (TransportQuestion params))
      (fun q => f (q.1.1.pointAt q.1.2, q.1.1.pointAt q.2)) =
    avgOver (uniformDistribution (AxisParallelTestSample params × Fq params))
      (fun sx => f (sx.1.1, Function.update sx.1.1 sx.1.2 sx.2)) := by
  classical
  let e : TransportQuestion params ≃
      (AxisParallelTestSample params × Fq params) × Fq params :=
    Equiv.prodCongr (axisParallelLinePointParamEquiv params) (Equiv.refl (Fq params))
  calc
    avgOver (uniformDistribution (TransportQuestion params))
        (fun q => f (q.1.1.pointAt q.1.2, q.1.1.pointAt q.2))
      = avgOver (uniformDistribution ((AxisParallelTestSample params × Fq params) × Fq params))
          (fun stx =>
            f (((e.symm stx).1.1).pointAt ((e.symm stx).1.2),
              ((e.symm stx).1.1).pointAt (e.symm stx).2)) := by
          exact avgOver_uniform_equiv (e := e)
            (f := fun q : TransportQuestion params =>
              f (q.1.1.pointAt q.1.2, q.1.1.pointAt q.2))
    _ = avgOver (uniformDistribution ((AxisParallelTestSample params × Fq params) × Fq params))
          (fun stx =>
            f (stx.1.1.1,
              Function.update stx.1.1.1 stx.1.1.2
                (addCoord (subCoord (stx.1.1.1 stx.1.1.2) stx.1.2) stx.2))) := by
          apply avgOver_congr
          intro stx
          exact congrArg f (transportQuestionEquiv_symm_pair params stx)
    _ = avgOver (uniformDistribution (AxisParallelTestSample params × Fq params))
          (fun stAux =>
            avgOver (uniformDistribution (Fq params))
              (fun t => f (stAux.1.1,
                Function.update stAux.1.1 stAux.1.2
                  (addCoord (subCoord (stAux.1.1 stAux.1.2) stAux.2) t)))) := by
          exact avgOver_uniform_prod
            (α := AxisParallelTestSample params × Fq params) (β := Fq params)
            (f := fun stAux t => f (stAux.1.1,
              Function.update stAux.1.1 stAux.1.2
                (addCoord (subCoord (stAux.1.1 stAux.1.2) stAux.2) t)))
    _ = avgOver (uniformDistribution (AxisParallelTestSample params × Fq params))
          (fun stAux =>
            avgOver (uniformDistribution (Fq params))
              (fun x => f (stAux.1.1, Function.update stAux.1.1 stAux.1.2 x))) := by
          apply avgOver_congr
          intro stAux
          let c : Fq params := subCoord (stAux.1.1 stAux.1.2) stAux.2
          calc
            avgOver (uniformDistribution (Fq params))
                (fun t => f (stAux.1.1,
                  Function.update stAux.1.1 stAux.1.2 (addCoord c t)))
              = avgOver (uniformDistribution (Fq params))
                  (fun x => f (stAux.1.1,
                    Function.update stAux.1.1 stAux.1.2
                      (addCoord c ((addCoordLeftEquiv params c).symm x)))) := by
                    exact avgOver_uniform_equiv (e := addCoordLeftEquiv params c)
                      (f := fun t => f (stAux.1.1,
                        Function.update stAux.1.1 stAux.1.2 (addCoord c t)))
            _ = avgOver (uniformDistribution (Fq params))
                  (fun x => f (stAux.1.1, Function.update stAux.1.1 stAux.1.2 x)) := by
                    apply avgOver_congr
                    intro x
                    simp [addCoordLeftEquiv]
    _ = avgOver (uniformDistribution (AxisParallelTestSample params))
          (fun s =>
            avgOver (uniformDistribution (Fq params))
              (fun x => f (s.1, Function.update s.1 s.2 x))) := by
          exact avgOver_uniform_fst
            (α := AxisParallelTestSample params) (β := Fq params)
            (fun s =>
              avgOver (uniformDistribution (Fq params))
                (fun x => f (s.1, Function.update s.1 s.2 x)))
    _ = avgOver (uniformDistribution (AxisParallelTestSample params × Fq params))
          (fun sx => f (sx.1.1, Function.update sx.1.1 sx.1.2 sx.2)) := by
          exact (avgOver_uniform_prod
            (α := AxisParallelTestSample params) (β := Fq params)
            (f := fun s x => f (s.1, Function.update s.1 s.2 x))).symm

lemma avgOver_axisParallelTestSample_update_eq_rerandomizeCoord
    (params : Parameters) [FieldModel params.q]
    (f : Point params × Point params → Error) :
    avgOver (uniformDistribution (AxisParallelTestSample params × Fq params))
      (fun sx => f (sx.1.1, Function.update sx.1.1 sx.1.2 sx.2)) =
    avgOver (rerandomizeCoord params) f := by
  rw [avgOver_rerandomizeCoord_eq_uniform_sample]
  rfl

lemma weightedGeneralizeBRightOperatorAtPolynomial_point_eq
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι)
    (g : Polynomial params)
    (ℓ : AxisParallelLine params) (u v : Point params) :
    weightedGeneralizeBRightOperatorAtPolynomial params strategy G g (ℓ, u) =
      weightedGeneralizeBRightOperatorAtPolynomial params strategy G g (ℓ, v) := by
  simp [weightedGeneralizeBRightOperatorAtPolynomial,
    generalizeBRightOperatorAtPolynomial, generalizeBRightEventSubMeasAtPolynomial]

private lemma localVarianceTransportLinePairBound
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (G : SubMeas (Polynomial params) ι)
    (g : Polynomial params) :
    avgOver (uniformDistribution (TransportQuestion params))
      (fun q =>
        let D := weightedPointConditionedOperatorAtPolynomial params strategy G g
            (q.1.1.pointAt q.1.2) -
          weightedPointConditionedOperatorAtPolynomial params strategy G g
            (q.1.1.pointAt q.2)
        ev strategy.state (Dᴴ * D)) ≤
      localVarianceTransportChainError params eps delta := by
  classical
  let A0 : TransportQuestion params → MIPStarRE.Quantum.Op (ι × ι) := fun q =>
    weightedPointConditionedOperatorAtPolynomial params strategy G g (q.1.1.pointAt q.1.2)
  let A1 : TransportQuestion params → MIPStarRE.Quantum.Op (ι × ι) := fun q =>
    weightedPointConditionedRightOperatorAtPolynomial params strategy G g (q.1.1.pointAt q.1.2)
  let A2 : TransportQuestion params → MIPStarRE.Quantum.Op (ι × ι) := fun q =>
    weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g
      (q.1.1, q.1.1.pointAt q.1.2)
  let A3 : TransportQuestion params → MIPStarRE.Quantum.Op (ι × ι) := fun q =>
    weightedGeneralizeBRightOperatorAtPolynomial params strategy G g
      (q.1.1, q.1.1.pointAt q.1.2)
  let A4 : TransportQuestion params → MIPStarRE.Quantum.Op (ι × ι) := fun q =>
    weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g
      (q.1.1, q.1.1.pointAt q.2)
  let A5 : TransportQuestion params → MIPStarRE.Quantum.Op (ι × ι) := fun q =>
    weightedPointConditionedRightOperatorAtPolynomial params strategy G g (q.1.1.pointAt q.2)
  let A6 : TransportQuestion params → MIPStarRE.Quantum.Op (ι × ι) := fun q =>
    weightedPointConditionedOperatorAtPolynomial params strategy G g (q.1.1.pointAt q.2)
  let 𝒟 := uniformDistribution (TransportQuestion params)
  have h01 : SDDOpRel strategy.state 𝒟
      (singletonOpFamily A0) (singletonOpFamily A1) (2 * delta) := by
    refine sddOpRel_singleton_of_bound strategy.state 𝒟 A0 A1 (2 * delta) ?_
    calc
      avgOver 𝒟 (fun q => ev strategy.state (((A0 q - A1 q)ᴴ) * (A0 q - A1 q)))
        = avgOver (uniformDistribution (Point params))
            (fun u =>
              let D := weightedPointConditionedOperatorAtPolynomial params strategy G g u -
                weightedPointConditionedRightOperatorAtPolynomial params strategy G g u
              ev strategy.state (Dᴴ * D)) := by
            exact avgOver_transport_leftPoint params (fun u =>
              let D := weightedPointConditionedOperatorAtPolynomial params strategy G g u -
                weightedPointConditionedRightOperatorAtPolynomial params strategy G g u
              ev strategy.state (Dᴴ * D))
      _ ≤ 2 * delta := pointConditionedEventSelfConsistency_weighted_point
        params strategy eps delta gamma hgood G g
  have h12 : SDDOpRel strategy.state 𝒟
      (singletonOpFamily A1) (singletonOpFamily A2) (2 * eps) := by
    refine sddOpRel_singleton_of_bound strategy.state 𝒟 A1 A2 (2 * eps) ?_
    calc
      avgOver 𝒟 (fun q => ev strategy.state (((A1 q - A2 q)ᴴ) * (A1 q - A2 q)))
        = avgOver (axisParallelLineQuestionDistribution params)
            (fun qu =>
              let D := weightedPointConditionedRightOperatorAtPolynomial
                  params strategy G g qu.2 -
                weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu
              ev strategy.state (Dᴴ * D)) := by
            exact avgOver_transport_leftQuestion params (fun qu =>
              let D := weightedPointConditionedRightOperatorAtPolynomial
                  params strategy G g qu.2 -
                weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu
              ev strategy.state (Dᴴ * D))
      _ ≤ 2 * eps := axisParallelPointLineConsistency_weighted_rightToLeftLineQuestion
        params strategy eps delta gamma hgood G g
  have h23 : SDDOpRel strategy.state 𝒟
      (singletonOpFamily A2) (singletonOpFamily A3) (generalizeBError params) := by
    refine sddOpRel_singleton_of_bound strategy.state 𝒟 A2 A3 (generalizeBError params) ?_
    calc
      avgOver 𝒟 (fun q => ev strategy.state (((A2 q - A3 q)ᴴ) * (A2 q - A3 q)))
        = avgOver (axisParallelLineQuestionDistribution params)
            (fun qu =>
              let D := weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu -
                weightedGeneralizeBRightOperatorAtPolynomial params strategy G g qu
              ev strategy.state (Dᴴ * D)) := by
            exact avgOver_transport_leftQuestion params (fun qu =>
              let D := weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu -
                weightedGeneralizeBRightOperatorAtPolynomial params strategy G g qu
              ev strategy.state (Dᴴ * D))
      _ ≤ generalizeBError params := by
            simpa [generalizeBDeviationAtPolynomial] using
              generalizeBPointwiseSchwartzZippel params strategy G g
  have h34 : SDDOpRel strategy.state 𝒟
      (singletonOpFamily A3) (singletonOpFamily A4) (generalizeBError params) := by
    refine sddOpRel_singleton_of_bound strategy.state 𝒟 A3 A4 (generalizeBError params) ?_
    calc
      avgOver 𝒟 (fun q => ev strategy.state (((A3 q - A4 q)ᴴ) * (A3 q - A4 q)))
        = avgOver 𝒟
            (fun q =>
              let D := weightedGeneralizeBRightOperatorAtPolynomial params strategy G g
                  (q.1.1, q.1.1.pointAt q.2) -
                weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g
                  (q.1.1, q.1.1.pointAt q.2)
              ev strategy.state (Dᴴ * D)) := by
            apply avgOver_congr
            intro q
            dsimp [A3, A4]
            rw [weightedGeneralizeBRightOperatorAtPolynomial_point_eq
              params strategy G g q.1.1 (q.1.1.pointAt q.1.2) (q.1.1.pointAt q.2)]
      _ = avgOver (axisParallelLineQuestionDistribution params)
            (fun qu =>
              let D := weightedGeneralizeBRightOperatorAtPolynomial params strategy G g qu -
                weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu
              ev strategy.state (Dᴴ * D)) := by
            exact avgOver_transport_rightQuestion params (fun qu =>
              let D := weightedGeneralizeBRightOperatorAtPolynomial params strategy G g qu -
                weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu
              ev strategy.state (Dᴴ * D))
      _ ≤ generalizeBError params := by
            exact generalizeBReversePointwiseBound params strategy strategy.state G
              (generalizeBFromSchwartzZippel params strategy eps delta gamma hgood G) g
  have h45 : SDDOpRel strategy.state 𝒟
      (singletonOpFamily A4) (singletonOpFamily A5) (2 * eps) := by
    refine sddOpRel_singleton_of_bound strategy.state 𝒟 A4 A5 (2 * eps) ?_
    calc
      avgOver 𝒟 (fun q => ev strategy.state (((A4 q - A5 q)ᴴ) * (A4 q - A5 q)))
        = avgOver (axisParallelLineQuestionDistribution params)
            (fun qu =>
              let D := weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu -
                weightedPointConditionedRightOperatorAtPolynomial params strategy G g qu.2
              ev strategy.state (Dᴴ * D)) := by
            exact avgOver_transport_rightQuestion params (fun qu =>
              let D := weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu -
                weightedPointConditionedRightOperatorAtPolynomial params strategy G g qu.2
              ev strategy.state (Dᴴ * D))
      _ ≤ 2 * eps := axisParallelPointLineConsistency_weighted_leftToRightLineQuestion
        params strategy eps delta gamma hgood G g
  have h56 : SDDOpRel strategy.state 𝒟
      (singletonOpFamily A5) (singletonOpFamily A6) (2 * delta) := by
    refine sddOpRel_singleton_of_bound strategy.state 𝒟 A5 A6 (2 * delta) ?_
    calc
      avgOver 𝒟 (fun q => ev strategy.state (((A5 q - A6 q)ᴴ) * (A5 q - A6 q)))
        = avgOver 𝒟 (fun q => ev strategy.state (((A6 q - A5 q)ᴴ) * (A6 q - A5 q))) := by
            apply avgOver_congr
            intro q
            exact ev_adjoint_sub_swap strategy.state (A6 q) (A5 q)
      _ = avgOver (uniformDistribution (Point params))
            (fun u =>
              let D := weightedPointConditionedOperatorAtPolynomial params strategy G g u -
                weightedPointConditionedRightOperatorAtPolynomial params strategy G g u
              ev strategy.state (Dᴴ * D)) := by
            exact avgOver_transport_rightPoint params (fun u =>
              let D := weightedPointConditionedOperatorAtPolynomial params strategy G g u -
                weightedPointConditionedRightOperatorAtPolynomial params strategy G g u
              ev strategy.state (Dᴴ * D))
      _ ≤ 2 * delta := pointConditionedEventSelfConsistency_weighted_point
        params strategy eps delta gamma hgood G g
  let families : Fin 7 → IdxOpFamily (TransportQuestion params) Unit (ι × ι) := fun i =>
    if i = 0 then singletonOpFamily A0
    else if i = 1 then singletonOpFamily A1
    else if i = 2 then singletonOpFamily A2
    else if i = 3 then singletonOpFamily A3
    else if i = 4 then singletonOpFamily A4
    else if i = 5 then singletonOpFamily A5
    else singletonOpFamily A6
  let errors : Fin 6 → Error := fun i =>
    if i = 0 then 2 * delta
    else if i = 1 then 2 * eps
    else if i = 2 then generalizeBError params
    else if i = 3 then generalizeBError params
    else if i = 4 then 2 * eps
    else 2 * delta
  have hsteps : ∀ i : Fin 6,
      SDDOpRel strategy.state 𝒟 (families i.castSucc) (families i.succ)
        (errors i) := by
    intro i
    fin_cases i <;> simp [families, errors, h01, h12, h23, h34, h45, h56]
  have hchain := sddOpRel_chain strategy.state 𝒟 6 families errors hsteps
  have hsum :
      (∑ i : Fin 6, errors i) =
        4 * eps + 4 * delta + 2 * generalizeBError params := by
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ,
      Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_one]
    simp [errors]
    ring
  have hbound :
      sddErrorOp strategy.state 𝒟 (singletonOpFamily A0) (singletonOpFamily A6) ≤
        localVarianceTransportChainError params eps delta := by
    calc
      sddErrorOp strategy.state 𝒟 (singletonOpFamily A0) (singletonOpFamily A6)
        = sddErrorOp strategy.state 𝒟 (families 0) (families (Fin.last 6)) := by
            simp [families]
      _ ≤ (6 : Error) * ∑ i : Fin 6, errors i := hchain.squaredDistanceBound
      _ = localVarianceTransportChainError params eps delta := by
            rw [hsum]
            simp [localVarianceTransportChainError]
  simpa [sddErrorOp, qSDDOp, qSDDCore, singletonOpFamily, A0, A6, 𝒟] using hbound

/-- The paper's six-step edge transport estimate in the native
`rerandomizeCoord` presentation.

The triangle chain is proved on the line-pair presentation above; this theorem
reindexes that presentation back to the hypercube-edge sampler
`u, i, x ↦ (u, u[i ↦ x])`, which is exactly `rerandomizeCoord`. -/
lemma localVarianceTransportChainBound
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (G : SubMeas (Polynomial params) ι)
    (g : Polynomial params) :
    localVarianceDeviationAtPolynomial params strategy strategy.state G g ≤
      localVarianceTransportChainError params eps delta := by
  let f : Point params × Point params → Error := fun uv =>
    let D := weightedPointConditionedOperatorAtPolynomial params strategy G g uv.1 -
      weightedPointConditionedOperatorAtPolynomial params strategy G g uv.2
    ev strategy.state (Dᴴ * D)
  change avgOver (rerandomizeCoord params) f ≤
    localVarianceTransportChainError params eps delta
  rw [← avgOver_axisParallelTestSample_update_eq_rerandomizeCoord params f]
  rw [← avgOver_transport_pointPair params f]
  exact localVarianceTransportLinePairBound params strategy eps delta gamma hgood G g

/-- The post-triangle six-step transport error is absorbed by the paper's
`24(ε + δ + md/q)` slack from `lem:local-variance-of-points`.

This is only the scalar arithmetic after applying
`prop:triangle-inequality-for-approx_delta` with `k = 6` to the estimates at
`references/ldt-paper/expansion.tex`, lines 305--311; it does not assert the
transport estimates themselves. -/
lemma localVarianceTransportChainError_le_localVarianceOfPointsError
    (params : Parameters)
    [FieldModel params.q]
    {eps delta gamma : Error}
    (strategy : SymStrat params ι)
    (hgood : strategy.IsGood eps delta gamma) :
    localVarianceTransportChainError params eps delta ≤
      localVarianceOfPointsError params eps delta := by
  have heps_nonneg := eps_nonneg_of_isGood params strategy hgood
  have hdelta_nonneg := delta_nonneg_of_isGood params strategy hgood
  have hgen_nonneg : 0 ≤ generalizeBError params := by
    dsimp [generalizeBError]
    positivity
  dsimp [localVarianceTransportChainError, localVarianceOfPointsError]
  linarith

end

end MIPStarRE.LDT.GlobalVariance

end LIDT


