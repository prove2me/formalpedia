-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_SelfConsistencyTransport_Utilities
-- name    : LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_SelfConsistencyTransport_Utilities
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T12:00:49.206176+00:00
-- url     : https://prove2.me/theorems/bac75af9-a14c-43e2-a82d-28175302db60
-- title:
--   LIDT definitions: LDT / GlobalVariance / Theorems / SelfConsistencyTransport / Utilities
-- statement:
--   This bundle collects the local algebra and contraction estimates that transport self-consistency through the global-variance argument. It provides adjoint rearrangements, option-indexed distance bounds, square-root weight contractions, and a shared approximate error-sum estimate.
--
--   Principal definitions:
--   - `ev_adjoint_sub_swap`: an expectation identity for swapping an adjoint across a subtraction.
--   - `qSDDCore_optionUnit_some_le`: the selected `some ()` contribution bounded by the full option-unit squared-distance core.
--   - `generalizeBReversePointwiseBound`: the reverse pointwise estimate used in the generalize-b step.
--   - `rightPolynomialWeightSqrt_contraction`: contraction of the right-tensor square root of a polynomial weight.
--   - `rightPolynomialWeightSqrt_grouped_contraction`: the grouped contraction after collecting outcomes with the same evaluation value.
--   - `cabApproxDelta_sum_from_sdd`: the polynomial-sum approximate-error bound obtained from state-dependent distance.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/GlobalVariance/Theorems/SelfConsistencyTransport/Utilities.lean#L32-L331

-- Generated from MIPStarRE/LDT/GlobalVariance/Theorems/SelfConsistencyTransport/Utilities.lean by skeleton subtraction.
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

/-! # Sampling and operator-symmetry utilities

Support lemmas for the good-strategy self-consistency transport
(`SelfConsistencyTransport`):

* `ev_adjoint_sub_swap` — squared-distance invariance under swapping endpoints
  (used by the reverse `generalize-b` step and by
  `pointConditionedEventSelfConsistency_weighted_rightEdge`);
* `generalizeBReversePointwiseBound` — the reverse `lem:generalize-b` step at
  `expansion.tex:309`;
* `avgOver_rerandomizeCoord_fst` / `avgOver_rerandomizeCoord_snd` — both
  marginals of the hypercube-edge sampling distribution are uniform
  (`expansion.tex:300–302`).
-/

namespace MIPStarRE.LDT.GlobalVariance

open MIPStarRE.LDT
open MIPStarRE.LDT.Preliminaries
open MIPStarRE.LDT.MakingMeasurementsProjective
open MIPStarRE.LDT.ExpansionHypercubeGraph
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

@[expose] public section

lemma ev_adjoint_sub_swap
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (ψ : QuantumState κ) (X Y : MIPStarRE.Quantum.Op κ) :
    ev ψ (((Y - X)ᴴ) * (Y - X)) =
      ev ψ (((X - Y)ᴴ) * (X - Y)) := by
  have hdiff : Y - X = -(X - Y) := by
    simp
  have hconjDiff : Yᴴ - Xᴴ = -(Xᴴ - Yᴴ) := by
    abel
  have hsqExpanded : (Yᴴ - Xᴴ) * (Y - X) = (Xᴴ - Yᴴ) * (X - Y) := by
    calc
      (Yᴴ - Xᴴ) * (Y - X) = (-(Xᴴ - Yᴴ)) * (Y - X) := by
        rw [hconjDiff]
      _ = (-(Xᴴ - Yᴴ)) * (-(X - Y)) := by rw [hdiff]
      _ = (Xᴴ - Yᴴ) * (X - Y) := by
        rw [neg_mul, mul_neg, neg_neg]
  calc
    ev ψ (((Y - X)ᴴ) * (Y - X)) = ev ψ ((Yᴴ - Xᴴ) * (Y - X)) := by
      simp
    _ = ev ψ ((Xᴴ - Yᴴ) * (X - Y)) := by
      exact congrArg (ev ψ) hsqExpanded
    _ = ev ψ (((X - Y)ᴴ) * (X - Y)) := by
      simp

/-- The selected `some ()` contribution is bounded by the full `Option Unit`
summed squared-distance core.

This extracts the common monotonicity step used when a two-outcome
postprocessed event is passed to `cabApproxDelta`: the singleton selected
outcome is one summand of the full `Option Unit` sum defining `qSDDCore`. -/
lemma qSDDCore_optionUnit_some_le
    {α κ : Type*} [Fintype κ] [DecidableEq κ]
    (ψ : QuantumState κ) (𝒟 : Distribution α)
    (A B : α → Option Unit → MIPStarRE.Quantum.Op κ) :
    avgOver 𝒟
        (fun x =>
          qSDDCore ψ
            (fun _ : Unit => A x (some ()))
            (fun _ : Unit => B x (some ()))) ≤
      avgOver 𝒟 (fun x => qSDDCore ψ (A x) (B x)) := by
  refine avgOver_mono _ _ _ ?_
  intro x
  unfold qSDDCore
  simpa using
    (Finset.single_le_sum
      (fun a _ => ev_adjoint_self_nonneg ψ (A x a - B x a))
      (Finset.mem_univ (some ())))

/-- The reverse `lem:generalize-b` step used at
`references/ldt-paper/expansion.tex`, line 309.

The paper first moves from the evaluated line event to the exact restriction
(line 308), then uses the same estimate in the reverse direction at the second
sampled point (line 309).  The squared-distance expression is unchanged by
swapping the two endpoints, because `(Y - X) = -(X - Y)`. -/
lemma generalizeBReversePointwiseBound
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (ψbi : QuantumState (ι × ι))
    (G : SubMeas (Polynomial params) ι)
    (hgen : GeneralizeBStatement params strategy ψbi G)
    (g : Polynomial params) :
    avgOver (axisParallelLineQuestionDistribution params)
      (fun qu =>
        let D := weightedGeneralizeBRightOperatorAtPolynomial params strategy G g qu -
          weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu
        ev ψbi (Dᴴ * D)) ≤ generalizeBError params := by
  calc
    avgOver (axisParallelLineQuestionDistribution params)
        (fun qu =>
          let D := weightedGeneralizeBRightOperatorAtPolynomial params strategy G g qu -
            weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu
          ev ψbi (Dᴴ * D))
      = generalizeBDeviationAtPolynomial params strategy ψbi G g := by
          unfold generalizeBDeviationAtPolynomial
          apply avgOver_congr
          intro qu
          dsimp only
          let X := weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu
          let Y := weightedGeneralizeBRightOperatorAtPolynomial params strategy G g qu
          exact ev_adjoint_sub_swap ψbi X Y
    _ ≤ generalizeBError params := hgen.pointwiseNormBound g





/-- The right tensor of the square-root polynomial weight is a contraction.

The square of `(G_g)^{1/2}` is the submeasurement outcome `G_g`, and every
outcome of a submeasurement is bounded by the identity. -/
lemma rightPolynomialWeightSqrt_contraction
    (params : Parameters)
    [FieldModel params.q]
    (G : SubMeas (Polynomial params) ι) (g : Polynomial params) :
    (rightTensor (ι₁ := ι) (polynomialWeightSqrtOperator params G g))ᴴ *
        rightTensor (ι₁ := ι) (polynomialWeightSqrtOperator params G g) ≤
      1 := by
  let S : MIPStarRE.Quantum.Op ι := polynomialWeightSqrtOperator params G g
  have hct : (rightTensor (ι₁ := ι) S)ᴴ = rightTensor (ι₁ := ι) Sᴴ := by
    simp
  calc
    (rightTensor (ι₁ := ι) S)ᴴ * rightTensor (ι₁ := ι) S =
        rightTensor (ι₁ := ι) (Sᴴ * S) := by
          rw [hct, rightTensor_mul_rightTensor]
    _ = rightTensor (ι₁ := ι) (G.outcome g) := by
          rw [show Sᴴ = S by simpa [S] using
            polynomialWeightSqrtOperator_conjTranspose (params := params) G g]
          rw [show S * S = G.outcome g by simpa [S] using
            polynomialWeightSqrtOperator_mul_self (params := params) G g]
    _ ≤ 1 := rightTensor_le_one (ι₁ := ι) (G.outcome_le_one g)

/-- Grouped-by-evaluation-value submeasurement contraction for `(G_g)^{1/2}`.

For a fixed point `u` and a field element `a`, sum over all polynomials `g`
with `g(u) = a` of the `rightTensor` of `(G_g)^{1/2} * (G_g)^{1/2}ᴴ`.
The contraction `∑_{g : g(u)=a} G_g ≤ I` follows from the submeasurement
inequality `G.total ≤ I`.  This is the key algebraic input that allows the
`cabApproxDelta` multiplier family in `cabApproxDelta_sum_from_sdd` and the
sum-form `2ε` endpoints to group polynomials by their evaluation value without
incurring a cardinality factor. -/
lemma rightPolynomialWeightSqrt_grouped_contraction
    (params : Parameters)
    [FieldModel params.q]
    (G : SubMeas (Polynomial params) ι)
    (u : Point params) (a : Fq params) :
    ∑ g : Polynomial params,
        (if a = g u then rightTensor (ι₁ := ι) (polynomialWeightSqrtOperator params G g)
          else 0)ᴴ *
          (if a = g u then rightTensor (ι₁ := ι) (polynomialWeightSqrtOperator params G g)
            else 0) ≤ 1 := by
  classical
  let fiber : Finset (Polynomial params) := Finset.univ.filter fun g => a = g u
  have hfiber_le_total :
      ∑ g ∈ fiber, G.outcome g ≤ G.total := by
    calc
      ∑ g ∈ fiber, G.outcome g ≤ ∑ g : Polynomial params, G.outcome g := by
        exact Finset.sum_le_sum_of_subset_of_nonneg
          (by
            intro g hg
            exact Finset.mem_univ g)
          (by
            intro g _ _hg
            exact G.outcome_pos g)
      _ = G.total := G.sum_eq_total
  calc
    ∑ g : Polynomial params,
        (if a = g u then rightTensor (ι₁ := ι) (polynomialWeightSqrtOperator params G g)
          else 0)ᴴ *
          (if a = g u then rightTensor (ι₁ := ι) (polynomialWeightSqrtOperator params G g)
            else 0)
      = ∑ g ∈ fiber, rightTensor (ι₁ := ι) (G.outcome g) := by
          dsimp [fiber]
          rw [Finset.sum_filter]
          refine Finset.sum_congr rfl ?_
          intro g _
          by_cases hg : a = g u
          · simp [hg, polynomialWeightSqrtOperator_conjTranspose,
              polynomialWeightSqrtOperator_mul_self, rightTensor_mul_rightTensor]
          · simp [hg]
    _ = rightTensor (ι₁ := ι) (∑ g ∈ fiber, G.outcome g) := by
          rw [rightTensor_finset_sum]
    _ ≤ 1 := rightTensor_le_one (ι₁ := ι) (le_trans hfiber_le_total G.total_le_one)

/-- Shared polynomial-sum `cabApproxDelta` transport.

The argument keeps the answer space at `Fq params`, applies
`prop:cab-approx-delta` with multiplier
`if a = g(base s) then I ⊗ (G_g)^{1/2} else 0`, and uses the grouped
contraction `rightPolynomialWeightSqrt_grouped_contraction`.  The bridge
hypotheses identify the surviving fiber `a = g(base s)` with the weighted
left and right operators desired by the caller. -/
lemma cabApproxDelta_sum_from_sdd
    {Sample : Type*}
    (params : Parameters)
    [FieldModel params.q]
    (ψ : QuantumState (ι × ι))
    (𝒟 : Distribution Sample)
    (base : Sample → Point params)
    (left right : Sample → Fq params → MIPStarRE.Quantum.Op (ι × ι))
    (L R : Sample → Polynomial params → MIPStarRE.Quantum.Op (ι × ι))
    (G : SubMeas (Polynomial params) ι)
    (η : Error)
    (hbase : avgOver 𝒟 (fun s => qSDDCore ψ (left s) (right s)) ≤ η)
    (hleft : ∀ s g,
      rightTensor (ι₁ := ι) (polynomialWeightSqrtOperator params G g) *
          left s (g (base s)) =
        L s g)
    (hright : ∀ s g,
      rightTensor (ι₁ := ι) (polynomialWeightSqrtOperator params G g) *
          right s (g (base s)) =
        R s g) :
    (∑ g : Polynomial params,
      avgOver 𝒟 (fun s => ev ψ (((L s g - R s g)ᴴ) * (L s g - R s g)))) ≤
      η := by
  classical
  let C : Sample → Fq params → Polynomial params → MIPStarRE.Quantum.Op (ι × ι) :=
    fun s a g =>
      if a = g (base s) then rightTensor (ι₁ := ι) (polynomialWeightSqrtOperator params G g)
      else 0
  have hC :
      ∀ s a, ∑ g : Polynomial params, (C s a g)ᴴ * C s a g ≤ 1 := by
    intro s a
    simpa [C] using rightPolynomialWeightSqrt_grouped_contraction params G (base s) a
  have hcab := cabApproxDelta ψ 𝒟 left right C η hbase hC
  calc
    (∑ g : Polynomial params,
      avgOver 𝒟 (fun s => ev ψ (((L s g - R s g)ᴴ) * (L s g - R s g))))
      = avgOver 𝒟
          (fun s =>
            qSDDCore ψ
              (fun ag : Fq params × Polynomial params => C s ag.1 ag.2 * left s ag.1)
              (fun ag : Fq params × Polynomial params => C s ag.1 ag.2 * right s ag.1)) := by
          rw [← avgOver_sum]
          apply avgOver_congr
          intro s
          unfold qSDDCore
          rw [Fintype.sum_prod_type]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro g _
          symm
          let term : Fq params → Error := fun x =>
            ev ψ ((((C s x g * left s x) - (C s x g * right s x))ᴴ) *
              ((C s x g * left s x) - (C s x g * right s x)))
          change (∑ x : Fq params, term x) =
            ev ψ (((L s g - R s g)ᴴ) * (L s g - R s g))
          calc
            (∑ x : Fq params, term x) = term (g (base s)) := by
              refine Finset.sum_eq_single (s := (Finset.univ : Finset (Fq params)))
                (a := g (base s)) ?_ ?_
              · intro x _ hx
                simpa [term, C, hx] using ev_zero ψ
              · intro hmissing
                exact False.elim (hmissing (Finset.mem_univ (g (base s))))
            _ = ev ψ (((L s g - R s g)ᴴ) * (L s g - R s g)) := by
              let S : MIPStarRE.Quantum.Op ι := polynomialWeightSqrtOperator params G g
              let X := L s g
              let Y := R s g
              calc
                term (g (base s)) =
                    ev ψ
                      (((rightTensor (ι₁ := ι) S * left s (g (base s)) -
                          rightTensor (ι₁ := ι) S * right s (g (base s)))ᴴ) *
                        (rightTensor (ι₁ := ι) S * left s (g (base s)) -
                          rightTensor (ι₁ := ι) S * right s (g (base s)))) := by
                        simp [term, C, S]
                _ = ev ψ (((X - Y)ᴴ) * (X - Y)) := by
                    rw [hleft s g, hright s g]
    _ ≤ η := hcab

end

end MIPStarRE.LDT.GlobalVariance

end LIDT


