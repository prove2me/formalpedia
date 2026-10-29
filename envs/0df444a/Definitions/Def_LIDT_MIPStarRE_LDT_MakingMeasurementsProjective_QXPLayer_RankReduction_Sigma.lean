-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayer_RankReduction_Sigma
-- name    : LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayer_RankReduction_Sigma
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T12:00:24.831628+00:00
-- url     : https://prove2.me/theorems/e691ec11-e754-47d9-8056-8e70610569f4
-- title:
--   LIDT definitions: LDT / MakingMeasurementsProjective / QXPLayer / RankReduction / Sigma
-- statement:
--   This bundle constructs the finite carrier and auxiliary matrix data used by rank reduction in the QXP layer. It represents the dependent sum carrier by finite enumerations, builds block projective measurements, and embeds the resulting range into matrices.
--
--   Principal definitions:
--   - `sigmaFinCarrier`: a finite-enumeration model of the dependent-sum carrier `Sigma a, Fin (m a)`.
--   - `sigmaFinLift`: the lifted carrier used as the auxiliary basis for `sigmaFin`.
--   - `sigmaFin`: the finite Hilbert space built from the lifted auxiliary carrier.
--   - `sigmaRangeCarrier`: the lifted carrier for the ranks of an operator family.
--   - `sigmaFinCarrierEquiv`: the equivalence between the finite-enumeration carrier and the literal dependent sum.
--   - `finSigmaProjMeas`: the canonical block projective measurement indexed by a finite rank parameter.
--   - `sigmaFinProjMeas`: the block projective measurement selecting an `a`-indexed block.
--   - `sigmaFinRangeEmbedding`: the matrix embedding associated with a projective family on the auxiliary space.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/MakingMeasurementsProjective/QXPLayer/RankReduction/Sigma.lean#L52-L715

-- Generated from MIPStarRE/LDT/MakingMeasurementsProjective/QXPLayer/RankReduction/Sigma.lean by skeleton subtraction.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Projectivization
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayer_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayer_TruncationCombinatorics
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Statements
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Completion
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Local
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_CauchySchwarz
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_ComparisonCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_CompletionTransfer
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_DistanceBounds
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichMain_Completeness
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_ApproxDelta
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_InnerProduct
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_QuantumNonneg
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_Defs
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
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad

open scoped _root_.Matrix

namespace LIDT

namespace MIPStarRE.LDT.Preliminaries
end MIPStarRE.LDT.Preliminaries

/-!
# Section 5 — Q/X/XHat/P rank reduction

Sigma-space projectors and rank-reduction lemmas for the paper's `Q/X/XHat/P`
intermediate layer.
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

namespace MIPStarRE.LDT.MakingMeasurementsProjective

open MIPStarRE.LDT

noncomputable section

universe uOutcome uι



/-- If a family of projectors sums to at most `c • I`, then the sum of their
ranks is at most `c` times the ambient dimension. -/
lemma sum_rank_le_scalar_mul_card_of_projectors_le {Outcome : Type*} [Fintype Outcome]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : Outcome → MIPStarRE.Quantum.Op ι)
    (hproj : ∀ a, MIPStarRE.Quantum.IsProj (R a))
    (c : Error)
    (htotal_le : (∑ a, R a) ≤ ((c : ℂ) • (1 : MIPStarRE.Quantum.Op ι))) :
    ((∑ a, (R a).rank : ℕ) : Error) ≤ c * Fintype.card ι := by
  have hpsd : (((c : ℂ) • (1 : MIPStarRE.Quantum.Op ι)) - ∑ a, R a).PosSemidef :=
    (Matrix.le_iff).mp htotal_le
  have htrace_nonneg : (0 : ℂ) ≤ (((c : ℂ) • (1 : MIPStarRE.Quantum.Op ι)) -
      ∑ a, R a).trace := hpsd.trace_nonneg
  have hreal_nonneg : 0 ≤ Complex.re ((((c : ℂ) • (1 : MIPStarRE.Quantum.Op ι)) -
      ∑ a, R a).trace) := (Complex.nonneg_iff.mp htrace_nonneg).1
  have htrace_rank : (∑ a, Complex.re (Matrix.trace (R a))) = ∑ a, ((R a).rank : ℝ) := by
    refine Finset.sum_congr rfl ?_
    intro a _
    rw [MIPStarRE.Quantum.IsProj.trace_eq_rank (R a) (hproj a)]
    simp
  have hreal_bound' : ∑ a, Complex.re (Matrix.trace (R a)) ≤ c * Fintype.card ι := by
    have hbound : ∑ a, Complex.re (Matrix.trace (R a)) ≤
        Complex.re (Matrix.trace ((c : ℂ) • (1 : MIPStarRE.Quantum.Op ι))) := by
      simpa [Matrix.trace_sub, Matrix.trace_sum] using hreal_nonneg
    have htrace_one :
        Complex.re (Matrix.trace ((c : ℂ) • (1 : MIPStarRE.Quantum.Op ι))) =
          c * Fintype.card ι := by
      rw [Matrix.trace_smul, Matrix.trace_one]
      simp
    exact hbound.trans_eq htrace_one
  simpa [htrace_rank] using hreal_bound'

namespace FiniteHilbertSpace

/-- A chosen finite-enumeration model of the paper's carrier `Σ a, Fin (m a)`.
Using `Fin (Fintype.card Outcome)` keeps the base carrier in a small universe;
`sigmaFin` then lifts it to the requested auxiliary-space universe with `ULift`. -/
noncomputable abbrev sigmaFinCarrier {Outcome : Type*} [Fintype Outcome]
    (m : Outcome → ℕ) :=
  Σ i : Fin (Fintype.card Outcome), Fin (m ((Fintype.equivFin Outcome).symm i))

/-- The lifted sigma carrier used as the auxiliary Hilbert-space basis for
`sigmaFin`. -/
noncomputable abbrev sigmaFinLift {Outcome : Type*} [Fintype Outcome]
    (m : Outcome → ℕ) : Type uι :=
  ULift.{uι} (sigmaFinCarrier m)

/-- The finite Hilbert space whose preferred basis is a lifted finite-enumeration
model of `Σ a, Fin (m a)`. -/
def sigmaFin {Outcome : Type*} [Fintype Outcome]
    (m : Outcome → ℕ) [Nonempty (sigmaFinCarrier m)] :
    FiniteHilbertSpace.{uι} where
  carrier := sigmaFinLift m
  instFintype := inferInstance
  instDecidableEq := inferInstance
  instNonempty := inferInstance

end FiniteHilbertSpace

/-- The lifted sigma carrier associated to the ranks of an operator family. -/
noncomputable abbrev sigmaRangeCarrier
    {Outcome : Type uOutcome} [Fintype Outcome]
    {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (q : OpFamily Outcome ι) : Type uι :=
  FiniteHilbertSpace.sigmaFinLift (fun a : Outcome => (q.outcome a).rank)

/-- A finite-enumeration carrier is equivalent to the paper's literal sigma type
`Σ a, Fin (m a)`. -/
private noncomputable def sigmaFinCarrierEquiv {Outcome : Type*} [Fintype Outcome]
    (m : Outcome → ℕ) :
    (Σ a : Outcome, Fin (m a)) ≃ FiniteHilbertSpace.sigmaFinCarrier m := by
  classical
  let e : Outcome ≃ Fin (Fintype.card Outcome) := Fintype.equivFin Outcome
  refine
    { toFun := fun x => ⟨e x.1, by simpa [e] using x.2⟩
      invFun := fun x => ⟨e.symm x.1, by simpa [e] using x.2⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro x
    ext <;> simp [e]
  · intro x
    ext <;> simp [e]

/-- The canonical block projective measurement on the lifted sigma carrier
indexed by `Fin n`. -/
noncomputable def finSigmaProjMeas (n : ℕ) (m : Fin n → ℕ) :
    ProjMeas (Fin n) (ULift.{uι} (Σ i : Fin n, Fin (m i))) where
  outcome := fun i =>
    Matrix.diagonal fun x : ULift.{uι} (Σ i : Fin n, Fin (m i)) => if x.down.1 = i then 1 else 0
  total := 1
  outcome_pos := fun i =>
    Matrix.nonneg_iff_posSemidef.mpr <| Matrix.PosSemidef.diagonal fun x => by
      by_cases hx : x.down.1 = i <;> simp [hx]
  sum_eq_total := Matrix.ext fun x y => by
    rw [Matrix.sum_apply]
    by_cases hxy : x = y
    · subst hxy
      simp [eq_comm]
    · simp [hxy]
  total_le_one := le_rfl
  total_eq_one := rfl
  proj := fun i => by
    rw [Matrix.diagonal_mul_diagonal]
    ext x y
    by_cases hxy : x = y
    · subst hxy
      by_cases hx : x.down.1 = i <;> simp [hx]
    · simp [hxy]

/-- The block projective measurement on the lifted finite-enumeration model of
`Σ a, Fin (m a)` selecting the `a`-block. -/
noncomputable def sigmaFinProjMeas {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (m : Outcome → ℕ) :
    ProjMeas Outcome (FiniteHilbertSpace.sigmaFinLift m) :=
  ProjMeas.transport (Fintype.equivFin Outcome).symm
    (finSigmaProjMeas (n := Fintype.card Outcome)
      (m := fun i => m ((Fintype.equivFin Outcome).symm i)))

/-- The matrix `X` associated to a projective family on the sigma auxiliary
space.

Rows are indexed by the finite model of `Σ a, Fin (rank Q_a)`.  The row
corresponding to `(a,i)` is the bra vector `⟨v_{a,i}|`, where
`v_{a,i}` is the `i`th vector in the chosen orthonormal basis of the range of
`Q_a`.  This is the Lean form of
`X = Σ_a Σ_i |a,i⟩⟨v_{a,i}|` in the paper. -/
noncomputable def sigmaFinRangeEmbedding {Outcome : Type uOutcome}
    [Fintype Outcome] [DecidableEq Outcome]
    {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (Q : Outcome → MIPStarRE.Quantum.Op ι)
    (hproj : ∀ a : Outcome, MIPStarRE.Quantum.IsProj (Q a)) :
    Matrix (ULift.{uι}
      (FiniteHilbertSpace.sigmaFinCarrier (fun a : Outcome => (Q a).rank))) ι ℂ :=
  fun x j =>
    let a : Outcome := (Fintype.equivFin Outcome).symm x.down.1
    star ((MIPStarRE.Quantum.IsProj.rangeONB (Q a) (hproj a)).vec x.down.2 j)







/-- The finite-enumeration range embedding realizes each projector as
`Q_a = X† T_a X`.

This is the universe-stable form of `sigmaRangeEmbedding_qa_eq`, with the same
sigma basis encoded by `FiniteHilbertSpace.sigmaFinCarrier`. -/
lemma sigmaFinRangeEmbedding_qa_eq {Outcome : Type uOutcome}
    [Fintype Outcome] [DecidableEq Outcome]
    {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (Q : Outcome → MIPStarRE.Quantum.Op ι)
    (hproj : ∀ a : Outcome, MIPStarRE.Quantum.IsProj (Q a))
    (a : Outcome) :
    let X := sigmaFinRangeEmbedding Q hproj
    let T := sigmaFinProjMeas (fun a : Outcome => (Q a).rank)
    Q a = Xᴴ * T.outcome a * X := by
  classical
  let onb : (b : Outcome) →
      MIPStarRE.Quantum.ProjectorRangeONB (Q b) (hproj b) :=
    fun b => MIPStarRE.Quantum.IsProj.rangeONB (Q b) (hproj b)
  ext i j
  have hdecomp :
      (Q a) i j =
        ∑ k : Fin (Q a).rank,
          (onb a).vec k i * star ((onb a).vec k j) := by
    simpa [onb, Matrix.sum_apply, Matrix.vecMulVec_apply] using
      congrFun (congrFun (onb a).decomposition i) j
  rw [hdecomp]
  let S := FiniteHilbertSpace.sigmaFinCarrier (fun a : Outcome => (Q a).rank)
  let e : Outcome ≃ Fin (Fintype.card Outcome) := Fintype.equivFin Outcome
  have hsum :
      (∑ x : ULift.{uι} S,
        if x.down.1 = e a then
          (onb (e.symm x.down.1)).vec x.down.2 i *
            star ((onb (e.symm x.down.1)).vec x.down.2 j)
        else 0) =
        ∑ k : Fin (Q a).rank,
          (onb a).vec k i * star ((onb a).vec k j) := by
    calc
      (∑ x : ULift.{uι} S,
        if x.down.1 = e a then
          (onb (e.symm x.down.1)).vec x.down.2 i *
            star ((onb (e.symm x.down.1)).vec x.down.2 j)
        else 0)
          = ∑ x : S,
              if x.1 = e a then
                (onb (e.symm x.1)).vec x.2 i *
                  star ((onb (e.symm x.1)).vec x.2 j)
              else 0 := by
              exact
                Equiv.sum_comp (Equiv.ulift : ULift.{uι} S ≃ S)
                  (fun x : S =>
                    if x.1 = e a then
                      (onb (e.symm x.1)).vec x.2 i *
                        star ((onb (e.symm x.1)).vec x.2 j)
                    else 0)
      _ = ∑ k : Fin (Q a).rank,
          (onb a).vec k i * star ((onb a).vec k j) := by
          suffices
              (∑ k : Fin (Q (e.symm (e a))).rank,
                (onb (e.symm (e a))).vec k i *
                  star ((onb (e.symm (e a))).vec k j)) =
              ∑ k : Fin (Q a).rank,
                (onb a).vec k i * star ((onb a).vec k j) by
            simpa [S, FiniteHilbertSpace.sigmaFinCarrier, Fintype.sum_sigma] using this
          let F : Outcome → ℂ := fun b =>
            ∑ k : Fin (Q b).rank, (onb b).vec k i * star ((onb b).vec k j)
          change F (e.symm (e a)) = F a
          exact congrArg F (e.symm_apply_apply a)
  simpa [onb, sigmaFinRangeEmbedding, sigmaFinProjMeas, finSigmaProjMeas,
    ProjMeas.transport, Measurement.transport, SubMeas.transport, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.diagonal_apply] using hsum.symm

/-- The finite-enumeration range embedding has right Gram matrix equal to the
total operator of the projective family.

This is the canonical sigma-space form of the paper's identity `X† X = Q`.  The
proof uses only that the auxiliary projectors `T_a` form a measurement and the
pointwise restatement `Q_a = X† T_a X`, together with the recorded total
identity `∑ a, Q_a = Q`. -/
lemma sigmaFinRangeEmbedding_gram_right {Outcome : Type uOutcome}
    [Fintype Outcome] [DecidableEq Outcome]
    {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (q : OpFamily Outcome ι)
    (qa_projective : ∀ a : Outcome, MIPStarRE.Quantum.IsProj (q.outcome a))
    (q_sum_eq_total : ∑ a : Outcome, q.outcome a = q.total) :
    (sigmaFinRangeEmbedding q.outcome qa_projective)ᴴ *
        (sigmaFinRangeEmbedding q.outcome qa_projective) =
      q.total := by
  classical
  let X := sigmaFinRangeEmbedding q.outcome qa_projective
  let T := sigmaFinProjMeas (fun a : Outcome => (q.outcome a).rank)
  have hT_sum :
      (∑ a : Outcome, T.outcome a) =
        (1 : MIPStarRE.Quantum.Op (ULift.{uι}
          (FiniteHilbertSpace.sigmaFinCarrier
            (fun a : Outcome => (q.outcome a).rank)))) := by
    simpa [T] using T.sum_eq
  have hmul_sum :
      Xᴴ * (∑ a : Outcome, T.outcome a) =
        ∑ a : Outcome, Xᴴ * T.outcome a := by
    simpa using
      (Matrix.mul_sum (s := Finset.univ)
        (f := fun a : Outcome => T.outcome a) (M := Xᴴ))
  have hsum_mul :
      (∑ a : Outcome, Xᴴ * T.outcome a) * X =
        ∑ a : Outcome, Xᴴ * T.outcome a * X := by
    simpa using
      (Matrix.sum_mul (s := Finset.univ)
        (f := fun a : Outcome => Xᴴ * T.outcome a) (M := X))
  calc
    (sigmaFinRangeEmbedding q.outcome qa_projective)ᴴ *
        (sigmaFinRangeEmbedding q.outcome qa_projective)
        = Xᴴ * X := rfl
    _ = Xᴴ * (∑ a : Outcome, T.outcome a) * X := by
          rw [hT_sum, Matrix.mul_one]
    _ = (∑ a : Outcome, Xᴴ * T.outcome a) * X := by rw [hmul_sum]
    _ = ∑ a : Outcome, Xᴴ * T.outcome a * X := hsum_mul
    _ = ∑ a : Outcome, q.outcome a := by
          refine Finset.sum_congr rfl ?_
          intro a _
          simpa [X, T] using
            (sigmaFinRangeEmbedding_qa_eq q.outcome qa_projective a).symm
    _ = q.total := q_sum_eq_total







/-- The finite-enumeration `Q` layer associated to an operator family.

The auxiliary Hilbert space is the finite-enumeration model of
`Σ a, Fin (rank Q_a)`, lifted to the universe of the ambient space.  The block
measurement selecting the summands indexed by a fixed outcome is projective.
This construction requires the sigma carrier to be nonempty; the degenerate
all-ranks-zero case is handled separately by the low-rank auxiliary-space
producer. -/
noncomputable def sigmaRangeQLayer
    {Outcome : Type uOutcome} [Fintype Outcome] [DecidableEq Outcome]
    {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (q : OpFamily Outcome ι)
    [Nonempty (FiniteHilbertSpace.sigmaFinCarrier
      (fun a : Outcome => (q.outcome a).rank))] :
    QLayerData Outcome ι where
  auxSpace := FiniteHilbertSpace.sigmaFin
    (fun a : Outcome => (q.outcome a).rank)
  q := q
  t := sigmaFinProjMeas (fun a : Outcome => (q.outcome a).rank)

/-- Assemble `QXPLayerData` from the canonical sigma-space embedding and the
remaining SVD/polar identities for `Xhat`.

The matrix `X` and the auxiliary projective measurement are fixed to be the
finite-enumeration sigma construction associated to the projective family `q`.
Thus the hypothesis `Q_a = X† T_a X` required by
`QXPLayerData.ofQLayerAndSvdIdentities` is supplied by
`sigmaFinRangeEmbedding_qa_eq`; only the coisometry and mixed-square-root
identities for `Xhat` remain as inputs. -/
noncomputable def QXPLayerData.ofSigmaRangeAndSvdIdentities
    {Outcome : Type uOutcome} [Fintype Outcome] [DecidableEq Outcome]
    {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (q : OpFamily Outcome ι)
    (qa_projective : ∀ a : Outcome, MIPStarRE.Quantum.IsProj (q.outcome a))
    (q_sum_eq_total : ∑ a : Outcome, q.outcome a = q.total)
    [Nonempty (FiniteHilbertSpace.sigmaFinCarrier
      (fun a : Outcome => (q.outcome a).rank))]
    (xHat : Matrix (sigmaRangeCarrier q) ι ℂ)
    (xHat_coisometry : xHat * xHatᴴ =
      (1 : MIPStarRE.Quantum.Op (sigmaRangeCarrier q)))
    (xHat_mixed : (sigmaFinRangeEmbedding q.outcome qa_projective)ᴴ * xHat =
      CFC.sqrt q.total) :
    QXPLayerData Outcome ι := by
  classical
  let qLayer : QLayerData Outcome ι := sigmaRangeQLayer q
  exact QXPLayerData.ofQLayerAndSvdIdentities qLayer qa_projective
    (by simpa [qLayer, sigmaRangeQLayer, Qa, QTotal] using q_sum_eq_total)
    (sigmaFinRangeEmbedding q.outcome qa_projective) xHat
    (by
      intro a
      change q.outcome a =
        (sigmaFinRangeEmbedding q.outcome qa_projective)ᴴ *
          (sigmaFinProjMeas (fun a : Outcome => Matrix.rank (q.outcome a))).outcome a *
        sigmaFinRangeEmbedding q.outcome qa_projective
      exact sigmaFinRangeEmbedding_qa_eq q.outcome qa_projective a)
    (by
      change xHat * xHatᴴ =
        (1 : MIPStarRE.Quantum.Op (ULift.{uι}
          (FiniteHilbertSpace.sigmaFinCarrier
            (fun a : Outcome => Matrix.rank (q.outcome a)))))
      exact xHat_coisometry)
    (by
      change (sigmaFinRangeEmbedding q.outcome qa_projective)ᴴ * xHat = CFC.sqrt q.total
      exact xHat_mixed)

/-- Assemble the sigma-space `Q/X/Xhat/P` layer from a rank-reduction witness
and the remaining SVD/polar identities for `Xhat`.

The rank-reduction witness supplies the two facts about the family `Q_a` that
enter the matrix decomposition: each `Q_a` is a projection, and
`∑_a Q_a = Q`.  The auxiliary space, the projective measurement `T`, and the
matrix `X` are therefore the canonical finite-enumeration construction attached
to the ranks of the projectors `Q_a`.  As in the paper, the only data still not
constructed here are the coisometry and mixed square-root identities for the
chosen matrix `Xhat`. -/
theorem exists_qxpLayerData_ofRankReductionSigmaRangeAndSvdIdentities
    {Outcome : Type uOutcome} [Fintype Outcome] [DecidableEq Outcome]
    {ι : Type uι} [Fintype ι] [DecidableEq ι]
    {ψ : QuantumState ι} {A : Measurement Outcome ι} {ζ : Error}
    {qLayer : QLayerData Outcome ι}
    (hRank : RankReductionWitness ψ A ζ qLayer)
    [Nonempty (FiniteHilbertSpace.sigmaFinCarrier
      (fun a : Outcome => (qLayer.q.outcome a).rank))]
    (xHat : Matrix (sigmaRangeCarrier qLayer.q) ι ℂ)
    (xHat_coisometry : xHat * xHatᴴ =
      (1 : MIPStarRE.Quantum.Op (sigmaRangeCarrier qLayer.q)))
    (xHat_mixed :
      (sigmaFinRangeEmbedding qLayer.q.outcome hRank.projective)ᴴ * xHat =
        CFC.sqrt (QTotal qLayer)) :
    ∃ data : QXPLayerData Outcome ι,
      ∃ hq : data.qLayer = sigmaRangeQLayer qLayer.q,
        hq ▸ data.x =
            (show Matrix (sigmaRangeQLayer qLayer.q).auxSpace.carrier ι ℂ from
              sigmaFinRangeEmbedding qLayer.q.outcome hRank.projective) ∧
          hq ▸ data.xHat =
            (show Matrix (sigmaRangeQLayer qLayer.q).auxSpace.carrier ι ℂ from xHat) := by
  classical
  exact
    ⟨QXPLayerData.ofSigmaRangeAndSvdIdentities (q := qLayer.q)
      hRank.projective hRank.sum_eq_total xHat xHat_coisometry xHat_mixed,
      rfl, rfl, rfl⟩



/-- A one-point projective measurement concentrating all mass on the chosen outcome. -/
noncomputable def pointProjMeas {Outcome : Type uOutcome}
    [Fintype Outcome] [DecidableEq Outcome]
    (a0 : Outcome) :
    ProjMeas Outcome (ULift.{uι} Unit) where
  outcome := fun a => if a = a0 then 1 else 0
  total := 1
  outcome_pos := fun a => by
    by_cases h : a = a0 <;> simp [h]
  sum_eq_total := Matrix.ext fun _ _ => by
    simp [eq_comm, Finset.sum_ite_eq]
  total_le_one := le_rfl
  total_eq_one := rfl
  proj := fun a => by
    by_cases h : a = a0 <;> simp [h]

/-- The lifted finite-enumeration model of `Σ a, Fin (m a)` has cardinality
bounded by the ambient dimension whenever the total multiplicity is bounded. -/
lemma sigmaFinCard_le_of_sum_le {Outcome : Type*} [Fintype Outcome]
    {ι : Type*} [Fintype ι]
    (m : Outcome → ℕ)
    (hm : ∑ a, m a ≤ Fintype.card ι) :
    Fintype.card (FiniteHilbertSpace.sigmaFinCarrier m) ≤ Fintype.card ι := by
  rw [← Fintype.card_congr (sigmaFinCarrierEquiv (m := m))]
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  exact hm

/-- **Paper source:** `references/ldt-paper/orthonormalization.tex:540-553`
(`\label{lem:projective-low-rank-sum}`).

A rank-reduction witness can be viewed on the canonical sigma-range auxiliary
space attached to the same projective family.  This is a Lean-only transport
from an arbitrary auxiliary model of the projective family to the finite
enumeration of its range bases; the mathematical hypotheses are exactly the
rank-reduction witness fields.

**Faithful encoding:** The theorem changes only the auxiliary-space model used
to present the same projective family `Q_a`; it is not an additional
mathematical assumption or proof obligation. -/
theorem RankReductionWitness.toSigmaRangeQLayer
    {Outcome : Type uOutcome} [Fintype Outcome] [DecidableEq Outcome]
    {ι : Type uι} [Fintype ι] [DecidableEq ι]
    {ψ : QuantumState ι} {A : Measurement Outcome ι} {ζ : Error}
    {qLayer : QLayerData Outcome ι}
    (hRank : RankReductionWitness ψ A ζ qLayer)
    [Nonempty (FiniteHilbertSpace.sigmaFinCarrier
      (fun a : Outcome => (qLayer.q.outcome a).rank))] :
    RankReductionWitness ψ A ζ (sigmaRangeQLayer qLayer.q) := by
  refine
    { projective := fun a => by
        simpa [sigmaRangeQLayer, Qa] using hRank.projective a
      outcome_nonneg := fun a => by
        simpa [sigmaRangeQLayer, Qa] using hRank.outcome_nonneg a
      sum_eq_total := ?_
      source_almost_projective := hRank.source_almost_projective
      closeness := ?_
      total_le := ?_
      totalRank_le := ?_
      auxDim_le := ?_ }
  · simpa [sigmaRangeQLayer, Qa, QTotal] using hRank.sum_eq_total
  · simpa [sigmaRangeQLayer] using hRank.closeness
  · simpa [sigmaRangeQLayer, QTotal] using hRank.total_le
  · simpa [sigmaRangeQLayer, Qa] using hRank.totalRank_le
  · change Fintype.card (sigmaRangeCarrier qLayer.q) ≤ Fintype.card ι
    rw [Fintype.card_ulift]
    exact sigmaFinCard_le_of_sum_le
      (m := fun a : Outcome => (qLayer.q.outcome a).rank)
      (ι := ι) hRank.totalRank_le









end

end MIPStarRE.LDT.MakingMeasurementsProjective

end

end LIDT


