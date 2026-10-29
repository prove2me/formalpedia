-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayer_Core
-- name    : LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayer_Core
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T11:56:19.446989+00:00
-- url     : https://prove2.me/theorems/7a2e46ae-dc79-4b9d-ae65-3a5e6c5a46a8
-- title:
--   LIDT definitions: LDT / MakingMeasurementsProjective / QXPLayer / Core
-- statement:
--   This bundle packages the QXP projectivization layers, including the rounded operator data, auxiliary rank-reduction witness, and derived projective family.
--
--   Principal definitions:
--   - `QLayerData`: records the rounded positive operator and its bounds.
--   - `QXPLayerData`: packages the Q, X, rank-reduced, and projective layers.
--   - `RankReductionWitness`: relates the reduced family to the auxiliary projective measurement.
--   - `pFamilyFromXHat`: constructs the projective family from the rank-reduced operator.
--   - `PFamily`: the projective family carried by the QXP layer.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/MakingMeasurementsProjective/QXPLayer/Core.lean#L24-L354

-- Generated from MIPStarRE/LDT/MakingMeasurementsProjective/QXPLayer/Core.lean by skeleton subtraction.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Statements
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Completion
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_CauchySchwarz
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_ComparisonCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_DistanceBounds
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichMain_Completeness
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_ApproxDelta
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_InnerProduct
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_QuantumNonneg
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

namespace MIPStarRE.LDT.Preliminaries
end MIPStarRE.LDT.Preliminaries

/-!
# Section 5 — Q/X/XHat/P core data

Scalar error estimates, core data structures, and shared operator-family
definitions for the paper's `Q/X/XHat/P` intermediate layer.
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

namespace MIPStarRE.LDT.MakingMeasurementsProjective

open MIPStarRE.LDT

noncomputable section

universe uOutcome uι

/-- The quarter-root error term `ζ^(1/4)` used throughout the paper's late-stage
orthonormalization estimates. -/
noncomputable def zetaQuarterRoot (ζ : Error) : Error :=
  Real.rpow ζ (1 / (4 : Error))

/-- The quarter-root error term is nonnegative on nonnegative input. -/
lemma zetaQuarterRoot_nonneg {ζ : Error} (hζ : 0 ≤ ζ) :
    0 ≤ zetaQuarterRoot ζ := by
  dsimp [zetaQuarterRoot]
  exact Real.rpow_nonneg hζ _

/-- **Scalar truncation inequality** (`lem:trunc-inequality`).

For `x ∈ [0,1]`, truncating at threshold `1 - δ` changes `x` by at most
`(1 / δ) * (x - x^2)` in squared distance. -/
lemma truncationInequality (δ x : Error) :
    0 < δ →
      δ ≤ 1 / 2 →
      0 ≤ x →
      x ≤ 1 →
      let trunc : Error := if 1 - δ ≤ x then 1 else 0
      (x - trunc) ^ (2 : Nat) ≤ (1 / δ) * (x - x ^ (2 : Nat)) := by
  intro hδ hδhalf hx hx1
  simp only []
  split
  · next h =>
    have h1x : 0 ≤ 1 - x := by linarith
    have hxd : 1 - x ≤ δ := by linarith
    rw [div_mul_eq_mul_div, le_div_iff₀ hδ]
    nlinarith [sq_nonneg (1 - x), sq_nonneg δ]
  · next h =>
    push Not at h
    simp only [sub_zero]
    rw [div_mul_eq_mul_div, le_div_iff₀ hδ]
    have hlt : 0 ≤ 1 - δ - x := by linarith
    nlinarith [mul_nonneg hx hlt,
      mul_nonneg (mul_nonneg (le_of_lt hδ) hx)
        (by linarith : (0 : ℝ) ≤ 1 - x)]

/-- The truncation error is nonnegative on nonnegative input. -/
lemma spectralTruncationError_nonneg {ζ : Error} (hζ : 0 ≤ ζ) :
    0 ≤ spectralTruncationError ζ := by
  dsimp [spectralTruncationError]
  exact Real.rpow_nonneg hζ _

/-- The truncation error is `√ζ`. -/
lemma spectralTruncationError_eq_sqrt (ζ : Error) :
    spectralTruncationError ζ = Real.sqrt ζ := by
  simp [spectralTruncationError, Real.sqrt_eq_rpow]

/-- A raw operator family viewed as a constant indexed family on the trivial
question set. -/
def constOpFamily {Outcome : Type*} {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (A : OpFamily Outcome ι) :
    IdxOpFamily Unit Outcome ι :=
  fun _ => A

/-- Data for the paper's intermediate `Q`-layer: the rank-reduced family
`Q_a`, its total operator `Q`, and the auxiliary projective measurement `T_a`
used to define `X_a`, `XHat_a`, and `P_a`. -/
structure QLayerData (Outcome : Type uOutcome) [Fintype Outcome]
    (ι : Type uι) [Fintype ι] [DecidableEq ι] where
  auxSpace : FiniteHilbertSpace.{uι}
  q : OpFamily Outcome ι
  t : ProjMeas Outcome auxSpace.carrier

/-- The paper's operator `Q_a`. -/
def Qa {Outcome : Type*} [Fintype Outcome]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (data : QLayerData Outcome ι) (a : Outcome) :
    MIPStarRE.Quantum.Op ι :=
  data.q.outcome a

/-- The paper's total operator `Q = ∑_a Q_a`. -/
def QTotal {Outcome : Type*} [Fintype Outcome]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (data : QLayerData Outcome ι) :
    MIPStarRE.Quantum.Op ι :=
  data.q.total

/-- The paper's auxiliary projector `T_a`. -/
def Ta {Outcome : Type*} [Fintype Outcome]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (data : QLayerData Outcome ι) (a : Outcome) :
    MIPStarRE.Quantum.Op data.auxSpace.carrier :=
  data.t.outcome a

/-- Paper origin: `references/ldt-paper/orthonormalization.tex:414-531`
(`\label{lem:projective-non-measurement}`; full rounding-to-projectors
lemma with `2√ζ` closeness and `(1+2√ζ)·I` total bound).

Witness structure for the paper's rounding-to-projectors lemma.

A value `RoundingToProjectorsWitness ψ A ζ R` is the honest output consumed by
this QXP rank-reduction layer: a chosen rounded family `R_a` together with the
paper's `2√ζ` closeness estimate and `(1 + 2√ζ) I` total-mass bound. -/
structure RoundingToProjectorsWitness {Outcome : Type*}
    [Fintype Outcome]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι) (A : Measurement Outcome ι)
    (ζ : Error) (R : OpFamily Outcome ι) : Prop where
  projective :
    ∀ a : Outcome, MIPStarRE.Quantum.IsProj (R.outcome a)
  closeness :
    SDDOpRel ψ (uniformDistribution Unit)
      (constOpFamily (A.toSubMeas : OpFamily Outcome ι))
      (constOpFamily R)
      (2 * spectralTruncationError ζ)
  sum_eq_total :
    ∑ a, R.outcome a = R.total
  total_le :
    R.total ≤ (((1 : Error) + 2 * spectralTruncationError ζ) : ℂ) •
      (1 : MIPStarRE.Quantum.Op ι)

/-- **Rounding to projectors** (`lem:projective-non-measurement`).

This is the paper-facing proposition consumed by the QXP rank-reduction layer:
there is a rounded projective family `R_a` equipped with the bounds recorded in
`RoundingToProjectorsWitness ψ A ζ R`. The constructive spectral-truncation
theorem supplies this witness from `eq:A-looks-projective`. -/
abbrev projectiveNonMeasurement {Outcome : Type uOutcome}
    {ι : Type uι} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι)
    (A : Measurement Outcome ι) (ζ : Error) : Prop :=
  ∃ R : OpFamily Outcome ι,
    RoundingToProjectorsWitness ψ A ζ R

/-- Paper origin: `references/ldt-paper/orthonormalization.tex:540-553`
(`\label{lem:projective-low-rank-sum}`; rank-reduction lemma with
`12√ζ` closeness, `(1+2√ζ)·I` total bound, and rank constraint
`∑ rank(Q_a) ≤ d`).

Witness structure for the rank-reduction lemma. -/
structure RankReductionWitness {Outcome : Type*}
    [Fintype Outcome]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι) (A : Measurement Outcome ι)
    (ζ : Error) (data : QLayerData Outcome ι) : Prop where
  projective :
    ∀ a : Outcome, MIPStarRE.Quantum.IsProj (Qa data a)
  outcome_nonneg :
    ∀ a : Outcome, 0 ≤ Qa data a
  sum_eq_total :
    ∑ a, Qa data a = QTotal data
  source_almost_projective :
    ∑ a, ev ψ (A.outcome a - A.outcome a * A.outcome a) ≤ 2 * ζ
  closeness :
    SDDOpRel ψ (uniformDistribution Unit)
      (constOpFamily (A.toSubMeas : OpFamily Outcome ι))
      (constOpFamily data.q)
      (roundingToProjectiveError ζ)
  total_le :
    QTotal data ≤ (((1 : Error) + 2 * spectralTruncationError ζ) : ℂ) •
      (1 : MIPStarRE.Quantum.Op ι)
  totalRank_le :
    ∑ a : Outcome, (Qa data a).rank ≤ Fintype.card ι
  auxDim_le :
    Fintype.card data.auxSpace.carrier ≤ Fintype.card ι

/-- The raw operator family obtained by sandwiching the auxiliary projectors
`T_a` with a candidate `XHat`. This is the family later named `P`. -/
noncomputable def pFamilyFromXHat {Outcome : Type*} [Fintype Outcome]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (qLayer : QLayerData Outcome ι)
    (xHat : Matrix qLayer.auxSpace.carrier ι ℂ) :
    OpFamily Outcome ι where
  outcome := fun a => xHatᴴ * Ta qLayer a * xHat
  total := ∑ a, xHatᴴ * Ta qLayer a * xHat

/-- Data for the paper's `X/XHat/P` layer built on top of `Q_a` and the
auxiliary projectors `T_a`.

The local API deliberately stores only the primitive identities used by the
subsequent `P`-vs-`Q` arguments.  Earlier versions also carried explicit SVD
matrices for `X * Xᴴ`, `Xᴴ * X`, and `X * XHatᴴ`; those fields required a
general rectangular complex-matrix SVD producer that is not available in the
current Mathlib toolchain and was not consumed by the downstream proofs. -/
structure QXPLayerData (Outcome : Type uOutcome) [Fintype Outcome]
    (ι : Type uι) [Fintype ι] [DecidableEq ι] where
  qLayer : QLayerData Outcome ι
  x : Matrix qLayer.auxSpace.carrier ι ℂ
  xHat : Matrix qLayer.auxSpace.carrier ι ℂ
  qa_eq : ∀ a : Outcome, qLayer.q.outcome a = xᴴ * Ta qLayer a * x
  qa_projective : ∀ a : Outcome, MIPStarRE.Quantum.IsProj (qLayer.q.outcome a)
  xHat_coisometry : xHat * xHatᴴ = 1
  x_gram_right : xᴴ * x = QTotal qLayer
  xHat_mixed : xᴴ * xHat = CFC.sqrt (QTotal qLayer)

/-- The paper's matrix `X_a = T_a · X`. -/
def Xa {Outcome : Type*} [Fintype Outcome]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (data : QXPLayerData Outcome ι) (a : Outcome) :
    Matrix data.qLayer.auxSpace.carrier ι ℂ :=
  Ta data.qLayer a * data.x



/-- The paper's operator `P_a = XHat† · T_a · XHat`. -/
def Pa {Outcome : Type*} [Fintype Outcome]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (data : QXPLayerData Outcome ι) (a : Outcome) :
    MIPStarRE.Quantum.Op ι :=
  data.xHatᴴ * Ta data.qLayer a * data.xHat

/-- The raw operator family `P = {P_a}`. -/
noncomputable def PFamily {Outcome : Type*} [Fintype Outcome]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (data : QXPLayerData Outcome ι) :
    OpFamily Outcome ι :=
  pFamilyFromXHat data.qLayer data.xHat







/-- **`X` squared** from the `Q_a = X† T_a X` decomposition.

If each `Q_a` is represented as `X† T_a X` and the auxiliary measurement
`T = {T_a}` sums to the identity, then the right Gram matrix of `X` is the total
operator `Q = ∑_a Q_a`.  This proves `lem:X-squared` from the
`Q_a = X† T_a X` representation, independently of the later `QXPLayerData`
record. -/
theorem xSquared_of_qa_eq {Outcome : Type uOutcome} [Fintype Outcome]
    {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (qLayer : QLayerData Outcome ι)
    (q_sum_eq_total : ∑ a : Outcome, Qa qLayer a = QTotal qLayer)
    (x : Matrix qLayer.auxSpace.carrier ι ℂ)
    (qa_eq : ∀ a : Outcome, qLayer.q.outcome a = xᴴ * Ta qLayer a * x) :
    xᴴ * x = QTotal qLayer := by
  have hT_sum :
      (∑ a : Outcome, Ta qLayer a) =
        (1 : MIPStarRE.Quantum.Op qLayer.auxSpace.carrier) := by
    simpa [Ta] using qLayer.t.sum_eq
  have hmul_sum :
      xᴴ * (∑ a : Outcome, Ta qLayer a) =
        ∑ a : Outcome, xᴴ * Ta qLayer a := by
    simpa using
      (Matrix.mul_sum (s := Finset.univ)
        (f := fun a : Outcome => Ta qLayer a) (M := xᴴ))
  have hsum_mul :
      (∑ a : Outcome, xᴴ * Ta qLayer a) * x =
        ∑ a : Outcome, xᴴ * Ta qLayer a * x := by
    simpa using
      (Matrix.sum_mul (s := Finset.univ)
        (f := fun a : Outcome => xᴴ * Ta qLayer a) (M := x))
  calc
    xᴴ * x
        = xᴴ * (∑ a : Outcome, Ta qLayer a) * x := by
          rw [hT_sum, Matrix.mul_one]
    _ = (∑ a : Outcome, xᴴ * Ta qLayer a) * x := by
          rw [hmul_sum]
    _ = ∑ a : Outcome, xᴴ * Ta qLayer a * x := hsum_mul
    _ = ∑ a : Outcome, qLayer.q.outcome a := by
          refine Finset.sum_congr rfl ?_
          intro a _
          exact (qa_eq a).symm
    _ = ∑ a : Outcome, Qa qLayer a := rfl
    _ = QTotal qLayer := q_sum_eq_total

/-- Assembles the `QXPLayerData` datum from a `Q`-layer and the
SVD-derived identities.

Given a `Q`-layer (`def:matrix-decomposition-Q`), the matrix decomposition `X`
of the paper, the chosen `Xhat`, and the two genuinely SVD-derived identities
`Xhat * Xhatᴴ = I` (`lem:X-hat-squared`) and `Xᴴ * Xhat = √Q`
(`lem:X-times-X-hat`), this assembles the `QXPLayerData` datum consumed by
the downstream `lem:P-Q-approx` argument.

The identity `x_gram_right` (`Xᴴ * X = Q`, paper label `lem:X-squared`) is
discharged by `xSquared_of_qa_eq`, from the representation
`Q_a = Xᴴ * T_a * X` and the measurement identity for `T`. The other
propositional fields, including `qa_projective`, are supplied by the caller.

The hypothesis `qa_eq` records exactly the `lem:qa-restated` choice, and the
two SVD-derived hypotheses (`xHat_coisometry` and `xHat_mixed`) are precisely
what the paper proves about `Xhat = U · I_{m×d} · V†`.  These hypotheses are
supplied by the sigma-range / rectangular polar-decomposition route, which
provides the unitary and coisometry factors from the positive spectral
subspace of `Q`.  The paper's `lem:X-squared`, `lem:X-hat-squared`, and
`lem:X-times-X-hat` are therefore proved given the `QXPLayerData` hypotheses;
the end-to-end chain through the rounding-to-projectors, rank-reduction, and
orthogonalization lemmas remains to be closed upstream. -/
noncomputable def QXPLayerData.ofQLayerAndSvdIdentities
    {Outcome : Type uOutcome} [Fintype Outcome]
    {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (qLayer : QLayerData Outcome ι)
    (qa_projective : ∀ a : Outcome, MIPStarRE.Quantum.IsProj (Qa qLayer a))
    (q_sum_eq_total : ∑ a : Outcome, Qa qLayer a = QTotal qLayer)
    (x : Matrix qLayer.auxSpace.carrier ι ℂ)
    (xHat : Matrix qLayer.auxSpace.carrier ι ℂ)
    (qa_eq : ∀ a : Outcome, qLayer.q.outcome a = xᴴ * Ta qLayer a * x)
    (xHat_coisometry : xHat * xHatᴴ = (1 : MIPStarRE.Quantum.Op qLayer.auxSpace.carrier))
    (xHat_mixed : xᴴ * xHat = CFC.sqrt (QTotal qLayer)) :
    QXPLayerData Outcome ι where
  qLayer := qLayer
  x := x
  xHat := xHat
  qa_eq := qa_eq
  qa_projective := qa_projective
  xHat_coisometry := xHat_coisometry
  x_gram_right := xSquared_of_qa_eq qLayer q_sum_eq_total x qa_eq
  xHat_mixed := xHat_mixed

end

end MIPStarRE.LDT.MakingMeasurementsProjective

end

end LIDT


