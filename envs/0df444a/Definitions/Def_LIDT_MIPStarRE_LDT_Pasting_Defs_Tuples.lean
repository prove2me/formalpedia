-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Tuples
-- name    : LIDT_MIPStarRE_LDT_Pasting_Defs_Tuples
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T11:32:17.098382+00:00
-- url     : https://prove2.me/theorems/d1c87022-630d-46c9-aa6f-c4edd397ae03
-- title:
--   LIDT definitions: LDT / Pasting / Defs / Tuples
-- statement:
--   This bundle defines the tuple-level questions and outcomes for pasted slice strategies. It introduces completed-slice and slice answer types, tuple outcomes and type patterns, sandwiched and vertical line questions, and the eligibility predicate controlling whether enough genuine answers are available for interpolation.
--
--   Principal definitions:
--   - `GHatOutcome`: the outcome type for the completed family G-hat.
--   - `SliceQuestion`: the question type for one slice height.
--   - `SlicePairQuestion`: the ordered pair of slice heights.
--   - `GHatTupleOutcome`: a tuple of completed-slice answers.
--   - `GHatType`: the Boolean pattern recording which tuple entries are completed answers.
--   - `SandwichedLineQuestion`: a point together with a tuple of slice heights.
--   - `VerticalLineQuestion`: the vertical-line question identified by its base point.
--   - `InterpolationEligible`: the predicate that the completed tuple has at least `d + 1` genuine entries.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/Pasting/Defs/Tuples.lean#L25-L243

-- Generated from MIPStarRE/LDT/Pasting/Defs/Tuples.lean by skeleton subtraction.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LinePolynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LowDegreePolynomial
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OpFamily
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OperatorExpectations
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersFiniteAnswers
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_QuantumState
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SubMeasurementCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SubMeasurementFamilies
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_TensorPlacement
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Mathlib

namespace LIDT

/-!
# Section 12 — Definitions: tuples and operators

Tuple distributions, type abbreviations, and basic operator helpers.
-/

@[expose] public section

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]



/-- The finite support of the distinct-tuple distribution. -/
noncomputable def distinctTupleSupport (params : Parameters) (k : ℕ) :
    Finset (PointTuple params k) := by
  classical
  exact Finset.univ.filter (fun xs : PointTuple params k => Function.Injective xs)

@[simp] theorem mem_distinctTupleSupport (params : Parameters) (k : ℕ)
    (xs : PointTuple params k) :
    xs ∈ distinctTupleSupport params k ↔ Function.Injective xs := by
  classical
  simp [distinctTupleSupport]







/-- Uniform distribution on pairwise-distinct `k`-tuples from `Fq`.
Support is the set of injective functions `Fin k → Fq params`;
weight is uniform `1 / |support|` on support, `0` outside. -/
noncomputable def distinctTupleDistribution (params : Parameters) (k : ℕ) :
    Distribution (PointTuple params k) :=
  Distribution.uniformOnFinset (distinctTupleSupport params k)

@[simp] theorem distinctTupleDistribution_support (params : Parameters) (k : ℕ) :
    (distinctTupleDistribution params k).support = distinctTupleSupport params k := by
  simp [distinctTupleDistribution]



/-- The distinct-tuple distribution has total mass at most `1`. -/
theorem distinctTupleDistribution_weight_sum_le_one (params : Parameters) (k : ℕ) :
    ∑ xs ∈ (distinctTupleDistribution params k).support,
      (distinctTupleDistribution params k).weight xs ≤ 1 := by
  simpa [distinctTupleDistribution] using
    Distribution.uniformOnFinset_weight_sum_le_one (distinctTupleSupport params k)







/-- The outcome type of the completed family `\widehat G`. -/
abbrev GHatOutcome (params : Parameters) [FieldModel params.q] := Option (Polynomial params)

/-- The question type for a single slice height. -/
abbrev SliceQuestion (params : Parameters) := Fq params

/-- The question type for an ordered pair of slice heights. -/
abbrev SlicePairQuestion (params : Parameters) := Fq params × Fq params

/-- The outcome type of a `k`-tuple of completed-slice answers. -/
abbrev GHatTupleOutcome (params : Parameters) [FieldModel params.q] (k : ℕ) :=
  Fin k → GHatOutcome params

/-- A Boolean type pattern for a completed-slice tuple. -/
abbrev GHatType (k : ℕ) := Fin k → Bool

/-- A sandwiched-line question consists of a point and a `k`-tuple of slice heights. -/
abbrev SandwichedLineQuestion (params : Parameters) (k : ℕ) :=
  Point params × PointTuple params k

/-- The question type for vertical lines, identified with their base point. -/
abbrev VerticalLineQuestion (params : Parameters) := Point params

/-- The Hamming weight `|τ|` of a type `τ ∈ {0,1}^k`. -/
def gHatTypeWeight {k : ℕ} (τ : GHatType k) : ℕ :=
  (Finset.univ.filter fun i => τ i).card

/-- Prepend one type bit to a tail type. -/
def prependTypeBit {k : ℕ} (b : Bool) (τ : GHatType k) : GHatType (k + 1) :=
  Fin.cons b τ

/-- The operator monomial associated with a type `τ`. -/
noncomputable def gHatTypeOperator (G : MIPStarRE.Quantum.Op ι) {k : ℕ}
    (τ : GHatType k) : MIPStarRE.Quantum.Op ι :=
  G ^ gHatTypeWeight τ * (1 - G) ^ (k - gHatTypeWeight τ)

/-- `def:truncated-type-sums`.

Fixing a tail type `τ_tail`, this sums the source-style monomials contributed by
all prefixes whose total Hamming weight can still reach the interpolation
threshold `d + 1`. The parameter `prefixLen` is the paper's `ℓ - 1`. -/
noncomputable def truncatedTypeSums (G : MIPStarRE.Quantum.Op ι)
    (d prefixLen : ℕ) {tailLen : ℕ} (τtail : GHatType tailLen) :
    MIPStarRE.Quantum.Op ι :=
  ∑ τprefix : GHatType prefixLen,
    if d + 1 ≤ gHatTypeWeight τprefix + gHatTypeWeight τtail then
      gHatTypeOperator G τprefix
    else 0

/-- The Bernoulli tail operator from `lem:chernoff-bernoulli-matrix`:
`F(X) = ∑_{r=degree+1}^{k} C(k,r) · X^r · (I - X)^{k-r}`.
This is the matrix-valued Bernoulli tail probability. -/
noncomputable def bernoulliTailOperator (k degree : ℕ)
    (X : MIPStarRE.Quantum.Op ι) : MIPStarRE.Quantum.Op ι :=
  ∑ r ∈ Finset.Icc (degree + 1) k,
    (Nat.choose k r : ℂ) • (X ^ r * (1 - X) ^ (k - r))



/-- Multiply each outcome operator by a total operator on the right. -/
noncomputable def multiplyByTotalOnRight {α β : Type*} [Fintype α] [Fintype β]
    (A : SubMeas α ι) (B : SubMeas β ι) :
    OpFamily α ι where
  outcome := fun a => A.outcome a * B.total
  total := A.total * B.total

/-- Multiply each outcome operator by a total operator on the left. -/
noncomputable def multiplyByTotalOnLeft {α β : Type*} [Fintype α] [Fintype β]
    (A : SubMeas α ι) (B : SubMeas β ι) :
    OpFamily β ι where
  outcome := fun b => A.total * B.outcome b
  total := A.total * B.total

/-- Record which completed-slice outcomes are genuine polynomial outcomes. -/
def gHatTupleType {params : Parameters} {k : ℕ}
    [FieldModel params.q]
    (gs : GHatTupleOutcome params k) : GHatType k :=
  fun i => Option.isSome (gs i)

/-- The support of a completed-slice tuple, i.e. the indices whose outcomes are
genuine polynomials rather than `⊥`. This matches the paper's support of the type
`τ ∈ {0,1}^k`. -/
def gHatTupleSupport {params : Parameters} {k : ℕ}
    [FieldModel params.q]
    (gs : GHatTupleOutcome params k) : Finset (Fin k) :=
  Finset.univ.filter fun i => (gs i).isSome

/-- The Hamming weight of a completed-slice tuple. -/
def gHatTupleHammingWeight {params : Parameters} {k : ℕ}
    [FieldModel params.q]
    (gs : GHatTupleOutcome params k) : ℕ :=
  (gHatTupleSupport gs).card

/-- The set `\mathsf{Outcomes}_\tau` of completed-slice tuples whose `Some`/`none`
pattern is prescribed by the type `τ`. -/
def outcomesByType {params : Parameters} {k : ℕ}
    [FieldModel params.q]
    (τ : GHatType k) : Set (GHatTupleOutcome params k) :=
  { gs | ∀ i : Fin k, (gs i).isSome = τ i }

/-- A completed-slice tuple is eligible for interpolation exactly when its type has
Hamming weight at least `d + 1`, matching the paper's `|w| ≥ d+1` filter. -/
def InterpolationEligible (params : Parameters) {k : ℕ}
    [FieldModel params.q]
    (gs : GHatTupleOutcome params k) : Prop :=
  params.d + 1 ≤ gHatTupleHammingWeight gs

end MIPStarRE.LDT.Pasting

end

end LIDT


