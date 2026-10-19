-- Prove2me | Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_Defs_Tuples
-- name    : MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_Defs_Tuples
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T01:58:09.623825+00:00
-- url     : https://prove2.me/theorems/af7a82fc-928d-4240-827b-673567e814c8
-- title:
--   Definitions of Tuples: Section 12 — Definitions: tuples and operators Tuple distributions, type abbreviations, and basic operator helpers
-- statement:
--   The definitions of the module `MIPRE.Background.LIDT.MIPStarRE.LDT.Pasting.Defs.Tuples` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Section 12 — Definitions: tuples and operators. Tuple distributions, type abbreviations, and basic operator helpers.
--
--   The module is vendored read-only, with the authors' permission, from [LionSR/MIPStarRE](https://github.com/LionSR/MIPStarRE) (Sirui Lu and the MIPStarRE contributors, Apache 2.0; commit and upstream path in the file header) by `scripts/vendor-lidt.py`.
--
--   **Definitions** (21): `MIPStarRE.LDT.Pasting.GHatOutcome` (The outcome type of the completed family `\widehat G`.); `MIPStarRE.LDT.Pasting.GHatTupleOutcome` (The outcome type of a `k`-tuple of completed-slice answers.); `MIPStarRE.LDT.Pasting.GHatType` (A Boolean type pattern for a completed-slice tuple.); `MIPStarRE.LDT.Pasting.InterpolationEligible` (A completed-slice tuple is eligible for interpolation exactly when its type has Hamming weight at least `d + 1`, matching the paper's `|w|…); `MIPStarRE.LDT.Pasting.SandwichedLineQuestion` (A sandwiched-line question consists of a point and a `k`-tuple of slice heights.); `MIPStarRE.LDT.Pasting.SlicePairQuestion` (The question type for an ordered pair of slice heights.); `MIPStarRE.LDT.Pasting.SliceQuestion` (The question type for a single slice height.); `MIPStarRE.LDT.Pasting.VerticalLineQuestion` (The question type for vertical lines, identified with their base point.); `MIPStarRE.LDT.Pasting.bernoulliTailOperator` (The Bernoulli tail operator from `lem:chernoff-bernoulli-matrix`: `F(X) = ∑_{r=degree+1}^{k} C(k,r) · X^r · (I - X)^{k-r}`.); `MIPStarRE.LDT.Pasting.distinctTupleDistribution` (Uniform distribution on pairwise-distinct `k`-tuples from `Fq`.); `MIPStarRE.LDT.Pasting.distinctTupleSupport` (The finite support of the distinct-tuple distribution.); `MIPStarRE.LDT.Pasting.gHatTupleHammingWeight` (The Hamming weight of a completed-slice tuple.); `MIPStarRE.LDT.Pasting.gHatTupleSupport` (The support of a completed-slice tuple, i.e.); and 0 more.
--
--   **Embedded lemmas** (2): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `distinctTupleDistribution_support`, `mem_distinctTupleSupport`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Background.LIDT.MIPStarRE.LDT.Pasting.Defs.Tuples` (`MIPRE/Background/LIDT/MIPStarRE/LDT/Pasting/Defs/Tuples.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 17 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/LIDT/MIPStarRE/LDT/Pasting/Defs/Tuples.lean

/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/Pasting/Defs/Tuples.lean
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/MIPStarRE/LDT/Pasting/Defs/Tuples.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Algebra.Hom
import Mathlib.Algebra.Algebra.Spectrum.Quasispectrum
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.CharP.Invertible
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Action.Pi
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Commute.Defs
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Finsupp
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Invertible.Defs
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Algebra.Group.Submonoid.Defs
import Mathlib.Algebra.Group.Subsemigroup.Defs
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.Hom
import Mathlib.Algebra.GroupWithZero.Invertible
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.GroupWithZero.NeZero
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Module.Submodule.Defs
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Algebra.MonoidAlgebra.Module
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.Polynomial
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.Notation.Defs
import Mathlib.Algebra.Notation.Pi.Defs
import Mathlib.Algebra.Opposites
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Group.Unbundled.Basic
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.GroupWithZero.Canonical
import Mathlib.Algebra.Order.IsBotOne
import Mathlib.Algebra.Order.Module.Defs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
import Mathlib.Algebra.Order.Nonneg.Basic
import Mathlib.Algebra.Order.Nonneg.Module
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Order.Sub.Defs
import Mathlib.Algebra.Order.SuccPred
import Mathlib.Algebra.Order.ZeroLEOne
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Algebra.Ring.Commute
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Star.Module
import Mathlib.Algebra.Star.SelfAdjoint
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.NonUnital
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Mathlib.Analysis.CStarAlgebra.Module.Defs
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Convex.Cone.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Complex.BigOperators
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finite.Defs
import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Empty
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.FunLike.Basic
import Mathlib.Data.FunLike.Equiv
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.List.Nodup
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Matrix.Diagonal
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Multiset.Count
import Mathlib.Data.Multiset.Defs
import Mathlib.Data.Multiset.MapFold
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Init
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Star
import Mathlib.Data.Set.Defs
import Mathlib.Data.SetLike.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Geometry.Convex.Cone.Pointed
import Mathlib.GroupTheory.GroupAction.Hom
import Mathlib.GroupTheory.GroupAction.Ring
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Logic.Basic
import Mathlib.Logic.Embedding.Basic
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.IsEmpty.Basic
import Mathlib.Logic.IsEmpty.Defs
import Mathlib.Logic.Nonempty
import Mathlib.Logic.Nontrivial.Defs
import Mathlib.Logic.Unique
import Mathlib.Order.Basic
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.Lattice
import Mathlib.Order.Lattice.Nat
import Mathlib.Order.Nat
import Mathlib.Order.RelClasses
import Mathlib.Order.SetNotation
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.CancelDenoms.Core
import Mathlib.Tactic.FieldSimp.Lemmas
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Positivity.Core
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Topology.Algebra.Field
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Topology.Algebra.InfiniteSum.SummationFilter
import Mathlib.Topology.Algebra.Module.ClosedSubmodule
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Algebra.Monoid.Defs
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Algebra.Star.Real
import Mathlib.Topology.Basic
import Mathlib.Topology.Constructions
import Mathlib.Topology.Continuous
import Mathlib.Topology.Defs.Basic
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Defs
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.Real
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.UniformSpace.Defs
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_LinePolynomials
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_LowDegreePolynomial
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_QuantumState
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_SubMeasurementCore
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_OperatorExpectations
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_SubMeasurementFamilies
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_ParametersFiniteAnswers
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_OpFamily

set_option backward.isDefEq.respectTransparency false

/-!
# Section 12 — Definitions: tuples and operators

Tuple distributions, type abbreviations, and basic operator helpers.
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open scoped BigOperators MatrixOrder Matrix ComplexOrder

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


