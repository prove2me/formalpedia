-- Prove2me | Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_Sandwich_PastedFamilies
-- name    : MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_Sandwich_PastedFamilies
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T03:53:50.066997+00:00
-- url     : https://prove2.me/theorems/c376a7a3-a2db-444c-a2ac-a5e4494bef5e
-- title:
--   Definitions of PastedFamilies: Section 12 — Sandwich constructions: pasted families Pasted interpolation families, recurrence weights, and final…
-- statement:
--   The definitions of the module `MIPRE.Background.LIDT.MIPStarRE.LDT.Pasting.Sandwich.PastedFamilies` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Section 12 — Sandwich constructions: pasted families. Pasted interpolation families, recurrence weights, and final operator families.
--
--   The module is vendored read-only, with the authors' permission, from [LionSR/MIPStarRE](https://github.com/LionSR/MIPStarRE) (Sirui Lu and the MIPStarRE contributors, Apache 2.0; commit and upstream path in the file header) by `scripts/vendor-lidt.py`.
--
--   **Definitions** (18): `MIPStarRE.LDT.Pasting.allOutcomesExpansionFamily` (The expansion over all outcome types `τ`, written as the total mass of the averaged sandwich family restricted to `|τ| ≥ d+1`.); `MIPStarRE.LDT.Pasting.averagedEligibleSandwichSubMeas` (The averaged sandwiched family restricted to outcome tuples of type `τ` with `|τ| ≥ d+1`, as in `lem:over-all-outcomes`.); `MIPStarRE.LDT.Pasting.averagedSandwichByTypeSubMeas` (Average the sandwiched completed-slice family over tuples whose completed/ incomplete pattern is exactly `τtail`.); `MIPStarRE.LDT.Pasting.averagedSliceAppendedSubMeas` (Degree-zero candidate pasted submeasurement obtained by averaging the slice family and viewing each slice polynomial as a polynomial in one…); `MIPStarRE.LDT.Pasting.bernoulliTailFromFamily` (The Bernoulli-tail polynomial in the averaged complete operator `G = E_x \sum_g G^x_g`.); `MIPStarRE.LDT.Pasting.bernoulliTailSubMeas` (The one-outcome submeasurement whose unique effect is the Bernoulli-tail operator of `X`.); `MIPStarRE.LDT.Pasting.constructedPastedMeasurement` (The specific pasted measurement obtained by completing the constructed pasted submeasurement.); `MIPStarRE.LDT.Pasting.constructedPastedSubMeas` (The specific pasted submeasurement constructed from the sandwich/interpolation scheme.); `MIPStarRE.LDT.Pasting.fromHToGRecurrenceWeight` (Source-style recurrence weight `S_{τtail}` from `lem:from-H-to-G`.); and -1 more.
--
--   **Embedded lemmas** (2): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `bernoulliTailSubMeas_outcome`, `bernoulliTailSubMeas_total`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Background.LIDT.MIPStarRE.LDT.Pasting.Sandwich.PastedFamilies` (`MIPRE/Background/LIDT/MIPStarRE/LDT/Pasting/Sandwich/PastedFamilies.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 39 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/LIDT/MIPStarRE/LDT/Pasting/Sandwich/PastedFamilies.lean

/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/Pasting/Sandwich/PastedFamilies.lean
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/MIPStarRE/LDT/Pasting/Sandwich/PastedFamilies.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.Algebra.Hom
import Mathlib.Algebra.Algebra.NonUnitalHom
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
import Mathlib.Algebra.Module.NatInt
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
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Algebra.Order.IsBotOne
import Mathlib.Algebra.Order.Module.Defs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.NatCast
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
import Mathlib.Algebra.Order.Nonneg.Basic
import Mathlib.Algebra.Order.Nonneg.Module
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.Ring.Star
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
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Complex.BigOperators
import Mathlib.Data.Countable.Defs
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.ENNReal.Operations
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finite.Defs
import Mathlib.Data.Finite.Prod
import Mathlib.Data.Finset.Attach
import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Empty
import Mathlib.Data.Finset.Erase
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Range
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.OfMap
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
import Mathlib.Data.Nat.Cast.Commute
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Init
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Prod.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Star
import Mathlib.Data.SProd
import Mathlib.Data.Set.Defs
import Mathlib.Data.SetLike.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Geometry.Convex.Cone.Pointed
import Mathlib.GroupTheory.GroupAction.Hom
import Mathlib.GroupTheory.GroupAction.Ring
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Logic.Basic
import Mathlib.Logic.Embedding.Basic
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Equiv.Prod
import Mathlib.Logic.Function.Basic
import Mathlib.Logic.IsEmpty.Basic
import Mathlib.Logic.IsEmpty.Defs
import Mathlib.Logic.Nonempty
import Mathlib.Logic.Nontrivial.Defs
import Mathlib.Logic.Unique
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Order.Basic
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.Lattice
import Mathlib.Order.Lattice.Nat
import Mathlib.Order.MinMax
import Mathlib.Order.Nat
import Mathlib.Order.Notation
import Mathlib.Order.RelClasses
import Mathlib.Order.SetNotation
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad
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
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.InfiniteSum.SummationFilter
import Mathlib.Topology.Algebra.Module.ClosedSubmodule
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
import Mathlib.Topology.Algebra.Module.LocallyConvex
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Algebra.Monoid.Defs
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Algebra.Star.Real
import Mathlib.Topology.Bases
import Mathlib.Topology.Basic
import Mathlib.Topology.Constructions
import Mathlib.Topology.Continuous
import Mathlib.Topology.Defs.Basic
import Mathlib.Topology.EMetricSpace.Defs
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Defs
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Metrizable.Uniformity
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.Real
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.UniformSpace.Defs
import Mathlib.Topology.UniformSpace.Real
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
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_PMFAverages
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_OpFamily
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Test_Defs
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Test_StrategyRole_Core
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_MeasurementLift
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_Defs
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_ComparisonCore
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_LinePolynomialEmbedding
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Test_StrategyPolynomialFamilies
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Test_StrategyRole_Algebra
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Test_StrategyFailures
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Core
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_CommutativityPoints_Defs
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_CommutativityPoints_Approximation
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_Defs_Tuples
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_Defs_Interpolation
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_Defs_Families
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_Sandwich_Switcheroo
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_Sandwich_GHatSandwich
import Theorems.Thm_MIPStarRE_LDT_Pasting_bernoulliTailOperator_le_one
import Theorems.Thm_MIPStarRE_LDT_Pasting_bernoulliTailOperator_nonneg
import Theorems.Thm_MIPStarRE_LDT_Pasting_distinctTupleDistribution_weight_sum_le_one
import Theorems.Thm_MIPStarRE_LDT_SubMeas_total_nonneg

set_option backward.isDefEq.respectTransparency false

/-!
# Section 12 — Sandwich constructions: pasted families

Pasted interpolation families, recurrence weights, and final operator families.
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Source-style recurrence weight `S_{τtail}` from `lem:from-H-to-G`.

The parameter `prefixLen` is the number of type bits already converted into the
Bernoulli polynomial.  This is exactly `truncatedTypeSums` specialized to the
averaged complete operator `G = E_x ∑_g G^x_g`. -/
noncomputable def fromHToGRecurrenceWeight (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (prefixLen : ℕ) {tailLen : ℕ}
    (τtail : GHatType tailLen) : MIPStarRE.Quantum.Op ι :=
  truncatedTypeSums family.averagedSubMeas.total params.d prefixLen τtail

/-- The interpolated operator `H^{x_1,\dots,x_k}_h` restricted to tuples that are
globally consistent with a single polynomial.

The paper's definition (`references/ldt-paper/ld-pasting.tex` lines 474–495) sums
only tuples `(g_1,…,g_k)` in `Global_τ(x)` — those consistent with a single
polynomial `h` — and then interpolates. The `|τ| ≥ d+1` eligibility filter is
applied by `interpolationEligibleSandwichFamily`; this definition additionally
restricts to globally consistent tuples via `IsGloballyConsistent`.
Consequently, `pastedInterpolationFamily` is supported only on tuples satisfying
both restrictions, and any fallback or default value in
`interpolateCompletedSlices` is irrelevant off that restricted support. -/
noncomputable def pastedInterpolationFamily (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (k : ℕ) :
    IdxSubMeas (PointTuple params k) (Polynomial params.next) ι :=
  fun xs =>
    postprocess
      (restrictSubMeas
        (interpolationEligibleSandwichFamily params family k xs)
        (IsGloballyConsistent params xs))
      (interpolateCompletedSlices params k xs)

/-- The averaged sandwiched family restricted to outcome tuples of type `τ`
with `|τ| ≥ d+1`, as in `lem:over-all-outcomes`. -/
noncomputable def averagedEligibleSandwichSubMeas (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (k : ℕ) :
    SubMeas (GHatTupleOutcome params k) ι :=
  averageIdxSubMeas
    (uniformDistribution (PointTuple params k))
    (interpolationEligibleSandwichFamily params family k)
    (uniformDistribution_weight_sum_le_one (PointTuple params k))

/-- The specific pasted submeasurement constructed from the sandwich/interpolation scheme. -/
noncomputable def constructedPastedSubMeas (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (k : ℕ) : SubMeas (Polynomial params.next) ι :=
  averageIdxSubMeas
    (distinctTupleDistribution params k)
    (pastedInterpolationFamily params family k)
    (distinctTupleDistribution_weight_sum_le_one params k)

/-- The distinguished fallback polynomial `h₀` that receives the completion mass. -/
noncomputable def pastedFallbackOutcome (params : Parameters) [FieldModel params.q] :
    Polynomial params.next :=
  fallbackInterpolatedPolynomial params

/-- The specific pasted measurement obtained by completing the constructed pasted submeasurement.

The paper adds all missing mass `I - H_total` to a single distinguished polynomial
outcome `h₀` (the fallback interpolant).  So the outcome operator for `h₀` becomes
`H_{h₀} + (I - H_total)` while all other outcomes keep their original operators, and
the total is genuinely the identity `I`. -/
noncomputable def constructedPastedMeasurement (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (k : ℕ) : Measurement (Polynomial params.next) ι :=
  Preliminaries.completeAtOutcome
    (constructedPastedSubMeas params family k)
    (pastedFallbackOutcome params)

/-- Degree-zero candidate pasted submeasurement obtained by averaging the slice
family and viewing each slice polynomial as a polynomial in one more variable.

Paper origin: `references/ldt-paper/ld-pasting.tex:12-55`.  This is a
Lean-only construction for the `d = 0` branch of `thm:ld-pasting`, where the
ordinary interpolation construction is not available because `d + 1 = 1`
collapses the distinct-height argument.  It introduces no additional
hypothesis. -/
noncomputable def averagedSliceAppendedSubMeas (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) : SubMeas (Polynomial params.next) ι :=
  postprocess family.averagedSubMeas
    (fun g => Polynomial.appendAtHeight params g zeroCoord)

/-- Placeholder family for the vertical axis-parallel line measurement `B^u_f`. -/
noncomputable def verticalLineMeasurementFamily (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) :
    IdxSubMeas (VerticalLineQuestion params) (AxisLinePolynomial params.next) ι :=
  fun u =>
    let ℓ : AxisParallelLine params.next :=
      { base := appendPoint params u zeroCoord
        direction := lastCoord params }
    (strategy.axisParallelMeasurement ℓ).toSubMeas

/-- Pull back the vertical-line answer family along `truncatePoint`, then read
its line polynomial at the lifted point's final coordinate. -/
noncomputable def liftedVerticalLineAnswerFamily
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) :
    IdxSubMeas (Point params.next) (Fq params) ι :=
  fun u =>
    postprocess
      (verticalLineMeasurementFamily params strategy (truncatePoint params u))
      (fun f => f (pointHeight params u))

/-- Explicit value extracted from the `i`-th genuine slice outcome at the test point.

The paper's one-point sandwich comparison only sums over tuples with
`g_i ≠ ⊥`; the `none` mass is therefore removed before postprocessing. -/
noncomputable def ldSandwichLineOnePointLeftFamily (params : Parameters) [FieldModel params.q]
    (_strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (k i : ℕ) : IdxSubMeas (SandwichedLineQuestion params k) (Option (Fq params)) ι :=
  fun q =>
    postprocess
      (restrictSubMeas (gHatSandwichFamily params family k q.2)
        (fun gs => if h : i < k then (gs ⟨i, h⟩).isSome = true else False))
      (fun gs => if h : i < k then Option.map (fun g => g q.1) (gs ⟨i, h⟩) else none)

/-- Explicit value extracted from the vertical line measurement `B^u` at the slice height `x_i`. -/
noncomputable def ldSandwichLineOnePointRightFamily (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (_family : IdxPolyFamily params ι)
    (k i : ℕ) : IdxSubMeas (SandwichedLineQuestion params k) (Option (Fq params)) ι :=
  fun q =>
    postprocess (verticalLineMeasurementFamily params strategy q.1) (fun f =>
      if h : i < k then
        some (f (q.2 ⟨i, h⟩))
      else
        none)

/-- Restrict a global polynomial-valued submeasurement to the vertical line through `u`. -/
noncomputable def hRestrictionToVerticalLine (params : Parameters) [FieldModel params.q]
    (H : SubMeas (Polynomial params.next) ι) :
    IdxSubMeas (VerticalLineQuestion params) (AxisLinePolynomial params.next) ι :=
  fun u =>
    let verticalLine : AxisParallelLine params.next :=
      { base := appendPoint params u zeroCoord
        direction := ⟨params.m, Nat.lt_succ_self params.m⟩ }
    postprocess H (fun h => Polynomial.restrictToAxisParallelLine params.next h verticalLine)

/-- Collapse a submeasurement to its `Unit`-valued total operator. -/
noncomputable def pastedMeasurementTotal
    {α : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]
    (H : SubMeas α ι) : IdxSubMeas Unit Unit ι :=
  constSubMeasFamily (postprocess H (fun _ => ()))

/-- The expansion over all outcome types `τ`, written as the
total mass of the averaged sandwich family restricted to `|τ| ≥ d+1`. -/
noncomputable def allOutcomesExpansionFamily (params : Parameters) [FieldModel params.q]
    (_strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι) (k : ℕ) :
    IdxSubMeas Unit Unit ι :=
  pastedMeasurementTotal (averagedEligibleSandwichSubMeas params family k)

/-- The one-outcome submeasurement whose unique effect is the Bernoulli-tail
operator of `X`. -/
noncomputable def bernoulliTailSubMeas {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k degree : ℕ) (X : MIPStarRE.Quantum.Op ι)
    (hXpsd : 0 ≤ X) (hXleOne : X ≤ 1) : SubMeas Unit ι :=
  SubMeas.singleOutcome (bernoulliTailOperator k degree X)
    (bernoulliTailOperator_nonneg k degree X hXpsd hXleOne)
    (bernoulliTailOperator_le_one k degree X hXpsd hXleOne)

@[simp] theorem bernoulliTailSubMeas_outcome {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k degree : ℕ) (X : MIPStarRE.Quantum.Op ι)
    (hXpsd : 0 ≤ X) (hXleOne : X ≤ 1) (u : Unit) :
    (bernoulliTailSubMeas k degree X hXpsd hXleOne).outcome u =
      bernoulliTailOperator k degree X :=
  rfl

@[simp] theorem bernoulliTailSubMeas_total {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k degree : ℕ) (X : MIPStarRE.Quantum.Op ι)
    (hXpsd : 0 ≤ X) (hXleOne : X ≤ 1) :
    (bernoulliTailSubMeas k degree X hXpsd hXleOne).total =
      bernoulliTailOperator k degree X :=
  rfl

/-- The Bernoulli-tail polynomial in the averaged complete operator `G = E_x \sum_g G^x_g`. -/
noncomputable def bernoulliTailFromFamily (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (k : ℕ) :
    IdxSubMeas Unit Unit ι :=
  constSubMeasFamily <|
    bernoulliTailSubMeas k params.d (IdxPolyFamily.averagedSubMeas family).total
      (IdxPolyFamily.averagedSubMeas family).total_nonneg
      (IdxPolyFamily.averagedSubMeas family).total_le_one

/-- Average the sandwiched completed-slice family over tuples whose completed/
incomplete pattern is exactly `τtail`.

This is the paper's operator
$$
\mathbb E_{x_{\ge \ell}} \sum_{g_{\ge \ell} \in \mathsf{Outcomes}_{\tau_{\ge \ell}}}
  \widehat H^{x_{\ge \ell}}_{g_{\ge \ell}},
$$
written in the existing `SubMeas Unit` API so that its total operator is the
relevant suffix-stage matrix.  Unlike the old `fromHToG` recurrence families,
this keeps the `\widehat H^{x_{\ge \ell}}_{g_{\ge \ell}}` suffix visible instead
of collapsing immediately to the full `k`-step total mass.

When this is used in `fromHToG`, the suffix length is `tailLen = k - ℓ`, and
the expectation is the paper's independent uniform average over the remaining
slice points `x_{≥ℓ}`. -/
noncomputable def averagedSandwichByTypeSubMeas (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (tailLen : ℕ) (τtail : GHatType tailLen) :
    SubMeas Unit ι :=
  open Classical in
    averageIdxSubMeas
      (uniformDistribution (PointTuple params tailLen))
      (fun xs =>
        postprocess
          (restrictSubMeas
            (gHatSandwichFamily params family tailLen xs)
            (fun gs => gs ∈ outcomesByType τtail))
          (fun _ => ()))
      (uniformDistribution_weight_sum_le_one (PointTuple params tailLen))

/-- The stage-`ℓ` suffix family from the proof of `lem:from-H-to-G`, for a fixed
remaining tail type `τ_{≥ℓ}`.

This is the operator-valued quantity displayed termwise in
`references/ldt-paper/ld-pasting.tex`, equation
`eq:i-think-this-is-what-i'm-supposed-to-prove-2` (lines 1386–1391), and in the
parallel blueprint discussion in `blueprint/src/chapter/ch09_pasting.tex`.
The parameter `prefixLen` is the Lean 0-based stage index. In the ambient
`k`-step recurrence where this family is used, the remaining tail length is
`tailLen = k - prefixLen`, so Lean stage `prefixLen` corresponds to the paper's
stage `prefixLen + 1`.

Concretely, this records
$$
\mathbb E_{x_{\ge \ell}} \sum_{g_{\ge \ell} \in \mathsf{Outcomes}_{\tau_{\ge \ell}}}
  \widehat H^{x_{\ge \ell}}_{g_{\ge \ell}} \otimes S_{\tau_{\ge \ell}}.
$$ -/
noncomputable def fromHToGTailStageFamily (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (prefixLen : ℕ)
    {tailLen : ℕ} (τtail : GHatType tailLen) :
    IdxOpFamily Unit Unit (ι × ι) :=
  fun _ =>
    let base := averagedSandwichByTypeSubMeas params family tailLen τtail
    let weight := fromHToGRecurrenceWeight params family prefixLen τtail
    { outcome := fun _ =>
        leftTensor (ι₂ := ι) base.total * rightTensor (ι₁ := ι) weight
      total := leftTensor (ι₂ := ι) base.total * rightTensor (ι₁ := ι) weight }

end MIPStarRE.LDT.Pasting


