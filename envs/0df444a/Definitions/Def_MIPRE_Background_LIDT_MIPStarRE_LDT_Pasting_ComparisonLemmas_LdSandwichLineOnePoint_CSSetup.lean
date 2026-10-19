-- Prove2me | Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_LdSandwichLineOnePoint_CSSetup
-- name    : MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_LdSandwichLineOnePoint_CSSetup
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T06:11:25.260114+00:00
-- url     : https://prove2.me/theorems/e37c16ba-44ea-4dda-9b58-f773ae13751c
-- title:
--   Definitions of CSSetup: Section 12 pasting: line one-point transport — Cauchy-Schwarz setup Internal helper module; part of the file-split for…
-- statement:
--   The definitions of the module `MIPRE.Background.LIDT.MIPStarRE.LDT.Pasting.ComparisonLemmas.LdSandwichLineOnePoint.CSSetup` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Section 12 pasting: line one-point transport — Cauchy-Schwarz setup. Internal helper module; part of the file-split for `#1127`.
--
--   The module is vendored read-only, with the authors' permission, from [LionSR/MIPStarRE](https://github.com/LionSR/MIPStarRE) (Sirui Lu and the MIPStarRE contributors, Apache 2.0; commit and upstream path in the file header) by `scripts/vendor-lidt.py`.
--
--   **Definitions** (23): `MIPStarRE.LDT.Pasting.LdSandwichLineOnePointAdjointRawCoreBound` (The adjoint-oriented raw commutator square-distance bound used by the two Cauchy--Schwarz applications in the proof of…); `MIPStarRE.LDT.Pasting.LdSandwichLineOnePointCSFacts` (Exact low-level facts needed to turn the generic `closenessOfIP*` lemmas into `ld-pasting.tex:964--1010` for the line-one-point statement.); `MIPStarRE.LDT.Pasting.LdSandwichLineOnePointOutcomeSumCSAbsBounds` (Absolute-value form of the two off-diagonal Cauchy--Schwarz moves.); `MIPStarRE.LDT.Pasting.LdSandwichLineOnePointOutcomeSumCSRoute` (Paper-faithful split of the remaining off-diagonal CS route.); `MIPStarRE.LDT.Pasting.ldSandwichLineOnePointAdjointRawLeftFamily` (Raw left family for the adjoint-oriented CS input, indexed by original outcomes.); `MIPStarRE.LDT.Pasting.ldSandwichLineOnePointAdjointRawRightFamily` (Raw right family for the adjoint-oriented CS input, indexed by original outcomes.); `MIPStarRE.LDT.Pasting.ldSandwichLineOnePointCS_Aord` (Raw ordered left tensor family used in the generic CS proposition.); `MIPStarRE.LDT.Pasting.ldSandwichLineOnePointCS_AordAdjointFamily` (The adjoint of the ordered raw CS family, as an indexed operator family.); `MIPStarRE.LDT.Pasting.ldSandwichLineOnePointCS_Arot` (Raw rotated left tensor family used in the generic CS proposition.); `MIPStarRE.LDT.Pasting.ldSandwichLineOnePointCS_ArotAdjointFamily` (The adjoint of the rotated raw CS family, as an indexed operator family.); and 11 more.
--
--   **Formalization Note** The bundle is the module `MIPRE.Background.LIDT.MIPStarRE.LDT.Pasting.ComparisonLemmas.LdSandwichLineOnePoint.CSSetup` (`MIPRE/Background/LIDT/MIPStarRE/LDT/Pasting/ComparisonLemmas/LdSandwichLineOnePoint/CSSetup.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 95 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/LIDT/MIPStarRE/LDT/Pasting/ComparisonLemmas/LdSandwichLineOnePoint/CSSetup.lean

/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/Pasting/ComparisonLemmas/LdSandwichLineOnePoint/CSSetup.lean
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/MIPStarRE/LDT/Pasting/ComparisonLemmas/LdSandwichLineOnePoint/CSSetup.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.Algebra.Hom
import Mathlib.Algebra.Algebra.NonUnitalHom
import Mathlib.Algebra.Algebra.Spectrum.Quasispectrum
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
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
import Mathlib.Algebra.Field.IsField
import Mathlib.Algebra.Field.Rat
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
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.Polynomial
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.Notation.Defs
import Mathlib.Algebra.Notation.Pi.Defs
import Mathlib.Algebra.Opposites
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Group.Unbundled.Basic
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.GroupWithZero.Canonical
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Algebra.Order.IsBotOne
import Mathlib.Algebra.Order.Module.Defs
import Mathlib.Algebra.Order.Monoid.Canonical.Defs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.NatCast
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.ExistsOfLE
import Mathlib.Algebra.Order.Nonneg.Basic
import Mathlib.Algebra.Order.Nonneg.Module
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Algebra.Order.Sub.Defs
import Mathlib.Algebra.Order.SuccPred
import Mathlib.Algebra.Order.ZeroLEOne
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Algebra.Ring.Commute
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Ring.Parity
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
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Complex.Trigonometric
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
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
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
import Mathlib.Data.FunLike.Embedding
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
import Mathlib.Data.Multiset.Filter
import Mathlib.Data.Multiset.MapFold
import Mathlib.Data.NNRat.Defs
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
import Mathlib.Data.Rat.Cast.CharZero
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Data.Rat.Cast.Lemmas
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Init
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Star
import Mathlib.Data.SProd
import Mathlib.Data.Set.Defs
import Mathlib.Data.SetLike.Basic
import Mathlib.Data.Subtype
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
import Mathlib.Logic.Function.Defs
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
import Mathlib.Order.Interval.Set.Defs
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.LocalRing.Defs
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.CancelDenoms.Core
import Mathlib.Tactic.FieldSimp.Lemmas
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.Linarith.Preprocessing
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Positivity.Core
import Mathlib.Tactic.Push
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
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_MainInductionStep_Defs
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_MeasurementLift
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_Defs
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_ComparisonCore
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_DistanceBounds
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_ConsistencyBridges
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_InnerProduct
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichMain_Completeness
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Core
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_CauchySchwarz
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_CompletionTransfer
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_Triangles_Core
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_LinePolynomialEmbedding
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Test_StrategyPolynomialFamilies
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Test_StrategyRole_Algebra
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Test_StrategyFailures
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Core
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_CommutativityPoints_Defs
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_Defs_Core
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_Defs_Stability
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_Defs_Normalization
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_Scaffold_Core
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_Scaffold_Products
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_CommutativityPoints_Approximation
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_EvaluatedSliceBounds_PhaseOneThree
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_EvaluatedSliceCommutation_Averages
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_Transport_EvaluationSpecialization
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_Transport_Pullback
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_Polynomials
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_PolynomialAgreement
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_Transport_FullSlice_Averages
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_Transport_FullSlice_Machinery_Marginalization_Core
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_Transport_FullSlice_Machinery_Marginalization_Y
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_Transport_FullSlice_Machinery_Normalization
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_Transport_FullSlice_Bridges_Closeness
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_Transport_FullSlice_Bridges_QSDD
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_Transport_FullSlice_ZeroBounds
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_Main_Auxiliary_HEvalTransport
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_Main_Auxiliary_ScalarMarginalization
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_CommutativityPoints_SharedHelpers_SharedLine
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_CommutativityPoints_BridgeTheorems_DropBridges
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_GCommStability_Scalar_RawSecond
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_ScalarApproximation_PaperChainPhaseFive
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_GCommStability_Scalar_First
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_ScalarApproximation_ProcessedG_PhaseTwo
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Commutativity_ScalarApproximation_ProcessedG_MainChain
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_Defs_Tuples
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_Defs_Interpolation
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_Defs_Families
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_Sandwich_Switcheroo
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_Sandwich_GHatSandwich
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_Sandwich_PastedFamilies
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_Statements
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_SwitcherooSetup_Centers
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_SwitcherooSetup_Terms
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_SwitcherooContraction_Split
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_SwitcherooContraction_ScalarTerms
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_SwitcherooCompletion
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_CommutingWithG_Complete
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_GHatFacts
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_CommuteGHalfSandwich_Setup_Definitions
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_CommuteGHalfSandwich_Setup_StepLemmas_Split
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_CommuteGHalfSandwich_MoveChain_Base
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_CommuteGHalfSandwich_MoveChain_Lifting
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_CommuteGHalfSandwich_MoveChain_Chain
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_CommuteGHalfSandwich_MoveChain_FlatChain
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_CommuteGHalfSandwich_MoveChain_BackChain
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_LdSandwichLineOnePoint_EndpointEquivs
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_Core_LdGbcon
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_LdSandwichLineOnePoint_Endpoint
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_ComparisonLemmas_LdSandwichLineOnePoint_PrefixMoved

set_option backward.isDefEq.respectTransparency false

/-!
# Section 12 pasting: line one-point transport — Cauchy-Schwarz setup

Internal helper module; part of the file-split for `#1127`.

## References

- `references/ldt-paper/ld-pasting.tex`
- `blueprint/src/chapter/ch09_pasting.tex`
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The linear (pre-`max`) form of the bipartite consistency defect.

Internal helper for the `LdSandwichLineOnePoint` Cauchy--Schwarz setup;
exposed for a future file-split (`#1127`). -/
noncomputable def qBipartiteLinearConsDefect {Outcome : Type*}
    {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype Outcome]
    (ψ : QuantumState (ιA × ιB))
    (A : SubMeas Outcome ιA) (B : SubMeas Outcome ιB) : Error :=
  ev ψ (opTensor A.total B.total) - qBipartiteMatchMass ψ A B

/-- The original expanded off-diagonal scalar in `ld-pasting.tex:960--963`.

This is the source side after deleting extraneous tail coordinates and expanding
the linear consistency defect as `Σ_a ⟨ψ|A_a ⊗ (I-B_a)|ψ⟩`. -/
noncomputable def ldSandwichLineOnePoint_prefix_sourceOutcomeSum
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    {k i : ℕ} (hi : i < k) : Error :=
  avgOver (uniformDistribution (SandwichedLineQuestion params k)) (fun q =>
    ∑ a : Fq params,
      ev strategy.state
        (opTensor
          (((ldSandwichLineOnePointPrefixOriginalFamily params family hi) q).outcome
            (some a))
          (1 - ((ldSandwichLineOnePointRightFamily params strategy family k i) q).outcome
            (some a))))

/-- The intermediate scalar after the first Cauchy--Schwarz move
`ld-pasting.tex:964--986` (`eq:gonna-need-a-bigger-cauchy-schwarz`).

For an original-order prefix outcome `gs`, `orderedHalf` is
`G^{x_<i}_{g_<i} G^{x_i}_{g_i}` while `rotatedHalf` is
`G^{x_i}_{g_i} G^{x_<i}_{g_<i}`.  The first CS move replaces only the left half
of the sandwich, leaving `orderedHalf†` on the right. -/
noncomputable def ldSandwichLineOnePoint_prefix_afterFirstCSOutcomeSum
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    {k i : ℕ} (hi : i < k) : Error :=
  avgOver (uniformDistribution (SandwichedLineQuestion params k)) (fun q =>
    ∑ gs : GHatTupleOutcome params (i + 1),
      match Option.map (fun g : Polynomial params => g q.1)
          (gs ⟨i, Nat.lt_succ_self i⟩) with
      | none => 0
      | some a =>
          let orderedHalf := gHatHalfProductOutcomeOperator params family (i + 1)
            (fun j => q.2 ⟨j.1, by omega⟩) gs
          let rotatedHalf := gHatHalfProductOutcomeOperator params family (i + 1)
            ((pointTupleLastFrontEquiv params i) (fun j => q.2 ⟨j.1, by omega⟩))
            ((gHatTupleOutcomeLastFrontEquiv params i) gs)
          ev strategy.state
            (opTensor (rotatedHalf * orderedHalfᴴ)
              (1 - ((ldSandwichLineOnePointRightFamily params strategy family k i) q).outcome
                (some a))))

/-- The target expanded off-diagonal scalar after the two CS moves.

This is the moved-prefix side.  The separate endpoint/prefix-completeness
collapse to `ldGbcon` is the already-proved
`ldSandwichLineOnePointPrefixMoved_eq_endpoint`, corresponding to
`ld-pasting.tex:1011--1024`. -/
noncomputable def ldSandwichLineOnePoint_prefix_movedOutcomeSum
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    {k i : ℕ} (hi : i < k) : Error :=
  avgOver (uniformDistribution (SandwichedLineQuestion params k)) (fun q =>
    ∑ a : Fq params,
      ev strategy.state
        (opTensor
          (((ldSandwichLineOnePointPrefixMovedFamily params family hi) q).outcome
            (some a))
          (1 - ((ldSandwichLineOnePointRightFamily params strategy family k i) q).outcome
            (some a))))

/-- Paper-faithful split of the remaining off-diagonal CS route.

The fields isolate the two uses of `Preliminaries.closenessOfIP` /
`Preliminaries.closenessOfIPAdjoint` in `ld-pasting.tex:964--1010`.  The endpoint
collapse after these fields is already packaged by
`ldSandwichLineOnePointPrefixMoved_eq_endpoint` (`ld-pasting.tex:1011--1024`). -/
structure LdSandwichLineOnePointOutcomeSumCSRoute
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (gamma zeta : Error)
    {k i : ℕ} (hi : i < k) : Prop where
  /-- First CS move, paper lines `964--986` and label
  `eq:gonna-need-a-bigger-cauchy-schwarz`: move the selected `G` to the left of
  the prefix in the left half of the sandwich. -/
  firstCauchySchwarz :
    ldSandwichLineOnePoint_prefix_sourceOutcomeSum params strategy family hi ≤
      ldSandwichLineOnePoint_prefix_afterFirstCSOutcomeSum params strategy family hi +
        Real.sqrt (commuteGHalfSandwichError params gamma zeta (i + 1))
  /-- Second CS move, paper lines `987--1010` and label `eq:even-bigger-CS`:
  move the selected `G` through the adjoint/right half, reaching the moved-prefix
  scalar. -/
  secondCauchySchwarz :
    ldSandwichLineOnePoint_prefix_afterFirstCSOutcomeSum params strategy family hi ≤
      ldSandwichLineOnePoint_prefix_movedOutcomeSum params strategy family hi +
        Real.sqrt (commuteGHalfSandwichError params gamma zeta (i + 1))

/-- Absolute-value form of the two off-diagonal Cauchy--Schwarz moves.

This is the direct output shape of `Preliminaries.closenessOfIPAdjoint` and
`Preliminaries.closenessOfIP`: each field compares the two adjacent scalar
averages from `ld-pasting.tex:964--1010` with error `√ν₄`.  The one-sided route
used downstream is only an arithmetic consequence of these absolute-value
bounds. -/
structure LdSandwichLineOnePointOutcomeSumCSAbsBounds
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (gamma zeta : Error)
    {k i : ℕ} (hi : i < k) : Prop where
  /-- First CS move in the exact absolute-value form of `prop:closeness-of-ip`,
  paper lines `964--986` and label `eq:gonna-need-a-bigger-cauchy-schwarz`. -/
  firstAbs :
    |ldSandwichLineOnePoint_prefix_sourceOutcomeSum params strategy family hi -
      ldSandwichLineOnePoint_prefix_afterFirstCSOutcomeSum params strategy family hi| ≤
      Real.sqrt (commuteGHalfSandwichError params gamma zeta (i + 1))
  /-- Second CS move in the exact absolute-value form of `prop:closeness-of-ip`,
  paper lines `987--1010` and label `eq:even-bigger-CS`. -/
  secondAbs :
    |ldSandwichLineOnePoint_prefix_afterFirstCSOutcomeSum params strategy family hi -
      ldSandwichLineOnePoint_prefix_movedOutcomeSum params strategy family hi| ≤
      Real.sqrt (commuteGHalfSandwichError params gamma zeta (i + 1))

/-- Ordered half-product appearing in the line-one-point CS step. -/
noncomputable def ldSandwichLineOnePointCS_orderedHalf
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    {k i : ℕ} (hi : i < k)
    (q : SandwichedLineQuestion params k)
    (gs : GHatTupleOutcome params (i + 1)) : MIPStarRE.Quantum.Op ι :=
  gHatHalfProductOutcomeOperator params family (i + 1)
    (fun j => q.2 ⟨j.1, by omega⟩) gs

/-- Rotated half-product appearing after moving the selected slice to the front. -/
noncomputable def ldSandwichLineOnePointCS_rotatedHalf
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    {k i : ℕ} (hi : i < k)
    (q : SandwichedLineQuestion params k)
    (gs : GHatTupleOutcome params (i + 1)) : MIPStarRE.Quantum.Op ι :=
  gHatHalfProductOutcomeOperator params family (i + 1)
    ((pointTupleLastFrontEquiv params i) (fun j => q.2 ⟨j.1, by omega⟩))
    ((gHatTupleOutcomeLastFrontEquiv params i) gs)

/-- Right-hand complement selected by the completed polynomial outcome. -/
noncomputable def ldSandwichLineOnePointCS_rightComplement
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    {k i : ℕ}
    (q : SandwichedLineQuestion params k)
    (gs : GHatTupleOutcome params (i + 1)) : MIPStarRE.Quantum.Op ι :=
  match Option.map (fun g : Polynomial params => g q.1)
      (gs ⟨i, Nat.lt_succ_self i⟩) with
  | none => 0
  | some a =>
      1 - ((ldSandwichLineOnePointRightFamily params strategy family k i) q).outcome (some a)

/-- Raw ordered left tensor family used in the generic CS proposition. -/
noncomputable def ldSandwichLineOnePointCS_Aord
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    {k i : ℕ} (hi : i < k) :
    SandwichedLineQuestion params k → GHatTupleOutcome params (i + 1) →
      MIPStarRE.Quantum.Op (ι × ι) := fun q gs =>
  leftTensor (ι₂ := ι) (ldSandwichLineOnePointCS_orderedHalf params family hi q gs)

/-- Raw rotated left tensor family used in the generic CS proposition. -/
noncomputable def ldSandwichLineOnePointCS_Arot
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    {k i : ℕ} (hi : i < k) :
    SandwichedLineQuestion params k → GHatTupleOutcome params (i + 1) →
      MIPStarRE.Quantum.Op (ι × ι) := fun q gs =>
  leftTensor (ι₂ := ι) (ldSandwichLineOnePointCS_rotatedHalf params family hi q gs)

/-- The adjoint of the ordered raw CS family, as an indexed operator family. -/
noncomputable def ldSandwichLineOnePointCS_AordAdjointFamily
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    {k i : ℕ} (hi : i < k) :
    IdxOpFamily (SandwichedLineQuestion params k)
      (GHatTupleOutcome params (i + 1)) (ι × ι) :=
  fun q =>
    { outcome := fun gs =>
        (ldSandwichLineOnePointCS_Aord params family hi q gs)ᴴ
      total := 0 }

/-- The adjoint of the rotated raw CS family, as an indexed operator family. -/
noncomputable def ldSandwichLineOnePointCS_ArotAdjointFamily
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    {k i : ℕ} (hi : i < k) :
    IdxOpFamily (SandwichedLineQuestion params k)
      (GHatTupleOutcome params (i + 1)) (ι × ι) :=
  fun q =>
    { outcome := fun gs =>
        (ldSandwichLineOnePointCS_Arot params family hi q gs)ᴴ
      total := 0 }

/-- Raw left family for the adjoint-oriented CS input, indexed by original outcomes. -/
noncomputable def ldSandwichLineOnePointAdjointRawLeftFamily
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    {k i : ℕ} (_hi : i < k) :
    IdxOpFamily (SandwichedLineQuestion params k) (GHatTupleOutcome params (i + 1)) (ι × ι) :=
  fun q =>
    { outcome := fun gs =>
        (gHatHalfSandwichLeft params family (i + 1)
          ((pointTupleLastReverseEquiv params i) (fun j => q.2 ⟨j.1, by omega⟩))).outcome
          ((gHatTupleOutcomeLastReverseEquiv params i) gs)
      total := (gHatHalfSandwichLeft params family (i + 1)
        ((pointTupleLastReverseEquiv params i) (fun j => q.2 ⟨j.1, by omega⟩))).total }

/-- Raw right family for the adjoint-oriented CS input, indexed by original outcomes. -/
noncomputable def ldSandwichLineOnePointAdjointRawRightFamily
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    {k i : ℕ} (_hi : i < k) :
    IdxOpFamily (SandwichedLineQuestion params k) (GHatTupleOutcome params (i + 1)) (ι × ι) :=
  fun q =>
    { outcome := fun gs =>
        (gHatHalfSandwichRight params family (i + 1)
          ((pointTupleLastReverseEquiv params i) (fun j => q.2 ⟨j.1, by omega⟩))).outcome
          ((gHatTupleOutcomeLastReverseEquiv params i) gs)
      total := (gHatHalfSandwichRight params family (i + 1)
        ((pointTupleLastReverseEquiv params i) (fun j => q.2 ⟨j.1, by omega⟩))).total }

/-- The $C$ family for the first, right-action CS move. -/
noncomputable def ldSandwichLineOnePointCS_Cfirst
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    {k i : ℕ} (hi : i < k) :
    SandwichedLineQuestion params k → GHatTupleOutcome params (i + 1) → Unit →
      MIPStarRE.Quantum.Op (ι × ι) := fun q gs _ =>
  opTensor (ldSandwichLineOnePointCS_orderedHalf params family hi q gs)ᴴ
    (ldSandwichLineOnePointCS_rightComplement params strategy family q gs)

/-- The $C$ family for the second, left-action CS move. -/
noncomputable def ldSandwichLineOnePointCS_Csecond
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    {k i : ℕ} (hi : i < k) :
    SandwichedLineQuestion params k → GHatTupleOutcome params (i + 1) → Unit →
      MIPStarRE.Quantum.Op (ι × ι) := fun q gs _ =>
  opTensor (ldSandwichLineOnePointCS_rotatedHalf params family hi q gs)
    (ldSandwichLineOnePointCS_rightComplement params strategy family q gs)

/-- Raw scalar on the source side of the first CS application. -/
noncomputable def ldSandwichLineOnePointCS_firstSourceRaw
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    {k i : ℕ} (hi : i < k) : Error :=
  avgOver (uniformDistribution (SandwichedLineQuestion params k)) (fun q =>
    ∑ gs : GHatTupleOutcome params (i + 1), ∑ u : Unit,
      ev strategy.state
        (ldSandwichLineOnePointCS_Aord params family hi q gs *
          ldSandwichLineOnePointCS_Cfirst params strategy family hi q gs u))

/-- Raw scalar on the target side of the first CS application. -/
noncomputable def ldSandwichLineOnePointCS_firstTargetRaw
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    {k i : ℕ} (hi : i < k) : Error :=
  avgOver (uniformDistribution (SandwichedLineQuestion params k)) (fun q =>
    ∑ gs : GHatTupleOutcome params (i + 1), ∑ u : Unit,
      ev strategy.state
        (ldSandwichLineOnePointCS_Arot params family hi q gs *
          ldSandwichLineOnePointCS_Cfirst params strategy family hi q gs u))

/-- Raw scalar on the source side of the second CS application. -/
noncomputable def ldSandwichLineOnePointCS_secondSourceRaw
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    {k i : ℕ} (hi : i < k) : Error :=
  avgOver (uniformDistribution (SandwichedLineQuestion params k)) (fun q =>
    ∑ gs : GHatTupleOutcome params (i + 1), ∑ u : Unit,
      ev strategy.state
        (ldSandwichLineOnePointCS_Csecond params strategy family hi q gs u *
          (ldSandwichLineOnePointCS_Aord params family hi q gs)ᴴ))

/-- Raw scalar on the target side of the second CS application. -/
noncomputable def ldSandwichLineOnePointCS_secondTargetRaw
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    {k i : ℕ} (hi : i < k) : Error :=
  avgOver (uniformDistribution (SandwichedLineQuestion params k)) (fun q =>
    ∑ gs : GHatTupleOutcome params (i + 1), ∑ u : Unit,
      ev strategy.state
        (ldSandwichLineOnePointCS_Csecond params strategy family hi q gs u *
          (ldSandwichLineOnePointCS_Arot params family hi q gs)ᴴ))

/-- Exact low-level facts needed to turn the generic `closenessOfIP*` lemmas into
`ld-pasting.tex:964--1010` for the line-one-point statement.

This record separates the generic CS theorem instantiation (proved below) from
the paper-specific facts:

* the adjoint-oriented raw square-distance bound corresponding to the first square
  root in lines 974--985 and reused in lines 1005--1010;
* the two unit-side measurement-completeness bounds from lines 986 and 1008;
* the algebraic regrouping/reindexing that identifies the raw CS scalars with the
  existing source, intermediate, and moved outcome sums.

The construction lemma below proves the unit bounds and regrouping equalities;
the remaining live analytic endpoint is the adjoint-oriented raw-core estimate
recorded by `LdSandwichLineOnePointAdjointRawCoreBound`. -/
structure LdSandwichLineOnePointCSFacts
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (gamma zeta : Error)
    {k i : ℕ} (hi : i < k) : Prop where
  adjointRawCore :
    avgOver (uniformDistribution (SandwichedLineQuestion params k))
      (fun q => qSDDCore strategy.state
        (fun gs : GHatTupleOutcome params (i + 1) =>
          (ldSandwichLineOnePointCS_Aord params family hi q gs)ᴴ)
        (fun gs : GHatTupleOutcome params (i + 1) =>
          (ldSandwichLineOnePointCS_Arot params family hi q gs)ᴴ)) ≤
      commuteGHalfSandwichError params gamma zeta (i + 1)
  firstUnitBound :
    ∀ q, ∑ gs : GHatTupleOutcome params (i + 1),
      (∑ u : Unit, ldSandwichLineOnePointCS_Cfirst params strategy family hi q gs u)ᴴ *
        (∑ u : Unit, ldSandwichLineOnePointCS_Cfirst params strategy family hi q gs u) ≤ 1
  secondUnitBound :
    ∀ q, ∑ gs : GHatTupleOutcome params (i + 1),
      (∑ u : Unit, ldSandwichLineOnePointCS_Csecond params strategy family hi q gs u) *
        (∑ u : Unit, ldSandwichLineOnePointCS_Csecond params strategy family hi q gs u)ᴴ ≤ 1
  source_eq_firstSourceRaw :
    ldSandwichLineOnePoint_prefix_sourceOutcomeSum params strategy family hi =
      ldSandwichLineOnePointCS_firstSourceRaw params strategy family hi
  afterFirst_eq_firstTargetRaw :
    ldSandwichLineOnePoint_prefix_afterFirstCSOutcomeSum params strategy family hi =
      ldSandwichLineOnePointCS_firstTargetRaw params strategy family hi
  afterFirst_eq_secondSourceRaw :
    ldSandwichLineOnePoint_prefix_afterFirstCSOutcomeSum params strategy family hi =
      ldSandwichLineOnePointCS_secondSourceRaw params strategy family hi
  moved_eq_secondTargetRaw :
    ldSandwichLineOnePoint_prefix_movedOutcomeSum params strategy family hi =
      ldSandwichLineOnePointCS_secondTargetRaw params strategy family hi

/-- The adjoint-oriented raw commutator square-distance bound used by the two
Cauchy--Schwarz applications in the proof of `lem:ld-sandwich-line-one-point`.

The surrounding endpoint expansions and option-valued match-mass identities are
proved directly where they are used; this structure records only the nontrivial
orientation of the half-sandwich commutation estimate. -/
structure LdSandwichLineOnePointAdjointRawCoreBound
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (gamma zeta : Error)
    {k i : ℕ} (hi : i < k) : Prop where
  bound :
    avgOver (uniformDistribution (SandwichedLineQuestion params k))
      (fun q => qSDDCore strategy.state
        (fun gs : GHatTupleOutcome params (i + 1) =>
          (ldSandwichLineOnePointCS_Aord params family hi q gs)ᴴ)
        (fun gs : GHatTupleOutcome params (i + 1) =>
          (ldSandwichLineOnePointCS_Arot params family hi q gs)ᴴ)) ≤
      commuteGHalfSandwichError params gamma zeta (i + 1)

end MIPStarRE.LDT.Pasting


