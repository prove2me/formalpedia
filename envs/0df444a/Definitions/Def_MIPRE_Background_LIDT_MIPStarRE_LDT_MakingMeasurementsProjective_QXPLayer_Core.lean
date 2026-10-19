-- Prove2me | Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayer_Core
-- name    : MIPRE_Background_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayer_Core
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T03:14:33.029856+00:00
-- url     : https://prove2.me/theorems/2fca8ad3-c7e4-4d37-bdc6-a318814f907c
-- title:
--   Definitions of Core: Section 5 — Q/X/XHat/P core data Scalar error estimates, core data structures, and shared operator-family definitions…
-- statement:
--   The definitions of the module `MIPRE.Background.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.QXPLayer.Core` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Section 5 — Q/X/XHat/P core data. Scalar error estimates, core data structures, and shared operator-family definitions for the paper's `Q/X/XHat/P` intermediate layer.
--
--   The module is vendored read-only, with the authors' permission, from [LionSR/MIPStarRE](https://github.com/LionSR/MIPStarRE) (Sirui Lu and the MIPStarRE contributors, Apache 2.0; commit and upstream path in the file header) by `scripts/vendor-lidt.py`.
--
--   **Definitions** (15): `MIPStarRE.LDT.MakingMeasurementsProjective.PFamily` (The raw operator family `P = {P_a}`.); `MIPStarRE.LDT.MakingMeasurementsProjective.Pa` (The paper's operator `P_a = XHat† · T_a · XHat`.); `MIPStarRE.LDT.MakingMeasurementsProjective.QLayerData` (Data for the paper's intermediate `Q`-layer: the rank-reduced family `Q_a`, its total operator `Q`, and the auxiliary projective…); `MIPStarRE.LDT.MakingMeasurementsProjective.QTotal` (The paper's total operator `Q = ∑_a Q_a`.); `MIPStarRE.LDT.MakingMeasurementsProjective.QXPLayerData` (Data for the paper's `X/XHat/P` layer built on top of `Q_a` and the auxiliary projectors `T_a`.); `MIPStarRE.LDT.MakingMeasurementsProjective.QXPLayerData.ofQLayerAndSvdIdentities` (Assembles the `QXPLayerData` datum from a `Q`-layer and the SVD-derived identities.); `MIPStarRE.LDT.MakingMeasurementsProjective.Qa` (The paper's operator `Q_a`.); `MIPStarRE.LDT.MakingMeasurementsProjective.RankReductionWitness` (Paper origin: `references/ldt-paper/orthonormalization.tex:540-553` (`\label{lem:projective-low-rank-sum}`; rank-reduction lemma with…); `MIPStarRE.LDT.MakingMeasurementsProjective.RoundingToProjectorsWitness` (Paper origin: `references/ldt-paper/orthonormalization.tex:414-531` (`\label{lem:projective-non-measurement}`; full rounding-to-projectors…); `MIPStarRE.LDT.MakingMeasurementsProjective.Ta` (The paper's auxiliary projector `T_a`.); `MIPStarRE.LDT.MakingMeasurementsProjective.Xa` (The paper's matrix `X_a = T_a · X`.); and -14 more.
--
--   **Embedded lemmas** (1): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `xSquared_of_qa_eq`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Background.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.QXPLayer.Core` (`MIPRE/Background/LIDT/MIPStarRE/LDT/MakingMeasurementsProjective/QXPLayer/Core.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 33 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/LIDT/MIPStarRE/LDT/MakingMeasurementsProjective/QXPLayer/Core.lean

/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/MakingMeasurementsProjective/QXPLayer/Core.lean
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/MIPStarRE/LDT/MakingMeasurementsProjective/QXPLayer/Core.lean (definition bundle: declarations the uploaded statements rest on);
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
import Mathlib.Algebra.Field.IsField
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
import Mathlib.Algebra.Order.Monoid.Defs
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
import Mathlib.Data.Finite.Defs
import Mathlib.Data.Finite.Prod
import Mathlib.Data.Finset.Attach
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
import Mathlib.Data.Nat.Init
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Prod.Basic
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
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Logic.Basic
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Equiv.Prod
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
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Statements
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_MeasurementLift
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_Defs
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_ComparisonCore
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_DistanceBounds
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_ConsistencyBridges
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_InnerProduct
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichMain_Completeness
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Core
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_CauchySchwarz
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Projectivization
import Theorems.Thm_MIPStarRE_LDT_Measurement_sum_eq

set_option backward.isDefEq.respectTransparency false

/-!
# Section 5 — Q/X/XHat/P core data

Scalar error estimates, core data structures, and shared operator-family
definitions for the paper's `Q/X/XHat/P` intermediate layer.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT.MakingMeasurementsProjective

open MIPStarRE.LDT

noncomputable section

universe uOutcome uι

/-- The quarter-root error term `ζ^(1/4)` used throughout the paper's late-stage
orthonormalization estimates. -/
noncomputable def zetaQuarterRoot (ζ : Error) : Error :=
  Real.rpow ζ (1 / (4 : Error))

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


