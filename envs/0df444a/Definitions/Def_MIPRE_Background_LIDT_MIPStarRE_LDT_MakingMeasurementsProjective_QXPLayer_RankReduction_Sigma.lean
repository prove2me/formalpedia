-- Prove2me | Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayer_RankReduction_Sigma
-- name    : MIPRE_Background_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayer_RankReduction_Sigma
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T03:16:00.553022+00:00
-- url     : https://prove2.me/theorems/0119edf6-6b1b-4691-8f30-14726302c6ac
-- title:
--   Definitions of Sigma: Section 5 — Q/X/XHat/P rank reduction Sigma-space projectors and rank-reduction lemmas for the paper's `Q/X/XHat/P`…
-- statement:
--   The definitions of the module `MIPRE.Background.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.QXPLayer.RankReduction.Sigma` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Section 5 — Q/X/XHat/P rank reduction. Sigma-space projectors and rank-reduction lemmas for the paper's `Q/X/XHat/P` intermediate layer.
--
--   The module is vendored read-only, with the authors' permission, from [LionSR/MIPStarRE](https://github.com/LionSR/MIPStarRE) (Sirui Lu and the MIPStarRE contributors, Apache 2.0; commit and upstream path in the file header) by `scripts/vendor-lidt.py`.
--
--   **Definitions** (11): `MIPStarRE.LDT.MakingMeasurementsProjective.FiniteHilbertSpace.sigmaFin` (The finite Hilbert space whose preferred basis is a lifted finite-enumeration model of `Σ a, Fin (m a)`.); `MIPStarRE.LDT.MakingMeasurementsProjective.FiniteHilbertSpace.sigmaFinCarrier` (A chosen finite-enumeration model of the paper's carrier `Σ a, Fin (m a)`.); `MIPStarRE.LDT.MakingMeasurementsProjective.FiniteHilbertSpace.sigmaFinLift` (The lifted sigma carrier used as the auxiliary Hilbert-space basis for `sigmaFin`.); `MIPStarRE.LDT.MakingMeasurementsProjective.QXPLayerData.ofSigmaRangeAndSvdIdentities` (Assemble `QXPLayerData` from the canonical sigma-space embedding and the remaining SVD/polar identities for `Xhat`.); `MIPStarRE.LDT.MakingMeasurementsProjective.pointProjMeas` (A one-point projective measurement concentrating all mass on the chosen outcome.); `MIPStarRE.LDT.MakingMeasurementsProjective.sigmaFinProjMeas` (The block projective measurement on the lifted finite-enumeration model of `Σ a, Fin (m a)` selecting the `a`-block.); `MIPStarRE.LDT.MakingMeasurementsProjective.sigmaFinRangeEmbedding` (The matrix `X` associated to a projective family on the sigma auxiliary space.); `MIPStarRE.LDT.MakingMeasurementsProjective.sigmaRangeCarrier` (The lifted sigma carrier associated to the ranks of an operator family.); `MIPStarRE.LDT.MakingMeasurementsProjective.sigmaRangeQLayer` (The finite-enumeration `Q` layer associated to an operator family.); and -7 more.
--
--   **Embedded lemmas** (1): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `sigmaFinRangeEmbedding_qa_eq`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Background.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.QXPLayer.RankReduction.Sigma` (`MIPRE/Background/LIDT/MIPStarRE/LDT/MakingMeasurementsProjective/QXPLayer/RankReduction/Sigma.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 36 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/LIDT/MIPStarRE/LDT/MakingMeasurementsProjective/QXPLayer/RankReduction/Sigma.lean

/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/MakingMeasurementsProjective/QXPLayer/RankReduction/Sigma.lean
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/MIPStarRE/LDT/MakingMeasurementsProjective/QXPLayer/RankReduction/Sigma.lean (definition bundle: declarations the uploaded statements rest on);
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
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Action.Pi
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Commute.Defs
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Finsupp
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Idempotent
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
import Mathlib.Algebra.Ring.CompTypeclasses
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
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
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
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
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
import Mathlib.Data.Fintype.Sigma
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
import Mathlib.Data.Sigma.Basic
import Mathlib.Data.ULift
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
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayer_Core
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_CompletionTransfer
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_Quantum_ProjectorONB

set_option backward.isDefEq.respectTransparency false

/-!
# Section 5 — Q/X/XHat/P rank reduction

Sigma-space projectors and rank-reduction lemmas for the paper's `Q/X/XHat/P`
intermediate layer.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT.MakingMeasurementsProjective

open MIPStarRE.LDT

noncomputable section

universe uOutcome uι

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
noncomputable def sigmaFinCarrierEquiv {Outcome : Type*} [Fintype Outcome]
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
              simpa [Equiv.ulift] using
                (Equiv.sum_comp (Equiv.ulift : ULift.{uι} S ≃ S)
                  (fun x : S =>
                    if x.1 = e a then
                      (onb (e.symm x.1)).vec x.2 i *
                        star ((onb (e.symm x.1)).vec x.2 j)
                    else 0))
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

end

end MIPStarRE.LDT.MakingMeasurementsProjective


