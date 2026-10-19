-- Prove2me | Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Projectivization
-- name    : MIPRE_Background_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Projectivization
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T03:13:11.277335+00:00
-- url     : https://prove2.me/theorems/73175641-fb01-461e-9c57-df66ef17935f
-- title:
--   Definitions of Projectivization: Section 5 — Rounding To Projectors Core Internal lemmas for the orthogonalization and rounding-to-projectors chain
-- statement:
--   The definitions of the module `MIPRE.Background.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.Projectivization` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Section 5 — Rounding To Projectors Core. Internal lemmas for the orthogonalization and rounding-to-projectors chain. This file extracts the consistency-to-almost-projective and spectral/rounding steps so that `QXPLayer.lean` can depend on them without importing the full Section 5 theorem file.
--
--   The module is vendored read-only, with the authors' permission, from [LionSR/MIPStarRE](https://github.com/LionSR/MIPStarRE) (Sirui Lu and the MIPStarRE contributors, Apache 2.0; commit and upstream path in the file header) by `scripts/vendor-lidt.py`.
--
--   **Definitions** (1): `MIPStarRE.LDT.MakingMeasurementsProjective.zeroProjSubMeas` (The zero family is a projective submeasurement.).
--
--   **Embedded lemmas** (10): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `abs_sum_ev_opTensor_le_sqrt_mul_sqrt`, `leftTensor_outcome_mul_conjTranspose_eq`, `qSSCDefect_leftPlacedMeasurement_le_two_qBipartiteConsDefect`, `qSSCDefect_rightPlacedMeasurement_le_two_qBipartiteConsDefect`, `rightTensor_outcome_conjTranspose_mul_eq`, `sourceAlmostProjective_of_ssc`, `sum_ev_leftTensor_outcome_sq_nonneg`, `sum_ev_opTensor_outcome_le_totalMass`, `sum_ev_rightTensor_outcome_sq_nonneg`, `totalMass_sub_two_defect_le_diagA`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Background.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.Projectivization` (`MIPRE/Background/LIDT/MIPStarRE/LDT/MakingMeasurementsProjective/Projectivization.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 32 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/LIDT/MIPStarRE/LDT/MakingMeasurementsProjective/Projectivization.lean

/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/MakingMeasurementsProjective/Projectivization.lean
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/MIPStarRE/LDT/MakingMeasurementsProjective/Projectivization.lean (definition bundle: declarations the uploaded statements rest on);
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
import Theorems.Thm_MIPStarRE_LDT_Measurement_outcome_le_one
import Theorems.Thm_MIPStarRE_LDT_Preliminaries_subMeas_diagMass_le_mass
import Theorems.Thm_MIPStarRE_LDT_SubMeas_outcome_hermitian
import Theorems.Thm_MIPStarRE_LDT_ev_adjoint_self_nonneg
import Theorems.Thm_MIPStarRE_LDT_ev_mono
import Theorems.Thm_MIPStarRE_LDT_ev_sub
import Theorems.Thm_MIPStarRE_LDT_ev_sum
import Theorems.Thm_MIPStarRE_LDT_leftTensor_finset_sum
import Theorems.Thm_MIPStarRE_LDT_leftTensor_mul_leftTensor
import Theorems.Thm_MIPStarRE_LDT_leftTensor_mul_rightTensor_eq_opTensor
import Theorems.Thm_MIPStarRE_LDT_leftTensor_one
import Theorems.Thm_MIPStarRE_LDT_opTensor_le_leftTensor
import Theorems.Thm_MIPStarRE_LDT_qBipartiteConsDefect_nonneg
import Theorems.Thm_MIPStarRE_LDT_rightTensor_mul_rightTensor
import Theorems.Thm_MIPStarRE_LDT_rightTensor_one

set_option backward.isDefEq.respectTransparency false

/-!
# Section 5 — Rounding To Projectors Core

Internal lemmas for the orthogonalization and rounding-to-projectors chain.

This file extracts the consistency-to-almost-projective and spectral/rounding
steps so that `QXPLayer.lean` can depend on them without importing the full
Section 5 theorem file.

## References

- `references/ldt-paper/orthonormalization.tex`
- `blueprint/src/chapter/ch04_projective.tex`
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT.MakingMeasurementsProjective

open MIPStarRE.LDT

/-! ### Orthonormalization helper lemmas -/

/-- `leftTensor (A_a) * (leftTensor (A_a))ᴴ = leftTensor (A_a * A_a)` for Hermitian outcomes. -/
lemma leftTensor_outcome_mul_conjTranspose_eq
    {Outcome : Type*} {ιA ιB : Type*} [Fintype Outcome]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (A : SubMeas Outcome ιA) (a : Outcome) :
    leftTensor (ι₂ := ιB) (A.outcome a) *
        (leftTensor (ι₂ := ιB) (A.outcome a))ᴴ =
      leftTensor (ι₂ := ιB) (A.outcome a * A.outcome a) := by
  rw [leftTensor_conjTranspose, A.outcome_hermitian, leftTensor_mul_leftTensor]

/-- The right-tensor analogue of
`leftTensor_outcome_mul_conjTranspose_eq`. -/
lemma rightTensor_outcome_conjTranspose_mul_eq
    {Outcome : Type*} {ιA ιB : Type*} [Fintype Outcome]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (B : SubMeas Outcome ιB) (a : Outcome) :
    (rightTensor (ι₁ := ιA) (B.outcome a))ᴴ *
        rightTensor (ι₁ := ιA) (B.outcome a) =
      rightTensor (ι₁ := ιA) (B.outcome a * B.outcome a) := by
  rw [rightTensor_conjTranspose, B.outcome_hermitian, rightTensor_mul_rightTensor]

/-- Cauchy–Schwarz bound for the sum `∑_a ⟨ψ | A_a ⊗ B_a | ψ⟩`, expressed in
terms of the left/right diagonal masses. -/
lemma abs_sum_ev_opTensor_le_sqrt_mul_sqrt
    {Outcome : Type*} {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype Outcome]
    (ψ : QuantumState (ιA × ιB))
    (A : SubMeas Outcome ιA) (B : SubMeas Outcome ιB) :
    |∑ a : Outcome, ev ψ (opTensor (A.outcome a) (B.outcome a))| ≤
      Real.sqrt
          (∑ a : Outcome,
            ev ψ (leftTensor (ι₂ := ιB) (A.outcome a * A.outcome a))) *
        Real.sqrt
          (∑ a : Outcome,
            ev ψ (rightTensor (ι₁ := ιA) (B.outcome a * B.outcome a))) := by
  have hX := fun a : Outcome =>
    leftTensor_outcome_mul_conjTranspose_eq (ιB := ιB) A a
  have hY := fun a : Outcome =>
    rightTensor_outcome_conjTranspose_mul_eq (ιA := ιA) B a
  simpa [leftTensor_mul_rightTensor_eq_opTensor, hX, hY,
      -leftTensor_conjTranspose, -rightTensor_conjTranspose] using
    MIPStarRE.LDT.Preliminaries.sum_ev_mul_le_sqrt ψ
      (fun a => leftTensor (ι₂ := ιB) (A.outcome a))
      (fun a => rightTensor (ι₁ := ιA) (B.outcome a))

/-- The `diagA` sum (in terms of `leftTensor (A_a * A_a)`) is nonnegative. -/
lemma sum_ev_leftTensor_outcome_sq_nonneg
    {Outcome : Type*} {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype Outcome]
    (ψ : QuantumState (ιA × ιB)) (A : SubMeas Outcome ιA) :
    0 ≤ ∑ a : Outcome,
          ev ψ (leftTensor (ι₂ := ιB) (A.outcome a * A.outcome a)) := by
  refine Finset.sum_nonneg fun a _ => ?_
  have h := ev_adjoint_self_nonneg ψ (leftTensor (ι₂ := ιB) (A.outcome a))
  rwa [leftTensor_conjTranspose, A.outcome_hermitian, leftTensor_mul_leftTensor] at h

/-- The `diagB` sum (in terms of `rightTensor (B_a * B_a)`) is nonnegative. -/
lemma sum_ev_rightTensor_outcome_sq_nonneg
    {Outcome : Type*} {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype Outcome]
    (ψ : QuantumState (ιA × ιB)) (B : SubMeas Outcome ιB) :
    0 ≤ ∑ a : Outcome,
          ev ψ (rightTensor (ι₁ := ιA) (B.outcome a * B.outcome a)) := by
  refine Finset.sum_nonneg fun a _ => ?_
  rw [← rightTensor_outcome_conjTranspose_mul_eq (ιA := ιA) B a]
  exact ev_adjoint_self_nonneg ψ (rightTensor (ι₁ := ιA) (B.outcome a))

/-- Bound the overlap sum `∑_a ⟨ψ | A_a ⊗ B_a | ψ⟩` by the total mass
`⟨ψ | 1 | ψ⟩` using `B.outcome a ≤ 1` and `A`'s completeness. -/
lemma sum_ev_opTensor_outcome_le_totalMass
    {Outcome : Type*} {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype Outcome]
    (ψ : QuantumState (ιA × ιB))
    (A : Measurement Outcome ιA) (B : Measurement Outcome ιB) :
    ∑ a : Outcome, ev ψ (opTensor (A.outcome a) (B.outcome a)) ≤
      ev ψ (1 : MIPStarRE.Quantum.Op (ιA × ιB)) := by
  have hleft_one :
      ev ψ (leftTensor (ι₂ := ιB) (1 : MIPStarRE.Quantum.Op ιA)) =
        ev ψ (1 : MIPStarRE.Quantum.Op (ιA × ιB)) := by
    simpa using congrArg (ev ψ) (leftTensor_one (ι₁ := ιA) (ι₂ := ιB))
  calc
    ∑ a : Outcome, ev ψ (opTensor (A.outcome a) (B.outcome a))
      ≤ ∑ a : Outcome, ev ψ (leftTensor (ι₂ := ιB) (A.outcome a)) := by
          refine Finset.sum_le_sum ?_
          intro a _
          exact ev_mono ψ _ _ <|
            opTensor_le_leftTensor (ι₂ := ιB)
              (A.outcome_pos a) (Measurement.outcome_le_one B a)
    _ = ev ψ (leftTensor (ι₂ := ιB) A.total) := by
          rw [← ev_sum ψ (fun a : Outcome => leftTensor (ι₂ := ιB) (A.outcome a))]
          rw [leftTensor_finset_sum (ι₂ := ιB) Finset.univ A.outcome]
          simp [A.sum_eq_total]
    _ = ev ψ (leftTensor (ι₂ := ιB) (1 : MIPStarRE.Quantum.Op ιA)) := by
          rw [A.total_eq_one]
    _ = ev ψ (1 : MIPStarRE.Quantum.Op (ιA × ιB)) := hleft_one

/-- Lower bound for the `diagA` sum in terms of the overlap and the bipartite
consistency defect, obtained from the Cauchy–Schwarz squared bound. -/
lemma totalMass_sub_two_defect_le_diagA
    {diagA diagB totalMass defect overlap : Error}
    (hdiagA_nonneg : 0 ≤ diagA)
    (hdefect_nonneg : 0 ≤ defect)
    (hdefect_eq : defect = totalMass - overlap)
    (hoverlap_sq : overlap ^ 2 ≤ diagA * diagB)
    (hdiagB_le : diagB ≤ totalMass) :
    totalMass - 2 * defect ≤ diagA := by
  by_cases hsmall : totalMass ≤ defect
  · linarith
  · have hmass_pos : 0 < totalMass := by
      have hdefect_lt : defect < totalMass := lt_of_not_ge hsmall
      linarith
    have hoverlap_eq : overlap = totalMass - defect := by linarith [hdefect_eq]
    have hsquare : (totalMass - defect) ^ 2 ≤ diagA * totalMass := by
      nlinarith [hoverlap_eq, hoverlap_sq, hdiagB_le, hdiagA_nonneg]
    nlinarith [hsquare, hmass_pos]

/-
The consistency defect of `(A,B)` controls the strong self-consistency defect
of the left-placed version of `A`. The Cauchy–Schwarz chain and tensor
hermitian identities have been factored out above, so the main proof is now a
straightforward combination of those helpers.
-/
lemma qSSCDefect_leftPlacedMeasurement_le_two_qBipartiteConsDefect
    {Outcome : Type*} {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype Outcome]
    (ψ : QuantumState (ιA × ιB))
    (A : Measurement Outcome ιA) (B : Measurement Outcome ιB) :
    qSSCDefect ψ (leftPlacedSubMeas (ιB := ιB) A.toSubMeas) ≤
      2 * qBipartiteConsDefect ψ A.toSubMeas B.toSubMeas := by
  classical
  let diagA : Error :=
    ∑ a : Outcome,
      ev ψ (leftTensor (ι₂ := ιB) (A.outcome a * A.outcome a))
  let diagB : Error :=
    ∑ a : Outcome,
      ev ψ (rightTensor (ι₁ := ιA) (B.outcome a * B.outcome a))
  let overlap : Error :=
    ∑ a : Outcome, ev ψ (opTensor (A.outcome a) (B.outcome a))
  let totalMass : Error := ev ψ (1 : MIPStarRE.Quantum.Op (ιA × ιB))
  let defect : Error := qBipartiteConsDefect ψ A.toSubMeas B.toSubMeas
  have hdefect_nonneg : 0 ≤ defect :=
    qBipartiteConsDefect_nonneg ψ A.toSubMeas B.toSubMeas
  have hdiagA_nonneg : 0 ≤ diagA :=
    sum_ev_leftTensor_outcome_sq_nonneg (ιB := ιB) ψ A.toSubMeas
  have hdiagB_nonneg : 0 ≤ diagB :=
    sum_ev_rightTensor_outcome_sq_nonneg (ιA := ιA) ψ B.toSubMeas
  have hleft_one :
      ev ψ (leftTensor (ι₂ := ιB) (1 : MIPStarRE.Quantum.Op ιA)) =
        totalMass := by
    simpa [totalMass] using congrArg (ev ψ) (leftTensor_one (ι₁ := ιA) (ι₂ := ιB))
  have hright_one :
      ev ψ (rightTensor (ι₁ := ιA) (1 : MIPStarRE.Quantum.Op ιB)) = totalMass := by
    simpa [totalMass] using congrArg (ev ψ) (rightTensor_one (ι₁ := ιA) (ι₂ := ιB))
  have hleftPlaced_outcome :
      ∀ a : Outcome,
        (leftPlacedSubMeas (ιB := ιB) A.toSubMeas).outcome a =
          leftTensor (ι₂ := ιB) (A.outcome a) := by
    intro a
    try rfl -- vendoring compile fix (Lean v4.33): the previous step may close the goal
  have hleftPlaced_total :
      (leftPlacedSubMeas (ιB := ιB) A.toSubMeas).total =
        leftTensor (ι₂ := ιB) A.total :=
    rfl
  have hrightPlaced_outcome :
      ∀ a : Outcome,
        (rightPlacedSubMeas (ιA := ιA) B.toSubMeas).outcome a =
          rightTensor (ι₁ := ιA) (B.outcome a) := by
    intro a
    try rfl -- vendoring compile fix (Lean v4.33): the previous step may close the goal
  have hrightPlaced_total :
      (rightPlacedSubMeas (ιA := ιA) B.toSubMeas).total =
        rightTensor (ι₁ := ιA) B.total :=
    rfl
  have hdiagA_le : diagA ≤ totalMass := by
    calc
      diagA ≤ ev ψ (leftTensor (ι₂ := ιB) (1 : MIPStarRE.Quantum.Op ιA)) := by
        simpa [diagA, hleftPlaced_outcome, hleftPlaced_total, leftTensor_mul_leftTensor,
          A.total_eq_one] using
          (MIPStarRE.LDT.Preliminaries.subMeas_diagMass_le_mass ψ
            (leftPlacedSubMeas (ιB := ιB) A.toSubMeas))
      _ = totalMass := hleft_one
  have hdiagB_le : diagB ≤ totalMass := by
    calc
      diagB ≤ ev ψ (rightTensor (ι₁ := ιA) (1 : MIPStarRE.Quantum.Op ιB)) := by
        simpa [diagB, hrightPlaced_outcome, hrightPlaced_total,
          rightTensor_mul_rightTensor, B.total_eq_one] using
          (MIPStarRE.LDT.Preliminaries.subMeas_diagMass_le_mass ψ
            (rightPlacedSubMeas (ιA := ιA) B.toSubMeas))
      _ = totalMass := hright_one
  have hoverlap_le : overlap ≤ totalMass :=
    sum_ev_opTensor_outcome_le_totalMass (ψ := ψ) A B
  have habs : |overlap| ≤ Real.sqrt diagA * Real.sqrt diagB :=
    abs_sum_ev_opTensor_le_sqrt_mul_sqrt (ψ := ψ) A.toSubMeas B.toSubMeas
  have hoverlap_upper : overlap ≤ Real.sqrt diagA * Real.sqrt diagB :=
    (abs_le.mp habs).2
  have hoverlap_sq : overlap ^ 2 ≤ diagA * diagB := by
    have hsq :
        overlap ^ 2 ≤ (Real.sqrt diagA * Real.sqrt diagB) ^ 2 := by
      have hoverlap_nonneg : 0 ≤ overlap :=
        Finset.sum_nonneg fun a _ =>
          ev_nonneg_of_psd ψ _ <| opTensor_nonneg (A.outcome_pos a) (B.outcome_pos a)
      nlinarith [hoverlap_nonneg, hoverlap_upper,
        Real.sqrt_nonneg diagA, Real.sqrt_nonneg diagB]
    calc
      overlap ^ 2 ≤ (Real.sqrt diagA * Real.sqrt diagB) ^ 2 := hsq
      _ = diagA * diagB := by
            ring_nf
            rw [Real.sq_sqrt hdiagA_nonneg, Real.sq_sqrt hdiagB_nonneg]
  have hdefect_eq : defect = totalMass - overlap := by
    have hoverlap_le_totalOverlap :
        overlap ≤ ev ψ (opTensor A.total B.total) := by
      simpa [totalMass, A.total_eq_one, B.total_eq_one, opTensor] using hoverlap_le
    dsimp [defect]
    unfold qBipartiteConsDefect
    rw [show qBipartiteMatchMass ψ A.toSubMeas B.toSubMeas = overlap by rfl]
    rw [show (let totalOverlap := ev ψ (opTensor A.total B.total);
          max 0 (totalOverlap - overlap)) =
        max 0 (ev ψ (opTensor A.total B.total) - overlap) by rfl]
    rw [max_eq_right (sub_nonneg.mpr hoverlap_le_totalOverlap)]
    simp [totalMass, A.total_eq_one, B.total_eq_one, opTensor]
  have hdiagA_lower : totalMass - 2 * defect ≤ diagA :=
    totalMass_sub_two_defect_le_diagA
      hdiagA_nonneg hdefect_nonneg hdefect_eq hoverlap_sq hdiagB_le
  have hinner : totalMass - diagA ≤ 2 * defect := by linarith
  have htarget_nonneg : 0 ≤ 2 * defect := by linarith
  have hmax : max 0 (totalMass - diagA) ≤ 2 * defect :=
    max_le_iff.mpr ⟨htarget_nonneg, hinner⟩
  have hmax' : max 0 (ev ψ (leftTensor (ι₂ := ιB) (1 : MIPStarRE.Quantum.Op ιA)) - diagA) ≤
      2 * defect := by
    simpa [hleft_one] using hmax
  simpa [qSSCDefect, diagA, hleftPlaced_outcome, hleftPlaced_total,
    leftTensor_mul_leftTensor, A.total_eq_one] using hmax'

/-- The consistency defect of `(A,B)` controls the strong self-consistency
defect of the right-placed version of `B`.  This is the right-register
counterpart of `qSSCDefect_leftPlacedMeasurement_le_two_qBipartiteConsDefect`;
it uses the same Cauchy--Schwarz calculation with the two diagonal terms
interchanged. -/
lemma qSSCDefect_rightPlacedMeasurement_le_two_qBipartiteConsDefect
    {Outcome : Type*} {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype Outcome]
    (ψ : QuantumState (ιA × ιB))
    (A : Measurement Outcome ιA) (B : Measurement Outcome ιB) :
    qSSCDefect ψ (rightPlacedSubMeas (ιA := ιA) B.toSubMeas) ≤
      2 * qBipartiteConsDefect ψ A.toSubMeas B.toSubMeas := by
  classical
  let diagA : Error :=
    ∑ a : Outcome,
      ev ψ (leftTensor (ι₂ := ιB) (A.outcome a * A.outcome a))
  let diagB : Error :=
    ∑ a : Outcome,
      ev ψ (rightTensor (ι₁ := ιA) (B.outcome a * B.outcome a))
  let overlap : Error :=
    ∑ a : Outcome, ev ψ (opTensor (A.outcome a) (B.outcome a))
  let totalMass : Error := ev ψ (1 : MIPStarRE.Quantum.Op (ιA × ιB))
  let defect : Error := qBipartiteConsDefect ψ A.toSubMeas B.toSubMeas
  have hdefect_nonneg : 0 ≤ defect :=
    qBipartiteConsDefect_nonneg ψ A.toSubMeas B.toSubMeas
  have hdiagA_nonneg : 0 ≤ diagA :=
    sum_ev_leftTensor_outcome_sq_nonneg (ιB := ιB) ψ A.toSubMeas
  have hdiagB_nonneg : 0 ≤ diagB :=
    sum_ev_rightTensor_outcome_sq_nonneg (ιA := ιA) ψ B.toSubMeas
  have hleft_one :
      ev ψ (leftTensor (ι₂ := ιB) (1 : MIPStarRE.Quantum.Op ιA)) =
        totalMass := by
    simpa [totalMass] using congrArg (ev ψ) (leftTensor_one (ι₁ := ιA) (ι₂ := ιB))
  have hright_one :
      ev ψ (rightTensor (ι₁ := ιA) (1 : MIPStarRE.Quantum.Op ιB)) = totalMass := by
    simpa [totalMass] using congrArg (ev ψ) (rightTensor_one (ι₁ := ιA) (ι₂ := ιB))
  have hleftPlaced_outcome :
      ∀ a : Outcome,
        (leftPlacedSubMeas (ιB := ιB) A.toSubMeas).outcome a =
          leftTensor (ι₂ := ιB) (A.outcome a) := by
    intro a
    try rfl -- vendoring compile fix (Lean v4.33): the previous step may close the goal
  have hleftPlaced_total :
      (leftPlacedSubMeas (ιB := ιB) A.toSubMeas).total =
        leftTensor (ι₂ := ιB) A.total :=
    rfl
  have hrightPlaced_outcome :
      ∀ a : Outcome,
        (rightPlacedSubMeas (ιA := ιA) B.toSubMeas).outcome a =
          rightTensor (ι₁ := ιA) (B.outcome a) := by
    intro a
    try rfl -- vendoring compile fix (Lean v4.33): the previous step may close the goal
  have hrightPlaced_total :
      (rightPlacedSubMeas (ιA := ιA) B.toSubMeas).total =
        rightTensor (ι₁ := ιA) B.total :=
    rfl
  have hdiagA_le : diagA ≤ totalMass := by
    calc
      diagA ≤ ev ψ (leftTensor (ι₂ := ιB) (1 : MIPStarRE.Quantum.Op ιA)) := by
        simpa [diagA, hleftPlaced_outcome, hleftPlaced_total, leftTensor_mul_leftTensor,
          A.total_eq_one] using
          (MIPStarRE.LDT.Preliminaries.subMeas_diagMass_le_mass ψ
            (leftPlacedSubMeas (ιB := ιB) A.toSubMeas))
      _ = totalMass := hleft_one
  have hdiagB_le : diagB ≤ totalMass := by
    calc
      diagB ≤ ev ψ (rightTensor (ι₁ := ιA) (1 : MIPStarRE.Quantum.Op ιB)) := by
        simpa [diagB, hrightPlaced_outcome, hrightPlaced_total,
          rightTensor_mul_rightTensor, B.total_eq_one] using
          (MIPStarRE.LDT.Preliminaries.subMeas_diagMass_le_mass ψ
            (rightPlacedSubMeas (ιA := ιA) B.toSubMeas))
      _ = totalMass := hright_one
  have hoverlap_le : overlap ≤ totalMass :=
    sum_ev_opTensor_outcome_le_totalMass (ψ := ψ) A B
  have habs : |overlap| ≤ Real.sqrt diagA * Real.sqrt diagB :=
    abs_sum_ev_opTensor_le_sqrt_mul_sqrt (ψ := ψ) A.toSubMeas B.toSubMeas
  have hoverlap_upper : overlap ≤ Real.sqrt diagA * Real.sqrt diagB :=
    (abs_le.mp habs).2
  have hoverlap_sq : overlap ^ 2 ≤ diagA * diagB := by
    have hsq :
        overlap ^ 2 ≤ (Real.sqrt diagA * Real.sqrt diagB) ^ 2 := by
      have hoverlap_nonneg : 0 ≤ overlap :=
        Finset.sum_nonneg fun a _ =>
          ev_nonneg_of_psd ψ _ <| opTensor_nonneg (A.outcome_pos a) (B.outcome_pos a)
      nlinarith [hoverlap_nonneg, hoverlap_upper,
        Real.sqrt_nonneg diagA, Real.sqrt_nonneg diagB]
    calc
      overlap ^ 2 ≤ (Real.sqrt diagA * Real.sqrt diagB) ^ 2 := hsq
      _ = diagA * diagB := by
            ring_nf
            rw [Real.sq_sqrt hdiagA_nonneg, Real.sq_sqrt hdiagB_nonneg]
  have hdefect_eq : defect = totalMass - overlap := by
    have hoverlap_le_totalOverlap :
        overlap ≤ ev ψ (opTensor A.total B.total) := by
      simpa [totalMass, A.total_eq_one, B.total_eq_one, opTensor] using hoverlap_le
    dsimp [defect]
    unfold qBipartiteConsDefect
    rw [show qBipartiteMatchMass ψ A.toSubMeas B.toSubMeas = overlap by rfl]
    rw [show (let totalOverlap := ev ψ (opTensor A.total B.total);
          max 0 (totalOverlap - overlap)) =
        max 0 (ev ψ (opTensor A.total B.total) - overlap) by rfl]
    rw [max_eq_right (sub_nonneg.mpr hoverlap_le_totalOverlap)]
    simp [totalMass, A.total_eq_one, B.total_eq_one, opTensor]
  have hoverlap_sq' : overlap ^ 2 ≤ diagB * diagA := by
    rw [mul_comm]
    exact hoverlap_sq
  have hdiagB_lower : totalMass - 2 * defect ≤ diagB :=
    totalMass_sub_two_defect_le_diagA
      hdiagB_nonneg hdefect_nonneg hdefect_eq hoverlap_sq' hdiagA_le
  have hinner : totalMass - diagB ≤ 2 * defect := by linarith
  have htarget_nonneg : 0 ≤ 2 * defect := by linarith
  have hmax : max 0 (totalMass - diagB) ≤ 2 * defect :=
    max_le_iff.mpr ⟨htarget_nonneg, hinner⟩
  have hmax' : max 0 (ev ψ (rightTensor (ι₁ := ιA) (1 : MIPStarRE.Quantum.Op ιB)) -
        diagB) ≤ 2 * defect := by
    simpa [hright_one] using hmax
  simpa [qSSCDefect, diagB, hrightPlaced_outcome, hrightPlaced_total,
    rightTensor_mul_rightTensor, B.total_eq_one] using hmax'

lemma sourceAlmostProjective_of_ssc {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι) (A : Measurement Outcome ι) (η : Error)
    (hssc : qSSCDefect ψ A.toSubMeas ≤ η) :
    ∑ a, ev ψ (A.outcome a - A.outcome a * A.outcome a) ≤ η := by
  classical
  let diagA : Error := ∑ a : Outcome, ev ψ (A.outcome a * A.outcome a)
  have hsource_eq :
      ∑ a : Outcome, ev ψ (A.outcome a - A.outcome a * A.outcome a) =
        ev ψ A.toSubMeas.total - diagA := by
    calc
      ∑ a : Outcome, ev ψ (A.outcome a - A.outcome a * A.outcome a)
          = ∑ a : Outcome,
              (ev ψ (A.outcome a) - ev ψ (A.outcome a * A.outcome a)) := by
              refine Finset.sum_congr rfl ?_
              intro a _
              exact ev_sub ψ (A.outcome a) (A.outcome a * A.outcome a)
      _ = (∑ a : Outcome, ev ψ (A.outcome a)) -
            ∑ a : Outcome, ev ψ (A.outcome a * A.outcome a) := by
            rw [Finset.sum_sub_distrib]
      _ = ev ψ A.toSubMeas.total - diagA := by
            rw [← ev_sum ψ A.outcome, A.toSubMeas.sum_eq_total]
  have hssc' : max 0 (ev ψ A.toSubMeas.total - diagA) ≤ η := by
    simpa [qSSCDefect, diagA] using hssc
  calc
    ∑ a, ev ψ (A.outcome a - A.outcome a * A.outcome a)
      = ev ψ A.toSubMeas.total - diagA := hsource_eq
    _ ≤ max 0 (ev ψ A.toSubMeas.total - diagA) := le_max_right 0 _
    _ ≤ η := hssc'

/-- The zero family is a projective submeasurement. This supplies trivial
large-error branches where the target error bound is already at least the
universal `qSDD ≤ 1` estimate. -/
def zeroProjSubMeas {Outcome : Type*} {ι : Type*}
    [Fintype Outcome] [Fintype ι] [DecidableEq ι] :
    ProjSubMeas Outcome ι where
  toSubMeas :=
    { outcome := fun _ => 0
      total := 0
      outcome_pos := fun _ => le_rfl
      sum_eq_total := Fintype.sum_eq_zero _ fun _ => rfl
      total_le_one := zero_le_one }
  proj := fun _ => by simp

end MIPStarRE.LDT.MakingMeasurementsProjective


