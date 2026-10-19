-- Prove2me | Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Families
-- name    : MIPRE_Background_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Families
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T02:22:10.835978+00:00
-- url     : https://prove2.me/theorems/ceb7979d-60a5-4c00-92ee-980e374e93bc
-- title:
--   Definitions of Families: Section 8 global variance: operator families Positivity and normalization lemmas for the point-conditioned outcome…
-- statement:
--   The definitions of the module `MIPRE.Background.LIDT.MIPStarRE.LDT.GlobalVariance.Defs.Families` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Section 8 global variance: operator families. Positivity and normalization lemmas for the point-conditioned outcome operator families used to build the global-variance comparisons.
--
--   The module is vendored read-only, with the authors' permission, from [LionSR/MIPStarRE](https://github.com/LionSR/MIPStarRE) (Sirui Lu and the MIPStarRE contributors, Apache 2.0; commit and upstream path in the file header) by `scripts/vendor-lidt.py`.
--
--   **Definitions** (17): `MIPStarRE.LDT.GlobalVariance.generalizeBCollisionResidual` (The line-collision residual obtained after expanding the projective line measurement in `lem:generalize-b` and moving the polynomial weight…); `MIPStarRE.LDT.GlobalVariance.generalizeBDeviation` (The polynomial-averaged deviation controlled by `lem:generalize-b`.); `MIPStarRE.LDT.GlobalVariance.generalizeBDeviationAtPolynomial` (The squared norm expression controlled by `lem:generalize-b` for a fixed `g`.); `MIPStarRE.LDT.GlobalVariance.generalizeBError` (The displayed error term in `lem:generalize-b`.); `MIPStarRE.LDT.GlobalVariance.generalizeBLeftFamily` (Aggregated family for the left-hand side of `lem:generalize-b` on the bipartite space `d * d`.); `MIPStarRE.LDT.GlobalVariance.generalizeBLineCollisionExpansion` (Explicit line/parameter expansion of the `lem:generalize-b` collision residual.); `MIPStarRE.LDT.GlobalVariance.generalizeBRightFamily` (Aggregated family for the right-hand side of `lem:generalize-b` on the bipartite space `d * d`.); `MIPStarRE.LDT.GlobalVariance.generalizeBSeedCollisionExpansion` (Uniform line/parameter seed expansion of the `lem:generalize-b` collision residual.); `MIPStarRE.LDT.GlobalVariance.globalVarianceDeviationAtPolynomial` (The independently sampled squared norm expression in `lem:global-variance-of-points`.); `MIPStarRE.LDT.GlobalVariance.globalVarianceLeftFamily` (The same weighted operator on the first independently sampled point.); and -5 more.
--
--   **Embedded lemmas** (5): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `cfc_sqrt_outcome_le_one`, `weightedPointConditionedOperatorAtPolynomial_le_one`, `weightedPointConditionedOperatorAtPolynomial_pos`, `weightedPolynomialOperator_le_one`, `weightedPolynomialOperator_pos`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Background.LIDT.MIPStarRE.LDT.GlobalVariance.Defs.Families` (`MIPRE/Background/LIDT/MIPStarRE/LDT/GlobalVariance/Defs/Families.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 25 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/LIDT/MIPStarRE/LDT/GlobalVariance/Defs/Families.lean

/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/GlobalVariance/Defs/Families.lean
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/MIPStarRE/LDT/GlobalVariance/Defs/Families.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.Algebra.Hom
import Mathlib.Algebra.Algebra.NonUnitalHom
import Mathlib.Algebra.Algebra.Spectrum.Basic
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
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unital
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
import Mathlib.Analysis.Real.Spectrum
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
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.NNReal.Star
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
import Mathlib.Order.Hom.Basic
import Mathlib.Order.Lattice
import Mathlib.Order.Lattice.Nat
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
import Mathlib.Topology.ContinuousOn
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
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Core
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Operators
import Theorems.Thm_MIPStarRE_LDT_Measurement_outcome_le_one
import Theorems.Thm_MIPStarRE_LDT_SubMeas_outcome_le_one
import Theorems.Thm_MIPStarRE_LDT_averageOperatorOverDistribution_nonneg
import Theorems.Thm_MIPStarRE_LDT_averageOperatorOverDistribution_uniform_le_one
import Theorems.Thm_MIPStarRE_LDT_leftTensor_le_one
import Theorems.Thm_MIPStarRE_LDT_opTensor_le_leftTensor

set_option backward.isDefEq.respectTransparency false

/-!
# Section 8 global variance: operator families

Positivity and normalization lemmas for the point-conditioned outcome
operator families used to build the global-variance comparisons.

## References

- `references/ldt-paper/expansion.tex`
- `blueprint/src/chapter/ch06_variance.tex`
-/

namespace MIPStarRE.LDT.GlobalVariance

open MIPStarRE.LDT
open MIPStarRE.LDT.MakingMeasurementsProjective
open MIPStarRE.LDT.ExpansionHypercubeGraph
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (params : Parameters) [FieldModel params.q]

/-- `CFC.sqrt (G.outcome g) ≤ 1` when `G` is a submeasurement.
Proved via the NNReal CFC spectrum API: `G.outcome g ≤ 1` means all
spectral values satisfy `λ ≤ 1`, so `√λ ≤ 1` as well. -/
lemma cfc_sqrt_outcome_le_one (params : Parameters) [FieldModel params.q]
    (G : SubMeas (Polynomial params) ι) (g : Polynomial params) :
    CFC.sqrt (G.outcome g) ≤ 1 := by
  have hspec_le : ∀ x, x ∈ spectrum NNReal (G.outcome g) → x ≤ 1 := by
    have hle : G.outcome g ≤ 1 := G.outcome_le_one g
    rw [← cfc_id' NNReal (G.outcome g) (ha := G.outcome_pos g),
      ← cfc_const_one (R := NNReal) (G.outcome g) (ha := G.outcome_pos g),
      cfc_nnreal_le_iff _ _ _ (SpectrumRestricts.nnreal_of_nonneg (G.outcome_pos g))
        (ha := G.outcome_pos g)] at hle
    exact hle
  rw [CFC.sqrt_eq_cfc, ← cfc_const_one (R := NNReal) (G.outcome g) (ha := G.outcome_pos g),
    cfc_nnreal_le_iff _ _ _ (SpectrumRestricts.nnreal_of_nonneg (G.outcome_pos g))
      (ha := G.outcome_pos g)]
  intro x hx
  -- √x ≤ 1 follows from x ≤ 1 for NNReal (NNReal.sqrt_le_one)
  simpa using hspec_le x hx

theorem weightedPolynomialOperator_pos (params : Parameters)
    [FieldModel params.q]
    (G : SubMeas (Polynomial params) ι)
    (g : Polynomial params)
    {A : MIPStarRE.Quantum.Op ι} (hA : 0 ≤ A) :
    0 ≤ opTensor A (polynomialWeightSqrtOperator params G g) := by
  simpa [polynomialWeightSqrtOperator] using
    (opTensor_nonneg hA (CFC.sqrt_nonneg (G.outcome g)))

theorem weightedPolynomialOperator_le_one (params : Parameters)
    [FieldModel params.q]
    (G : SubMeas (Polynomial params) ι)
    (g : Polynomial params)
    {A : MIPStarRE.Quantum.Op ι}
    (hA_pos : 0 ≤ A) (hA_le_one : A ≤ 1) :
    opTensor A (polynomialWeightSqrtOperator params G g) ≤ 1 := by
  calc
    opTensor A (polynomialWeightSqrtOperator params G g)
      ≤ leftTensor (ι₂ := ι) A :=
        opTensor_le_leftTensor hA_pos (cfc_sqrt_outcome_le_one params G g)
    _ ≤ 1 := leftTensor_le_one hA_le_one

theorem weightedPointConditionedOperatorAtPolynomial_pos (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι)
    (g : Polynomial params) (u : Point params) :
    0 ≤ weightedPointConditionedOperatorAtPolynomial params strategy G g u := by
  simpa [weightedPointConditionedOperatorAtPolynomial] using
    (weightedPolynomialOperator_pos (ι := ι) (params := params) (G := G) (g := g)
      (A := pointConditionedOutcomeOperatorAtPolynomial params strategy g u)
      (by
        simpa [pointConditionedOutcomeOperatorAtPolynomial] using
          (strategy.pointMeasurement u).outcome_pos (g u)))

theorem weightedPointConditionedOperatorAtPolynomial_le_one (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι)
    (g : Polynomial params) (u : Point params) :
    weightedPointConditionedOperatorAtPolynomial params strategy G g u ≤ 1 := by
  have hA_le_one :
      pointConditionedOutcomeOperatorAtPolynomial params strategy g u ≤ 1 := by
    simpa [pointConditionedOutcomeOperatorAtPolynomial] using
      Measurement.outcome_le_one (strategy.pointMeasurement u).toMeasurement (g u)
  simpa [weightedPointConditionedOperatorAtPolynomial] using
    (weightedPolynomialOperator_le_one (ι := ι) (params := params) (G := G) (g := g)
      (A := pointConditionedOutcomeOperatorAtPolynomial params strategy g u)
      (by
        simpa [pointConditionedOutcomeOperatorAtPolynomial] using
          (strategy.pointMeasurement u).outcome_pos (g u))
      hA_le_one)

/-- The squared norm expression controlled by `lem:generalize-b` for a fixed `g`.
Uses bipartite state `ψbi` on `d * d`. -/
noncomputable def generalizeBDeviationAtPolynomial (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (ψbi : QuantumState (ι × ι))
    (G : SubMeas (Polynomial params) ι)
    (g : Polynomial params) : Error :=
  avgOver (axisParallelLineQuestionDistribution params)
    (fun qu =>
      let D := weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu -
               weightedGeneralizeBRightOperatorAtPolynomial params strategy G g qu
      ev ψbi (Dᴴ * D))

/-- The polynomial-averaged deviation controlled by `lem:generalize-b`. -/
noncomputable def generalizeBDeviation (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (ψbi : QuantumState (ι × ι))
    (G : SubMeas (Polynomial params) ι) : Error :=
  avgOver (polynomialDistribution params)
    (fun g => generalizeBDeviationAtPolynomial params strategy ψbi G g)

/-- The line-collision residual obtained after expanding the projective line
measurement in `lem:generalize-b` and moving the polynomial weight from
`(G_g)^{1/2}` to `G_g`.  The remaining unproved analytic step is to bound this
quantity by Schwartz--Zippel and the submeasurement property of `G`.

Paper origin: `references/ldt-paper/expansion.tex:273-288`
(`\label{lem:generalize-b}`). -/
noncomputable def generalizeBCollisionResidual (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (ψbi : QuantumState (ι × ι))
    (G : SubMeas (Polynomial params) ι)
    (g : Polynomial params) : Error :=
  avgOver (axisParallelLineQuestionDistribution params)
    (fun qu =>
      ev ψbi (opTensor
        (generalizeBCollisionOperatorAtPolynomial params strategy g qu)
        (G.outcome g)))

/-- Uniform line/parameter seed expansion of the `lem:generalize-b` collision residual.

This is the paper's `expansion.tex`, lines 286--288, after replacing an
incident line question `(ℓ,u)` by a line `ℓ` and affine parameter `t` with
`u = ℓ(t)`, but before commuting the finite average over `t` past the finite
sum over line answers `f`.  The equality from the original collision residual to
this seed expansion is proved in
`generalizeBCollisionResidual_eq_seedCollisionExpansion`. -/
noncomputable def generalizeBSeedCollisionExpansion (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (ψbi : QuantumState (ι × ι))
    (G : SubMeas (Polynomial params) ι)
    (g : Polynomial params) : Error :=
  avgOver (uniformDistribution (AxisParallelLine params × Fq params))
    (fun ℓt =>
      ∑ f : AxisLinePolynomial params,
        (if f ℓt.2 = (Polynomial.restrictToAxisParallelLine params g ℓt.1) ℓt.2 ∧
            f.poly ≠ (Polynomial.restrictToAxisParallelLine params g ℓt.1).poly then
          (1 : Error)
        else 0) *
          ev ψbi (opTensor
            ((strategy.axisParallelMeasurement ℓt.1).toSubMeas.outcome f)
            (G.outcome g)))

/-- Explicit line/parameter expansion of the `lem:generalize-b` collision residual.

This is the commuted finite-sum form of `generalizeBSeedCollisionExpansion`: for
fixed `ℓ` and `f`, the coefficient is the fraction of parameters where the line
answer `f` both collides with `g|_ℓ` at `t` and is not equal to `g|_ℓ`. -/
noncomputable def generalizeBLineCollisionExpansion (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (ψbi : QuantumState (ι × ι))
    (G : SubMeas (Polynomial params) ι)
    (g : Polynomial params) : Error :=
  avgOver (uniformDistribution (AxisParallelLine params))
    (fun ℓ =>
      ∑ f : AxisLinePolynomial params,
        avgOver (uniformDistribution (Fq params))
          (fun t =>
            if f t = (Polynomial.restrictToAxisParallelLine params g ℓ) t ∧
                f.poly ≠ (Polynomial.restrictToAxisParallelLine params g ℓ).poly then
              (1 : Error)
            else 0) *
          ev ψbi (opTensor
            ((strategy.axisParallelMeasurement ℓ).toSubMeas.outcome f)
            (G.outcome g)))

/-- Aggregated family for the left-hand side of `lem:generalize-b`
on the bipartite space `d * d`. -/
noncomputable def generalizeBLeftFamily (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι) :
    IdxSubMeas (AxisParallelLineQuestion params) Unit (ι × ι) :=
  fun qu =>
    let F : Polynomial params → MIPStarRE.Quantum.Op (ι × ι) :=
      fun g => weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu
    SubMeas.singleOutcome
      (averageOperatorOverDistribution (uniformDistribution (Polynomial params)) F)
      (averageOperatorOverDistribution_nonneg
        (uniformDistribution (Polynomial params)) F
        (fun g => by
          change
            0 ≤ weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu
          simpa [weightedGeneralizeBLeftOperatorAtPolynomial] using
            (weightedPolynomialOperator_pos (ι := ι) (params := params) (G := G) (g := g)
              (A := generalizeBLeftOperatorAtPolynomial params strategy g qu)
              (by
                simpa [generalizeBLeftOperatorAtPolynomial] using
                  (generalizeBLeftEventSubMeasAtPolynomial
                    params strategy g qu).outcome_pos (some ())))))
      (averageOperatorOverDistribution_uniform_le_one F
        (fun g => by
          change weightedGeneralizeBLeftOperatorAtPolynomial params strategy G g qu ≤ 1
          simpa [weightedGeneralizeBLeftOperatorAtPolynomial] using
            (weightedPolynomialOperator_le_one (ι := ι) (params := params) (G := G)
              (g := g)
              (A := generalizeBLeftOperatorAtPolynomial params strategy g qu)
              (by
                simpa [generalizeBLeftOperatorAtPolynomial] using
                  (generalizeBLeftEventSubMeasAtPolynomial
                    params strategy g qu).outcome_pos (some ()))
              (by
                simpa [generalizeBLeftOperatorAtPolynomial] using
                  SubMeas.outcome_le_one
                    (generalizeBLeftEventSubMeasAtPolynomial params strategy g qu)
                    (some ())))))

/-- Aggregated family for the right-hand side of `lem:generalize-b`
on the bipartite space `d * d`. -/
noncomputable def generalizeBRightFamily (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι) :
    IdxSubMeas (AxisParallelLineQuestion params) Unit (ι × ι) :=
  fun qu =>
    let F : Polynomial params → MIPStarRE.Quantum.Op (ι × ι) :=
      fun g => weightedGeneralizeBRightOperatorAtPolynomial params strategy G g qu
    SubMeas.singleOutcome
      (averageOperatorOverDistribution (uniformDistribution (Polynomial params)) F)
      (averageOperatorOverDistribution_nonneg
        (uniformDistribution (Polynomial params)) F
        (fun g => by
          change
            0 ≤ weightedGeneralizeBRightOperatorAtPolynomial params strategy G g qu
          simpa [weightedGeneralizeBRightOperatorAtPolynomial] using
            (weightedPolynomialOperator_pos (ι := ι) (params := params) (G := G) (g := g)
              (A := generalizeBRightOperatorAtPolynomial params strategy g qu)
              (by
                simpa [generalizeBRightOperatorAtPolynomial] using
                  (generalizeBRightEventSubMeasAtPolynomial
                    params strategy g qu).outcome_pos (some ())))))
      (averageOperatorOverDistribution_uniform_le_one F
        (fun g => by
          change weightedGeneralizeBRightOperatorAtPolynomial params strategy G g qu ≤ 1
          simpa [weightedGeneralizeBRightOperatorAtPolynomial] using
            (weightedPolynomialOperator_le_one (ι := ι) (params := params) (G := G)
              (g := g)
              (A := generalizeBRightOperatorAtPolynomial params strategy g qu)
              (by
                simpa [generalizeBRightOperatorAtPolynomial] using
                  (generalizeBRightEventSubMeasAtPolynomial
                    params strategy g qu).outcome_pos (some ()))
              (by
                simpa [generalizeBRightOperatorAtPolynomial] using
                  SubMeas.outcome_le_one
                    (generalizeBRightEventSubMeasAtPolynomial params strategy g qu)
                    (some ())))))

/-- Aggregated family for `A^u_[g(u)] ⊗ (G_g)^{1/2}`
on the bipartite space `d * d`. -/
noncomputable def localVarianceLeftFamily (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι) :
    IdxSubMeas (PointPairQuestion params) Unit (ι × ι) :=
  fun uv =>
    let F : Polynomial params → MIPStarRE.Quantum.Op (ι × ι) :=
      fun g => weightedPointConditionedOperatorAtPolynomial params strategy G g uv.1
    SubMeas.singleOutcome
      (averageOperatorOverDistribution (uniformDistribution (Polynomial params)) F)
      (averageOperatorOverDistribution_nonneg
        (uniformDistribution (Polynomial params)) F
        (fun g => weightedPointConditionedOperatorAtPolynomial_pos params strategy G g uv.1))
      (averageOperatorOverDistribution_uniform_le_one F
        (fun g => weightedPointConditionedOperatorAtPolynomial_le_one params strategy G g uv.1))

/-- Aggregated family for `A^v_[g(v)] ⊗ (G_g)^{1/2}`
on the bipartite space `d * d`. -/
noncomputable def localVarianceRightFamily (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι) :
    IdxSubMeas (PointPairQuestion params) Unit (ι × ι) :=
  fun uv =>
    let F : Polynomial params → MIPStarRE.Quantum.Op (ι × ι) :=
      fun g => weightedPointConditionedOperatorAtPolynomial params strategy G g uv.2
    SubMeas.singleOutcome
      (averageOperatorOverDistribution (uniformDistribution (Polynomial params)) F)
      (averageOperatorOverDistribution_nonneg
        (uniformDistribution (Polynomial params)) F
        (fun g => weightedPointConditionedOperatorAtPolynomial_pos params strategy G g uv.2))
      (averageOperatorOverDistribution_uniform_le_one F
        (fun g => weightedPointConditionedOperatorAtPolynomial_le_one params strategy G g uv.2))

/-- The same weighted operator on the first independently sampled point.
On the bipartite space `d * d`. -/
noncomputable def globalVarianceLeftFamily (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι) :
    IdxSubMeas (PointPairQuestion params) Unit (ι × ι) :=
  localVarianceLeftFamily params strategy G

/-- The same weighted operator on the second independently sampled point.
On the bipartite space `d * d`. -/
noncomputable def globalVarianceRightFamily (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι) :
    IdxSubMeas (PointPairQuestion params) Unit (ι × ι) :=
  localVarianceRightFamily params strategy G

/-- The edgewise squared norm expression in `lem:local-variance-of-points`.
Uses bipartite state `ψbi` on `d * d`. -/
noncomputable def localVarianceDeviationAtPolynomial (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (ψbi : QuantumState (ι × ι))
    (G : SubMeas (Polynomial params) ι)
    (g : Polynomial params) : Error :=
  avgOver (rerandomizeCoord params)
    (fun uv =>
      let D := weightedPointConditionedOperatorAtPolynomial params strategy G g uv.1 -
               weightedPointConditionedOperatorAtPolynomial params strategy G g uv.2
      ev ψbi (Dᴴ * D))

/-- The independently sampled squared norm expression in `lem:global-variance-of-points`.
Uses bipartite state `ψbi` on `d * d`. -/
noncomputable def globalVarianceDeviationAtPolynomial (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (ψbi : QuantumState (ι × ι))
    (G : SubMeas (Polynomial params) ι)
    (g : Polynomial params) : Error :=
  avgOver (independentPointPair params)
    (fun uv =>
      let D := weightedPointConditionedOperatorAtPolynomial params strategy G g uv.1 -
               weightedPointConditionedOperatorAtPolynomial params strategy G g uv.2
      ev ψbi (Dᴴ * D))

/-- The displayed error term in `lem:generalize-b`. -/
noncomputable def generalizeBError (params : Parameters) : Error :=
  ((params.m : Error) * (params.d : Error)) / (params.q : Error)

/-- The post-triangle-inequality error term for the six-step transport in
`lem:local-variance-of-points`.

The six comparisons at `references/ldt-paper/expansion.tex`, lines 305--311
have errors `2δ`, `2ε`, `md/q`, `md/q`, `2ε`, and `2δ`, whose sum is
`4ε + 4δ + 2md/q`.  The paper then applies
`prop:triangle-inequality-for-approx_delta` (`preliminaries.tex:622--642`) with
`k = 6`, yielding `6 * (4ε + 4δ + 2md/q)`.  This is the genuine residual that
the six-step chain is expected to prove before it is absorbed by the displayed
`24(ε + δ + md/q)` slack. -/
noncomputable def localVarianceTransportChainError (params : Parameters)
    (eps delta : Error) : Error :=
  6 * (4 * eps + 4 * delta + 2 * generalizeBError params)

/-- The displayed error term in `lem:local-variance-of-points`. -/
noncomputable def localVarianceOfPointsError (params : Parameters)
    (eps delta : Error) : Error :=
  24 * (eps + delta + generalizeBError params)

/-- The displayed error term in `lem:global-variance-of-points`. -/
noncomputable def globalVarianceOfPointsError (params : Parameters)
    (eps delta : Error) : Error :=
  24 * (params.m : Error) * (eps + delta + generalizeBError params)

end MIPStarRE.LDT.GlobalVariance


