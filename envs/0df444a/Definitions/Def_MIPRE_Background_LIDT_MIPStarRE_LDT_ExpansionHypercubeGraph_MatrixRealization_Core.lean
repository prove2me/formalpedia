-- Prove2me | Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_MatrixRealization_Core
-- name    : MIPRE_Background_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_MatrixRealization_Core
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T01:56:06.269866+00:00
-- url     : https://prove2.me/theorems/38475f23-8e62-4938-8283-3f690e596701
-- title:
--   Definitions of Core: Section 7 — Matrix realization This file gives concrete finite-dimensional matrix realizations of the hypercube…
-- statement:
--   The definitions of the module `MIPRE.Background.LIDT.MIPStarRE.LDT.ExpansionHypercubeGraph.MatrixRealization.Core` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Section 7 — Matrix realization. This file gives concrete finite-dimensional matrix realizations of the hypercube variance operators, Fourier projectors, and spectral inequalities introduced in `Defs`.
--
--   The module is vendored read-only, with the authors' permission, from [LionSR/MIPStarRE](https://github.com/LionSR/MIPStarRE) (Sirui Lu and the MIPStarRE contributors, Apache 2.0; commit and upstream path in the file header) by `scripts/vendor-lidt.py`.
--
--   **Definitions** (7): `MIPStarRE.LDT.ExpansionHypercubeGraph.MatrixOperatorFamilyRealization` (The concrete matrix family underlying the variance calculations.); `MIPStarRE.LDT.ExpansionHypercubeGraph.RectangularMatrixOperator` (Rectangular operators from `H` into `K`, represented as concrete matrices.); `MIPStarRE.LDT.ExpansionHypercubeGraph.constantModeProjectorMatrix` (The normalized all-ones projector onto the constant mode.); `MIPStarRE.LDT.ExpansionHypercubeGraph.matrixHypercubeEdgeDistribution` (The Section 7.1 edge distribution used by the matrix model.); `MIPStarRE.LDT.ExpansionHypercubeGraph.matrixTensorOperator` (Kronecker product of two concrete operators.); `MIPStarRE.LDT.ExpansionHypercubeGraph.orthogonalModeProjectorMatrix` (The projector onto the orthogonal complement of the constant mode.); `MIPStarRE.LDT.ExpansionHypercubeGraph.tensorHilbertSpace` (Tensor two finite Hilbert spaces by taking the cartesian product of indices.).
--
--   **Embedded lemmas** (12): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `constantModeProjectorMatrix_eq_fourierBasisProjector_zero`, `fourierBasisState_apply_comm`, `fourierBasisState_inner_product_dual`, `fourierBasis_norm_sq`, `frequencyWeight_pos_of_ne_zero`, `frequencyWeight_zero`, `hypercubeSpectralGap_operator_posSemidef`, `laplacianEigenvalue_zero`, `matrixAdjacencyOperator_spectral_decomp`, `matrixLaplacianOperator_spectral_decomp`, ….
--
--   **Formalization Note** The bundle is the module `MIPRE.Background.LIDT.MIPStarRE.LDT.ExpansionHypercubeGraph.MatrixRealization.Core` (`MIPRE/Background/LIDT/MIPStarRE/LDT/ExpansionHypercubeGraph/MatrixRealization/Core.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 14 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/LIDT/MIPStarRE/LDT/ExpansionHypercubeGraph/MatrixRealization/Core.lean

/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/ExpansionHypercubeGraph/MatrixRealization/Core.lean
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/MIPStarRE/LDT/ExpansionHypercubeGraph/MatrixRealization/Core.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.Algebra.Spectrum.Quasispectrum
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.CharP.Invertible
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Action.Pi
import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Commute.Defs
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Algebra.Group.Finsupp
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Invertible.Defs
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Algebra.Group.Submonoid.Defs
import Mathlib.Algebra.Group.Subsemigroup.Defs
import Mathlib.Algebra.Group.Units.Basic
import Mathlib.Algebra.Group.Units.Defs
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
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.Notation.Defs
import Mathlib.Algebra.Notation.Pi.Basic
import Mathlib.Algebra.Notation.Pi.Defs
import Mathlib.Algebra.Opposites
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Group.Unbundled.Basic
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.GroupWithZero.Canonical
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Algebra.Order.Module.Defs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
import Mathlib.Algebra.Order.Nonneg.Basic
import Mathlib.Algebra.Order.Nonneg.Module
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Order.Sub.Defs
import Mathlib.Algebra.Order.ZeroLEOne
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Roots
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
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Convex.Cone.Basic
import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
import Mathlib.Analysis.Fourier.ZMod
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
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
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
import Mathlib.Data.Fin.SuccPred
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
import Mathlib.Data.Int.Cast.Basic
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Sort
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Matrix.Diagonal
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Multiset.Bind
import Mathlib.Data.Multiset.Defs
import Mathlib.Data.Multiset.MapFold
import Mathlib.Data.Multiset.ZeroCons
import Mathlib.Data.NNRat.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Init
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Prod.Basic
import Mathlib.Data.Rat.Init
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Star
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Operations
import Mathlib.Data.SetLike.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Defs
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Geometry.Convex.Cone.Pointed
import Mathlib.GroupTheory.GroupAction.Hom
import Mathlib.GroupTheory.GroupAction.Ring
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Logic.Basic
import Mathlib.Logic.Embedding.Basic
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Equiv.Prod
import Mathlib.Logic.Function.Basic
import Mathlib.Logic.IsEmpty.Basic
import Mathlib.Logic.IsEmpty.Defs
import Mathlib.Logic.Nonempty
import Mathlib.Logic.Unique
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Mathlib.Order.Basic
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Fin.Basic
import Mathlib.Order.Lattice
import Mathlib.Order.Monotone.Defs
import Mathlib.Order.Notation
import Mathlib.Order.RelClasses
import Mathlib.Order.SetNotation
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp.Lemmas
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
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
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_QuantumState
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_SubMeasurementCore
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_PMFAverages
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Fourier
import Theorems.Thm_MIPStarRE_LDT_ExpansionHypercubeGraph_addCharFq_dotProduct_eq_stdAddChar_dotProductZMod
import Theorems.Thm_MIPStarRE_LDT_ExpansionHypercubeGraph_eigenvectors
import Theorems.Thm_MIPStarRE_LDT_ExpansionHypercubeGraph_fourierBasisState_inner_product
import Theorems.Thm_MIPStarRE_LDT_ExpansionHypercubeGraph_hypercubeSpectralGap_le_laplacianEigenvalue
import Theorems.Thm_MIPStarRE_LDT_ExpansionHypercubeGraph_laplacianEigenvalue_eq

set_option backward.isDefEq.respectTransparency false

/-!
# Section 7 — Matrix realization

This file gives concrete finite-dimensional matrix realizations of the
hypercube variance operators, Fourier projectors, and spectral inequalities
introduced in `Defs`.

## References

- `blueprint/src/chapter/ch05_expansion.tex`
- `references/ldt-paper/expansion.tex`
-/

namespace MIPStarRE.LDT.ExpansionHypercubeGraph

open MIPStarRE.LDT
open MIPStarRE.LDT.MakingMeasurementsProjective
open scoped BigOperators MatrixOrder Matrix ComplexOrder

universe u

/-- Tensor two finite Hilbert spaces by taking the cartesian product of indices. -/
def tensorHilbertSpace (H K : FiniteHilbertSpace) : FiniteHilbertSpace where
  carrier := H.carrier × K.carrier
  instFintype := inferInstance
  instDecidableEq := inferInstance
  instNonempty := inferInstance

/-- Kronecker product of two concrete operators. -/
def matrixTensorOperator {H K : FiniteHilbertSpace}
    (A : MatrixOperator H) (B : MatrixOperator K) :
    MatrixOperator (tensorHilbertSpace H K) :=
  Matrix.kronecker A B

/-- Rectangular operators from `H` into `K`, represented as concrete matrices. -/
abbrev RectangularMatrixOperator (H K : FiniteHilbertSpace) :=
  Matrix K.carrier H.carrier ℂ

/-- The concrete matrix family underlying the variance calculations. -/
structure MatrixOperatorFamilyRealization (params : Parameters) where
  space : FiniteHilbertSpace.{u}
  state : PositiveMatrixState space
  family : Point params → MatrixOperator space

/-- The Section 7.1 edge distribution used by the matrix model. -/
noncomputable def matrixHypercubeEdgeDistribution (params : Parameters) :
    Distribution (Point params × Point params) :=
  rerandomizeCoord params

/-- The normalized all-ones projector onto the constant mode. -/
noncomputable def constantModeProjectorMatrix (params : Parameters) :
    MatrixOperator (pointHilbertSpace params) :=
  fun _ _ => (hypercubeVertexCount params : ℂ)⁻¹

/-- The projector onto the orthogonal complement of the constant mode. -/
noncomputable def orthogonalModeProjectorMatrix (params : Parameters) :
    MatrixOperator (pointHilbertSpace params) :=
  1 - constantModeProjectorMatrix params

lemma fourierBasisState_apply_comm (params : Parameters) (α u : Point params) :
    fourierBasisState params α u = fourierBasisState params u α := by
  unfold fourierBasisState
  have hdot : dotProductZMod params u α = dotProductZMod params α u := by
    unfold dotProductZMod
    refine Finset.sum_congr rfl ?_
    intro i _
    ring
  rw [addCharFq_dotProduct_eq_stdAddChar_dotProductZMod,
    addCharFq_dotProduct_eq_stdAddChar_dotProductZMod, hdot]

lemma fourierBasisState_inner_product_dual (params : Parameters) (u v : Point params) :
    ∑ α : Point params,
      star (fourierBasisState params α u) * fourierBasisState params α v =
        if u = v then 1 else 0 := by
  conv_lhs =>
    arg 2; ext α
    rw [fourierBasisState_apply_comm params α u, fourierBasisState_apply_comm params α v]
  exact fourierBasisState_inner_product params u v

lemma sum_fourierBasisProjector_eq_one (params : Parameters) :
    (∑ α : Point params, fourierBasisProjector params α) =
      (1 : MatrixOperator (pointHilbertSpace params)) := by
  ext u v
  have key :
      ∑ α : Point params,
        (fourierBasisProjector params α) u v =
      ∑ α : Point params,
        star (fourierBasisState params α v) * fourierBasisState params α u := by
    refine Finset.sum_congr rfl ?_
    intro α _
    simp [fourierBasisProjector, Matrix.vecMulVec_apply]; ring
  have hsum :
      (∑ α : Point params, fourierBasisProjector params α) u v =
        ∑ α : Point params, (fourierBasisProjector params α) u v := by
    simpa using
      (Matrix.sum_apply u v (Finset.univ : Finset (Point params))
        (fun α => fourierBasisProjector params α))
  rw [hsum, key, fourierBasisState_inner_product_dual params v u]
  by_cases h : v = u
  · subst v
    change (if u = u then (1 : ℂ) else 0) = (if u = u then 1 else 0)
    try rfl -- vendoring compile fix (Lean v4.33): the previous step may close the goal
  · change (if v = u then (1 : ℂ) else 0) = (if u = v then 1 else 0)
    simp [h, show u ≠ v by intro huv; exact h huv.symm]

lemma frequencyWeight_zero (params : Parameters) :
    frequencyWeight params (0 : Point params) = 0 := by
  simp [frequencyWeight]

lemma frequencyWeight_pos_of_ne_zero (params : Parameters) {α : Point params}
    (hα : α ≠ 0) : 0 < frequencyWeight params α := by
  rw [frequencyWeight, Finset.card_pos]
  by_contra hempty
  apply hα
  funext i
  by_contra hi
  have hi_mem : i ∈ Finset.univ.filter (fun j : Fin params.m => α j ≠ (0 : Fq params)) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hi
  exact hempty ⟨i, hi_mem⟩

lemma fourierBasis_norm_sq (params : Parameters) :
    (((Real.sqrt (hypercubeVertexCount params : ℝ))⁻¹ : ℂ) *
      star (((Real.sqrt (hypercubeVertexCount params : ℝ))⁻¹ : ℂ))) =
        (hypercubeVertexCount params : ℂ)⁻¹ := by
  have hMpos : 0 < (hypercubeVertexCount params : ℝ) := by
    exact_mod_cast (pow_pos params.hq params.m)
  have hsqrt_ne : Real.sqrt (hypercubeVertexCount params : ℝ) ≠ 0 :=
    Real.sqrt_ne_zero'.2 hMpos
  have hnormR : (Real.sqrt (hypercubeVertexCount params : ℝ))⁻¹ *
      (Real.sqrt (hypercubeVertexCount params : ℝ))⁻¹ =
    (hypercubeVertexCount params : ℝ)⁻¹ := by
    field_simp [hsqrt_ne]
    nlinarith [Real.sq_sqrt (le_of_lt hMpos)]
  have hstar : star ((Real.sqrt (hypercubeVertexCount params : ℝ))⁻¹ : ℂ) =
    ((Real.sqrt (hypercubeVertexCount params : ℝ))⁻¹ : ℂ) := by
    simp [Complex.conj_ofReal]
  rw [hstar]
  simpa [Complex.ofReal_inv, Complex.ofReal_mul] using
    congrArg (fun x : ℝ => (x : ℂ)) hnormR

lemma constantModeProjectorMatrix_eq_fourierBasisProjector_zero (params : Parameters) :
    constantModeProjectorMatrix params = fourierBasisProjector params 0 := by
  ext u v
  simp only [constantModeProjectorMatrix, fourierBasisProjector, fourierBasisState,
    Matrix.vecMulVec_apply, Pi.star_apply]
  have hzero : ∀ w : Point params, addCharFq params (dotProductFq params w 0) = 1 := by
    intro w
    have : dotProductFq params w 0 = ⟨0, params.hq⟩ := by simp [dotProductFq]
    rw [this]; simp [addCharFq]
  simp only [star_mul]
  rw [hzero u, hzero v]
  simpa [mul_assoc] using (fourierBasis_norm_sq params).symm

lemma orthogonalModeProjectorMatrix_eq_sum (params : Parameters) :
    orthogonalModeProjectorMatrix params =
      ∑ α ∈ (Finset.univ.erase (0 : Point params)), fourierBasisProjector params α := by
  have hsplit :
      fourierBasisProjector params 0 +
          ∑ α ∈ (Finset.univ.erase (0 : Point params)), fourierBasisProjector params α =
        ∑ α : Point params, fourierBasisProjector params α := by
    exact
      (Finset.add_sum_erase (s := (Finset.univ : Finset (Point params)))
         (f := fun α => fourierBasisProjector params α) (Finset.mem_univ _))
  calc
    orthogonalModeProjectorMatrix params
      = (∑ α : Point params, fourierBasisProjector params α) - fourierBasisProjector params 0 := by
          rw [orthogonalModeProjectorMatrix,
            constantModeProjectorMatrix_eq_fourierBasisProjector_zero,
            sum_fourierBasisProjector_eq_one]
          try rfl -- vendoring compile fix (Lean v4.33): the previous step may close the goal
    _ = ∑ α ∈ (Finset.univ.erase (0 : Point params)), fourierBasisProjector params α := by
          rw [← hsplit]
          simp [sub_eq_add_neg, add_left_comm]

lemma matrixAdjacencyOperator_spectral_decomp (params : Parameters) :
    matrixAdjacencyOperator params =
      ∑ α : Point params,
        (((adjacencyEigenvalue params α : Error) : ℂ) • fourierBasisProjector params α) := by
  ext u v
  rw [Matrix.sum_apply]
  calc
    (matrixAdjacencyOperator params) u v
      = ∑ w : Point params,
          (matrixAdjacencyOperator params) u w *
            (if v = w then (1 : ℂ) else 0) := by
              symm
              simpa using
                (Finset.sum_eq_single
                  (s := (Finset.univ : Finset (Point params)))
                  (f := fun w : Point params =>
                    (matrixAdjacencyOperator params) u w *
                      (if v = w then (1 : ℂ) else 0))
                  v
              (by
                    intro w _ hw
                    simp [show ¬v = w by intro hvw; exact hw hvw.symm])
                  (by simp))
    _ = ∑ w : Point params,
          (matrixAdjacencyOperator params) u w *
            ∑ α : Point params,
              star (fourierBasisState params α v) * fourierBasisState params α w := by
            congr 1 with w
            rw [fourierBasisState_inner_product_dual params v w]
            try rfl -- vendoring compile fix (Lean v4.33): the previous step may close the goal
    _ = ∑ α : Point params,
          star (fourierBasisState params α v) *
            ((matrixAdjacencyOperator params).mulVec (fourierBasisState params α)) u := by
          calc
            ∑ w : Point params,
                (matrixAdjacencyOperator params) u w *
                  ∑ α : Point params,
                    star (fourierBasisState params α v) * fourierBasisState params α w
              = ∑ w : Point params,
                  ∑ α : Point params,
                    (matrixAdjacencyOperator params) u w *
                      (star (fourierBasisState params α v) * fourierBasisState params α w) := by
                        refine Finset.sum_congr rfl ?_
                        intro w _
                        rw [Finset.mul_sum]
            _ = ∑ α : Point params,
                  ∑ w : Point params,
                    star (fourierBasisState params α v) *
                      ((matrixAdjacencyOperator params) u w * fourierBasisState params α w) := by
                        rw [Finset.sum_comm]
                        refine Finset.sum_congr rfl ?_
                        intro α _
                        refine Finset.sum_congr rfl ?_
                        intro w _
                        ring
            _ = ∑ α : Point params,
                  star (fourierBasisState params α v) *
                    ((matrixAdjacencyOperator params).mulVec (fourierBasisState params α)) u := by
                        refine Finset.sum_congr rfl ?_
                        intro α _
                        rw [Matrix.mulVec, dotProduct]
                        exact
                          (Finset.mul_sum
                            (s := (Finset.univ : Finset (Point params)))
                            (a := star (fourierBasisState params α v))
                            (f := fun i =>
                              (matrixAdjacencyOperator params) u i *
                                fourierBasisState params α i)).symm
    _ = ∑ α : Point params,
          (((adjacencyEigenvalue params α : Error) : ℂ) •
            fourierBasisProjector params α) u v := by
          refine Finset.sum_congr rfl ?_
          intro α _
          have hα := congrFun (eigenvectors params α) u
          simp only [Pi.smul_apply] at hα
          simp [fourierBasisProjector, Matrix.vecMulVec_apply, hα, mul_assoc, mul_comm]

lemma matrixLaplacianOperator_spectral_decomp (params : Parameters) :
    matrixLaplacianOperator params =
      ∑ α : Point params,
        (((laplacianEigenvalue params α : Error) : ℂ) • fourierBasisProjector params α) := by
  have hrel :
      ∀ α : Point params,
        (((laplacianEigenvalue params α : Error) : ℂ)) =
          (hypercubeVertexCount params : ℂ)⁻¹ -
            (((adjacencyEigenvalue params α : Error) : ℂ)) := by
    intro α
    simpa [one_div] using
      congrArg (fun x : Error => (x : ℂ))
        (laplacianEigenvalue_eq params α)
  calc
    matrixLaplacianOperator params
      = ((hypercubeVertexCount params : ℂ)⁻¹) •
            ∑ α : Point params, fourierBasisProjector params α -
          ∑ α : Point params,
            (((adjacencyEigenvalue params α : Error) : ℂ) • fourierBasisProjector params α) := by
          rw [matrixLaplacianOperator, sum_fourierBasisProjector_eq_one,
            matrixAdjacencyOperator_spectral_decomp]
          try rfl -- vendoring compile fix (Lean v4.33): the previous step may close the goal
    _ = ∑ α : Point params,
          (((hypercubeVertexCount params : ℂ)⁻¹ -
              (((adjacencyEigenvalue params α : Error) : ℂ))) •
            fourierBasisProjector params α) := by
          rw [Finset.smul_sum]
          ext u v
          rw [Matrix.sub_apply, Matrix.sum_apply, Matrix.sum_apply, Matrix.sum_apply,
            ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl ?_
          intro α _
          simp [sub_mul]
    _ = ∑ α : Point params,
          (((laplacianEigenvalue params α : Error) : ℂ) • fourierBasisProjector params α) := by
          refine Finset.sum_congr rfl ?_
          intro α _
          rw [hrel α]

lemma laplacianEigenvalue_zero (params : Parameters) :
    laplacianEigenvalue params (0 : Point params) = 0 := by
  simp [laplacianEigenvalue, frequencyWeight_zero]

lemma hypercubeSpectralGap_operator_posSemidef (params : Parameters) :
    (matrixLaplacianOperator params -
      ((hypercubeSpectralGap params : ℂ) • orthogonalModeProjectorMatrix params)).PosSemidef := by
  have hlap0 := laplacianEigenvalue_zero params
  have hcoeff_nonneg :
      ∀ α ∈ (Finset.univ.erase (0 : Point params)),
        0 ≤ laplacianEigenvalue params α - hypercubeSpectralGap params := by
    intro α hα
    have hα0 : α ≠ 0 := by simpa using Finset.mem_erase.mp hα |>.1
    exact sub_nonneg.mpr <|
      hypercubeSpectralGap_le_laplacianEigenvalue params α
        (frequencyWeight_pos_of_ne_zero params hα0)
  have hdecomp :
      matrixLaplacianOperator params -
          ((hypercubeSpectralGap params : ℂ) • orthogonalModeProjectorMatrix params) =
        ∑ α ∈ (Finset.univ.erase (0 : Point params)),
          (((laplacianEigenvalue params α - hypercubeSpectralGap params : Error) : ℂ) •
            fourierBasisProjector params α) := by
    rw [matrixLaplacianOperator_spectral_decomp, orthogonalModeProjectorMatrix_eq_sum]
    have hweighted :
        ∑ α : Point params,
            (((laplacianEigenvalue params α : Error) : ℂ) • fourierBasisProjector params α) =
          ∑ α ∈ (Finset.univ.erase (0 : Point params)),
            (((laplacianEigenvalue params α : Error) : ℂ) •
              fourierBasisProjector params α) := by
      have hsplit :
          (((laplacianEigenvalue params 0 : Error) : ℂ) • fourierBasisProjector params 0) +
              ∑ α ∈ (Finset.univ.erase (0 : Point params)),
                (((laplacianEigenvalue params α : Error) : ℂ) •
                  fourierBasisProjector params α) =
            ∑ α : Point params,
              (((laplacianEigenvalue params α : Error) : ℂ) •
                fourierBasisProjector params α) := by
        exact
          (Finset.add_sum_erase (s := (Finset.univ : Finset (Point params)))
            (f := fun α =>
              (((laplacianEigenvalue params α : Error) : ℂ) • fourierBasisProjector params α))
            (Finset.mem_univ _))
      rw [← hsplit]
      simp [hlap0]
    calc
      (∑ α : Point params,
          (((laplacianEigenvalue params α : Error) : ℂ) • fourierBasisProjector params α)) -
          ((hypercubeSpectralGap params : ℂ) •
            ∑ α ∈ (Finset.univ.erase (0 : Point params)), fourierBasisProjector params α)
        = (∑ α ∈ (Finset.univ.erase (0 : Point params)),
            (((laplacianEigenvalue params α : Error) : ℂ) •
              fourierBasisProjector params α)) -
            ((hypercubeSpectralGap params : ℂ) •
              ∑ α ∈ (Finset.univ.erase (0 : Point params)), fourierBasisProjector params α) := by
            rw [hweighted]
      _ = (∑ α ∈ (Finset.univ.erase (0 : Point params)),
            (((laplacianEigenvalue params α : Error) : ℂ) •
              fourierBasisProjector params α)) -
            ∑ α ∈ (Finset.univ.erase (0 : Point params)),
              ((hypercubeSpectralGap params : ℂ) • fourierBasisProjector params α) := by
            rw [Finset.smul_sum]
      _ = ∑ α ∈ (Finset.univ.erase (0 : Point params)),
            ((((laplacianEigenvalue params α : Error) : ℂ) •
                fourierBasisProjector params α) -
              ((hypercubeSpectralGap params : ℂ) • fourierBasisProjector params α)) := by
            rw [Finset.sum_sub_distrib]
      _ = ∑ α ∈ (Finset.univ.erase (0 : Point params)),
            (((laplacianEigenvalue params α - hypercubeSpectralGap params : Error) : ℂ) •
              fourierBasisProjector params α) := by
            refine Finset.sum_congr rfl ?_
            intro α hα
            rw [← sub_smul]
            norm_num
  rw [hdecomp]
  refine Matrix.posSemidef_sum _ ?_
  intro α hα
  have hproj :
      (fourierBasisProjector params α).PosSemidef := by
    simpa [fourierBasisProjector] using
      (Matrix.posSemidef_vecMulVec_self_star (fourierBasisState params α))
  have hmatrix :
      ((laplacianEigenvalue params α - hypercubeSpectralGap params : Error) •
          fourierBasisProjector params α) =
        (((laplacianEigenvalue params α - hypercubeSpectralGap params : Error) : ℂ) •
          fourierBasisProjector params α) := by
    ext u v
    simp
  change
    ((((laplacianEigenvalue params α - hypercubeSpectralGap params : Error) : ℂ) •
      fourierBasisProjector params α)).PosSemidef
  rw [← hmatrix]
  exact hproj.smul (hcoeff_nonneg α hα)

end MIPStarRE.LDT.ExpansionHypercubeGraph


