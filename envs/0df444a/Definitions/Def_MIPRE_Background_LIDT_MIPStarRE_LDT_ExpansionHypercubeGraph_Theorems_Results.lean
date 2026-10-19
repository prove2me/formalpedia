-- Prove2me | Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Theorems_Results
-- name    : MIPRE_Background_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Theorems_Results
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T02:43:32.815072+00:00
-- url     : https://prove2.me/theorems/d69de832-3f44-4100-b7ac-42866c7b6adf
-- title:
--   Definitions of Results: Section 7 hypercube graph: local-to-global variance theorems This file assembles the public Section 7 results about the…
-- statement:
--   The definitions of the module `MIPRE.Background.LIDT.MIPStarRE.LDT.ExpansionHypercubeGraph.Theorems.Results` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Section 7 hypercube graph: local-to-global variance theorems. This file assembles the public Section 7 results about the hypercube graph: the Laplacian edge-difference formula, the local and global variance rewrites, and the local-to-global inequality. The proof route passes through the matrix-realization theorems and then exposes the statements in the `QuantumState` and operator-family language used elsewhere in the LDT formalization.
--
--   The module is vendored read-only, with the authors' permission, from [LionSR/MIPStarRE](https://github.com/LionSR/MIPStarRE) (Sirui Lu and the MIPStarRE contributors, Apache 2.0; commit and upstream path in the file header) by `scripts/vendor-lidt.py`.
--
--   **Embedded lemmas** (2): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `matrixLocalVariance_eq_closedForm`, `matrixTraceForm_localToGlobal`.
--
--   The bundle holds no definition of its own: it carries the lemmas listed above, which later bundles and proofs import.
--
--   **Formalization Note** The bundle is the module `MIPRE.Background.LIDT.MIPStarRE.LDT.ExpansionHypercubeGraph.Theorems.Results` (`MIPRE/Background/LIDT/MIPStarRE/LDT/ExpansionHypercubeGraph/Theorems/Results.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 19 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/LIDT/MIPStarRE/LDT/ExpansionHypercubeGraph/Theorems/Results.lean

/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/ExpansionHypercubeGraph/Theorems/Results.lean
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/MIPStarRE/LDT/ExpansionHypercubeGraph/Theorems/Results.lean (definition bundle: declarations the uploaded statements rest on);
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
import Mathlib.Algebra.Field.Basic
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
import Mathlib.Algebra.Order.Ring.Abs
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
import Mathlib.LinearAlgebra.Matrix.CharP
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
import Mathlib.Tactic.CancelDenoms.Core
import Mathlib.Tactic.FieldSimp.Lemmas
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Eq
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
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_QuantumState
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_SubMeasurementCore
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_OperatorExpectations
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_PMFAverages
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Fourier
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_MatrixRealization_Core
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_MatrixRealization_TraceForms
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Theorems_Foundations
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Theorems_Matrix
import Theorems.Thm_MIPStarRE_LDT_ExpansionHypercubeGraph_avgOver_rerandomizeCoord_eq_weight_sum
import Theorems.Thm_MIPStarRE_LDT_ExpansionHypercubeGraph_conjTranspose_mul_mul_mono
import Theorems.Thm_MIPStarRE_LDT_ExpansionHypercubeGraph_corr_symm
import Theorems.Thm_MIPStarRE_LDT_ExpansionHypercubeGraph_hypercubeSpectralGap_operator
import Theorems.Thm_MIPStarRE_LDT_ExpansionHypercubeGraph_normalizedTrace_re_mono
import Theorems.Thm_MIPStarRE_LDT_ExpansionHypercubeGraph_rerandomizeCoordWeight_colSum
import Theorems.Thm_MIPStarRE_LDT_ExpansionHypercubeGraph_rerandomizeCoordWeight_rowSum
import Theorems.Thm_MIPStarRE_LDT_ExpansionHypercubeGraph_sqdiff_eq_corr
import Theorems.Thm_MIPStarRE_LDT_ExpansionHypercubeGraph_sum_sum_add
import Theorems.Thm_MIPStarRE_LDT_ExpansionHypercubeGraph_sum_sum_sub
import Theorems.Thm_MIPStarRE_Quantum_kronecker_mono_left
import Theorems.Thm_MIPStarRE_Quantum_normalizedTrace_smul

set_option backward.isDefEq.respectTransparency false

/-!
# Section 7 hypercube graph: local-to-global variance theorems

This file assembles the public Section 7 results about the hypercube graph:
the Laplacian edge-difference formula, the local and global variance rewrites,
and the local-to-global inequality.  The proof route passes through the
matrix-realization theorems and then exposes the statements in the
`QuantumState` and operator-family language used elsewhere in the LDT
formalization.

## References

- `references/ldt-paper/expansion.tex`, especially `prop:laplacian-rewrite`,
  `lem:local-rewrite`, `lem:global-rewrite`, and `lem:local-to-global`
- `blueprint/src/chapter/ch05_expansion.tex`
-/

namespace MIPStarRE.LDT.ExpansionHypercubeGraph

open MIPStarRE.LDT
open MIPStarRE.LDT.MakingMeasurementsProjective
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

-- vendoring compile fix (Lean v4.33): the previous step may close the goal

lemma matrixLocalVariance_eq_closedForm (params : Parameters)
    (model : MatrixOperatorFamilyRealization params) :
    matrixLocalVariance params model =
      (hypercubeVertexCount params : Error)⁻¹ *
          ∑ u, ev (matrixModelState model) ((model.family u)ᴴ * model.family u) -
        ∑ u, ∑ v,
          rerandomizeCoordWeight params u v *
            ev (matrixModelState model) ((model.family v)ᴴ * model.family u) := by
  let diag : Point params → Error :=
    fun u => ev (matrixModelState model) ((model.family u)ᴴ * model.family u)
  let corr : Point params → Point params → Error :=
    fun u v => ev (matrixModelState model) ((model.family v)ᴴ * model.family u)
  let w : Point params → Point params → Error := rerandomizeCoordWeight params
  have hsqdiff : ∀ u v,
      matrixSquaredDifferenceExpectation model.state (model.family u) (model.family v) =
        diag u + diag v - corr u v - corr u v := by
    intro u v
    simp [diag, corr, sqdiff_eq_corr, corr_symm]
  have hdiagLeft :
      ∑ u : Point params, ∑ v : Point params, w u v * diag u =
        (hypercubeVertexCount params : Error)⁻¹ * ∑ u : Point params, diag u := by
    calc
      ∑ u : Point params, ∑ v : Point params, w u v * diag u
        = ∑ u : Point params, (∑ v : Point params, w u v) * diag u := by
            refine Finset.sum_congr rfl ?_
            intro u hu
            simpa using
              (Finset.sum_mul
                (s := (Finset.univ : Finset (Point params)))
                (f := fun v : Point params => w u v)
                (a := diag u)).symm
      _ = ∑ u : Point params, (hypercubeVertexCount params : Error)⁻¹ * diag u := by
            refine Finset.sum_congr rfl ?_
            intro u hu
            simp [w, rerandomizeCoordWeight_rowSum]
      _ = (hypercubeVertexCount params : Error)⁻¹ * ∑ u : Point params, diag u := by
            simpa using
              (Finset.mul_sum
                (s := (Finset.univ : Finset (Point params)))
                (f := diag)
                (a := (hypercubeVertexCount params : Error)⁻¹)).symm
  have hdiagRight :
      ∑ u : Point params, ∑ v : Point params, w u v * diag v =
        (hypercubeVertexCount params : Error)⁻¹ * ∑ u : Point params, diag u := by
    calc
      ∑ u : Point params, ∑ v : Point params, w u v * diag v
        = ∑ v : Point params, ∑ u : Point params, w u v * diag v := by
            rw [Finset.sum_comm]
      _ = ∑ v : Point params, (∑ u : Point params, w u v) * diag v := by
            refine Finset.sum_congr rfl ?_
            intro v hv
            simpa using
              (Finset.sum_mul
                (s := (Finset.univ : Finset (Point params)))
                (f := fun u : Point params => w u v)
                (a := diag v)).symm
      _ = ∑ v : Point params, (hypercubeVertexCount params : Error)⁻¹ * diag v := by
            refine Finset.sum_congr rfl ?_
            intro v hv
            simp [w, rerandomizeCoordWeight_colSum]
      _ = (hypercubeVertexCount params : Error)⁻¹ * ∑ v : Point params, diag v := by
            simpa using
              (Finset.mul_sum
                (s := (Finset.univ : Finset (Point params)))
                (f := diag)
                (a := (hypercubeVertexCount params : Error)⁻¹)).symm
  unfold matrixLocalVariance matrixHypercubeEdgeDistribution
  rw [avgOver_rerandomizeCoord_eq_weight_sum]
  rw [Fintype.sum_prod_type]
  simp_rw [hsqdiff]
  let diagSum : Error := ∑ u, diag u
  let corrSum : Error := ∑ u, ∑ v, w u v * corr u v
  let diagLeft : Error := ∑ u : Point params, ∑ v : Point params, w u v * diag u
  let diagRight : Error := ∑ u : Point params, ∑ v : Point params, w u v * diag v
  have hsplit :
      ∑ u, ∑ v, w u v * (diag u + diag v - corr u v - corr u v) =
        diagLeft + diagRight - corrSum - corrSum := by
    unfold diagLeft diagRight corrSum
    calc
      ∑ u, ∑ v, w u v * (diag u + diag v - corr u v - corr u v)
          = ∑ u, ∑ v,
              (w u v * diag u +
                (w u v * diag v - w u v * corr u v - w u v * corr u v)) := by
              refine Finset.sum_congr rfl ?_
              intro u hu
              refine Finset.sum_congr rfl ?_
              intro v hv
              ring
      _ = ∑ u, ∑ v, w u v * diag u +
            ∑ u, ∑ v, (w u v * diag v - w u v * corr u v - w u v * corr u v) := by
              exact sum_sum_add
                (f := fun u v => w u v * diag u)
                (g := fun u v => w u v * diag v - w u v * corr u v - w u v * corr u v)
      _ = ∑ u, ∑ v, w u v * diag u +
            ((∑ u, ∑ v, w u v * diag v) - (∑ u, ∑ v, w u v * corr u v) -
              (∑ u, ∑ v, w u v * corr u v)) := by
              congr 1
              rw [sum_sum_sub, sum_sum_sub]
      _ = diagLeft + diagRight - corrSum - corrSum := by ring
  have hsum :
      ∑ u, ∑ v, w u v * (diag u + diag v - corr u v - corr u v) =
        2 * ((hypercubeVertexCount params : Error)⁻¹ * diagSum - corrSum) := by
    calc
      ∑ u, ∑ v, w u v * (diag u + diag v - corr u v - corr u v)
          = diagLeft + diagRight - corrSum - corrSum := hsplit
      _ = (hypercubeVertexCount params : Error)⁻¹ * diagSum +
            (hypercubeVertexCount params : Error)⁻¹ * diagSum - corrSum - corrSum := by
              rw [show diagLeft = (hypercubeVertexCount params : Error)⁻¹ * diagSum by
                    simpa [diagLeft, diagSum] using hdiagLeft]
              rw [show diagRight = (hypercubeVertexCount params : Error)⁻¹ * diagSum by
                    simpa [diagRight, diagSum] using hdiagRight]
      _ = 2 * ((hypercubeVertexCount params : Error)⁻¹ * diagSum - corrSum) := by ring
  rw [hsum]
  calc
    (1 / 2 : Error) * (2 * ((hypercubeVertexCount params : Error)⁻¹ * diagSum - corrSum))
      = (hypercubeVertexCount params : Error)⁻¹ * diagSum - corrSum := by ring
    _ =
        (hypercubeVertexCount params : Error)⁻¹ *
            ∑ u, ev (matrixModelState model) ((model.family u)ᴴ * model.family u) -
          ∑ u, ∑ v,
            rerandomizeCoordWeight params u v *
              ev (matrixModelState model) ((model.family v)ᴴ * model.family u) := by
            simp [diagSum, corrSum, w, diag, corr]

lemma matrixTraceForm_localToGlobal (params : Parameters)
    (model : MatrixOperatorFamilyRealization params) :
    matrixGlobalVarianceTraceForm params model ≤
      (params.m : Error) * matrixLocalVarianceTraceForm params model := by
  have htensor :
      matrixTensorOperator (((hypercubeSpectralGap params : ℂ) •
          orthogonalModeProjectorMatrix params)) model.state.matrix ≤
        matrixTensorOperator (matrixLaplacianOperator params) model.state.matrix := by
    change Matrix.kronecker
        (((hypercubeSpectralGap params : ℂ) • orthogonalModeProjectorMatrix params))
        model.state.matrix ≤
      Matrix.kronecker (matrixLaplacianOperator params) model.state.matrix
    exact MIPStarRE.Quantum.kronecker_mono_left
      (hypercubeSpectralGap_operator params) model.state.positive
  have hwitness :
      ((hypercubeSpectralGap params : ℂ) • matrixGlobalVarianceTraceWitness params model) ≤
        matrixLocalVarianceTraceWitness params model := by
    have hraw :=
      MIPStarRE.LDT.ExpansionHypercubeGraph.conjTranspose_mul_mul_mono
        (matrixCombinedColumnOperator params model) htensor
    let c : ℂ := hypercubeSpectralGap params
    have hscale :
        (matrixCombinedColumnOperator params model)ᴴ *
            (matrixTensorOperator (c • orthogonalModeProjectorMatrix params) model.state.matrix *
              matrixCombinedColumnOperator params model) =
          c • matrixGlobalVarianceTraceWitness params model := by
      calc
        (matrixCombinedColumnOperator params model)ᴴ *
            (matrixTensorOperator (c • orthogonalModeProjectorMatrix params) model.state.matrix *
              matrixCombinedColumnOperator params model)
          = (matrixCombinedColumnOperator params model)ᴴ *
              (((c • matrixTensorOperator (orthogonalModeProjectorMatrix params)
                  model.state.matrix) *
                matrixCombinedColumnOperator params model)) := by
                  simp [matrixTensorOperator, Matrix.smul_kronecker]
                  try rfl -- vendoring compile fix (Lean v4.33): the previous step may close the goal
        _ = c •
              ((matrixCombinedColumnOperator params model)ᴴ *
                (matrixTensorOperator (orthogonalModeProjectorMatrix params)
                  model.state.matrix *
                  matrixCombinedColumnOperator params model)) := by
                  simp
        _ = c • matrixGlobalVarianceTraceWitness params model := by
                  simp [matrixGlobalVarianceTraceWitness]
    change
      (matrixCombinedColumnOperator params model)ᴴ *
          (matrixTensorOperator (c • orthogonalModeProjectorMatrix params) model.state.matrix *
            matrixCombinedColumnOperator params model) ≤
        matrixLocalVarianceTraceWitness params model at hraw
    rw [hscale] at hraw
    simpa [c] using hraw
  have htrace :
      hypercubeSpectralGap params *
          Complex.re (MIPStarRE.Quantum.normalizedTrace
            (matrixGlobalVarianceTraceWitness params model)) ≤
        Complex.re (MIPStarRE.Quantum.normalizedTrace
          (matrixLocalVarianceTraceWitness params model)) := by
    have hmono := MIPStarRE.LDT.ExpansionHypercubeGraph.normalizedTrace_re_mono hwitness
    rw [MIPStarRE.Quantum.normalizedTrace_smul] at hmono
    simpa [Complex.mul_re] using hmono
  have hm_nonneg : 0 ≤ (params.m : Error) := by positivity
  have hm_ne : (params.m : Error) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt params.hm)
  have hM_pos : 0 < hypercubeVertexCount params := by
    simp [hypercubeVertexCount, pow_pos params.hq]
  have hM_ne : (hypercubeVertexCount params : Error) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hM_pos)
  have hgap_scale :
      (params.m : Error) * hypercubeSpectralGap params =
        (hypercubeVertexCount params : Error)⁻¹ := by
    unfold hypercubeSpectralGap
    field_simp [hm_ne, hM_ne]
  have hgap_scale' :
      1 / (hypercubeVertexCount params : Error) =
        (params.m : Error) * hypercubeSpectralGap params := by
    simpa [one_div] using hgap_scale.symm
  have hmul := mul_le_mul_of_nonneg_left htrace hm_nonneg
  calc
    matrixGlobalVarianceTraceForm params model
      = (params.m : Error) *
          (hypercubeSpectralGap params *
            Complex.re (MIPStarRE.Quantum.normalizedTrace
              (matrixGlobalVarianceTraceWitness params model))) := by
          rw [matrixGlobalVarianceTraceForm, hgap_scale']
          ring
    _ ≤ (params.m : Error) *
          Complex.re (MIPStarRE.Quantum.normalizedTrace
            (matrixLocalVarianceTraceWitness params model)) := hmul
    _ = (params.m : Error) * matrixLocalVarianceTraceForm params model := by
          simp [matrixLocalVarianceTraceForm]

/-! ## Public theorem wrappers -/

end MIPStarRE.LDT.ExpansionHypercubeGraph


