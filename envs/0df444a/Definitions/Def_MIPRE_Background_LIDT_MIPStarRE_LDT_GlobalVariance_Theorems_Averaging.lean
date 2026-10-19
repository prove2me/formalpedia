-- Prove2me | Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_Averaging
-- name    : MIPRE_Background_LIDT_MIPStarRE_LDT_GlobalVariance_Theorems_Averaging
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T02:23:20.499728+00:00
-- url     : https://prove2.me/theorems/bd33342c-e36b-40a7-a3de-3b5a18d464d4
-- title:
--   Definitions of Averaging: Uniform averaging infrastructure
-- statement:
--   The definitions of the module `MIPRE.Background.LIDT.MIPStarRE.LDT.GlobalVariance.Theorems.Averaging` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). ## Uniform averaging infrastructure
--
--   The module is vendored read-only, with the authors' permission, from [LionSR/MIPStarRE](https://github.com/LionSR/MIPStarRE) (Sirui Lu and the MIPStarRE contributors, Apache 2.0; commit and upstream path in the file header) by `scripts/vendor-lidt.py`.
--
--   **Embedded lemmas** (2): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `ev_uniformAverage_sq_le_avg`, `qSDD_unit_family_of_average_le_avg`.
--
--   The bundle holds no definition of its own: it carries the lemmas listed above, which later bundles and proofs import.
--
--   **Formalization Note** The bundle is the module `MIPRE.Background.LIDT.MIPStarRE.LDT.GlobalVariance.Theorems.Averaging` (`MIPRE/Background/LIDT/MIPStarRE/LDT/GlobalVariance/Theorems/Averaging.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 26 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/LIDT/MIPStarRE/LDT/GlobalVariance/Theorems/Averaging.lean

/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/GlobalVariance/Theorems/Averaging.lean
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/MIPStarRE/LDT/GlobalVariance/Theorems/Averaging.lean (definition bundle: declarations the uploaded statements rest on);
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
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Families
import Theorems.Thm_MIPStarRE_LDT_avgOver_nonneg
import Theorems.Thm_MIPStarRE_LDT_ev_abs_mul_le_sqrt
import Theorems.Thm_MIPStarRE_LDT_ev_adjoint_self_nonneg
import Theorems.Thm_MIPStarRE_LDT_ev_scale
import Theorems.Thm_MIPStarRE_LDT_ev_sum

set_option backward.isDefEq.respectTransparency false

namespace MIPStarRE.LDT.GlobalVariance

open MIPStarRE.LDT
open MIPStarRE.LDT.MakingMeasurementsProjective
open MIPStarRE.LDT.ExpansionHypercubeGraph
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Uniform averaging infrastructure -/

lemma ev_uniformAverage_sq_le_avg
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    (ψ : QuantumState ι)
    (D : α → MIPStarRE.Quantum.Op ι) :
    ev ψ
      ((averageOperatorOverDistribution (uniformDistribution α) D)ᴴ *
        averageOperatorOverDistribution (uniformDistribution α) D)
      ≤ avgOver (uniformDistribution α) (fun a => ev ψ ((D a)ᴴ * D a)) := by
  let c : Error := 1 / (Fintype.card α : Error)
  let S : MIPStarRE.Quantum.Op ι :=
    averageOperatorOverDistribution (uniformDistribution α) D
  let x : α → Error := fun a => ev ψ ((D a)ᴴ * D a)
  have hc_nonneg : 0 ≤ c := by
    positivity
  have hx_nonneg : ∀ a, 0 ≤ x a := by
    intro a
    exact ev_adjoint_self_nonneg ψ (D a)
  have hcard : (Fintype.card α : Error) ≠ 0 := by
    positivity
  have hsumc : ∑ a : α, c = 1 := by
    unfold c
    calc
      ∑ a : α, (1 / (Fintype.card α : Error))
          = (Fintype.card α : Error) * (1 / (Fintype.card α : Error)) := by
              simp [Finset.sum_const, nsmul_eq_mul]
      _ = 1 := by
            field_simp [hcard]
  have h_expand :
      ev ψ (Sᴴ * S)
        = ∑ a : α, ∑ b : α, c * (c * ev ψ ((D a)ᴴ * D b)) := by
    have hSsum : S = ∑ a : α, c • D a := by
      ext i j
      simp [S, c, averageOperatorOverDistribution, uniformDistribution]
    have hconj :
        (∑ a : α, c • D a)ᴴ = ∑ a : α, c • (D a)ᴴ := by
      simpa using
        (Matrix.conjTranspose_sum (s := Finset.univ)
          (M := fun a : α => c • D a))
    calc
      ev ψ (Sᴴ * S)
        = ev ψ (((∑ a : α, c • D a)ᴴ) * ∑ b : α, c • D b) := by
            rw [hSsum]
      _ = ev ψ ((∑ a : α, c • (D a)ᴴ) * ∑ b : α, c • D b) := by
            rw [hconj]
      _ = ev ψ (∑ b : α, ∑ a : α, ((c • (D a)ᴴ) * (c • D b))) := by
            congr 1
            rw [Matrix.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro b _
            rw [Finset.sum_mul]
      _ = ev ψ (∑ a : α, ∑ b : α, ((c • (D a)ᴴ) * (c • D b))) := by
            congr 1
            rw [Finset.sum_comm]
      _ = ∑ a : α, ∑ b : α, ev ψ ((c • (D a)ᴴ) * (c • D b)) := by
            rw [ev_sum]
            refine Finset.sum_congr rfl ?_
            intro a _
            rw [ev_sum]
      _ = ∑ a : α, ∑ b : α, c * (c * ev ψ ((D a)ᴴ * D b)) := by
            refine Finset.sum_congr rfl ?_
            intro a _
            refine Finset.sum_congr rfl ?_
            intro b _
            rw [show ((c • (D a)ᴴ) * (c • D b)) =
                c • (c • ((D a)ᴴ * D b)) by
                  rw [smul_mul_assoc, mul_smul_comm]]
            rw [show c • (c • ((D a)ᴴ * D b)) =
                ((c : ℂ) • ((c : ℂ) • ((D a)ᴴ * D b))) by rfl]
            rw [ev_scale, ev_scale]
  have h_bound :
      ∑ a : α, ∑ b : α, c * (c * ev ψ ((D a)ᴴ * D b))
        ≤ ∑ a : α, ∑ b : α, c * (c * (Real.sqrt (x a) * Real.sqrt (x b))) := by
    refine Finset.sum_le_sum ?_
    intro a _
    refine Finset.sum_le_sum ?_
    intro b _
    have hab :
        ev ψ ((D a)ᴴ * D b) ≤ Real.sqrt (x a) * Real.sqrt (x b) := by
      calc
        ev ψ ((D a)ᴴ * D b) ≤ |ev ψ ((D a)ᴴ * D b)| := le_abs_self _
        _ ≤ Real.sqrt (x a) * Real.sqrt (x b) := by
              simpa [x] using ev_abs_mul_le_sqrt ψ ((D a)ᴴ) (D b)
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hab hc_nonneg) hc_nonneg
  let s : Error := ∑ a : α, c * Real.sqrt (x a)
  have hs_square :
      ∑ a : α, ∑ b : α, c * (c * (Real.sqrt (x a) * Real.sqrt (x b))) = s * s := by
    unfold s
    calc
      ∑ a : α, ∑ b : α, c * (c * (Real.sqrt (x a) * Real.sqrt (x b)))
        = ∑ a : α, (c * Real.sqrt (x a)) * ∑ b : α, c * Real.sqrt (x b) := by
            refine Finset.sum_congr rfl ?_
            intro a _
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro b _
            ring
      _ = (∑ a : α, c * Real.sqrt (x a)) * ∑ b : α, c * Real.sqrt (x b) := by
            rw [← Finset.sum_mul]
      _ = s * s := by
            try rfl -- vendoring compile fix (Lean v4.33): the previous step may close the goal
  have hs_le :
      s ≤ Real.sqrt (avgOver (uniformDistribution α) x) := by
    have hs_raw :
        ∑ a : α, Real.sqrt (c * x a) * Real.sqrt c
          ≤ Real.sqrt (∑ a : α, c * x a) * Real.sqrt (∑ a : α, c) := by
            exact Real.sum_sqrt_mul_sqrt_le (s := Finset.univ)
              (f := fun a => c * x a) (g := fun _ => c)
              (fun a => mul_nonneg hc_nonneg (hx_nonneg a))
              (fun _ => hc_nonneg)
    have hs_lhs :
        ∑ a : α, Real.sqrt (c * x a) * Real.sqrt c = s := by
      unfold s
      refine Finset.sum_congr rfl ?_
      intro a _
      calc
        Real.sqrt (c * x a) * Real.sqrt c
          = Real.sqrt c * Real.sqrt (x a) * Real.sqrt c := by
              rw [Real.sqrt_mul hc_nonneg (x a)]
        _ = (Real.sqrt c * Real.sqrt c) * Real.sqrt (x a) := by
              ring
        _ = c * Real.sqrt (x a) := by
              rw [show Real.sqrt c * Real.sqrt c = c by
                nlinarith [Real.sq_sqrt hc_nonneg]]
    have hs_rhs :
        Real.sqrt (∑ a : α, c * x a) * Real.sqrt (∑ a : α, c) =
          Real.sqrt (avgOver (uniformDistribution α) x) := by
      rw [hsumc, Real.sqrt_one, mul_one]
      simp [avgOver, uniformDistribution, c]
    rw [hs_lhs, hs_rhs] at hs_raw
    exact hs_raw
  have hs_nonneg : 0 ≤ s := by
    unfold s
    exact Finset.sum_nonneg fun a _ => mul_nonneg hc_nonneg (Real.sqrt_nonneg _)
  have havg_nonneg : 0 ≤ avgOver (uniformDistribution α) x := by
    exact avgOver_nonneg _ _ hx_nonneg
  calc
    ev ψ (Sᴴ * S)
      = ∑ a : α, ∑ b : α, c * (c * ev ψ ((D a)ᴴ * D b)) := h_expand
    _ ≤ ∑ a : α, ∑ b : α, c * (c * (Real.sqrt (x a) * Real.sqrt (x b))) := h_bound
    _ = s * s := hs_square
    _ ≤ avgOver (uniformDistribution α) x := by
          nlinarith [hs_nonneg, hs_le, Real.sq_sqrt havg_nonneg]

lemma qSDD_unit_family_of_average_le_avg
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    (ψ : QuantumState ι)
    (MA MB : SubMeas Unit ι)
    (A B : α → MIPStarRE.Quantum.Op ι)
    (hMA :
      MA.outcome () = averageOperatorOverDistribution (uniformDistribution α) A)
    (hMB :
      MB.outcome () = averageOperatorOverDistribution (uniformDistribution α) B) :
    qSDD ψ MA MB
      ≤ avgOver (uniformDistribution α)
          (fun a => ev ψ (((A a - B a)ᴴ) * (A a - B a))) := by
  let D : α → MIPStarRE.Quantum.Op ι := fun a => A a - B a
  have havg_sub :
      averageOperatorOverDistribution (uniformDistribution α) A -
          averageOperatorOverDistribution (uniformDistribution α) B =
        averageOperatorOverDistribution (uniformDistribution α) D := by
    simp [D, averageOperatorOverDistribution,
      uniformDistribution, Finset.sum_sub_distrib, smul_sub]
  calc
    qSDD ψ MA MB
      = ev ψ
          (((averageOperatorOverDistribution (uniformDistribution α) A -
              averageOperatorOverDistribution (uniformDistribution α) B)ᴴ) *
            (averageOperatorOverDistribution (uniformDistribution α) A -
              averageOperatorOverDistribution (uniformDistribution α) B)) := by
              unfold qSDD qSDDCore
              simp [hMA, hMB]
    _ = ev ψ
          ((averageOperatorOverDistribution (uniformDistribution α) D)ᴴ *
            averageOperatorOverDistribution (uniformDistribution α) D) := by
          rw [havg_sub]
    _ ≤ avgOver (uniformDistribution α) (fun a => ev ψ ((D a)ᴴ * D a)) := by
          exact ev_uniformAverage_sq_le_avg ψ D
    _ = avgOver (uniformDistribution α)
          (fun a => ev ψ (((A a - B a)ᴴ) * (A a - B a))) := by
          try rfl -- vendoring compile fix (Lean v4.33): the previous step may close the goal

/-! ## Averaging and local-to-global helpers -/

end MIPStarRE.LDT.GlobalVariance


