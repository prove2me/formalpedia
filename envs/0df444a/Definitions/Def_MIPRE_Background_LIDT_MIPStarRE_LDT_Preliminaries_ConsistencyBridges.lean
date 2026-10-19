-- Prove2me | Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_ConsistencyBridges
-- name    : MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_ConsistencyBridges
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T02:45:25.763208+00:00
-- url     : https://prove2.me/theorems/34ab8919-8f08-447a-9853-431733681ef0
-- title:
--   Definitions of ConsistencyBridges: Preliminary comparison theorems: consistency-to-distance estimates Estimates converting consistency of a submeasurement…
-- statement:
--   The definitions of the module `MIPRE.Background.LIDT.MIPStarRE.LDT.Preliminaries.ConsistencyBridges` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Preliminary comparison theorems: consistency-to-distance estimates. Estimates converting consistency of a submeasurement and a measurement into state-dependent distance controls for the diagonal and total sandwich families of `prop:cons-sub-meas`.
--
--   The module is vendored read-only, with the authors' permission, from [LionSR/MIPStarRE](https://github.com/LionSR/MIPStarRE) (Sirui Lu and the MIPStarRE contributors, Apache 2.0; commit and upstream path in the file header) by `scripts/vendor-lidt.py`.
--
--   **Embedded lemmas** (3): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `consSubMeas_controlHelper`, `consSubMeas_diagonalControl`, `consSubMeas_sandwichControl`.
--
--   The bundle holds no definition of its own: it carries the lemmas listed above, which later bundles and proofs import.
--
--   **Formalization Note** The bundle is the module `MIPRE.Background.LIDT.MIPStarRE.LDT.Preliminaries.ConsistencyBridges` (`MIPRE/Background/LIDT/MIPStarRE/LDT/Preliminaries/ConsistencyBridges.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 23 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/LIDT/MIPStarRE/LDT/Preliminaries/ConsistencyBridges.lean

/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/Preliminaries/ConsistencyBridges.lean
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/MIPStarRE/LDT/Preliminaries/ConsistencyBridges.lean (definition bundle: declarations the uploaded statements rest on);
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
import Mathlib.Data.Fintype.Option
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
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Logic.Basic
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Equiv.Prod
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
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_MeasurementLift
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_Defs
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_ComparisonCore
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_DistanceBounds
import Theorems.Thm_MIPStarRE_LDT_Measurement_outcome_le_one
import Theorems.Thm_MIPStarRE_LDT_Measurement_sum_eq
import Theorems.Thm_MIPStarRE_LDT_SubMeas_outcome_le_one
import Theorems.Thm_MIPStarRE_LDT_SubMeas_outcome_le_total
import Theorems.Thm_MIPStarRE_LDT_SubMeas_total_nonneg
import Theorems.Thm_MIPStarRE_LDT_avgOver_mono
import Theorems.Thm_MIPStarRE_LDT_bipartiteConsError_eq_consError_placed
import Theorems.Thm_MIPStarRE_LDT_ev_mono
import Theorems.Thm_MIPStarRE_LDT_ev_sub
import Theorems.Thm_MIPStarRE_LDT_ev_sum
import Theorems.Thm_MIPStarRE_LDT_leftTensor_finset_sum
import Theorems.Thm_MIPStarRE_LDT_leftTensor_le_one
import Theorems.Thm_MIPStarRE_LDT_leftTensor_mul_rightTensor_eq_opTensor
import Theorems.Thm_MIPStarRE_LDT_opTensor_le_leftTensor
import Theorems.Thm_MIPStarRE_LDT_opTensor_mono_left
import Theorems.Thm_MIPStarRE_LDT_rightTensor_finset_sum
import Theorems.Thm_MIPStarRE_Quantum_sq_le_self

set_option backward.isDefEq.respectTransparency false

/-!
# Preliminary comparison theorems: consistency-to-distance estimates

Estimates converting consistency of a submeasurement and a measurement into
state-dependent distance controls for the diagonal and total sandwich families
of `prop:cons-sub-meas`.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT.Preliminaries

open MIPStarRE.LDT

/-! ### Consistency controls for `prop:cons-sub-meas` -/

lemma consSubMeas_controlHelper
    {Outcome : Type*} {κ : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype Outcome]
    (ψ : QuantumState κ)
    (P Q M N : SubMeas Outcome κ)
    (X : Outcome → MIPStarRE.Quantum.Op κ)
    (hSq :
      ∀ a : Outcome,
        ev ψ
            (((M.outcome a - N.outcome a)ᴴ) *
              (M.outcome a - N.outcome a)) =
          ev ψ (X a * X a))
    (hX_nonneg : ∀ a : Outcome, 0 ≤ X a)
    (hX_le_one : ∀ a : Outcome, X a ≤ 1)
    (hSum :
      ∑ a : Outcome, ev ψ (X a) =
        ev ψ (P.total * Q.total) - qMatchMass ψ P Q) :
    qSDD ψ M N ≤ qConsDefect ψ P Q := by
  have hsummand :
      ∀ a : Outcome,
        ev ψ
            (((M.outcome a - N.outcome a)ᴴ) *
              (M.outcome a - N.outcome a)) ≤
          ev ψ (X a) := by
    intro a
    calc
      ev ψ
          (((M.outcome a - N.outcome a)ᴴ) *
            (M.outcome a - N.outcome a))
        = ev ψ (X a * X a) := hSq a
      _ ≤ ev ψ (X a) := by
          exact ev_mono ψ _ _ (MIPStarRE.Quantum.sq_le_self (hX_nonneg a) (hX_le_one a))
  have hnonneg :
      0 ≤ ev ψ (P.total * Q.total) - qMatchMass ψ P Q := by
    calc
      0 ≤ ∑ a : Outcome, ev ψ (X a) := by
          exact Finset.sum_nonneg fun a _ =>
            ev_nonneg_of_psd ψ _ (hX_nonneg a)
      _ = ev ψ (P.total * Q.total) - qMatchMass ψ P Q := hSum
  unfold qSDD qSDDCore qConsDefect
  rw [max_eq_right hnonneg]
  calc
    ∑ a : Outcome,
        ev ψ
          (((M.outcome a - N.outcome a)ᴴ) *
            (M.outcome a - N.outcome a))
      ≤ ∑ a : Outcome, ev ψ (X a) := by
          exact Finset.sum_le_sum fun a _ => hsummand a
    _ = ev ψ (P.total * Q.total) - qMatchMass ψ P Q := hSum

lemma consSubMeas_diagonalControl
    {Question Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState (ι × ι)) (𝒟 : Distribution Question)
    (A : IdxSubMeas Question Outcome ι)
    (B : IdxMeas Question Outcome ι) (γ : Error) :
    ConsRel ψ 𝒟
      A
      (IdxMeas.toIdxSubMeas B) γ →
    SDDRel ψ 𝒟 (IdxSubMeas.liftLeft A)
      (diagonalSandwichFamily A B) γ := by
  intro ⟨hcons⟩
  rw [bipartiteConsError_eq_consError_placed] at hcons
  constructor
  unfold sddError consError at *
  calc
    avgOver 𝒟
        (fun q => qSDD ψ ((IdxSubMeas.liftLeft A) q) ((diagonalSandwichFamily A B) q))
      ≤ avgOver 𝒟
          (fun q =>
            qConsDefect ψ
              ((IdxSubMeas.liftLeft A) q)
              ((IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas B)) q)) := by
          apply avgOver_mono
          intro q
          let X : Outcome → MIPStarRE.Quantum.Op (ι × ι) := fun a =>
            ((IdxSubMeas.liftLeft A) q).outcome a -
              ((diagonalSandwichFamily A B) q).outcome a
          have hX_nonneg : ∀ a : Outcome, 0 ≤ X a := by
            intro a
            dsimp [X]
            simp only [IdxSubMeas.liftLeft, diagonalSandwichFamily,
              LDT.leftTensor_mul_rightTensor_eq_opTensor, sub_nonneg]
            exact MIPStarRE.LDT.opTensor_le_leftTensor
              ((A q).outcome_pos a)
              (Measurement.outcome_le_one (B q) a)
          have hX_le_one : ∀ a : Outcome, X a ≤ 1 := by
            intro a
            have hX_le_left :
                X a ≤ ((IdxSubMeas.liftLeft A) q).outcome a := by
              dsimp [X]
              exact sub_le_self _ ((diagonalSandwichFamily A B q).outcome_pos a)
            exact le_trans hX_le_left <|
              leftTensor_le_one (ι₂ := ι) ((A q).outcome_le_one a)
          refine consSubMeas_controlHelper ψ
            (((IdxSubMeas.liftLeft A) q))
            (((IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas B)) q))
            (((IdxSubMeas.liftLeft A) q))
            (((diagonalSandwichFamily A B) q))
            X
            ?_
            hX_nonneg
            hX_le_one
            ?_
          · intro a
            have hXh : (X a)ᴴ = X a :=
              (Matrix.nonneg_iff_posSemidef.mp (hX_nonneg a)).isHermitian.eq
            simp [X, hXh]
          · have hleft :
                ∑ a : Outcome, ev ψ (leftTensor (ι₂ := ι) ((A q).outcome a)) =
                  ev ψ (leftTensor (ι₂ := ι) ((A q).total)) := by
              rw [← ev_sum ψ (fun a : Outcome => leftTensor (ι₂ := ι) ((A q).outcome a))]
              simp [leftTensor_finset_sum, (A q).sum_eq_total]
            calc
              ∑ a : Outcome, ev ψ (X a)
                = ∑ a : Outcome, ev ψ (leftTensor (ι₂ := ι) ((A q).outcome a)) -
                    ∑ a : Outcome,
                      ev ψ
                        (leftTensor (ι₂ := ι) ((A q).outcome a) *
                          rightTensor (ι₁ := ι) ((B q).outcome a)) := by
                          simp [X, IdxSubMeas.liftLeft,
                            diagonalSandwichFamily, ev_sub]
              _ = ev ψ (leftTensor (ι₂ := ι) ((A q).total)) -
                    qMatchMass ψ
                      (((IdxSubMeas.liftLeft A) q))
                      (((IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas B)) q)) := by
                          unfold qMatchMass
                          simp [hleft, IdxSubMeas.liftLeft, IdxSubMeas.liftRight,
                            IdxMeas.toIdxSubMeas]
              _ =
                  ev ψ
                    ((((IdxSubMeas.liftLeft A) q).total) *
                      (((IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas B)) q).total)) -
                    qMatchMass ψ
                      (((IdxSubMeas.liftLeft A) q))
                      (((IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas B)) q)) := by
                        have htotalOverlap :
                            ev ψ
                                ((((IdxSubMeas.liftLeft A) q).total) *
                                  (((IdxSubMeas.liftRight
                                      (IdxMeas.toIdxSubMeas B)) q).total)) =
                              ev ψ (leftTensor (ι₂ := ι) ((A q).total)) := by
                          rw [show (((IdxSubMeas.liftLeft A) q).total) *
                              (((IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas B)) q).total) =
                                leftTensor (ι₂ := ι) ((A q).total) *
                                  rightTensor (ι₁ := ι) ((B q).total) by rfl]
                          rw [(B q).total_eq_one]
                          simp [leftTensor, rightTensor]
                        rw [htotalOverlap]
    _ ≤ γ := by
      simpa [IdxSubMeas.liftLeft, IdxSubMeas.liftRight, IdxSubMeas.placeLeft,
        IdxSubMeas.placeRight, leftPlacedSubMeas, rightPlacedSubMeas,
        IdxMeas.toIdxSubMeas] using hcons

lemma consSubMeas_sandwichControl
    {Question Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState (ι × ι)) (𝒟 : Distribution Question)
    (A : IdxSubMeas Question Outcome ι)
    (B : IdxMeas Question Outcome ι) (γ : Error) :
    ConsRel ψ 𝒟
      A
      (IdxMeas.toIdxSubMeas B) γ →
    SDDRel ψ 𝒟
      (diagonalSandwichFamily A B)
      (totalSandwichFamily A B) γ := by
  intro ⟨hcons⟩
  rw [bipartiteConsError_eq_consError_placed] at hcons
  constructor
  unfold sddError consError at *
  calc
    avgOver 𝒟
        (fun q => qSDD ψ ((diagonalSandwichFamily A B) q) ((totalSandwichFamily A B) q))
      ≤ avgOver 𝒟
          (fun q =>
            qConsDefect ψ
              ((IdxSubMeas.liftLeft A) q)
              ((IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas B)) q)) := by
          apply avgOver_mono
          intro q
          let X : Outcome → MIPStarRE.Quantum.Op (ι × ι) := fun a =>
            ((totalSandwichFamily A B) q).outcome a -
              ((diagonalSandwichFamily A B) q).outcome a
          have hX_nonneg : ∀ a : Outcome, 0 ≤ X a := by
            intro a
            dsimp [X]
            simp only [totalSandwichFamily, LDT.leftTensor_mul_rightTensor_eq_opTensor,
              diagonalSandwichFamily, sub_nonneg]
            exact MIPStarRE.LDT.opTensor_mono_left
              ((A q).outcome_le_total a)
              ((B q).outcome_pos a)
          have hX_le_one : ∀ a : Outcome, X a ≤ 1 := by
            intro a
            have hX_le_total :
                X a ≤ ((totalSandwichFamily A B) q).outcome a := by
              dsimp [X]
              exact sub_le_self _ ((diagonalSandwichFamily A B q).outcome_pos a)
            have htotal_le :
                ((totalSandwichFamily A B) q).outcome a ≤ 1 := by
              dsimp [totalSandwichFamily]
              have hop :
                  opTensor ((A q).total) ((B q).outcome a) ≤
                    leftTensor (ι₂ := ι) ((A q).total) := by
                exact MIPStarRE.LDT.opTensor_le_leftTensor
                  ((A q).total_nonneg)
                  (Measurement.outcome_le_one (B q) a)
              simpa [MIPStarRE.LDT.leftTensor_mul_rightTensor_eq_opTensor] using
                le_trans hop (leftTensor_le_one (ι₂ := ι) (A q).total_le_one)
            exact le_trans hX_le_total htotal_le
          refine consSubMeas_controlHelper ψ
            (((IdxSubMeas.liftLeft A) q))
            (((IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas B)) q))
            (((diagonalSandwichFamily A B) q))
            (((totalSandwichFamily A B) q))
            X
            ?_
            hX_nonneg
            hX_le_one
            ?_
          · intro a
            have hXh : (X a)ᴴ = X a :=
              (Matrix.nonneg_iff_posSemidef.mp (hX_nonneg a)).isHermitian.eq
            have hneg :
                ((diagonalSandwichFamily A B) q).outcome a -
                    ((totalSandwichFamily A B) q).outcome a =
                  -(X a) := by
              simp [X]
            simp [hneg, hXh]
          · have htotal :
                ∑ a : Outcome,
                    ev ψ
                      (((totalSandwichFamily A B) q).outcome a) =
                  ev ψ (leftTensor (ι₂ := ι) ((A q).total)) := by
              rw [← ev_sum ψ (fun a : Outcome => ((totalSandwichFamily A B) q).outcome a)]
              calc
                ev ψ (∑ a : Outcome, ((totalSandwichFamily A B) q).outcome a)
                  =
                    ev ψ
                      (∑ a : Outcome,
                        leftTensor (ι₂ := ι) ((A q).total) *
                          rightTensor (ι₁ := ι) ((B q).outcome a)) := by
                            simp [totalSandwichFamily]
                _ = ev ψ
                      (leftTensor (ι₂ := ι) ((A q).total) *
                        ∑ a : Outcome, rightTensor (ι₁ := ι) ((B q).outcome a)) := by
                            rw [← Finset.mul_sum]
                _ = ev ψ
                      (leftTensor (ι₂ := ι) ((A q).total) *
                        rightTensor (ι₁ := ι) (∑ a : Outcome, (B q).outcome a)) := by
                            rw [rightTensor_finset_sum (ι₁ := ι) Finset.univ
                              (fun a : Outcome => (B q).outcome a)]
                _ =
                    ev ψ
                      (leftTensor (ι₂ := ι) ((A q).total) *
                        rightTensor (ι₁ := ι) 1) := by
                            rw [(B q).sum_eq]
                _ = ev ψ (leftTensor (ι₂ := ι) ((A q).total)) := by
                            simp [leftTensor, rightTensor]
            calc
              ∑ a : Outcome, ev ψ (X a)
                = ∑ a : Outcome, ev ψ (((totalSandwichFamily A B) q).outcome a) -
                    ∑ a : Outcome, ev ψ (((diagonalSandwichFamily A B) q).outcome a) := by
                        simp [X, ev_sub]
              _ = ev ψ (leftTensor (ι₂ := ι) ((A q).total)) -
                    qMatchMass ψ
                      (((IdxSubMeas.liftLeft A) q))
                      (((IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas B)) q)) := by
                        unfold qMatchMass
                        simp [htotal, diagonalSandwichFamily, IdxSubMeas.liftLeft,
                          IdxSubMeas.liftRight, IdxMeas.toIdxSubMeas]
              _ =
                  ev ψ
                    ((((IdxSubMeas.liftLeft A) q).total) *
                      (((IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas B)) q).total)) -
                    qMatchMass ψ
                      (((IdxSubMeas.liftLeft A) q))
                      (((IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas B)) q)) := by
                        rw [show ((IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas B)) q).total =
                            rightTensor (ι₁ := ι) ((B q).total) by rfl]
                        rw [(B q).total_eq_one]
                        simp [IdxSubMeas.liftLeft, rightTensor, leftTensor]
    _ ≤ γ := by
      simpa [IdxSubMeas.liftLeft, IdxSubMeas.liftRight, IdxSubMeas.placeLeft,
        IdxSubMeas.placeRight, leftPlacedSubMeas, rightPlacedSubMeas,
        IdxMeas.toIdxSubMeas] using hcons

end MIPStarRE.LDT.Preliminaries


