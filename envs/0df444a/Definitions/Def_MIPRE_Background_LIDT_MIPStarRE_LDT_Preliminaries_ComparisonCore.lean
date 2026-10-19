-- Prove2me | Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_ComparisonCore
-- name    : MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_ComparisonCore
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T02:43:47.301986+00:00
-- url     : https://prove2.me/theorems/8a19b224-66e2-4469-9ab4-e673e6bd6d96
-- title:
--   Definitions of ComparisonCore: Preliminary comparison theorems: core layer Core comparison lemmas and measurement-agreement translations for the…
-- statement:
--   The definitions of the module `MIPRE.Background.LIDT.MIPStarRE.LDT.Preliminaries.ComparisonCore` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Preliminary comparison theorems: core layer. Core comparison lemmas and measurement-agreement translations for the preliminaries chapter.
--
--   The module is vendored read-only, with the authors' permission, from [LionSR/MIPStarRE](https://github.com/LionSR/MIPStarRE) (Sirui Lu and the MIPStarRE contributors, Apache 2.0; commit and upstream path in the file header) by `scripts/vendor-lidt.py`.
--
--   **Embedded lemmas** (4): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `ev_leftTensor_mul_rightTensor_nonneg`, `qMatchMass_leftRight_postprocess_ge`, `qConsDefect_leftRight_postprocess_le`, `questionSDD_le_two_questionConsistency`.
--
--   The bundle holds no definition of its own: it carries the lemmas listed above, which later bundles and proofs import.
--
--   **Formalization Note** The bundle is the module `MIPRE.Background.LIDT.MIPStarRE.LDT.Preliminaries.ComparisonCore` (`MIPRE/Background/LIDT/MIPStarRE/LDT/Preliminaries/ComparisonCore.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 21 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/LIDT/MIPStarRE/LDT/Preliminaries/ComparisonCore.lean

/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/Preliminaries/ComparisonCore.lean
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/MIPStarRE/LDT/Preliminaries/ComparisonCore.lean (definition bundle: declarations the uploaded statements rest on);
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
import Theorems.Thm_MIPStarRE_LDT_Measurement_outcome_hermitian
import Theorems.Thm_MIPStarRE_LDT_Measurement_outcome_le_one
import Theorems.Thm_MIPStarRE_LDT_Measurement_sum_eq
import Theorems.Thm_MIPStarRE_LDT_ev_adjoint_self_nonneg
import Theorems.Thm_MIPStarRE_LDT_ev_finset_sum
import Theorems.Thm_MIPStarRE_LDT_ev_mono
import Theorems.Thm_MIPStarRE_LDT_ev_mul_comm_of_psd
import Theorems.Thm_MIPStarRE_LDT_ev_sub
import Theorems.Thm_MIPStarRE_LDT_ev_sum
import Theorems.Thm_MIPStarRE_LDT_leftTensor_finset_sum
import Theorems.Thm_MIPStarRE_LDT_leftTensor_mul_rightTensor_eq_opTensor
import Theorems.Thm_MIPStarRE_LDT_postprocess_total
import Theorems.Thm_MIPStarRE_LDT_qSDD_nonneg
import Theorems.Thm_MIPStarRE_LDT_rightTensor_finset_sum
import Theorems.Thm_MIPStarRE_Quantum_sq_le_self

set_option backward.isDefEq.respectTransparency false

/-!
# Preliminary comparison theorems: core layer

Core comparison lemmas and measurement-agreement translations for the
preliminaries chapter.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT.ConsRel

end MIPStarRE.LDT.ConsRel

namespace MIPStarRE.LDT.Preliminaries

open MIPStarRE.LDT

/-- Atomic mathematical fact: for a full measurement, the squared-distance defect
is at most `2 * qConsDefect`. -/
lemma questionSDD_le_two_questionConsistency {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι) (A B : Measurement Outcome ι) :
    qSDD ψ A.toSubMeas B.toSubMeas ≤
      2 * qConsDefect ψ A.toSubMeas B.toSubMeas := by
  have hA_sq_sum_le : ∑ a, ev ψ (A.outcome a * A.outcome a) ≤ ev ψ 1 := by
    calc
      ∑ a, ev ψ (A.outcome a * A.outcome a)
        ≤ ∑ a, ev ψ (A.outcome a) := by
            exact Finset.sum_le_sum fun a _ =>
              ev_mono ψ _ _ <|
                MIPStarRE.Quantum.sq_le_self
                  (A.outcome_pos a)
                  (Measurement.outcome_le_one A a)
      _ = ev ψ 1 := by
            rw [← ev_sum ψ A.outcome, A.sum_eq]
  have hB_sq_sum_le : ∑ a, ev ψ (B.outcome a * B.outcome a) ≤ ev ψ 1 := by
    calc
      ∑ a, ev ψ (B.outcome a * B.outcome a)
        ≤ ∑ a, ev ψ (B.outcome a) := by
            exact Finset.sum_le_sum fun a _ =>
              ev_mono ψ _ _ <|
                MIPStarRE.Quantum.sq_le_self
                  (B.outcome_pos a)
                  (Measurement.outcome_le_one B a)
      _ = ev ψ 1 := by
            rw [← ev_sum ψ B.outcome, B.sum_eq]
  have h_expand : ∀ a,
      ev ψ ((A.outcome a - B.outcome a)ᴴ * (A.outcome a - B.outcome a)) =
        ev ψ (A.outcome a * A.outcome a) +
          ev ψ (B.outcome a * B.outcome a) -
          2 * ev ψ (A.outcome a * B.outcome a) := by
    intro a
    have hcomm :
        ev ψ (B.outcome a * A.outcome a) =
          ev ψ (A.outcome a * B.outcome a) :=
      ev_mul_comm_of_psd ψ _ _ (B.outcome_pos a) (A.outcome_pos a)
    calc
      ev ψ ((A.outcome a - B.outcome a)ᴴ * (A.outcome a - B.outcome a))
        = ev ψ ((A.outcome a * A.outcome a - A.outcome a * B.outcome a) -
            (B.outcome a * A.outcome a - B.outcome a * B.outcome a)) := by
              congr 1
              simp [sub_mul, mul_sub, Measurement.outcome_hermitian]
              abel
      _ = ev ψ (A.outcome a * A.outcome a) - ev ψ (A.outcome a * B.outcome a) -
            (ev ψ (B.outcome a * A.outcome a) -
              ev ψ (B.outcome a * B.outcome a)) := by
              rw [ev_sub, ev_sub, ev_sub]
      _ = ev ψ (A.outcome a * A.outcome a) +
            ev ψ (B.outcome a * B.outcome a) -
            2 * ev ψ (A.outcome a * B.outcome a) := by
              rw [hcomm]
              ring
  have hbound :
      qSDD ψ A.toSubMeas B.toSubMeas ≤
        2 * (ev ψ (A.total * B.total) -
          qMatchMass ψ A.toSubMeas B.toSubMeas) := by
    unfold qSDD qSDDCore qMatchMass
    calc
      ∑ a, ev ψ ((A.outcome a - B.outcome a)ᴴ * (A.outcome a - B.outcome a))
        = ∑ a, (ev ψ (A.outcome a * A.outcome a) +
            ev ψ (B.outcome a * B.outcome a) -
            2 * ev ψ (A.outcome a * B.outcome a)) := by
              refine Finset.sum_congr rfl ?_
              intro a _
              exact h_expand a
      _ = (∑ a, ev ψ (A.outcome a * A.outcome a)) +
            (∑ a, ev ψ (B.outcome a * B.outcome a)) -
            2 * ∑ a, ev ψ (A.outcome a * B.outcome a) := by
              rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]
      _ ≤ ev ψ 1 + ev ψ 1 - 2 * ∑ a, ev ψ (A.outcome a * B.outcome a) := by
              linarith
      _ = 2 * (ev ψ (A.total * B.total) -
            ∑ a, ev ψ (A.outcome a * B.outcome a)) := by
              simp [A.total_eq_one, B.total_eq_one]
              ring
  have hinner_nonneg :
      0 ≤ ev ψ (A.total * B.total) -
        qMatchMass ψ A.toSubMeas B.toSubMeas := by
    have hnonneg := qSDD_nonneg ψ A.toSubMeas B.toSubMeas
    linarith
  unfold qConsDefect
  rw [max_eq_right hinner_nonneg]
  exact hbound

lemma ev_leftTensor_mul_rightTensor_nonneg
    {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (ψ : QuantumState (ιA × ιB))
    {X : MIPStarRE.Quantum.Op ιA} {Y : MIPStarRE.Quantum.Op ιB}
    (hX : 0 ≤ X) (hY : 0 ≤ Y) :
    0 ≤ ev ψ (leftTensor (ι₂ := ιB) X * rightTensor (ι₁ := ιA) Y) := by
  rw [leftTensor_mul_rightTensor_eq_opTensor]
  first | (assumption) | (apply _root_.MIPStarRE.LDT.ev_nonneg_of_psd; (first | (assumption) | (apply _root_.MIPStarRE.LDT.ev_nonneg_of_psd; (first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith))) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (apply _root_.MIPStarRE.LDT.opTensor_nonneg <;> (first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith))) | (apply _root_.MIPStarRE.LDT.leftTensor_nonneg; (first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith))) | (apply _root_.MIPStarRE.LDT.rightTensor_nonneg; (first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith))) | (apply _root_.IsSelfAdjoint.conjugate_nonneg; focus ((first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith)); done); focus ((first | assumption | exact _root_.MIPStarRE.LDT.SubMeas.outcome_hermitian _ _ | simp [*]); done)) | (apply _root_.Finset.sum_nonneg; intro _ _; (first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith))) | (apply _root_.smul_nonneg <;> (first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith))) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith))) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (apply _root_.MIPStarRE.LDT.opTensor_nonneg <;> (first | (assumption) | (apply _root_.MIPStarRE.LDT.ev_nonneg_of_psd; (first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith))) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (apply _root_.MIPStarRE.LDT.opTensor_nonneg <;> (first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith))) | (apply _root_.MIPStarRE.LDT.leftTensor_nonneg; (first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith))) | (apply _root_.MIPStarRE.LDT.rightTensor_nonneg; (first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith))) | (apply _root_.IsSelfAdjoint.conjugate_nonneg; focus ((first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith)); done); focus ((first | assumption | exact _root_.MIPStarRE.LDT.SubMeas.outcome_hermitian _ _ | simp [*]); done)) | (apply _root_.Finset.sum_nonneg; intro _ _; (first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith))) | (apply _root_.smul_nonneg <;> (first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith))) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith))) | (apply _root_.MIPStarRE.LDT.leftTensor_nonneg; (first | (assumption) | (apply _root_.MIPStarRE.LDT.ev_nonneg_of_psd; (first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith))) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (apply _root_.MIPStarRE.LDT.opTensor_nonneg <;> (first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith))) | (apply _root_.MIPStarRE.LDT.leftTensor_nonneg; (first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith))) | (apply _root_.MIPStarRE.LDT.rightTensor_nonneg; (first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith))) | (apply _root_.IsSelfAdjoint.conjugate_nonneg; focus ((first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith)); done); focus ((first | assumption | exact _root_.MIPStarRE.LDT.SubMeas.outcome_hermitian _ _ | simp [*]); done)) | (apply _root_.Finset.sum_nonneg; intro _ _; (first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith))) | (apply _root_.smul_nonneg <;> (first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith))) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith))) | (apply _root_.MIPStarRE.LDT.rightTensor_nonneg; (first | (assumption) | (apply _root_.MIPStarRE.LDT.ev_nonneg_of_psd; (first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith))) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (apply _root_.MIPStarRE.LDT.opTensor_nonneg <;> (first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith))) | (apply _root_.MIPStarRE.LDT.leftTensor_nonneg; (first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith))) | (apply _root_.MIPStarRE.LDT.rightTensor_nonneg; (first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith))) | (apply _root_.IsSelfAdjoint.conjugate_nonneg; focus ((first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith)); done); focus ((first | assumption | exact _root_.MIPStarRE.LDT.SubMeas.outcome_hermitian _ _ | simp [*]); done)) | (apply _root_.Finset.sum_nonneg; intro _ _; (first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith))) | (apply _root_.smul_nonneg <;> (first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith))) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith))) | (apply _root_.IsSelfAdjoint.conjugate_nonneg; focus ((first | (assumption) | (apply _root_.MIPStarRE.LDT.ev_nonneg_of_psd; (first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith))) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (apply _root_.MIPStarRE.LDT.opTensor_nonneg <;> (first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith))) | (apply _root_.MIPStarRE.LDT.leftTensor_nonneg; (first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith))) | (apply _root_.MIPStarRE.LDT.rightTensor_nonneg; (first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith))) | (apply _root_.IsSelfAdjoint.conjugate_nonneg; focus ((first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith)); done); focus ((first | assumption | exact _root_.MIPStarRE.LDT.SubMeas.outcome_hermitian _ _ | simp [*]); done)) | (apply _root_.Finset.sum_nonneg; intro _ _; (first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith))) | (apply _root_.smul_nonneg <;> (first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith))) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith)); done); focus ((first | assumption | exact _root_.MIPStarRE.LDT.SubMeas.outcome_hermitian _ _ | simp [*]); done)) | (apply _root_.Finset.sum_nonneg; intro _ _; (first | (assumption) | (apply _root_.MIPStarRE.LDT.ev_nonneg_of_psd; (first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith))) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (apply _root_.MIPStarRE.LDT.opTensor_nonneg <;> (first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith))) | (apply _root_.MIPStarRE.LDT.leftTensor_nonneg; (first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith))) | (apply _root_.MIPStarRE.LDT.rightTensor_nonneg; (first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith))) | (apply _root_.IsSelfAdjoint.conjugate_nonneg; focus ((first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith)); done); focus ((first | assumption | exact _root_.MIPStarRE.LDT.SubMeas.outcome_hermitian _ _ | simp [*]); done)) | (apply _root_.Finset.sum_nonneg; intro _ _; (first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith))) | (apply _root_.smul_nonneg <;> (first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith))) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith))) | (apply _root_.smul_nonneg <;> (first | (assumption) | (apply _root_.MIPStarRE.LDT.ev_nonneg_of_psd; (first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith))) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (apply _root_.MIPStarRE.LDT.opTensor_nonneg <;> (first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith))) | (apply _root_.MIPStarRE.LDT.leftTensor_nonneg; (first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith))) | (apply _root_.MIPStarRE.LDT.rightTensor_nonneg; (first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith))) | (apply _root_.IsSelfAdjoint.conjugate_nonneg; focus ((first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith)); done); focus ((first | assumption | exact _root_.MIPStarRE.LDT.SubMeas.outcome_hermitian _ _ | simp [*]); done)) | (apply _root_.Finset.sum_nonneg; intro _ _; (first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith))) | (apply _root_.smul_nonneg <;> (first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith))) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith))) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith)
lemma qMatchMass_leftRight_postprocess_ge {α β : Type*}
    {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype α] [Fintype β]
    (ψ : QuantumState (ιA × ιB)) (A : SubMeas α ιA) (B : SubMeas α ιB)
    (f : α → β) :
    qMatchMass ψ
        (leftPlacedSubMeas (ιB := ιB) (postprocess A f))
        (rightPlacedSubMeas (ιA := ιA) (postprocess B f)) ≥
      qMatchMass ψ
        (leftPlacedSubMeas (ιB := ιB) A)
        (rightPlacedSubMeas (ιA := ιA) B) := by
  classical
  let fiber : β → Finset α := fun b => Finset.univ.filter fun a => f a = b
  let diagTerm : α → Error := fun a =>
    ev ψ
      (leftTensor (ι₂ := ιB) (A.outcome a) *
        rightTensor (ι₁ := ιA) (B.outcome a))
  let pairTerm : α → α → Error := fun a a' =>
    ev ψ
      (leftTensor (ι₂ := ιB) (A.outcome a) *
        rightTensor (ι₁ := ιA) (B.outcome a'))
  let fiberDiag : β → Error := fun b => (fiber b).sum diagTerm
  let fiberPair : β → Error := fun b => (fiber b).sum fun a => (fiber b).sum fun a' => pairTerm a a'
  have hdiag_le (b : β) : fiberDiag b ≤ fiberPair b := by
    dsimp [fiberDiag, fiberPair]
    refine Finset.sum_le_sum ?_
    intro a ha
    exact Finset.single_le_sum
      (fun a' ha' =>
        ev_leftTensor_mul_rightTensor_nonneg ψ (A.outcome_pos a) (B.outcome_pos a'))
      ha
  have hfiber_expand (b : β) :
      ev ψ
        (((fiber b).sum fun a => leftTensor (ι₂ := ιB) (A.outcome a)) *
          ((fiber b).sum fun a => rightTensor (ι₁ := ιA) (B.outcome a))) =
      fiberPair b := by
    dsimp [fiberPair]
    rw [Matrix.sum_mul, ev_finset_sum]
    refine Finset.sum_congr rfl ?_
    intro a ha
    rw [Matrix.mul_sum, ev_finset_sum]
  calc
    qMatchMass ψ
        (leftPlacedSubMeas (ιB := ιB) A)
        (rightPlacedSubMeas (ιA := ιA) B)
      = ∑ b : β, fiberDiag b := by
          dsimp [fiberDiag, diagTerm, fiber]
          unfold qMatchMass leftPlacedSubMeas rightPlacedSubMeas
          symm
          exact Finset.sum_fiberwise Finset.univ f
            (fun a =>
              ev ψ
                (leftTensor (ι₂ := ιB) (A.outcome a) *
                  rightTensor (ι₁ := ιA) (B.outcome a)))
    _ ≤ ∑ b : β, fiberPair b := by
          refine Finset.sum_le_sum ?_
          intro b _
          exact hdiag_le b
    _ = qMatchMass ψ
          (leftPlacedSubMeas (ιB := ιB) (postprocess A f))
          (rightPlacedSubMeas (ιA := ιA) (postprocess B f)) := by
          dsimp [fiberPair, pairTerm, fiber]
          unfold qMatchMass leftPlacedSubMeas rightPlacedSubMeas postprocess
          refine Finset.sum_congr rfl ?_
          intro b _
          symm
          calc
            ev ψ
                (leftTensor (ι₂ := ιB)
                    (∑ a ∈ Finset.univ.filter (fun a => f a = b), A.outcome a) *
                  rightTensor (ι₁ := ιA)
                    (∑ a ∈ Finset.univ.filter (fun a => f a = b), B.outcome a))
              =
                ev ψ
                  (((Finset.univ.filter (fun a => f a = b)).sum fun a =>
                      leftTensor (ι₂ := ιB) (A.outcome a)) *
                    ((Finset.univ.filter (fun a => f a = b)).sum fun a =>
                      rightTensor (ι₁ := ιA) (B.outcome a))) := by
                    rw [← leftTensor_finset_sum (ι₂ := ιB)
                      (Finset.univ.filter (fun a => f a = b)) (fun a => A.outcome a)]
                    rw [← rightTensor_finset_sum (ι₁ := ιA)
                      (Finset.univ.filter (fun a => f a = b)) (fun a => B.outcome a)]
            _ = fiberPair b := hfiber_expand b

lemma qConsDefect_leftRight_postprocess_le {α β : Type*}
    {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype α] [Fintype β]
    (ψ : QuantumState (ιA × ιB)) (A : SubMeas α ιA) (B : SubMeas α ιB)
    (f : α → β) :
    qConsDefect ψ
        (leftPlacedSubMeas (ιB := ιB) (postprocess A f))
        (rightPlacedSubMeas (ιA := ιA) (postprocess B f))
      ≤
    qConsDefect ψ
        (leftPlacedSubMeas (ιB := ιB) A)
        (rightPlacedSubMeas (ιA := ιA) B) := by
  have hmatch :=
    qMatchMass_leftRight_postprocess_ge ψ A B f
  have hsub :
      ev ψ
          ((leftPlacedSubMeas (ιB := ιB) A).total *
            (rightPlacedSubMeas (ιA := ιA) B).total) -
        qMatchMass ψ
          (leftPlacedSubMeas (ιB := ιB) (postprocess A f))
          (rightPlacedSubMeas (ιA := ιA) (postprocess B f))
      ≤
      ev ψ
          ((leftPlacedSubMeas (ιB := ιB) A).total *
            (rightPlacedSubMeas (ιA := ιA) B).total) -
        qMatchMass ψ
          (leftPlacedSubMeas (ιB := ιB) A)
          (rightPlacedSubMeas (ιA := ιA) B) := by
    linarith
  unfold qConsDefect
  have htotal :
      ev ψ
          ((leftPlacedSubMeas (ιB := ιB) (postprocess A f)).total *
            (rightPlacedSubMeas (ιA := ιA) (postprocess B f)).total) =
        ev ψ
          ((leftPlacedSubMeas (ιB := ιB) A).total *
            (rightPlacedSubMeas (ιA := ιA) B).total) := by
    simp [leftPlacedSubMeas, rightPlacedSubMeas, postprocess_total]
  rw [htotal]
  exact max_le_max le_rfl hsub

end MIPStarRE.LDT.Preliminaries


