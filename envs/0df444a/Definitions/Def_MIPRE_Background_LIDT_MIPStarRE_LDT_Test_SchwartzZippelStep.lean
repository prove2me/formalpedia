-- Prove2me | Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Test_SchwartzZippelStep
-- name    : MIPRE_Background_LIDT_MIPStarRE_LDT_Test_SchwartzZippelStep
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T02:43:30.10539+00:00
-- url     : https://prove2.me/theorems/9eea5952-5189-4c1f-aa30-8d88dd1ce598
-- title:
--   Definitions of SchwartzZippelStep: `mainFormal` Step 5 — Schwartz--Zippel self-consistency handoff This file isolates the paper's Step 5 bridge in…
-- statement:
--   The definitions of the module `MIPRE.Background.LIDT.MIPStarRE.LDT.Test.SchwartzZippelStep` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). `mainFormal` Step 5 — Schwartz--Zippel self-consistency handoff. This file isolates the paper's Step 5 bridge in `references/ldt-paper/inductive_step.tex`, lines 119--133. The algebraic expansion/reindexing from evaluated consistency to the full-polynomial consistency defect is proved here, and the genuinely Schwartz--Zippel part is provided by the shared tensor bound `Preliminaries.polynomialCollisionMass_le_mdq`.
--
--   The module is vendored read-only, with the authors' permission, from [LionSR/MIPStarRE](https://github.com/LionSR/MIPStarRE) (Sirui Lu and the MIPStarRE contributors, Apache 2.0; commit and upstream path in the file header) by `scripts/vendor-lidt.py`.
--
--   **Definitions** (2): `MIPStarRE.LDT.Test.MainFormalStep5ExpansionBound` (The exact algebraic expansion/reindexing statement used in `mainFormal` Step 5.); `_private.MIPRE.Background.LIDT.MIPStarRE.LDT.Test.SchwartzZippelStep.0.MIPStarRE.LDT.Test.localCollisionMass`.
--
--   **Embedded lemmas** (4): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `avg_localCollisionMass_eval_eq_polynomialCollisionMass`, `qBipartiteConsDefect_le_postprocess_add_localCollision`, `qBipartiteMatchMass_postprocess_eq_add_localCollision`, `qBipartiteMatchMass_postprocess_eq_pair_sum`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Background.LIDT.MIPStarRE.LDT.Test.SchwartzZippelStep` (`MIPRE/Background/LIDT/MIPStarRE/LDT/Test/SchwartzZippelStep.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 21 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/LIDT/MIPStarRE/LDT/Test/SchwartzZippelStep.lean

/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/Test/SchwartzZippelStep.lean
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/MIPStarRE/LDT/Test/SchwartzZippelStep.lean (definition bundle: declarations the uploaded statements rest on);
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
import Mathlib.Algebra.Polynomial.Roots
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
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Nat.Cast.Order.Ring
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
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_Polynomials
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_PolynomialAgreement
import Theorems.Thm_MIPStarRE_LDT_avgOver_congr
import Theorems.Thm_MIPStarRE_LDT_avgOver_mul_const
import Theorems.Thm_MIPStarRE_LDT_avgOver_sum
import Theorems.Thm_MIPStarRE_LDT_avgOver_zero
import Theorems.Thm_MIPStarRE_LDT_ev_sum
import Theorems.Thm_MIPStarRE_LDT_ev_zero
import Theorems.Thm_MIPStarRE_LDT_opTensor_sum_left_univ
import Theorems.Thm_MIPStarRE_LDT_opTensor_sum_right_univ
import Theorems.Thm_MIPStarRE_LDT_postprocess_total

set_option backward.isDefEq.respectTransparency false

/-!
# `mainFormal` Step 5 — Schwartz--Zippel self-consistency handoff

This file isolates the paper's Step 5 bridge in
`references/ldt-paper/inductive_step.tex`, lines 119--133.  The algebraic
expansion/reindexing from evaluated consistency to the full-polynomial
consistency defect is proved here, and the genuinely Schwartz--Zippel part is
provided by the shared tensor bound
`Preliminaries.polynomialCollisionMass_le_mdq`.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT

namespace Test

open Classical in
lemma qBipartiteMatchMass_postprocess_eq_pair_sum
    {α β ιA ιB : Type*} [Fintype α] [Fintype β]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (ψ : QuantumState (ιA × ιB)) (A : SubMeas α ιA) (B : SubMeas α ιB)
    (f : α → β) :
    qBipartiteMatchMass ψ (postprocess A f) (postprocess B f) =
      ∑ aa : α × α,
        if f aa.1 = f aa.2 then
          ev ψ (opTensor (A.outcome aa.1) (B.outcome aa.2))
        else 0 := by
  classical
  unfold qBipartiteMatchMass
  calc
    ∑ b : β, ev ψ (opTensor ((postprocess A f).outcome b) ((postprocess B f).outcome b))
      = ∑ b : β, ∑ aa : α × α,
          if f aa.1 = b ∧ f aa.2 = b then
            ev ψ (opTensor (A.outcome aa.1) (B.outcome aa.2))
          else 0 := by
            refine Finset.sum_congr rfl ?_
            intro b _
            simp only [postprocess, Finset.sum_filter, opTensor_sum_left_univ,
              opTensor_sum_right_univ, ev_sum]
            rw [Fintype.sum_prod_type]
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl ?_
            intro a _
            refine Finset.sum_congr rfl ?_
            intro x _
            by_cases ha : f a = b <;> by_cases hx : f x = b <;>
              simp [ha, hx, opTensor, ev_zero]
    _ = ∑ aa : α × α, ∑ b : β,
          if f aa.1 = b ∧ f aa.2 = b then
            ev ψ (opTensor (A.outcome aa.1) (B.outcome aa.2))
          else 0 := by
            rw [Finset.sum_comm]
    _ = ∑ aa : α × α,
        if f aa.1 = f aa.2 then
          ev ψ (opTensor (A.outcome aa.1) (B.outcome aa.2))
        else 0 := by
            refine Finset.sum_congr rfl ?_
            intro aa _
            by_cases h : f aa.1 = f aa.2
            · rw [Finset.sum_eq_single (f aa.1)]
              · simp [h]
              · intro b _ hb
                have hb1 : f aa.1 ≠ b := by
                  intro hEq
                  exact hb hEq.symm
                by_cases h1 : f aa.1 = b
                · exact (hb1 h1).elim
                · simp [h1]
              · simp
            · have hzero : (∑ b : β,
                  if f aa.1 = b ∧ f aa.2 = b then
                    ev ψ (opTensor (A.outcome aa.1) (B.outcome aa.2)) else 0) = 0 := by
                refine Finset.sum_eq_zero ?_
                intro b _
                by_cases h1 : f aa.1 = b
                · have h2 : f aa.2 ≠ b := by
                    intro h2
                    exact h (h1.trans h2.symm)
                  simp [h1, h2]
                · simp [h1]
              simp [h, hzero]

open Classical in
noncomputable def localCollisionMass
    {α β ιA ιB : Type*} [Fintype α]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (ψ : QuantumState (ιA × ιB)) (A : SubMeas α ιA) (B : SubMeas α ιB)
    (f : α → β) : Error :=
  ∑ aa : α × α,
    (if aa.1 = aa.2 then 0 else if f aa.1 = f aa.2 then (1 : Error) else 0) *
      ev ψ (opTensor (A.outcome aa.1) (B.outcome aa.2))

lemma qBipartiteMatchMass_postprocess_eq_add_localCollision
    {α β ιA ιB : Type*} [Fintype α] [Fintype β]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (ψ : QuantumState (ιA × ιB)) (A : SubMeas α ιA) (B : SubMeas α ιB)
    (f : α → β) :
    qBipartiteMatchMass ψ (postprocess A f) (postprocess B f) =
      qBipartiteMatchMass ψ A B + localCollisionMass ψ A B f := by
  classical
  have hdiag :
      qBipartiteMatchMass ψ A B =
        ∑ aa : α × α,
          if aa.1 = aa.2 then
            ev ψ (opTensor (A.outcome aa.1) (B.outcome aa.2))
          else 0 := by
    unfold qBipartiteMatchMass
    symm
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl ?_
    intro a _
    rw [Finset.sum_eq_single a]
    · simp
    · intro b _ hb
      have hb' : ¬ a = b := by
        intro hEq
        exact hb hEq.symm
      simp [hb']
    · simp
  rw [qBipartiteMatchMass_postprocess_eq_pair_sum]
  rw [hdiag]
  unfold localCollisionMass
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro aa _
  by_cases hEq : aa.1 = aa.2
  · simp [hEq]
  · by_cases hf : f aa.1 = f aa.2 <;> simp [hEq, hf]

lemma qBipartiteConsDefect_le_postprocess_add_localCollision
    {α β ιA ιB : Type*} [Fintype α] [Fintype β]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (ψ : QuantumState (ιA × ιB)) (A : SubMeas α ιA) (B : SubMeas α ιB)
    (f : α → β) :
    qBipartiteConsDefect ψ A B ≤
      qBipartiteConsDefect ψ (postprocess A f) (postprocess B f) +
        localCollisionMass ψ A B f := by
  classical
  let c := localCollisionMass ψ A B f
  have hc : 0 ≤ c := by
    dsimp [c, localCollisionMass]
    refine Finset.sum_nonneg ?_
    intro aa _
    apply mul_nonneg
    · by_cases hEq : aa.1 = aa.2
      · simp [hEq]
      · by_cases hf : f aa.1 = f aa.2
        · simp [hEq, hf]
        · simp [hEq, hf]
    · exact ev_nonneg_of_psd ψ _
        (opTensor_nonneg (A.outcome_pos aa.1) (B.outcome_pos aa.2))
  have hmatch := qBipartiteMatchMass_postprocess_eq_add_localCollision ψ A B f
  unfold qBipartiteConsDefect
  simp only [postprocess_total]
  rw [hmatch]
  change max 0 (ev ψ (opTensor A.total B.total) - qBipartiteMatchMass ψ A B) ≤
    max 0 (ev ψ (opTensor A.total B.total) -
      (qBipartiteMatchMass ψ A B + c)) + c
  apply max_le
  · exact add_nonneg (le_max_left 0 _) hc
  · have hle :
        ev ψ (opTensor A.total B.total) - qBipartiteMatchMass ψ A B - c ≤
          max 0 (ev ψ (opTensor A.total B.total) -
            (qBipartiteMatchMass ψ A B + c)) := by
      have hrewrite :
          ev ψ (opTensor A.total B.total) - qBipartiteMatchMass ψ A B - c =
            ev ψ (opTensor A.total B.total) - (qBipartiteMatchMass ψ A B + c) := by
        rw [sub_add_eq_sub_sub]
      rw [hrewrite]
      exact le_max_right 0 _
    linarith

lemma avg_localCollisionMass_eval_eq_polynomialCollisionMass
    {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (params : Parameters) [FieldModel params.q]
    (ψ : QuantumState (ιA × ιB))
    (Left : SubMeas (Polynomial params) ιA) (Right : SubMeas (Polynomial params) ιB) :
    avgOver (uniformDistribution (Point params))
      (fun u => localCollisionMass ψ Left Right (fun g : Polynomial params => g u)) =
      Preliminaries.polynomialCollisionMass params ψ Left Right := by
  classical
  unfold localCollisionMass Preliminaries.polynomialCollisionMass
  rw [avgOver_sum]
  refine Finset.sum_congr rfl ?_
  intro gg _
  by_cases hEq : gg.1 = gg.2
  · simp [hEq, avgOver_zero]
  · simp only [hEq, if_false]
    rw [avgOver_mul_const]
    congr 1
    apply avgOver_congr
    intro u
    by_cases h : gg.1 u = gg.2 u <;> simp [h]

/-- The exact algebraic expansion/reindexing statement used in `mainFormal` Step 5.

Paper origin: `references/ldt-paper/inductive_step.tex:119-130`
(`\label{eq:G-self-consistency}`), with the collision estimate supplied by the
Schwartz--Zippel lemma.

Paper lines 119--128 compare the evaluated consistency defect

`E_u ∑_{a ≠ b} ⟨ψ| G^A_[g(u)=a] ⊗ G^B_[h(u)=b] |ψ⟩`

with the full-polynomial consistency defect

`∑_{g ≠ h} ⟨ψ| G^A_g ⊗ G^B_h |ψ⟩`.

The paper reuses `g` as the bound name in the Alice and Bob sums; Lean writes
these independently-bound polynomial outcomes as `g` and `h` to make the
independence explicit.

After expanding the postprocessed outcomes and separating the colliding pairs
`g(u)=h(u)`, the only extra term is the collision mass bounded by
Schwartz--Zippel in `Preliminaries.polynomialCollisionMass_le_mdq`.  This
predicate records precisely that expansion step, without bundling the
Schwartz--Zippel estimate itself into an unproved hypothesis. -/
def MainFormalStep5ExpansionBound
    {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (params : Parameters) [FieldModel params.q]
    (ψ : QuantumState (ιA × ιB))
    (Left : SubMeas (Polynomial params) ιA) (Right : SubMeas (Polynomial params) ιB) :
    Prop :=
  bipartiteConsError ψ (uniformDistribution Unit)
      (constSubMeasFamily Left) (constSubMeasFamily Right) ≤
    bipartiteConsError ψ (uniformDistribution (Point params))
      (polynomialEvaluationFamily params Left)
      (polynomialEvaluationFamily params Right) +
    Preliminaries.polynomialCollisionMass params ψ Left Right

end Test

end MIPStarRE.LDT


