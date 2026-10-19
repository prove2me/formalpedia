-- Prove2me | Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_Defs
-- name    : MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_Defs
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T02:20:13.602161+00:00
-- url     : https://prove2.me/theorems/291b0aa2-c0ab-4de5-9456-7e0b37bf54ec
-- title:
--   Definitions of Defs: Preliminary definitions and statement structures This file collects the lightweight statement and definition layer for…
-- statement:
--   The definitions of the module `MIPRE.Background.LIDT.MIPStarRE.LDT.Preliminaries.Defs` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Preliminary definitions and statement structures. This file collects the lightweight statement and definition layer for the preliminaries chapter of the LDT development. It records the paper's consistency, sandwich, and completion statements in a form used by later files.
--
--   The module is vendored read-only, with the authors' permission, from [LionSR/MIPStarRE](https://github.com/LionSR/MIPStarRE) (Sirui Lu and the MIPStarRE contributors, Apache 2.0; commit and upstream path in the file header) by `scripts/vendor-lidt.py`.
--
--   **Definitions** (11): `MIPStarRE.LDT.Preliminaries.BipartiteSDDRel` (Source-style left/right relation `A^x_a ⊗ I ≈_δ I ⊗ B^x_a`.); `MIPStarRE.LDT.Preliminaries.CompTransferStmt` (Conclusion statement for `prop:completeness-transfer-projective-P`.); `MIPStarRE.LDT.Preliminaries.ConsSubMeasStmt` (Same-space output statement for `prop:cons-sub-meas`.); `MIPStarRE.LDT.Preliminaries.OpBounded01` (Condition `0 ≤ B ≤ I` for the switch-sandwich argument.); `MIPStarRE.LDT.Preliminaries.SwitchSandwichStmt` (Conclusion statement for `prop:switch-sandwich`.); `MIPStarRE.LDT.Preliminaries.completeAtOutcome` (Canonical completion of `B` by adjoining the residual `I - Σ_a B_a` to the distinguished outcome `a0`.); `MIPStarRE.LDT.Preliminaries.diagonalSandwichFamily` (`A_a ⊗ B_a`, the diagonal bipartite family from `prop:cons-sub-meas`.); `MIPStarRE.LDT.Preliminaries.leftSandwichExpectation` (Averaged left term `E_x ∑_a ⟨ψ, (A_a B A_a ⊗ I) ψ⟩`.); `MIPStarRE.LDT.Preliminaries.middleSandwichExpectation` (Averaged middle term `E_x ∑_a ⟨ψ, (B ⊗ A_a) ψ⟩`.); `MIPStarRE.LDT.Preliminaries.rightSandwichExpectation` (Averaged right term `E_x ∑_a ⟨ψ, (B A_a ⊗ I) ψ⟩`.); `MIPStarRE.LDT.Preliminaries.totalSandwichFamily` (`A ⊗ B_a`, the total bipartite family from `prop:cons-sub-meas`.).
--
--   **Embedded lemmas** (3): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `completeAtOutcome_sum_eq_one`, `diagonalSandwichFamily_total_le_one`, `totalSandwichFamily_total_le_one`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Background.LIDT.MIPStarRE.LDT.Preliminaries.Defs` (`MIPRE/Background/LIDT/MIPStarRE/LDT/Preliminaries/Defs.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 19 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/LIDT/MIPStarRE/LDT/Preliminaries/Defs.lean

/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/Preliminaries/Defs.lean
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/MIPStarRE/LDT/Preliminaries/Defs.lean (definition bundle: declarations the uploaded statements rest on);
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
import Theorems.Thm_MIPStarRE_LDT_Measurement_outcome_le_one
import Theorems.Thm_MIPStarRE_LDT_Measurement_sum_eq
import Theorems.Thm_MIPStarRE_LDT_SubMeas_total_nonneg
import Theorems.Thm_MIPStarRE_LDT_ev_adjoint_self_nonneg
import Theorems.Thm_MIPStarRE_LDT_leftTensor_finset_sum
import Theorems.Thm_MIPStarRE_LDT_leftTensor_le_one
import Theorems.Thm_MIPStarRE_LDT_leftTensor_mul_rightTensor_eq_opTensor
import Theorems.Thm_MIPStarRE_LDT_leftTensor_nonneg
import Theorems.Thm_MIPStarRE_LDT_opTensor_le_leftTensor
import Theorems.Thm_MIPStarRE_LDT_rightTensor_finset_sum
import Theorems.Thm_MIPStarRE_LDT_rightTensor_nonneg

set_option backward.isDefEq.respectTransparency false

/-!
# Preliminary definitions and statement structures

This file collects the lightweight statement and definition layer for the
preliminaries chapter of the LDT development. It records the paper's
consistency, sandwich, and completion statements in a form used by later files.

## Main definitions

- `BipartiteSDDRel`: the paper-style left/right state-dependent distance
  relation.
- `ConsAgreement`: the measurement reformulation of consistency.
- `ConsSubMeasStmt`, `SwitchSandwichStmt`, `CompTransferStmt`, and
  `CompletingToMeasStmt`: conclusion statements for the main preliminary
  propositions.
- `completeAtOutcome`: completion of a submeasurement at a distinguished
  outcome.

## References

- `references/ldt-paper/preliminaries.tex`
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT.Preliminaries

open MIPStarRE.LDT
open MIPStarRE.Quantum

/-! ## Consistency and distance statements -/

/-- Source-style left/right relation `A^x_a ⊗ I ≈_δ I ⊗ B^x_a`. -/
structure BipartiteSDDRel {Question Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState (ι × ι)) (𝒟 : Distribution Question)
    (A B : IdxSubMeas Question Outcome ι) (δ : Error) : Prop where
  leftRightSquaredDistanceBound :
    sddError ψ 𝒟 (IdxSubMeas.liftLeft A) (IdxSubMeas.liftRight B) ≤ δ

/-- Condition `0 ≤ B ≤ I` for the switch-sandwich argument. -/
structure OpBounded01 {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : MIPStarRE.Quantum.Op ι) : Prop where
  nonnegative : 0 ≤ B
  boundedByIdentity : 0 ≤ (1 : MIPStarRE.Quantum.Op ι) - B

/-- A diagonal sandwich family has total operator at most the identity. -/
theorem diagonalSandwichFamily_total_le_one {Question Outcome : Type*}
    {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype Outcome] (A : IdxSubMeas Question Outcome ιA)
    (B : IdxMeas Question Outcome ιB) (q : Question) :
    (∑ a : Outcome,
      leftTensor (ι₂ := ιB) ((A q).outcome a) *
        rightTensor (ι₁ := ιA) ((B q).outcome a)) ≤ 1 := by
  calc
    ∑ a : Outcome,
        leftTensor (ι₂ := ιB) ((A q).outcome a) *
          rightTensor (ι₁ := ιA) ((B q).outcome a)
      ≤ ∑ a : Outcome, leftTensor (ι₂ := ιB) ((A q).outcome a) := by
          refine Finset.sum_le_sum ?_
          intro a _ha
          rw [leftTensor_mul_rightTensor_eq_opTensor]
          exact opTensor_le_leftTensor
            ((A q).outcome_pos a) (Measurement.outcome_le_one (B q) a)
    _ = leftTensor (ι₂ := ιB) ((A q).total) := by
      rw [leftTensor_finset_sum (ι₂ := ιB) Finset.univ (fun a => (A q).outcome a)]
      rw [(A q).sum_eq_total]
    _ ≤ 1 := leftTensor_le_one (ι₂ := ιB) (A q).total_le_one

/-- A total sandwich family has total operator at most the identity. -/
theorem totalSandwichFamily_total_le_one {Question Outcome : Type*}
    {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype Outcome] (A : IdxSubMeas Question Outcome ιA)
    (B : IdxMeas Question Outcome ιB) (q : Question) :
    (∑ a : Outcome,
      leftTensor (ι₂ := ιB) ((A q).total) *
        rightTensor (ι₁ := ιA) ((B q).outcome a)) ≤ 1 := by
  calc
    ∑ a : Outcome,
        leftTensor (ι₂ := ιB) ((A q).total) *
          rightTensor (ι₁ := ιA) ((B q).outcome a)
      = leftTensor (ι₂ := ιB) ((A q).total) := by
          rw [← Finset.mul_sum]
          rw [rightTensor_finset_sum (ι₁ := ιA) Finset.univ (fun a => (B q).outcome a)]
          rw [(B q).sum_eq]
          simp [leftTensor, rightTensor]
    _ ≤ 1 := leftTensor_le_one (ι₂ := ιB) (A q).total_le_one

/-- `A_a ⊗ B_a`, the diagonal bipartite family from `prop:cons-sub-meas`.

This same-space version is the specialization used by the existing
main-theorem path.  The paper-facing two-space version is
`heterogeneousDiagonalSandwichFamily`. -/
noncomputable def diagonalSandwichFamily {Question Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (A : IdxSubMeas Question Outcome ι)
    (B : IdxMeas Question Outcome ι) :
    IdxSubMeas Question Outcome (ι × ι) :=
  fun q => {
    outcome := fun a =>
      leftTensor (ι₂ := ι) ((A q).outcome a) *
        rightTensor (ι₁ := ι) ((B q).outcome a)
    total := ∑ a : Outcome,
      leftTensor (ι₂ := ι) ((A q).outcome a) *
        rightTensor (ι₁ := ι) ((B q).outcome a)
    outcome_pos := fun a => by
      rw [leftTensor_mul_rightTensor_eq_opTensor]
      first | (assumption) | (apply _root_.MIPStarRE.LDT.ev_nonneg_of_psd; (first | (assumption) | (apply _root_.MIPStarRE.LDT.ev_nonneg_of_psd; (first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith))) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (apply _root_.MIPStarRE.LDT.opTensor_nonneg <;> (first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith))) | (apply _root_.MIPStarRE.LDT.leftTensor_nonneg; (first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith))) | (apply _root_.MIPStarRE.LDT.rightTensor_nonneg; (first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith))) | (apply _root_.IsSelfAdjoint.conjugate_nonneg; focus ((first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith)); done); focus ((first | assumption | exact _root_.MIPStarRE.LDT.SubMeas.outcome_hermitian _ _ | simp [*]); done)) | (apply _root_.Finset.sum_nonneg; intro _ _; (first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith))) | (apply _root_.smul_nonneg <;> (first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith))) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith))) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (apply _root_.MIPStarRE.LDT.opTensor_nonneg <;> (first | (assumption) | (apply _root_.MIPStarRE.LDT.ev_nonneg_of_psd; (first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith))) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (apply _root_.MIPStarRE.LDT.opTensor_nonneg <;> (first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith))) | (apply _root_.MIPStarRE.LDT.leftTensor_nonneg; (first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith))) | (apply _root_.MIPStarRE.LDT.rightTensor_nonneg; (first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith))) | (apply _root_.IsSelfAdjoint.conjugate_nonneg; focus ((first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith)); done); focus ((first | assumption | exact _root_.MIPStarRE.LDT.SubMeas.outcome_hermitian _ _ | simp [*]); done)) | (apply _root_.Finset.sum_nonneg; intro _ _; (first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith))) | (apply _root_.smul_nonneg <;> (first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith))) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith))) | (apply _root_.MIPStarRE.LDT.leftTensor_nonneg; (first | (assumption) | (apply _root_.MIPStarRE.LDT.ev_nonneg_of_psd; (first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith))) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (apply _root_.MIPStarRE.LDT.opTensor_nonneg <;> (first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith))) | (apply _root_.MIPStarRE.LDT.leftTensor_nonneg; (first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith))) | (apply _root_.MIPStarRE.LDT.rightTensor_nonneg; (first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith))) | (apply _root_.IsSelfAdjoint.conjugate_nonneg; focus ((first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith)); done); focus ((first | assumption | exact _root_.MIPStarRE.LDT.SubMeas.outcome_hermitian _ _ | simp [*]); done)) | (apply _root_.Finset.sum_nonneg; intro _ _; (first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith))) | (apply _root_.smul_nonneg <;> (first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith))) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith))) | (apply _root_.MIPStarRE.LDT.rightTensor_nonneg; (first | (assumption) | (apply _root_.MIPStarRE.LDT.ev_nonneg_of_psd; (first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith))) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (apply _root_.MIPStarRE.LDT.opTensor_nonneg <;> (first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith))) | (apply _root_.MIPStarRE.LDT.leftTensor_nonneg; (first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith))) | (apply _root_.MIPStarRE.LDT.rightTensor_nonneg; (first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith))) | (apply _root_.IsSelfAdjoint.conjugate_nonneg; focus ((first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith)); done); focus ((first | assumption | exact _root_.MIPStarRE.LDT.SubMeas.outcome_hermitian _ _ | simp [*]); done)) | (apply _root_.Finset.sum_nonneg; intro _ _; (first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith))) | (apply _root_.smul_nonneg <;> (first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith))) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith))) | (apply _root_.IsSelfAdjoint.conjugate_nonneg; focus ((first | (assumption) | (apply _root_.MIPStarRE.LDT.ev_nonneg_of_psd; (first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith))) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (apply _root_.MIPStarRE.LDT.opTensor_nonneg <;> (first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith))) | (apply _root_.MIPStarRE.LDT.leftTensor_nonneg; (first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith))) | (apply _root_.MIPStarRE.LDT.rightTensor_nonneg; (first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith))) | (apply _root_.IsSelfAdjoint.conjugate_nonneg; focus ((first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith)); done); focus ((first | assumption | exact _root_.MIPStarRE.LDT.SubMeas.outcome_hermitian _ _ | simp [*]); done)) | (apply _root_.Finset.sum_nonneg; intro _ _; (first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith))) | (apply _root_.smul_nonneg <;> (first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith))) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith)); done); focus ((first | assumption | exact _root_.MIPStarRE.LDT.SubMeas.outcome_hermitian _ _ | simp [*]); done)) | (apply _root_.Finset.sum_nonneg; intro _ _; (first | (assumption) | (apply _root_.MIPStarRE.LDT.ev_nonneg_of_psd; (first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith))) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (apply _root_.MIPStarRE.LDT.opTensor_nonneg <;> (first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith))) | (apply _root_.MIPStarRE.LDT.leftTensor_nonneg; (first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith))) | (apply _root_.MIPStarRE.LDT.rightTensor_nonneg; (first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith))) | (apply _root_.IsSelfAdjoint.conjugate_nonneg; focus ((first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith)); done); focus ((first | assumption | exact _root_.MIPStarRE.LDT.SubMeas.outcome_hermitian _ _ | simp [*]); done)) | (apply _root_.Finset.sum_nonneg; intro _ _; (first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith))) | (apply _root_.smul_nonneg <;> (first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith))) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith))) | (apply _root_.smul_nonneg <;> (first | (assumption) | (apply _root_.MIPStarRE.LDT.ev_nonneg_of_psd; (first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith))) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (apply _root_.MIPStarRE.LDT.opTensor_nonneg <;> (first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith))) | (apply _root_.MIPStarRE.LDT.leftTensor_nonneg; (first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith))) | (apply _root_.MIPStarRE.LDT.rightTensor_nonneg; (first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith))) | (apply _root_.IsSelfAdjoint.conjugate_nonneg; focus ((first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith)); done); focus ((first | assumption | exact _root_.MIPStarRE.LDT.SubMeas.outcome_hermitian _ _ | simp [*]); done)) | (apply _root_.Finset.sum_nonneg; intro _ _; (first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith))) | (apply _root_.smul_nonneg <;> (first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith))) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith))) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith)
    sum_eq_total := rfl
    total_le_one := diagonalSandwichFamily_total_le_one A B q
  }

/-- `A ⊗ B_a`, the total bipartite family from `prop:cons-sub-meas`.

This same-space version is the specialization used by the existing
main-theorem path.  The paper-facing two-space version is
`heterogeneousTotalSandwichFamily`. -/
noncomputable def totalSandwichFamily {Question Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (A : IdxSubMeas Question Outcome ι)
    (B : IdxMeas Question Outcome ι) :
    IdxSubMeas Question Outcome (ι × ι) :=
  fun q => {
    outcome := fun a =>
      leftTensor (ι₂ := ι) ((A q).total) *
        rightTensor (ι₁ := ι) ((B q).outcome a)
    total := ∑ a : Outcome,
      leftTensor (ι₂ := ι) ((A q).total) *
        rightTensor (ι₁ := ι) ((B q).outcome a)
    outcome_pos := fun a => by
      rw [leftTensor_mul_rightTensor_eq_opTensor]
      first | (assumption) | (apply _root_.MIPStarRE.LDT.ev_nonneg_of_psd; (first | (assumption) | (apply _root_.MIPStarRE.LDT.ev_nonneg_of_psd; (first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith))) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (apply _root_.MIPStarRE.LDT.opTensor_nonneg <;> (first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith))) | (apply _root_.MIPStarRE.LDT.leftTensor_nonneg; (first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith))) | (apply _root_.MIPStarRE.LDT.rightTensor_nonneg; (first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith))) | (apply _root_.IsSelfAdjoint.conjugate_nonneg; focus ((first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith)); done); focus ((first | assumption | exact _root_.MIPStarRE.LDT.SubMeas.outcome_hermitian _ _ | simp [*]); done)) | (apply _root_.Finset.sum_nonneg; intro _ _; (first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith))) | (apply _root_.smul_nonneg <;> (first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith))) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith))) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (apply _root_.MIPStarRE.LDT.opTensor_nonneg <;> (first | (assumption) | (apply _root_.MIPStarRE.LDT.ev_nonneg_of_psd; (first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith))) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (apply _root_.MIPStarRE.LDT.opTensor_nonneg <;> (first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith))) | (apply _root_.MIPStarRE.LDT.leftTensor_nonneg; (first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith))) | (apply _root_.MIPStarRE.LDT.rightTensor_nonneg; (first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith))) | (apply _root_.IsSelfAdjoint.conjugate_nonneg; focus ((first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith)); done); focus ((first | assumption | exact _root_.MIPStarRE.LDT.SubMeas.outcome_hermitian _ _ | simp [*]); done)) | (apply _root_.Finset.sum_nonneg; intro _ _; (first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith))) | (apply _root_.smul_nonneg <;> (first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith))) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith))) | (apply _root_.MIPStarRE.LDT.leftTensor_nonneg; (first | (assumption) | (apply _root_.MIPStarRE.LDT.ev_nonneg_of_psd; (first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith))) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (apply _root_.MIPStarRE.LDT.opTensor_nonneg <;> (first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith))) | (apply _root_.MIPStarRE.LDT.leftTensor_nonneg; (first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith))) | (apply _root_.MIPStarRE.LDT.rightTensor_nonneg; (first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith))) | (apply _root_.IsSelfAdjoint.conjugate_nonneg; focus ((first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith)); done); focus ((first | assumption | exact _root_.MIPStarRE.LDT.SubMeas.outcome_hermitian _ _ | simp [*]); done)) | (apply _root_.Finset.sum_nonneg; intro _ _; (first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith))) | (apply _root_.smul_nonneg <;> (first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith))) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith))) | (apply _root_.MIPStarRE.LDT.rightTensor_nonneg; (first | (assumption) | (apply _root_.MIPStarRE.LDT.ev_nonneg_of_psd; (first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith))) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (apply _root_.MIPStarRE.LDT.opTensor_nonneg <;> (first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith))) | (apply _root_.MIPStarRE.LDT.leftTensor_nonneg; (first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith))) | (apply _root_.MIPStarRE.LDT.rightTensor_nonneg; (first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith))) | (apply _root_.IsSelfAdjoint.conjugate_nonneg; focus ((first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith)); done); focus ((first | assumption | exact _root_.MIPStarRE.LDT.SubMeas.outcome_hermitian _ _ | simp [*]); done)) | (apply _root_.Finset.sum_nonneg; intro _ _; (first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith))) | (apply _root_.smul_nonneg <;> (first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith))) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith))) | (apply _root_.IsSelfAdjoint.conjugate_nonneg; focus ((first | (assumption) | (apply _root_.MIPStarRE.LDT.ev_nonneg_of_psd; (first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith))) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (apply _root_.MIPStarRE.LDT.opTensor_nonneg <;> (first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith))) | (apply _root_.MIPStarRE.LDT.leftTensor_nonneg; (first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith))) | (apply _root_.MIPStarRE.LDT.rightTensor_nonneg; (first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith))) | (apply _root_.IsSelfAdjoint.conjugate_nonneg; focus ((first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith)); done); focus ((first | assumption | exact _root_.MIPStarRE.LDT.SubMeas.outcome_hermitian _ _ | simp [*]); done)) | (apply _root_.Finset.sum_nonneg; intro _ _; (first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith))) | (apply _root_.smul_nonneg <;> (first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith))) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith)); done); focus ((first | assumption | exact _root_.MIPStarRE.LDT.SubMeas.outcome_hermitian _ _ | simp [*]); done)) | (apply _root_.Finset.sum_nonneg; intro _ _; (first | (assumption) | (apply _root_.MIPStarRE.LDT.ev_nonneg_of_psd; (first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith))) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (apply _root_.MIPStarRE.LDT.opTensor_nonneg <;> (first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith))) | (apply _root_.MIPStarRE.LDT.leftTensor_nonneg; (first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith))) | (apply _root_.MIPStarRE.LDT.rightTensor_nonneg; (first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith))) | (apply _root_.IsSelfAdjoint.conjugate_nonneg; focus ((first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith)); done); focus ((first | assumption | exact _root_.MIPStarRE.LDT.SubMeas.outcome_hermitian _ _ | simp [*]); done)) | (apply _root_.Finset.sum_nonneg; intro _ _; (first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith))) | (apply _root_.smul_nonneg <;> (first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith))) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith))) | (apply _root_.smul_nonneg <;> (first | (assumption) | (apply _root_.MIPStarRE.LDT.ev_nonneg_of_psd; (first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith))) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (apply _root_.MIPStarRE.LDT.opTensor_nonneg <;> (first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith))) | (apply _root_.MIPStarRE.LDT.leftTensor_nonneg; (first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith))) | (apply _root_.MIPStarRE.LDT.rightTensor_nonneg; (first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith))) | (apply _root_.IsSelfAdjoint.conjugate_nonneg; focus ((first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith)); done); focus ((first | assumption | exact _root_.MIPStarRE.LDT.SubMeas.outcome_hermitian _ _ | simp [*]); done)) | (apply _root_.Finset.sum_nonneg; intro _ _; (first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith))) | (apply _root_.smul_nonneg <;> (first | (assumption) | (exact _root_.MIPStarRE.LDT.ev_adjoint_self_nonneg _ _) | (exact _root_.star_mul_self_nonneg _) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith))) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith))) | (exact _root_.zero_le_one) | (exact _root_.MIPStarRE.LDT.SubMeas.outcome_pos _ _) | (exact _root_.MIPStarRE.LDT.SubMeas.total_nonneg _) | (positivity) | (nlinarith)
    sum_eq_total := rfl
    total_le_one := totalSandwichFamily_total_le_one A B q
  }

/-- Same-space output statement for `prop:cons-sub-meas`.

The paper-facing two-space output statement is
`ConsSubMeasHeterogeneousStmt`. -/
structure ConsSubMeasStmt {Question Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState (ι × ι)) (𝒟 : Distribution Question)
    (A : IdxSubMeas Question Outcome ι)
    (B : IdxMeas Question Outcome ι) (γ : Error) : Prop where
  diagonalControl :
    SDDRel ψ 𝒟 (IdxSubMeas.liftLeft A) (diagonalSandwichFamily A B) γ
  sandwichControl :
    SDDRel ψ 𝒟 (diagonalSandwichFamily A B) (totalSandwichFamily A B) γ
  combinedControl :
    SDDRel ψ 𝒟 (IdxSubMeas.liftLeft A) (totalSandwichFamily A B) (4 * γ)

/-! ## Sandwich expectations -/

/-- Averaged left term `E_x ∑_a ⟨ψ, (A_a B A_a ⊗ I) ψ⟩`. -/
noncomputable def leftSandwichExpectation {Question Outcome : Type*}
    {ι : Type*} [Fintype Outcome] [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState (ι × ι)) (𝒟 : Distribution Question)
    (A : IdxProjSubMeas Question Outcome ι)
    (B : MIPStarRE.Quantum.Op ι) : Error :=
  avgOver 𝒟 fun q =>
    ∑ a, ev ψ
      (leftTensor (ι₂ := ι) ((A q).outcome a) *
        leftTensor (ι₂ := ι) B *
        leftTensor (ι₂ := ι) ((A q).outcome a))

/-- Averaged middle term `E_x ∑_a ⟨ψ, (B ⊗ A_a) ψ⟩`. -/
noncomputable def middleSandwichExpectation {Question Outcome : Type*}
    {ι : Type*} [Fintype Outcome] [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState (ι × ι)) (𝒟 : Distribution Question)
    (A : IdxProjSubMeas Question Outcome ι)
    (B : MIPStarRE.Quantum.Op ι) : Error :=
  avgOver 𝒟 fun q =>
    ∑ a, ev ψ
      (leftTensor (ι₂ := ι) B *
        rightTensor (ι₁ := ι) ((A q).outcome a))

/-- Averaged right term `E_x ∑_a ⟨ψ, (B A_a ⊗ I) ψ⟩`. -/
noncomputable def rightSandwichExpectation {Question Outcome : Type*}
    {ι : Type*} [Fintype Outcome] [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState (ι × ι)) (𝒟 : Distribution Question)
    (A : IdxProjSubMeas Question Outcome ι)
    (B : MIPStarRE.Quantum.Op ι) : Error :=
  avgOver 𝒟 fun q =>
    ∑ a, ev ψ
      (leftTensor (ι₂ := ι) (B * (A q).outcome a))

/-- Conclusion statement for `prop:switch-sandwich`. -/
structure SwitchSandwichStmt {Question Outcome : Type*}
    {ι : Type*} [Fintype Outcome] [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState (ι × ι)) (𝒟 : Distribution Question)
    (A : IdxProjSubMeas Question Outcome ι)
    (B : MIPStarRE.Quantum.Op ι) (δ : Error) : Prop where
  leftSandwichTransfer :
    |leftSandwichExpectation ψ 𝒟 A B -
      middleSandwichExpectation ψ 𝒟 A B|
      ≤ 2 * Real.sqrt δ
  rightSandwichTransfer :
    |middleSandwichExpectation ψ 𝒟 A B -
      rightSandwichExpectation ψ 𝒟 A B|
      ≤ Real.sqrt δ

/-- Conclusion statement for `prop:completeness-transfer-projective-P`. -/
structure CompTransferStmt {Question Outcome : Type*}
    {ι : Type*} [Fintype Outcome] [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι) (𝒟 : Distribution Question)
    (A : IdxSubMeas Question Outcome ι)
    (P : IdxProjSubMeas Question Outcome ι) (ε : Error) : Prop where
  completenessTransfer :
    idxSubMeasMass ψ 𝒟 A ≥
      idxSubMeasMass ψ 𝒟
        (IdxProjSubMeas.toIdxSubMeas P)
        - 2 * Real.sqrt ε

/-! ## Completion -/

/-- The completed outcomes sum to the identity. -/
theorem completeAtOutcome_sum_eq_one {Outcome : Type*}
    {ι : Type*} [Fintype Outcome] [DecidableEq Outcome] [Fintype ι] [DecidableEq ι]
    (B : SubMeas Outcome ι) (a0 : Outcome) :
    (∑ a : Outcome,
      if a = a0 then B.outcome a + (1 - B.total) else B.outcome a) = 1 := by
  have hsingle :
      (∑ x : Outcome, if x = a0 then 1 - B.total else 0) = 1 - B.total := by
    simp
  have hrewrite :
      (∑ a : Outcome, if a = a0 then B.outcome a + (1 - B.total) else B.outcome a) =
        ∑ a : Outcome, (B.outcome a + if a = a0 then 1 - B.total else 0) := by
    apply Finset.sum_congr rfl
    intro a _
    by_cases h : a = a0 <;> simp [h]
  rw [hrewrite, Finset.sum_add_distrib, B.sum_eq_total, hsingle]
  simp

/-- Canonical completion of `B` by adjoining the residual `I - Σ_a B_a`
to the distinguished outcome `a0`. -/
noncomputable def completeAtOutcome {Outcome : Type*}
    {ι : Type*} [Fintype Outcome] [Fintype ι] [DecidableEq ι]
    (B : SubMeas Outcome ι) (a0 : Outcome) : Measurement Outcome ι := by
  classical
  let residual := 1 - B.total
  exact {
    toSubMeas := {
      outcome := fun a =>
        if h : a = a0 then
          B.outcome a + residual
        else
          B.outcome a
      total := 1
      outcome_pos := fun a => by
        by_cases h : a = a0
        · simpa [h, residual] using
            add_nonneg (B.outcome_pos a0) (sub_nonneg.mpr B.total_le_one)
        · simp [h, B.outcome_pos a]
      sum_eq_total := completeAtOutcome_sum_eq_one B a0
      total_le_one := le_rfl
    }
    total_eq_one := rfl
  }

end MIPStarRE.LDT.Preliminaries


