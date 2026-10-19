-- Prove2me | Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_SubMeasurementFamilies
-- name    : MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_SubMeasurementFamilies
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T01:56:03.760977+00:00
-- url     : https://prove2.me/theorems/6baa0ada-c8b2-4278-a80f-8469de64032b
-- title:
--   Definitions of SubMeasurementFamilies: Indexed and bipartite submeasurement infrastructure Indexed measurement families, tensor placements, and lift/placement…
-- statement:
--   The definitions of the module `MIPRE.Background.LIDT.MIPStarRE.LDT.Basic.SubMeasurementFamilies` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Indexed and bipartite submeasurement infrastructure. Indexed measurement families, tensor placements, and lift/placement constructors.
--
--   The module is vendored read-only, with the authors' permission, from [LionSR/MIPStarRE](https://github.com/LionSR/MIPStarRE) (Sirui Lu and the MIPStarRE contributors, Apache 2.0; commit and upstream path in the file header) by `scripts/vendor-lidt.py`.
--
--   **Definitions** (27): `MIPStarRE.LDT.IdxMeas` (Question-indexed family of measurements.); `MIPStarRE.LDT.IdxMeas.toIdxSubMeas` (Forget completeness from an indexed measurement family.); `MIPStarRE.LDT.IdxProjMeas` (Question-indexed family of projective measurements.); `MIPStarRE.LDT.IdxProjMeas.toIdxMeas` (Forget projectivity from an indexed projective measurement family.); `MIPStarRE.LDT.IdxProjMeas.toIdxSubMeas` (Forget both projectivity and completeness from an indexed projective measurement family.); `MIPStarRE.LDT.IdxProjSubMeas` (Question-indexed family of projective submeasurements.); `MIPStarRE.LDT.IdxProjSubMeas.toIdxSubMeas` (Forget projectivity from an indexed projective submeasurement family.); `MIPStarRE.LDT.IdxSubMeas` (Question-indexed family of submeasurements.); `MIPStarRE.LDT.IdxSubMeas.liftLeft` (Lift an indexed submeasurement family to the left tensor factor.); `MIPStarRE.LDT.IdxSubMeas.liftRight` (Lift an indexed submeasurement family to the right tensor factor.); `MIPStarRE.LDT.IdxSubMeas.placeLeft` (Lift an indexed submeasurement family to the left tensor factor of `ιA × ιB` (general bipartite placement).); `MIPStarRE.LDT.IdxSubMeas.placeRight` (Lift an indexed submeasurement family to the right tensor factor of `ιA × ιB` (general bipartite placement).); `MIPStarRE.LDT.Measurement.transport` (Transport a measurement along an equivalence of outcome types.); `MIPStarRE.LDT.ProjMeas.postprocess` (Postprocess a projective measurement along a relabeling of the outcome type.); and 11 more.
--
--   **Embedded lemmas** (15): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `postprocess_toSubMeas`, `transport_toSubMeas`, `postprocess_outcome_proj`, `postprocess_id`, `postprocess_outcome`, `transport_outcome`, `transport_total`, `leftPlacedSubMeas_outcome`, `leftPlacedSubMeas_total`, `mkLeftPlacedSubMeas_outcome`, ….
--
--   **Formalization Note** The bundle is the module `MIPRE.Background.LIDT.MIPStarRE.LDT.Basic.SubMeasurementFamilies` (`MIPRE/Background/LIDT/MIPStarRE/LDT/Basic/SubMeasurementFamilies.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 10 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/LIDT/MIPStarRE/LDT/Basic/SubMeasurementFamilies.lean

/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/Basic/SubMeasurementFamilies.lean
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/MIPStarRE/LDT/Basic/SubMeasurementFamilies.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Defs
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
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.Notation.Defs
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
import Mathlib.Algebra.Order.Module.Defs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
import Mathlib.Algebra.Order.Nonneg.Basic
import Mathlib.Algebra.Order.Nonneg.Module
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Order.Sub.Defs
import Mathlib.Algebra.Order.ZeroLEOne
import Mathlib.Algebra.Polynomial.Basic
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
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Complex.BigOperators
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.Finite.Defs
import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Empty
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
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.FunLike.Basic
import Mathlib.Data.FunLike.Equiv
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.List.Nodup
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Matrix.Diagonal
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Multiset.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Init
import Mathlib.Data.Nat.Prime.Defs
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
import Mathlib.Logic.IsEmpty.Basic
import Mathlib.Logic.IsEmpty.Defs
import Mathlib.Logic.Nonempty
import Mathlib.Logic.Unique
import Mathlib.Order.Basic
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Lattice
import Mathlib.Order.RelClasses
import Mathlib.Order.SetNotation
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
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
import Theorems.Thm_MIPStarRE_LDT_ProjSubMeas_outcome_orthogonal
import Theorems.Thm_MIPStarRE_LDT_SubMeas_ext
import Theorems.Thm_MIPStarRE_LDT_averageOperatorOverDistribution_congr
import Theorems.Thm_MIPStarRE_LDT_averageOperatorOverDistribution_le_one_of_weight_sum_le_one
import Theorems.Thm_MIPStarRE_LDT_averageOperatorOverDistribution_nonneg
import Theorems.Thm_MIPStarRE_LDT_averageOperatorOverDistribution_sum
import Theorems.Thm_MIPStarRE_LDT_leftTensor_finset_sum
import Theorems.Thm_MIPStarRE_LDT_leftTensor_le_one
import Theorems.Thm_MIPStarRE_LDT_leftTensor_mul_leftTensor
import Theorems.Thm_MIPStarRE_LDT_leftTensor_nonneg
import Theorems.Thm_MIPStarRE_LDT_rightTensor_finset_sum
import Theorems.Thm_MIPStarRE_LDT_rightTensor_le_one
import Theorems.Thm_MIPStarRE_LDT_rightTensor_nonneg

attribute [ext] MIPStarRE.LDT.SubMeas.ext

set_option backward.isDefEq.respectTransparency false

/-!
# Indexed and bipartite submeasurement infrastructure

Indexed measurement families, tensor placements, and lift/placement constructors.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT

/-! ### Indexed measurement families -/

/-- Question-indexed family of submeasurements. -/
abbrev IdxSubMeas (Question Outcome : Type*) (ι : Type*)
    [Fintype Outcome] [Fintype ι] [DecidableEq ι] :=
  Question → SubMeas Outcome ι

/-- Question-indexed family of measurements. -/
abbrev IdxMeas (Question Outcome : Type*) (ι : Type*)
    [Fintype Outcome] [Fintype ι] [DecidableEq ι] :=
  Question → Measurement Outcome ι

/-- Question-indexed family of projective submeasurements. -/
abbrev IdxProjSubMeas (Question Outcome : Type*) (ι : Type*)
    [Fintype Outcome] [Fintype ι] [DecidableEq ι] :=
  Question → ProjSubMeas Outcome ι

/-- Question-indexed family of projective measurements. -/
abbrev IdxProjMeas (Question Outcome : Type*) (ι : Type*)
    [Fintype Outcome] [Fintype ι] [DecidableEq ι] :=
  Question → ProjMeas Outcome ι

namespace IdxMeas

/-- Forget completeness from an indexed measurement family. -/
def toIdxSubMeas {Question Outcome : Type*} {ι : Type*}
    [Fintype Outcome] [Fintype ι] [DecidableEq ι]
    (A : IdxMeas Question Outcome ι) :
    IdxSubMeas Question Outcome ι :=
  fun q => (A q).toSubMeas

end IdxMeas

namespace IdxProjSubMeas

/-- Forget projectivity from an indexed projective submeasurement family. -/
def toIdxSubMeas {Question Outcome : Type*} {ι : Type*}
    [Fintype Outcome] [Fintype ι] [DecidableEq ι]
    (A : IdxProjSubMeas Question Outcome ι) :
    IdxSubMeas Question Outcome ι :=
  fun q => (A q).toSubMeas

end IdxProjSubMeas

namespace IdxProjMeas

/-- Forget projectivity from an indexed projective measurement family. -/
def toIdxMeas {Question Outcome : Type*} {ι : Type*}
    [Fintype Outcome] [Fintype ι] [DecidableEq ι]
    (A : IdxProjMeas Question Outcome ι) :
    IdxMeas Question Outcome ι :=
  fun q => (A q).toMeasurement

/-- Forget both projectivity and completeness from an indexed projective measurement family. -/
def toIdxSubMeas {Question Outcome : Type*} {ι : Type*}
    [Fintype Outcome] [Fintype ι] [DecidableEq ι]
    (A : IdxProjMeas Question Outcome ι) :
    IdxSubMeas Question Outcome ι :=
  fun q => (A q).toSubMeas

end IdxProjMeas

open scoped Classical in
/-- Post-process the outcomes of a submeasurement. The processed operator at `b` is the
sum of the operators of all `a` with `f a = b`. -/
noncomputable def postprocess {α β : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype α] [Fintype β]
    (A : SubMeas α ι) (f : α → β) :
    SubMeas β ι where
  outcome := fun b =>
    ∑ a ∈ Finset.univ.filter (fun a => f a = b), A.outcome a
  total := A.total
  outcome_pos := fun _ => Finset.sum_nonneg fun a _ => A.outcome_pos a
  sum_eq_total := (Finset.sum_fiberwise Finset.univ f A.outcome).trans A.sum_eq_total
  total_le_one := A.total_le_one

namespace SubMeas

/-- The outcome of a postprocessed submeasurement is the sum over the fiber of
the readout map. -/
@[simp] theorem postprocess_outcome {α β ι : Type*}
    [Fintype α] [Fintype β] [Fintype ι] [DecidableEq β] [DecidableEq ι]
    (A : SubMeas α ι) (f : α → β) (b : β) :
    (postprocess A f).outcome b =
      ∑ a ∈ Finset.univ.filter (fun a => f a = b), A.outcome a := by
  classical
  simp only [postprocess]
  refine Finset.sum_congr ?_ ?_
  · ext a
    simp
  · intro a _
    try rfl -- vendoring compile fix (Lean v4.33): the previous step may close the goal

/-- Postprocessing a submeasurement by the identity readout leaves it unchanged. -/
@[simp] theorem postprocess_id {α ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    (A : SubMeas α ι) :
    postprocess A (fun a : α => a) = A := by
  classical
  refine SubMeas.ext ?_ rfl
  intro a
  simp only [postprocess, Finset.sum_filter]
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _hb hba
    simp [hba]
  · intro ha
    simp at ha

/-- Transport a submeasurement along an equivalence of outcome types. -/
noncomputable def transport {α β : Type*} {ι : Type*}
    [Fintype α] [Fintype β] [Fintype ι] [DecidableEq ι]
    (e : α ≃ β) (A : SubMeas α ι) :
    SubMeas β ι where
  outcome := fun b => A.outcome (e.symm b)
  total := A.total
  outcome_pos := fun b => A.outcome_pos (e.symm b)
  sum_eq_total := (Equiv.sum_comp e.symm A.outcome).trans A.sum_eq_total
  total_le_one := A.total_le_one

@[simp] theorem transport_outcome {α β : Type*} {ι : Type*}
    [Fintype α] [Fintype β] [Fintype ι] [DecidableEq ι]
    (e : α ≃ β) (A : SubMeas α ι) (b : β) :
    (transport e A).outcome b = A.outcome (e.symm b) :=
  rfl

@[simp] theorem transport_total {α β : Type*} {ι : Type*}
    [Fintype α] [Fintype β] [Fintype ι] [DecidableEq ι]
    (e : α ≃ β) (A : SubMeas α ι) :
    (transport e A).total = A.total :=
  rfl

end SubMeas

namespace Measurement

/-- Transport a measurement along an equivalence of outcome types. -/
noncomputable def transport {α β : Type*} {ι : Type*}
    [Fintype α] [Fintype β] [Fintype ι] [DecidableEq ι]
    (e : α ≃ β) (A : Measurement α ι) :
    Measurement β ι where
  toSubMeas := SubMeas.transport e A.toSubMeas
  total_eq_one := A.total_eq_one

end Measurement

namespace ProjSubMeas

/-- Postprocessing a projective submeasurement preserves outcome projectivity. -/
theorem postprocess_outcome_proj {α β : Type*} {ι : Type*}
    [Fintype α] [Fintype β] [Fintype ι] [DecidableEq ι]
    (P : ProjSubMeas α ι) (f : α → β) (b : β) :
    (postprocess P.toSubMeas f).outcome b * (postprocess P.toSubMeas f).outcome b =
      (postprocess P.toSubMeas f).outcome b := by
  classical
  let fiber : Finset α := Finset.univ.filter fun a => f a = b
  calc
    (postprocess P.toSubMeas f).outcome b * (postprocess P.toSubMeas f).outcome b
      = (∑ a ∈ fiber, P.outcome a) * (∑ a' ∈ fiber, P.outcome a') := by
          simp [postprocess, fiber]
    _ = ∑ a ∈ fiber, ∑ a' ∈ fiber, P.outcome a * P.outcome a' := by
          rw [Finset.sum_mul]
          simp_rw [Finset.mul_sum]
    _ = ∑ a ∈ fiber, ∑ a' ∈ fiber, if a' = a then P.outcome a else 0 := by
          refine Finset.sum_congr rfl ?_
          intro a ha
          refine Finset.sum_congr rfl ?_
          intro a' ha'
          by_cases h : a' = a
          · subst h
            simp [P.proj]
          · have hne : a ≠ a' := fun h' => h h'.symm
            simp [ProjSubMeas.outcome_orthogonal P _ _ hne, h]
    _ = ∑ a ∈ fiber, P.outcome a := by
          refine Finset.sum_congr rfl ?_
          intro a ha
          simp [fiber, ha]
    _ = (postprocess P.toSubMeas f).outcome b := by
          simp [postprocess, fiber]

end ProjSubMeas

namespace ProjMeas

/-- Transport a projective measurement along an equivalence of outcome types. -/
noncomputable def transport {α β : Type*} {ι : Type*}
    [Fintype α] [Fintype β] [Fintype ι] [DecidableEq ι]
    (e : α ≃ β) (A : ProjMeas α ι) :
    ProjMeas β ι where
  toMeasurement := Measurement.transport e A.toMeasurement
  proj := fun b => A.proj (e.symm b)

@[simp] theorem transport_toSubMeas {α β : Type*} {ι : Type*}
    [Fintype α] [Fintype β] [Fintype ι] [DecidableEq ι]
    (e : α ≃ β) (A : ProjMeas α ι) :
    (transport e A).toSubMeas = SubMeas.transport e A.toSubMeas :=
  rfl

/-- Postprocess a projective measurement along a relabeling of the outcome type.

The fiber of each output value is a sum of mutually orthogonal projectors, so
postprocessing preserves projectivity as well as completeness. -/
noncomputable def postprocess {α β : Type*} {ι : Type*}
    [Fintype α] [Fintype β] [Fintype ι] [DecidableEq ι]
    (A : ProjMeas α ι) (f : α → β) :
    ProjMeas β ι where
  toMeasurement := {
    toSubMeas := MIPStarRE.LDT.postprocess A.toSubMeas f
    total_eq_one := A.total_eq_one
  }
  proj := fun b => ProjSubMeas.postprocess_outcome_proj ⟨A.toSubMeas, A.proj⟩ f b

@[simp] theorem postprocess_toSubMeas {α β : Type*} {ι : Type*}
    [Fintype α] [Fintype β] [Fintype ι] [DecidableEq ι]
    (A : ProjMeas α ι) (f : α → β) :
    (postprocess A f).toSubMeas = MIPStarRE.LDT.postprocess A.toSubMeas f :=
  rfl

end ProjMeas

/-- Complete a submeasurement by adjoining a distinguished failure outcome. -/
noncomputable def completeSubMeas {α : Type*} {ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    (A : SubMeas α ι) : Measurement (Option α) ι where
  toSubMeas := {
    outcome := fun
      | some a => A.outcome a
      | none => 1 - A.total
    total := 1
    outcome_pos := fun
      | some a => A.outcome_pos a
      | none => sub_nonneg.mpr A.total_le_one
    sum_eq_total := (Fintype.sum_option _).trans <|
      (congrArg (1 - A.total + ·) A.sum_eq_total).trans (sub_add_cancel 1 A.total)
    total_le_one := le_rfl
  }
  total_eq_one := rfl

/-- Constant indexed family taking the same submeasurement on every question. -/
def constSubMeasFamily {α : Type*} {ι : Type*} [Fintype α] [Fintype ι] [DecidableEq ι]
    (A : SubMeas α ι) :
    IdxSubMeas Unit α ι :=
  fun _ => A

/-- Average an indexed submeasurement family against a finite distribution.

The hypothesis `∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1` says that `𝒟` is a sub-probability
distribution (total mass at most `1`); this is all that is needed to keep the
averaged total operator below `1`. -/
noncomputable def averageIdxSubMeas {Question Outcome : Type*} [Fintype Outcome]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (𝒟 : Distribution Question) (A : IdxSubMeas Question Outcome ι)
    (h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1) :
    SubMeas Outcome ι where
  outcome := fun a =>
    averageOperatorOverDistribution 𝒟 (fun q => (A q).outcome a)
  total :=
    averageOperatorOverDistribution 𝒟 (fun q => (A q).total)
  outcome_pos := fun a =>
    averageOperatorOverDistribution_nonneg 𝒟
      (fun q => (A q).outcome a) (fun q => (A q).outcome_pos a)
  sum_eq_total :=
    (averageOperatorOverDistribution_sum 𝒟 (fun q a => (A q).outcome a)).symm.trans
      (averageOperatorOverDistribution_congr 𝒟 _ _ fun q => (A q).sum_eq_total)
  total_le_one :=
    averageOperatorOverDistribution_le_one_of_weight_sum_le_one 𝒟
      (fun q => (A q).total) h𝒟 (fun q => (A q).total_le_one)

/-! ### Tensor-placement constructors -/

def mkLeftPlacedSubMeas {α : Type*}
    {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype α] (A : SubMeas α ιA) :
    SubMeas α (ιA × ιB) where
  outcome := fun a => leftTensor (ι₂ := ιB) (A.outcome a)
  total := leftTensor (ι₂ := ιB) A.total
  outcome_pos := fun a => leftTensor_nonneg (ι₂ := ιB) (A.outcome_pos a)
  sum_eq_total := (leftTensor_finset_sum (ι₂ := ιB) Finset.univ A.outcome).trans
    (congrArg (leftTensor (ι₂ := ιB)) A.sum_eq_total)
  total_le_one := leftTensor_le_one (ι₂ := ιB) A.total_le_one

def mkRightPlacedSubMeas {α : Type*}
    {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype α] (A : SubMeas α ιB) :
    SubMeas α (ιA × ιB) where
  outcome := fun a => rightTensor (ι₁ := ιA) (A.outcome a)
  total := rightTensor (ι₁ := ιA) A.total
  outcome_pos := fun a => rightTensor_nonneg (ι₁ := ιA) (A.outcome_pos a)
  sum_eq_total := (rightTensor_finset_sum (ι₁ := ιA) Finset.univ A.outcome).trans
    (congrArg (rightTensor (ι₁ := ιA)) A.sum_eq_total)
  total_le_one := rightTensor_le_one (ι₁ := ιA) A.total_le_one

/-- Helper-level projection equation for left-placed outcomes. -/
@[simp] theorem mkLeftPlacedSubMeas_outcome {α : Type*}
    {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype α] (A : SubMeas α ιA) (a : α) :
    (mkLeftPlacedSubMeas (ιB := ιB) A).outcome a =
      leftTensor (ι₂ := ιB) (A.outcome a) :=
  rfl

/-- Helper-level projection equation for left-placed totals. -/
@[simp] theorem mkLeftPlacedSubMeas_total {α : Type*}
    {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype α] (A : SubMeas α ιA) :
    (mkLeftPlacedSubMeas (ιB := ιB) A).total =
      leftTensor (ι₂ := ιB) A.total :=
  rfl

/-- Helper-level projection equation for right-placed outcomes. -/
@[simp] theorem mkRightPlacedSubMeas_outcome {α : Type*}
    {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype α] (A : SubMeas α ιB) (a : α) :
    (mkRightPlacedSubMeas (ιA := ιA) A).outcome a =
      rightTensor (ι₁ := ιA) (A.outcome a) :=
  rfl

/-- Helper-level projection equation for right-placed totals. -/
@[simp] theorem mkRightPlacedSubMeas_total {α : Type*}
    {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype α] (A : SubMeas α ιB) :
    (mkRightPlacedSubMeas (ιA := ιA) A).total =
      rightTensor (ι₁ := ιA) A.total :=
  rfl

/-! ### Square bipartite lifts -/

/-- Lift a submeasurement to the left tensor factor of a bipartite space `ι × ι`.
Each outcome operator `A_a : Op ι` becomes `A_a ⊗ I : Op (ι × ι)`. -/
def SubMeas.liftLeft {α : Type*} {ι : Type*} [Fintype α] [Fintype ι] [DecidableEq ι]
    (A : SubMeas α ι) : SubMeas α (ι × ι) :=
  mkLeftPlacedSubMeas (ιB := ι) A

/-- Lift an indexed submeasurement family to the left tensor factor. -/
def IdxSubMeas.liftLeft {Question Outcome : Type*} {ι : Type*}
    [Fintype Outcome] [Fintype ι] [DecidableEq ι]
    (A : IdxSubMeas Question Outcome ι) : IdxSubMeas Question Outcome (ι × ι) :=
  fun q => mkLeftPlacedSubMeas (ιB := ι) (A q)

/-- Lift a projective submeasurement to the left tensor factor of a bipartite
space `ι × ι`. -/
def ProjSubMeas.liftLeft {α : Type*} {ι : Type*} [Fintype α] [Fintype ι] [DecidableEq ι]
    (A : ProjSubMeas α ι) : ProjSubMeas α (ι × ι) :=
  { toSubMeas := A.toSubMeas.liftLeft
    proj := fun a => (leftTensor_mul_leftTensor (A.outcome a) (A.outcome a)).trans
      (congrArg (leftTensor (ι₂ := ι)) (A.proj a)) }

/-- Lift a submeasurement to the right tensor factor of a bipartite space `ι × ι`.
Each outcome operator `A_a : Op ι` becomes `I ⊗ A_a : Op (ι × ι)`. -/
def SubMeas.liftRight {α : Type*} {ι : Type*} [Fintype α] [Fintype ι] [DecidableEq ι]
    (A : SubMeas α ι) : SubMeas α (ι × ι) :=
  mkRightPlacedSubMeas (ιA := ι) A

/-- Lift an indexed submeasurement family to the right tensor factor. -/
def IdxSubMeas.liftRight {Question Outcome : Type*} {ι : Type*}
    [Fintype Outcome] [Fintype ι] [DecidableEq ι]
    (A : IdxSubMeas Question Outcome ι) : IdxSubMeas Question Outcome (ι × ι) :=
  fun q => mkRightPlacedSubMeas (ιA := ι) (A q)

/-! ### General bipartite placement -/

/-- Place a submeasurement on the left tensor factor of `ιA × ιB`. -/
def leftPlacedSubMeas {α : Type*}
    {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype α]
    (A : SubMeas α ιA) :
    SubMeas α (ιA × ιB) :=
  mkLeftPlacedSubMeas (ιB := ιB) A

/-- Outcome operators of a left-placed submeasurement are left tensor placements. -/
@[simp] theorem leftPlacedSubMeas_outcome {α : Type*}
    {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype α] (A : SubMeas α ιA) (a : α) :
    (leftPlacedSubMeas (ιB := ιB) A).outcome a =
      leftTensor (ι₂ := ιB) (A.outcome a) :=
  rfl

/-- The total operator of a left-placed submeasurement is a left tensor placement. -/
@[simp] theorem leftPlacedSubMeas_total {α : Type*}
    {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype α] (A : SubMeas α ιA) :
    (leftPlacedSubMeas (ιB := ιB) A).total =
      leftTensor (ι₂ := ιB) A.total :=
  rfl

/-- Place a submeasurement on the right tensor factor of `ιA × ιB`. -/
def rightPlacedSubMeas {α : Type*}
    {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype α]
    (A : SubMeas α ιB) :
    SubMeas α (ιA × ιB) :=
  mkRightPlacedSubMeas (ιA := ιA) A

/-- Outcome operators of a right-placed submeasurement are right tensor placements. -/
@[simp] theorem rightPlacedSubMeas_outcome {α : Type*}
    {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype α] (A : SubMeas α ιB) (a : α) :
    (rightPlacedSubMeas (ιA := ιA) A).outcome a =
      rightTensor (ι₁ := ιA) (A.outcome a) :=
  rfl

/-- The total operator of a right-placed submeasurement is a right tensor placement. -/
@[simp] theorem rightPlacedSubMeas_total {α : Type*}
    {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype α] (A : SubMeas α ιB) :
    (rightPlacedSubMeas (ιA := ιA) A).total =
      rightTensor (ι₁ := ιA) A.total :=
  rfl

/-- Lift an indexed submeasurement family to the left tensor factor of
`ιA × ιB` (general bipartite placement). -/
def IdxSubMeas.placeLeft {Question Outcome : Type*}
    {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype Outcome]
    (A : IdxSubMeas Question Outcome ιA) :
    IdxSubMeas Question Outcome (ιA × ιB) :=
  fun q => mkLeftPlacedSubMeas (ιB := ιB) (A q)

/-- Lift an indexed submeasurement family to the right tensor factor of
`ιA × ιB` (general bipartite placement). -/
def IdxSubMeas.placeRight {Question Outcome : Type*}
    {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype Outcome]
    (A : IdxSubMeas Question Outcome ιB) :
    IdxSubMeas Question Outcome (ιA × ιB) :=
  fun q => mkRightPlacedSubMeas (ιA := ιA) (A q)

end MIPStarRE.LDT


