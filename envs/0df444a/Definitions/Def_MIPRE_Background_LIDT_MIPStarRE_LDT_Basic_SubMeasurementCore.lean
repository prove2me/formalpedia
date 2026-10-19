-- Prove2me | Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_SubMeasurementCore
-- name    : MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_SubMeasurementCore
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T00:57:10.992499+00:00
-- url     : https://prove2.me/theorems/6a43f42e-c68c-46a2-bc51-9ea95ac84c0a
-- title:
--   Definitions of SubMeasurementCore: Core submeasurement structures for the low individual degree test Foundational measurement, submeasurement, and…
-- statement:
--   The definitions of the module `MIPRE.Background.LIDT.MIPStarRE.LDT.Basic.SubMeasurementCore` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Core submeasurement structures for the low individual degree test. Foundational measurement, submeasurement, and projective-measurement structures.
--
--   The module is vendored read-only, with the authors' permission, from [LionSR/MIPStarRE](https://github.com/LionSR/MIPStarRE) (Sirui Lu and the MIPStarRE contributors, Apache 2.0; commit and upstream path in the file header) by `scripts/vendor-lidt.py`.
--
--   **Definitions** (8): `MIPStarRE.LDT.Measurement` (A paper-local measurement: a POVM whose PSD effects sum to the identity.); `MIPStarRE.LDT.Measurement.trivialDistinguishedOutcome` (⚠️ DEGENERATE — Construct a trivial measurement where only the distinguished outcome `a₀` is the identity and all other outcomes are zero.); `MIPStarRE.LDT.ProjMeas` (A paper-local projective measurement (complete POVM + projective).); `MIPStarRE.LDT.ProjMeas.trivialDistinguishedOutcome` (⚠️ DEGENERATE — Construct a trivial projective measurement where only the distinguished outcome `a₀` is the identity and all other outcomes…); `MIPStarRE.LDT.ProjSubMeas` (A paper-local projective submeasurement (each effect is idempotent).); `MIPStarRE.LDT.SubMeas` (A paper-local submeasurement with outcomes in `α` and Hilbert space index `ι`.); `MIPStarRE.LDT.SubMeas.singleOutcome` (A one-outcome submeasurement associated to a single positive operator bounded by the identity.); `MIPStarRE.LDT.SubMeas.toMeasurement` (Promote a complete submeasurement to a measurement.).
--
--   **Embedded lemmas** (6): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `singleOutcome_outcome`, `singleOutcome_total`, `toMeasurement_outcome`, `toMeasurement_toSubMeas`, `trivialDistinguishedOutcome_outcome_pos`, `trivialDistinguishedOutcome_proj`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Background.LIDT.MIPStarRE.LDT.Basic.SubMeasurementCore` (`MIPRE/Background/LIDT/MIPStarRE/LDT/Basic/SubMeasurementCore.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 7 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/LIDT/MIPStarRE/LDT/Basic/SubMeasurementCore.lean

/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/Basic/SubMeasurementCore.lean
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/MIPStarRE/LDT/Basic/SubMeasurementCore.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Algebra.Spectrum.Quasispectrum
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.CharP.Invertible
import Mathlib.Algebra.CharZero.Defs
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
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Order.Group.Unbundled.Basic
import Mathlib.Algebra.Order.Module.Defs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
import Mathlib.Algebra.Order.Nonneg.Basic
import Mathlib.Algebra.Order.Nonneg.Module
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Order.Sub.Defs
import Mathlib.Algebra.Order.ZeroLEOne
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
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
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Complex.BigOperators
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.Finite.Defs
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Empty
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.EquivFin
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
import Mathlib.Order.RelClasses
import Mathlib.Order.SetNotation
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp.Lemmas
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Topology.Algebra.Field
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
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.UniformSpace.Defs
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_QuantumState

set_option backward.isDefEq.respectTransparency false

/-!
# Core submeasurement structures for the low individual degree test

Foundational measurement, submeasurement, and projective-measurement structures.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT

/-- A paper-local submeasurement with outcomes in `α` and Hilbert space index `ι`.

There is intentionally no global `Inhabited` instance: the zero family satisfies
these raw axioms, but using it as an ambient default would silently turn later
arguments into vacuous submeasurement statements. -/
structure SubMeas (α : Type*) [Fintype α] (ι : Type*) [Fintype ι] [DecidableEq ι] where
  outcome : α → MIPStarRE.Quantum.Op ι := fun _ => 0
  total : MIPStarRE.Quantum.Op ι := 0
  outcome_pos : ∀ a, 0 ≤ outcome a
  sum_eq_total : ∑ a, outcome a = total
  total_le_one : total ≤ 1

/-- A paper-local measurement: a POVM whose PSD effects sum to the identity. -/
structure Measurement (α : Type*) (ι : Type*) [Fintype α] [Fintype ι] [DecidableEq ι]
    extends SubMeas α ι where
  total_eq_one : total = 1

set_option linter.unusedFintypeInType false in
open scoped Classical in
/-- For a trivial distinguished-outcome measurement, every outcome operator is
positive semidefinite: `0 ≤ if a = a₀ then 1 else 0`. -/
theorem Measurement.trivialDistinguishedOutcome_outcome_pos
    {α : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι] (a₀ a : α) :
    (0 : MIPStarRE.Quantum.Op ι) ≤ if a = a₀ then 1 else 0 := by
  by_cases h : a = a₀ <;> simp [h]

open scoped Classical in
/-- ⚠️ DEGENERATE — Construct a trivial measurement where only the distinguished
outcome `a₀` is the identity and all other outcomes are zero.

This is a valid POVM but highly degenerate: it is only used in vacuous
fallback branches of the proof where the error bound is ≥ 1 (see
`Test/MainTheorem.lean:mainFormal_trivial_witness`).

Call this function explicitly with a chosen outcome.  There is intentionally no
ambient `Inhabited (Measurement α ι)` instance: choosing a hidden
`default : α` would make degenerate witnesses available to paper-facing
existential statements without displaying the selected outcome. -/
noncomputable def Measurement.trivialDistinguishedOutcome
    {α : Type*} {ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    (a₀ : α) : Measurement α ι where
  toSubMeas := {
    outcome := fun a => if a = a₀ then 1 else 0
    total := 1
    outcome_pos := fun a => Measurement.trivialDistinguishedOutcome_outcome_pos a₀ a
    sum_eq_total :=
      (Finset.sum_ite_eq' Finset.univ a₀ fun _ => 1).trans (if_pos (Finset.mem_univ a₀))
    total_le_one := le_rfl
  }
  total_eq_one := rfl

/-- A paper-local projective submeasurement (each effect is idempotent).

There is intentionally no global `Inhabited` instance: any such default would
again collapse to the degenerate zero family. -/
structure ProjSubMeas (α : Type*) [Fintype α] (ι : Type*) [Fintype ι] [DecidableEq ι]
    extends SubMeas α ι where
  proj : ∀ a, outcome a * outcome a = outcome a

/-- A paper-local projective measurement (complete POVM + projective). -/
structure ProjMeas (α : Type*) (ι : Type*) [Fintype α] [Fintype ι] [DecidableEq ι]
    extends Measurement α ι where
  proj : ∀ a, outcome a * outcome a = outcome a

/-- For a trivial distinguished-outcome projective measurement, every outcome operator
is idempotent. -/
theorem ProjMeas.trivialDistinguishedOutcome_proj
    {α : Type*} {ι : Type*} [Fintype α] [Fintype ι] [DecidableEq ι] (a₀ a : α) :
    (Measurement.trivialDistinguishedOutcome (ι := ι) a₀).outcome a *
        (Measurement.trivialDistinguishedOutcome (ι := ι) a₀).outcome a =
      (Measurement.trivialDistinguishedOutcome (ι := ι) a₀).outcome a := by
  classical
  by_cases h : a = a₀ <;> simp [Measurement.trivialDistinguishedOutcome, h]

/-- ⚠️ DEGENERATE — Construct a trivial projective measurement where only the
distinguished outcome `a₀` is the identity and all other outcomes are zero.

This is a valid projective POVM but highly degenerate: see the discussion at
`Measurement.trivialDistinguishedOutcome`.  Prefer calling this function
explicitly (with a chosen outcome) rather than relying on the ambient
`Inhabited` instance.  As for `Measurement`, there is intentionally no ambient
`Inhabited (ProjMeas α ι)` instance. -/
noncomputable def ProjMeas.trivialDistinguishedOutcome
    {α : Type*} {ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    (a₀ : α) : ProjMeas α ι where
  toMeasurement := Measurement.trivialDistinguishedOutcome a₀
  proj := ProjMeas.trivialDistinguishedOutcome_proj a₀

/-! ### Derived properties -/

-- vendoring compile fix (Lean v4.33): the previous step may close the goal

-- vendoring compile fix (Lean v4.33): the previous step may close the goal

-- vendoring compile fix (Lean v4.33): the previous step may close the goal

/-- A one-outcome submeasurement associated to a single positive operator
bounded by the identity. -/
def SubMeas.singleOutcome {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : MIPStarRE.Quantum.Op ι) (hA_pos : 0 ≤ A) (hA_le_one : A ≤ 1) :
    SubMeas Unit ι where
  outcome := fun _ => A
  total := A
  outcome_pos := fun _ => hA_pos
  sum_eq_total := Fintype.sum_unique fun _ => A
  total_le_one := hA_le_one

@[simp] theorem SubMeas.singleOutcome_outcome {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : MIPStarRE.Quantum.Op ι) (hA_pos : 0 ≤ A) (hA_le_one : A ≤ 1)
    (u : Unit) :
    (SubMeas.singleOutcome (ι := ι) A hA_pos hA_le_one).outcome u = A :=
  rfl

@[simp] theorem SubMeas.singleOutcome_total {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : MIPStarRE.Quantum.Op ι) (hA_pos : 0 ≤ A) (hA_le_one : A ≤ 1) :
    (SubMeas.singleOutcome (ι := ι) A hA_pos hA_le_one).total = A :=
  rfl

/-- Promote a complete submeasurement to a measurement.

This is the explicit bridge from the paper's sub-measurement convention
`∑ a, A_a ≤ I` to the POVM convention `∑ a, A_a = I`: callers must supply the
completion proof rather than relying on a degenerate default. -/
def SubMeas.toMeasurement {α : Type*} {ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    (A : SubMeas α ι) (hcomplete : A.total = 1) :
    Measurement α ι where
  toSubMeas := A
  total_eq_one := hcomplete

@[simp] theorem SubMeas.toMeasurement_toSubMeas {α : Type*} {ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    (A : SubMeas α ι) (hcomplete : A.total = 1) :
    (A.toMeasurement hcomplete).toSubMeas = A :=
  rfl

@[simp] theorem SubMeas.toMeasurement_outcome {α : Type*} {ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    (A : SubMeas α ι) (hcomplete : A.total = 1) (a : α) :
    (A.toMeasurement hcomplete).outcome a = A.outcome a :=
  rfl

end MIPStarRE.LDT


