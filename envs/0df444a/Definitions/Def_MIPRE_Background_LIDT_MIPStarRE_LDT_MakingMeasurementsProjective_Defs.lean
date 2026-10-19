-- Prove2me | Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
-- name    : MIPRE_Background_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T00:57:43.859705+00:00
-- url     : https://prove2.me/theorems/b0cd8441-e39a-4561-8646-8b70f3c4faf2
-- title:
--   Definitions of Defs: Section 5 — Making measurements projective: definitions Definitions for Naimark dilation and orthonormalization,…
-- statement:
--   The definitions of the module `MIPRE.Background.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.Defs` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Section 5 — Making measurements projective: definitions. Definitions for Naimark dilation and orthonormalization, matching Section 5 of `references/ldt-paper/orthonormalization.tex` and Chapter 4 of the blueprint (`blueprint/src/chapter/ch04_projective.tex`).
--
--   The module is vendored read-only, with the authors' permission, from [LionSR/MIPStarRE](https://github.com/LionSR/MIPStarRE) (Sirui Lu and the MIPStarRE contributors, Apache 2.0; commit and upstream path in the file header) by `scripts/vendor-lidt.py`.
--
--   **Definitions** (16): `MIPStarRE.LDT.MakingMeasurementsProjective.FiniteHilbertSpace` (A finite-dimensional Hilbert space represented by a finite index type.); `MIPStarRE.LDT.MakingMeasurementsProjective.MatrixMeasurement` (Concrete measurements on a finite Hilbert space.); `MIPStarRE.LDT.MakingMeasurementsProjective.MatrixMeasurement.toMeasurement` (View a concrete matrix measurement as the paper-local measurement structure.); `MIPStarRE.LDT.MakingMeasurementsProjective.MatrixOperator` (Concrete operators on a finite Hilbert space.); `MIPStarRE.LDT.MakingMeasurementsProjective.MatrixOperator.normedAddCommGroup`; `MIPStarRE.LDT.MakingMeasurementsProjective.MatrixOperator.normedSpace`; `MIPStarRE.LDT.MakingMeasurementsProjective.MatrixOperator.seminormedAddCommGroup`; `MIPStarRE.LDT.MakingMeasurementsProjective.MatrixSubmeasurement` (Concrete submeasurements on a finite Hilbert space.); `MIPStarRE.LDT.MakingMeasurementsProjective.MatrixSubmeasurement.toSubMeas` (View a concrete matrix submeasurement as the paper-local submeasurement structure.); `MIPStarRE.LDT.MakingMeasurementsProjective.PositiveMatrixState` (A positive operator used as a possibly unnormalized state witness.); `MIPStarRE.LDT.MakingMeasurementsProjective.consistencyToAlmostProjectiveError` (The almost-projective error extracted from a consistency hypothesis.); `MIPStarRE.LDT.MakingMeasurementsProjective.matrixExpectation` (The concrete expectation `τ(ρ X)` on the local matrix layer.); and 3 more.
--
--   **Embedded lemmas** (4): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `toMeasurement_outcome`, `toMeasurement_toSubMeas`, `toSubMeas_outcome`, `toSubMeas_total`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Background.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.Defs` (`MIPRE/Background/LIDT/MIPStarRE/LDT/MakingMeasurementsProjective/Defs.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 9 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/LIDT/MIPStarRE/LDT/MakingMeasurementsProjective/Defs.lean

/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/MakingMeasurementsProjective/Defs.lean
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/MIPStarRE/LDT/MakingMeasurementsProjective/Defs.lean (definition bundle: declarations the uploaded statements rest on);
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
import Mathlib.Analysis.LocallyConvex.WithSeminorms
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
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Complex.BigOperators
import Mathlib.Data.Countable.Defs
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
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.UniformSpace.Defs
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_QuantumState
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_SubMeasurementCore
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_Quantum_Measurement

set_option backward.isDefEq.respectTransparency false

/-!
# Section 5 — Making measurements projective: definitions

Definitions for Naimark dilation and orthonormalization, matching
Section 5 of `references/ldt-paper/orthonormalization.tex` and
Chapter 4 of the blueprint (`blueprint/src/chapter/ch04_projective.tex`).

## Naimark dilation structure

The key mathematical content is the **Naimark dilation theorem**: given
submeasurements on a bipartite space, there exist auxiliary registers and
projective measurements on the enlarged space that preserve all correlations
exactly.

### One-measurement Naimark (Lemma 5.2)

The building block is the one-measurement Naimark lemma. Given a
submeasurement `{M_a}_{a ∈ α}` on `Op d`, it produces a projective
submeasurement on the enlarged space `Op (d × Option α)`. The auxiliary
register has dimension `|α| + 1`, with the extra dimension absorbing the
"missing mass" `I − ∑ M_a`. The construction uses the isometry
`V|ψ⟩ = ∑_a √M_a |ψ⟩ ⊗ |a⟩ + √(I−M)|ψ⟩ ⊗ |⊥⟩` and defines
`P̂_a = V† (I ⊗ |a⟩⟨a|) V`.

### Questionwise Naimark data

For a prospective full bipartite assembly, one-measurement Naimark is applied
independently to each question on each side.  The current formal interface
records these questionwise local data and their marginal preservation
identities, not the full tensor-product correlation theorem.

## Matrix-level witnesses

Concrete `Matrix d d ℂ` witnesses are provided alongside the abstract
operator-algebra formulation, giving honest probability and overlap formulas.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT.MakingMeasurementsProjective

open MIPStarRE.LDT

/-! ### Finite Hilbert space infrastructure -/

/-- A finite-dimensional Hilbert space represented by a finite index type. -/
structure FiniteHilbertSpace where
  carrier : Type*
  instFintype : Fintype carrier
  instDecidableEq : DecidableEq carrier
  instNonempty : Nonempty carrier

attribute [instance] MIPStarRE.LDT.MakingMeasurementsProjective.FiniteHilbertSpace.instFintype
attribute [instance] MIPStarRE.LDT.MakingMeasurementsProjective.FiniteHilbertSpace.instDecidableEq
attribute [instance] MIPStarRE.LDT.MakingMeasurementsProjective.FiniteHilbertSpace.instNonempty

/-- Concrete operators on a finite Hilbert space. -/
abbrev MatrixOperator (H : FiniteHilbertSpace) :=
  MIPStarRE.Quantum.Op H.carrier

namespace MatrixOperator

/-! The SDP separation argument uses the elementwise finite-matrix norm.  These
instances record that choice once for the project's concrete operator type,
rather than reintroducing it in each analytic argument. -/

noncomputable instance seminormedAddCommGroup
    (H : FiniteHilbertSpace) :
    SeminormedAddCommGroup (MatrixOperator H) :=
  Matrix.seminormedAddCommGroup

noncomputable instance normedAddCommGroup
    (H : FiniteHilbertSpace) :
    NormedAddCommGroup (MatrixOperator H) :=
  Matrix.normedAddCommGroup

noncomputable instance normedSpace
    (H : FiniteHilbertSpace) :
    NormedSpace ℝ (MatrixOperator H) :=
  Matrix.normedSpace

end MatrixOperator

/-- A positive operator used as a possibly unnormalized state witness. -/
structure PositiveMatrixState (H : FiniteHilbertSpace) where
  matrix : MatrixOperator H
  positive : 0 ≤ matrix

/-- Concrete submeasurements on a finite Hilbert space. -/
abbrev MatrixSubmeasurement (Outcome : Type*)
    [Fintype Outcome] [DecidableEq Outcome] (H : FiniteHilbertSpace) :=
  MIPStarRE.Quantum.Submeasurement Outcome H.carrier

/-- Concrete measurements on a finite Hilbert space. -/
abbrev MatrixMeasurement (Outcome : Type*)
    [Fintype Outcome] [DecidableEq Outcome] (H : FiniteHilbertSpace) :=
  MIPStarRE.Quantum.Measurement Outcome H.carrier

namespace MatrixSubmeasurement

/-- View a concrete matrix submeasurement as the paper-local submeasurement
structure. -/
noncomputable def toSubMeas {Outcome : Type*}
    [Fintype Outcome] [DecidableEq Outcome]
    {H : FiniteHilbertSpace}
    (M : MatrixSubmeasurement Outcome H) : SubMeas Outcome H.carrier where
  outcome := M.effect
  total := MIPStarRE.Quantum.Submeasurement.total M
  outcome_pos := M.pos
  sum_eq_total := rfl
  total_le_one := M.sum_le_one

@[simp] theorem toSubMeas_outcome {Outcome : Type*}
    [Fintype Outcome] [DecidableEq Outcome]
    {H : FiniteHilbertSpace}
    (M : MatrixSubmeasurement Outcome H) (a : Outcome) :
    (toSubMeas M).outcome a = M.effect a :=
  rfl

@[simp] theorem toSubMeas_total {Outcome : Type*}
    [Fintype Outcome] [DecidableEq Outcome]
    {H : FiniteHilbertSpace}
    (M : MatrixSubmeasurement Outcome H) :
    (toSubMeas M).total = MIPStarRE.Quantum.Submeasurement.total M :=
  rfl

end MatrixSubmeasurement

namespace MatrixMeasurement

/-- View a concrete matrix measurement as the paper-local measurement
structure. -/
noncomputable def toMeasurement {Outcome : Type*}
    [Fintype Outcome] [DecidableEq Outcome]
    {H : FiniteHilbertSpace}
    (M : MatrixMeasurement Outcome H) : MIPStarRE.LDT.Measurement Outcome H.carrier where
  toSubMeas := MatrixSubmeasurement.toSubMeas M.toSubmeasurement
  total_eq_one := M.sum_eq_one

@[simp] theorem toMeasurement_toSubMeas {Outcome : Type*}
    [Fintype Outcome] [DecidableEq Outcome]
    {H : FiniteHilbertSpace}
    (M : MatrixMeasurement Outcome H) :
    (toMeasurement M).toSubMeas =
      MatrixSubmeasurement.toSubMeas M.toSubmeasurement :=
  rfl

@[simp] theorem toMeasurement_outcome {Outcome : Type*}
    [Fintype Outcome] [DecidableEq Outcome]
    {H : FiniteHilbertSpace}
    (M : MatrixMeasurement Outcome H) (a : Outcome) :
    (toMeasurement M).outcome a = M.effect a :=
  rfl

end MatrixMeasurement

/-- The concrete expectation `τ(ρ X)` on the local matrix layer. -/
noncomputable def matrixExpectation {H : FiniteHilbertSpace}
    (ρ : PositiveMatrixState H) (X : MatrixOperator H) : ℂ :=
  MIPStarRE.Quantum.normalizedTrace (ρ.matrix * X)

/-! ### One-measurement Naimark dilation (Lemma 5.2)

The one-measurement Naimark dilation is the building block for the full
theorem. Given a submeasurement `M` on space `d`, it produces a projective
submeasurement on the enlarged space `d × Option α`, where `Option α`
models the auxiliary register with one extra dimension `none = ⊥` for the
missing mass `I − ∑ M_a`. -/

/-! ### Questionwise Naimark data

The current Lean data applies one-measurement Naimark independently to each
question on each side. -/

-- NOTE: no global `Inhabited` instance for `NaimarkData`:
-- constructing defaults for projective measurements is mathematically non-canonical
-- and would require additional assumptions on outcome types.

/-! ### Error functions for orthonormalization -/

/-- The explicit error in `thm:orthonormalization`. -/
noncomputable def orthonormalizationError (ζ : Error) : Error :=
  100 * Real.rpow ζ (1 / (4 : Error))

/-- The explicit error in the measurement version of the lemma. -/
noncomputable def orthonormalizationMainLemmaError (ζ : Error) : Error :=
  84 * Real.rpow ζ (1 / (4 : Error))

/-- The almost-projective error extracted from a consistency hypothesis. -/
def consistencyToAlmostProjectiveError (ζ : Error) : Error :=
  2 * ζ

/-- The spectral-truncation error when rounding one almost-projective effect to a
    projection via eigenvalue truncation. Dominated by `√ζ`. -/
noncomputable def spectralTruncationError (ζ : Error) : Error :=
  Real.rpow ζ (1 / (2 : Error))

/-- The rounding error when converting an almost-projective POVM to a projective submeasurement. -/
noncomputable def roundingToProjectiveError (ζ : Error) : Error :=
  12 * Real.rpow ζ (1 / (2 : Error))

end MIPStarRE.LDT.MakingMeasurementsProjective


