-- Prove2me | Definitions.Def_MIPRE_Background_LIDT_Bridge_Measurement
-- name    : MIPRE_Background_LIDT_Bridge_Measurement
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T02:20:48.260537+00:00
-- url     : https://prove2.me/theorems/f3d0ffff-abcd-4f70-8ea2-c472798d4f5e
-- title:
--   Definitions of Measurement: Bridge, part 3: measurements A strategy for our game carries one projective measurement per question, with outcomes in…
-- statement:
--   The definitions of the module `MIPRE.Background.LIDT.Bridge.Measurement` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Bridge, part 3: measurements. A strategy for our game carries one projective measurement per question, with outcomes in `Answer F m d`. The MIPStarRE strategy container `ProjStrat` wants instead * point measurements with outcomes in the coded field, * a measurement for *every* presentation `(base, direction)` of an axis-parallel line, with outcomes the polynomials of degree `≤ d` in the parameter of that presentation, covariant under rebasing the presentation (`AxisParallelMeasurementReparamInvariant`), * and likewise for diagonal lines. This file builds these from the strategy's measurements…
--
--   **Definitions** (14): `MIPRE.LIDT.Bridge.affine` (Substitute `b + c·X` into a univariate polynomial.); `MIPRE.LIDT.Bridge.axisAnswer` (The axis-line answer, in the parameter `t` of a presentation whose base point has parameter `b` on the canonical line (so that `s = b +…); `MIPRE.LIDT.Bridge.axisBase` (The parameter, on the canonical line, of the base point of an axis-parallel line presentation.); `MIPRE.LIDT.Bridge.axisCanon` (The canonical line of an axis-parallel line presentation.); `MIPRE.LIDT.Bridge.axisMeas` (The axis-parallel line measurement family induced by a strategy's measurement family.); `MIPRE.LIDT.Bridge.axisPolyOf` (The univariate polynomial of degree `≤ d` answered to an axis-parallel line question (`0` for ill-typed answers).); `MIPRE.LIDT.Bridge.codedValue` (The coded value of an answer to a point question.); `MIPRE.LIDT.Bridge.diagAnswer` (The diagonal-line answer, in the parameter `t` of a presentation related to the canonical parameter by `s = b + c·t`, read from an answer…); `MIPRE.LIDT.Bridge.diagCanon` (The canonical line of a diagonal line presentation.); `MIPRE.LIDT.Bridge.diagData` (The change of parameters `s = b + c·t` from a diagonal line presentation to its canonical line: `b` is the pivot coordinate of the base…); `MIPRE.LIDT.Bridge.diagMeas` (The diagonal line measurement family induced by a strategy's measurement family.); and -6 more.
--
--   **Embedded lemmas** (6): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `eval_affine`, `natDegree_affine_le`, `natDegree_axisPolyOf_le`, `natDegree_diagPolyOf_le`, `toProjMeas_outcome`, `toProjMeas_total`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Background.LIDT.Bridge.Measurement` (`MIPRE/Background/LIDT/Bridge/Measurement.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 25 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/LIDT/Bridge/Measurement.lean

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/Bridge/Measurement.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.Algebra.Hom
import Mathlib.Algebra.Algebra.NonUnitalHom
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
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
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
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fin.Tuple.Basic
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
import Mathlib.FieldTheory.Finite.Basic
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
import Mathlib.Tactic.DeriveFintype
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
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Background_LIDT_Game
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_MIPRE_Background_LIDT_Bridge_Field
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_LinePolynomials
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_LowDegreePolynomial
import Definitions.Def_MIPRE_Background_LIDT_Bridge_Polynomial
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

set_option backward.isDefEq.respectTransparency false

/-!
# Bridge, part 3: measurements

A strategy for our game carries one projective measurement per question, with outcomes
in `Answer F m d`. The MIPStarRE strategy container `ProjStrat` wants instead

* point measurements with outcomes in the coded field,
* a measurement for *every* presentation `(base, direction)` of an axis-parallel line,
  with outcomes the polynomials of degree `≤ d` in the parameter of that presentation,
  covariant under rebasing the presentation (`AxisParallelMeasurementReparamInvariant`),
* and likewise for diagonal lines.

This file builds these from the strategy's measurements at the *canonical* line
questions: the measurement at a presentation `ℓ` is the coarse-graining
(`ProjMeas.postprocess`) of the measurement at the canonical question of `ℓ` along the
map sending an answer `g` (a polynomial in the canonical parameter `s`) to the polynomial
`t ↦ g(b + c·t)` in the parameter `t` of `ℓ`, where `s = b + c·t` is the change of
parameters. Covariance under rebasing then follows from the composition law
`affine_comp_shift`, and ill-typed answers are sent to the zero polynomial.
-/

open MIPStarRE.LDT (Fq ProjMeas SubMeas Measurement IdxProjMeas AxisParallelLine DiagonalLine AxisLinePolynomial DiagonalLinePolynomial AxisParallelMeasurementReparamInvariant DiagonalMeasurementReparamInvariant decodeScalar encodeScalar zeroCoord)
open scoped MatrixOrder ComplexOrder

noncomputable section

namespace MIPRE.LIDT

/-! ## Lemmas on canonical lines -/

namespace Line

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m : ℕ}

end Line

namespace Bridge

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d : ℕ} [NeZero m]

/-! ## From projective measurement families to MIPStarRE measurements -/

/-- The measurement for the question `x` of a projective family on `ℂ^{n×n}`, as a
MIPStarRE projective measurement. -/
def toProjMeas {X A n : Type*} [Fintype A] [Fintype n] [DecidableEq n]
    (P : ProjectiveMeasurement X A (Matrix n n ℂ)) (x : X) : ProjMeas A n where
  outcome := P.M x
  total := 1
  outcome_pos a := by
    have h := Matrix.posSemidef_conjTranspose_mul_self (P.M x a)
    rw [← Matrix.star_eq_conjTranspose, P.selfAdjoint x a, P.projective x a] at h
    exact Matrix.nonneg_iff_posSemidef.mpr h
  sum_eq_total := P.normalized x
  total_le_one := le_rfl
  total_eq_one := rfl
  proj := P.projective x

@[simp] theorem toProjMeas_outcome {X A n : Type*} [Fintype A] [Fintype n] [DecidableEq n]
    (P : ProjectiveMeasurement X A (Matrix n n ℂ)) (x : X) (a : A) :
    (toProjMeas P x).outcome a = P.M x a := rfl

@[simp] theorem toProjMeas_total {X A n : Type*} [Fintype A] [Fintype n] [DecidableEq n]
    (P : ProjectiveMeasurement X A (Matrix n n ℂ)) (x : X) :
    (toProjMeas P x).total = 1 := rfl

/-! ## Affine reparametrization of line answers -/

/-- Substitute `b + c·X` into a univariate polynomial. -/
def affine (g : _root_.Polynomial F) (b c : F) : _root_.Polynomial F :=
  g.comp (_root_.Polynomial.C b + _root_.Polynomial.C c * _root_.Polynomial.X)

omit [Fintype F] [DecidableEq F] in
theorem natDegree_affine_le {g : _root_.Polynomial F} {k : ℕ} (hg : g.natDegree ≤ k)
    (b c : F) : (affine g b c).natDegree ≤ k := by
  refine _root_.Polynomial.natDegree_comp_le.trans ?_
  have h1 : (_root_.Polynomial.C b + _root_.Polynomial.C c * _root_.Polynomial.X).natDegree ≤ 1 :=
    (_root_.Polynomial.natDegree_add_le _ _).trans (max_le (by simp)
      ((_root_.Polynomial.natDegree_C_mul_le _ _).trans _root_.Polynomial.natDegree_X_le))
  calc g.natDegree * (_root_.Polynomial.C b + _root_.Polynomial.C c * _root_.Polynomial.X).natDegree
      ≤ k * 1 := Nat.mul_le_mul hg h1
    _ = k := mul_one k

omit [Fintype F] [DecidableEq F] in
@[simp] theorem eval_affine (g : _root_.Polynomial F) (b c t : F) :
    (affine g b c).eval t = g.eval (b + c * t) := by
  simp [affine, _root_.Polynomial.eval_comp]

/-- The univariate polynomial of degree `≤ d` answered to an axis-parallel line question
(`0` for ill-typed answers). -/
def axisPolyOf : Answer F m d → _root_.Polynomial F
  | .axisPoly c => ofCoeffs c
  | _ => 0

omit [Fintype F] [DecidableEq F] [NeZero m] in
theorem natDegree_axisPolyOf_le (a : Answer F m d) : (axisPolyOf a).natDegree ≤ d := by
  cases a <;> simp [axisPolyOf, natDegree_ofCoeffs_le]

/-- The univariate polynomial of degree `≤ m·d` answered to a diagonal line question
(`0` for ill-typed answers). -/
def diagPolyOf : Answer F m d → _root_.Polynomial F
  | .diagPoly c => ofCoeffs c
  | _ => 0

omit [Fintype F] [DecidableEq F] [NeZero m] in
theorem natDegree_diagPolyOf_le (a : Answer F m d) : (diagPolyOf a).natDegree ≤ m * d := by
  cases a <;> simp [diagPolyOf, natDegree_ofCoeffs_le]

/-- The axis-line answer, in the parameter `t` of a presentation whose base point has
parameter `b` on the canonical line (so that `s = b + t`), read from an answer of the
strategy at the canonical question. -/
def axisAnswer (b : F) (a : Answer F m d) : AxisLinePolynomial (lidtParams F m d) :=
  ⟨affine (axisPolyOf a) b 1, natDegree_affine_le (natDegree_axisPolyOf_le a) b 1⟩

/-- The diagonal-line answer, in the parameter `t` of a presentation related to the
canonical parameter by `s = b + c·t`, read from an answer of the strategy at the
canonical question. -/
def diagAnswer (b c : F) (a : Answer F m d) : DiagonalLinePolynomial (lidtParams F m d) :=
  ⟨affine (diagPolyOf a) b c, natDegree_affine_le (natDegree_diagPolyOf_le a) b c⟩

/-! ## Line measurement families -/

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The canonical line of an axis-parallel line presentation. -/
def axisCanon (ℓ : AxisParallelLine (lidtParams F m d)) : Line F m :=
  Line.through (decP ℓ.base) (Pi.single ℓ.direction 1)

/-- The parameter, on the canonical line, of the base point of an axis-parallel line
presentation. -/
def axisBase (ℓ : AxisParallelLine (lidtParams F m d)) : F := dec (ℓ.base ℓ.direction)

/-- The axis-parallel line measurement family induced by a strategy's measurement family. -/
def axisMeas (P : ProjectiveMeasurement (Question F m) (Answer F m d) (Matrix n n ℂ)) :
    IdxProjMeas (AxisParallelLine (lidtParams F m d)) (AxisLinePolynomial (lidtParams F m d)) n :=
  fun ℓ => (toProjMeas P (.axisLine (axisCanon ℓ))).postprocess (axisAnswer (axisBase ℓ))

/-- The canonical line of a diagonal line presentation. -/
def diagCanon (ℓ : DiagonalLine (lidtParams F m d)) : Line F m :=
  Line.through (decP ℓ.base) (decP ℓ.direction)

/-- The change of parameters `s = b + c·t` from a diagonal line presentation to its canonical
line: `b` is the pivot coordinate of the base point and `c` the pivot coordinate of the
direction (`(0, 0)` for a singleton line). -/
def diagData (ℓ : DiagonalLine (lidtParams F m d)) : F × F :=
  if h : ∃ j, decP ℓ.direction j ≠ 0 then
    (decP ℓ.base (Fin.find (fun j => decP ℓ.direction j ≠ 0) h),
      decP ℓ.direction (Fin.find (fun j => decP ℓ.direction j ≠ 0) h))
  else (0, 0)

/-- The diagonal line measurement family induced by a strategy's measurement family. -/
def diagMeas (P : ProjectiveMeasurement (Question F m) (Answer F m d) (Matrix n n ℂ)) :
    IdxProjMeas (DiagonalLine (lidtParams F m d)) (DiagonalLinePolynomial (lidtParams F m d)) n :=
  fun ℓ => (toProjMeas P (.diagLine (diagCanon ℓ))).postprocess
    (diagAnswer (diagData ℓ).1 (diagData ℓ).2)

/-! ## Point measurement families -/

/-- The coded value of an answer to a point question. -/
def codedValue (a : Answer F m d) : Fq (lidtParams F m d) := enc a.toValue

/-- The point measurement family induced by a strategy's measurement family. -/
def pointMeas (P : ProjectiveMeasurement (Question F m) (Answer F m d) (Matrix n n ℂ)) :
    IdxProjMeas (MIPStarRE.LDT.Point (lidtParams F m d)) (Fq (lidtParams F m d)) n :=
  fun u => (toProjMeas P (.point (decP u))).postprocess codedValue

end Bridge

end MIPRE.LIDT

end


