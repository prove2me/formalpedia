-- Prove2me | Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Test_Defs
-- name    : MIPRE_Background_LIDT_MIPStarRE_LDT_Test_Defs
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T02:18:59.507775+00:00
-- url     : https://prove2.me/theorems/ed19f8fb-681c-4d24-b41b-62dd202dfa04
-- title:
--   Definitions of Defs: Section 3 — Definitions Core definitions for the low individual degree test: evaluation families, matching mass,…
-- statement:
--   The definitions of the module `MIPRE.Background.LIDT.MIPStarRE.LDT.Test.Defs` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Section 3 — Definitions. Core definitions for the low individual degree test: evaluation families, matching mass, consistency defect, and test-passing predicates. All operator fields now use `Op ι` directly with a generic `Fintype` index `ι`.
--
--   The module is vendored read-only, with the authors' permission, from [LionSR/MIPStarRE](https://github.com/LionSR/MIPStarRE) (Sirui Lu and the MIPStarRE contributors, Apache 2.0; commit and upstream path in the file header) by `scripts/vendor-lidt.py`.
--
--   **Definitions** (28): `MIPStarRE.LDT.BipartiteSSCRel` (Bipartite strong self-consistency relation (paper's definition).); `MIPStarRE.LDT.CompletenessAtLeast` (Completeness statement for a submeasurement.); `MIPStarRE.LDT.ConsRel` (Consistency relation (bipartite, paper Definition 4.8).); `MIPStarRE.LDT.SDDOpRel` (State-dependent distance relation for raw operator families.); `MIPStarRE.LDT.SDDRel` (State-dependent distance relation.); `MIPStarRE.LDT.SSCRel` (Strong self-consistency relation.); `MIPStarRE.LDT.Test.polynomialEvaluationMeasurementFamily` (Namespace-compatible form of `polynomialEvaluationMeasurementFamily`.); `MIPStarRE.LDT.bipartiteConsError` (Averaged bipartite off-diagonal mass for consistency statements.); `MIPStarRE.LDT.bipartiteSSCError` (Averaged bipartite SSC defect.); `MIPStarRE.LDT.consError` (Averaged off-diagonal mass for consistency statements.); `MIPStarRE.LDT.evaluateAt` (Evaluate a polynomial-valued submeasurement at a point.); `MIPStarRE.LDT.evaluateFiberFamilyAtNextPoint` (Evaluate an indexed slice family at a point `(u, x)` in `F_q^{m+1}`.); `MIPStarRE.LDT.idxSubMeasMass` (Averaged total mass of an indexed submeasurement.); `MIPStarRE.LDT.polynomialEvaluationFamily` (View a global polynomial submeasurement as a point-indexed answer family.); `MIPStarRE.LDT.polynomialEvaluationMeasurementFamily` (View a global polynomial measurement as a point-indexed answer measurement family.); `MIPStarRE.LDT.qBipartiteConsDefect` (Bipartite questionwise consistency defect.); and 9 more.
--
--   **Embedded lemmas** (1): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `evaluateAt_postprocess_appendAtHeight_appendPoint`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Background.LIDT.MIPStarRE.LDT.Test.Defs` (`MIPRE/Background/LIDT/MIPStarRE/LDT/Test/Defs.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 18 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/LIDT/MIPStarRE/LDT/Test/Defs.lean

/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/Test/Defs.lean
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/MIPStarRE/LDT/Test/Defs.lean (definition bundle: declarations the uploaded statements rest on);
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
import Theorems.Thm_MIPStarRE_LDT_Polynomial_appendAtHeight_apply_appendPoint
import Theorems.Thm_MIPStarRE_LDT_SubMeas_postprocess_comp

attribute [simp] MIPStarRE.LDT.Polynomial.appendAtHeight_apply_appendPoint
attribute [simp] MIPStarRE.LDT.SubMeas.postprocess_comp

set_option backward.isDefEq.respectTransparency false

/-!
# Section 3 — Definitions

Core definitions for the low individual degree test: evaluation families,
matching mass, consistency defect, and test-passing predicates.

All operator fields now use `Op ι` directly with a generic `Fintype` index `ι`.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT

/-- Evaluate a polynomial-valued submeasurement at a point. -/
noncomputable def evaluateAt {ι : Type*} [Fintype ι] [DecidableEq ι]
    (params : Parameters) [FieldModel params.q] (u : Point params)
    (G : SubMeas (Polynomial params) ι) : SubMeas (Fq params) ι :=
  postprocess G (fun g => g u)

/-- Evaluation after adjoining an unused coordinate agrees with evaluation before
adjoining that coordinate. -/
@[simp] theorem evaluateAt_postprocess_appendAtHeight_appendPoint
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (params : Parameters) [FieldModel params.q]
    (G : SubMeas (Polynomial params) ι)
    (x : Fq params) (u : Point params) (y : Fq params) :
    evaluateAt params.next (appendPoint params u y)
        (postprocess G (fun g => Polynomial.appendAtHeight params g x)) =
      evaluateAt params u G := by
  unfold evaluateAt
  rw [SubMeas.postprocess_comp]
  congr
  funext g
  exact Polynomial.appendAtHeight_apply_appendPoint params g x u y

/-- View a global polynomial submeasurement as a point-indexed answer family. -/
noncomputable def polynomialEvaluationFamily {ι : Type*} [Fintype ι] [DecidableEq ι]
    (params : Parameters) [FieldModel params.q]
    (G : SubMeas (Polynomial params) ι) :
    IdxSubMeas (Point params) (Fq params) ι :=
  fun u => evaluateAt params u G

/-- View a global polynomial measurement as a point-indexed answer measurement family.

The submeasurement-valued `polynomialEvaluationFamily` is the form used by most
consistency statements.  The heterogeneous triangle step in the final theorem
uses complete measurements, so this version keeps the same postprocessing while
retaining the total-mass proof. -/
noncomputable def polynomialEvaluationMeasurementFamily
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (params : Parameters) [FieldModel params.q]
    (G : Measurement (Polynomial params) ι) :
    IdxMeas (Point params) (Fq params) ι :=
  fun u =>
    { toSubMeas := evaluateAt params u G.toSubMeas
      total_eq_one := G.total_eq_one }

namespace Test

/-- Namespace-compatible form of `polynomialEvaluationMeasurementFamily`.

This name is used by the two-space final-theorem route, where the surrounding
theorems live in the `Test` namespace. -/
noncomputable abbrev polynomialEvaluationMeasurementFamily
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (params : Parameters) [FieldModel params.q]
    (G : Measurement (Polynomial params) ι) :
    IdxMeas (Point params) (Fq params) ι :=
  MIPStarRE.LDT.polynomialEvaluationMeasurementFamily params G

end Test

/-- Evaluate an indexed slice family at a point `(u, x)` in `F_q^{m+1}`. -/
noncomputable def evaluateFiberFamilyAtNextPoint {ι : Type*} [Fintype ι] [DecidableEq ι]
    (params : Parameters) [FieldModel params.q]
    (G : IdxSubMeas (Fq params) (Polynomial params) ι) :
    IdxSubMeas (Point params.next) (Fq params) ι :=
  fun u => evaluateAt params (truncatePoint params u) (G (pointHeight params u))

/-- Questionwise matching mass `∑_a ⟨ψ, A_a B_a ψ⟩`, summed over outcomes. -/
noncomputable def qMatchMass {Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι) (A B : SubMeas Outcome ι) : Error :=
  ∑ a, ev ψ (A.outcome a * B.outcome a)

/-- Questionwise off-diagonal mass surrogate for consistency. -/
noncomputable def qConsDefect {Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι) (A B : SubMeas Outcome ι) : Error :=
  let totalOverlap := ev ψ (A.total * B.total)
  max 0 (totalOverlap - qMatchMass ψ A B)

/-- Questionwise squared-distance defect. -/
noncomputable def qSDDCore {Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι)
    (A B : Outcome → MIPStarRE.Quantum.Op ι) : Error :=
  ∑ a, ev ψ ((A a - B a)ᴴ * (A a - B a))

/-- Questionwise squared-distance defect. -/
noncomputable def qSDD {Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι) (A B : SubMeas Outcome ι) : Error :=
  qSDDCore ψ A.outcome B.outcome

/-- State-dependent distance for raw operator families.
Matches the paper's `≈_δ` for arbitrary matrix families.
This keeps the raw-family API separate while sharing the same core formula as
`qSDD`. -/
noncomputable def qSDDOp {Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι) (A B : OpFamily Outcome ι) : Error :=
  qSDDCore ψ A.outcome B.outcome

/-- Questionwise strong self-consistency defect. -/
noncomputable def qSSCDefect {Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι) (A : SubMeas Outcome ι) : Error :=
  let totalMass := ev ψ A.total
  let diagonalMass := ∑ a, ev ψ (A.outcome a * A.outcome a)
  max 0 (totalMass - diagonalMass)

/-- Averaged off-diagonal mass for consistency statements. -/
noncomputable def consError {Question Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι) (𝒟 : Distribution Question)
    (A B : IdxSubMeas Question Outcome ι) : Error :=
  avgOver 𝒟 (fun q => qConsDefect ψ (A q) (B q))

/-- Averaged squared distance for `≈_δ`. -/
noncomputable def sddError {Question Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι) (𝒟 : Distribution Question)
    (A B : IdxSubMeas Question Outcome ι) : Error :=
  avgOver 𝒟 (fun q => qSDD ψ (A q) (B q))

/-- Averaged squared distance for raw operator families. -/
noncomputable def sddErrorOp {Question Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι) (𝒟 : Distribution Question)
    (A B : IdxOpFamily Question Outcome ι) : Error :=
  avgOver 𝒟 (fun q => qSDDOp ψ (A q) (B q))

/-- Averaged defect in strong self-consistency. -/
noncomputable def sscError {Question Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι) (𝒟 : Distribution Question)
    (A : IdxSubMeas Question Outcome ι) : Error :=
  avgOver 𝒟 (fun q => qSSCDefect ψ (A q))

/-- Total mass of a submeasurement on state `ψ`, computed from the concrete total operator. -/
noncomputable def subMeasMass {Outcome : Type*} {ι : Type*}
    [Fintype Outcome] [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι) (A : SubMeas Outcome ι) : Error :=
  ev ψ A.total

/-- Averaged total mass of an indexed submeasurement. -/
noncomputable def idxSubMeasMass {Question Outcome : Type*} {ι : Type*}
    [Fintype Outcome] [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι) (𝒟 : Distribution Question)
    (A : IdxSubMeas Question Outcome ι) : Error :=
  avgOver 𝒟 (fun q => subMeasMass ψ (A q))

/-- Bipartite matching mass `∑_a ⟨ψ, (A_a ⊗ B_a) ψ⟩`, with `A` on the left
register and `B` on the right register of a tensor-product state. -/
noncomputable def qBipartiteMatchMass {Outcome : Type*}
    {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype Outcome]
    (ψ : QuantumState (ιA × ιB))
    (A : SubMeas Outcome ιA) (B : SubMeas Outcome ιB) : Error :=
  ∑ a, ev ψ (opTensor (A.outcome a) (B.outcome a))

/-- Bipartite questionwise consistency defect.

In the paper (Definition 4.8), the consistency of `A` on `H_A` and `B` on
`H_B` for a shared state `|ψ⟩ ∈ H_A ⊗ H_B` is:
  `E_x ∑_{a≠b} ⟨ψ| A^x_a ⊗ B^x_b |ψ⟩ ≤ δ`
which equals
  `max 0 (⟨ψ| A_total ⊗ B_total |ψ⟩ − ∑_a ⟨ψ| A_a ⊗ B_a |ψ⟩)`. -/
noncomputable def qBipartiteConsDefect {Outcome : Type*}
    {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype Outcome]
    (ψ : QuantumState (ιA × ιB))
    (A : SubMeas Outcome ιA) (B : SubMeas Outcome ιB) : Error :=
  let totalOverlap := ev ψ (opTensor A.total B.total)
  max 0 (totalOverlap - qBipartiteMatchMass ψ A B)

/-- Averaged bipartite off-diagonal mass for consistency statements. -/
noncomputable def bipartiteConsError {Question Outcome : Type*}
    {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype Outcome]
    (ψ : QuantumState (ιA × ιB)) (𝒟 : Distribution Question)
    (A : IdxSubMeas Question Outcome ιA)
    (B : IdxSubMeas Question Outcome ιB) : Error :=
  avgOver 𝒟 (fun q => qBipartiteConsDefect ψ (A q) (B q))

/-- Consistency relation (bipartite, paper Definition 4.8).

The state `ψ` lives on `H_A ⊗ H_B`, Alice's submeasurement `A` acts on
`H_A`, and Bob's submeasurement `B` acts on `H_B`. The relation encodes
  `E_{x ∼ D} ∑_{a≠b} ⟨ψ| A^x_a ⊗ B^x_b |ψ⟩ ≤ δ`. -/
structure ConsRel {Question Outcome : Type*}
    {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype Outcome]
    (ψ : QuantumState (ιA × ιB)) (𝒟 : Distribution Question)
    (A : IdxSubMeas Question Outcome ιA)
    (B : IdxSubMeas Question Outcome ιB)
    (δ : Error) : Prop where
  offDiagonalBound : bipartiteConsError ψ 𝒟 A B ≤ δ

/-- State-dependent distance relation. -/
structure SDDRel {Question Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι) (𝒟 : Distribution Question)
    (A B : IdxSubMeas Question Outcome ι) (δ : Error) : Prop where
  squaredDistanceBound : sddError ψ 𝒟 A B ≤ δ

/-- State-dependent distance relation for raw operator families. -/
structure SDDOpRel {Question Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι) (𝒟 : Distribution Question)
    (A B : IdxOpFamily Question Outcome ι) (δ : Error) : Prop where
  squaredDistanceBound : sddErrorOp ψ 𝒟 A B ≤ δ

/-- Strong self-consistency relation. -/
structure SSCRel {Question Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι) (𝒟 : Distribution Question)
    (A : IdxSubMeas Question Outcome ι) (δ : Error) : Prop where
  diagonalOverlapBound : sscError ψ 𝒟 A ≤ δ

/-- Bipartite questionwise strong self-consistency defect.
This is the paper's SSC condition (Definition 4.3/4.4):
  `max 0 (∑ₐ ev ψ (Aₐ ⊗ I) − ∑ₐ ev ψ (Aₐ ⊗ Aₐ))`.
It measures the gap between the total mass on one register and the
diagonal cross-register overlap. -/
noncomputable def qBipartiteSSCDefect
    {Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState (ι × ι)) (A : SubMeas Outcome ι) : Error :=
  let totalMass := ev ψ (leftTensor (ι₂ := ι) A.total)
  let overlapMass := ∑ a, ev ψ (opTensor (A.outcome a) (A.outcome a))
  max 0 (totalMass - overlapMass)

/-- Averaged bipartite SSC defect. -/
noncomputable def bipartiteSSCError
    {Question Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState (ι × ι)) (𝒟 : Distribution Question)
    (A : IdxSubMeas Question Outcome ι) : Error :=
  avgOver 𝒟 (fun q => qBipartiteSSCDefect ψ (A q))

/-- Bipartite strong self-consistency relation (paper's definition).
Uses the cross-register overlap `∑ₐ ev ψ (Aₐ ⊗ Aₐ)` rather than
the local square `∑ₐ ev ψ (Aₐ² ⊗ I)`. -/
structure BipartiteSSCRel
    {Question Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState (ι × ι)) (𝒟 : Distribution Question)
    (A : IdxSubMeas Question Outcome ι) (δ : Error) : Prop where
  overlapBound : bipartiteSSCError ψ 𝒟 A ≤ δ

/-- Completeness statement for a submeasurement. -/
structure CompletenessAtLeast {Outcome : Type*} {ι : Type*}
    [Fintype Outcome] [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι) (A : SubMeas Outcome ι) (r : Error) : Prop where
  lowerBound : subMeasMass ψ A ≥ r

/-! ### Nonnegativity lemmas for defect measures -/

/-! ### Postprocessing preserves totals -/

-- vendoring compile fix (Lean v4.33): the previous step may close the goal

/- The naive monotonicity statement
`qConsDefect ψ (postprocess A f) (postprocess B f) ≤ qConsDefect ψ A B`
is false for arbitrary submeasurements: without opposite-side / commuting
hypotheses, the extra cross terms created by postprocessing need not be
nonnegative. The paper's data-processing proposition is therefore recorded in
the bipartite form `Preliminaries.simeqDataProcessing`, not as a generic fact
about `qConsDefect`. -/

end MIPStarRE.LDT


