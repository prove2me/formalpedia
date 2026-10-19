-- Prove2me | Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Operators
-- name    : MIPRE_Background_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Operators
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T02:20:56.927153+00:00
-- url     : https://prove2.me/theorems/a6b2496b-d41f-4b49-b29e-bad93fda14f0
-- title:
--   Definitions of Operators: Weighted operators and variance families
-- statement:
--   The definitions of the module `MIPRE.Background.LIDT.MIPStarRE.LDT.GlobalVariance.Defs.Operators` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). ## Weighted operators and variance families
--
--   The module is vendored read-only, with the authors' permission, from [LionSR/MIPStarRE](https://github.com/LionSR/MIPStarRE) (Sirui Lu and the MIPStarRE contributors, Apache 2.0; commit and upstream path in the file header) by `scripts/vendor-lidt.py`.
--
--   **Definitions** (19): `MIPStarRE.LDT.GlobalVariance.generalizeBCollisionEventProjMeasAtPolynomial` (The residual projective `Option Unit` event from the proof of `lem:generalize-b`: axis-line answers that collide with `g` at the sampled…); `MIPStarRE.LDT.GlobalVariance.generalizeBCollisionEventSubMeasAtPolynomial` (The residual event above, forgetting projectivity to a submeasurement.); `MIPStarRE.LDT.GlobalVariance.generalizeBCollisionOperatorAtPolynomial` (The event operator for the residual line-collision event in `lem:generalize-b`.); `MIPStarRE.LDT.GlobalVariance.generalizeBLeftEventSubMeasAtPolynomial` (The `Option Unit` event submeasurement selecting axis-line answers that match `g(u)` at the queried point `u` on the left side of…); `MIPStarRE.LDT.GlobalVariance.generalizeBLeftOperatorAtPolynomial` (The event operator `B^ℓ_{[f(u)=g(u)]}`: sum of axis-line measurement outcomes `f` that evaluate to the same value as `g` at point `u`.); `MIPStarRE.LDT.GlobalVariance.generalizeBRightEventSubMeasAtPolynomial` (The `Option Unit` event submeasurement selecting axis-line answers that match the restriction of `g` to `ℓ` on the right side of…); `MIPStarRE.LDT.GlobalVariance.generalizeBRightOperatorAtPolynomial` (The event operator `B^ℓ_{[f = g|_ℓ]}`: sum of axis-line measurement outcomes `f` that agree with `g` restricted to line `ℓ`.); `MIPStarRE.LDT.GlobalVariance.pointConditionedEventSubMeasAtPolynomial` (The two-outcome point event selecting the answer `g(u)`.); and -8 more.
--
--   **Embedded lemmas** (1): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `pointConditionedEventSubMeasAtPolynomial_some`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Background.LIDT.MIPStarRE.LDT.GlobalVariance.Defs.Operators` (`MIPRE/Background/LIDT/MIPStarRE/LDT/GlobalVariance/Defs/Operators.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 24 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/LIDT/MIPStarRE/LDT/GlobalVariance/Defs/Operators.lean

/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/GlobalVariance/Defs/Operators.lean
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/MIPStarRE/LDT/GlobalVariance/Defs/Operators.lean (definition bundle: declarations the uploaded statements rest on);
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

set_option backward.isDefEq.respectTransparency false

namespace MIPStarRE.LDT.GlobalVariance

open MIPStarRE.LDT
open MIPStarRE.LDT.MakingMeasurementsProjective
open MIPStarRE.LDT.ExpansionHypercubeGraph
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (params : Parameters) [FieldModel params.q]

/-! ## Weighted operators and variance families -/

/-- The operator `(G_g)^{1/2}` used throughout `expansion.tex`.
Uses `CFC.sqrt` (continuous functional calculus) to compute the matrix
square root of the PSD operator `G.outcome g`. -/
noncomputable def polynomialWeightSqrtOperator (params : Parameters) [FieldModel params.q]
    (G : SubMeas (Polynomial params) ι) (g : Polynomial params) : MIPStarRE.Quantum.Op ι :=
  CFC.sqrt (G.outcome g)

/-- The weighted state `|ψ_g⟩ = (I ⊗ √G_g)|ψ⟩`, modeled as a density-matrix
transformation: `ρ_g = W_g ρ W_g†` where `W_g = I ⊗ √(G_g)`.

This is not necessarily normalized — normalization would require dividing by
`Tr(G_g ρ_B)`. We keep it unnormalized since the variance quantities in the
paper use unnormalized weighted expectations. -/
noncomputable def weightedPolynomialState (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι) (g : Polynomial params) :
    QuantumState (ι × ι) :=
  let sqrtG := polynomialWeightSqrtOperator params G g
  let W := rightTensor (ι₁ := ι) sqrtG
  { density := W * strategy.state.density * Wᴴ
    density_psd :=
      by
        simpa [Matrix.star_eq_conjTranspose] using
          star_right_conjugate_nonneg strategy.state.density_psd W }

/-- The concrete operator `A^u_{g(u)}` for a fixed polynomial `g`. -/
noncomputable def pointConditionedOutcomeOperatorAtPolynomial (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (g : Polynomial params) (u : Point params) : MIPStarRE.Quantum.Op ι :=
  (strategy.pointMeasurement u).toSubMeas.outcome (g u)

/-- The two-outcome point event selecting the answer `g(u)`.

This is the submeasurement form of the point operator used in the first and last
steps of `lem:local-variance-of-points` (`expansion.tex`, lines 305 and 311).
Its `some ()` outcome is exactly `A^u_{g(u)}`; the `none` outcome is the
complementary point-answer mass. -/
noncomputable def pointConditionedEventSubMeasAtPolynomial (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (g : Polynomial params) (u : Point params) : SubMeas (Option Unit) ι :=
  postprocess ((strategy.pointMeasurement u).toSubMeas)
    (fun a : Fq params => if a = g u then some () else none)

/-- The selected outcome of `pointConditionedEventSubMeasAtPolynomial` is
`A^u_{g(u)}`. -/
@[simp] lemma pointConditionedEventSubMeasAtPolynomial_some (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (g : Polynomial params) (u : Point params) :
    (pointConditionedEventSubMeasAtPolynomial params strategy g u).outcome (some ()) =
      pointConditionedOutcomeOperatorAtPolynomial params strategy g u := by
  classical
  unfold pointConditionedEventSubMeasAtPolynomial pointConditionedOutcomeOperatorAtPolynomial
  simp only [postprocess]
  refine Finset.sum_eq_single (g u) ?_ ?_
  · intro a ha hne
    simp [hne] at ha
  · simp

/-- The paper's weighted operator `A^u_{g(u)} ⊗ (G_g)^{1/2}`
on the bipartite space `d * d`. -/
noncomputable def weightedPointConditionedOperatorAtPolynomial (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι)
    (g : Polynomial params) (u : Point params) : MIPStarRE.Quantum.Op (ι × ι) :=
  opTensor
    (pointConditionedOutcomeOperatorAtPolynomial params strategy g u)
    (polynomialWeightSqrtOperator params G g)

/-- The right-register intermediate `I ⊗ (G_g)^{1/2} A^u_{g(u)}`
from the first and last self-consistency moves of
`lem:local-variance-of-points` (`expansion.tex`, lines 306 and 310). -/
noncomputable def weightedPointConditionedRightOperatorAtPolynomial (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι)
    (g : Polynomial params) (u : Point params) : MIPStarRE.Quantum.Op (ι × ι) :=
  rightTensor (ι₁ := ι)
    (polynomialWeightSqrtOperator params G g *
      pointConditionedOutcomeOperatorAtPolynomial params strategy g u)

/-- The local variance of `A(g)` on the weighted state `|ψ_g⟩`.
Operators are lifted to the left tensor factor of the bipartite state. -/
noncomputable def pointConditionedLocalVarianceAtPolynomial (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι)
    (g : Polynomial params) : Error :=
  localVariance params
    (fun u => leftTensor (ι₂ := ι)
      (pointConditionedOutcomeOperatorAtPolynomial params strategy g u))
    (weightedPolynomialState params strategy G g)

/-- The global variance of `A(g)` on the weighted state `|ψ_g⟩`.
Operators are lifted to the left tensor factor of the bipartite state. -/
noncomputable def pointConditionedGlobalVarianceAtPolynomial (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι)
    (g : Polynomial params) : Error :=
  globalVariance params
    (fun u => leftTensor (ι₂ := ι)
      (pointConditionedOutcomeOperatorAtPolynomial params strategy g u))
    (weightedPolynomialState params strategy G g)

/-- The polynomial-averaged local variance of the conditioned points family. -/
noncomputable def pointConditionedLocalVariance (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι) : Error :=
  avgOver (polynomialDistribution params)
    (fun g => pointConditionedLocalVarianceAtPolynomial params strategy G g)

/-- The polynomial-averaged global variance of the conditioned points family. -/
noncomputable def pointConditionedGlobalVariance (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι) : Error :=
  avgOver (polynomialDistribution params)
    (fun g => pointConditionedGlobalVarianceAtPolynomial params strategy G g)

/-- The `Option Unit` event submeasurement selecting axis-line answers that
match `g(u)` at the queried point `u` on the left side of `lem:generalize-b`. -/
noncomputable def generalizeBLeftEventSubMeasAtPolynomial (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (g : Polynomial params)
    (qu : AxisParallelLineQuestion params) : SubMeas (Option Unit) ι :=
  let (ℓ, u) := qu
  postprocess
    ((strategy.axisParallelMeasurement ℓ).toSubMeas)
    (fun f : AxisLinePolynomial params =>
      if f (axisParallelLineQuestionParameter qu) = g u then
        some ()
      else
        none)

/-- The `Option Unit` event submeasurement selecting axis-line answers that
match the restriction of `g` to `ℓ` on the right side of `lem:generalize-b`. -/
noncomputable def generalizeBRightEventSubMeasAtPolynomial (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (g : Polynomial params)
    (qu : AxisParallelLineQuestion params) : SubMeas (Option Unit) ι :=
  let ℓ := qu.1
  let gRestricted := Polynomial.restrictToAxisParallelLine params g ℓ
  postprocess
    ((strategy.axisParallelMeasurement ℓ).toSubMeas)
    (fun f : AxisLinePolynomial params =>
      if f.poly = gRestricted.poly then
        some ()
      else
        none)

/-- The residual projective `Option Unit` event from the proof of
`lem:generalize-b`: axis-line answers that collide with `g` at the sampled point
`u`, but are not the restricted polynomial `g|_ℓ`.  After the
projective-measurement expansion, the squared difference is controlled by this
collision event. -/
noncomputable def generalizeBCollisionEventProjMeasAtPolynomial (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (g : Polynomial params)
    (qu : AxisParallelLineQuestion params) : ProjMeas (Option Unit) ι :=
  let (ℓ, u) := qu
  let gRestricted := Polynomial.restrictToAxisParallelLine params g ℓ
  ProjMeas.postprocess (strategy.axisParallelMeasurement ℓ)
    (fun f : AxisLinePolynomial params =>
      if f (axisParallelLineQuestionParameter qu) = g u ∧ f.poly ≠ gRestricted.poly then
        some ()
      else
        none)

/-- The residual event above, forgetting projectivity to a submeasurement.  Keeping
this definition as the `toSubMeas` of `generalizeBCollisionEventProjMeasAtPolynomial`
prevents the projective and submeasurement views from drifting apart. -/
noncomputable def generalizeBCollisionEventSubMeasAtPolynomial (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (g : Polynomial params)
    (qu : AxisParallelLineQuestion params) : SubMeas (Option Unit) ι :=
  (generalizeBCollisionEventProjMeasAtPolynomial params strategy g qu).toSubMeas

/-- The event operator for the residual line-collision event in `lem:generalize-b`. -/
noncomputable def generalizeBCollisionOperatorAtPolynomial (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (g : Polynomial params)
    (qu : AxisParallelLineQuestion params) : MIPStarRE.Quantum.Op ι :=
  (generalizeBCollisionEventSubMeasAtPolynomial params strategy g qu).outcome (some ())

/-- The event operator `B^ℓ_{[f(u)=g(u)]}`: sum of axis-line measurement
outcomes `f` that evaluate to the same value as `g` at point `u`. -/
noncomputable def generalizeBLeftOperatorAtPolynomial (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (g : Polynomial params)
    (qu : AxisParallelLineQuestion params) : MIPStarRE.Quantum.Op ι :=
  (generalizeBLeftEventSubMeasAtPolynomial params strategy g qu).outcome (some ())

/-- The event operator `B^ℓ_{[f = g|_ℓ]}`: sum of axis-line measurement
outcomes `f` that agree with `g` restricted to line `ℓ`. -/
noncomputable def generalizeBRightOperatorAtPolynomial (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (g : Polynomial params)
    (qu : AxisParallelLineQuestion params) : MIPStarRE.Quantum.Op ι :=
  (generalizeBRightEventSubMeasAtPolynomial params strategy g qu).outcome (some ())

/-- The weighted left operator in `lem:generalize-b`
on the bipartite space `d * d`. -/
noncomputable def weightedGeneralizeBLeftOperatorAtPolynomial (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι)
    (g : Polynomial params)
    (qu : AxisParallelLineQuestion params) : MIPStarRE.Quantum.Op (ι × ι) :=
  opTensor
    (generalizeBLeftOperatorAtPolynomial params strategy g qu)
    (polynomialWeightSqrtOperator params G g)

/-- The weighted right operator in `lem:generalize-b`
on the bipartite space `d * d`. -/
noncomputable def weightedGeneralizeBRightOperatorAtPolynomial (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι)
    (g : Polynomial params)
    (qu : AxisParallelLineQuestion params) : MIPStarRE.Quantum.Op (ι × ι) :=
  opTensor
    (generalizeBRightOperatorAtPolynomial params strategy g qu)
    (polynomialWeightSqrtOperator params G g)

end MIPStarRE.LDT.GlobalVariance


