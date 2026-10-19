-- Prove2me | Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_SpectralTruncation_ProjectiveNonMeasurement
-- name    : MIPRE_Background_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_SpectralTruncation_ProjectiveNonMeasurement
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T03:51:18.367263+00:00
-- url     : https://prove2.me/theorems/267c287a-8d1c-42e8-9a02-aaf0b6fa627b
-- title:
--   Definitions of ProjectiveNonMeasurement: Section 5 — Projective Non-Measurement from Spectral Truncation This file proves the constructive spectral-truncation…
-- statement:
--   The definitions of the module `MIPRE.Background.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.SpectralTruncation.ProjectiveNonMeasurement` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Section 5 — Projective Non-Measurement from Spectral Truncation. This file proves the constructive spectral-truncation form of the paper witness `lem:projective-non-measurement`. The rounded projective family is obtained by functional calculus, using the threshold `1 - sqrt ζ` in the nontrivial regime and the zero family in the large-error regime.
--
--   The module is vendored read-only, with the authors' permission, from [LionSR/MIPStarRE](https://github.com/LionSR/MIPStarRE) (Sirui Lu and the MIPStarRE contributors, Apache 2.0; commit and upstream path in the file header) by `scripts/vendor-lidt.py`.
--
--   **Definitions** (2): `_private.MIPRE.Background.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.SpectralTruncation.ProjectiveNonMeasurement.0.MIPStarRE.LDT.MakingMeasurementsProjective.roundedProjectorFamily`; `_private.MIPRE.Background.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.SpectralTruncation.ProjectiveNonMeasurement.0.MIPStarRE.LDT.MakingMeasurementsProjective.truncationCutoff`.
--
--   **Embedded lemmas** (11): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `continuousOn_outcome_spectrum`, `outcome_spectrum_le_one`, `outcome_spectrum_nonneg`, `roundedProjectorFamily_closeness`, `roundedProjectorFamily_outcome_le_scale`, `roundedProjectorFamily_outcome_qSDD_bound`, `roundedProjectorFamily_projective`, `roundedProjectorFamily_total_le_one_zero`, `roundedProjectorFamily_total_le_scale`, `sourceAlmostProjective_eq_zero_per_outcome`, ….
--
--   **Formalization Note** The bundle is the module `MIPRE.Background.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.SpectralTruncation.ProjectiveNonMeasurement` (`MIPRE/Background/LIDT/MIPStarRE/LDT/MakingMeasurementsProjective/SpectralTruncation/ProjectiveNonMeasurement.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 35 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/LIDT/MIPStarRE/LDT/MakingMeasurementsProjective/SpectralTruncation/ProjectiveNonMeasurement.lean

/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/MakingMeasurementsProjective/SpectralTruncation/ProjectiveNonMeasurement.lean
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/MIPStarRE/LDT/MakingMeasurementsProjective/SpectralTruncation/ProjectiveNonMeasurement.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.Algebra.Hom
import Mathlib.Algebra.Algebra.NonUnitalHom
import Mathlib.Algebra.Algebra.Spectrum.Basic
import Mathlib.Algebra.Algebra.Spectrum.Quasispectrum
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
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
import Mathlib.Algebra.Group.Idempotent
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
import Mathlib.Algebra.GroupWithZero.Units.Lemmas
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
import Mathlib.Algebra.Order.Group.Abs
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
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unital
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
import Mathlib.Analysis.Matrix.Spectrum
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
import Mathlib.Data.Finite.Prod
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
import Mathlib.Data.Set.Finite.Range
import Mathlib.Data.Set.Operations
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
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Logic.Basic
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Equiv.Prod
import Mathlib.Logic.Function.Defs
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
import Mathlib.Tactic.Linarith.Preprocessing
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.NormNum.RealSqrt
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
import Mathlib.Topology.ContinuousMap.ContinuousSqrt
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.Defs.Basic
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.EMetricSpace.Defs
import Mathlib.Topology.GDelta.MetrizableSpace
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Defs
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Metrizable.Uniformity
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.Real
import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.Separation.GDelta
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Separation.Regular
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
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Statements
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_MeasurementLift
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_Defs
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_ComparisonCore
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_DistanceBounds
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_ConsistencyBridges
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_InnerProduct
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichMain_Completeness
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Core
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_CauchySchwarz
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Projectivization
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_QXPLayer_Core
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_CompletionTransfer
import Theorems.Thm_MIPStarRE_LDT_MakingMeasurementsProjective_sourceAlmostProjective_nonneg
import Theorems.Thm_MIPStarRE_LDT_MakingMeasurementsProjective_truncationInequality
import Theorems.Thm_MIPStarRE_LDT_Measurement_outcome_hermitian
import Theorems.Thm_MIPStarRE_LDT_Measurement_outcome_le_one
import Theorems.Thm_MIPStarRE_LDT_ev_mono
import Theorems.Thm_MIPStarRE_LDT_ev_scale
import Theorems.Thm_MIPStarRE_Quantum_sq_le_self

set_option backward.isDefEq.respectTransparency false

/-!
# Section 5 — Projective Non-Measurement from Spectral Truncation

This file proves the constructive spectral-truncation form of the paper witness
`lem:projective-non-measurement`.  The rounded projective family is obtained by
functional calculus, using the threshold `1 - sqrt ζ` in the nontrivial regime
and the zero family in the large-error regime.

## References

- `references/ldt-paper/orthonormalization.tex` (lines 420-550)
- Blueprint: Chapter 4 (`blueprint/src/chapter/ch04_projective.tex`)
- Related downstream applications: #422 (mainFormal), #834 (Step 6)
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT.MakingMeasurementsProjective

open MIPStarRE.LDT

universe uOutcome uι

noncomputable def truncationCutoff (δ : Error) : Error → Error :=
  fun x => if 1 - δ ≤ x then 1 else 0

lemma truncationCutoff_le_inv_one_sub_mul
    (δ x : Error) (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2) (hx0 : 0 ≤ x) :
    truncationCutoff δ x ≤ (1 / (1 - δ)) * x := by
  by_cases h : 1 - δ ≤ x
  · have hden : 0 < 1 - δ := by linarith
    simp [truncationCutoff, h]
    have hdiv : 1 ≤ x / (1 - δ) := by
      rw [le_div_iff₀ hden]
      linarith
    simpa [div_eq_mul_inv, mul_comm] using hdiv
  · have hden : 0 < 1 - δ := by linarith
    have hfac : 0 ≤ (1 - δ)⁻¹ := by positivity
    have hmul : 0 ≤ (1 - δ)⁻¹ * x := mul_nonneg hfac hx0
    simpa [truncationCutoff, h] using hmul

lemma continuousOn_outcome_spectrum {Outcome : Type uOutcome}
    [Fintype Outcome]
    {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (A : Measurement Outcome ι) (a : Outcome) (f : Error → Error) :
    ContinuousOn f (spectrum ℝ (A.outcome a)) := by
  classical
  have hherm : (A.outcome a).IsHermitian := A.outcome_hermitian a
  have hs : (spectrum ℝ (A.outcome a)).Finite := by
    rw [hherm.spectrum_real_eq_range_eigenvalues]
    exact Set.finite_range _
  exact hs.continuousOn _

noncomputable def roundedProjectorFamily {Outcome : Type uOutcome}
    [Fintype Outcome] [DecidableEq Outcome]
    {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (A : Measurement Outcome ι) (δ : Error) : OpFamily Outcome ι where
  outcome := fun a => cfc (truncationCutoff δ) (A.outcome a)
  total := ∑ a, cfc (truncationCutoff δ) (A.outcome a)

lemma outcome_spectrum_nonneg {Outcome : Type uOutcome}
    [Fintype Outcome]
    {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (A : Measurement Outcome ι) (a : Outcome) :
    ∀ x ∈ spectrum ℝ (A.outcome a), 0 ≤ x := by
  have hherm : (A.outcome a).IsHermitian := A.outcome_hermitian a
  have hsa : IsSelfAdjoint (A.outcome a) := hherm.isSelfAdjoint
  have hnonneg : 0 ≤ cfc (id : Error → Error) (A.outcome a) := by
    simpa [cfc_id ℝ (A.outcome a) (ha := hsa)] using A.outcome_pos a
  exact (cfc_nonneg_iff (R := ℝ) (f := id) (a := A.outcome a) (ha := hsa)).mp hnonneg

lemma outcome_spectrum_le_one {Outcome : Type uOutcome}
    [Fintype Outcome]
    {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (A : Measurement Outcome ι) (a : Outcome) :
    ∀ x ∈ spectrum ℝ (A.outcome a), x ≤ 1 := by
  have hherm : (A.outcome a).IsHermitian := A.outcome_hermitian a
  have hsa : IsSelfAdjoint (A.outcome a) := hherm.isSelfAdjoint
  have hle : cfc (id : Error → Error) (A.outcome a) ≤ 1 := by
    simpa [cfc_id ℝ (A.outcome a) (ha := hsa)] using A.outcome_le_one a
  exact (cfc_le_one_iff (f := id) (a := A.outcome a) (ha := hsa)).mp hle

lemma roundedProjectorFamily_projective {Outcome : Type uOutcome}
    [Fintype Outcome] [DecidableEq Outcome]
    {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (A : Measurement Outcome ι) (δ : Error) (a : Outcome) :
    MIPStarRE.Quantum.IsProj ((roundedProjectorFamily A δ).outcome a) := by
  refine { isIdempotentElem := ?_, isSelfAdjoint := ?_ }
  · change cfc (truncationCutoff δ) (A.outcome a) * cfc (truncationCutoff δ) (A.outcome a) =
      cfc (truncationCutoff δ) (A.outcome a)
    calc
      cfc (truncationCutoff δ) (A.outcome a) * cfc (truncationCutoff δ) (A.outcome a)
          = cfc (fun x => truncationCutoff δ x * truncationCutoff δ x) (A.outcome a) := by
              symm
              exact cfc_mul (R := ℝ) (truncationCutoff δ) (truncationCutoff δ) (A.outcome a)
                (hf := continuousOn_outcome_spectrum A a (truncationCutoff δ))
                (hg := continuousOn_outcome_spectrum A a (truncationCutoff δ))
      _ = cfc (truncationCutoff δ) (A.outcome a) := by
            apply cfc_congr
            intro x _hx
            by_cases h : 1 - δ ≤ x <;> simp [truncationCutoff, h]
  · exact cfc_predicate (R := ℝ) (truncationCutoff δ) (A.outcome a)

lemma roundedProjectorFamily_outcome_le_scale {Outcome : Type uOutcome}
    [Fintype Outcome] [DecidableEq Outcome]
    {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (A : Measurement Outcome ι) (δ : Error) (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2)
    (a : Outcome) :
    (roundedProjectorFamily A δ).outcome a ≤
      (((1 / (1 - δ)) : Error) : ℂ) • A.outcome a := by
  have hsa : IsSelfAdjoint (A.outcome a) :=
    (show (A.outcome a).IsHermitian from A.outcome_hermitian a).isSelfAdjoint
  have hmono :
      cfc (truncationCutoff δ) (A.outcome a) ≤
        cfc (fun x => (1 / (1 - δ)) * x) (A.outcome a) := by
    apply cfc_mono (R := ℝ) (a := A.outcome a)
      (hf := continuousOn_outcome_spectrum A a (truncationCutoff δ))
    intro x hx
    exact truncationCutoff_le_inv_one_sub_mul δ x hδ hδhalf
      (outcome_spectrum_nonneg A a x hx)
  calc
    (roundedProjectorFamily A δ).outcome a = cfc (truncationCutoff δ) (A.outcome a) := rfl
    _ ≤ cfc (fun x => (1 / (1 - δ)) * x) (A.outcome a) := hmono
    _ = (((1 / (1 - δ)) : Error) : ℂ) • A.outcome a := by
          simpa [RCLike.real_smul_eq_coe_smul (K := ℂ)] using
            (cfc_const_mul_id (R := ℝ) ((1 / (1 - δ)) : Error) (A.outcome a)
              (ha := hsa))

lemma roundedProjectorFamily_total_le_scale {Outcome : Type uOutcome}
    [Fintype Outcome] [DecidableEq Outcome]
    {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (A : Measurement Outcome ι) (δ : Error) (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2) :
    (roundedProjectorFamily A δ).total ≤
      (((1 / (1 - δ)) : Error) : ℂ) • (1 : MIPStarRE.Quantum.Op ι) := by
  calc
    (roundedProjectorFamily A δ).total
      = ∑ a, (roundedProjectorFamily A δ).outcome a := by rfl
    _ ≤ ∑ a, (((1 / (1 - δ)) : Error) : ℂ) • A.outcome a := by
          refine Finset.sum_le_sum ?_
          intro a _
          exact roundedProjectorFamily_outcome_le_scale A δ hδ hδhalf a
    _ = (((1 / (1 - δ)) : Error) : ℂ) • ∑ a, A.outcome a := by
          rw [Finset.smul_sum]
    _ = (((1 / (1 - δ)) : Error) : ℂ) • (1 : MIPStarRE.Quantum.Op ι) := by
          simp [A.sum_eq_total, A.total_eq_one]

lemma roundedProjectorFamily_outcome_qSDD_bound {Outcome : Type uOutcome}
    [Fintype Outcome] [DecidableEq Outcome]
    {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι) (A : Measurement Outcome ι) (δ : Error)
    (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2) (a : Outcome) :
    ev ψ (((A.outcome a - (roundedProjectorFamily A δ).outcome a)ᴴ) *
        (A.outcome a - (roundedProjectorFamily A δ).outcome a)) ≤
      (1 / δ) * ev ψ (A.outcome a - A.outcome a * A.outcome a) := by
  have hsa : IsSelfAdjoint (A.outcome a) :=
    (show (A.outcome a).IsHermitian from A.outcome_hermitian a).isSelfAdjoint
  have hmono :
      cfc (fun x => (x - truncationCutoff δ x) ^ (2 : Nat)) (A.outcome a) ≤
        cfc (fun x : Error => (1 / δ) * (x - x ^ (2 : Nat))) (A.outcome a) := by
    apply cfc_mono (R := ℝ) (a := A.outcome a)
      (hf := continuousOn_outcome_spectrum A a (fun x => (x - truncationCutoff δ x) ^ (2 : Nat)))
      (hg := continuousOn_outcome_spectrum A a (fun x : Error => (1 / δ) * (x - x ^ (2 : Nat))))
    intro x hx
    simpa [truncationCutoff, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      truncationInequality δ x hδ hδhalf
        (outcome_spectrum_nonneg A a x hx)
        (outcome_spectrum_le_one A a x hx)
  have hleft :
      cfc (fun x => (x - truncationCutoff δ x) ^ (2 : Nat)) (A.outcome a) =
        (A.outcome a - (roundedProjectorFamily A δ).outcome a) *
          (A.outcome a - (roundedProjectorFamily A δ).outcome a) := by
    have hid : cfc (R := ℝ) (id : Error → Error) (A.outcome a) = A.outcome a := by
      change cfc (fun x : Error => x) (A.outcome a) = A.outcome a
      exact cfc_id' ℝ (A.outcome a) (ha := hsa)
    have hsub :
        cfc (fun x => x - truncationCutoff δ x) (A.outcome a) =
          A.outcome a - cfc (truncationCutoff δ) (A.outcome a) := by
      calc
        cfc (fun x => x - truncationCutoff δ x) (A.outcome a)
          = cfc (R := ℝ) (id : Error → Error) (A.outcome a) -
              cfc (truncationCutoff δ) (A.outcome a) := by
              simpa using
                (cfc_sub (R := ℝ) (f := id) (g := truncationCutoff δ) (a := A.outcome a)
                  (hf := continuousOn_outcome_spectrum A a id)
                  (hg := continuousOn_outcome_spectrum A a (truncationCutoff δ)))
        _ = A.outcome a - cfc (truncationCutoff δ) (A.outcome a) := by
              rw [hid]
    calc
      cfc (fun x => (x - truncationCutoff δ x) ^ (2 : Nat)) (A.outcome a)
        = cfc (fun x => x - truncationCutoff δ x) (A.outcome a) ^ 2 := by
            exact cfc_pow (R := ℝ) (fun x => x - truncationCutoff δ x) 2 (A.outcome a)
              (hf := continuousOn_outcome_spectrum A a (fun x => x - truncationCutoff δ x))
              (ha := hsa)
      _ = (A.outcome a - cfc (truncationCutoff δ) (A.outcome a)) ^ 2 := by
            rw [hsub]
      _ = (A.outcome a - (roundedProjectorFamily A δ).outcome a) *
            (A.outcome a - (roundedProjectorFamily A δ).outcome a) := by
            simp [roundedProjectorFamily, pow_two]
  have hright :
      cfc (fun x => (1 / δ) * (x - x ^ (2 : Nat))) (A.outcome a) =
        (((1 / δ) : Error) : ℂ) • (A.outcome a - A.outcome a * A.outcome a) := by
    have hid : cfc (R := ℝ) (id : Error → Error) (A.outcome a) = A.outcome a := by
      change cfc (fun x : Error => x) (A.outcome a) = A.outcome a
      exact cfc_id' ℝ (A.outcome a) (ha := hsa)
    have hsub :
        cfc (fun x : Error => x - x ^ (2 : Nat)) (A.outcome a) =
          A.outcome a - A.outcome a * A.outcome a := by
      calc
        cfc (fun x : Error => x - x ^ (2 : Nat)) (A.outcome a)
          = cfc (R := ℝ) (id : Error → Error) (A.outcome a) -
              cfc (fun x : Error => x ^ (2 : Nat)) (A.outcome a) := by
              simpa using
                (cfc_sub (R := ℝ) (f := id) (g := fun x : Error => x ^ (2 : Nat))
                  (a := A.outcome a)
                  (hf := continuousOn_outcome_spectrum A a id)
                  (hg := continuousOn_outcome_spectrum A a (fun x : Error => x ^ (2 : Nat))))
        _ = A.outcome a - cfc (fun x : Error => x ^ (2 : Nat)) (A.outcome a) := by
              rw [hid]
        _ = A.outcome a - A.outcome a * A.outcome a := by
              rw [cfc_pow_id (R := ℝ) (A.outcome a) 2 (ha := hsa)]
              simp [pow_two]
    calc
      cfc (fun x : Error => (1 / δ) * (x - x ^ (2 : Nat))) (A.outcome a)
        = (1 / δ : Error) • cfc (fun x : Error => x - x ^ (2 : Nat)) (A.outcome a) := by
            exact cfc_const_mul (R := ℝ) (1 / δ : Error) (fun x : Error => x - x ^ (2 : Nat))
              (A.outcome a)
              (hf := continuousOn_outcome_spectrum A a (fun x : Error => x - x ^ (2 : Nat)))
      _ = (((1 / δ) : Error) : ℂ) • (A.outcome a - A.outcome a * A.outcome a) := by
            rw [hsub]
            simp [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  have hdiff_herm :
      (A.outcome a - (roundedProjectorFamily A δ).outcome a).IsHermitian := by
    exact (show (A.outcome a).IsHermitian from A.outcome_hermitian a).sub
      (roundedProjectorFamily_projective A δ a).isSelfAdjoint.isHermitian
  have hmain :
      (A.outcome a - (roundedProjectorFamily A δ).outcome a) *
          (A.outcome a - (roundedProjectorFamily A δ).outcome a) ≤
        (((1 / δ) : Error) : ℂ) • (A.outcome a - A.outcome a * A.outcome a) := by
    rw [← hleft, ← hright]
    exact hmono
  calc
    ev ψ (((A.outcome a - (roundedProjectorFamily A δ).outcome a)ᴴ) *
        (A.outcome a - (roundedProjectorFamily A δ).outcome a))
      = ev ψ ((A.outcome a - (roundedProjectorFamily A δ).outcome a) *
          (A.outcome a - (roundedProjectorFamily A δ).outcome a)) := by
            simp [hdiff_herm.eq]
    _ ≤ ev ψ ((((1 / δ) : Error) : ℂ) • (A.outcome a - A.outcome a * A.outcome a)) :=
          ev_mono ψ _ _ hmain
    _ = (1 / δ) * ev ψ (A.outcome a - A.outcome a * A.outcome a) := by
          simpa using ev_scale ψ (1 / δ) (A.outcome a - A.outcome a * A.outcome a)

lemma roundedProjectorFamily_closeness {Outcome : Type uOutcome}
    [Fintype Outcome] [DecidableEq Outcome]
    {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι) (A : Measurement Outcome ι) (ζ δ : Error)
    (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2)
    (hsource : ∑ a, ev ψ (A.outcome a - A.outcome a * A.outcome a) ≤ ζ) :
    SDDOpRel ψ (uniformDistribution Unit)
      (constOpFamily (A.toSubMeas : OpFamily Outcome ι))
      (constOpFamily (roundedProjectorFamily A δ))
      ((1 / δ) * ζ) := by
  constructor
  have hq :
      qSDDOp ψ (A.toSubMeas : OpFamily Outcome ι)
          (roundedProjectorFamily A δ) ≤
        (1 / δ) * ζ := by
    unfold qSDDOp qSDDCore
    calc
      ∑ a : Outcome,
          ev ψ (((A.toSubMeas.outcome a - (roundedProjectorFamily A δ).outcome a)ᴴ) *
            (A.toSubMeas.outcome a - (roundedProjectorFamily A δ).outcome a))
        ≤ ∑ a : Outcome, (1 / δ) * ev ψ (A.outcome a - A.outcome a * A.outcome a) := by
            refine Finset.sum_le_sum ?_
            intro a _
            simpa using roundedProjectorFamily_outcome_qSDD_bound ψ A δ hδ hδhalf a
      _ = (1 / δ) * ∑ a : Outcome, ev ψ (A.outcome a - A.outcome a * A.outcome a) := by
            rw [← Finset.mul_sum]
      _ ≤ (1 / δ) * ζ := by
            have hδinv_nonneg : 0 ≤ 1 / δ := by positivity
            exact mul_le_mul_of_nonneg_left hsource hδinv_nonneg
  simpa [sddErrorOp, avgOver, uniformDistribution, constOpFamily] using hq

lemma roundedProjectorFamily_total_le_one_zero {Outcome : Type uOutcome}
    [Fintype Outcome] [DecidableEq Outcome]
    {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (A : Measurement Outcome ι) :
    (roundedProjectorFamily A 0).total ≤ (1 : MIPStarRE.Quantum.Op ι) := by
  have houtcome_le :
      ∀ a : Outcome, (roundedProjectorFamily A 0).outcome a ≤ A.outcome a := by
    intro a
    have hmono :
        cfc (truncationCutoff 0) (A.outcome a) ≤
          cfc (R := ℝ) (id : Error → Error) (A.outcome a) := by
      apply cfc_mono (R := ℝ) (a := A.outcome a)
        (f := truncationCutoff 0) (g := id)
        (hf := continuousOn_outcome_spectrum A a (truncationCutoff 0))
        (hg := continuousOn_outcome_spectrum A a id)
      intro x hx
      have hx0 := outcome_spectrum_nonneg A a x hx
      have hx1 := outcome_spectrum_le_one A a x hx
      by_cases h : 1 ≤ x
      · have hx_eq : x = 1 := le_antisymm hx1 h
        simp [truncationCutoff, hx_eq]
      · simp [truncationCutoff, h, hx0]
    calc
      (roundedProjectorFamily A 0).outcome a = cfc (truncationCutoff 0) (A.outcome a) := rfl
      _ ≤ cfc (R := ℝ) (id : Error → Error) (A.outcome a) := hmono
      _ = A.outcome a := cfc_id' ℝ (A.outcome a)
        (ha := (show IsSelfAdjoint (A.outcome a) from
          (show (A.outcome a).IsHermitian from A.outcome_hermitian a).isSelfAdjoint))
  calc
    (roundedProjectorFamily A 0).total = ∑ a, (roundedProjectorFamily A 0).outcome a := by rfl
    _ ≤ ∑ a, A.outcome a := by
          refine Finset.sum_le_sum ?_
          intro a _
          exact houtcome_le a
    _ = 1 := by simpa [A.sum_eq_total] using A.total_eq_one

lemma sourceAlmostProjective_eq_zero_per_outcome {Outcome : Type uOutcome}
    [Fintype Outcome]
    {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι) (A : Measurement Outcome ι)
    (hsource : ∑ a, ev ψ (A.outcome a - A.outcome a * A.outcome a) ≤ 0) :
    ∀ a : Outcome, ev ψ (A.outcome a - A.outcome a * A.outcome a) = 0 := by
  classical
  have hsum_nonneg :
      0 ≤ ∑ a, ev ψ (A.outcome a - A.outcome a * A.outcome a) :=
    sourceAlmostProjective_nonneg ψ A
  have hsum_zero :
      ∑ a, ev ψ (A.outcome a - A.outcome a * A.outcome a) = 0 :=
    le_antisymm hsource hsum_nonneg
  have hterms := (Finset.sum_eq_zero_iff_of_nonneg fun a _ =>
      ev_nonneg_of_psd ψ _ <|
        sub_nonneg.mpr <|
          MIPStarRE.Quantum.sq_le_self (A.outcome_pos a) (A.outcome_le_one a)).mp hsum_zero
  intro a
  exact hterms a (by simp)

end MIPStarRE.LDT.MakingMeasurementsProjective


