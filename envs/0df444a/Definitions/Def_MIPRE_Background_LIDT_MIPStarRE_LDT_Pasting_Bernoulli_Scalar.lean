-- Prove2me | Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_Bernoulli_Scalar
-- name    : MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_Bernoulli_Scalar
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T02:04:14.862478+00:00
-- url     : https://prove2.me/theorems/30bb1705-4d9e-4442-9838-1783bce85009
-- title:
--   Definitions of Scalar: Scalar Bernoulli polynomial helpers for pasting Purely scalar inequalities used by the matrix Chernoff comparison
-- statement:
--   The definitions of the module `MIPRE.Background.LIDT.MIPStarRE.LDT.Pasting.Bernoulli.Scalar` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Scalar Bernoulli polynomial helpers for pasting. Purely scalar inequalities used by the matrix Chernoff comparison.
--
--   The module is vendored read-only, with the authors' permission, from [LionSR/MIPStarRE](https://github.com/LionSR/MIPStarRE) (Sirui Lu and the MIPStarRE contributors, Apache 2.0; commit and upstream path in the file header) by `scripts/vendor-lidt.py`.
--
--   **Definitions** (3): `MIPStarRE.LDT.Pasting.bernoulliTailLowerAffine` (The affine lower envelope used in the matrix Chernoff reduction.); `MIPStarRE.LDT.Pasting.scalarBernoulliTail` (Scalar Bernoulli tail polynomial `F(p) = ∑_{r=degree+1}^k C(k,r) p^r (1-p)^{k-r}` from `lem:chernoff-bernoulli-matrix`.); `_private.MIPRE.Background.LIDT.MIPStarRE.LDT.Pasting.Bernoulli.Scalar.0.MIPStarRE.LDT.Pasting.scalarBernoulliLowerTail` (The complementary lower-tail sum `∑_{r=0}^d C(k,r) p^r (1-p)^(k-r)`.).
--
--   **Embedded lemmas** (7): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `bernoulli_centered_mgf_le`, `binomial_centered_mgf_eq`, `binomial_centered_mgf_le`, `binomial_lowerTail_eq`, `degree_div_le_theta_half`, `scalarBernoulliLowerTail_add_scalarBernoulliTail`, `scalarBernoulliLowerTail_le_exp`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Background.LIDT.MIPStarRE.LDT.Pasting.Bernoulli.Scalar` (`MIPRE/Background/LIDT/MIPStarRE/LDT/Pasting/Bernoulli/Scalar.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 19 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/LIDT/MIPStarRE/LDT/Pasting/Bernoulli/Scalar.lean

/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/Pasting/Bernoulli/Scalar.lean
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/MIPStarRE/LDT/Pasting/Bernoulli/Scalar.lean (definition bundle: declarations the uploaded statements rest on);
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
import Mathlib.Algebra.BigOperators.Intervals
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
import Mathlib.Algebra.GroupWithZero.Commute
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
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.Polynomial
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.Notation.Defs
import Mathlib.Algebra.Notation.Indicator
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
import Mathlib.Algebra.Order.Monoid.Canonical.Defs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
import Mathlib.Algebra.Order.Nonneg.Basic
import Mathlib.Algebra.Order.Nonneg.Module
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Order.Sub.Basic
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
import Mathlib.Analysis.Complex.Exponential
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
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.Analysis.Normed.Group.Real
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
import Mathlib.Data.ENNReal.Operations
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finite.Defs
import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Empty
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Range
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.FunLike.Basic
import Mathlib.Data.FunLike.Equiv
import Mathlib.Data.Int.Cast.Basic
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
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Init
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Star
import Mathlib.Data.Set.CoeSort
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
import Mathlib.Logic.Embedding.Basic
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Function.Defs
import Mathlib.Logic.IsEmpty.Basic
import Mathlib.Logic.IsEmpty.Defs
import Mathlib.Logic.Nonempty
import Mathlib.Logic.Nontrivial.Defs
import Mathlib.Logic.Unique
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Instances
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.OuterMeasure.AE
import Mathlib.MeasureTheory.OuterMeasure.Defs
import Mathlib.Order.Basic
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Order.CompleteLattice.Defs
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Filter.Defs
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Order.Lattice
import Mathlib.Order.Lattice.Nat
import Mathlib.Order.Nat
import Mathlib.Order.Notation
import Mathlib.Order.RelClasses
import Mathlib.Order.SetNotation
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.Probability.Distributions.Binomial
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.Moments.Basic
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
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
import Mathlib.Topology.UnitInterval
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
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_OpFamily
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_Defs_Tuples
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_Bernoulli_TruncatedSums

set_option backward.isDefEq.respectTransparency false

/-!
# Scalar Bernoulli polynomial helpers for pasting

Purely scalar inequalities used by the matrix Chernoff comparison.
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MeasureTheory ProbabilityTheory
open scoped BigOperators

/-- Scalar Bernoulli tail polynomial
`F(p) = ∑_{r=degree+1}^k C(k,r) p^r (1-p)^{k-r}` from
`lem:chernoff-bernoulli-matrix`. -/
noncomputable def scalarBernoulliTail (k degree : ℕ) (p : Error) : Error :=
  ∑ r ∈ Finset.Icc (degree + 1) k,
    (Nat.choose k r : Error) * (p ^ r * (1 - p) ^ (k - r))

/-- The complementary lower-tail sum `∑_{r=0}^d C(k,r) p^r (1-p)^(k-r)`. -/
noncomputable def scalarBernoulliLowerTail (k degree : ℕ) (p : Error) : Error :=
  ∑ r ∈ Finset.range (degree + 1),
    (Nat.choose k r : Error) * (p ^ r * (1 - p) ^ (k - r))

/-- The affine lower envelope used in the matrix Chernoff reduction. -/
noncomputable def bernoulliTailLowerAffine (theta c : Error) (p : Error) : Error :=
  (1 - c) - ((1 / (1 - theta)) * (1 - p))

/-- Hoeffding's lemma for a centered Bernoulli random variable. -/
lemma bernoulli_centered_mgf_le {p t : Error}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (1 - p) * Real.exp (t * p) + p * Real.exp (t * (p - 1)) ≤
      Real.exp (t ^ (2 : ℕ) / 8) := by
  let pI : unitInterval := ⟨p, hp0, hp1⟩
  have hpI_coe : (pI : Error) = p := rfl
  let μ : Measure Bool := ProbabilityTheory.bernoulliMeasure true false pI
  have hm : AEMeasurable (fun b : Bool => cond b (1 : Error) 0) μ := by
    simpa using (measurable_of_finite (fun b : Bool => cond b (1 : Error) 0)).aemeasurable
  have hb : ∀ᵐ b ∂μ, (cond b (1 : Error) 0) ∈ Set.Icc (0 : Error) 1 := by
    filter_upwards with b
    cases b <;> simp
  have hsubG := ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc hm hb
  have hcentered :
      ProbabilityTheory.HasSubgaussianMGF
        (fun b : Bool => p - cond b (1 : Error) 0)
        ((‖(1 : Error) - 0‖₊ / 2) ^ (2 : ℕ)) μ := by
    refine hsubG.neg.congr ?_
    filter_upwards with b
    simp [μ, ProbabilityTheory.integral_bernoulliMeasure, hpI_coe]
  have hmgf := hcentered.mgf_le t
  have hmgf' :
      p * Real.exp (t * (p - 1)) +
          (1 - p) * Real.exp (p * t) ≤
        Real.exp (t ^ (2 : ℕ) * (2 ^ (2 : ℕ))⁻¹ / 2) := by
    simpa [μ, ProbabilityTheory.mgf, ProbabilityTheory.integral_bernoulliMeasure,
      smul_eq_mul, hpI_coe, mul_comm, add_comm]
      using hmgf
  have hexp :
      Real.exp (t ^ (2 : ℕ) * (2 ^ (2 : ℕ))⁻¹ / 2) = Real.exp (t ^ (2 : ℕ) / 8) := by
    congr 1
    ring_nf
  rw [hexp] at hmgf'
  simpa [mul_comm, add_comm] using hmgf'

/-- The centered moment-generating function of the binomial law is the binomial expansion of the
corresponding one-step Bernoulli moment-generating function. -/
lemma binomial_centered_mgf_eq
    (k : ℕ) {p t : Error} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ProbabilityTheory.mgf (fun i : ℕ => p * k - i)
      (ProbabilityTheory.binomial k (⟨p, hp0, hp1⟩ : unitInterval)) t =
        ∑ r ∈ Finset.range (k + 1),
          (Nat.choose k r : Error) * (p ^ r * (1 - p) ^ (k - r)) *
            Real.exp (t * (p * k - r)) := by
  let pI : unitInterval := ⟨p, hp0, hp1⟩
  have hpI_coe : (pI : Error) = p := rfl
  calc
    ProbabilityTheory.mgf (fun i : ℕ => p * k - i) (ProbabilityTheory.binomial k pI) t
      = ∫ i, Real.exp (t * (p * k - i)) ∂ProbabilityTheory.binomial k pI := by
          try rfl -- vendoring compile fix (Lean v4.33): the previous step may close the goal
    _ = ∑ r ∈ Finset.Iic k,
          (Nat.choose k r : Error) * (p ^ r * (1 - p) ^ (k - r)) *
            Real.exp (t * (p * k - r)) := by
          rw [ProbabilityTheory.integral_binomial]
          refine Finset.sum_congr rfl ?_
          intro r hr
          simp [hpI_coe, smul_eq_mul]
          ring
    _ = ∑ r ∈ Finset.range (k + 1),
          (Nat.choose k r : Error) * (p ^ r * (1 - p) ^ (k - r)) *
            Real.exp (t * (p * k - r)) := by
          rw [Nat.range_succ_eq_Iic]

/-- A Hoeffding bound for the centered binomial moment-generating function. -/
lemma binomial_centered_mgf_le
    (k : ℕ) {p t : Error} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ProbabilityTheory.mgf (fun i : ℕ => p * k - i)
      (ProbabilityTheory.binomial k (⟨p, hp0, hp1⟩ : unitInterval)) t ≤
        Real.exp ((k : Error) * t ^ (2 : ℕ) / 8) := by
  let a : Error := p * Real.exp (t * (p - 1))
  let b : Error := (1 - p) * Real.exp (t * p)
  have hrewrite :
      (∑ r ∈ Finset.range (k + 1),
        (Nat.choose k r : Error) * (p ^ r * (1 - p) ^ (k - r)) *
          Real.exp (t * (p * k - r))) =
        ∑ r ∈ Finset.range (k + 1), (Nat.choose k r : Error) * (a ^ r * b ^ (k - r)) := by
    refine Finset.sum_congr rfl ?_
    intro r hr
    dsimp [a, b]
    have hrle : r ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hr)
    have hexp :
        Real.exp (t * (p * k - r)) =
          Real.exp (((k : Error) - r) * (t * p)) * Real.exp ((r : Error) * (t * (p - 1))) := by
      rw [show t * (p * k - r) =
          ((k : Error) - r) * (t * p) + (r : Error) * (t * (p - 1)) by ring]
      rw [Real.exp_add]
    have hfirst :
        Real.exp (((k : Error) - r) * (t * p)) = Real.exp (t * p) ^ (k - r) := by
      rw [← Nat.cast_sub hrle]
      simpa using (Real.exp_nat_mul (t * p) (k - r))
    have hsecond :
        Real.exp ((r : Error) * (t * (p - 1))) = Real.exp (t * (p - 1)) ^ r := by
      simpa using (Real.exp_nat_mul (t * (p - 1)) r)
    rw [hexp, hfirst, hsecond]
    calc
      (Nat.choose k r : Error) * (p ^ r * (1 - p) ^ (k - r)) *
          (Real.exp (t * p) ^ (k - r) * Real.exp (t * (p - 1)) ^ r)
        = (Nat.choose k r : Error) *
            ((p ^ r * Real.exp (t * (p - 1)) ^ r) *
              ((1 - p) ^ (k - r) * Real.exp (t * p) ^ (k - r))) := by
              ring
      _ = (Nat.choose k r : Error) *
            ((p * Real.exp (t * (p - 1))) ^ r * ((1 - p) * Real.exp (t * p)) ^ (k - r)) := by
              rw [← mul_pow, ← mul_pow]
      _ = (Nat.choose k r : Error) * (a ^ r * b ^ (k - r)) := by
              try rfl -- vendoring compile fix (Lean v4.33): the previous step may close the goal
  have hpow :
      (∑ r ∈ Finset.range (k + 1), (Nat.choose k r : Error) * (a ^ r * b ^ (k - r))) =
        (a + b) ^ k := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using (add_pow a b k).symm
  let pI : unitInterval := ⟨p, hp0, hp1⟩
  calc
    ProbabilityTheory.mgf (fun i : ℕ => p * k - i)
        (ProbabilityTheory.binomial k pI) t
      = ∑ r ∈ Finset.range (k + 1),
          (Nat.choose k r : Error) * (p ^ r * (1 - p) ^ (k - r)) *
            Real.exp (t * (p * k - r)) :=
        binomial_centered_mgf_eq k hp0 hp1
    _ = ∑ r ∈ Finset.range (k + 1), (Nat.choose k r : Error) * (a ^ r * b ^ (k - r)) := hrewrite
    _ = (a + b) ^ k := hpow
    _ ≤ (Real.exp (t ^ (2 : ℕ) / 8)) ^ k := by
          have ha_nonneg : 0 ≤ a := by
            dsimp [a]
            positivity
          have hOneSub_nonneg : 0 ≤ 1 - p := by
            linarith
          have hb_nonneg : 0 ≤ b := by
            dsimp [b]
            exact mul_nonneg hOneSub_nonneg (by positivity)
          have hab_nonneg : 0 ≤ a + b := by
            linarith
          apply pow_le_pow_left₀ hab_nonneg
          simpa [a, b, add_comm] using bernoulli_centered_mgf_le hp0 hp1
    _ = Real.exp ((k : Error) * (t ^ (2 : ℕ) / 8)) := by
          symm
          simpa [mul_comm] using (Real.exp_nat_mul (t ^ (2 : ℕ) / 8) k)
    _ = Real.exp ((k : Error) * t ^ (2 : ℕ) / 8) := by
          congr 1
          ring

/-- The lower tail of the binomial law is the lower partial sum of the Bernoulli polynomial. -/
lemma binomial_lowerTail_eq
    (k degree : ℕ) {p : Error} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (ProbabilityTheory.binomial k (⟨p, hp0, hp1⟩ : unitInterval)).real
        {i : ℕ | (i : Error) ≤ degree} =
      scalarBernoulliLowerTail k degree p := by
  let pI : unitInterval := ⟨p, hp0, hp1⟩
  have hpI_coe : (pI : Error) = p := rfl
  let f : ℕ → Error := fun r =>
    (Nat.choose k r : Error) * (p ^ r * (1 - p) ^ (k - r))
  calc
    (ProbabilityTheory.binomial k pI).real {i : ℕ | (i : Error) ≤ degree}
      = ∑ r ∈ Finset.Iic k, if r ≤ degree then f r else 0 := by
          rw [measureReal_def, ProbabilityTheory.binomial_eq_sum_dirac,
            Measure.finsetSum_apply, ENNReal.toReal_sum]
          · refine Finset.sum_congr rfl ?_
            intro r hr
            by_cases hrd : r ≤ degree
            · have hcoeff_nonneg :
                  0 ≤ (Nat.choose k r : Error) * p ^ r * (1 - p) ^ (k - r) := by
                positivity
              have hmem : r ∈ {i : ℕ | i ≤ degree} := hrd
              have htoReal :
                  (ENNReal.ofReal ((Nat.choose k r : Error) * p ^ r *
                    (1 - p) ^ (k - r))).toReal =
                    (Nat.choose k r : Error) * (p ^ r * (1 - p) ^ (k - r)) := by
                rw [ENNReal.toReal_ofReal hcoeff_nonneg]
                ring
              simpa only [Nat.cast_le, Measure.smul_apply,
                MeasurableSpace.measurableSet_top, Measure.dirac_apply', smul_eq_mul,
                Set.indicator_of_mem hmem, Pi.one_apply, mul_one, hrd, if_true, f, hpI_coe]
                using htoReal
            · simp [Measure.smul_apply, hrd, f, hpI_coe, smul_eq_mul]
          · intro r hr
            refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top ?_
            by_cases hrd : r ≤ degree <;> simp [Set.indicator, hrd]
    _ = ∑ r ∈ Finset.range (k + 1), if r ≤ degree then f r else 0 := by
          rw [Nat.range_succ_eq_Iic]
    _ = ∑ r ∈ Finset.range (degree + 1), f r := by
          by_cases hdk : degree ≤ k
          · have hRange :
                (∑ r ∈ Finset.range (degree + 1), if r ≤ degree then f r else 0) =
                  ∑ r ∈ Finset.range (degree + 1), f r := by
                refine Finset.sum_congr rfl ?_
                intro r hr
                have hrle : r ≤ degree := Nat.le_of_lt_succ (Finset.mem_range.mp hr)
                simp [hrle]
            have hIcoZero :
                (∑ r ∈ Finset.Ico (degree + 1) (k + 1), if r ≤ degree then f r else 0) = 0 := by
                refine Finset.sum_eq_zero ?_
                intro r hr
                have hlt : degree < r := (Finset.mem_Ico.mp hr).1
                simp [Nat.not_le.mpr hlt]
            have hsplit :=
              Finset.sum_range_add_sum_Ico (f := fun r => if r ≤ degree then f r else 0)
                (h := Nat.succ_le_succ hdk)
            calc
              (∑ r ∈ Finset.range (k + 1), if r ≤ degree then f r else 0)
                =
                  ∑ r ∈ Finset.range (degree + 1), if r ≤ degree then f r else 0 := by
                      symm
                      rw [hIcoZero, add_zero] at hsplit
                      exact hsplit
              _ = ∑ r ∈ Finset.range (degree + 1), f r := hRange
          · have hdk' : k < degree := Nat.lt_of_not_ge hdk
            have hAll :
                (∑ r ∈ Finset.range (k + 1), if r ≤ degree then f r else 0) =
                  ∑ r ∈ Finset.range (k + 1), f r := by
                refine Finset.sum_congr rfl ?_
                intro r hr
                have hrle : r ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hr)
                have hrdeg : r ≤ degree := hrle.trans (Nat.le_of_lt hdk')
                simp [hrdeg]
            have hIcoZero : ∑ r ∈ Finset.Ico (k + 1) (degree + 1), f r = 0 := by
              refine Finset.sum_eq_zero ?_
              intro r hr
              have hklt : k < r := (Finset.mem_Ico.mp hr).1
              change (Nat.choose k r : Error) * (p ^ r * (1 - p) ^ (k - r)) = 0
              rw [Nat.choose_eq_zero_of_lt hklt]
              simp
            have hsplit :=
              Finset.sum_range_add_sum_Ico (f := f) (h := Nat.succ_le_succ (Nat.le_of_lt hdk'))
            calc
              (∑ r ∈ Finset.range (k + 1), if r ≤ degree then f r else 0)
                = ∑ r ∈ Finset.range (k + 1), f r := hAll
              _ = ∑ r ∈ Finset.range (degree + 1), f r := by
                    rw [hIcoZero, add_zero] at hsplit
                    exact hsplit
    _ = scalarBernoulliLowerTail k degree p := by
          try rfl -- vendoring compile fix (Lean v4.33): the previous step may close the goal

/-- The binomial lower tail obeys the additive Hoeffding bound. -/
lemma scalarBernoulliLowerTail_le_exp
    (k degree : ℕ) {p : Error} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hpd : (degree : Error) / (k : Error) ≤ p) :
    scalarBernoulliLowerTail k degree p ≤
      Real.exp (-(2 * ((p - (degree : Error) / (k : Error)) ^ (2 : ℕ)) * (k : Error))) := by
  by_cases hk0 : k = 0
  · subst hk0
    have htail : scalarBernoulliLowerTail 0 degree p = 1 := by
      unfold scalarBernoulliLowerTail
      rw [Finset.sum_eq_single 0]
      · simp
      · intro r hr hr0
        have hrpos : 0 < r := Nat.pos_iff_ne_zero.mpr hr0
        simp [Nat.choose_eq_zero_of_lt hrpos]
      · simp
    rw [htail]
    simp
  · have hkpos : 0 < (k : Error) := by
      exact_mod_cast Nat.pos_iff_ne_zero.mpr hk0
    let ε : Error := p * (k : Error) - degree
    let t : Error := 4 * (p - degree / (k : Error))
    let pI : unitInterval := ⟨p, hp0, hp1⟩
    let μ : Measure ℕ := ProbabilityTheory.binomial k pI
    have hε_nonneg : 0 ≤ ε := by
      dsimp [ε]
      have hpd' : (degree : Error) ≤ p * (k : Error) := by
        rw [div_le_iff₀ hkpos] at hpd
        simpa [mul_comm] using hpd
      linarith
    have ht_nonneg : 0 ≤ t := by
      dsimp [t]
      nlinarith
    have hInt :
        Integrable (fun i : ℕ => Real.exp (t * (p * (k : Error) - i))) μ := by
      exact ProbabilityTheory.integrable_binomial _
    have hCher :=
      ProbabilityTheory.measure_ge_le_exp_mul_mgf
        (μ := μ) (X := fun i : ℕ => p * (k : Error) - i) (t := t) ε
        ht_nonneg hInt
    have hEvent :
        {i : ℕ | ε ≤ p * (k : Error) - i} =
          {i : ℕ | (i : Error) ≤ degree} := by
      ext i
      dsimp [ε]
      constructor <;> intro hi <;> linarith
    calc
      scalarBernoulliLowerTail k degree p
        = μ.real {i : ℕ | ε ≤ p * (k : Error) - i} := by
            rw [hEvent]
            symm
            exact binomial_lowerTail_eq k degree hp0 hp1
      _ ≤ Real.exp (-t * ε) *
            ProbabilityTheory.mgf (fun i : ℕ => p * (k : Error) - i) μ t := hCher
      _ ≤ Real.exp (-t * ε) * Real.exp ((k : Error) * t ^ (2 : ℕ) / 8) := by
            gcongr
            exact binomial_centered_mgf_le k hp0 hp1 (t := t)
      _ = Real.exp (-t * ε + (k : Error) * t ^ (2 : ℕ) / 8) := by
            rw [← Real.exp_add]
      _ = Real.exp (-(2 * ((p - (degree : Error) / (k : Error)) ^ (2 : ℕ)) * (k : Error))) := by
            have hε_eq : ε = (p - degree / (k : Error)) * (k : Error) := by
              dsimp [ε]
              field_simp [hkpos.ne']
            dsimp [t]
            rw [hε_eq]
            congr 1
            ring_nf

/-- The lower and upper binomial tails partition the full Bernoulli polynomial. -/
lemma scalarBernoulliLowerTail_add_scalarBernoulliTail
    (k degree : ℕ) (p : Error) :
    scalarBernoulliLowerTail k degree p + scalarBernoulliTail k degree p = 1 := by
  let f : ℕ → Error := fun r =>
    (Nat.choose k r : Error) * (p ^ r * (1 - p) ^ (k - r))
  have hfull : ∑ r ∈ Finset.range (k + 1), f r = 1 := by
    calc
      ∑ r ∈ Finset.range (k + 1), f r
        = ∑ r ∈ Finset.range (k + 1), p ^ r * (1 - p) ^ (k - r) * Nat.choose k r := by
              refine Finset.sum_congr rfl ?_
              intro r hr
              ring
      _ = (p + (1 - p)) ^ k := by
            simpa using (add_pow p (1 - p) k).symm
      _ = 1 := by
            ring
  by_cases hdk : degree ≤ k
  · have hTail :
        ∑ r ∈ Finset.Ico (degree + 1) (k + 1), f r = scalarBernoulliTail k degree p := by
      have hIco : Finset.Ico (degree + 1) (k + 1) = Finset.Icc (degree + 1) k := by
        ext r
        simp
      simp [scalarBernoulliTail, f, hIco]
    calc
      scalarBernoulliLowerTail k degree p + scalarBernoulliTail k degree p
        =
          (∑ r ∈ Finset.range (degree + 1), f r) +
            ∑ r ∈ Finset.Ico (degree + 1) (k + 1), f r := by
              rw [scalarBernoulliLowerTail, ← hTail]
      _ = ∑ r ∈ Finset.range (k + 1), f r := by
            exact Finset.sum_range_add_sum_Ico (f := f) (h := Nat.succ_le_succ hdk)
      _ = 1 := hfull
  · have hdk' : k < degree := Nat.lt_of_not_ge hdk
    have hTailZero : scalarBernoulliTail k degree p = 0 := by
      unfold scalarBernoulliTail
      refine Finset.sum_eq_zero ?_
      intro r hr
      have hr1 : degree + 1 ≤ r := (Finset.mem_Icc.mp hr).1
      have hr2 : r ≤ k := (Finset.mem_Icc.mp hr).2
      omega
    have hIcoZero : ∑ r ∈ Finset.Ico (k + 1) (degree + 1), f r = 0 := by
      refine Finset.sum_eq_zero ?_
      intro r hr
      have hklt : k < r := (Finset.mem_Ico.mp hr).1
      change (Nat.choose k r : Error) * (p ^ r * (1 - p) ^ (k - r)) = 0
      rw [Nat.choose_eq_zero_of_lt hklt]
      simp
    have hsplit :=
      Finset.sum_range_add_sum_Ico (f := f) (h := Nat.succ_le_succ (Nat.le_of_lt hdk'))
    calc
      scalarBernoulliLowerTail k degree p + scalarBernoulliTail k degree p
        = ∑ r ∈ Finset.range (degree + 1), f r := by
            rw [scalarBernoulliLowerTail, hTailZero, add_zero]
      _ = ∑ r ∈ Finset.range (k + 1), f r := by
            rw [hIcoZero, add_zero] at hsplit
            exact hsplit.symm
      _ = 1 := hfull

/-- The paper's size condition `k ≥ 2d/θ` implies `d/k ≤ θ/2`. -/
lemma degree_div_le_theta_half
    (theta : Error) (k degree : ℕ)
    (hθ0 : 0 < theta) (hk : (2 * (degree : Error)) / theta ≤ (k : Error)) :
    (degree : Error) / (k : Error) ≤ theta / 2 := by
  by_cases hk0 : k = 0
  · subst hk0
    have hdeg : degree = 0 := by
      by_contra hdeg
      have hdegpos : 0 < (degree : Error) := by
        exact_mod_cast Nat.pos_iff_ne_zero.mpr hdeg
      have hfracpos : 0 < (2 * (degree : Error)) / theta := by
        positivity
      linarith
    subst hdeg
    have hnonneg : 0 ≤ theta / 2 := by
      positivity
    simpa using hnonneg
  · have hkpos : 0 < (k : Error) := by
      exact_mod_cast Nat.pos_iff_ne_zero.mpr hk0
    have hk' := hk
    field_simp [hθ0.ne', hkpos.ne'] at hk'
    have h2 : (2 * (degree : Error)) / (k : Error) ≤ theta := by
      rw [div_le_iff₀ hkpos]
      simpa [mul_comm, mul_left_comm, mul_assoc] using hk'
    have h2' : 2 * ((degree : Error) / (k : Error)) ≤ theta := by
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using h2
    linarith

end MIPStarRE.LDT.Pasting


