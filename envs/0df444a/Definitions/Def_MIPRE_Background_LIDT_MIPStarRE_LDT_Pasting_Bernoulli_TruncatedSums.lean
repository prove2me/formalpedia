-- Prove2me | Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_Bernoulli_TruncatedSums
-- name    : MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_Bernoulli_TruncatedSums
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T02:02:38.56262+00:00
-- url     : https://prove2.me/theorems/4ca2a132-76bd-486c-922d-0725ef3fd7e1
-- title:
--   Definitions of TruncatedSums: Section 12 pasting: Bernoulli truncated sums Truncated type sums and their one-step recurrence
-- statement:
--   The definitions of the module `MIPRE.Background.LIDT.MIPStarRE.LDT.Pasting.Bernoulli.TruncatedSums` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Section 12 pasting: Bernoulli truncated sums. Truncated type sums and their one-step recurrence.
--
--   The module is vendored read-only, with the authors' permission, from [LionSR/MIPStarRE](https://github.com/LionSR/MIPStarRE) (Sirui Lu and the MIPStarRE contributors, Apache 2.0; commit and upstream path in the file header) by `scripts/vendor-lidt.py`.
--
--   **Embedded lemmas** (7): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `full_gHatType_sum_eq_one`, `gHatTypeOperator_nonneg`, `gHatTypeOperator_prepend_false`, `gHatTypeOperator_prepend_true`, `gHatTypeWeight_le`, `gHatTypeWeight_prepend_false`, `gHatTypeWeight_prepend_true`.
--
--   The bundle holds no definition of its own: it carries the lemmas listed above, which later bundles and proofs import.
--
--   **Formalization Note** The bundle is the module `MIPRE.Background.LIDT.MIPStarRE.LDT.Pasting.Bernoulli.TruncatedSums` (`MIPRE/Background/LIDT/MIPStarRE/LDT/Pasting/Bernoulli/TruncatedSums.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 18 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/LIDT/MIPStarRE/LDT/Pasting/Bernoulli/TruncatedSums.lean

/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/Pasting/Bernoulli/TruncatedSums.lean
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/MIPStarRE/LDT/Pasting/Bernoulli/TruncatedSums.lean (definition bundle: declarations the uploaded statements rest on);
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
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Init
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.SuccPred
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
import Mathlib.Logic.Embedding.Basic
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.IsEmpty.Basic
import Mathlib.Logic.IsEmpty.Defs
import Mathlib.Logic.Nonempty
import Mathlib.Logic.Nontrivial.Defs
import Mathlib.Logic.Unique
import Mathlib.Order.Basic
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.Lattice
import Mathlib.Order.Lattice.Nat
import Mathlib.Order.Nat
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

set_option backward.isDefEq.respectTransparency false

/-!
# Section 12 pasting: Bernoulli truncated sums

Truncated type sums and their one-step recurrence.
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Bernoulli recurrence weights -/

lemma gHatTypeWeight_le {k : ℕ} (τ : GHatType k) :
    gHatTypeWeight τ ≤ k := by
  unfold gHatTypeWeight
  simpa using (Finset.card_filter_le
    (s := (Finset.univ : Finset (Fin k)))
    (p := fun i : Fin k => τ i))

lemma gHatTypeWeight_prepend_true {k : ℕ} (τ : GHatType k) :
    gHatTypeWeight (prependTypeBit true τ) = gHatTypeWeight τ + 1 := by
  unfold gHatTypeWeight
  simpa [prependTypeBit, Fin.cons_zero, Fin.cons_succ, add_comm] using
    (Fin.card_filter_univ_succ
      (n := k) (p := fun i : Fin (k + 1) => (Fin.cons true τ : GHatType (k + 1)) i = true))

lemma gHatTypeWeight_prepend_false {k : ℕ} (τ : GHatType k) :
    gHatTypeWeight (prependTypeBit false τ) = gHatTypeWeight τ := by
  unfold gHatTypeWeight
  simpa [prependTypeBit, Fin.cons_zero, Fin.cons_succ] using
    (Fin.card_filter_univ_succ
      (n := k) (p := fun i : Fin (k + 1) => (Fin.cons false τ : GHatType (k + 1)) i = true))

lemma gHatTypeOperator_nonneg
    (G : MIPStarRE.Quantum.Op ι)
    (hGpsd : 0 ≤ G)
    (hGleOne : G ≤ 1)
    {k : ℕ} (τ : GHatType k) :
    0 ≤ gHatTypeOperator G τ := by
  have hcomm : Commute G (1 - G) :=
    (Commute.one_right G).sub_right (Commute.refl G)
  have hGpow : 0 ≤ G ^ gHatTypeWeight τ := by
    exact (Matrix.PosSemidef.pow (Matrix.nonneg_iff_posSemidef.mp hGpsd) _).nonneg
  have hIGpow : 0 ≤ (1 - G) ^ (k - gHatTypeWeight τ) := by
    exact
      (Matrix.PosSemidef.pow
        (Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr hGleOne)) _).nonneg
  have hcommPow : Commute (G ^ gHatTypeWeight τ) ((1 - G) ^ (k - gHatTypeWeight τ)) :=
    (hcomm.pow_left _).pow_right _
  exact Commute.mul_nonneg hGpow hIGpow hcommPow

lemma gHatTypeOperator_prepend_true
    (G : MIPStarRE.Quantum.Op ι)
    {k : ℕ} (τ : GHatType k) :
    gHatTypeOperator G (prependTypeBit true τ) = gHatTypeOperator G τ * G := by
  have hcomm : Commute G (1 - G) :=
    (Commute.one_right G).sub_right (Commute.refl G)
  have hsub : k + 1 - (gHatTypeWeight τ + 1) = k - gHatTypeWeight τ := by
    have hweight_le : gHatTypeWeight τ ≤ k := gHatTypeWeight_le τ
    omega
  unfold gHatTypeOperator
  rw [gHatTypeWeight_prepend_true, hsub, pow_succ]
  calc
    (G ^ gHatTypeWeight τ * G) * (1 - G) ^ (k - gHatTypeWeight τ)
      = G ^ gHatTypeWeight τ * (G * (1 - G) ^ (k - gHatTypeWeight τ)) := by
          simp [mul_assoc]
    _ = G ^ gHatTypeWeight τ * ((1 - G) ^ (k - gHatTypeWeight τ) * G) := by
          rw [(hcomm.pow_right _).eq]
    _ = (G ^ gHatTypeWeight τ * (1 - G) ^ (k - gHatTypeWeight τ)) * G := by
          simp [mul_assoc]

lemma gHatTypeOperator_prepend_false
    (G : MIPStarRE.Quantum.Op ι)
    {k : ℕ} (τ : GHatType k) :
    gHatTypeOperator G (prependTypeBit false τ) = gHatTypeOperator G τ * (1 - G) := by
  have hsub : k + 1 - gHatTypeWeight τ = k - gHatTypeWeight τ + 1 := by
    have hweight_le : gHatTypeWeight τ ≤ k := gHatTypeWeight_le τ
    omega
  unfold gHatTypeOperator
  rw [gHatTypeWeight_prepend_false, hsub, pow_succ]
  simp [mul_assoc]

/-- The full sum of type operators equals the identity.

This is the commuting binomial expansion
`∑ τ : GHatType k, G ^ |τ| * (1 - G) ^ (k - |τ|) = (G + (1 - G))^k = 1`. -/
lemma full_gHatType_sum_eq_one
    (G : MIPStarRE.Quantum.Op ι) :
    ∀ prefixLen : ℕ, ∑ τprefix : GHatType prefixLen, gHatTypeOperator G τprefix = 1
  | 0 => by
      simp [gHatTypeOperator, gHatTypeWeight]
  | prefixLen + 1 => by
      have hsplit :
          (∑ τprefix : GHatType (prefixLen + 1),
              gHatTypeOperator G τprefix) =
            ∑ p : Bool × GHatType prefixLen,
              gHatTypeOperator G (Fin.cons p.1 p.2) := by
        exact (Fintype.sum_equiv
          ((Fin.consEquiv (fun _ : Fin (prefixLen + 1) => Bool)).symm)
          (fun τprefix => gHatTypeOperator G τprefix)
          (fun p => gHatTypeOperator G (Fin.cons p.1 p.2))
          (by
            intro τprefix
            simp))
      have hprod :
          (∑ p : Bool × GHatType prefixLen,
              gHatTypeOperator G (Fin.cons p.1 p.2)) =
            ∑ b : Bool,
              ∑ τprefix : GHatType prefixLen,
                gHatTypeOperator G (Fin.cons b τprefix) := by
        simpa using
          (Fintype.sum_prod_type'
            (f := fun b τprefix => gHatTypeOperator G (Fin.cons b τprefix)))
      calc
        ∑ τprefix : GHatType (prefixLen + 1), gHatTypeOperator G τprefix
          = ∑ p : Bool × GHatType prefixLen,
              gHatTypeOperator G (Fin.cons p.1 p.2) := hsplit
        _ = ∑ b : Bool,
              ∑ τprefix : GHatType prefixLen,
                gHatTypeOperator G (Fin.cons b τprefix) := hprod
        _ =
            (∑ τprefix : GHatType prefixLen,
              gHatTypeOperator G (Fin.cons true τprefix)) +
              ∑ τprefix : GHatType prefixLen,
                gHatTypeOperator G (Fin.cons false τprefix) := by
                rw [Fintype.sum_bool]
        _ =
            (∑ τprefix : GHatType prefixLen,
              gHatTypeOperator G (prependTypeBit true τprefix)) +
              ∑ τprefix : GHatType prefixLen,
                gHatTypeOperator G (prependTypeBit false τprefix) := by
                simp [prependTypeBit]
        _ =
            (∑ τprefix : GHatType prefixLen, gHatTypeOperator G τprefix * G) +
              ∑ τprefix : GHatType prefixLen,
                gHatTypeOperator G τprefix * (1 - G) := by
                simp_rw [gHatTypeOperator_prepend_true, gHatTypeOperator_prepend_false]
        _ =
            (∑ τprefix : GHatType prefixLen, gHatTypeOperator G τprefix) * G +
              (∑ τprefix : GHatType prefixLen,
                gHatTypeOperator G τprefix) * (1 - G) := by
                rw [Finset.sum_mul, Finset.sum_mul]
        _ = 1 * G + 1 * (1 - G) := by
              simp [full_gHatType_sum_eq_one G prefixLen]
        _ = 1 := by
              have hcancel : G + (1 - G) = (1 : MIPStarRE.Quantum.Op ι) := by
                abel
              rw [one_mul, one_mul]
              exact hcancel

end MIPStarRE.LDT.Pasting


