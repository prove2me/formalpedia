-- Prove2me | Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_Defs_Families
-- name    : MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_Defs_Families
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T02:43:51.352031+00:00
-- url     : https://prove2.me/theorems/1398b29a-46e9-4c0a-83bc-2b811f8c3f9e
-- title:
--   Definitions of Families: Section 12 — Definitions: consistency and families Global-consistency predicates and the completed-slice family…
-- statement:
--   The definitions of the module `MIPRE.Background.LIDT.MIPStarRE.LDT.Pasting.Defs.Families` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Section 12 — Definitions: consistency and families. Global-consistency predicates and the completed-slice family constructions.
--
--   The module is vendored read-only, with the authors' permission, from [LionSR/MIPStarRE](https://github.com/LionSR/MIPStarRE) (Sirui Lu and the MIPStarRE contributors, Apache 2.0; commit and upstream path in the file header) by `scripts/vendor-lidt.py`.
--
--   **Definitions** (11): `MIPStarRE.LDT.Pasting.IsGloballyConsistent` (A completed-slice tuple `gs` is globally consistent at evaluation points `xs` if there exists a single polynomial `h` in `m+1` variables…); `MIPStarRE.LDT.Pasting.completePartLeftFamily` (Left tensor-placement for the complete part `G^x` on the bipartite space `d * d`.); `MIPStarRE.LDT.Pasting.completePartRightFamily` (Right tensor-placement for the complete part `G^x` on the bipartite space `d * d`.); `MIPStarRE.LDT.Pasting.completePartSubMeas` (Aggregate the polynomial outcomes of `G^x` into its complete part `G^x`.); `MIPStarRE.LDT.Pasting.gHatIdxMeas` (Complete each projective slice submeasurement by adjoining the failure outcome.); `MIPStarRE.LDT.Pasting.globallyConsistentWitness` (Paper origin: `references/ldt-paper/ld-pasting.tex:1131-1135` (definition of `\mathsf{Global}_{\tau}(x)`).); `MIPStarRE.LDT.Pasting.incompletePartLeftFamily` (Left tensor-placement for the incomplete part `G^x_⊥` on the bipartite space `d * d`.); `MIPStarRE.LDT.Pasting.incompletePartRightFamily` (Right tensor-placement for the incomplete part `G^x_⊥` on the bipartite space `d * d`.); `MIPStarRE.LDT.Pasting.incompletePartSubMeas` (Placeholder for the incomplete part `G^x_⊥ = I - G^x`.); `MIPStarRE.LDT.Pasting.interpolateCompletedSlices` (Recover a global polynomial from a completed-slice tuple.); `MIPStarRE.LDT.Pasting.isGloballyConsistent_decidablePred` (`IsGloballyConsistent params xs` is only classically decidable.).
--
--   **Embedded lemmas** (2): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `completePartSubMeas_outcome_unit`, `completePartSubMeas_total`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Background.LIDT.MIPStarRE.LDT.Pasting.Defs.Families` (`MIPRE/Background/LIDT/MIPStarRE/LDT/Pasting/Defs/Families.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 24 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/LIDT/MIPStarRE/LDT/Pasting/Defs/Families.lean

/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/Pasting/Defs/Families.lean
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/MIPStarRE/LDT/Pasting/Defs/Families.lean (definition bundle: declarations the uploaded statements rest on);
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
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finite.Defs
import Mathlib.Data.Finset.Attach
import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Empty
import Mathlib.Data.Finset.Erase
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
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Logic.Basic
import Mathlib.Logic.Embedding.Basic
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
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Order.Interval.Finset.Nat
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
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_LinePolynomialEmbedding
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Test_StrategyPolynomialFamilies
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_Defs_Tuples
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Pasting_Defs_Interpolation
import Theorems.Thm_MIPStarRE_LDT_SubMeas_total_nonneg
import Theorems.Thm_MIPStarRE_LDT_postprocess_total

set_option backward.isDefEq.respectTransparency false

/-!
# Section 12 — Definitions: consistency and families

Global-consistency predicates and the completed-slice family constructions.
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A completed-slice tuple `gs` is globally consistent at evaluation
points `xs` if there exists a single polynomial `h` in `m+1` variables
whose restriction to each genuine slice height `xᵢ` agrees with the
corresponding slice polynomial `gᵢ`.

This matches the paper's `Global_τ(x)` predicate from
`references/ldt-paper/ld-pasting.tex` lines 1123-1131. -/
def IsGloballyConsistent (params : Parameters) [FieldModel params.q]
    {k : ℕ}
    (xs : PointTuple params k)
    (gs : GHatTupleOutcome params k) : Prop :=
  ∃ h : Polynomial params.next,
    ∀ i : Fin k, ∀ (hi : (gs i).isSome = true),
      (Polynomial.restrictAtHeight params h (xs i)).poly =
        ((gs i).get hi).poly

/-- `IsGloballyConsistent params xs` is only classically decidable.
The predicate quantifies over a witness polynomial in the ambient global polynomial
space, so there is no finitary decision procedure to search for such a witness.
This nonconstructive instance is used only for finite `restrictSubMeas` filters. -/
noncomputable instance isGloballyConsistent_decidablePred
    (params : Parameters) [FieldModel params.q] {k : ℕ}
    (xs : PointTuple params k) :
    DecidablePred (IsGloballyConsistent params xs) :=
  fun _gs => Classical.dec _

/-- Paper origin: `references/ldt-paper/ld-pasting.tex:1131-1135`
(definition of `\mathsf{Global}_{\tau}(x)`).

Choose a witness polynomial for a globally consistent tuple. -/
noncomputable def globallyConsistentWitness (params : Parameters) [FieldModel params.q]
    {k : ℕ} (xs : PointTuple params k) (gs : GHatTupleOutcome params k)
    (hGlobal : IsGloballyConsistent params xs gs) : Polynomial params.next :=
  open Classical in
    Classical.choose hGlobal

/-- Recover a global polynomial from a completed-slice tuple.

On the actual pasting path this map is only applied after restricting to tuples in
`Global_τ(x)` with `|τ| ≥ d+1`, so the ineligible branch lies outside the support
of `pastedInterpolationFamily`. We nevertheless make the nonempty ineligible branch
honest: for globally consistent tuples of length `k + 1` that fail the eligibility
cutoff, we return a chosen witness polynomial rather than a placeholder.

The empty-tuple branch keeps the distinguished fallback outcome `h₀`, matching the
completion outcome used in `constructedPastedMeasurement`.

In the eligible branch we still keep the explicit interpolation support witness: a
chosen subset `σ ⊆ support(gs)` of size `d+1` is packaged together with its proof
fields and then passed to `interpolateCompletedSlicesFromSupport`. -/
noncomputable def interpolateCompletedSlices (params : Parameters) [FieldModel params.q] :
    (k : ℕ) → PointTuple params k → GHatTupleOutcome params k → Polynomial params.next
  | 0, _xs, _gs => fallbackInterpolatedPolynomial params
  | _ + 1, xs, gs =>
      if hEligible : InterpolationEligible params gs then
        let supportData := interpolationSupportWitness gs hEligible
        interpolateCompletedSlicesFromSupport params xs gs
          supportData.support supportData.subset_support supportData.card_eq
      else if hGlobal : IsGloballyConsistent params xs gs then
        globallyConsistentWitness params xs gs hGlobal
      else
        fallbackInterpolatedPolynomial params

/-- Aggregate the polynomial outcomes of `G^x` into its complete part `G^x`. -/
noncomputable def completePartSubMeas (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (x : Fq params) : SubMeas Unit ι :=
  postprocess ((family.meas x).toSubMeas) (fun _ => ())

/-- The total operator of the complete part is the original slice total. -/
@[simp] theorem completePartSubMeas_total (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (x : Fq params) :
    (completePartSubMeas params family x).total = (family.meas x).total := by
  simp [completePartSubMeas, postprocess_total]

/-- The unique outcome of the complete part equals its total operator. -/
@[simp] theorem completePartSubMeas_outcome_unit (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (x : Fq params) :
    (completePartSubMeas params family x).outcome () =
      (completePartSubMeas params family x).total := by
  rw [← (completePartSubMeas params family x).sum_eq_total]
  simp [completePartSubMeas]

/-- Placeholder for the incomplete part `G^x_⊥ = I - G^x`. -/
noncomputable def incompletePartSubMeas (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (x : Fq params) : SubMeas Unit ι :=
  let X := 1 - (completePartSubMeas params family x).total
  SubMeas.singleOutcome X
    (sub_nonneg.mpr (completePartSubMeas params family x).total_le_one)
    (sub_le_self _ (completePartSubMeas params family x).total_nonneg)

/-- Complete each projective slice submeasurement by adjoining the failure outcome. -/
noncomputable def gHatIdxMeas (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    IdxMeas (Fq params) (GHatOutcome params) ι :=
  fun x => completeSubMeas ((family.meas x).toSubMeas)

/-- Left tensor-placement for the complete part `G^x`
on the bipartite space `d * d`. -/
noncomputable def completePartLeftFamily (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    IdxSubMeas (SliceQuestion params) Unit (ι × ι) :=
  fun x => leftPlacedSubMeas (ιB := ι) (completePartSubMeas params family x)

/-- Right tensor-placement for the complete part `G^x`
on the bipartite space `d * d`. -/
noncomputable def completePartRightFamily (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    IdxSubMeas (SliceQuestion params) Unit (ι × ι) :=
  fun x => rightPlacedSubMeas (ιA := ι) (completePartSubMeas params family x)

/-- Left tensor-placement for the incomplete part `G^x_⊥`
on the bipartite space `d * d`. -/
noncomputable def incompletePartLeftFamily (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    IdxSubMeas (SliceQuestion params) Unit (ι × ι) :=
  fun x => leftPlacedSubMeas (ιB := ι) (incompletePartSubMeas params family x)

/-- Right tensor-placement for the incomplete part `G^x_⊥`
on the bipartite space `d * d`. -/
noncomputable def incompletePartRightFamily (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    IdxSubMeas (SliceQuestion params) Unit (ι × ι) :=
  fun x => rightPlacedSubMeas (ιA := ι) (incompletePartSubMeas params family x)

end MIPStarRE.LDT.Pasting


