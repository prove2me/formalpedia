-- Prove2me | Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_SelfConsistency_DataProcessing
-- name    : MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_SelfConsistency_DataProcessing
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T03:56:55.334458+00:00
-- url     : https://prove2.me/theorems/e7fc124a-040b-457b-8b86-89f24ebfa1f5
-- title:
--   Definitions of DataProcessing: Self-consistency: data processing `prop:self-consistency-implies-data-processing`: self-consistency implies that…
-- statement:
--   The definitions of the module `MIPRE.Background.LIDT.MIPStarRE.LDT.Preliminaries.SelfConsistency.DataProcessing` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Self-consistency: data processing. `prop:self-consistency-implies-data-processing`: self-consistency implies that postprocessing a measurement cannot substantially decrease consistency.
--
--   The module is vendored read-only, with the authors' permission, from [LionSR/MIPStarRE](https://github.com/LionSR/MIPStarRE) (Sirui Lu and the MIPStarRE contributors, Apache 2.0; commit and upstream path in the file header) by `scripts/vendor-lidt.py`.
--
--   **Embedded lemmas** (1): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `wrongSideEstimate`.
--
--   The bundle holds no definition of its own: it carries the lemmas listed above, which later bundles and proofs import.
--
--   **Formalization Note** The bundle is the module `MIPRE.Background.LIDT.MIPStarRE.LDT.Preliminaries.SelfConsistency.DataProcessing` (`MIPRE/Background/LIDT/MIPStarRE/LDT/Preliminaries/SelfConsistency/DataProcessing.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 33 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/LIDT/MIPStarRE/LDT/Preliminaries/SelfConsistency/DataProcessing.lean

/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/LDT/Preliminaries/SelfConsistency/DataProcessing.lean
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/MIPStarRE/LDT/Preliminaries/SelfConsistency/DataProcessing.lean (definition bundle: declarations the uploaded statements rest on);
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
import Mathlib.Algebra.Order.Monoid.NatCast
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
import Mathlib.Tactic.NormNum.Basic
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
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Test_StrategyRole_Core
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_MeasurementLift
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_Defs
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_ComparisonCore
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_DistanceBounds
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_ConsistencyBridges
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_InnerProduct
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichMain_Completeness
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Core
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_CauchySchwarz
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Preliminaries_Triangles_Core
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Test_StrategyRole_Algebra
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Test_StrategyFailures
import Theorems.Thm_MIPStarRE_LDT_Preliminaries_completenessTransferProjectiveP
import Theorems.Thm_MIPStarRE_LDT_Preliminaries_easyApproxFromApproxDelta
import Theorems.Thm_MIPStarRE_LDT_Preliminaries_sddRel_symm
import Theorems.Thm_MIPStarRE_LDT_Preliminaries_subMeas_diagMass_le_mass
import Theorems.Thm_MIPStarRE_LDT_SubMeas_outcome_hermitian
import Theorems.Thm_MIPStarRE_LDT_avgOver_mono
import Theorems.Thm_MIPStarRE_LDT_ev_mul_comm_of_psd
import Theorems.Thm_MIPStarRE_LDT_ev_sub
import Theorems.Thm_MIPStarRE_LDT_leftTensor_mul_leftTensor
import Theorems.Thm_MIPStarRE_LDT_leftTensor_mul_rightTensor_eq_opTensor
import Theorems.Thm_MIPStarRE_LDT_postprocess_total

set_option backward.isDefEq.respectTransparency false

/-!
# Self-consistency: data processing

`prop:self-consistency-implies-data-processing`: self-consistency implies that
postprocessing a measurement cannot substantially decrease consistency.

## References

- `references/ldt-paper/preliminaries.tex`
- `blueprint/src/chapter/ch03_preliminaries.tex`
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT.Preliminaries

open MIPStarRE.LDT

/-- `prop:self-consistency-implies-data-processing`.

Proof:
1. First prove the “wrong-side” estimate
   `P_[f_q] ⊗ I ≈_{2δ + 4√ε} I ⊗ A_[f_q]` by:
   - expanding the `qSDD` square,
   - bounding the mass of `P` via `completenessTransferProjectiveP`,
   - comparing the mixed overlap with the diagonal overlap of `A`,
   - and using SSC plus question-dependent postprocessing monotonicity.
2. Apply `twoNotionsOfSelfConsistencyAfterEvaluation` to obtain
   `A_[f_q] ⊗ I ≈_{2δ} I ⊗ A_[f_q]`.
3. Use the `SDDRel` triangle inequality to conclude
   `P_[f_q] ⊗ I ≈_{8δ + 8√ε} A_[f_q] ⊗ I`. -/
lemma wrongSideEstimate
    {Question α β : Type*} {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype α] [Fintype β]
    (ψ : QuantumState (ι × ι))
    (hperm : PermInvState ψ)
    (hψ : ψ.IsNormalized)
    (𝒟 : Distribution Question)
    (h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1)
    (A : IdxSubMeas Question α ι)
    (P : IdxProjSubMeas Question α ι)
    (δ ε : Error) (f : Question → α → β) :
    BipartiteSSCRel ψ 𝒟 A δ →
    SDDRel ψ 𝒟
      (IdxSubMeas.liftLeft (IdxProjSubMeas.toIdxSubMeas P))
      (IdxSubMeas.liftLeft A) ε →
      SDDRel ψ 𝒟
        (IdxSubMeas.liftLeft (fun q => postprocess ((P q).toSubMeas) (f q)))
        (IdxSubMeas.liftRight (fun q => postprocess (A q) (f q)))
        (2 * δ + 4 * Real.sqrt ε) := by
  intro hssc ⟨hε⟩
  let PL : IdxProjSubMeas Question α (ι × ι) := fun q =>
    { toSubMeas := ((P q).toSubMeas).liftLeft
      proj := fun a => by simp [SubMeas.liftLeft, leftTensor_mul_leftTensor, (P q).proj a] }
  let LPf : IdxSubMeas Question β (ι × ι) :=
    IdxSubMeas.liftLeft (fun q => postprocess ((P q).toSubMeas) (f q))
  let RAf : IdxSubMeas Question β (ι × ι) :=
    IdxSubMeas.liftRight (fun q => postprocess (A q) (f q))
  let crossPost : Question → Error := fun q =>
    qMatchMass ψ (LPf q) (RAf q)
  let crossOrig : Question → Error := fun q =>
    qMatchMass ψ
      ((IdxSubMeas.liftLeft (IdxProjSubMeas.toIdxSubMeas P)) q)
      ((IdxSubMeas.liftRight A) q)
  let overlapA : Question → Error := fun q =>
    qMatchMass ψ ((IdxSubMeas.liftLeft A) q) ((IdxSubMeas.liftRight A) q)
  have hcomp :
      CompTransferStmt ψ 𝒟 (IdxSubMeas.liftLeft A) PL ε := by
    apply completenessTransferProjectiveP ψ 𝒟 hψ h𝒟 (IdxSubMeas.liftLeft A) PL ε
    exact
      sddRel_symm ψ 𝒟
        (IdxSubMeas.liftLeft (IdxProjSubMeas.toIdxSubMeas P))
        (IdxSubMeas.liftLeft A) ε
        ⟨hε⟩
  have hmassP :
      idxSubMeasMass ψ 𝒟 LPf ≤
        idxSubMeasMass ψ 𝒟 (IdxSubMeas.liftLeft A) + 2 * Real.sqrt ε := by
    have hpost :
        idxSubMeasMass ψ 𝒟 LPf =
          idxSubMeasMass ψ 𝒟 (IdxProjSubMeas.toIdxSubMeas PL) := by
      unfold idxSubMeasMass subMeasMass avgOver LPf PL
      refine Finset.sum_congr rfl ?_
      intro q hq
      change
        𝒟.weight q *
            ev ψ (((postprocess ((P q).toSubMeas) (f q)).liftLeft).total) =
          𝒟.weight q * ev ψ ((((P q).toSubMeas).liftLeft).total)
      simp [SubMeas.liftLeft, postprocess_total]
    have hbase := hcomp.completenessTransfer
    rw [hpost]
    linarith
  have hmassA :
      idxSubMeasMass ψ 𝒟 RAf =
        idxSubMeasMass ψ 𝒟 (IdxSubMeas.liftLeft A) := by
    unfold idxSubMeasMass subMeasMass avgOver RAf
    refine Finset.sum_congr rfl ?_
    intro q hq
    change
      𝒟.weight q *
          ev ψ (rightTensor (ι₁ := ι) ((postprocess (A q) (f q)).total)) =
      𝒟.weight q * ev ψ (leftTensor (ι₂ := ι) ((A q).total))
    rw [postprocess_total, ← hperm.swap_ev ((A q).total)]
  have hcross_post_ge :
      avgOver 𝒟 crossPost ≥ avgOver 𝒟 crossOrig := by
    unfold avgOver crossPost crossOrig
    refine Finset.sum_le_sum ?_
    intro q hq
    exact mul_le_mul_of_nonneg_left
      (qMatchMass_leftRight_postprocess_ge ψ ((P q).toSubMeas) (A q) (f q))
      (𝒟.nonnegative q)
  have hcross_close :
      |avgOver 𝒟 crossOrig - avgOver 𝒟 overlapA| ≤ Real.sqrt ε := by
    simpa [crossOrig, overlapA, qMatchMass, IdxProjSubMeas.toIdxSubMeas,
      IdxSubMeas.liftLeft, IdxSubMeas.liftRight] using
      easyApproxFromApproxDelta ψ hψ 𝒟 h𝒟
        (IdxSubMeas.liftLeft (IdxProjSubMeas.toIdxSubMeas P))
        (IdxSubMeas.liftLeft A)
        (IdxSubMeas.liftRight A)
        ε
        ⟨hε⟩
  have hcross_ge :
      avgOver 𝒟 crossPost ≥ avgOver 𝒟 overlapA - Real.sqrt ε := by
    linarith [hcross_post_ge, (abs_le.mp hcross_close).1]
  have hssc_gap :
      idxSubMeasMass ψ 𝒟 (IdxSubMeas.liftLeft A) - avgOver 𝒟 overlapA ≤ δ := by
    rcases hssc with ⟨hssc⟩
    calc
      idxSubMeasMass ψ 𝒟 (IdxSubMeas.liftLeft A) - avgOver 𝒟 overlapA
        = avgOver 𝒟
            (fun q =>
              subMeasMass ψ ((IdxSubMeas.liftLeft A) q) - overlapA q) := by
              unfold idxSubMeasMass subMeasMass avgOver overlapA
              rw [← Finset.sum_sub_distrib]
              refine Finset.sum_congr rfl ?_
              intro q hq
              ring
      _ ≤ avgOver 𝒟 (fun q => qBipartiteSSCDefect ψ (A q)) := by
            apply avgOver_mono
            intro q
            have hdef :
                qBipartiteSSCDefect ψ (A q) =
                  max 0 (subMeasMass ψ ((IdxSubMeas.liftLeft A) q) - overlapA q) := by
              simp [qBipartiteSSCDefect, overlapA, qMatchMass, subMeasMass,
                IdxSubMeas.liftLeft, IdxSubMeas.liftRight,
                leftTensor_mul_rightTensor_eq_opTensor]
            rw [hdef]
            exact le_max_right 0 _
      _ ≤ δ := by
            simpa [bipartiteSSCError, overlapA, qMatchMass, IdxSubMeas.liftLeft,
              IdxSubMeas.liftRight] using hssc
  have hpointwise :
      ∀ q, qSDD ψ (LPf q) (RAf q) ≤
        subMeasMass ψ (LPf q) + subMeasMass ψ (RAf q) - 2 * crossPost q := by
    intro q
    let diagP : Error := ∑ b : β, ev ψ ((LPf q).outcome b * (LPf q).outcome b)
    let diagA : Error := ∑ b : β, ev ψ ((RAf q).outcome b * (RAf q).outcome b)
    have hdiagP_le :
        diagP ≤ subMeasMass ψ (LPf q) := by
      simpa [diagP, subMeasMass] using subMeas_diagMass_le_mass ψ (LPf q)
    have hdiagA_le :
        diagA ≤ subMeasMass ψ (RAf q) := by
      simpa [diagA, subMeasMass] using subMeas_diagMass_le_mass ψ (RAf q)
    have h_expand : qSDD ψ (LPf q) (RAf q) = diagP + diagA - 2 * crossPost q := by
      have hterm :
          ∀ b : β,
            ev ψ (((LPf q).outcome b - (RAf q).outcome b)ᴴ *
                ((LPf q).outcome b - (RAf q).outcome b)) =
              ev ψ ((LPf q).outcome b * (LPf q).outcome b) +
                ev ψ ((RAf q).outcome b * (RAf q).outcome b) -
                2 * ev ψ ((LPf q).outcome b * (RAf q).outcome b) := by
        intro b
        have hcomm :
            ev ψ ((RAf q).outcome b * (LPf q).outcome b) =
              ev ψ ((LPf q).outcome b * (RAf q).outcome b) := by
          exact
            ev_mul_comm_of_psd ψ _ _
              ((RAf q).outcome_pos b)
              ((LPf q).outcome_pos b)
        calc
          ev ψ (((LPf q).outcome b - (RAf q).outcome b)ᴴ *
              ((LPf q).outcome b - (RAf q).outcome b))
            =
              ev ψ
                ((((LPf q).outcome b * (LPf q).outcome b) -
                    (LPf q).outcome b * (RAf q).outcome b) -
                  ((RAf q).outcome b * (LPf q).outcome b -
                    (RAf q).outcome b * (RAf q).outcome b)) := by
                  congr 1
                  simp [sub_mul, mul_sub, SubMeas.outcome_hermitian]
                  abel
          _ =
              ev ψ ((LPf q).outcome b * (LPf q).outcome b) -
                ev ψ ((LPf q).outcome b * (RAf q).outcome b) -
                (ev ψ ((RAf q).outcome b * (LPf q).outcome b) -
                  ev ψ ((RAf q).outcome b * (RAf q).outcome b)) := by
                    rw [ev_sub, ev_sub, ev_sub]
          _ =
              ev ψ ((LPf q).outcome b * (LPf q).outcome b) +
                ev ψ ((RAf q).outcome b * (RAf q).outcome b) -
                2 * ev ψ ((LPf q).outcome b * (RAf q).outcome b) := by
                  rw [hcomm]
                  ring
      unfold qSDD qSDDCore crossPost
      calc
        ∑ b : β,
            ev ψ (((LPf q).outcome b - (RAf q).outcome b)ᴴ *
              ((LPf q).outcome b - (RAf q).outcome b))
          =
            ∑ b : β,
              (ev ψ ((LPf q).outcome b * (LPf q).outcome b) +
                ev ψ ((RAf q).outcome b * (RAf q).outcome b) -
                2 * ev ψ ((LPf q).outcome b * (RAf q).outcome b)) := by
                  refine Finset.sum_congr rfl ?_
                  intro b hb
                  exact hterm b
        _ = diagP + diagA - 2 * qMatchMass ψ (LPf q) (RAf q) := by
              unfold diagP diagA qMatchMass
              rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]
    rw [h_expand]
    linarith
  constructor
  calc
    sddError ψ 𝒟 LPf RAf
      ≤ avgOver 𝒟
          (fun q =>
            subMeasMass ψ (LPf q) + subMeasMass ψ (RAf q) - 2 * crossPost q) := by
              unfold sddError
              apply avgOver_mono
              intro q
              exact hpointwise q
    _ = idxSubMeasMass ψ 𝒟 LPf +
          idxSubMeasMass ψ 𝒟 RAf -
            2 * avgOver 𝒟 crossPost := by
              unfold idxSubMeasMass subMeasMass avgOver
              calc
                ∑ q ∈ 𝒟.support,
                    𝒟.weight q *
                      (ev ψ (LPf q).total + ev ψ (RAf q).total -
                        2 * crossPost q)
                  =
                    ∑ q ∈ 𝒟.support,
                      (𝒟.weight q * ev ψ (LPf q).total +
                        (𝒟.weight q * ev ψ (RAf q).total -
                          2 * (𝒟.weight q * crossPost q))) := by
                          refine Finset.sum_congr rfl ?_
                          intro q hq
                          ring
                _ =
                    (∑ q ∈ 𝒟.support, 𝒟.weight q * ev ψ (LPf q).total) +
                      ((∑ q ∈ 𝒟.support, 𝒟.weight q * ev ψ (RAf q).total) -
                        2 * ∑ q ∈ 𝒟.support, 𝒟.weight q * crossPost q) := by
                          rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
                _ = idxSubMeasMass ψ 𝒟 LPf +
                    idxSubMeasMass ψ 𝒟 RAf -
                      2 * avgOver 𝒟 crossPost := by
                          simp [idxSubMeasMass, avgOver, subMeasMass]
                          ring
    _ ≤
        (idxSubMeasMass ψ 𝒟 (IdxSubMeas.liftLeft A) + 2 * Real.sqrt ε) +
          idxSubMeasMass ψ 𝒟 (IdxSubMeas.liftLeft A) -
            2 * (avgOver 𝒟 overlapA - Real.sqrt ε) := by
              rw [hmassA]
              linarith
    _ ≤ 2 * δ + 4 * Real.sqrt ε := by
          linarith

end MIPStarRE.LDT.Preliminaries


