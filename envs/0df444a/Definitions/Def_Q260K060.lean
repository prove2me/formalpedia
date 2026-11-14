-- Prove2me | Definitions.Def_Q260K060
-- name    : Q260K060
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-13T06:33:01.722195+00:00
-- url     : https://prove2.me/theorems/901a622d-55fd-41e3-8302-cd4f3ef3ce6c
-- title:
--   Definitions bundle Q260K060 of the split of OpenAI, Universal strong Kadison–Kastler stability (result family 289)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KadisonKastler.universal_strong_stability`, carved from OpenAI's openai/math development (OpenAI, *Universal strong Kadison–Kastler stability (result family 289)*, OpenAI Math Release, September 23, 2026, result family 289, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 8 declarations of OpenAI's Lean: 8 theorems.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`FactorGeneration_TraceHilbert`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/FactorGeneration/TraceHilbert.lean).
--
--   **Imports.** It imports the bundle `Q260K059` of this split.
--
--   **Imported by** (directly, in this split): the bundle `Q260K026`; the statement `OAI_KadisonKastler_uniform_typeIII_selfAdjoint_infinitesimal_estimate`; the proof of `OAI_KadisonKastler_uniform_typeIII_selfAdjoint_infinitesimal_estimate`.
-- source:
--   OpenAI, Universal strong Kadison–Kastler stability (result family 289), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 289; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-strong-Kadison-Kastler-stability-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.WeakOperatorTopology
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.LocallyConvex.SeparatingDual
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.LocallyConvex.WeakDual
import Mathlib.Analysis.LocallyConvex.WeakSpace
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Module.RCLike.Extend
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Order.Filter.AtTopBot.Prod
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Order.Zorn
import Mathlib.RingTheory.Congruence.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Topology.Algebra.Algebra
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Instances.Complex
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Order
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.UniformApproximation
import Definitions.Def_Q260K059

section
-- module Solutions.OAIQ075_KS.FactorGeneration_TraceHilbert
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.boundedSequenceCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instFintypeSignedPermutation _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! A separate type with the constructed trace inner product. Its norm is the
trace two-norm; the original concrete algebra retains its operator norm.
Lean's inner product is linear in the second argument. -/

/-! The trace two-norm bound for left multiplication uses the original
operator norm and positivity of a concrete sandwich. -/

/-! Bounded left multiplication on the actual constructed trace Hilbert space.
All representation laws are proved on its dense algebraic subspace. -/

/-! Bounded right multiplication and its commutation with the constructed
left action. These supply separation on the actual double commutant. -/
section
open scoped ComplexConjugate CStarAlgebra
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
attribute [local instance] OAI.Generator.Tracial.traceHilbertRightCStar
local instance traceHilbertRightOrder_r0d281d_1 : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance traceHilbertRightStarOrder_r0d281d_1 : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)
variable (hunit : (1 : M.toStarSubalgebra) ≠ 0)

local notation "K" => TraceFreeHilbert hfactor hdiff hfinite hunit

local notation "π" => traceFreeHilbertAction hfactor hdiff hfinite hunit

local notation "R" => traceFreeRightAction hfactor hdiff hfinite hunit

local instance traceHilbertRightOperatorCStar_r0d281d_1 : CStarAlgebra (K →L[ℂ] K) := {}
theorem traceFreeLeftRight_commute (a b : M.toStarSubalgebra) : π a*R b = R b*π a := by
  ext x
  refine UniformSpace.Completion.induction_on x (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro c
  change traceFreeLeftAction hfactor hdiff hfinite hunit a (R b (c : K)) =
    R b (traceFreeLeftAction hfactor hdiff hfinite hunit a (c : K))
  simp only [traceFreeLeftAction_coe,traceFreeRightAction_coe,mul_assoc]

end

/-! The actual double commutant of the new representation, with a constructed
faithful tracial vector. Equality with the original image is a later theorem. -/
section
open Filter
open scoped ComplexConjugate CStarAlgebra Pointwise Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
local instance traceHilbertClosureCStar_r0d281d_1 : CStarAlgebra M.toStarSubalgebra := {}
local instance traceHilbertClosureOrder_r0d281d_1 : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance traceHilbertClosureStarOrder_r0d281d_1 : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)
variable (hunit : (1 : M.toStarSubalgebra) ≠ 0)

local notation "K" => TraceFreeHilbert hfactor hdiff hfinite hunit

local notation "π" => traceFreeHilbertAction hfactor hdiff hfinite hunit
local notation "Ω" => traceFreeHilbertVector hfactor hdiff hfinite hunit

local notation "N" => traceFreeHilbertClosure hfactor hdiff hfinite hunit

attribute [local instance] OAI.Generator.Tracial.traceHilbertClosureOperatorCStar
theorem traceFreeHilbertClosure_strong_net (T : (N).toStarSubalgebra) :
    ∃ a : Finset K × ℕ → M.toStarSubalgebra, ∀ x : K,
      Tendsto (fun d => π (a d) x) atTop (𝓝 (T.val x)) := by
  obtain ⟨b,hb⟩ := bicommutant_exists_strong_net (π).range T.val
    ((traceFreeHilbertClosure_mem_iff hfactor hdiff hfinite hunit T.val).mp T.property)
  have hex (d : Finset K × ℕ) : ∃ a : M.toStarSubalgebra, π a = (b d).val := (b d).property
  choose a ha using hex
  exact ⟨a,fun x => by simpa only [ha] using hb x⟩

theorem traceFreeHilbertClosure_right_commute (T : (N).toStarSubalgebra) (a : M.toStarSubalgebra) :
    traceFreeRightAction hfactor hdiff hfinite hunit a*T.val =
      T.val*traceFreeRightAction hfactor hdiff hfinite hunit a := by
  apply (traceFreeHilbertClosure_mem_iff hfactor hdiff hfinite hunit T.val).mp T.property
  rintro B ⟨b,rfl⟩
  exact traceFreeLeftRight_commute hfactor hdiff hfinite hunit b a

theorem traceFreeHilbertClosure_separating (T : (N).toStarSubalgebra) (hT : T.val Ω = 0) : T = 0 := by
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  change ∀ x : K, T.val x = (0 : K)
  apply isClosed_property (traceFreeHilbertAction_cyclic hfactor hdiff hfinite hunit)
    (isClosed_eq T.val.continuous continuous_const)
  intro a
  rw [traceFreeHilbertAction_vector,← traceFreeRightAction_vector hfactor hdiff hfinite hunit a]
  have he := congrArg (fun B : K →L[ℂ] K => B Ω)
    (traceFreeHilbertClosure_right_commute hfactor hdiff hfinite hunit T a)
  simpa only [mul_apply_eq_comp,hT,map_zero] using he.symm

theorem traceFreeHilbertClosure_trace_commute_copy (T : (N).toStarSubalgebra) (b : M.toStarSubalgebra) :
    inner ℂ Ω (T.val (π b Ω)) = inner ℂ Ω (π b (T.val Ω)) := by
  classical
  obtain ⟨a,ha⟩ := traceFreeHilbertClosure_strong_net hfactor hdiff hfinite hunit T
  have he (d : Finset K × ℕ) : inner ℂ Ω (π (a d) (π b Ω)) =
      inner ℂ Ω (π b (π (a d) Ω)) := by
    change inner ℂ Ω ((π (a d)*π b) Ω) = inner ℂ Ω ((π b*π (a d)) Ω)
    rw [← map_mul,← map_mul,traceFreeHilbertAction_trace,traceFreeHilbertAction_trace]
    exact (traceFreeTrace_spec hfactor hdiff hfinite hunit).2.2.2.2 _ _
  have hl := (innerSL ℂ Ω).continuous.continuousAt.tendsto.comp (ha (π b Ω))
  have hr := ((innerSL ℂ Ω).comp (π b)).continuous.continuousAt.tendsto.comp (ha Ω)
  exact tendsto_nhds_unique hl (hr.congr (fun d => (he d).symm))

end

/-! The constructed representation is WOT continuous on every original
operator-norm ball. This does not assert whole-carrier WOT continuity. -/
open scoped ComplexConjugate CStarAlgebra BigOperators
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
attribute [local instance] OAI.Generator.Tracial.traceHilbertWOTCStar
local instance traceHilbertWOTOrder_r0d281d_1 : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance traceHilbertWOTStarOrder_r0d281d_1 : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)
variable (hunit : (1 : M.toStarSubalgebra) ≠ 0)

local notation "copy" => traceFreeCopy hfactor hdiff hfinite hunit

local notation "K" => TraceFreeHilbert hfactor hdiff hfinite hunit
local notation "ι" => traceFreeInclusion hfactor hdiff hfinite hunit

local notation "π" => traceFreeHilbertAction hfactor hdiff hfinite hunit

attribute [local instance] OAI.Generator.Tracial.traceHilbertWOTOperatorCStar
theorem traceFreeHilbertCoefficient_copy_ball_continuous (C : ℝ) (a b : M.toStarSubalgebra) :
    Continuous (fun T : weakOperatorBall M C =>
      traceFreeHilbertCoefficient hfactor hdiff hfinite hunit (ι (copy a)) (ι (copy b))
        ⟨T.val.toCLM,T.property.1⟩) := by
  obtain ⟨n,ξ,η,ht⟩ := traceFreeTrace_finite_vector_representation hfactor hdiff hfinite hunit
  have he (T : weakOperatorBall M C) :
      traceFreeHilbertCoefficient hfactor hdiff hfinite hunit (ι (copy a)) (ι (copy b))
        ⟨T.val.toCLM,T.property.1⟩ = ∑ i, inner ℂ (b.val (η i)) (T.val (a.val (ξ i))) := by
    rw [traceFreeHilbertCoefficient_apply,traceFreeHilbertAction_inclusion,traceFreeInclusion_inner,ht]
    apply Finset.sum_congr rfl
    intro i _
    change inner ℂ (η i) ((star b.val) (T.val (a.val (ξ i)))) = _
    rw [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_right]
  simp_rw [he]
  exact continuous_finsetSum _ (fun i _ =>
    ContinuousLinearMapWOT.continuous_inner_apply continuous_subtype_val (a.val (ξ i)) (b.val (η i)))

theorem traceFreeHilbertCoefficient_ball_continuous (C : ℝ) (x y : K) :
    Continuous (fun T : weakOperatorBall M C =>
      inner ℂ y (π ⟨T.val.toCLM,T.property.1⟩ x)) := by
  have hd : DenseRange (fun a : M.toStarSubalgebra => ι (copy a)) := by
    simpa only [traceFreeHilbertAction_vector] using
      traceFreeHilbertAction_cyclic hfactor hdiff hfinite hunit
  have hc := (ballContinuousFunctionals_isClosed M C).preimage
    (traceFreeHilbertCoefficient_continuous hfactor hdiff hfinite hunit)
  have hm : ∀ p : K × K,
      traceFreeHilbertCoefficient hfactor hdiff hfinite hunit p.1 p.2 ∈ ballContinuousFunctionals M C := by
    apply isClosed_property (hd.prodMap hd) hc
    intro p
    exact traceFreeHilbertCoefficient_copy_ball_continuous hfactor hdiff hfinite hunit C p.1 p.2
  exact hm (x,y)

theorem traceFreeHilbertBallMap_continuous (C : ℝ) :
    Continuous (traceFreeHilbertBallMap hfactor hdiff hfinite hunit C) :=
  ContinuousLinearMapWOT.continuous_iff.mpr
    (traceFreeHilbertCoefficient_ball_continuous hfactor hdiff hfinite hunit C)

end Generator.Tracial

end

end OAI
end


