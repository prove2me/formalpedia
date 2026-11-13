-- Prove2me | Definitions.Def_Q260K055
-- name    : Q260K055
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-13T04:54:46.606836+00:00
-- url     : https://prove2.me/theorems/75ed87cf-c97f-4f30-8049-78f49e98adb5
-- title:
--   Definitions bundle Q260K055 of the split of OpenAI, Universal strong Kadison–Kastler stability (result family 289)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KadisonKastler.universal_strong_stability`, carved from OpenAI's openai/math development (OpenAI, *Universal strong Kadison–Kastler stability (result family 289)*, OpenAI Math Release, September 23, 2026, result family 289, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 14 declarations of OpenAI's Lean: 2 definitions and 12 theorems. The definitions and types are `OAI.Generator.Tracial.dimensionSpectralValue`, `OAI.Generator.Tracial.traceFreeDyadicSibling`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`FactorGeneration_Dimension`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/FactorGeneration/Dimension.lean), [`FactorGeneration_SpectralDimension`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/FactorGeneration/SpectralDimension.lean), [`FactorGeneration_SpectralStates`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/FactorGeneration/SpectralStates.lean).
--
--   **Imports.** It imports the bundles `Q260K009` and `Q260K010` of this split.
--
--   **Imported by** (directly, in this split): the bundle `Q260K056`; the statements `OAI_KadisonKastler_concrete_unitary_of_abelian_character_average`, `OAI_KadisonKastler_coreTraceOriginal_gauge_balance`, `OAI_KadisonKastler_uniform_common_action_of_frequency_defects` and `OAI_KadisonKastler_vector_bicentralizer_scalar_of_modular_coisometries`; the proofs of `OAI_KadisonKastler_concrete_unitary_of_abelian_character_average`, `OAI_KadisonKastler_exists_commutant_projection_of_finite_gap`, `OAI_KadisonKastler_exists_finite_uniform_pinching_gap`, `OAI_KadisonKastler_exists_selfAdjoint_split_of_factor`, `OAI_KadisonKastler_reverse_nearInclusion_reducing_commutants_after_alignment`, `OAI_KadisonKastler_uniform_common_action_of_frequency_defects` and `OAI_KadisonKastler_vector_bicentralizer_scalar_of_modular_coisometries`.
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
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.WeakOperatorTopology
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.LocallyConvex.WeakSpace
import Mathlib.Analysis.Normed.Module.Basic
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
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Topology.Algebra.Algebra
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Instances.Complex
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Order
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Sequences
import Definitions.Def_Q260K009
import Definitions.Def_Q260K010

section
-- module Solutions.OAIQ075_KS.FactorGeneration_Dimension
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.instFintypeSignedPermutation _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator

/-! Archimedean comparison for the constructed dyadic reference projections.
Orthogonal sibling corners supply copies for the finite-algebra shift argument. -/
section
namespace Tracial
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)

def traceFreeDyadicSibling (p : AlgebraProjection M) (n : ℕ) : AlgebraProjection M :=
  ((traceFreeDyadicPartition hfactor hdiff p (n+1)).leg (dyadicFalseIndex n,true)).target

theorem traceFreeDyadicReference_antitone (p : AlgebraProjection M) :
    Antitone (traceFreeDyadicReference hfactor hdiff p) := by
  apply antitone_nat_of_succ_le
  intro n
  exact traceFreeDyadic_child_le hfactor hdiff p n (dyadicFalseIndex n) false

end Tracial

end

/-! Finite rounding by actual subset projections. A maximal fitting subset
leaves a remainder smaller in comparison than any unused equivalent piece. -/

/-! Classification of projection comparison by the constructed finite
dimension, and a wrapper for exactly the original IsII1Factor predicate.
No normality or trace-extension claim is made here. -/

/-! Bounds and concrete dyadic upper approximants for the constructed
projection dimension. These finite estimates do not assume continuity. -/

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_SpectralDimension
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.functionalSubspaceWeakScalarTower _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.algebraCStarAlgebra _root_.OAI.KadisonKastler.instFintypeSignedPermutation _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.varyingSequenceCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedAlgebraComplexSubtypeMemNonUnitalStarSubalgebra _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.Generator.Tracial.cyclicCoefficient_apply _root_.OAI.Generator.Tracial.cyclicPredualEvaluation_apply _root_.OAI.KadisonKastler.FullMatrixCorner.ofEquivalentProjectionFamily_entry _root_.OAI.KadisonKastler.ScalarInvariantMean.algebraMean_coe _root_.OAI.KadisonKastler.ambientAlgebraFamily_apply _root_.OAI.KadisonSimilarity.concretePredualEquiv_symm_apply _root_.OAI.KadisonSimilarity.dyadicCornerHom_coe _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.normalCoefficient_apply _root_.OAI.KadisonSimilarity.predualCoefficient_apply _root_.OAI.KadisonSimilarity.predualEvaluation_apply _root_.OAI.KadisonSimilarity.predualRestriction_apply _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Finite spectral weights of the constructed projection dimension obey an
operator-norm bound. No linear trace on noncommuting elements is assumed. -/

/-! Construct the unique real spectral dimension value of each self-adjoint
operator by norm approximation. Global noncommuting additivity is not asserted. -/
section
open Filter
open scoped BigOperators Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

include hfinite in
/-- Actual finite spectral approximants are Cauchy in their dimension values,
and their real limit controls every commuting spectral approximation. -/
theorem traceFreeDimension_exists_spectral_value
    (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (x : M.toStarSubalgebra) (hx : IsSelfAdjoint x) :
    ∃ t : ℂ, t.im=0 ∧ IsDimensionSpectralValue hfactor hdiff x t := by
  classical
  have happrox (n : ℕ) :
      ∃ (Q : CornerPartition (⟨1,IsStarProjection.one _⟩ : AlgebraProjection M))
        (c : Fin Q.size → ℝ),
        (∀ y : M.toStarSubalgebra, Commute x y → ∀ i, Commute (Q.piece i).val y) ∧
        ‖x-∑ i, (c i : ℂ) • (Q.piece i).val‖ < 1/2^n := by
    obtain ⟨Q,c,_,hQ,herr⟩ := exists_finite_spectral_approximation_preserving_commutant
      ⟨1,IsStarProjection.one _⟩ x hx (1/2^n) (by positivity)
    exact ⟨Q,c,fun y hy => hQ y hy (Commute.one_left y),by simpa only [one_mul,mul_one] using herr⟩
  choose Q c hQ herr using happrox
  let f (n : ℕ) : ℂ := ∑ i, (c n i : ℂ)*(traceFreeDimension hfactor hdiff ((Q n).piece i) : ℂ)
  let a (n : ℕ) : M.toStarSubalgebra := ∑ i, (c n i : ℂ) • ((Q n).piece i).val
  have hbound (n : ℕ) (R : CornerPartition (⟨1,IsStarProjection.one _⟩ : AlgebraProjection M))
      (d : Fin R.size → ℂ) (hR : ∀ j, Commute (R.piece j).val x) :
      ‖f n-∑ j, d j*(traceFreeDimension hfactor hdiff (R.piece j) : ℂ)‖ ≤
        1/2^n+‖x-∑ j, d j • (R.piece j).val‖ := by
    have hc (i : Fin (Q n).size) (j : Fin R.size) :
        Commute ((Q n).piece i).val (R.piece j).val := hQ n _ (hR j).symm i
    have h := (Q n).dimension_weight_cross_norm_le hfactor hdiff hfinite R hc hunit
      (fun i => (c n i : ℂ)) d
    refine h.trans ?_
    have htri := dist_triangle (a n) x (∑ j, d j • (R.piece j).val)
    simp only [dist_eq_norm] at htri
    rw [norm_sub_rev (a n) x] at htri
    exact htri.trans (add_le_add (herr n).le le_rfl)
  have heps : Tendsto (fun n : ℕ => (1 : ℝ)/2^n) atTop (𝓝 0) := by
    simpa only [one_div_pow] using tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ)<1)
  have hf : CauchySeq f := by
    apply Metric.cauchySeq_iff.mpr
    intro ε hε
    obtain ⟨N,hN⟩ := eventually_atTop.mp (heps.eventually (gt_mem_nhds (half_pos hε)))
    refine ⟨N,?_⟩
    intro m hm n hn
    rw [dist_eq_norm]
    have h := hbound m (Q n) (fun i => (c n i : ℂ)) (hQ n x (Commute.refl x))
    have he := herr n
    have hm' := hN m hm
    have hn' := hN n hn
    change ‖f m-f n‖ ≤ _ at h
    linarith
  obtain ⟨t,ht⟩ := cauchySeq_tendsto_of_complete hf
  have him (n : ℕ) : (f n).im=0 := by simp [f]
  refine ⟨t,?_,?_⟩
  · have hi := Complex.continuous_im.tendsto t |>.comp ht
    exact tendsto_nhds_unique hi (by
      change Tendsto (fun n => (f n).im) atTop (𝓝 0)
      simpa only [him] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)))
  · intro R d hR
    apply le_of_tendsto_of_tendsto' ((ht.sub_const _).norm)
      (by simpa only [zero_add] using heps.add_const ‖x-∑ j, d j • (R.piece j).val‖)
    exact fun n => hbound n R d hR

/-- This is a constructed scalar value on self-adjoint operators; it is not
yet packaged as a linear functional. -/
def dimensionSpectralValue (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (x : M.toStarSubalgebra) (hx : IsSelfAdjoint x) : ℂ :=
  (traceFreeDimension_exists_spectral_value hfactor hdiff hfinite hunit x hx).choose

theorem dimensionSpectralValue_spec (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (x : M.toStarSubalgebra) (hx : IsSelfAdjoint x) :
    (dimensionSpectralValue hfactor hdiff hfinite hunit x hx).im=0 ∧
      IsDimensionSpectralValue hfactor hdiff x
        (dimensionSpectralValue hfactor hdiff hfinite hunit x hx) :=
  (traceFreeDimension_exists_spectral_value hfactor hdiff hfinite hunit x hx).choose_spec

end

/-! The constructed spectral value is bounded and extends the actual
projection dimension. These laws do not assert noncommuting additivity. -/
section
open scoped BigOperators
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

theorem dimensionSpectralValue_norm_le (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (x : M.toStarSubalgebra) (hx : IsSelfAdjoint x) :
    ‖dimensionSpectralValue hfactor hdiff hfinite hunit x hx‖ ≤ ‖x‖ :=
  (dimensionSpectralValue_spec hfactor hdiff hfinite hunit x hx).2.norm_le hfactor hdiff

theorem dimensionSpectralValue_projection (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (p : AlgebraProjection M) :
    dimensionSpectralValue hfactor hdiff hfinite hunit p.val p.property.isSelfAdjoint=
      (traceFreeDimension hfactor hdiff p : ℂ) :=
  (dimensionSpectralValue_spec hfactor hdiff hfinite hunit p.val p.property.isSelfAdjoint).2.on_projection
    hfactor hdiff p

end

/-! Finite-family tests and real homogeneity for the constructed spectral value.
These statements do not assert additivity for noncommuting operators. -/
open scoped BigOperators
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

theorem dimensionSpectralValue_eq_of_approximants
    (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (x : M.toStarSubalgebra) (hx : IsSelfAdjoint x) (t : ℂ)
    (h : ∀ ε : ℝ, 0 < ε →
      ∃ (Q : CornerPartition (⟨1,IsStarProjection.one _⟩ : AlgebraProjection M))
        (c : Fin Q.size → ℂ),
        (∀ i, Commute (Q.piece i).val x) ∧
        ‖x-∑ i, c i • (Q.piece i).val‖ < ε ∧
        ‖t-∑ i, c i*(traceFreeDimension hfactor hdiff (Q.piece i) : ℂ)‖ < ε) :
    dimensionSpectralValue hfactor hdiff hfinite hunit x hx=t := by
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  apply le_antisymm ?_ (norm_nonneg _)
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨Q,c,hc,hxerr,hterr⟩ := h (ε/2) (half_pos hε)
  have hxval := (dimensionSpectralValue_spec hfactor hdiff hfinite hunit x hx).2 Q c hc
  have htri := dist_triangle
    (dimensionSpectralValue hfactor hdiff hfinite hunit x hx)
    (∑ i, c i*(traceFreeDimension hfactor hdiff (Q.piece i) : ℂ)) t
  simp only [dist_eq_norm] at htri
  rw [norm_sub_rev (∑ i, c i*(traceFreeDimension hfactor hdiff (Q.piece i) : ℂ)) t] at htri
  linarith

theorem dimensionSpectralValue_real_smul
    (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (r : ℝ) (x : M.toStarSubalgebra) (hx : IsSelfAdjoint x) :
    dimensionSpectralValue hfactor hdiff hfinite hunit (r • x) ((IsSelfAdjoint.all r).smul hx)=
      (r : ℂ)*dimensionSpectralValue hfactor hdiff hfinite hunit x hx := by
  apply dimensionSpectralValue_eq_of_approximants hfactor hdiff hfinite hunit
  intro ε hε
  have hr : 0 < ‖r‖+1 := by positivity
  obtain ⟨Q,c,_,hQ,herr⟩ := exists_finite_spectral_approximation_preserving_commutant
    ⟨1,IsStarProjection.one _⟩ x hx (ε/(‖r‖+1)) (div_pos hε hr)
  simp only [one_mul,mul_one] at herr
  have hc := hQ x (Commute.refl x) (Commute.one_left x)
  have hval := (dimensionSpectralValue_spec hfactor hdiff hfinite hunit x hx).2
    Q (fun i => (c i : ℂ)) hc
  have hb : ‖r‖*(ε/(‖r‖+1)) < ε := by
    have hh := (div_pos hε hr)
    have he : (‖r‖+1)*(ε/(‖r‖+1))=ε := mul_div_cancel₀ _ (ne_of_gt hr)
    nlinarith
  refine ⟨Q,fun i => (r : ℂ)*(c i : ℂ),?_,?_,?_⟩
  · intro i
    show (Q.piece i).val*(r • x)=(r • x)*(Q.piece i).val
    rw [mul_smul_comm,smul_mul_assoc,(hc i).eq]
  · have he : (r • x)-∑ i, ((r : ℂ)*(c i : ℂ)) • (Q.piece i).val=
        r • (x-∑ i, (c i : ℂ) • (Q.piece i).val) := by
      simp only [smul_sub,Finset.smul_sum,← smul_assoc,Complex.real_smul]
    rw [he,norm_smul]
    exact (mul_le_mul_of_nonneg_left herr.le (norm_nonneg r)).trans_lt hb
  · rw [show (∑ i, ((r : ℂ)*(c i : ℂ))*(traceFreeDimension hfactor hdiff (Q.piece i) : ℂ))=
        (r : ℂ)*(∑ i, (c i : ℂ)*(traceFreeDimension hfactor hdiff (Q.piece i) : ℂ)) by
          rw [Finset.mul_sum]; simp only [mul_assoc],← mul_sub,norm_mul,Complex.norm_real]
    exact (mul_le_mul_of_nonneg_left (hval.trans herr.le) (norm_nonneg r)).trans_lt hb

theorem dimensionSpectralValue_zero (hunit : (1 : M.toStarSubalgebra) ≠ 0) :
    dimensionSpectralValue hfactor hdiff hfinite hunit 0 (IsSelfAdjoint.zero _)=0 := by
  have h := dimensionSpectralValue_norm_le hfactor hdiff hfinite hunit 0 (IsSelfAdjoint.zero _)
  rw [norm_zero] at h
  exact norm_eq_zero.mp (le_antisymm h (norm_nonneg _))

theorem dimensionSpectralValue_neg (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (x : M.toStarSubalgebra) (hx : IsSelfAdjoint x) :
    dimensionSpectralValue hfactor hdiff hfinite hunit (-x) hx.neg=
      -dimensionSpectralValue hfactor hdiff hfinite hunit x hx := by
  simpa only [neg_one_smul,Complex.ofReal_neg,Complex.ofReal_one,neg_one_mul] using
    dimensionSpectralValue_real_smul hfactor hdiff hfinite hunit (-1) x hx

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_SpectralStates
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealPartialOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.functionalSubspaceWeakScalarTower _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.algebraCStarAlgebra _root_.OAI.KadisonKastler.instFintypeSignedPermutation _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.varyingSequenceCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedAlgebraComplexSubtypeMemNonUnitalStarSubalgebra _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instPartialOrderSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerPartialOrder _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Additivity on commuting self-adjoint operators, proved using actual common
spectral refinements. The commutation hypothesis is essential to this proof. -/
open scoped BigOperators

/-! Positive spectral approximants, positivity of the constructed scalar, and
order preservation on commuting self-adjoint operators. -/
open scoped BigOperators CStarAlgebra
section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

attribute [local instance] OAI.Generator.Tracial.spectralValueStarOrder
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

attribute [local instance] OAI.Generator.Tracial.spectralValueCStar
attribute [local instance] OAI.Generator.Tracial.spectralValueOrder
attribute [local instance] OAI.Generator.Tracial.spectralValuePreorder
attribute [local instance] OAI.Generator.Tracial.spectralValueLE
theorem dimensionSpectralValue_nonneg
    (hunit : (1 : M.toStarSubalgebra) ≠ 0) (x : M.toStarSubalgebra) (hx : 0 ≤ x) :
    0 ≤ (dimensionSpectralValue hfactor hdiff hfinite hunit x hx.isSelfAdjoint).re := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨Q,c,hc,hQ,herr⟩ := exists_positive_spectral_approximation x hx ε hε
  have hval := (dimensionSpectralValue_spec hfactor hdiff hfinite hunit x hx.isSelfAdjoint).2
    Q (fun i => (c i : ℂ)) (hQ x (Commute.refl x))
  let t := dimensionSpectralValue hfactor hdiff hfinite hunit x hx.isSelfAdjoint
  let w : ℝ := ∑ i, c i*traceFreeDimension hfactor hdiff (Q.piece i)
  have hw : 0 ≤ w := Finset.sum_nonneg (fun i _ => mul_nonneg (hc i)
    (traceFreeDimension_nonneg hfactor hdiff _))
  have he : (w : ℂ)=∑ i, (c i : ℂ)*(traceFreeDimension hfactor hdiff (Q.piece i) : ℂ) := by
    simp only [w,Complex.ofReal_sum,Complex.ofReal_mul]
  have hb : ‖t-(w : ℂ)‖ < ε := by rw [he]; exact hval.trans_lt herr
  have hre := Complex.re_le_norm ((w : ℂ)-t)
  rw [Complex.sub_re,Complex.ofReal_re,norm_sub_rev (w : ℂ) t] at hre
  change 0 ≤ t.re+ε
  linarith

end

/-! A nonzero positive operator dominates a positive multiple of an actual
nonzero spectral projection. This proves faithfulness without linearity. -/
open scoped CStarAlgebra

/-! Unitary conjugacy preserves projection dimension and its constructed
spectral extension. No trace identity is assumed. -/
open scoped BigOperators
section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

theorem dimensionSpectralValue_unitary_conjugate
    (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (u : unitary M.toStarSubalgebra) (x : M.toStarSubalgebra) (hx : IsSelfAdjoint x) :
    dimensionSpectralValue hfactor hdiff hfinite hunit
      (Unitary.conjStarAlgAut ℂ M.toStarSubalgebra u x)
      (hx.map (Unitary.conjStarAlgAut ℂ M.toStarSubalgebra u))=
      dimensionSpectralValue hfactor hdiff hfinite hunit x hx := by
  classical
  let φ := Unitary.conjStarAlgAut ℂ M.toStarSubalgebra u
  have hnorm (a : M.toStarSubalgebra) : ‖φ a‖=‖a‖ := by
    change ‖((u : M.toStarSubalgebra)*a)*(star u : unitary M.toStarSubalgebra)‖=‖a‖
    rw [CStarRing.norm_mul_coe_unitary,CStarRing.norm_coe_unitary_mul]
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  apply le_antisymm ?_ (norm_nonneg _)
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨Q,c,_,hQ,herr⟩ := exists_finite_spectral_approximation_preserving_commutant
    ⟨1,IsStarProjection.one _⟩ x hx (ε/2) (half_pos hε)
  simp only [one_mul,mul_one] at herr
  have hc := hQ x (Commute.refl x) (Commute.one_left x)
  let q (i : Fin Q.size) := (Q.piece i).unitaryConjugate u
  have ho (i j : Fin Q.size) (hij : i≠j) : (q i).val*(q j).val=0 := by
    change φ (Q.piece i).val*φ (Q.piece j).val=0
    exact (map_mul φ (Q.piece i).val (Q.piece j).val).symm.trans
      ((congrArg φ (Q.orthogonal i j hij)).trans (map_zero φ))
  have hs : (∑ i, (q i).val)=(1 : M.toStarSubalgebra) := by
    change (∑ i, φ (Q.piece i).val)=1
    exact (map_sum φ (fun i => (Q.piece i).val) Finset.univ).symm.trans
      ((congrArg φ Q.total).trans (map_one φ))
  have hcomm (i : Fin Q.size) : Commute (q i).val (φ x) :=
    (hc i).map φ
  have hmap : (∑ i, (c i : ℂ) • (q i).val)=φ (∑ i, (c i : ℂ) • (Q.piece i).val) := by
    change (∑ i, (c i : ℂ) • φ (Q.piece i).val)=_
    simp only [map_sum,map_smul]
  have hval := (dimensionSpectralValue_spec hfactor hdiff hfinite hunit (φ x) (hx.map φ)).2.family_bound
    hfactor hdiff q ho hs (fun i => (c i : ℂ)) hcomm
  have hweight : (∑ i, (c i : ℂ)*(traceFreeDimension hfactor hdiff (q i) : ℂ))=
      ∑ i, (c i : ℂ)*(traceFreeDimension hfactor hdiff (Q.piece i) : ℂ) := by
    simp only [q,traceFreeDimension_unitaryConjugate hfactor hdiff]
  have hval' :
      ‖dimensionSpectralValue hfactor hdiff hfinite hunit (φ x) (hx.map φ) -
        ∑ i, (c i : ℂ) * (traceFreeDimension hfactor hdiff (Q.piece i) : ℂ)‖ ≤
      ‖x - ∑ i, (c i : ℂ) • (Q.piece i).val‖ := by
    calc
      _ = ‖dimensionSpectralValue hfactor hdiff hfinite hunit (φ x) (hx.map φ) -
          ∑ i, (c i : ℂ) * (traceFreeDimension hfactor hdiff (q i) : ℂ)‖ :=
        congrArg (fun z : ℂ => ‖dimensionSpectralValue hfactor hdiff hfinite hunit
          (φ x) (hx.map φ) - z‖) hweight.symm
      _ ≤ ‖φ x - ∑ i, (c i : ℂ) • (q i).val‖ := hval
      _ = ‖φ (x - ∑ i, (c i : ℂ) • (Q.piece i).val)‖ :=
        congrArg (fun z : M.toStarSubalgebra => ‖z‖)
          ((congrArg (fun z => φ x - z) hmap).trans (map_sub φ x _).symm)
      _ = _ := hnorm _
  have hxval := (dimensionSpectralValue_spec hfactor hdiff hfinite hunit x hx).2
    Q (fun i => (c i : ℂ)) hc
  have htri := dist_triangle
    (dimensionSpectralValue hfactor hdiff hfinite hunit (φ x) (hx.map φ))
    (∑ i, (c i : ℂ)*(traceFreeDimension hfactor hdiff (Q.piece i) : ℂ))
    (dimensionSpectralValue hfactor hdiff hfinite hunit x hx)
  simp only [dist_eq_norm] at htri
  rw [norm_sub_rev (∑ i, (c i : ℂ)*(traceFreeDimension hfactor hdiff (Q.piece i) : ℂ))
    (dimensionSpectralValue hfactor hdiff hfinite hunit x hx)] at htri
  change ‖dimensionSpectralValue hfactor hdiff hfinite hunit (φ x) (hx.map φ)-
    dimensionSpectralValue hfactor hdiff hfinite hunit x hx‖ ≤ 0+ε
  linarith only [htri,hval',hxval,herr]

end

/-! The constructed scalar agrees on x*x and xx*, by an actual unitary polar
decomposition. This is a quadratic identity, not unrestricted additivity. -/
open scoped CStarAlgebra
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
attribute [local instance] OAI.Generator.Tracial.spectralSquareStarOrder
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

attribute [local instance] OAI.Generator.Tracial.spectralSquareCStar
attribute [local instance] OAI.Generator.Tracial.spectralSquareOrder
theorem dimensionSpectralValue_star_mul_self
    (hunit : (1 : M.toStarSubalgebra) ≠ 0) (x : M.toStarSubalgebra) :
    dimensionSpectralValue hfactor hdiff hfinite hunit (star x*x) (IsSelfAdjoint.star_mul_self x)=
      dimensionSpectralValue hfactor hdiff hfinite hunit (x*star x) (IsSelfAdjoint.mul_star_self x) := by
  obtain ⟨u,hu⟩ := exists_unitary_polar_decomposition hfactor hfinite x
  let a := CFC.sqrt (star x*x)
  have ha : star a=a := (CFC.sqrt_nonneg _).isSelfAdjoint.star_eq
  have haa : a*a=star x*x := CFC.sqrt_mul_sqrt_self _ (star_mul_self_nonneg _)
  have he : Unitary.conjStarAlgAut ℂ M.toStarSubalgebra u (star x*x)=x*star x := by
    change (u : M.toStarSubalgebra)*(star x*x)*star (u : M.toStarSubalgebra)=x*star x
    calc _ = ((u : M.toStarSubalgebra)*a)*star ((u : M.toStarSubalgebra)*a) := by
           rw [star_mul,ha,← haa]
           simp only [mul_assoc]
      _ = x*star x := by rw [hu]
  have h := dimensionSpectralValue_unitary_conjugate hfactor hdiff hfinite hunit
    u (star x*x) (IsSelfAdjoint.star_mul_self x)
  simpa only [he] using h.symm

end Generator.Tracial

end

end OAI
end


