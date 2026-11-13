-- Prove2me | Definitions.Def_Q260K057
-- name    : Q260K057
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-13T05:29:54.932947+00:00
-- url     : https://prove2.me/theorems/b8bf89b9-614f-4ca9-820f-73f96a0b09fe
-- title:
--   Definitions bundle Q260K057 of the split of OpenAI, Universal strong Kadison–Kastler stability (result family 289)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KadisonKastler.universal_strong_stability`, carved from OpenAI's openai/math development (OpenAI, *Universal strong Kadison–Kastler stability (result family 289)*, OpenAI Math Release, September 23, 2026, result family 289, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 16 declarations of OpenAI's Lean: 2 definitions, 2 instances and 12 theorems. The definitions and types are `OAI.Generator.Tracial.TraceFreeHilbert`, `OAI.Generator.Tracial.traceFreeInnerCore`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`FactorGeneration_NormalTrace`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/FactorGeneration/NormalTrace.lean), [`FactorGeneration_SpectralStates`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/FactorGeneration/SpectralStates.lean), [`FactorGeneration_TraceHilbert`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/FactorGeneration/TraceHilbert.lean).
--
--   **Imports.** It imports the bundles `Q260K016` and `Q260K017` of this split.
--
--   **Imported by** (directly, in this split): the bundle `Q260K058`; the statement `OAI_KadisonKastler_uniform_typeIII_selfAdjoint_infinitesimal_estimate`; the proofs of `OAI_KadisonKastler_TypeIII1Factor_of_normalHom` and `OAI_KadisonKastler_uniform_typeIII_selfAdjoint_infinitesimal_estimate`.
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
import Definitions.Def_Q260K016
import Definitions.Def_Q260K017

section
-- module Solutions.OAIQ075_KS.FactorGeneration_SpectralStates
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealPartialOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.functionalSubspaceWeakScalarTower _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.algebraCStarAlgebra _root_.OAI.KadisonKastler.boundedSequenceCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instFintypeSignedPermutation _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.typeIIIInitialSpaceComplete _root_.OAI.KadisonKastler.varyingSequenceCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedAlgebraComplexSubtypeMemNonUnitalStarSubalgebra _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instPartialOrderSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerPartialOrder _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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
section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

theorem dimensionSpectralValue_add_of_commute
    (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (x y : M.toStarSubalgebra) (hx : IsSelfAdjoint x) (hy : IsSelfAdjoint y)
    (hxy : Commute x y) :
    dimensionSpectralValue hfactor hdiff hfinite hunit (x+y) (hx.add hy)=
      dimensionSpectralValue hfactor hdiff hfinite hunit x hx+
      dimensionSpectralValue hfactor hdiff hfinite hunit y hy := by
  classical
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  apply le_antisymm ?_ (norm_nonneg _)
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨Q,c,_,hQ,herrQ⟩ := exists_finite_spectral_approximation_preserving_commutant
    ⟨1,IsStarProjection.one _⟩ x hx (ε/4) (by positivity)
  obtain ⟨R,d,_,hR,herrR⟩ := exists_finite_spectral_approximation_preserving_commutant
    ⟨1,IsStarProjection.one _⟩ y hy (ε/4) (by positivity)
  simp only [one_mul,mul_one] at herrQ herrR
  have hQx := hQ x (Commute.refl x) (Commute.one_left x)
  have hQy := hQ y hxy (Commute.one_left y)
  have hRx := hR x hxy.symm (Commute.one_left x)
  have hRy := hR y (Commute.refl y) (Commute.one_left y)
  have hc (i : Fin Q.size) (j : Fin R.size) :
      Commute (Q.piece i).val (R.piece j).val :=
    (hR _ (hQy i).symm (Commute.one_left _) j).symm
  let q := Q.jointPiece R hc
  let b (a : Fin Q.size × Fin R.size) : ℂ := (c a.1 : ℂ)+(d a.2 : ℂ)
  let sx : M.toStarSubalgebra := ∑ i, (c i : ℂ) • (Q.piece i).val
  let sy : M.toStarSubalgebra := ∑ j, (d j : ℂ) • (R.piece j).val
  let wx : ℂ := ∑ i, (c i : ℂ)*(traceFreeDimension hfactor hdiff (Q.piece i) : ℂ)
  let wy : ℂ := ∑ j, (d j : ℂ)*(traceFreeDimension hfactor hdiff (R.piece j) : ℂ)
  have hsum : (∑ a, b a • (q a).val)=sx+sy := by
    simp only [b,add_smul,Finset.sum_add_distrib]
    exact congrArg₂ (·+·) (Q.joint_sum_left R hc (fun i => (c i : ℂ)))
      (Q.joint_sum_right R hc (fun j => (d j : ℂ)))
  have hweight : (∑ a, b a*(traceFreeDimension hfactor hdiff (q a) : ℂ))=wx+wy := by
    simp only [b,add_mul,Finset.sum_add_distrib]
    exact congrArg₂ (·+·)
      (Q.dimension_weight_joint_left hfactor hdiff hfinite R hc hunit (fun i => (c i : ℂ)))
      (Q.dimension_weight_joint_right hfactor hdiff hfinite R hc hunit (fun j => (d j : ℂ)))
  have hcomm (a : Fin Q.size × Fin R.size) : Commute (q a).val (x+y) :=
    ((hQx a.1).mul_left (hRx a.2)).add_right ((hQy a.1).mul_left (hRy a.2))
  have hz := (dimensionSpectralValue_spec hfactor hdiff hfinite hunit (x+y) (hx.add hy)).2.family_bound
    hfactor hdiff q (Q.jointPiece_orthogonal R hc) (Q.jointPiece_total R hc) b hcomm
  rw [hsum,hweight] at hz
  have he : ‖(x+y)-(sx+sy)‖ ≤ ‖x-sx‖+‖y-sy‖ := by
    rw [show (x+y)-(sx+sy)=(x-sx)+(y-sy) by abel]
    exact norm_add_le _ _
  have hxv := (dimensionSpectralValue_spec hfactor hdiff hfinite hunit x hx).2
    Q (fun i => (c i : ℂ)) hQx
  have hyv := (dimensionSpectralValue_spec hfactor hdiff hfinite hunit y hy).2
    R (fun j => (d j : ℂ)) hRy
  let vx := dimensionSpectralValue hfactor hdiff hfinite hunit x hx
  let vy := dimensionSpectralValue hfactor hdiff hfinite hunit y hy
  have hv : ‖(vx+vy)-(wx+wy)‖ ≤ ‖vx-wx‖+‖vy-wy‖ := by
    rw [show (vx+vy)-(wx+wy)=(vx-wx)+(vy-wy) by abel]
    exact norm_add_le _ _
  have htri := dist_triangle
    (dimensionSpectralValue hfactor hdiff hfinite hunit (x+y) (hx.add hy)) (wx+wy) (vx+vy)
  simp only [dist_eq_norm] at htri
  rw [norm_sub_rev (wx+wy) (vx+vy)] at htri
  change ‖vx-wx‖ ≤ ‖x-sx‖ at hxv
  change ‖vy-wy‖ ≤ ‖y-sy‖ at hyv
  change ‖x-sx‖ < ε/4 at herrQ
  change ‖y-sy‖ < ε/4 at herrR
  change ‖dimensionSpectralValue hfactor hdiff hfinite hunit (x+y) (hx.add hy)-(vx+vy)‖ ≤ 0+ε
  linarith

theorem dimensionSpectralValue_sub_of_commute
    (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (x y : M.toStarSubalgebra) (hx : IsSelfAdjoint x) (hy : IsSelfAdjoint y)
    (hxy : Commute x y) :
    dimensionSpectralValue hfactor hdiff hfinite hunit (x-y) (hx.sub hy)=
      dimensionSpectralValue hfactor hdiff hfinite hunit x hx-
      dimensionSpectralValue hfactor hdiff hfinite hunit y hy := by
  simpa only [sub_eq_add_neg,dimensionSpectralValue_neg hfactor hdiff hfinite hunit y hy] using
    dimensionSpectralValue_add_of_commute hfactor hdiff hfinite hunit x (-y) hx hy.neg hxy.neg_right

end

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
theorem dimensionSpectralValue_mono_of_commute
    (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (x y : M.toStarSubalgebra) (hx : IsSelfAdjoint x) (hy : IsSelfAdjoint y)
    (hxy : Commute x y) (hle : x ≤ y) :
    (dimensionSpectralValue hfactor hdiff hfinite hunit x hx).re ≤
      (dimensionSpectralValue hfactor hdiff hfinite hunit y hy).re := by
  have h := dimensionSpectralValue_nonneg hfactor hdiff hfinite hunit (y-x) (sub_nonneg.mpr hle)
  rw [dimensionSpectralValue_sub_of_commute hfactor hdiff hfinite hunit y x hy hx hxy.symm,
    Complex.sub_re] at h
  exact sub_nonneg.mp h

end

/-! A nonzero positive operator dominates a positive multiple of an actual
nonzero spectral projection. This proves faithfulness without linearity. -/
open scoped CStarAlgebra
section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

attribute [local instance] OAI.Generator.Tracial.spectralFaithfulStarOrder
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

attribute [local instance] OAI.Generator.Tracial.spectralFaithfulCStar
attribute [local instance] OAI.Generator.Tracial.spectralFaithfulOrder
attribute [local instance] OAI.Generator.Tracial.spectralFaithfulPreorder
attribute [local instance] OAI.Generator.Tracial.spectralFaithfulLE
theorem dimensionSpectralValue_spectral_cut_lower
    (hunit : (1 : M.toStarSubalgebra) ≠ 0) (x : M.toStarSubalgebra) (hx : 0 ≤ x) (t : ℝ) :
    t*traceFreeDimension hfactor hdiff (cornerSpectralCut ⟨1,IsStarProjection.one _⟩ x t) ≤
      (dimensionSpectralValue hfactor hdiff hfinite hunit x hx.isSelfAdjoint).re := by
  let q := cornerSpectralCut (⟨1,IsStarProjection.one _⟩ : AlgebraProjection M) x t
  have hq : Commute q.val x := by
    show q.val*x=x*q.val
    simpa only [one_mul,mul_one] using cornerSpectralCut_commutes
      ⟨1,IsStarProjection.one _⟩ x hx.isSelfAdjoint t
  have htq : Commute (t • q.val) x := by
    show (t • q.val)*x=x*(t • q.val)
    rw [smul_mul_assoc,mul_smul_comm,hq.eq]
  have hle : t • q.val ≤ x := by
    simpa only [Complex.coe_smul] using positive_spectral_cut_domination x hx t
  have h := dimensionSpectralValue_mono_of_commute hfactor hdiff hfinite hunit
    (t • q.val) x ((IsSelfAdjoint.all t).smul q.property.isSelfAdjoint) hx.isSelfAdjoint htq hle
  rw [dimensionSpectralValue_real_smul hfactor hdiff hfinite hunit t q.val q.property.isSelfAdjoint,
    dimensionSpectralValue_projection hfactor hdiff hfinite hunit q,
    ← Complex.ofReal_mul,Complex.ofReal_re] at h
  exact h

theorem dimensionSpectralValue_pos
    (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (x : M.toStarSubalgebra) (hx : 0 ≤ x) (hx0 : x≠0) :
    0 < (dimensionSpectralValue hfactor hdiff hfinite hunit x hx.isSelfAdjoint).re := by
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  let q := cornerSpectralCut (⟨1,IsStarProjection.one _⟩ : AlgebraProjection M) x (‖x‖/2)
  have hq : q.val≠0 := positive_spectral_cut_ne_zero x hx (‖x‖/2) (by positivity) (by linarith)
  have hd : 0 < traceFreeDimension hfactor hdiff q := traceFreeDyadicSup_pos
    hfactor hdiff hfinite ⟨1,IsStarProjection.one _⟩ q hq
  exact (mul_pos (half_pos hn) hd).trans_le
    (dimensionSpectralValue_spectral_cut_lower hfactor hdiff hfinite hunit x hx (‖x‖/2))

theorem dimensionSpectralValue_eq_zero_iff_of_nonneg
    (hunit : (1 : M.toStarSubalgebra) ≠ 0) (x : M.toStarSubalgebra) (hx : 0 ≤ x) :
    dimensionSpectralValue hfactor hdiff hfinite hunit x hx.isSelfAdjoint=0 ↔ x=0 := by
  constructor
  · intro h
    by_contra hx0
    have hp := dimensionSpectralValue_pos hfactor hdiff hfinite hunit x hx hx0
    rw [h,Complex.zero_re] at hp
    exact (lt_irrefl 0) hp
  · intro h
    subst x
    exact dimensionSpectralValue_zero hfactor hdiff hfinite hunit

end

/-! Unitary conjugacy preserves projection dimension and its constructed
spectral extension. No trace identity is assumed. -/
open scoped BigOperators

/-! The constructed scalar agrees on x*x and xx*, by an actual unitary polar
decomposition. This is a quadratic identity, not unrestricted additivity. -/
open scoped CStarAlgebra

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_NormalTrace
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealPartialOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.functionalSubspaceWeakScalarTower _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.algebraCStarAlgebra _root_.OAI.KadisonKastler.boundedSequenceCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.typeIIIInitialSpaceComplete _root_.OAI.KadisonKastler.varyingSequenceCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instPartialOrderSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerPartialOrder _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! A genuine linear state with exact equality of real quadratic values,
constructed from the original finite factor predicates by scalar compactness. -/

/-! Construction of a tracial state on the original concrete finite diffuse factor without a supplied trace. -/

/-! Every positive normalized tracial functional agrees with the dimension on
all projections. Lower and upper dyadic bounds use actual partial isometries. -/

/-! Identification of the actual tracial state with the spectral dimension
value, and unrestricted additivity for noncommuting self-adjoint operators. -/
section
open scoped BigOperators CStarAlgebra
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
attribute [local instance] OAI.Generator.Tracial.spectralAdditivityCStar
local instance spectralAdditivityOrder_raac7c7_1 : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance spectralAdditivityPreorder_raac7c7_1 : Preorder M.toStarSubalgebra :=
  (CStarAlgebra.spectralOrder _).toPreorder
local instance spectralAdditivityLE_raac7c7_1 : LE M.toStarSubalgebra := (CStarAlgebra.spectralOrder _).toLE
local instance spectralAdditivityStarOrder_raac7c7_1 : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

theorem functional_eq_dimensionSpectralValue (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (φ : M.toStarSubalgebra →L[ℂ] ℂ) (hnorm : ‖φ‖ ≤ 1)
    (hproj : ∀ p : AlgebraProjection M, φ p.val=(traceFreeDimension hfactor hdiff p : ℂ))
    (x : M.toStarSubalgebra) (hx : IsSelfAdjoint x) :
    φ x=dimensionSpectralValue hfactor hdiff hfinite hunit x hx :=
  (functional_isDimensionSpectralValue hfactor hdiff φ hnorm hproj x).unique hfactor hdiff hx
    (dimensionSpectralValue_spec hfactor hdiff hfinite hunit x hx).2

end

/-! The constructed faithful normalized trace on the original algebra.
Projection-net continuity is proved explicitly; no general normality or
representation theorem is hidden in the definition. -/
section
open Filter
open scoped Topology CStarAlgebra
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
attribute [local instance] OAI.Generator.Tracial.traceStarOrder
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)
variable (hunit : (1 : M.toStarSubalgebra) ≠ 0)

attribute [local instance] OAI.Generator.Tracial.traceCStar
attribute [local instance] OAI.Generator.Tracial.traceOrder
local instance tracePreorder_raac7c7_1 : Preorder M.toStarSubalgebra :=
  (CStarAlgebra.spectralOrder _).toPreorder
attribute [local instance] OAI.Generator.Tracial.traceLE
theorem traceFreeTrace_spec :
    ‖traceFreeTrace hfactor hdiff hfinite hunit‖ ≤ 1 ∧
    traceFreeTrace hfactor hdiff hfinite hunit 1=1 ∧
    (∀ x : M.toStarSubalgebra, 0 ≤ x → 0 ≤ (traceFreeTrace hfactor hdiff hfinite hunit x).re) ∧
    (∀ x : M.toStarSubalgebra, traceFreeTrace hfactor hdiff hfinite hunit (star x)=
      star (traceFreeTrace hfactor hdiff hfinite hunit x)) ∧
    ∀ x y : M.toStarSubalgebra, traceFreeTrace hfactor hdiff hfinite hunit (x*y)=
      traceFreeTrace hfactor hdiff hfinite hunit (y*x) :=
  (exists_tracial_state hfactor hdiff hfinite hunit).choose_spec

theorem traceFreeTrace_projection (p : AlgebraProjection M) :
    traceFreeTrace hfactor hdiff hfinite hunit p.val=(traceFreeDimension hfactor hdiff p : ℂ) := by
  obtain ⟨_,h1,hpos,hstar,htrace⟩ := traceFreeTrace_spec hfactor hdiff hfinite hunit
  exact tracialFunctional_projection_dimension hfactor hdiff hfinite hunit _ h1 hpos hstar htrace p

theorem traceFreeTrace_selfAdjoint (x : M.toStarSubalgebra) (hx : IsSelfAdjoint x) :
    traceFreeTrace hfactor hdiff hfinite hunit x=
      dimensionSpectralValue hfactor hdiff hfinite hunit x hx :=
  functional_eq_dimensionSpectralValue hfactor hdiff hfinite hunit _
    (traceFreeTrace_spec hfactor hdiff hfinite hunit).1
    (traceFreeTrace_projection hfactor hdiff hfinite hunit) x hx

theorem traceFreeTrace_faithful (x : M.toStarSubalgebra) (hx : 0 ≤ x) :
    traceFreeTrace hfactor hdiff hfinite hunit x=0 ↔ x=0 := by
  rw [traceFreeTrace_selfAdjoint hfactor hdiff hfinite hunit x hx.isSelfAdjoint]
  exact dimensionSpectralValue_eq_zero_iff_of_nonneg hfactor hdiff hfinite hunit x hx

end

/-! The constructed trace is dominated by a finite sum of concrete vector
functionals. The matrix partition is constructed inside the localized corner. -/

/-! Finite vector-functional representation and actual ultraweak continuity of
the constructed trace. No normality criterion is taken as an axiom. -/
open scoped BigOperators CStarAlgebra

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_TraceHilbert
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealPartialOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.boundedSequenceCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instPartialOrderSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerPartialOrder _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.ScalarInvariantMean.algebraMean_coe _root_.OAI.KadisonKastler.ambientAlgebraFamily_apply _root_.OAI.KadisonSimilarity.concretePredualEquiv_symm_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.normalCoefficient_apply _root_.OAI.KadisonSimilarity.predualCoefficient_apply _root_.OAI.KadisonSimilarity.predualEvaluation_apply _root_.OAI.KadisonSimilarity.predualRestriction_apply _root_.OAI.NaimarkZFC.gns_apply_coe
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
section
open scoped ComplexConjugate CStarAlgebra
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

attribute [local instance] OAI.Generator.Tracial.traceHilbertStarOrder
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)
variable (hunit : (1 : M.toStarSubalgebra) ≠ 0)

local notation "E" => TraceFreePreHilbert hfactor hdiff hfinite hunit
local notation "τ₀" => traceFreeTrace hfactor hdiff hfinite hunit

local notation "copy" => traceFreeCopy hfactor hdiff hfinite hunit

attribute [local instance] OAI.Generator.Tracial.traceHilbertCStar
attribute [local instance] OAI.Generator.Tracial.traceHilbertOrder
@[instance_reducible] def traceFreeInnerCore : InnerProductSpace.Core ℂ E where
  inner x y := τ₀ (star ((copy).symm x) * (copy).symm y)
  conj_inner_symm x y := by
    change star (τ₀ (star ((copy).symm y) * (copy).symm x)) = _
    rw [← (traceFreeTrace_spec hfactor hdiff hfinite hunit).2.2.2.1]
    simp only [star_mul, star_star]
  re_inner_nonneg x :=
    (traceFreeTrace_spec hfactor hdiff hfinite hunit).2.2.1 _ (star_mul_self_nonneg _)
  add_left x y z := by simp only [map_add, star_add, add_mul]
  smul_left x y c := by
    simp only [map_smul, star_smul, smul_mul_assoc]
    rfl
  definite x hx := by
    have hz := (traceFreeTrace_faithful hfactor hdiff hfinite hunit _
      (star_mul_self_nonneg ((copy).symm x))).mp hx
    have hx' : (copy).symm x = 0 := (CStarRing.star_mul_self_eq_zero_iff _).mp hz
    exact (copy).symm.injective (hx'.trans (map_zero (copy).symm).symm)

instance traceFreePreHilbertNormedAddCommGroup : NormedAddCommGroup E :=
  (traceFreeInnerCore hfactor hdiff hfinite hunit).toNormedAddCommGroup
instance traceFreePreHilbertInnerProductSpace : InnerProductSpace ℂ E :=
  .ofCore { traceFreeInnerCore hfactor hdiff hfinite hunit with }

@[simp] theorem traceFreeCopy_inner (x y : M.toStarSubalgebra) :
    inner ℂ (copy x) (copy y) = τ₀ (star x*y) := rfl

/-- The actual Hilbert completion; no representation is supplied. -/
abbrev TraceFreeHilbert := UniformSpace.Completion E

end

/-! The trace two-norm bound for left multiplication uses the original
operator norm and positivity of a concrete sandwich. -/

/-! Bounded left multiplication on the actual constructed trace Hilbert space.
All representation laws are proved on its dense algebraic subspace. -/

/-! Bounded right multiplication and its commutation with the constructed
left action. These supply separation on the actual double commutant. -/

/-! The actual double commutant of the new representation, with a constructed
faithful tracial vector. Equality with the original image is a later theorem. -/

/-! The constructed representation is WOT continuous on every original
operator-norm ball. This does not assert whole-carrier WOT continuity. -/
open scoped ComplexConjugate CStarAlgebra BigOperators

end Generator.Tracial

end

end OAI
end


