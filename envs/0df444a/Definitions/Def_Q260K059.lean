-- Prove2me | Definitions.Def_Q260K059
-- name    : Q260K059
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-13T06:06:52.414422+00:00
-- url     : https://prove2.me/theorems/f38244aa-887a-47b4-b38e-3f7cf432c89b
-- title:
--   Definitions bundle Q260K059 of the split of OpenAI, Universal strong Kadison–Kastler stability (result family 289)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KadisonKastler.universal_strong_stability`, carved from OpenAI's openai/math development (OpenAI, *Universal strong Kadison–Kastler stability (result family 289)*, OpenAI Math Release, September 23, 2026, result family 289, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 17 declarations of OpenAI's Lean: 7 definitions and 10 theorems. The definitions and types are `OAI.Generator.Tracial.traceFreeHilbertActionCLM`, `OAI.Generator.Tracial.traceFreeHilbertBallMap`, `OAI.Generator.Tracial.traceFreeHilbertClosure`, `OAI.Generator.Tracial.traceFreeHilbertCoefficient`, `OAI.Generator.Tracial.traceHilbertClosureOperatorCStar`, `OAI.Generator.Tracial.traceHilbertWOTCStar`, `OAI.Generator.Tracial.traceHilbertWOTOperatorCStar`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`FactorGeneration_NormalTrace`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/FactorGeneration/NormalTrace.lean), [`FactorGeneration_TraceHilbert`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/FactorGeneration/TraceHilbert.lean).
--
--   **Imports.** It imports the bundle `Q260K021` of this split.
--
--   **Imported by** (directly, in this split): the bundle `Q260K060`; the statement `OAI.Generator.Tracial.traceFreeHilbertClosureTrace_cyclic`; the proofs of `OAI_KadisonKastler_PointedMatrixSites_block_coisometry`, `OAI_KadisonKastler_PointedMatrixSites_exists_spatial_modular_coisometries`, `OAI_KadisonKastler_PointedMatrixSites_twoRatio_centralizer_diffuse`, `OAI.KadisonKastler.TypeIIInfinityFactor.nonempty_finiteMatrixCornerData`, `OAI_KadisonKastler_expectedMatrixSubfactorModel_of_central_contraction`, `OAI_KadisonKastler_positiveCone_polar_conjugation`, `OAI.KadisonKastler.projectionSemifinite_of_finite_projection` and `OAI.KadisonKastler.separableSpace_of_traceHilbert`.
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
import Definitions.Def_Q260K021

section
-- module Solutions.OAIQ075_KS.FactorGeneration_NormalTrace
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealPartialOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.functionalSubspaceWeakScalarTower _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.boundedSequenceCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instFintypeSignedPermutation _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.typeIIIInitialSpaceComplete _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instPartialOrderSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerPartialOrder _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.Generator.Tracial.cyclicCoefficient_apply _root_.OAI.Generator.Tracial.cyclicPredualEvaluation_apply _root_.OAI.Generator.Tracial.traceFreeCopy_inner _root_.OAI.Generator.Tracial.traceFreeInclusion_inner _root_.OAI.KadisonKastler.FullMatrixCorner.ofEquivalentProjectionFamily_entry _root_.OAI.KadisonKastler.ScalarInvariantMean.algebraMean_coe _root_.OAI.KadisonKastler.ambientAlgebraFamily_apply _root_.OAI.KadisonSimilarity.concretePredualEquiv_symm_apply _root_.OAI.KadisonSimilarity.dyadicCornerHom_coe _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.normalCoefficient_apply _root_.OAI.KadisonSimilarity.predualCoefficient_apply _root_.OAI.KadisonSimilarity.predualEvaluation_apply _root_.OAI.KadisonSimilarity.predualRestriction_apply _root_.OAI.NaimarkZFC.gns_apply_coe
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

/-! The constructed faithful normalized trace on the original algebra.
Projection-net continuity is proved explicitly; no general normality or
representation theorem is hidden in the definition. -/

/-! The constructed trace is dominated by a finite sum of concrete vector
functionals. The matrix partition is constructed inside the localized corner. -/
section
open scoped BigOperators CStarAlgebra
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
attribute [local instance] OAI.Generator.Tracial.dominationStarOrder
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)
variable (hunit : (1 : M.toStarSubalgebra) ≠ 0)

attribute [local instance] OAI.Generator.Tracial.dominationCStar
attribute [local instance] OAI.Generator.Tracial.dominationLE
theorem traceFreeTrace_matrix_diagonal {ι : Type*} [Fintype ι]
    (Q : EquivalentPartition (⟨1,IsStarProjection.one _⟩ : AlgebraProjection M) ι)
    (x : M.toStarSubalgebra) :
    (∑ i, traceFreeTrace hfactor hdiff hfinite hunit (Q.stateCoefficient x i i))=
      traceFreeTrace hfactor hdiff hfinite hunit x := by
  let τ := traceFreeTrace hfactor hdiff hfinite hunit
  have ht := (traceFreeTrace_spec hfactor hdiff hfinite hunit).2.2.2.2
  have hi (i : ι) : τ (Q.stateCoefficient x i i)=τ ((Q.leg i).target.val*x) := by
    change τ ((star (Q.leg i).val*x)*(Q.leg i).val)=_
    rw [ht]
    congr 1
  change (∑ i, τ (Q.stateCoefficient x i i))=τ x
  simp_rw [hi]
  rw [← map_sum,← Finset.sum_mul,Q.total,one_mul]

attribute [local instance] OAI.Generator.Tracial.dominationOrder
local instance dominationPreorder_rdde8c3_1 : Preorder M.toStarSubalgebra :=
  (CStarAlgebra.spectralOrder _).toPreorder
theorem traceFreeTrace_exists_finite_vector_domination :
    ∃ (n : ℕ) (ξ : Fin n → H) (C : ℝ), 0<C ∧
      ∀ x : M.toStarSubalgebra, 0 ≤ x →
        (traceFreeTrace hfactor hdiff hfinite hunit x).re ≤
          C * ∑ i, (inner ℂ (ξ i) (x.val (ξ i))).re := by
  obtain ⟨ξ,hξ⟩ := exists_unit_vector_of_unit_ne_zero hunit
  obtain ⟨E,a,hE,ha,hloc⟩ := exists_localized_vector_functional hfactor hdiff hfinite hunit ξ hξ 1 (by norm_num)
  obtain ⟨n,_,Q,hQE,_⟩ := exists_equivalent_partition_base_le hfactor hdiff hfinite hunit E hE
  refine ⟨n,fun i => (Q.leg i).val.val ξ,a⁻¹,inv_pos.mpr ha,?_⟩
  intro x hx
  let τ := traceFreeTrace hfactor hdiff hfinite hunit
  have hi (i : Fin n) : a*(τ (Q.stateCoefficient x i i)).re ≤
      (vectorFunctional ξ (Q.stateCoefficient x i i)).re := by
    have hpos : 0 ≤ Q.stateCoefficient x i i := star_left_conjugate_nonneg hx (Q.leg i).val
    have hEx : E.val*Q.stateCoefficient x i i=Q.stateCoefficient x i i := by
      calc E.val*Q.stateCoefficient x i i =
          E.val*(Q.base.val*Q.stateCoefficient x i i) := by rw [Q.stateCoefficient_left]
        _ = Q.stateCoefficient x i i := by rw [← mul_assoc,hQE,Q.stateCoefficient_left]
    have h := (hloc (Q.stateCoefficient x i i) hpos hEx).1
    rwa [← traceFreeTrace_selfAdjoint hfactor hdiff hfinite hunit _ hpos.isSelfAdjoint] at h
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) => hi i)
  rw [← Finset.mul_sum,← Complex.re_sum,
    traceFreeTrace_matrix_diagonal hfactor hdiff hfinite hunit] at hsum
  have hv : (∑ i, (vectorFunctional ξ (Q.stateCoefficient x i i)).re)=
      ∑ i, (inner ℂ ((Q.leg i).val.val ξ) (x.val ((Q.leg i).val.val ξ))).re := by
    rw [← Complex.re_sum,← Q.matrixVectorFunctional_apply]
    simp only [EquivalentPartition.matrixVectorFunctional,sum_apply,Complex.re_sum,
      vectorFunctional_apply]
  rw [hv] at hsum
  have h := mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr ha.le)
  simpa only [← mul_assoc,inv_mul_cancel₀ ha.ne',one_mul] using h

/-- The scalar Cauchy--Schwarz bound follows from positivity of a centered square. -/
theorem traceFreeTrace_norm_sq_le (x : M.toStarSubalgebra) :
    ‖traceFreeTrace hfactor hdiff hfinite hunit x‖^2 ≤
      (traceFreeTrace hfactor hdiff hfinite hunit (star x*x)).re := by
  let τ := traceFreeTrace hfactor hdiff hfinite hunit
  obtain ⟨_,h1,hpos,hstar,_⟩ := traceFreeTrace_spec hfactor hdiff hfinite hunit
  change τ 1=1 at h1
  change ∀ x : M.toStarSubalgebra, τ (star x)=star (τ x) at hstar
  have h := hpos (star (x-(τ x) • 1)*(x-(τ x) • 1)) (star_mul_self_nonneg _)
  change 0 ≤ (τ (star (x-(τ x) • 1)*(x-(τ x) • 1))).re at h
  have he : τ (star (x-(τ x) • 1)*(x-(τ x) • 1))=
      τ (star x*x)-star (τ x)*(τ x) := by
    simp only [star_sub,star_smul,star_one,sub_mul,mul_sub,smul_mul_assoc,
      mul_smul_comm,mul_one,one_mul,map_sub,map_smul,smul_eq_mul,h1,hstar]
    ring
  rw [he,Complex.sub_re] at h
  change ‖τ x‖^2 ≤ (τ (star x*x)).re
  have hn : (star (τ x)*(τ x)).re=‖τ x‖^2 := by
    rw [RCLike.star_def,Complex.conj_mul',← Complex.ofReal_pow,Complex.ofReal_re]
  rw [hn] at h
  linarith

end

/-! Finite vector-functional representation and actual ultraweak continuity of
the constructed trace. No normality criterion is taken as an axiom. -/
open scoped BigOperators CStarAlgebra
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
attribute [local instance] OAI.Generator.Tracial.traceNormalStarOrder
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)
variable (hunit : (1 : M.toStarSubalgebra) ≠ 0)

local instance traceNormalCStar_rdde8c3_1 : CStarAlgebra M.toStarSubalgebra := {}
attribute [local instance] OAI.Generator.Tracial.traceNormalOrder
local instance traceNormalPreorder_rdde8c3_1 : Preorder M.toStarSubalgebra :=
  (CStarAlgebra.spectralOrder _).toPreorder
local instance traceNormalLE_rdde8c3_1 : LE M.toStarSubalgebra := (CStarAlgebra.spectralOrder _).toLE
theorem traceFreeTrace_finite_vector_representation :
    ∃ (n : ℕ) (ξ η : Fin n → H), ∀ x : M.toStarSubalgebra,
      traceFreeTrace hfactor hdiff hfinite hunit x=∑ i, inner ℂ (η i) (x.val (ξ i)) := by
  obtain ⟨n,ξ,C,hC,hbound⟩ := traceFreeTrace_exists_finite_vector_domination hfactor hdiff hfinite hunit
  let V := PiLp 2 (fun _ : Fin n => H)
  let F : M.toStarSubalgebra →ₗ[ℂ] V :=
    { toFun := fun x => WithLp.toLp 2 (fun i => x.val (ξ i))
      map_add' := by intros; ext i; rfl
      map_smul' := by intros; ext i; rfl }
  let τ := traceFreeTrace hfactor hdiff hfinite hunit
  have hb (x : M.toStarSubalgebra) : ‖τ x‖ ≤ Real.sqrt C*‖F x‖ := by
    have hs := (traceFreeTrace_norm_sq_le hfactor hdiff hfinite hunit x).trans
      (hbound (star x*x) (star_mul_self_nonneg _))
    have hi (i : Fin n) : (inner ℂ (ξ i) ((star x*x).val (ξ i))).re=‖x.val (ξ i)‖^2 := by
      change (vectorFunctional (ξ i) (star x*x)).re=_
      rw [vectorFunctional_star_mul_self,← Complex.ofReal_pow,Complex.ofReal_re]
    simp only [hi] at hs
    have hFn : ‖F x‖^2=∑ i, ‖x.val (ξ i)‖^2 := PiLp.norm_sq_eq_of_L2 _ (F x)
    rw [← hFn] at hs
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
    rw [mul_pow,Real.sq_sqrt hC.le]
    exact hs
  obtain ⟨η,hη⟩ := exists_inner_factor_of_bound F τ.toLinearMap (Real.sqrt C) hb
  refine ⟨n,ξ,fun i => η i,?_⟩
  intro x
  exact (hη x).trans (PiLp.inner_apply η (F x))

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_TraceHilbert
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.algebraCStarAlgebra _root_.OAI.KadisonKastler.boundedSequenceCStarAlgebra _root_.OAI.KadisonKastler.canonicalInitialSpaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.typeIIIInitialSpaceComplete _root_.OAI.KadisonKastler.varyingSequenceCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedAlgebraComplexSubtypeMemNonUnitalStarSubalgebra _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

/-! The trace two-norm bound for left multiplication uses the original
operator norm and positivity of a concrete sandwich. -/

/-! Bounded left multiplication on the actual constructed trace Hilbert space.
All representation laws are proved on its dense algebraic subspace. -/
section
open scoped ComplexConjugate CStarAlgebra
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
attribute [local instance] OAI.Generator.Tracial.traceHilbertActionCStar
local instance traceHilbertActionOrder_rdde8c3_1 : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance traceHilbertActionStarOrder_rdde8c3_1 : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)
variable (hunit : (1 : M.toStarSubalgebra) ≠ 0)

local notation "τ₀" => traceFreeTrace hfactor hdiff hfinite hunit

local notation "copy" => traceFreeCopy hfactor hdiff hfinite hunit

local notation "K" => TraceFreeHilbert hfactor hdiff hfinite hunit
local notation "ι" => traceFreeInclusion hfactor hdiff hfinite hunit

local notation "π" => traceFreeHilbertAction hfactor hdiff hfinite hunit

local notation "Ω" => traceFreeHilbertVector hfactor hdiff hfinite hunit

attribute [local instance] OAI.Generator.Tracial.traceHilbertOperatorCStar
theorem traceFreeHilbertAction_trace (a : M.toStarSubalgebra) : inner ℂ Ω (π a Ω) = τ₀ a := by
  rw [traceFreeHilbertAction_vector]
  change inner ℂ (ι (copy 1)) (ι (copy a)) = _
  rw [traceFreeInclusion_inner,star_one,one_mul]

theorem traceFreeHilbertAction_cyclic : DenseRange (fun a : M.toStarSubalgebra => π a Ω) := by
  have hc : Function.Surjective (fun a : M.toStarSubalgebra => copy a) :=
    fun b => ⟨(copy).symm b,(copy).apply_symm_apply b⟩
  have h := (traceFreeInclusion_denseRange hfactor hdiff hfinite hunit).comp
    hc.denseRange (ι).continuous
  simpa only [traceFreeHilbertAction_vector,Function.comp_def] using h

end

/-! Bounded right multiplication and its commutation with the constructed
left action. These supply separation on the actual double commutant. -/

/-! The actual double commutant of the new representation, with a constructed
faithful tracial vector. Equality with the original image is a later theorem. -/
section
open Filter
open scoped ComplexConjugate CStarAlgebra Pointwise Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
local instance traceHilbertClosureCStar_rdde8c3_1 : CStarAlgebra M.toStarSubalgebra := {}
local instance traceHilbertClosureOrder_rdde8c3_1 : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance traceHilbertClosureStarOrder_rdde8c3_1 : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)
variable (hunit : (1 : M.toStarSubalgebra) ≠ 0)

local notation "K" => TraceFreeHilbert hfactor hdiff hfinite hunit
local instance traceHilbertClosureOperatorCStar : CStarAlgebra (K →L[ℂ] K) := {}

local notation "π" => traceFreeHilbertAction hfactor hdiff hfinite hunit

/-- The bicommutant is a von Neumann algebra; no image-closedness is assumed. -/
def traceFreeHilbertClosure : VonNeumannAlgebra K where
  toStarSubalgebra := StarSubalgebra.centralizer ℂ
    (StarSubalgebra.centralizer ℂ ((π).range : Set (K →L[ℂ] K)) : Set (K →L[ℂ] K))
  centralizer_centralizer' := by
    change Set.centralizer (Set.centralizer
      ((StarSubalgebra.centralizer ℂ (StarSubalgebra.centralizer ℂ
        ((π).range : Set (K →L[ℂ] K)) : Set (K →L[ℂ] K))) : Set (K →L[ℂ] K))) =
      ((StarSubalgebra.centralizer ℂ (StarSubalgebra.centralizer ℂ
        ((π).range : Set (K →L[ℂ] K)) : Set (K →L[ℂ] K))) : Set (K →L[ℂ] K))
    rw [StarSubalgebra.coe_centralizer_centralizer]
    simp only [Set.centralizer_centralizer_centralizer]

local notation "N" => traceFreeHilbertClosure hfactor hdiff hfinite hunit

theorem traceFreeHilbertClosure_mem_iff (T : K →L[ℂ] K) :
    T ∈ N ↔ T ∈ Set.centralizer (Set.centralizer ((π).range : Set (K →L[ℂ] K))) := by
  change T ∈ (StarSubalgebra.centralizer ℂ
    (StarSubalgebra.centralizer ℂ ((π).range : Set (K →L[ℂ] K)) : Set (K →L[ℂ] K))) ↔ _
  simp only [← SetLike.mem_coe,StarSubalgebra.coe_centralizer_centralizer,
    StarMemClass.star_coe_eq,Set.union_self]

theorem traceFreeHilbertAction_mem_closure (a : M.toStarSubalgebra) : π a ∈ N := by
  apply (traceFreeHilbertClosure_mem_iff hfactor hdiff hfinite hunit _).mpr
  intro T hT
  exact (hT (π a) ⟨a,rfl⟩).symm

end

/-! The constructed representation is WOT continuous on every original
operator-norm ball. This does not assert whole-carrier WOT continuity. -/
open scoped ComplexConjugate CStarAlgebra BigOperators
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
local instance traceHilbertWOTCStar : CStarAlgebra M.toStarSubalgebra := {}
local instance traceHilbertWOTOrder_rdde8c3_1 : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance traceHilbertWOTStarOrder_rdde8c3_1 : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)
variable (hunit : (1 : M.toStarSubalgebra) ≠ 0)

local notation "K" => TraceFreeHilbert hfactor hdiff hfinite hunit
local instance traceHilbertWOTOperatorCStar : CStarAlgebra (K →L[ℂ] K) := {}

local notation "π" => traceFreeHilbertAction hfactor hdiff hfinite hunit

def traceFreeHilbertActionCLM : M.toStarSubalgebra →L[ℂ] (K →L[ℂ] K) :=
  (π).toLinearMap.mkContinuous 1 (by
    intro a
    rw [one_mul]
    exact (traceFreeHilbertAction_norm hfactor hdiff hfinite hunit a).le)

def traceFreeHilbertCoefficient (x y : K) : StrongDual ℂ M.toStarSubalgebra :=
  (innerSL ℂ y).comp ((ContinuousLinearMap.apply ℂ K x).comp
    (traceFreeHilbertActionCLM hfactor hdiff hfinite hunit))

@[simp] theorem traceFreeHilbertCoefficient_apply (x y : K) (a : M.toStarSubalgebra) :
    traceFreeHilbertCoefficient hfactor hdiff hfinite hunit x y a = inner ℂ y (π a x) := rfl

theorem traceFreeHilbertCoefficient_continuous : Continuous
    (fun p : K × K => traceFreeHilbertCoefficient hfactor hdiff hfinite hunit p.1 p.2) :=
  ((innerSL ℂ).continuous.comp continuous_snd).clm_comp
    (((ContinuousLinearMap.apply ℂ K).continuous.comp continuous_fst).clm_comp continuous_const)

def traceFreeHilbertBallMap (C : ℝ) (T : weakOperatorBall M C) : K →WOT[ℂ] K :=
  ContinuousLinearMapWOT.ofCLM (π ⟨T.val.toCLM,T.property.1⟩)

end Generator.Tracial

end

end OAI
end


