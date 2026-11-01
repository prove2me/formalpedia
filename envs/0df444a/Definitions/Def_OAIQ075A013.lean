-- Prove2me | Definitions.Def_OAIQ075A013
-- name    : OAIQ075A013
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T08:06:36.226795+00:00
-- url     : https://prove2.me/theorems/3baee417-d3e6-4ab3-97f2-305cca4651df
-- title:
--   Definitions bundle OAIQ075A013 of the split of OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KadisonSimilarity.similarityTheorem`, `OAI.KadisonSimilarity.universalCommutatorTheorem` and `OAI.KadisonSimilarity.universalHyperreflexivity`, carved from OpenAI's openai/math development (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math) at commit 1581d4c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 123 declarations of OpenAI's Lean: 36 definitions and 87 theorems. The definitions and types are `OAI.BoundedHochschild.KadisonRingrose.matrixFunctionalCP`, `OAI.BoundedHochschild.KadisonRingrose.operatorSystemMatrixFunctional`, `OAI.BoundedHochschild.KadisonRingrose.paulsenLinear`, `OAI.BoundedHochschild.KadisonRingrose.paulsenMatrixDiagonal`, `OAI.BoundedHochschild.KadisonRingrose.paulsenMatrixUpper`, `OAI.BoundedHochschild.KadisonRingrose.paulsenOperatorMap`, `OAI.BoundedHochschild.KadisonRingrose.paulsenSystem`, `OAI.BoundedHochschild.KadisonRingrose.paulsenSystemMap`, `OAI.BoundedHochschild.KadisonRingrose.positiveBlock`, `OAI.BoundedHochschild.KadisonRingrose.positiveUnitBlock`, `OAI.BoundedHochschild.KadisonRingrose.stinespringEmbedding`, `OAI.BoundedHochschild.KadisonRingrose.stinespringOperator`, `OAI.BoundedHochschild.KadisonRingrose.stinespringPreOperator`, `OAI.BoundedHochschild.KadisonRingrose.stinespringPreVector`, `OAI.BoundedHochschild.KadisonRingrose.stinespringRepresentation`, `OAI.BoundedHochschild.KadisonRingrose.stinespringVector`, `OAI.BoundedHochschild.KadisonRingrose.unitaryPredualAction`, `OAI.Generator.FiniteMatrixStage.commutant`, `OAI.Generator.MatrixUnitSystem.concreteAlgebra`, `OAI.Generator.MatrixUnitSystem.concreteHom`, `OAI.Generator.MatrixUnitSystem.relativeVonNeumann`, `OAI.Generator.Tracial.TraceOrthogonal`, `OAI.Generator.Tracial.baseVector`, `OAI.Generator.Tracial.insideAlgebra`, `OAI.Generator.Tracial.instCStarAlgebraSubtypeContinuousLinearMapComplexIdMemStarSubalgebra_solutions`, `OAI.Generator.Tracial.instLESubtypeContinuousLinearMapComplexIdMemStarSubalgebra_solutions`, `OAI.Generator.Tracial.interiorCStar`, `OAI.Generator.Tracial.interiorLE`, `OAI.Generator.Tracial.interiorOrder`, `OAI.Generator.Tracial.interiorPreorder`, `OAI.Generator.Tracial.selfAdjointTraceBall`, `OAI.Generator.Tracial.tracePairingCStar`, `OAI.Generator.Tracial.tracePairingLE`, `OAI.Generator.Tracial.truncationCStar`, `OAI.Generator.Tracial.upperTruncate`, `OAI.PopaCorner.predualEquiv`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `BoundedHochschild_CompleteAdditivity`, `BoundedHochschild_FiniteCentralDecomposition`, `BoundedHochschild_FiniteConstraints`, `BoundedHochschild_FiniteNormalOrbit`, `BoundedHochschild_FiniteNormalState`, `BoundedHochschild_FiniteNormalTrace`, `BoundedHochschild_InfinitePairChains`, `BoundedHochschild_IsometryDefectColumns`, `BoundedHochschild_MatrixFunctionalDilation`, `BoundedHochschild_MaximalInfiniteProjection`, `BoundedHochschild_NormalModulus`, `BoundedHochschild_NormalOperators`, `BoundedHochschild_NormalOrbitHull`, `BoundedHochschild_NormalOrbitInvariance`, `BoundedHochschild_NormalTraceFaithfulness`, `BoundedHochschild_OperatorSystemMatrices`, `BoundedHochschild_PartialUnitaries`, `BoundedHochschild_PaulsenExtension`, `BoundedHochschild_PaulsenMatrixBlocks`, `BoundedHochschild_PaulsenSystem`, `BoundedHochschild_PositiveBlocks`, `BoundedHochschild_PositiveCompleteAdditivity`, `BoundedHochschild_PositiveCompression`, `BoundedHochschild_PositiveOrbitCompactness`, `BoundedHochschild_PositiveUnitBlocks`, `BoundedHochschild_ProperlyInfiniteColumns`, `BoundedHochschild_ProperlyInfiniteCorners`, `BoundedHochschild_ProperlyInfiniteIsometries`, `BoundedHochschild_StinespringEmbedding`, `BoundedHochschild_StinespringLeftAction`, `BoundedHochschild_StinespringRepresentation`, `BoundedHochschild_StinespringStar`, `BoundedHochschild_TraceFreeHalving`, `BoundedHochschild_TypeIICharacterization`, `BoundedHochschild_UnitaryPredualAction`, `BoundedHochschild_WeakPredual`, `FactorGeneration_CornerTrace`, `FactorGeneration_Expectations`, `FactorGeneration_HilbertLimits`, `FactorGeneration_MatrixAlgebras`, `FactorGeneration_MatrixRefinement`, `FactorGeneration_MatrixSequence`, `FactorGeneration_Pinching`, `FactorGeneration_SpectralTruncation`, `FactorGeneration_Subfactors`, `FactorGeneration_TraceTopology`, `FactorGeneration_TracialInclusion`, `FactorGeneration_UnitaryMetric`, `TracialCohomology_CornerComparison`, `TracialCohomology_Corners`, `TracialCohomology_TypeII`.
--
--   **Imports.** It imports the bundles `OAIQ075A007` and `OAIQ075A008` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ075A019`, `OAIQ075A020`, `OAIQ075A021`, `OAIQ075A022`, `OAIQ075A023`, `OAIQ075A024` and `OAIQ075A025`; the statement `OAI_KadisonSimilarity_exists_corner_intertwiner_of_column_tests`; the proofs of `OAI.BoundedHochschild.KadisonRingrose.factorization_of_complete_bound` and `OAI_KadisonSimilarity_TracialCornerGeometry_rightSupportInput_of_normal_range`.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 1581d4c

import Mathlib
import Definitions.Def_OAIQ075A007
import Definitions.Def_OAIQ075A008

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_NormalModulus
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.UltrapowerBridge.instStarTracialQuotient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normal cochains, bounded-ball continuity and primitive construction. -/

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal Function
open Filter Topology
open scoped ComplexOrder
namespace BoundedHochschild
open HochschildRigidity
variable {M X I : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)

lemma preGNS_zero_of_predual_limit
    (hL : ∀ b : M, HasPreadjoint e (ContinuousLinearMap.mul ℂ M b))
    (hτ : TraceInPredual e τ) {a : I → M} {l : Filter I} [l.NeBot] {b : M}
    (ha : Tendsto (fun i => ‖τ.toPreGNS (a i)‖) l (𝓝 0))
    (hb : PredualTendsto e a l b) : ‖τ.toPreGNS b‖ = 0 := by
  apply le_antisymm _ (norm_nonneg _)
  apply le_of_forall_pos_le_add
  intro ε hε
  simpa only [zero_add] using preGNS_norm_le_of_predual_tendsto e τ hL hτ ε hε.le
    (ha.eventually (ge_mem_nhds hε)) hb

 

theorem predual_tendsto_of_preGNS
    (hL : ∀ b : M, HasPreadjoint e (ContinuousLinearMap.mul ℂ M b))
    (hτ : TraceInPredual e τ) (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)
    {a : I → M} {l : Filter I} (C : ℝ) (ha : ∀ i, ‖a i‖ ≤ C) {b : M}
    (hb : Tendsto (fun i => ‖τ.toPreGNS (a i-b)‖) l (𝓝 0)) :
    PredualTendsto e a l b := by
  intro z
  apply (tendsto_iff_ultrafilter _ _ _).mpr
  intro u hu
  obtain ⟨c,_hc,ht⟩ := exists_predual_ultralimit e u a C ha
  have hzero := preGNS_zero_of_predual_limit e τ hL hτ (hb.mono_left hu)
    (predual_tendsto_sub e ht (predual_tendsto_const e b (u : Filter I)))
  have hcb : c=b := by
    apply sub_eq_zero.mp
    exact (preGNS_norm_eq_zero_iff τ hfaith (c-b)).mp hzero
  simpa only [hcb] using ht z



end BoundedHochschild

 

open Filter Topology
open scoped ComplexOrder



open Filter Topology
open scoped ComplexOrder



open Filter Topology
open scoped ComplexOrder
end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_FiniteConstraints
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.UltrapowerBridge.instStarTracialQuotient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite cocycle constraints and exactness for bounded primitives. -/

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal Function
open Filter Topology
open scoped ComplexOrder



open Filter Topology
open scoped ComplexOrder



open Filter Topology
open scoped ComplexOrder
namespace BoundedHochschild
variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
variable (hL : ∀ b : M, HasPreadjoint e (ContinuousLinearMap.mul ℂ M b))
  (hτ : TraceInPredual e τ) (htr : ∀ x y : M, τ (x*y)=τ (y*x))
  (hfaith : ∀ a : M, τ (Star.star a*a)=0 → a=0)

include e hL hτ htr hfaith in
lemma exists_monotone_projection_limit (a : ℕ → M) (ha : ∀ n, IsStarProjection (a n))
    (ham : Monotone a) :
    ∃ p : M, IsStarProjection p ∧ GNSTendsto τ a atTop p ∧ (∀ n, a n ≤ p) ∧
      ∀ q : M, IsStarProjection q → (∀ n, a n ≤ q) → p ≤ q := by
  obtain ⟨p,_hp,ht⟩ := exists_bounded_preGNS_limit e τ hL hτ 1
    (fun n => (ha n).norm_le _)
    (monotone_contractions_preGNS_cauchy τ a (fun n => (ha n).nonneg)
      (fun n => (ha n).le_one) ham)
  change GNSTendsto τ a atTop p at ht
  have hstar : star p=p := by
    apply GNSTendsto.unique τ hfaith (ht.star τ htr)
    simpa only [(ha _).isSelfAdjoint.star_eq] using ht
  have hmul : p*p=p := by
    apply GNSTendsto.unique τ hfaith (ht.mul τ htr ht 1 (fun n => (ha n).norm_le _))
    simpa only [(ha _).isIdempotentElem.eq] using ht
  have hp : IsStarProjection p := ⟨hmul,hstar⟩
  refine ⟨p,hp,ht,?_,?_⟩
  · intro n
    apply ((ha n).le_iff_mul_eq_left hp).mpr
    apply GNSTendsto.unique τ hfaith
      ((GNSTendsto.const τ (a n) (atTop : Filter ℕ)).mul τ htr ht 1
        (fun _ => (ha n).norm_le _))
    change Tendsto (fun m => ‖τ.toPreGNS (a n*a m-a n)‖) atTop (𝓝 0)
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop n] with m hm
    simp only [((ha n).le_iff_mul_eq_left (ha m)).mp (ham hm),sub_self,map_zero,norm_zero]
  · intro q hq haq
    apply (hp.le_iff_mul_eq_left hq).mpr
    apply GNSTendsto.unique τ hfaith
      (ht.mul τ htr (GNSTendsto.const τ q atTop) 1 (fun n => (ha n).norm_le _))
    simpa only [((ha _).le_iff_mul_eq_left hq).mp (haq _)] using ht

end BoundedHochschild

 

open Filter Topology
open scoped ComplexOrder
end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_NormalOperators
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.UltrapowerBridge.instStarTracialQuotient
attribute [-simp] _root_.OAI.HochschildNormalPart.hilbertNormalFunctional_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normal parts of scalar functionals and bounded operators. -/

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal Function
open scoped NNReal
open scoped ComplexOrder BoundedContinuousFunction CStarAlgebra
open scoped ComplexOrder CStarAlgebra
open scoped BigOperators
open scoped InnerProductSpace
open scoped ComplexStarModule
open scoped InnerProductSpace ComplexOrder
namespace HochschildNormalPart
universe u
attribute [instance] FunctionalModel.normed FunctionalModel.innerSpace FunctionalModel.complete

end HochschildNormalPart

 

namespace HochschildNormalPart
universe u v
variable {M X : Type u} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma scalarNormalPart_comp_left (φ : StrongDual ℂ M) (b : M) :
    scalarNormalPart e (φ.comp (ContinuousLinearMap.mul ℂ M b))=
      (scalarNormalPart e φ).comp (ContinuousLinearMap.mul ℂ M b) := by
  let m := functionalModel φ
  have hc (ξ : m.H) : (coefficient m.representation m.leftVector ξ).comp
      (ContinuousLinearMap.mul ℂ M b)=coefficient m.representation (m.representation (star b) m.leftVector) ξ := by
    ext a
    simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.mul_apply',coefficient_apply,
      map_mul,mul_apply_eq_comp,map_star,ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_inner_left]
  rw [← m.realizes,hc,scalarNormalPart_coefficient,scalarNormalPart_coefficient,hc]

lemma scalarNormalPart_comp_right (φ : StrongDual ℂ M) (b : M) :
    scalarNormalPart e (φ.comp ((ContinuousLinearMap.mul ℂ M).flip b))=
      (scalarNormalPart e φ).comp ((ContinuousLinearMap.mul ℂ M).flip b) := by
  let m := functionalModel φ
  have hc (ξ : m.H) : (coefficient m.representation m.leftVector ξ).comp
      ((ContinuousLinearMap.mul ℂ M).flip b)=coefficient m.representation m.leftVector (m.representation b ξ) := by
    ext a
    simp [map_mul]
  rw [← m.realizes,hc,scalarNormalPart_coefficient,scalarNormalPart_coefficient,hc]
  exact congrArg (coefficient m.representation m.leftVector)
    (congrArg (fun T : m.H →L[ℂ] m.H => T m.rightVector) (normalProjection_mul e m.representation b))

end HochschildNormalPart



end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_PartialUnitaries
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Partial unitaries, ordered limits and trace estimates. -/

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal Function
open scoped NNReal
open scoped ComplexOrder BoundedContinuousFunction CStarAlgebra
open scoped ComplexOrder CStarAlgebra
open scoped BigOperators
open scoped InnerProductSpace
open scoped ComplexStarModule
open scoped InnerProductSpace ComplexOrder
open Filter Topology
open scoped ComplexOrder
namespace HochschildComparison
open BoundedHochschild
variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

namespace PartialUnitary
section
omit [PartialOrder M] [StarOrderedRing M]

lemma norm_le_one (v : PartialUnitary M) : ‖(v : M)‖≤1 := v.val.norm_le_one
end

end PartialUnitary
end HochschildComparison

 

 

open Filter Topology
open scoped ComplexOrder







open scoped ComplexOrder
end

end OAI
end

section
-- module Solutions.OAIQ075_KS.TracialCohomology_CornerComparison
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.UltrapowerBridge.instStarTracialQuotient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Corner comparison for bounded Hochschild cohomology. -/

noncomputable section

open Filter Topology
open scoped ComplexOrder
namespace PopaCorners
open BoundedHochschild HochschildRigidity HochschildDixmier HochschildDiffuse
variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (h1 : τ 1 = 1)
  (htr : ∀ a b : M, τ (a*b) = τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a) = 0 → a = 0)
  (hfactor : ∀ b : M, (∀ x : M, Commute b x) → ∃ c : ℂ, b = c • (1 : M))

include e in

theorem corner_polar {p q b : M} (hp : IsStarProjection p)
    (hq : IsStarProjection q) (hbp : b*p=b) (hqb : q*b=b) :
    ∃ v r s : M, IsStarProjection r ∧ IsStarProjection s ∧
      r ≤ p ∧ s ≤ q ∧ star v*v=r ∧ v*star v=s ∧ v*r=v ∧ s*v=v ∧
      b=v*CFC.abs b := by
  obtain ⟨v,r,s,hr,hi,hf,hs,hb,hvr,hsb⟩ :=
    HochschildPolar.exists_polar_partial_isometry e b
  have habs : star v*b=CFC.abs b := by
    calc
      star v*b = star v*(v*CFC.abs b) := congrArg (fun x => star v*x) hb
      _ = CFC.abs b := by rw [← mul_assoc,hi,hr.left]
  have hrp : r ≤ p := hr.le_of_support hp (by
    rw [← habs,mul_assoc,hbp])
  have hqv : q*v=v := by
    have hz : (q*v-v)*CFC.abs b=0 := by
      rw [sub_mul,mul_assoc,← hb,hqb,sub_self]
    have hzr := HochschildPolar.support_right_annihilate hr
      (IsSelfAdjoint.of_nonneg (CFC.abs_nonneg b)) hz
    simpa only [sub_mul,mul_assoc,hvr,sub_eq_zero] using hzr
  have hsq : s ≤ q := (hs.le_iff_mul_eq_right hq).mpr (by
    rw [← hf,← mul_assoc,hqv])
  have hsv : s*v=v := by rw [← hf,mul_assoc,hi,hvr]
  exact ⟨v,r,s,hr.proj,hs,hrp,hsq,hi,hf,hvr,hsv,hb⟩

end PopaCorners

open Filter Topology
open scoped ComplexOrder

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.TracialCohomology_Corners
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.KadisonSimilarity.cstarCornerSubalgebra_closed _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.UltrapowerBridge.instStarTracialQuotient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Corners for bounded Hochschild cohomology. -/

noncomputable section

open scoped ComplexOrder

open Filter Topology
open scoped ComplexOrder
namespace PopaCorner
open BoundedHochschild HochschildRigidity
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) {p : M} (hp : IsStarProjection p)

omit [PartialOrder M] [StarOrderedRing M] in
lemma weakSpace_closed : IsClosed (weakSpace e hp : Set (WeakDual ℂ X)) := by
  have hL := WeakAlgebra.normal_continuous e (ContinuousLinearMap.mul ℂ M p)
    ((HochschildSakai.abstract_multiplication_normal e).1 p)
  have hR := WeakAlgebra.normal_continuous e ((ContinuousLinearMap.mul ℂ M).flip p)
    ((HochschildSakai.abstract_multiplication_normal e).2 p)
  have he : (weakSpace e hp : Set (WeakDual ℂ X)) =
      {f | (WeakAlgebra.weakEquiv e).symm (p*WeakAlgebra.weakEquiv e f)=f} ∩
      {f | (WeakAlgebra.weakEquiv e).symm (WeakAlgebra.weakEquiv e f*p)=f} := by
    ext f
    change (p*WeakAlgebra.weakEquiv e f=WeakAlgebra.weakEquiv e f ∧
      WeakAlgebra.weakEquiv e f*p=WeakAlgebra.weakEquiv e f) ↔ _
    simp only [Set.mem_inter_iff,Set.mem_ofPred_eq,LinearEquiv.symm_apply_eq]
  rw [he]
  exact (isClosed_eq hL continuous_id).inter (isClosed_eq hR continuous_id)

def predualEquiv : StrongDual ℂ (X ⧸ WeakSubspace.preannihilator (weakSpace e hp)) ≃ₗᵢ⋆[ℂ] algebra hp :=
  (WeakSubspace.quotientDualEquiv (weakSpace e hp) (weakSpace_closed e hp)).trans
    (strongEquiv e hp)

end PopaCorner

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.TracialCohomology_TypeII
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instPartialOrderSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.cstarCornerSubalgebra_closed _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.UltrapowerBridge.instStarTracialQuotient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Type ii for bounded Hochschild cohomology. -/

noncomputable section

open scoped ComplexOrder
namespace PopaTypeII
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

lemma projection_commute_of_all (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (a : M)
    (ha : ∀ q : M, IsStarProjection q → Commute q a) (b : M) : Commute b a := by
  let T : M →L[ℂ] M := (ContinuousLinearMap.mul ℂ M).flip a-(ContinuousLinearMap.mul ℂ M) a
  have hs : Submodule.span ℂ {q : M | IsStarProjection q} ≤ T.ker := by
    apply Submodule.span_le.mpr
    intro q hq
    change q*a-a*q=0
    exact sub_eq_zero.mpr (ha q hq).eq
  have hc : (Submodule.span ℂ {q : M | IsStarProjection q}).topologicalClosure ≤ T.ker :=
    Submodule.topologicalClosure_minimal _ hs T.isClosed_ker
  rw [HochschildSakai.projection_span_dense e] at hc
  exact sub_eq_zero.mp (hc (Submodule.mem_top : b ∈ (⊤ : Submodule ℂ M)))

theorem orthogonal_pair (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (hII : NoAbelianCorners M) {p : M} (hp : IsStarProjection p) (hp0 : p ≠ 0) :
    ∃ v : PopaCorners.CornerIso p p, v.initial*v.final=0 ∧ (v:M) ≠ 0 := by
  classical
  let N := PopaCorner.algebra hp
  let eN := PopaCorner.predualEquiv e hp
  obtain ⟨a,b,hab⟩ := hII p hp hp0
  have hex : ∃ q : N, IsStarProjection q ∧ ¬ Commute q b := by
    by_contra hh
    push Not at hh
    exact hab (projection_commute_of_all eN b hh a)
  obtain ⟨q,hq,hqb⟩ := hex
  obtain ⟨y,hy⟩ : ∃ y : N, (1-q)*y*q ≠ 0 := by
    rcases off_diagonal_nonzero hq hqb with h | h
    · exact ⟨b,h⟩
    · exact ⟨star b,h⟩
  have h1q := hq.one_sub
  have hr := (hq.map (PopaCorner.incl hp))
  have hs := (h1q.map (PopaCorner.incl hp))
  let Q : M := (q:N)
  let R : M := ((1-q:N):N)
  let B : M := (((1-q)*y*q:N):N)
  have hB0 : B ≠ 0 := fun hh => hy (Subtype.ext hh)
  have hBQ : B*Q=B := by
    change (((1-q)*y*q:N):M)*(q:M)=_
    exact congrArg Subtype.val (show ((1-q)*y*q)*q=(1-q)*y*q from by rw [mul_assoc,hq.isIdempotentElem.eq])
  have hRB : R*B=B := by
    exact congrArg Subtype.val (show (1-q)*((1-q)*y*q)=(1-q)*y*q from by
      rw [←mul_assoc,←mul_assoc,h1q.isIdempotentElem.eq])
  obtain ⟨v,r,s,hr',hs',hrQ,hsR,hvi,hvf,hvr,hsv,hB⟩ := PopaCorners.corner_polar e hr hs hBQ hRB
  have hQp : Q ≤ p := (hr.le_iff_mul_eq_right hp).mpr q.property.1
  have hRp : R ≤ p := (hs.le_iff_mul_eq_right hp).mpr (1-q:N).property.1
  let V : PopaCorners.CornerIso p p := ⟨v,by rwa [hvi],by rwa [hvi],by rw [hvi]; exact hrQ.trans hQp,by rw [hvf]; exact hsR.trans hRp⟩
  have hQR : Q*R=0 := congrArg Subtype.val (show q*(1-q)=0 from by
    rw [mul_sub,mul_one,hq.isIdempotentElem.eq,sub_self])
  have hrs : r*s=0 := by
    have hrQ' : r*Q=r := (hr'.le_iff_mul_eq_left hr).mp hrQ
    have hRs : R*s=s := (hs'.le_iff_mul_eq_right hs).mp hsR
    calc
      r*s=(r*Q)*(R*s) := by rw [hrQ',hRs]
      _=0 := by simp only [mul_assoc,←mul_assoc Q R s,hQR,zero_mul,mul_zero]
  refine ⟨V,?_,?_⟩
  · change (star v*v)*(v*star v)=0
    rwa [hvi,hvf]
  · intro hv
    change v=0 at hv
    exact hB0 (by simpa only [hv,zero_mul] using hB)

end PopaTypeII

open Filter Topology
open scoped ComplexOrder

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_FiniteCentralDecomposition
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.UltrapowerBridge.instStarTracialQuotient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The maximal finite central cut, constructed without an assumed trace. -/

noncomputable section

open scoped ComplexOrder

namespace BoundedHochschild
namespace KadisonRingrose

variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- Finiteness passes to every subprojection, without a centrality hypothesis. -/
lemma finiteCorner_mono {p q : M} (hp : IsStarProjection p)
    (hq : IsStarProjection q) (hpq : p ≤ q) (hfinite : FiniteCorner q) :
    FiniteCorner p := by
  let pC : HochschildCorners.Corner q hq :=
    ⟨p, (hp.le_iff_mul_eq_right hq).mp hpq, (hp.le_iff_mul_eq_left hq).mp hpq⟩
  have hpC : IsStarProjection pC :=
    ⟨Subtype.ext hp.isIdempotentElem.eq, Subtype.ext hp.isSelfAdjoint.star_eq⟩
  exact finiteCorner_trans hq pC
    (finiteCorner_of_finiteAlgebra ((finiteCorner_iff q hq).mp hfinite) pC hpC)

end KadisonRingrose
end BoundedHochschild

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_FiniteNormalOrbit
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.UltrapowerBridge.instStarTracialQuotient
attribute [-simp] _root_.OAI.BoundedHochschild.KadisonRingrose.columnTransition_final _root_.OAI.BoundedHochschild.KadisonRingrose.columnTransition_initial _root_.OAI.BoundedHochschild.KadisonRingrose.isometryColumn_coe _root_.OAI.BoundedHochschild.KadisonRingrose.isometryColumn_initial _root_.OAI.BoundedHochschild.KadisonRingrose.matrixSystemOfColumns_diagonal _root_.OAI.BoundedHochschild.KadisonRingrose.partialIsoCornerEquiv_apply _root_.OAI.BoundedHochschild.KadisonRingrose.partialIsoFromCorner_final _root_.OAI.BoundedHochschild.KadisonRingrose.partialIsoFromCorner_initial _root_.OAI.BoundedHochschild.KadisonRingrose.partialIsoInCorner_final _root_.OAI.BoundedHochschild.KadisonRingrose.partialIsoInCorner_initial _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Uniform normal-state decay along unitary orbits

Ringrose, *Lectures on the trace in a finite von Neumann algebra*, Lemma 5.2,
for positive normal functionals. This is the specialization needed for the
normal-state orbit used in constructing a trace.
-/

noncomputable section

open Filter Topology
open scoped ComplexOrder

namespace BoundedHochschild
namespace KadisonRingrose

open HochschildComparison

universe u

variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- Choosing a different unitary at each index still gives normal-state decay. -/
theorem normal_positive_unitary_orbit_tendsto_zero (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (hfinite : FiniteAlgebra M) (ψ : M →ₚ[ℂ] ℂ) (hψ : TraceInPredual e ψ)
    (q : ℕ → M) (hq : ∀ n, IsStarProjection (q n))
    (horth : ∀ i j, i ≠ j → q i * q j = 0) (u : ℕ → unitary M) :
    Tendsto (fun n => ψ ((u n : M) * q n * star (u n : M))) atTop (𝓝 0) := by
  let w (n : ℕ) : PartialIso M := ⟨(u n : M) * q n, by
    have hu := (Unitary.mem_iff.mp (u n).property).1
    simp only [star_mul, (hq n).isSelfAdjoint.star_eq]
    calc
      ((u n : M) * q n) * (q n * star (u n : M)) * ((u n : M) * q n) =
          (u n : M) * (q n * q n) * (star (u n : M) * (u n : M)) * q n := by
        simp only [mul_assoc]
      _ = (u n : M) * q n := by
        rw [(hq n).isIdempotentElem.eq, hu, mul_one, mul_assoc,
          (hq n).isIdempotentElem.eq]⟩
  have hwi (n : ℕ) : (w n).initial = q n := by
    change star ((u n : M) * q n) * ((u n : M) * q n) = q n
    rw [star_mul, (hq n).isSelfAdjoint.star_eq]
    calc
      _ = q n * (star (u n : M) * (u n : M)) * q n := by simp only [mul_assoc]
      _ = q n := by rw [(Unitary.mem_iff.mp (u n).property).1, mul_one,
        (hq n).isIdempotentElem.eq]
  have hwf (n : ℕ) : (w n).final = (u n : M) * q n * star (u n : M) := by
    change ((u n : M) * q n) * star ((u n : M) * q n) = _
    rw [star_mul, (hq n).isSelfAdjoint.star_eq]
    calc
      _ = (u n : M) * (q n * q n) * star (u n : M) := by simp only [mul_assoc]
      _ = _ := by rw [(hq n).isIdempotentElem.eq]
  have ht := normal_positive_subequivalent_tendsto_zero e hfinite ψ hψ
    (fun n => (w n).final) q (fun n => (w n).final_proj) hq horth
    (fun n => ⟨adjointPartialIso (w n), by simp, by simp [hwi]⟩)
  simpa only [hwf] using ht

/-- Normal positive functionals are uniformly small on every unitary conjugate
of the terms of an orthogonal projection sequence in a finite algebra. -/
theorem normal_positive_uniform_unitary_orbit (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (hfinite : FiniteAlgebra M) (ψ : M →ₚ[ℂ] ℂ) (hψ : TraceInPredual e ψ)
    (q : ℕ → M) (hq : ∀ n, IsStarProjection (q n))
    (horth : ∀ i j, i ≠ j → q i * q j = 0) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ u : unitary M, ‖ψ ((u : M) * q n * star (u : M))‖ < ε := by
  classical
  let u (n : ℕ) : unitary M := if h : ∃ v : unitary M,
      ε ≤ ‖ψ ((v : M) * q n * star (v : M))‖ then h.choose else 1
  have ht := normal_positive_unitary_orbit_tendsto_zero e hfinite ψ hψ q hq horth u
  have hlt : ∀ᶠ n in atTop, ‖ψ ((u n : M) * q n * star (u n : M))‖ < ε :=
    (tendsto_order.1 (by simpa only [norm_zero] using ht.norm)).2 ε hε
  filter_upwards [hlt] with n hn v
  by_contra hv
  have hex : ∃ v : unitary M, ε ≤ ‖ψ ((v : M) * q n * star (v : M))‖ :=
    ⟨v, le_of_not_gt hv⟩
  have hu : ε ≤ ‖ψ ((u n : M) * q n * star (u n : M))‖ := by
    simpa only [u, dite_eq_left hex] using hex.choose_spec
  exact (not_le_of_gt hn) hu

end KadisonRingrose
end BoundedHochschild

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_NormalOrbitHull
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.UltrapowerBridge.instStarTracialQuotient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The norm-closed convex orbit of a normal positive functional

This family remains normal and positive, preserves values on the center,
and satisfies the uniform orthogonal-projection decay in Ringrose Lemma 5.2.
-/

noncomputable section

open Filter Topology
open scoped ComplexOrder

namespace BoundedHochschild
namespace KadisonRingrose

open HochschildNormalPart

universe u

variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- Uniform decay survives both convex averaging and norm closure. -/
theorem normal_positive_uniform_orbit_hull (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (hfinite : FiniteAlgebra M) (ψ : M →ₚ[ℂ] ℂ) (hψ : TraceInPredual e ψ)
    (q : ℕ → M) (hq : ∀ n, IsStarProjection (q n))
    (horth : ∀ i j, i ≠ j → q i * q j = 0) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ G ∈ unitaryOrbitHull (positiveFunctionalCLM ψ), ‖G (q n)‖ < ε := by
  have heps : 0 < ε / 2 := half_pos hε
  filter_upwards [normal_positive_uniform_unitary_orbit e hfinite ψ hψ q hq horth
    (ε / 2) heps] with n hn G hG
  exact (unitaryOrbitHull_eval_bound (positiveFunctionalCLM ψ) (q n) (ε / 2)
    (fun u => (hn u).le) G hG).trans_lt (half_lt_self hε)

end KadisonRingrose
end BoundedHochschild

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_CompleteAdditivity
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.UltrapowerBridge.instStarTracialQuotient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Complete additivity on orthogonal projections

This is the complete-additivity condition of Ringrose, Section 4 (Takesaki's
normality criterion), expressed through the net of finite partial sums.
-/

noncomputable section

open Filter Topology

namespace BoundedHochschild
namespace KadisonRingrose

open HochschildNormalPart

universe u

variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

lemma normal_completelyAdditive (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    {F : StrongDual ℂ M} (hF : F ∈ normalDual e) : CompletelyAdditive F := by
  classical
  intro I p hp horth P hP hu hl
  obtain ⟨Q, hQ, hqu, hql, ht⟩ := exists_orthogonal_projection_sum e p hp horth
  have hQP : Q = P := le_antisymm (hql P hP hu) (hl Q hQ hqu)
  subst Q
  obtain ⟨z, hz⟩ := (mem_normalDual e F).mp hF
  have hconv : Tendsto (fun s : Finset I => F (∑ i ∈ s, p i)) atTop (𝓝 (F P)) := by
    simpa only [hz] using (ht z).star
  simpa only [map_sum] using hconv

end KadisonRingrose
end BoundedHochschild

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_FiniteNormalState
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Normal states and the remaining tracial averaging step

A normal state faithful on central projections is faithful on positive
central elements. The property passes to its actual central corner.
Composing such a state with a faithful normal positive central averaging
map gives a faithful normal tracial state. Constructing that map from
finiteness is a separate remaining theorem; no such map is postulated here.
-/

noncomputable section

open Filter Topology
open scoped ComplexOrder

namespace BoundedHochschild
namespace KadisonRingrose

open HochschildCorners

universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- The support projection of a null positive contraction is null for a normal functional. -/
lemma exists_null_support_projection (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (ψ : M →ₚ[ℂ] ℂ) (hψ : TraceInPredual e ψ) {c : M}
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hψc : ψ c = 0) :
    ∃ r : M, IsSupportProjection c r ∧ ψ r = 0 := by
  obtain ⟨r, hr, ht⟩ := HochschildSakai.exists_support_contraction e c hc0 hc1
  have hpow (n : ℕ) : ψ ((1 - c) ^ n) = ψ 1 := by
    induction n with
    | zero => simp only [pow_zero]
    | succ n ih =>
      rw [pow_succ', sub_mul, one_mul, map_sub,
        positive_contraction_zero_mul ψ hc0 hc1 hψc, sub_zero, ih]
  have hzero (n : ℕ) : ψ (1 - (1 - c) ^ n) = 0 := by
    rw [map_sub, hpow, sub_self]
  refine ⟨r, hr, ?_⟩
  have hl := trace_predual_tendsto e ψ hψ ht
  have heq : (fun n : ℕ => ψ (1 - (1 - c) ^ n)) = (fun _ : ℕ => (0 : ℂ)) := funext hzero
  rw [heq] at hl
  exact tendsto_nhds_unique hl tendsto_const_nhds

end KadisonRingrose
end BoundedHochschild

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_PositiveCompression
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.UltrapowerBridge.instStarTracialQuotient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normality of positive functionals localized to a projection corner. -/

noncomputable section

open scoped ComplexOrder

namespace BoundedHochschild
namespace KadisonRingrose

open HochschildNormalPart HochschildCorners

universe u

variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- A singular positive functional has zero mass on every corner where its
compression is normal. -/
theorem singular_zero_of_normal_compression (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    {p : M} (hp : IsStarProjection p) (ψ : M →ₚ[ℂ] ℂ)
    (hs : scalarNormalPart e (positiveFunctionalCLM ψ) = 0)
    (hn : TraceInPredual e (compressionPositive hp ψ)) : ψ p = 0 := by
  have hfix := scalarNormalPart_fixes e ((mem_normalDual e (positiveFunctionalCLM (compressionPositive hp ψ))).mpr hn)
  rw [compressionPositive_clm, scalarNormalPart_comp_left, scalarNormalPart_comp_right, hs] at hfix
  have hc : positiveFunctionalCLM (compressionPositive hp ψ) = 0 := by
    rw [compressionPositive_clm]
    simpa only [ContinuousLinearMap.zero_comp] using hfix.symm
  have he := congrArg (fun F : StrongDual ℂ M => F 1) hc
  change ψ (p * 1 * p) = 0 at he
  simpa only [mul_one, hp.isIdempotentElem.eq] using he

end KadisonRingrose
end BoundedHochschild

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_PositiveCompleteAdditivity
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.UltrapowerBridge.instStarTracialQuotient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Complete additivity implies normality for positive functionals

The positive-functional case of Takesaki's criterion, as proved in Ringrose,
*Lectures on the trace in a finite von Neumann algebra*, Lemmas 4.1--4.3.
Only this case is needed for the normal-state orbit in the trace construction.
-/

noncomputable section

open scoped ComplexOrder

namespace BoundedHochschild
namespace KadisonRingrose

open HochschildNormalPart

universe u

variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- A positive completely additive functional is normal. -/
theorem positive_normal_of_completelyAdditive (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (ψ : M →ₚ[ℂ] ℂ) (hψ : CompletelyAdditive (positiveFunctionalCLM ψ)) :
    TraceInPredual e ψ := by
  classical
  let χ := positiveSingularPart e ψ
  have hχeq : positiveFunctionalCLM χ =
      positiveFunctionalCLM ψ - scalarNormalPart e (positiveFunctionalCLM ψ) :=
    positiveSingularPart_eq e ψ
  have hχadd : CompletelyAdditive (positiveFunctionalCLM χ) := by
    rw [hχeq]
    exact hψ.sub (normal_completelyAdditive e (scalarNormalPart_mem e _))
  have hχsing : scalarNormalPart e (positiveFunctionalCLM χ) = 0 := by
    rw [hχeq, map_sub, scalarNormalPart_fixes e (scalarNormalPart_mem e _), sub_self]
  have hχzero : positiveFunctionalCLM χ = 0 := by
    by_contra hχne
    have hχ1 : χ 1 ≠ 0 := fun hz => hχne (positiveFunctional_zero_of_one_zero χ hz)
    obtain ⟨E, hE, hχE, hfaith⟩ := exists_additive_positive_support e χ hχadd
    have hE0 : E ≠ 0 := by
      intro hE0
      apply hχ1
      rw [← hχE, hE0, map_zero]
    obtain ⟨φ, hφ, hlarge⟩ := exists_normal_positive_larger_on_projection e hE hE0 (χ E).re
    let F := positiveFunctionalCLM φ - positiveFunctionalCLM χ
    have hF : CompletelyAdditive F := (normal_completelyAdditive e
      ((mem_normalDual e (positiveFunctionalCLM φ)).mpr hφ)).sub hχadd
    obtain ⟨p, hp, hpE, hEp, hnonneg⟩ := exists_nonnegative_projection_corner e F hF hE
    have hFE : 0 < (F E).re := by
      change 0 < (φ E - χ E).re
      rw [Complex.sub_re]
      exact sub_pos.mpr hlarge
    have hp0 : p ≠ 0 := by
      intro hp0
      rw [hp0, map_zero, Complex.zero_re] at hEp
      linarith
    have hdom : ∀ q : M, IsStarProjection q → q ≤ p → χ q ≤ φ q := by
      intro q hq hqp
      apply sub_nonneg.mp
      apply Complex.nonneg_iff.mpr
      constructor
      · exact hnonneg q hq hqp
      · have hχq : (χ q).im = 0 := (Complex.im_eq_zero_iff_isSelfAdjoint _).mpr
          (hq.isSelfAdjoint.map χ)
        have hφq : (φ q).im = 0 := (Complex.im_eq_zero_iff_isSelfAdjoint _).mpr
          (hq.isSelfAdjoint.map φ)
        simp only [Complex.sub_im, hφq, hχq, sub_self]
    have hn := compression_normal_of_projection_dominance e hp χ φ hφ hdom
    have hpnull := singular_zero_of_normal_compression e hp χ hχsing hn
    exact hp0 (hfaith p hp hpE hpnull)
  have hfix : scalarNormalPart e (positiveFunctionalCLM ψ) = positiveFunctionalCLM ψ := by
    rw [hχeq] at hχzero
    exact (sub_eq_zero.mp hχzero).symm
  apply (mem_normalDual e (positiveFunctionalCLM ψ)).mp
  rw [← hfix]
  exact scalarNormalPart_mem e _

end KadisonRingrose
end BoundedHochschild

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_PositiveOrbitCompactness
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.UltrapowerBridge.instStarTracialQuotient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Weak compactness of positive normal orbits

The positive-functional specialization of Ringrose, Theorem 4.7 and Lemma 5.3.
The gliding-block estimate and complete-additivity criterion ensure that no
singular functional enters the weak-star closure.
-/

noncomputable section

open Filter Topology
open scoped ComplexOrder

namespace BoundedHochschild
namespace KadisonRingrose

open HochschildNormalPart

universe u

variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- A uniform orthogonal-sequence estimate makes every positive weak-star
cluster functional normal. -/
theorem weakFunctionalClosure_normal (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (K : Set (StrongDual ℂ M))
    (hpos : ∀ F ∈ K, ∀ a : M, 0 ≤ a → 0 ≤ F a)
    (hnormal : ∀ F ∈ K, F ∈ normalDual e)
    (hdecay : ∀ q : ℕ → M, (∀ n, IsStarProjection (q n)) →
      (∀ m n, m ≠ n → q m * q n = 0) → ∀ ε : ℝ, 0 < ε →
        ∀ᶠ n in atTop, ∀ F ∈ K, ‖F (q n)‖ < ε)
    {F : WeakDual ℂ M} (hF : F ∈ weakFunctionalClosure K) :
    WeakDual.toStrongDual F ∈ normalDual e := by
  classical
  have hFpos := weakFunctionalClosure_positive K hpos hF
  let ψ : M →ₚ[ℂ] ℂ :=
    { toLinearMap := (WeakDual.toStrongDual F).toLinearMap
      monotone' := (monotone_iff_map_nonneg _).mpr hFpos }
  apply (mem_normalDual e (positiveFunctionalCLM ψ)).mpr
  apply positive_normal_of_completelyAdditive e ψ
  intro I p hp ho P hP hu hl
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨s, hs⟩ := uniform_orthogonal_sum_remainder K
    (fun G hG => normal_completelyAdditive e (hnormal G hG))
    hdecay I p hp ho P hP hu hl (ε / 2) (half_pos hε)
  have hsmall : (F (P - ∑ i ∈ s, p i)).re ≤ ε / 2 := by
    apply closure_minimal
      (t := {G : WeakDual ℂ M | (G (P - ∑ i ∈ s, p i)).re ≤ ε / 2}) _
      (isClosed_le (Complex.continuous_re.comp (WeakDual.eval_continuous _))
        continuous_const) hF
    rintro _ ⟨G, hGK, rfl⟩
    exact (hs G hGK).le
  refine ⟨s, fun t hst => ?_⟩
  have hsum : (∑ i ∈ s, p i) ≤ ∑ i ∈ t, p i :=
    Finset.sum_le_sum_of_subset_of_nonneg hst (fun i _ _ => (hp i).nonneg)
  have htail : 0 ≤ P - ∑ i ∈ t, p i :=
    sub_nonneg.mpr (orthogonal_projection_finset_sum_le p hp ho hP hu t)
  have horder : 0 ≤ F (P - ∑ i ∈ s, p i) - F (P - ∑ i ∈ t, p i) := by
    rw [← map_sub]
    apply hFpos
    exact sub_nonneg.mpr (sub_le_sub_left hsum P)
  have hposval := hFpos _ htail
  have hnorm : ‖F (P - ∑ i ∈ t, p i)‖ ≤ ε / 2 := by
    have hle : F (P - ∑ i ∈ t, p i) ≤ (ε / 2 : ℝ) := by
      apply Complex.le_def.mpr
      constructor
      · exact ((Complex.nonneg_iff.mp horder).1 |> fun h => by
          rw [Complex.sub_re] at h
          simpa only [Complex.ofReal_re] using (by linarith : (F (P - ∑ i ∈ t, p i)).re ≤ ε / 2))
      · simpa only [Complex.ofReal_im] using (Complex.nonneg_iff.mp hposval).2.symm
    calc
      ‖F (P - ∑ i ∈ t, p i)‖ ≤ ‖((ε / 2 : ℝ) : ℂ)‖ :=
        CStarAlgebra.norm_le_norm_of_le_of_nonneg hle hposval
      _ = ε / 2 := Complex.norm_of_nonneg (half_pos hε).le
  rw [dist_eq_norm, ← map_sum]
  change ‖F (∑ i ∈ t, p i) - F P‖ < ε
  simpa only [map_sub, norm_sub_rev] using hnorm.trans_lt (half_lt_self hε)

/-- The weak-star closure of the positive normal orbit is compact. -/
theorem normal_positive_orbit_compact (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (hfinite : FiniteAlgebra M) (ψ : M →ₚ[ℂ] ℂ) (hψ : TraceInPredual e ψ) :
    IsCompact (weakFunctionalClosure (unitaryOrbitHull (positiveFunctionalCLM ψ))) ∧
      ∀ F ∈ weakFunctionalClosure (unitaryOrbitHull (positiveFunctionalCLM ψ)),
        WeakDual.toStrongDual F ∈ normalDual e := by
  constructor
  · apply (WeakDual.isCompact_closedBall (0 : StrongDual ℂ M)
      ‖positiveFunctionalCLM ψ‖).of_isClosed_subset isClosed_closure
    apply closure_minimal _ (WeakDual.isClosed_closedBall 0 _)
    rintro _ ⟨G, hG, rfl⟩
    simpa only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right,
      StrongDual.toStrongDual_toWeakDual] using
      unitaryOrbitHull_norm_le (positiveFunctionalCLM ψ) hG
  · intro F hF
    apply weakFunctionalClosure_normal e _ (unitaryOrbitHull_positive ψ)
      (fun _ hG => unitaryOrbitHull_normal e
        ((mem_normalDual e (positiveFunctionalCLM ψ)).mpr hψ) hG) _ hF
    exact fun q hq ho ε hε => normal_positive_uniform_orbit_hull e hfinite ψ hψ q hq ho ε hε

end KadisonRingrose
end BoundedHochschild

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_WeakPredual
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The normal dual, with its weak-star topology, is the weak predual. -/

noncomputable section

open Topology
open scoped ComplexOrder

namespace BoundedHochschild
namespace KadisonRingrose

open HochschildNormalPart

universe u

variable {M X : Type u} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]

variable [PartialOrder M] [StarOrderedRing M] [CompleteSpace X]

/-- The positive unitary orbit has a compact realization in the weak predual. -/
theorem normal_positive_predual_orbit_compact (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (hfinite : FiniteAlgebra M) (ψ : M →ₚ[ℂ] ℂ) (hψ : TraceInPredual e ψ) :
    IsCompact ((weakPredualMap e) ⁻¹'
      weakFunctionalClosure (unitaryOrbitHull (positiveFunctionalCLM ψ))) := by
  obtain ⟨hc, hn⟩ := normal_positive_orbit_compact e hfinite ψ hψ
  apply (weakPredualMap_isEmbedding e).isInducing.isCompact_preimage' hc
  intro F hF
  rw [range_weakPredualMap]
  exact hn F hF

end KadisonRingrose
end BoundedHochschild

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_UnitaryPredualAction
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.UltrapowerBridge.instStarTracialQuotient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The isometric unitary action on a von Neumann predual. -/

noncomputable section

open Topology

namespace BoundedHochschild
namespace KadisonRingrose

open HochschildNormalPart

universe u

variable {M X : Type u} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

variable [PartialOrder M] [StarOrderedRing M]

/-- Pullback by the inverse unitary gives a left group action on the predual. -/
def unitaryPredualAction (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (u : unitary M) : X ≃ₗᵢ[ℂ] X :=
  (predualNormalEquiv e).trans
    ((normalUnitaryEquiv e (star u)).trans (predualNormalEquiv e).symm)

lemma predualEmbedding_unitaryAction (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (u : unitary M) (x : X) :
    predualEmbedding e (unitaryPredualAction e u x) =
      unitaryPullback (predualEmbedding e x) (star u) := by
  have h := congrArg Subtype.val ((predualNormalEquiv e).apply_symm_apply
    (normalUnitaryEquiv e (star u) (predualNormalEquiv e x)))
  exact h

lemma unitaryPredualAction_one (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (x : X) :
    unitaryPredualAction e 1 x = x := by
  apply (predualEmbedding e).injective
  rw [predualEmbedding_unitaryAction, star_one, unitaryPullback_one]

lemma unitaryPredualAction_mul (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (u v : unitary M) (x : X) :
    unitaryPredualAction e (u * v) x = unitaryPredualAction e u (unitaryPredualAction e v x) := by
  apply (predualEmbedding e).injective
  simp only [predualEmbedding_unitaryAction, unitaryPullback_mul, star_mul]

end KadisonRingrose
end BoundedHochschild

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_NormalOrbitInvariance
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.UltrapowerBridge.instStarTracialQuotient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Convexity and invariance of the compact normal-state orbit. -/

noncomputable section

open Topology

namespace BoundedHochschild
namespace KadisonRingrose

open HochschildNormalPart

universe u

variable {M X : Type u} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

variable [PartialOrder M] [StarOrderedRing M]

lemma weakPredualOrbit_invariant (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (F : StrongDual ℂ M)
    (u : unitary M) :
    Set.MapsTo (weakIsometry (unitaryPredualAction e u))
      ((weakPredualMap e) ⁻¹' weakFunctionalClosure (unitaryOrbitHull F))
      ((weakPredualMap e) ⁻¹' weakFunctionalClosure (unitaryOrbitHull F)) := by
  intro x hx
  have heq : weakPredualMap e (weakIsometry (unitaryPredualAction e u) x) =
      weakUnitaryPullback (star u) (weakPredualMap e x) := by
    apply WeakDual.toStrongDual.injective
    exact predualEmbedding_unitaryAction e u ((toWeakSpace ℂ X).symm x)
  change weakPredualMap e (weakIsometry (unitaryPredualAction e u) x) ∈
    weakFunctionalClosure (unitaryOrbitHull F)
  rw [heq]
  exact weakOrbitClosure_invariant F (star u) hx

end KadisonRingrose
end BoundedHochschild

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_FiniteNormalTrace
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.UltrapowerBridge.instStarTracialQuotient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Normal traces in finite von Neumann algebras

Ringrose, Theorem 5.4: the compact convex unitary orbit of a positive normal
functional contains a normal trace with the same values on the center.
This construction assumes no scalar or center-valued trace.
-/

noncomputable section

open Topology
open scoped ComplexOrder

namespace BoundedHochschild
namespace KadisonRingrose

open HochschildNormalPart

universe u

variable {M X : Type u} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

variable [PartialOrder M] [StarOrderedRing M]

/-- Every positive normal functional on a finite von Neumann algebra has a
normal tracial average agreeing with it on the center. -/
theorem exists_normal_tracial_average (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (hfinite : FiniteAlgebra M) (ψ : M →ₚ[ℂ] ℂ) (hψ : TraceInPredual e ψ) :
    ∃ τ : M →ₚ[ℂ] ℂ, TraceInPredual e τ ∧ τ 1 = ψ 1 ∧
      (∀ a b : M, τ (a * b) = τ (b * a)) ∧
      ∀ a : M, (∀ b : M, a * b = b * a) → τ a = ψ a := by
  classical
  let C : Set (WeakSpace ℂ X) := (weakPredualMap e) ⁻¹'
    weakFunctionalClosure (unitaryOrbitHull (positiveFunctionalCLM ψ))
  have hC : IsCompact C := normal_positive_predual_orbit_compact e hfinite ψ hψ
  obtain ⟨z, hz⟩ := hψ
  have hemb : predualEmbedding e z = positiveFunctionalCLM ψ := by
    ext a
    exact (hz a).symm
  have hn : C.Nonempty := by
    refine ⟨toWeakSpace ℂ X z, ?_⟩
    change StrongDual.toWeakDual (predualEmbedding e z) ∈
      weakFunctionalClosure (unitaryOrbitHull (positiveFunctionalCLM ψ))
    rw [hemb]
    apply subset_closure
    refine ⟨positiveFunctionalCLM ψ, ?_, rfl⟩
    have hmem := subset_closure (subset_convexHull ℝ
      (Set.range (unitaryPullback (positiveFunctionalCLM ψ))) (Set.mem_range_self 1))
    simpa only [unitaryPullback_one, unitaryOrbitHull] using hmem
  obtain ⟨x, hx, hfix⟩ := weakCompact_isometric_fixedPoint (unitaryPredualAction e)
    (unitaryPredualAction_one e) (unitaryPredualAction_mul e) C hC hn
    (weakPredualOrbit_convex e _) (weakPredualOrbit_invariant e _)
  let F := weakPredualMap e x
  have hFpos : ∀ a : M, 0 ≤ a → 0 ≤ F a :=
    weakFunctionalClosure_positive _ (unitaryOrbitHull_positive ψ) hx
  let τ : M →ₚ[ℂ] ℂ :=
    { toLinearMap := (WeakDual.toStrongDual F).toLinearMap
      monotone' := (monotone_iff_map_nonneg _).mpr hFpos }
  have hτnormal : TraceInPredual e τ := by
    exact ⟨(toWeakSpace ℂ X).symm x, fun _ => rfl⟩
  have hτcenter (a : M) (ha : ∀ b : M, a * b = b * a) : τ a = ψ a :=
    weakFunctionalClosure_eval_eq _ a (ψ a)
      (unitaryOrbitHull_central (positiveFunctionalCLM ψ) ha) hx
  have hτinv : ∀ (u : unitary M) (a : M), τ ((u : M) * a * star (u : M)) = τ a := by
    intro u a
    have hxfix : unitaryPredualAction e (star u) ((toWeakSpace ℂ X).symm x) =
        (toWeakSpace ℂ X).symm x := congrArg (toWeakSpace ℂ X).symm (hfix (star u))
    have heq := congrArg (predualEmbedding e) hxfix
    rw [predualEmbedding_unitaryAction, star_star] at heq
    exact congrArg (fun f : StrongDual ℂ M => f a) heq
  exact ⟨τ, hτnormal, hτcenter 1 (fun b => by rw [one_mul, mul_one]),
    tracial_of_unitary_invariant (positiveFunctionalCLM τ) hτinv, hτcenter⟩

end KadisonRingrose
end BoundedHochschild

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_IsometryDefectColumns
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.UltrapowerBridge.instStarTracialQuotient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Orthogonal columns from an isometry defect

A nonunitary isometry supplies countably many equivalent, orthogonal defect
projections. This is an algebraic ingredient of the properly infinite case.
-/

noncomputable section

namespace BoundedHochschild.KadisonRingrose

open HochschildComparison

variable {M : Type*} [CStarAlgebra M]

lemma isometryColumn_star_mul_of_lt {v p : M} (hv : star v * v = 1)
    (hp : IsStarProjection p) (hpv : p * v = 0) {i j : ℕ} (hij : i < j) :
    star (isometryColumn v hv p hp i : M) * (isometryColumn v hv p hp j : M) = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hij
  have hpk : p * v ^ (k + 1) = 0 := by
    rw [pow_succ', ← mul_assoc, hpv, zero_mul]
  simp only [isometryColumn_coe, star_mul, hp.isSelfAdjoint.star_eq]
  calc
    _ = p * (star (v ^ i) * v ^ (i + (k + 1))) * p := by
      simp only [mul_assoc, Nat.add_assoc]
    _ = 0 := by rw [isometry_pow_cancel hv, hpk, zero_mul]

lemma isometryColumn_star_mul_of_ne {v p : M} (hv : star v * v = 1)
    (hp : IsStarProjection p) (hpv : p * v = 0) {i j : ℕ} (hij : i ≠ j) :
    star (isometryColumn v hv p hp i : M) * (isometryColumn v hv p hp j : M) = 0 := by
  rcases lt_or_gt_of_ne hij with h | h
  · exact isometryColumn_star_mul_of_lt hv hp hpv h
  · simpa only [star_mul, star_star, star_zero] using
      congrArg star (isometryColumn_star_mul_of_lt hv hp hpv h)

lemma isometryColumn_final_orthogonal {v p : M} (hv : star v * v = 1)
    (hp : IsStarProjection p) (hpv : p * v = 0) {i j : ℕ} (hij : i ≠ j) :
    (isometryColumn v hv p hp i).final * (isometryColumn v hv p hp j).final = 0 := by
  change (((isometryColumn v hv p hp i : M) * star (isometryColumn v hv p hp i : M)) *
    ((isometryColumn v hv p hp j : M) * star (isometryColumn v hv p hp j : M))) = 0
  rw [mul_assoc, ← mul_assoc (star (isometryColumn v hv p hp i : M)),
    isometryColumn_star_mul_of_ne hv hp hpv hij, zero_mul, mul_zero]

end BoundedHochschild.KadisonRingrose

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_ProperlyInfiniteColumns
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.UltrapowerBridge.instStarTracialQuotient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Properly infinite projections from orthogonal columns

Countably many equivalent orthogonal projections split into even and odd
columns. The resulting operators are actual partial isometries in the algebra.
-/

noncomputable section

namespace BoundedHochschild.KadisonRingrose

open HochschildComparison

universe u

variable {M : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- The supremum of countably many equivalent orthogonal projections is
properly infinite. Only the particular even/odd shift operators are needed. -/
theorem properlyInfinite_of_columns (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    {p : M} (c : ℕ → PartialIso M) (hi : ∀ i, (c i).initial = p)
    (ho : ∀ i j, i ≠ j → (c i).final * (c j).final = 0) :
    ∃ q : M, IsStarProjection q ∧ ProperlyInfiniteProjection q ∧
      (∀ i, (c i).final ≤ q) ∧
      (∀ r : M, IsStarProjection r → (∀ i, (c i).final ≤ r) → q ≤ r) := by
  obtain ⟨q, hq, hqi, hqmin, _⟩ := exists_orthogonal_projection_sum e
    (fun i => (c i).final) (fun i => (c i).final_proj) ho
  let a (i : ℕ) := columnTransition (c (2 * i)) (c i) ((hi _).trans (hi _).symm)
  let b (i : ℕ) := columnTransition (c (2 * i + 1)) (c i) ((hi _).trans (hi _).symm)
  have hai (i) : (a i).initial = (c i).final := columnTransition_initial ..
  have hbi (i) : (b i).initial = (c i).final := columnTransition_initial ..
  have haf (i) : (a i).final = (c (2 * i)).final := columnTransition_final ..
  have hbf (i) : (b i).final = (c (2 * i + 1)).final := columnTransition_final ..
  obtain ⟨v, hvi, _, hvi_min, hvf_min⟩ := exists_countable_partialIso_sum e a
    (fun i j hij => by rw [hai, hai]; exact ho i j hij)
    (fun i j hij => by rw [haf, haf]; exact ho _ _ (by omega))
  obtain ⟨w, hwi, _, hwi_min, hwf_min⟩ := exists_countable_partialIso_sum e b
    (fun i j hij => by rw [hbi, hbi]; exact ho i j hij)
    (fun i j hij => by rw [hbf, hbf]; exact ho _ _ (by omega))
  have hvq : v.initial = q := le_antisymm
    (hvi_min q hq (fun i => by rw [hai]; exact hqi i))
    (hqmin _ v.initial_proj (fun i => by rw [← hai]; exact hvi i))
  have hwq : w.initial = q := le_antisymm
    (hwi_min q hq (fun i => by rw [hbi]; exact hqi i))
    (hqmin _ w.initial_proj (fun i => by rw [← hbi]; exact hwi i))
  refine ⟨q, hq, ⟨v, w, hvq, hwq,
    hvf_min q hq (fun i => by rw [haf]; exact hqi _),
    hwf_min q hq (fun i => by rw [hbf]; exact hqi _), ?_⟩, hqi, hqmin⟩
  have hw_even (i : ℕ) : w.final ≤ 1 - (a i).final := by
    apply hwf_min _ (a i).final_proj.one_sub
    intro j
    apply projection_le_complement_of_mul_zero (b j).final_proj (a i).final_proj
    rw [hbf, haf]
    exact ho _ _ (by omega)
  have hav (i : ℕ) : (a i).final ≤ 1 - w.final := by
    apply projection_le_complement_of_mul_zero (a i).final_proj w.final_proj
    exact HochschildTypeII.projection_orthogonal_of_le_complement (a i).final_proj
      w.final_proj (hw_even i)
  have h := HochschildTypeII.projection_orthogonal_of_le_complement w.final_proj
    v.final_proj (hvf_min _ w.final_proj.one_sub hav)
  simpa only [star_mul, v.final_proj.isSelfAdjoint.star_eq,
    w.final_proj.isSelfAdjoint.star_eq, star_zero] using congrArg star h

/-- A nonunitary isometry produces a nonzero properly infinite projection. -/
theorem nonunitary_isometry_has_properlyInfinite_projection
    (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) {v : M} (hv : star v * v = 1)
    (hnot : v * star v ≠ 1) :
    ∃ q : M, IsStarProjection q ∧ q ≠ 0 ∧ ProperlyInfiniteProjection q := by
  let p := isometryDefect v
  have hp : IsStarProjection p := isometryDefect_projection hv
  let c := isometryColumn v hv p hp
  obtain ⟨q, hq, hproper, hqi, _⟩ := properlyInfinite_of_columns e c
    (fun i => isometryColumn_initial ..)
    (fun i j hij => isometryColumn_final_orthogonal hv hp (isometryDefect_mul hv) hij)
  refine ⟨q, hq, ?_, hproper⟩
  intro hq0
  have hp0 : p = 0 := by
    have h : p ≤ q := by
      simpa only [c, isometryColumn, PartialIso.final, pow_zero, one_mul,
        hp.isSelfAdjoint.star_eq, hp.isIdempotentElem.eq] using hqi 0
    exact le_antisymm (hq0 ▸ h) hp.nonneg
  exact hnot (sub_eq_zero.mp hp0).symm

end BoundedHochschild.KadisonRingrose

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_TraceFreeHalving
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.UltrapowerBridge.instStarTracialQuotient
attribute [-simp] _root_.OAI.BoundedHochschild.KadisonRingrose.adjointPartialIso_final _root_.OAI.BoundedHochschild.KadisonRingrose.adjointPartialIso_initial _root_.OAI.BoundedHochschild.KadisonRingrose.centralCutPartialIso_final _root_.OAI.BoundedHochschild.KadisonRingrose.centralCutPartialIso_initial _root_.OAI.BoundedHochschild.KadisonRingrose.columnTransition_final _root_.OAI.BoundedHochschild.KadisonRingrose.columnTransition_initial _root_.OAI.BoundedHochschild.KadisonRingrose.composePartialIso_initial _root_.OAI.BoundedHochschild.KadisonRingrose.isometryColumn_coe _root_.OAI.BoundedHochschild.KadisonRingrose.isometryColumn_initial _root_.OAI.BoundedHochschild.KadisonRingrose.matrixSystemOfColumns_diagonal _root_.OAI.BoundedHochschild.KadisonRingrose.partialIsoCornerEquiv_apply _root_.OAI.BoundedHochschild.KadisonRingrose.partialIsoFromCorner_final _root_.OAI.BoundedHochschild.KadisonRingrose.partialIsoFromCorner_initial _root_.OAI.BoundedHochschild.KadisonRingrose.partialIsoInCorner_final _root_.OAI.BoundedHochschild.KadisonRingrose.partialIsoInCorner_initial _root_.OAI.HochschildComparison.Frame.zero_part _root_.OAI.HochschildComparison.PartialIso.ofProjection_coe _root_.OAI.HochschildComparison.PartialIso.ofProjection_final _root_.OAI.HochschildComparison.PartialIso.ofProjection_initial _root_.OAI.HochschildComparison.PartialIso.restrict_coe _root_.OAI.HochschildComparison.PartialIso.restrict_initial _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.PopaPatching.Rep.toCorner_initial _root_.OAI.PopaPatching.Rep.toCorner_val
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Halving projections without a trace

Orthogonality of initial and final projections is preserved by increasing
chains of partial isometries. A maximal such partial isometry exhausts any
projection in an algebra with no nonzero abelian corners.
-/

noncomputable section

namespace BoundedHochschild
namespace KadisonRingrose

open HochschildComparison

universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- The initial/final orthogonality condition is closed under chain suprema. -/
lemma orthogonal_partialIso_chain_upper (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    {p : M} (hp : IsStarProjection p)
    (c : Set (PartialIso M)) (hc : IsChain (· ≤ ·) c) (hne : c.Nonempty)
    (hs : ∀ v ∈ c, v.initial ≤ p ∧ v.final ≤ p ∧ v.initial * v.final = 0) :
    ∃ w : PartialIso M, w.initial ≤ p ∧ w.final ≤ p ∧
      w.initial * w.final = 0 ∧ ∀ v ∈ c, v ≤ w := by
  obtain ⟨w, hu, _, hi, hf⟩ := exists_partialIso_chain_supremum e c hc hne
  have hcross (v : PartialIso M) (hv : v ∈ c) (z : PartialIso M) (hz : z ∈ c) :
      v.initial * z.final = 0 := by
    rcases hc.total hv hz with h | h
    · calc
        v.initial * z.final = (v.initial * z.initial) * z.final := by
          rw [(v.initial_proj.le_iff_mul_eq_left z.initial_proj).mp h.1]
        _ = 0 := by rw [mul_assoc, (hs z hz).2.2, mul_zero]
    · calc
        v.initial * z.final = v.initial * (v.final * z.final) := by
          rw [(z.final_proj.le_iff_mul_eq_right v.final_proj).mp
            (PartialIso.final_mono h)]
        _ = 0 := by rw [← mul_assoc, (hs v hv).2.2, zero_mul]
  have hwi (v : PartialIso M) (hv : v ∈ c) : w.initial * v.final = 0 := by
    have hb : w.initial ≤ 1 - v.final := hi _ v.final_proj.one_sub (fun z hz =>
      (z.initial_proj.le_iff_mul_eq_left v.final_proj.one_sub).mpr (by
        rw [mul_sub, mul_one, hcross z hz v hv, sub_zero]))
    have he := (w.initial_proj.le_iff_mul_eq_left v.final_proj.one_sub).mp hb
    rw [mul_sub, mul_one] at he
    exact sub_eq_self.mp he
  have hfinal : w.final ≤ 1 - w.initial := hf _ w.initial_proj.one_sub (fun v hv => by
    apply (v.final_proj.le_iff_mul_eq_left w.initial_proj.one_sub).mpr
    have ho : v.final * w.initial = 0 := by
      simpa only [star_mul, w.initial_proj.isSelfAdjoint.star_eq,
        v.final_proj.isSelfAdjoint.star_eq, star_zero] using congrArg star (hwi v hv)
    rw [mul_sub, mul_one, ho, sub_zero])
  refine ⟨w, hi p hp (fun v hv => (hs v hv).1),
    hf p hp (fun v hv => (hs v hv).2.1), ?_, hu⟩
  have he := (w.final_proj.le_iff_mul_eq_right w.initial_proj.one_sub).mp hfinal
  rw [sub_mul, one_mul] at he
  exact sub_eq_self.mp he

/-- Every projection in a von Neumann algebra without abelian corners is the
sum of the orthogonal initial and final projections of a partial isometry. -/
theorem exists_trace_free_halving (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (hII : PopaTypeII.NoAbelianCorners M) {p : M} (hp : IsStarProjection p) :
    ∃ v : PartialIso M, v.initial * v.final = 0 ∧ v.initial + v.final = p := by
  classical
  let S : Set (PartialIso M) :=
    {v | v.initial ≤ p ∧ v.final ≤ p ∧ v.initial * v.final = 0}
  have hz : (0 : PartialIso M) ∈ S :=
    ⟨by simpa using hp.nonneg, by simpa using hp.nonneg, by simp⟩
  obtain ⟨v, _, hmax⟩ := zorn_le_nonempty₀ S (fun c hc hchain y hy => by
    obtain ⟨w, hwi, hwf, hwo, hu⟩ := orthogonal_partialIso_chain_upper e hp c hchain
      ⟨y, hy⟩ (fun z hz => hc hz)
    exact ⟨w, ⟨hwi, hwf, hwo⟩, hu⟩) 0 hz
  have hvi : v.initial ≤ p := hmax.1.1
  have hvf : v.final ≤ p := hmax.1.2.1
  have hvo : v.initial * v.final = 0 := hmax.1.2.2
  have hsum : IsStarProjection (v.initial + v.final) :=
    v.initial_proj.add v.final_proj hvo
  have hsump : v.initial + v.final ≤ p := by
    apply (hsum.le_iff_mul_eq_right hp).mpr
    rw [mul_add, (v.initial_proj.le_iff_mul_eq_right hp).mp hvi,
      (v.final_proj.le_iff_mul_eq_right hp).mp hvf]
  let r : M := p - (v.initial + v.final)
  have hr : IsStarProjection r := (hsum.le_iff_sub hp).mp hsump
  have hrI : r ≤ p - v.initial :=
    sub_le_sub_left (le_add_of_nonneg_right v.final_proj.nonneg) p
  have hrF : r ≤ p - v.final :=
    sub_le_sub_left (le_add_of_nonneg_left v.initial_proj.nonneg) p
  have hr0 : r = 0 := by
    by_contra hr0
    obtain ⟨u, huo, hu0⟩ := PopaTypeII.orthogonal_pair e hII hr hr0
    let U : PartialIso M := ⟨(u : M), by
      simpa only [← mul_assoc] using u.absorb⟩
    have hUi : U.initial ≤ r := u.init_le
    have hUf : U.final ≤ r := u.final_le
    have hUo : U.initial * U.final = 0 := huo
    have hi : v.initial * U.initial = 0 :=
      PopaCorners.CornerIso.projection_mul_zero_of_le_sub hp v.initial_proj U.initial_proj
        hvi (hUi.trans hrI)
    have hf : v.final * U.final = 0 :=
      PopaCorners.CornerIso.projection_mul_zero_of_le_sub hp v.final_proj U.final_proj
        hvf (hUf.trans hrF)
    have hiF : v.initial * U.final = 0 :=
      PopaCorners.CornerIso.projection_mul_zero_of_le_sub hp v.initial_proj U.final_proj
        hvi (hUf.trans hrI)
    have hfI : U.initial * v.final = 0 := by
      have h := PopaCorners.CornerIso.projection_mul_zero_of_le_sub hp v.final_proj U.initial_proj
        hvf (hUi.trans hrF)
      simpa only [star_mul, v.final_proj.isSelfAdjoint.star_eq,
        U.initial_proj.isSelfAdjoint.star_eq, star_zero] using congrArg star h
    have hW : v.orthogonalSum U hi hf ∈ S := by
      constructor
      · rw [PartialIso.orthogonalSum_initial]
        calc
          v.initial + U.initial ≤ v.initial + (p - v.initial) :=
            add_le_add_right (hUi.trans hrI) _
          _ = p := by abel
      constructor
      · rw [PartialIso.orthogonalSum_final]
        calc
          v.final + U.final ≤ v.final + (p - v.final) :=
            add_le_add_right (hUf.trans hrF) _
          _ = p := by abel
      · rw [PartialIso.orthogonalSum_initial, PartialIso.orthogonalSum_final,
          add_mul, mul_add, mul_add, hvo, hiF, hfI, hUo, zero_add, add_zero]
    have hle := v.le_orthogonalSum U hi hf
    have heq := le_antisymm (hmax.2 hW hle) hle
    have he : (v : M) + (u : M) = v :=
      congrArg (fun z : PartialIso M => (z : M)) heq
    exact hu0 (add_eq_left.mp he)
  exact ⟨v, hvo, (sub_eq_zero.mp hr0).symm⟩

end KadisonRingrose
end BoundedHochschild

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_TypeIICharacterization
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.UltrapowerBridge.instStarTracialQuotient
attribute [-simp] _root_.OAI.BoundedHochschild.KadisonRingrose.adjointPartialIso_final _root_.OAI.BoundedHochschild.KadisonRingrose.adjointPartialIso_initial _root_.OAI.BoundedHochschild.KadisonRingrose.centralCutPartialIso_final _root_.OAI.BoundedHochschild.KadisonRingrose.centralCutPartialIso_initial _root_.OAI.BoundedHochschild.KadisonRingrose.columnTransition_final _root_.OAI.BoundedHochschild.KadisonRingrose.columnTransition_initial _root_.OAI.BoundedHochschild.KadisonRingrose.composePartialIso_initial _root_.OAI.BoundedHochschild.KadisonRingrose.isometryColumn_coe _root_.OAI.BoundedHochschild.KadisonRingrose.isometryColumn_initial _root_.OAI.BoundedHochschild.KadisonRingrose.matrixSystemOfColumns_diagonal _root_.OAI.BoundedHochschild.KadisonRingrose.partialIsoFromCorner_final _root_.OAI.BoundedHochschild.KadisonRingrose.partialIsoFromCorner_initial _root_.OAI.BoundedHochschild.KadisonRingrose.partialIsoInCorner_final _root_.OAI.BoundedHochschild.KadisonRingrose.partialIsoInCorner_initial _root_.OAI.HochschildComparison.Frame.zero_part _root_.OAI.HochschildComparison.PartialIso.ofProjection_coe _root_.OAI.HochschildComparison.PartialIso.ofProjection_final _root_.OAI.HochschildComparison.PartialIso.ofProjection_initial _root_.OAI.HochschildComparison.PartialIso.restrict_coe _root_.OAI.HochschildComparison.PartialIso.restrict_initial _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Type II structure without an assumed trace

A nonzero abelian projection has a central type I support, with the type I
condition tested on all subprojections. Thus absence of a type I central
part is equivalent to absence of abelian corners, before constructing a
trace. The projection-halving theorem can consequently use exactly the
type II hypothesis of the main application.
-/

noncomputable section

open scoped ComplexOrder

namespace BoundedHochschild
namespace KadisonRingrose

open FinitePathMain HochschildComparison

universe u

variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- A nonzero abelian projection generates a nonzero central type I part. -/
theorem exists_typeICorner_support (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    {p : M} (hp : IsStarProjection p) (hpa : PopaTypeII.AbelianProjection hp)
    (hp0 : p ≠ 0) :
    ∃ (z : M) (hz : IsStarProjection z), (∀ a : M, z * a = a * z) ∧
      p ≤ z ∧ z ≠ 0 ∧ PopaTypeII.TypeICorner hz := by
  classical
  let S : Set M := {s | CentralProjection s ∧ s * p = 0}
  have hzero : (0 : M) ∈ S :=
    ⟨⟨IsStarProjection.zero M, fun _ => Commute.zero_left _⟩, zero_mul _⟩
  obtain ⟨s, _, hmax⟩ := zorn_le_nonempty₀ S (fun c hc hchain y hy => by
    obtain ⟨t, ht, htp, hu⟩ := central_annihilator_chain e p c hchain ⟨y, hy⟩
      (fun q hq => hc hq)
    exact ⟨t, ⟨ht, htp⟩, hu⟩) 0 hzero
  have hs : CentralProjection s := hmax.1.1
  have hsp : s * p = 0 := hmax.1.2
  have hz : IsStarProjection (1 - s) := hs.1.one_sub
  have hzc : ∀ a : M, (1 - s) * a = a * (1 - s) := by
    intro a
    exact ((Commute.one_left a).sub_left (hs.2 a)).eq
  have hpz : p ≤ 1 - s := (hp.le_iff_mul_eq_right hz).mpr
    (by rw [sub_mul, one_mul, hsp, sub_zero])
  refine ⟨1 - s, hz, hzc, hpz, ?_, ?_⟩
  · intro h
    exact hp0 (le_antisymm (h ▸ hpz) hp.nonneg)
  · intro q hq hqz hq0
    have hex : ∃ a : M, q * a * p ≠ 0 := by
      by_contra hn
      push Not at hn
      obtain ⟨r, hr, hqr, hrp⟩ := exists_trace_free_central_separator e hq hp hn
      let t := (1 - s) * r
      have ht : CentralProjection t :=
        ⟨hz.mul hr.1 (hzc r), fun a => (show Commute (1 - s) a from hzc a).mul_left (hr.2 a)⟩
      have hst : s * t = 0 := by
        dsimp [t]
        rw [← mul_assoc, hs.1.mul_one_sub_self, zero_mul]
      have htp : t * p = 0 := by
        dsimp [t]
        rw [mul_assoc, hrp, mul_zero]
      have hnew : s + t ∈ S :=
        ⟨⟨hs.1.add ht.1 hst, fun a => (hs.2 a).add_left (ht.2 a)⟩,
          by rw [add_mul, hsp, htp, zero_add]⟩
      have hle : s ≤ s + t := le_add_of_nonneg_right ht.1.nonneg
      have ht0 : t = 0 := add_eq_left.mp (le_antisymm (hmax.2 hnew hle) hle)
      have htq : t * q = q := by
        dsimp [t]
        rw [mul_assoc, (hq.le_iff_mul_eq_right hr.1).mp hqr,
          (hq.le_iff_mul_eq_right hz).mp hqz]
      exact hq0 (by simpa only [ht0, zero_mul] using htq.symm)
    obtain ⟨a, ha⟩ := hex
    obtain ⟨v, hv0, hvi, hvf⟩ := partialIso_of_nonzero_corner e hq hp (q * a * p) ha
      (by rw [← mul_assoc, ← mul_assoc, hq.isIdempotentElem.eq])
      (by rw [mul_assoc, hp.isIdempotentElem.eq])
    have hfinal0 : v.final ≠ 0 := by
      intro h
      apply hv0
      simpa only [h, zero_mul] using v.final_mul.symm
    exact ⟨v.final, v.final_proj, hvf, hfinal0,
      abelianProjection_partialIso v (abelian_projection_mono hp v.initial_proj hvi hpa)⟩

/-- The two type II hypotheses agree for every von Neumann algebra, without
a faithful normal trace hypothesis. -/
theorem noTypeICentralPart_iff_noAbelianCorners (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) :
    PopaTypeII.NoTypeICentralPart M ↔ PopaTypeII.NoAbelianCorners M := by
  constructor
  · intro hM p hp hp0
    by_contra hn
    push Not at hn
    have hab : PopaTypeII.AbelianProjection hp := fun a b => hn a b
    obtain ⟨z, hz, hzc, _, hz0, hI⟩ := exists_typeICorner_support e hp hab hp0
    exact hM z hz (fun a => hzc a) hz0 hI
  · intro hM z hz _ hz0 hI
    obtain ⟨p, hp, _, hp0, hab⟩ := hI z hz le_rfl hz0
    obtain ⟨a, b, h⟩ := hM p hp hp0
    exact h (hab a b)

/-- Exact type II projection halving, before the finite trace is constructed. -/
theorem typeII_projection_halving (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (hII : PopaTypeII.NoTypeICentralPart M) {p : M} (hp : IsStarProjection p) :
    ∃ v : PartialIso M, v.initial * v.final = 0 ∧ v.initial + v.final = p :=
  exists_trace_free_halving e ((noTypeICentralPart_iff_noAbelianCorners e).mp hII) hp

end KadisonRingrose
end BoundedHochschild

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_ProperlyInfiniteCorners
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instPartialOrderSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.UltrapowerBridge.instStarTracialQuotient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Corner transport and finiteness obstructions for properly infinite projections. -/

noncomputable section

namespace BoundedHochschild.KadisonRingrose

open HochschildComparison HochschildCorners FinitePathMain

universe u

variable {M : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

omit [PartialOrder M] [StarOrderedRing M] in
lemma finiteCorner_of_equivalent (v : PartialIso M) (h : FiniteCorner v.final) :
    FiniteCorner v.initial := by
  apply (finiteCorner_iff v.initial v.initial_proj).mpr
  exact finiteAlgebra_of_equiv (partialIsoCornerEquiv v)
    ((finiteCorner_iff v.final v.final_proj).mp h)

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- Every infinite corner contains a nonzero properly infinite projection. -/
theorem exists_properlyInfinite_subprojection (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    {p : M} (hp : IsStarProjection p) (h : ¬ FiniteCorner p) :
    ∃ q : M, IsStarProjection q ∧ q ≤ p ∧ q ≠ 0 ∧ ProperlyInfiniteProjection q := by
  have hn : ¬ FiniteAlgebra (Corner p hp) := fun hfin => h ((finiteCorner_iff p hp).mpr hfin)
  simp only [FiniteAlgebra, not_forall] at hn
  obtain ⟨v, hvi, hvf⟩ := hn
  obtain ⟨q, hq, hq0, hproper⟩ := nonunitary_isometry_has_properlyInfinite_projection
    (cornerPredualEquiv p hp e) hvi hvf
  exact ⟨(q : M), corner_projection_coe p hp hq, corner_projection_le p hp hq,
    fun hz => hq0 (Subtype.ext hz), properlyInfinite_from_corner hp hproper⟩

end BoundedHochschild.KadisonRingrose

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_InfinitePairChains
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.UltrapowerBridge.instStarTracialQuotient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Increasing chains of pairs implementing properly infinite projections. -/

noncomputable section

namespace BoundedHochschild.KadisonRingrose

open HochschildComparison

universe u

variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

lemma infinitePair_cross_orthogonal {C : Set (PartialIso M × PartialIso M)}
    (hC : ∀ a ∈ C, IsInfinitePair a) (hchain : IsChain (· ≤ ·) C)
    {a b : PartialIso M × PartialIso M} (ha : a ∈ C) (hb : b ∈ C) :
    a.1.final * b.2.final = 0 := by
  rcases hchain.total ha hb with h | h
  · calc
      _ = (a.1.final * b.1.final) * b.2.final := by
        rw [(a.1.final_proj.le_iff_mul_eq_left b.1.final_proj).mp (PartialIso.final_mono h.1)]
      _ = 0 := by rw [mul_assoc, (hC b hb).2.2.2, mul_zero]
  · calc
      _ = a.1.final * (a.2.final * b.2.final) := by
        rw [(b.2.final_proj.le_iff_mul_eq_right a.2.final_proj).mp (PartialIso.final_mono h.2)]
      _ = 0 := by rw [← mul_assoc, (hC a ha).2.2.2, zero_mul]

/-- The pair order preserves both common initial supports and orthogonality
at a chain supremum. -/
theorem infinitePair_chain_upper (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (C : Set (PartialIso M × PartialIso M)) (hC : ∀ a ∈ C, IsInfinitePair a)
    (hchain : IsChain (· ≤ ·) C) (hne : C.Nonempty) :
    ∃ a : PartialIso M × PartialIso M, IsInfinitePair a ∧ ∀ b ∈ C, b ≤ a := by
  let L := Prod.fst '' C
  let R := Prod.snd '' C
  have hL : IsChain (· ≤ ·) L := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ _
    exact (hchain.total ha hb).imp (fun h => h.1) (fun h => h.1)
  have hR : IsChain (· ≤ ·) R := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ _
    exact (hchain.total ha hb).imp (fun h => h.2) (fun h => h.2)
  obtain ⟨v, hv, _, hvi, hvf⟩ := exists_partialIso_chain_supremum e L hL (hne.image _)
  obtain ⟨w, hw, _, hwi, hwf⟩ := exists_partialIso_chain_supremum e R hR (hne.image _)
  have hV (a) (ha : a ∈ C) : a.1 ≤ v := hv a.1 ⟨a, ha, rfl⟩
  have hW (a) (ha : a ∈ C) : a.2 ≤ w := hw a.2 ⟨a, ha, rfl⟩
  have hi : v.initial = w.initial := by
    apply le_antisymm
    · apply hvi _ w.initial_proj
      rintro _ ⟨a, ha, rfl⟩
      rw [(hC a ha).1]
      exact (hW a ha).1
    · apply hwi _ v.initial_proj
      rintro _ ⟨a, ha, rfl⟩
      rw [← (hC a ha).1]
      exact (hV a ha).1
  have hfv : v.final ≤ v.initial := by
    apply hvf _ v.initial_proj
    rintro _ ⟨a, ha, rfl⟩
    exact (hC a ha).2.1.trans (hV a ha).1
  have hfw : w.final ≤ v.initial := by
    apply hwf _ v.initial_proj
    rintro _ ⟨a, ha, rfl⟩
    exact (hC a ha).2.2.1.trans (hV a ha).1
  have hcross (a) (ha : a ∈ C) : a.1.final * w.final = 0 := by
    have hbound : w.final ≤ 1 - a.1.final := by
      apply hwf _ a.1.final_proj.one_sub
      rintro _ ⟨b, hb, rfl⟩
      have ho := infinitePair_cross_orthogonal hC hchain ha hb
      apply projection_le_complement_of_mul_zero b.2.final_proj a.1.final_proj
      simpa only [star_mul, a.1.final_proj.isSelfAdjoint.star_eq,
        b.2.final_proj.isSelfAdjoint.star_eq, star_zero] using congrArg star ho
    exact HochschildTypeII.projection_orthogonal_of_le_complement a.1.final_proj
      w.final_proj hbound
  have hfinal : v.final ≤ 1 - w.final := by
    apply hvf _ w.final_proj.one_sub
    rintro _ ⟨a, ha, rfl⟩
    exact projection_le_complement_of_mul_zero a.1.final_proj w.final_proj (hcross a ha)
  have ho : v.final * w.final = 0 := by
    have h := (v.final_proj.le_iff_mul_eq_left w.final_proj.one_sub).mp hfinal
    rw [mul_sub, mul_one] at h
    exact sub_eq_self.mp h
  exact ⟨(v, w), ⟨hi, hfv, hfw, ho⟩, fun a ha => ⟨hV a ha, hW a ha⟩⟩

end BoundedHochschild.KadisonRingrose

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_NormalTraceFaithfulness
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.UltrapowerBridge.instStarTracialQuotient
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A normal trace faithful on the center is faithful on the whole algebra. -/

noncomputable section

open Filter Topology
open scoped ComplexOrder

namespace BoundedHochschild
namespace KadisonRingrose

universe u

variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

lemma normal_tracial_null_projection_join (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (τ : M →ₚ[ℂ] ℂ) (htr : ∀ a b : M, τ (a * b) = τ (b * a))
    {p q : M} (hp : IsStarProjection p) (hq : IsStarProjection q)
    (htp : τ p = 0) (htq : τ q = 0) :
    ∃ r : M, IsStarProjection r ∧ p ≤ r ∧ q ≤ r ∧ τ r = 0 := by
  obtain ⟨v, hvq, _, hr, hpr, hqr, _⟩ := exists_trace_free_projection_join e p q hp hq
  have hvi : τ v.initial = 0 := le_antisymm ((τ.monotone hvq).trans_eq htq)
    (τ.map_nonneg v.initial_proj.nonneg)
  have hvf : τ v.final = 0 := (htr v.val (star v.val)).trans hvi
  exact ⟨p + v.final, hr, hpr, hqr, by rw [map_add, htp, hvf, add_zero]⟩

/-- The largest projection annihilated by a normal trace is central. -/
theorem normal_trace_largest_null_projection (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (τ : M →ₚ[ℂ] ℂ) (hτ : TraceInPredual e τ)
    (htr : ∀ a b : M, τ (a * b) = τ (b * a)) :
    ∃ p : M, IsStarProjection p ∧ (∀ a : M, p * a = a * p) ∧ τ p = 0 ∧
      ∀ q : M, IsStarProjection q → τ q = 0 → q ≤ p := by
  classical
  let S : Set M := {p | IsStarProjection p ∧ τ p = 0}
  obtain ⟨p, _, hmax⟩ := zorn_le_nonempty₀ S (fun c hc hchain a ha => by
    obtain ⟨p, hp, hu, _, _, U, _, ht⟩ :=
      exists_projection_chain_supremum_with_limit e c ⟨a, ha⟩ hchain
        (fun q hq => (hc hq).1)
    refine ⟨p, ⟨hp, ?_⟩, hu⟩
    have heq : (fun q : c => τ (q : M)) = (fun _ : c => (0 : ℂ)) :=
      funext (fun q => (hc q.property).2)
    have hlim := trace_predual_tendsto e τ hτ ht
    rw [heq] at hlim
    exact tendsto_nhds_unique hlim tendsto_const_nhds) 0
      (show (0 : M) ∈ S from ⟨IsStarProjection.zero M, map_zero τ⟩)
  have hp := hmax.1.1
  have hnull := hmax.1.2
  have hgreat (q : M) (hq : IsStarProjection q) (htq : τ q = 0) : q ≤ p := by
    obtain ⟨r, hr, hpr, hqr, htr0⟩ := normal_tracial_null_projection_join e τ htr hp hq hnull htq
    exact hqr.trans (hmax.2 ⟨hr, htr0⟩ hpr)
  have hconj (u : unitary M) : (u : M) * p * star (u : M) ≤ p := by
    apply hgreat
    · constructor
      · change ((u : M) * p * star (u : M)) * ((u : M) * p * star (u : M)) =
          (u : M) * p * star (u : M)
        calc
          _ = (u : M) * (p * ((star (u : M) * (u : M)) * p)) * star (u : M) := by
            noncomm_ring
          _ = _ := by rw [Unitary.star_mul_self_of_mem u.property, one_mul, hp.isIdempotentElem.eq]
      · change star ((u : M) * p * star (u : M)) = (u : M) * p * star (u : M)
        simp only [star_mul, star_star, hp.isSelfAdjoint.star_eq, mul_assoc]
    · rw [htr, ← mul_assoc, Unitary.star_mul_self_of_mem u.property, one_mul, hnull]
  have hfix (u : unitary M) : (u : M) * p * star (u : M) = p := by
    apply le_antisymm (hconj u)
    have h := star_right_conjugate_le_conjugate (hconj (star u)) (u : M)
    simp only [Unitary.coe_star, star_star, mul_assoc,
      Unitary.mul_star_self_of_mem u.property, mul_one] at h
    have huus : (u : M) * (star (u : M) * p) = p := by
      rw [← mul_assoc, Unitary.mul_star_self_of_mem u.property, one_mul]
    rw [huus] at h
    simpa only [mul_assoc] using h
  have hcomm (u : unitary M) : p * (u : M) = (u : M) * p := by
    have h := congrArg (fun a : M => a * (u : M)) (hfix u)
    simpa only [mul_assoc, Unitary.star_mul_self_of_mem u.property, mul_one] using h.symm
  refine ⟨p, hp, ?_, hnull, hgreat⟩
  intro a
  obtain ⟨u, c, rfl, _⟩ := CStarAlgebra.exists_sum_four_unitary a
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_smul_comm, smul_mul_assoc, hcomm]

/-- Faithfulness on central projections suffices for a normal trace. -/
theorem normal_trace_faithful_of_center (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (τ : M →ₚ[ℂ] ℂ) (hτ : TraceInPredual e τ)
    (htr : ∀ a b : M, τ (a * b) = τ (b * a))
    (hcenter : ∀ p : M, IsStarProjection p → (∀ a : M, p * a = a * p) →
      τ p = 0 → p = 0) : ∀ a : M, τ (star a * a) = 0 → a = 0 := by
  obtain ⟨p, hp, hpc, hnull, hgreat⟩ := normal_trace_largest_null_projection e τ hτ htr
  have hp0 : p = 0 := hcenter p hp hpc hnull
  intro a ha
  let t : ℝ := ‖star a * a‖ + 1
  have ht : 0 < t := by dsimp [t]; positivity
  let c : M := t⁻¹ • (star a * a)
  have hc0 : 0 ≤ c := smul_nonneg (inv_nonneg.mpr ht.le) (star_mul_self_nonneg a)
  have hcn : ‖c‖ ≤ 1 := by
    rw [show c = t⁻¹ • (star a * a) from rfl, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr ht)]
    exact (inv_mul_le_one₀ ht).mpr (by dsimp [t]; linarith)
  have hc1 : c ≤ 1 := (CStarAlgebra.norm_le_one_iff_of_nonneg c hc0).mp hcn
  have hτc : τ c = 0 := by
    rw [show c = t⁻¹ • (star a * a) from rfl, τ.map_smul_of_tower, ha, smul_zero]
  obtain ⟨q, hq, hτq⟩ := exists_null_support_projection e τ hτ hc0 hc1 hτc
  have hq0 : q = 0 := le_antisymm (hp0 ▸ hgreat q hq.proj hτq) hq.proj.nonneg
  have hc : c = 0 := by simpa only [hq0, zero_mul] using hq.left.symm
  have haa : star a * a = 0 := (smul_eq_zero.mp hc).resolve_left (inv_ne_zero ht.ne')
  apply norm_eq_zero.mp
  have hn := congrArg norm haa
  rw [CStarRing.norm_star_mul_self, norm_zero] at hn
  nlinarith [norm_nonneg a]

end KadisonRingrose
end BoundedHochschild

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_MaximalInfiniteProjection
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.UltrapowerBridge.instStarTracialQuotient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A maximal properly infinite projection has finite complement. -/

noncomputable section

namespace BoundedHochschild.KadisonRingrose

open HochschildComparison

universe u

variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- A von Neumann algebra contains a properly infinite projection with finite
complement. This includes the zero projection when the algebra is finite. -/
theorem exists_properlyInfinite_with_finite_complement (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) :
    ∃ p : M, IsStarProjection p ∧ ProperlyInfiniteProjection p ∧ FiniteCorner (1 - p) := by
  classical
  let S : Set (PartialIso M × PartialIso M) := {a | IsInfinitePair a}
  have hzero : ((0, 0) : PartialIso M × PartialIso M) ∈ S := by
    simp only [S, Set.mem_ofPred_eq, IsInfinitePair, PartialIso.initial_zero,
      PartialIso.final_zero, le_refl, mul_zero, and_self]
  obtain ⟨a, _, hm⟩ := zorn_le_nonempty₀ S (fun C hC hchain b hb => by
    obtain ⟨c, hc, hu⟩ := infinitePair_chain_upper e C (fun a ha => hC ha) hchain ⟨b, hb⟩
    exact ⟨c, hc, hu⟩) (0, 0) hzero
  have ha : IsInfinitePair a := hm.1
  let p := a.1.initial
  have hp : IsStarProjection p := a.1.initial_proj
  refine ⟨p, hp, ⟨a.1, a.2, rfl, ha.1.symm, ha.2.1, ha.2.2.1, ha.2.2.2⟩, ?_⟩
  by_contra hn
  obtain ⟨q, hq, hqp, hq0, u, w, hui, hwi, huf, hwf, huw⟩ :=
    exists_properlyInfinite_subprojection e hp.one_sub hn
  have hpq : p * q = 0 := HochschildTypeII.projection_orthogonal_of_le_complement hp hq hqp
  have hi1 : a.1.initial * u.initial = 0 := by rw [hui]; exact hpq
  have hi2 : a.2.initial * w.initial = 0 := by rw [← ha.1, hwi]; exact hpq
  have hf1 : a.1.final * u.final = 0 :=
    projection_mul_zero_of_bounds hp hq a.1.final_proj u.final_proj hpq ha.2.1 huf
  have hf2 : a.2.final * w.final = 0 :=
    projection_mul_zero_of_bounds hp hq a.2.final_proj w.final_proj hpq ha.2.2.1 hwf
  let b := (a.1.orthogonalSum u hi1 hf1, a.2.orthogonalSum w hi2 hf2)
  have hbi : b.1.initial = p + q := by rw [PartialIso.orthogonalSum_initial, hui]
  have hbii : b.2.initial = p + q := by rw [PartialIso.orthogonalSum_initial, ← ha.1, hwi]
  have hbf : b.1.final = a.1.final + u.final := by
    exact PartialIso.orthogonalSum_final a.1 u hi1 hf1
  have hbff : b.2.final = a.2.final + w.final := by
    exact PartialIso.orthogonalSum_final a.2 w hi2 hf2
  have hb : b ∈ S := by
    refine ⟨hbi.trans hbii.symm, ?_, ?_, ?_⟩
    · rw [hbf, hbi]
      exact add_le_add ha.2.1 huf
    · rw [hbff, hbi]
      exact add_le_add ha.2.2.1 hwf
    · have hcross1 : a.1.final * w.final = 0 :=
        projection_mul_zero_of_bounds hp hq a.1.final_proj w.final_proj hpq ha.2.1 hwf
      have hcross2 : u.final * a.2.final = 0 := by
        have h := projection_mul_zero_of_bounds hp hq a.2.final_proj u.final_proj
          hpq ha.2.2.1 huf
        simpa only [star_mul, a.2.final_proj.isSelfAdjoint.star_eq,
          u.final_proj.isSelfAdjoint.star_eq, star_zero] using congrArg star h
      rw [hbf, hbff]
      simp only [add_mul, mul_add, ha.2.2.2, huw, hcross1, hcross2, zero_add]
  have hab : a ≤ b := ⟨a.1.le_orthogonalSum u hi1 hf1, a.2.le_orthogonalSum w hi2 hf2⟩
  have he := le_antisymm (hm.2 hb hab) hab
  have hip : p + q = p := by
    have h := congrArg (fun b : PartialIso M × PartialIso M => b.1.initial) he
    exact hbi.symm.trans h
  exact hq0 (add_eq_left.mp hip)

end BoundedHochschild.KadisonRingrose

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_ProperlyInfiniteIsometries
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.UltrapowerBridge.instStarTracialQuotient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Two isometries in an algebra without finite central summands

Comparison embeds the finite complement of a maximal properly infinite
projection into that projection. Its two orthogonal copies then absorb the
complement and give isometries with initial projection one.
-/

noncomputable section

namespace BoundedHochschild.KadisonRingrose

open HochschildComparison FinitePathMain

universe u

variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

lemma finite_complement_embeds_properlyInfinite (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (hno : NoFiniteCentralSummand M) {p : M} (hp : IsStarProjection p)
    (hproper : ProperlyInfiniteProjection p) (hfin : FiniteCorner (1 - p)) :
    ∃ t : PartialIso M, t.initial = 1 - p ∧ t.final ≤ p := by
  obtain ⟨z, t, hz, hti, htf, hzf, hzi⟩ := trace_free_central_comparison e hp.one_sub hp
  let s := centralCutPartialIso z hz.1 (fun a => (hz.2 a).eq) t
  have hsi : s.initial ≤ t.initial := by
    apply (s.initial_proj.le_iff_mul_eq_left t.initial_proj).mpr
    rw [centralCutPartialIso_initial, mul_assoc, t.initial_proj.isIdempotentElem.eq]
  have hsi_fin : FiniteCorner s.initial :=
    finiteCorner_mono s.initial_proj hp.one_sub (hsi.trans hti) hfin
  have hsf_fin : FiniteCorner s.final := by
    simpa only [adjointPartialIso_initial, adjointPartialIso_final] using
      finiteCorner_of_equivalent (adjointPartialIso s) (by
        simpa only [adjointPartialIso_final] using hsi_fin)
  have hzpfin : FiniteCorner (z * p) := by
    simpa only [s, centralCutPartialIso_final, hzf] using hsf_fin
  have hzp : IsStarProjection (z * p) := hz.1.mul hp (hz.2 p)
  have hzp0 : z * p = 0 := properlyInfinite_finite_eq_zero hzp
    (properlyInfinite_central_cut hp hz hproper) hzpfin
  have hzfin : FiniteCorner z := finiteCorner_mono hz.1 hp.one_sub
    (projection_le_complement_of_mul_zero hz.1 hp hzp0) hfin
  have hz0 : z = 0 := hno z hz.1 (fun a => (hz.2 a).eq)
    ((finiteCorner_iff z hz.1).mp hzfin)
  refine ⟨t, ?_, htf⟩
  simpa only [hz0, sub_zero, one_mul] using hzi

/-- The unit is properly infinite when no nonzero central corner is finite. -/
theorem properlyInfinite_one (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (hno : NoFiniteCentralSummand M) : ProperlyInfiniteProjection (1 : M) := by
  obtain ⟨p, hp, hproper, hfin⟩ := exists_properlyInfinite_with_finite_complement e
  obtain ⟨t, hti, htf⟩ := finite_complement_embeds_properlyInfinite e hno hp hproper hfin
  obtain ⟨v, w, hvi, hwi, hvf, hwf, ho⟩ := hproper
  let b := composePartialIso w t (by rw [hwi]; exact htf)
  have hbi : b.initial = 1 - p := by rw [composePartialIso_initial, hti]
  have hbf : b.final ≤ w.final := composePartialIso_final_le ..
  have hi : v.initial * b.initial = 0 := by rw [hvi, hbi, hp.mul_one_sub_self]
  have hf : v.final * b.final = 0 := projection_mul_zero_of_bounds v.final_proj w.final_proj
    v.final_proj b.final_proj ho le_rfl hbf
  let a := v.orthogonalSum b hi hf
  have hai : a.initial = 1 := by
    rw [PartialIso.orthogonalSum_initial, hvi, hbi]
    abel
  have haf : a.final ≤ p := by
    apply (a.final_proj.le_iff_mul_eq_right hp).mpr
    rw [PartialIso.orthogonalSum_final, mul_add,
      (v.final_proj.le_iff_mul_eq_right hp).mp hvf,
      (b.final_proj.le_iff_mul_eq_right hp).mp (hbf.trans hwf)]
  let V := composePartialIso v a (by rw [hvi]; exact haf)
  let W := composePartialIso w a (by rw [hwi]; exact haf)
  have hV : V.final ≤ v.final := composePartialIso_final_le ..
  have hW : W.final ≤ w.final := composePartialIso_final_le ..
  exact ⟨V, W, (composePartialIso_initial ..).trans hai,
    (composePartialIso_initial ..).trans hai, V.final_proj.le_one, W.final_proj.le_one,
    projection_mul_zero_of_bounds v.final_proj w.final_proj V.final_proj W.final_proj ho hV hW⟩

/-- Actual orthogonal isometries, with no trace, separability, or factor assumption. -/
theorem exists_two_orthogonal_isometries (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (hno : NoFiniteCentralSummand M) :
    ∃ v w : M, star v * v = 1 ∧ star w * w = 1 ∧ star v * w = 0 := by
  obtain ⟨v, w, hvi, hwi, _, _, ho⟩ := properlyInfinite_one e hno
  exact ⟨(v : M), (w : M), hvi, hwi, PartialIso.star_mul_eq_zero_of_final_orthogonal ho⟩

end BoundedHochschild.KadisonRingrose

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_MatrixFunctionalDilation
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.UltrapowerBridge.instStarTracialQuotient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A positive functional on a matrix algebra gives a completely positive
map into the corresponding finite-dimensional operator algebra. -/

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace BoundedHochschild.KadisonRingrose

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def matrixFunctionalCP {n : ℕ} (F : CStarMatrix (Fin n) (Fin n) A →ₚ[ℂ] ℂ)
    (i₀ : Fin n) : CompletelyPositiveMap A
      (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) :=
  compressCompletelyPositive
    (CompletelyPositiveMapClass.toCompletelyPositiveLinearMap
      (F.gnsStarAlgHom.comp (matrixScalarHom n))) (matrixFunctionalEmbedding F i₀)

end BoundedHochschild.KadisonRingrose

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_OperatorSystemMatrices
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The scalar matrix functional used in finite-dimensional positive extension. -/

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace BoundedHochschild.KadisonRingrose

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def operatorSystemMatrixFunctional (S : Submodule ℂ A) (φ : S →ₗ[ℂ] (H →L[ℂ] H))
    {n : ℕ} (ξ : Fin n → H) : operatorSystemMatrices S n →ₗ[ℂ] ℂ :=
  (operatorMatrixVectorFunctional ξ).toLinearMap.comp (operatorSystemAmplification S φ n)

end BoundedHochschild.KadisonRingrose

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_PositiveUnitBlocks
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.UltrapowerBridge.instStarTracialQuotient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The elementary two-by-two positivity test for a contraction. -/

noncomputable section

open scoped ComplexOrder

namespace BoundedHochschild.KadisonRingrose

open HochschildMatrixDilation

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def positiveUnitBlock (a : A) : Mat A := 1 + offdiag a (star a)

end BoundedHochschild.KadisonRingrose

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_PositiveBlocks
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.UltrapowerBridge.instStarTracialQuotient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normalize the two diagonal entries of a positive two-by-two block. -/

noncomputable section

open scoped ComplexOrder

namespace BoundedHochschild.KadisonRingrose

open HochschildMatrixDilation

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def positiveBlock (p q x : A) : Mat A := diag p q + offdiag x (star x)

end BoundedHochschild.KadisonRingrose

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_PaulsenSystem
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero
attribute [-simp] _root_.OAI.HochschildMatrixDilation.diag_pow _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The unital two-by-two operator system associated to a linear map. -/

noncomputable section

namespace BoundedHochschild.KadisonRingrose

open HochschildMatrixDilation

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

def paulsenSystem (A : Type*) [CStarAlgebra A] : Submodule ℂ (Mat A) where
  carrier := {X | ∃ z w : ℂ, X 0 0 = algebraMap ℂ A z ∧ X 1 1 = algebraMap ℂ A w}
  zero_mem' := ⟨0, 0, by simp, by simp⟩
  add_mem' := by
    rintro X Y ⟨z, w, hz, hw⟩ ⟨z', w', hz', hw'⟩
    exact ⟨z + z', w + w', by simp only [CStarMatrix.add_apply, map_add, hz, hz'],
      by simp only [CStarMatrix.add_apply, map_add, hw, hw']⟩
  smul_mem' := by
    rintro c X ⟨z, w, hz, hw⟩
    refine ⟨c * z, c * w, ?_, ?_⟩
    · simp only [CStarMatrix.smul_apply, hz, Algebra.smul_def, map_mul]
    · simp only [CStarMatrix.smul_apply, hw, Algebra.smul_def, map_mul]

lemma paulsenSystem_one : (1 : Mat A) ∈ paulsenSystem A := by
  exact ⟨1, 1, by simp, by simp⟩

def paulsenLinear (f : A →ₗ[ℂ] ℂ) (T : A →ₗ[ℂ] B) : Mat A →ₗ[ℂ] Mat B where
  toFun X := CStarMatrix.ofMatrix !![
    algebraMap ℂ B (f (X 0 0)), T (X 0 1);
    starConjugateLinear T (X 1 0), algebraMap ℂ B (f (X 1 1))]
  map_add' X Y := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_smul' z X := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Algebra.algebraMap_eq_smul_one, smul_smul]

def paulsenSystemMap (f : A →ₗ[ℂ] ℂ) (T : A →ₗ[ℂ] B) : paulsenSystem A →ₗ[ℂ] Mat B :=
  (paulsenLinear f T).comp (paulsenSystem A).subtype

end BoundedHochschild.KadisonRingrose

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_PaulsenMatrixBlocks
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Identify amplified two-by-two operator systems with scalar-diagonal blocks. -/

noncomputable section

open scoped ComplexOrder

namespace BoundedHochschild.KadisonRingrose

open HochschildMatrixDilation

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

variable [PartialOrder A] [StarOrderedRing A]

def paulsenMatrixDiagonal (f : A →ₗ[ℂ] ℂ) {n : ℕ} (i : Fin 2)
    (X : operatorSystemMatrices (paulsenSystem A) n) : CStarMatrix (Fin n) (Fin n) ℂ :=
  CStarMatrix.ofMatrix (fun p q => f (X.val p q i i))

def paulsenMatrixUpper {n : ℕ} (X : operatorSystemMatrices (paulsenSystem A) n) :
    CStarMatrix (Fin n) (Fin n) A := CStarMatrix.ofMatrix (fun p q => X.val p q 0 1)

end BoundedHochschild.KadisonRingrose

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_StinespringLeftAction
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.UltrapowerBridge.instStarTracialQuotient
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Left multiplication on the auxiliary positive-kernel Hilbert space. -/

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace BoundedHochschild.KadisonRingrose

variable {M H : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma stinespringLeft_bound (φ : CompletelyPositiveMap M (H →L[ℂ] H)) (b : M)
    (x : (M × H) →₀ ℂ) :
    (kernelForm (fun p q => stinespringKernel φ (stinespringLeftLabel b p)
      (stinespringLeftLabel b q)) x x).re ≤ ‖b‖ ^ 2 * (kernelForm (stinespringKernel φ) x x).re := by
  classical
  change (kernelForm (fun p q : M × H => inner ℂ p.2
    (φ (star (b * p.1) * (b * q.1)) q.2)) x x).re ≤
      ‖b‖ ^ 2 * (kernelForm (fun p q : M × H => inner ℂ p.2
        (φ (star p.1 * q.1) q.2)) x x).re
  rw [kernelForm_coefficients, kernelForm_coefficients]
  exact completelyPositive_kernel_left_bound φ (fun p : x.support => p.val.1)
    (fun p : x.support => x p • p.val.2) b

/-- The bounded left action before completing the kernel space. -/
def stinespringPreOperator (φ : CompletelyPositiveMap M (H →L[ℂ] H)) (b : M) :
    StinespringPreSpace φ →L[ℂ] StinespringPreSpace φ :=
  kernelPreMap (stinespringKernel φ) (stinespringKernel_positive φ)
    (stinespringLeftLabel b) ‖b‖ (norm_nonneg _) (stinespringLeft_bound φ b)

/-- The induced action on the separated Hilbert completion. -/
def stinespringOperator (φ : CompletelyPositiveMap M (H →L[ℂ] H)) (b : M) :
    StinespringSpace φ →L[ℂ] StinespringSpace φ :=
  (stinespringPreOperator φ b).completion

@[simp] lemma stinespringOperator_coe (φ : CompletelyPositiveMap M (H →L[ℂ] H))
    (b : M) (x : StinespringPreSpace φ) :
    stinespringOperator φ b x =
      (UniformSpace.Completion.coe' (stinespringShift φ b x)) := by
  exact ContinuousLinearMap.completion_apply_coe (stinespringPreOperator φ b) x

end BoundedHochschild.KadisonRingrose

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_StinespringRepresentation
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.UltrapowerBridge.instStarTracialQuotient
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The star representation obtained from the positive-kernel Hilbert space. -/

noncomputable section

open scoped ComplexOrder InnerProductSpace
open UniformSpace

namespace BoundedHochschild.KadisonRingrose

variable {M H : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma stinespringOperator_ext (φ : CompletelyPositiveMap M (H →L[ℂ] H))
    (A B : StinespringSpace φ →L[ℂ] StinespringSpace φ)
    (h : ∀ x y : StinespringPreSpace φ,
      inner ℂ (x : StinespringSpace φ) (A y) = inner ℂ (x : StinespringSpace φ) (B y)) :
    A = B := by
  apply ContinuousLinearMap.ext
  intro η
  apply ext_inner_left ℂ
  intro ξ
  induction ξ, η using Completion.induction_on₂ with
  | hp => apply isClosed_eq <;> fun_prop
  | ih x y => exact h x y

lemma stinespringOperator_inner_coe (φ : CompletelyPositiveMap M (H →L[ℂ] H))
    (b : M) (x y : StinespringPreSpace φ) :
    inner ℂ (x : StinespringSpace φ) (stinespringOperator φ b y) =
      kernelForm (fun p q : M × H => inner ℂ p.2 (φ (star p.1 * b * q.1) q.2)) x y := by
  rw [stinespringOperator_coe, Completion.inner_coe]
  change kernelForm (stinespringKernel φ) x (Finsupp.mapDomain (stinespringLeftLabel b) y) = _
  have he := kernelForm_mapDomain_right (stinespringKernel φ) (stinespringLeftLabel b)
    (show (M × H) →₀ ℂ from x) (show (M × H) →₀ ℂ from y)
  refine he.trans ?_
  congr 1
  funext p q
  simp only [stinespringKernel, stinespringLeftLabel, mul_assoc]

lemma stinespringOperator_zero (φ : CompletelyPositiveMap M (H →L[ℂ] H)) :
    stinespringOperator φ 0 = 0 := by
  apply stinespringOperator_ext φ
  intro x y
  rw [stinespringOperator_inner_coe]
  simp [kernelForm, Finsupp.sum]

lemma stinespringOperator_add (φ : CompletelyPositiveMap M (H →L[ℂ] H)) (a b : M) :
    stinespringOperator φ (a + b) = stinespringOperator φ a + stinespringOperator φ b := by
  apply stinespringOperator_ext φ
  intro x y
  simp only [add_apply, inner_add_right, stinespringOperator_inner_coe, kernelForm,
    mul_add, add_mul, map_add, Finsupp.sum, Finset.sum_add_distrib]

lemma stinespringOperator_one (φ : CompletelyPositiveMap M (H →L[ℂ] H)) :
    stinespringOperator φ 1 = 1 := by
  apply stinespringOperator_ext φ
  intro x y
  rw [stinespringOperator_coe]
  rw [stinespringShift_one]
  rfl

lemma stinespringOperator_mul (φ : CompletelyPositiveMap M (H →L[ℂ] H)) (a b : M) :
    stinespringOperator φ (a * b) = stinespringOperator φ a * stinespringOperator φ b := by
  apply stinespringOperator_ext φ
  intro x y
  rw [mul_apply_eq_comp, stinespringOperator_coe, stinespringOperator_coe,
    stinespringOperator_coe, stinespringShift_mul]

end BoundedHochschild.KadisonRingrose

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_StinespringStar
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.UltrapowerBridge.instStarTracialQuotient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The adjoint and scalar identities of the positive-kernel representation. -/

noncomputable section

open scoped ComplexOrder InnerProductSpace
open UniformSpace

namespace BoundedHochschild.KadisonRingrose

variable {M H : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma stinespringOperator_star (φ : CompletelyPositiveMap M (H →L[ℂ] H)) (b : M) :
    stinespringOperator φ (star b) = star (stinespringOperator φ b) := by
  rw [ContinuousLinearMap.star_eq_adjoint]
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro ξ η
  induction ξ, η using Completion.induction_on₂ with
  | hp => apply isClosed_eq <;> fun_prop
  | ih x y =>
    rw [stinespringOperator_coe, stinespringOperator_coe, Completion.inner_coe, Completion.inner_coe]
    change kernelForm (stinespringKernel φ) (Finsupp.mapDomain (stinespringLeftLabel (star b)) x) y =
      kernelForm (stinespringKernel φ) x (Finsupp.mapDomain (stinespringLeftLabel b) y)
    have hl := kernelForm_mapDomain_left (stinespringKernel φ) (stinespringLeftLabel (star b))
      (show (M × H) →₀ ℂ from x) (show (M × H) →₀ ℂ from y)
    have hr := kernelForm_mapDomain_right (stinespringKernel φ) (stinespringLeftLabel b)
      (show (M × H) →₀ ℂ from x) (show (M × H) →₀ ℂ from y)
    refine hl.trans ((congrArg (fun K : Matrix (M × H) (M × H) ℂ => kernelForm K x y) ?_).trans hr.symm)
    funext p q
    simp only [stinespringKernel, stinespringLeftLabel, star_mul, star_star, mul_assoc]

lemma stinespringOperator_smul (φ : CompletelyPositiveMap M (H →L[ℂ] H)) (z : ℂ) (b : M) :
    stinespringOperator φ (z • b) = z • stinespringOperator φ b := by
  apply stinespringOperator_ext φ
  intro x y
  rw [smul_apply, inner_smul_right, stinespringOperator_inner_coe, stinespringOperator_inner_coe]
  simp only [kernelForm, mul_smul_comm, smul_mul_assoc, map_smul,
    smul_apply, inner_smul_right, Finsupp.sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- The genuine unital star representation on the positive-kernel Hilbert
space associated to a completely positive map. -/
def stinespringRepresentation (φ : CompletelyPositiveMap M (H →L[ℂ] H)) :
    M →⋆ₐ[ℂ] (StinespringSpace φ →L[ℂ] StinespringSpace φ) where
  toFun := stinespringOperator φ
  map_zero' := stinespringOperator_zero φ
  map_one' := stinespringOperator_one φ
  map_add' := stinespringOperator_add φ
  map_mul' := stinespringOperator_mul φ
  map_star' := stinespringOperator_star φ
  commutes' z := by
    rw [Algebra.algebraMap_eq_smul_one, stinespringOperator_smul, stinespringOperator_one]
    rfl

end BoundedHochschild.KadisonRingrose

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_StinespringEmbedding
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.UltrapowerBridge.instStarTracialQuotient
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The bounded vector map and factorization of a completely positive map. -/

noncomputable section

open scoped ComplexOrder InnerProductSpace
open UniformSpace

namespace BoundedHochschild.KadisonRingrose

variable {M H : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def stinespringPreVector (φ : CompletelyPositiveMap M (H →L[ℂ] H)) (ξ : H) :
    StinespringPreSpace φ := Finsupp.single (1, ξ) 1

def stinespringVector (φ : CompletelyPositiveMap M (H →L[ℂ] H)) (ξ : H) :
    StinespringSpace φ := Completion.coe' (stinespringPreVector φ ξ)

lemma stinespringVector_pairing (φ : CompletelyPositiveMap M (H →L[ℂ] H))
    (x : StinespringPreSpace φ) (ξ : H) :
    inner ℂ (x : StinespringSpace φ) (stinespringVector φ ξ) =
      x.sum (fun p z => star z * inner ℂ p.2 (φ (star p.1) ξ)) := by
  classical
  rw [stinespringVector, Completion.inner_coe]
  change kernelForm (stinespringKernel φ) x (stinespringPreVector φ ξ) = _
  simp [kernelForm, stinespringKernel, stinespringPreVector]

lemma stinespringVector_add (φ : CompletelyPositiveMap M (H →L[ℂ] H)) (ξ η : H) :
    stinespringVector φ (ξ + η) = stinespringVector φ ξ + stinespringVector φ η := by
  apply ext_inner_left ℂ
  intro ω
  induction ω using Completion.induction_on with
  | hp => apply isClosed_eq <;> fun_prop
  | ih x =>
    simp only [inner_add_right, stinespringVector_pairing, map_add, mul_add,
      Finsupp.sum, Finset.sum_add_distrib]

lemma stinespringVector_smul (φ : CompletelyPositiveMap M (H →L[ℂ] H)) (z : ℂ) (ξ : H) :
    stinespringVector φ (z • ξ) = z • stinespringVector φ ξ := by
  apply ext_inner_left ℂ
  intro ω
  induction ω using Completion.induction_on with
  | hp => apply isClosed_eq <;> fun_prop
  | ih x =>
    simp only [inner_smul_right, stinespringVector_pairing, map_smul,
      Finsupp.sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    ring

lemma stinespringVector_norm_sq (φ : CompletelyPositiveMap M (H →L[ℂ] H)) (ξ : H) :
    ‖stinespringVector φ ξ‖ ^ 2 = (inner ℂ ξ (φ 1 ξ)).re := by
  classical
  rw [norm_sq_eq_re_inner (𝕜 := ℂ)]
  change (inner ℂ ((stinespringPreVector φ ξ) : StinespringSpace φ) (stinespringVector φ ξ)).re = _
  rw [stinespringVector_pairing]
  simp [stinespringPreVector]

lemma stinespringVector_bound (φ : CompletelyPositiveMap M (H →L[ℂ] H)) (ξ : H) :
    ‖stinespringVector φ ξ‖ ≤ Real.sqrt ‖φ 1‖ * ‖ξ‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow, Real.sq_sqrt (norm_nonneg _), stinespringVector_norm_sq]
  calc
    _ ≤ ‖inner ℂ ξ (φ 1 ξ)‖ := Complex.re_le_norm _
    _ ≤ ‖ξ‖ * ‖φ 1 ξ‖ := norm_inner_le_norm _ _
    _ ≤ ‖ξ‖ * (‖φ 1‖ * ‖ξ‖) :=
      mul_le_mul_of_nonneg_left ((φ 1).le_opNorm ξ) (norm_nonneg _)
    _ = _ := by ring

/-- The bounded map sending a vector to its unit-labelled kernel vector. -/
def stinespringEmbedding (φ : CompletelyPositiveMap M (H →L[ℂ] H)) :
    H →L[ℂ] StinespringSpace φ :=
  LinearMap.mkContinuous
    { toFun := stinespringVector φ
      map_add' := stinespringVector_add φ
      map_smul' := stinespringVector_smul φ }
    (Real.sqrt ‖φ 1‖) (stinespringVector_bound φ)

@[simp] lemma stinespringEmbedding_apply (φ : CompletelyPositiveMap M (H →L[ℂ] H)) (ξ : H) :
    stinespringEmbedding φ ξ = stinespringVector φ ξ := rfl

end BoundedHochschild.KadisonRingrose

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_PaulsenExtension
attribute [-instance] _root_.OAI.UltrapowerBridge.instStarTracialQuotient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Extend the two-by-two operator-system map into operators on the doubled
Hilbert space, using the proved positive extension theorem. -/

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace BoundedHochschild.KadisonRingrose

open HochschildMatrixDilation

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def paulsenOperatorMap (f : A →ₗ[ℂ] ℂ) (T : A →ₗ[ℂ] (H →L[ℂ] H)) :
    paulsenSystem A →ₗ[ℂ] (HilbertDouble H →L[ℂ] HilbertDouble H) :=
  (doubleMatrixHom (H := H) : Mat (H →L[ℂ] H) →ₗ[ℂ]
    (HilbertDouble H →L[ℂ] HilbertDouble H)).comp (paulsenSystemMap f T)

end BoundedHochschild.KadisonRingrose

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_TraceTopology
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Operator-norm bounded trace-norm limits remain in the same ball of the algebra, without requiring a cyclic trace vector. -/
section
open Filter
open scoped Topology
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

theorem bounded_trace_limit (a : ℕ → M.toStarSubalgebra) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ n, ‖a n‖ ≤ C) (ξ : H)
    (hξ : Tendsto (fun n => (a n : H →L[ℂ] H) τ.vector) atTop (𝓝 ξ)) :
    ∃ b : M.toStarSubalgebra, ‖b‖ ≤ C ∧ (b : H →L[ℂ] H) τ.vector = ξ := by
  let ω : Ultrafilter ℕ := Ultrafilter.of atTop
  obtain ⟨T, hT, ht⟩ := exists_weak_operator_ultralimit ω
    (fun n => (a n : H →L[ℂ] H)) C hC ha
  refine ⟨⟨T, weak_operator_limit_mem M a T ht⟩, hT, ?_⟩
  apply ext_inner_left ℂ
  intro y
  exact tendsto_nhds_unique (ht τ.vector y)
    ((continuous_const.inner continuous_id).continuousAt.tendsto.comp
      (hξ.mono_left (Ultrafilter.of_le atTop)))

/-! The actual closed convex unitary orbit in the coordinate trace Hilbert
space, with bounded representatives and conjugation invariance. -/

def baseVector : M.toStarSubalgebra →ₗ[ℂ] H where
  toFun a := (a : H →L[ℂ] H) τ.vector
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end

/-! The least-norm point of the actual orbit hull is represented in M and
fixed by every conjugating unitary; its trace and distance bounds are retained. -/
open scoped Topology
open UltrapowerBridge

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_TracialInclusion
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Generator.Tracial

/-! The restricted faithful trace and the actual P^omega -> M^omega
inclusion. All constructions are on the bounded-sequence quotient. -/
noncomputable section
open Filter
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M P : VonNeumannAlgebra H} (τ : TracialRepresentation M) (hPM : P ≤ M)

/-- P, as a star subalgebra of M. Its completeness is derived, not assumed. -/
def insideAlgebra : StarSubalgebra ℂ M.toStarSubalgebra :=
  P.toStarSubalgebra.comap M.toStarSubalgebra.subtype

end

end Generator.Tracial

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_CornerTrace
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedAlgebraComplexSubtypeMemNonUnitalStarSubalgebra _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Trace estimates in the actual ambient algebra. The corner scalar uses
its normalized trace. These estimates do not assume or assert the existence
of a local-quantizing projection. -/
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

theorem cornerTrace_add (x y : M.toStarSubalgebra) :
    τ.trace (x+y) = τ.trace x + τ.trace y := inner_add_right _ _ _

theorem cornerTrace_smul (c : ℂ) (x : M.toStarSubalgebra) :
    τ.trace (c • x) = c * τ.trace x := inner_smul_right _ _ _

end

/-! Actual noncommutative L1 on the coordinate algebra: trace(sqrt(x* x)).
The supported L2-to-L1 estimate retains the square root of the support trace.
No quantizing projection or conditional expectation theorem is assumed. -/
section
open scoped CStarAlgebra
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
local instance instCStarAlgebraSubtypeContinuousLinearMapComplexIdMemStarSubalgebra_solutions : CStarAlgebra M.toStarSubalgebra := {}
local instance instLESubtypeContinuousLinearMapComplexIdMemStarSubalgebra_solutions : LE M.toStarSubalgebra := (CStarAlgebra.spectralOrder _).toLE

end

/-! A finite compression-energy estimate yields a nonzero corner projection with simultaneous L1 control. -/

/-! The scalar trace estimate for a term with two supported patch letters.
It reduces to the actual compressed middle coefficient and keeps trace(q),
not trace(p), as the scale of the error. -/
open UltrapowerBridge

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_Pinching
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Finite pinching in the actual ambient algebra. The squared L2 energy
is a sum of the energies of the mutually orthogonal compression blocks.
These identities do not postulate a local-quantizing partition. -/
section
open scoped BigOperators
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

/-! Actual compression energies and the energy lost by finite pinching.
No existence statement about small-energy partitions is assumed here. -/

theorem norm₂_sq_trace (x : M.toStarSubalgebra) :
    τ.norm₂ x ^ 2 = (τ.trace (star x*x)).re := by
  rw [τ.trace_star_mul, ← Complex.ofReal_pow, Complex.ofReal_re]

theorem baseVector_inner_trace (x y : M.toStarSubalgebra) :
    inner ℂ (baseVector τ x) (baseVector τ y) = τ.trace (star x*y) := by
  change inner ℂ ((x : H →L[ℂ] H) τ.vector) ((y : H →L[ℂ] H) τ.vector) = _
  rw [← ContinuousLinearMap.adjoint_inner_right]
  rfl

end

/-! Actual finite refinement of a corner partition by partitions of its blocks.
The dependent family of block sizes is flattened without changing any piece.
No small-energy partition is an input to these constructions. -/

/-! Centered energy and the block scalar term that refinement preserves.
A blockwise descent applies to centered compressions, not to their full energy. -/

/-! Energy of compatible block refinements, including the scalar term.
The scalar term is necessary even when the original operator has trace zero. -/
open scoped BigOperators
open UltrapowerBridge

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_HilbertLimits
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.PopaCorner.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator

/-! Multiplication and adjoint limits in L2, with the necessary uniform
operator norm bounds stated explicitly. -/
namespace Tracial
open Filter
open scoped Topology
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

theorem tendsto_vector_iff_norm₂ {I : Type*} (l : Filter I)
    (a : I → M.toStarSubalgebra) (b : M.toStarSubalgebra) :
    Tendsto (fun i => (a i : H →L[ℂ] H) τ.vector) l (𝓝 ((b : H →L[ℂ] H) τ.vector)) ↔
    Tendsto (fun i => τ.norm₂ (a i-b)) l (𝓝 0) := by
  simpa only [dist_eq_norm,TracialRepresentation.norm₂_sub] using
    (tendsto_iff_dist_tendsto_zero (f := fun i => (a i : H →L[ℂ] H) τ.vector)
      (a := (b : H →L[ℂ] H) τ.vector))

theorem norm₂_limit_unique {I : Type*} {l : Filter I} [l.NeBot]
    (a : I → M.toStarSubalgebra) {b c : M.toStarSubalgebra}
    (hb : Tendsto (fun i => τ.norm₂ (a i-b)) l (𝓝 0))
    (hc : Tendsto (fun i => τ.norm₂ (a i-c)) l (𝓝 0)) : b=c := by
  have he := tendsto_nhds_unique ((tendsto_vector_iff_norm₂ τ l a b).mpr hb)
    ((tendsto_vector_iff_norm₂ τ l a c).mpr hc)
  apply sub_eq_zero.mp
  apply τ.separating
  change (b : H →L[ℂ] H) τ.vector-(c : H →L[ℂ] H) τ.vector=0
  exact sub_eq_zero.mpr he

theorem norm₂_limit_star {I : Type*} {l : Filter I} (a : I → M.toStarSubalgebra)
    (b : M.toStarSubalgebra) (h : Tendsto (fun i => τ.norm₂ (a i-b)) l (𝓝 0)) :
    Tendsto (fun i => τ.norm₂ (star (a i)-star b)) l (𝓝 0) := by
  simpa only [← star_sub,τ.norm₂_star] using h

end Tracial

/-! A separating vector for a concrete von Neumann algebra is cyclic for its
commutant. The original representation need not be cyclic for the algebra. -/

/-! Restrict the faithful trace representation to the closure of M times its
trace vector. This constructs a faithful, isometric, cyclic representation on
an actual Hilbert subspace. No Banach predual or WOT-closed image is asserted. -/

/-! A real linear functional continuous for bounded trace-two-norm sequences
is WOT continuous on the unit ball. Closed convex slices of the trace-vector
ball supply the conversion; no identification of the two topologies is assumed. -/
open Filter
open scoped Topology

/-! On a uniformly operator-norm bounded family in a faithfully vector-traced
von Neumann algebra, L2 convergence implies strong and adjoint-strong convergence
in the original Hilbert space. -/
open Filter
open scoped Topology

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_UnitaryMetric
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedAlgebraComplexSubtypeMemNonUnitalStarSubalgebra _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Bounded self-adjoint least-distance elements in a von Neumann subalgebra. -/
section
open Filter
open scoped Topology
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H}

def selfAdjointTraceBall (τ : TracialRepresentation N) (R : ℝ) : Set H :=
  {ξ | ∃ a : N.toStarSubalgebra, IsSelfAdjoint a ∧ ‖a‖ ≤ R ∧ baseVector τ a=ξ}

theorem selfAdjointTraceBall_closed (τ : TracialRepresentation N) (R : ℝ) :
    IsClosed (selfAdjointTraceBall τ R) := by
  apply IsSeqClosed.isClosed
  intro ξ z hz hlim
  choose a ha hR he using hz
  have hlimA : Tendsto (fun n => baseVector τ (a n)) atTop (𝓝 z) := by
    convert hlim using 1
    all_goals try with_reducible_and_instances rfl
    exact funext he
  obtain ⟨b,hb,hbz⟩ := bounded_trace_limit τ a R ((norm_nonneg _).trans (hR 0)) hR z
    hlimA
  have hvec : Tendsto (fun n => (a n : H →L[ℂ] H) τ.vector) atTop
      (𝓝 ((b : H →L[ℂ] H) τ.vector)) := by rw [hbz]; exact hlimA
  have h := (tendsto_vector_iff_norm₂ τ atTop a b).mp hvec
  have hs := norm₂_limit_star τ a b h
  simp only [(ha _).star_eq] at hs
  have hsb : star b=b := norm₂_limit_unique τ a hs h
  exact ⟨b,hsb,hb,hbz⟩

theorem selfAdjointTraceBall_convex (τ : TracialRepresentation N) (R : ℝ) :
    Convex ℝ (selfAdjointTraceBall τ R) := by
  intro x hx y hy s t hs ht hst
  obtain ⟨a,ha,hRa,rfl⟩ := hx
  obtain ⟨b,hb,hRb,rfl⟩ := hy
  refine ⟨s • a+t • b,((IsSelfAdjoint.all s).smul ha).add
    ((IsSelfAdjoint.all t).smul hb),?_,rfl⟩
  calc ‖s • a+t • b‖ ≤ ‖s • a‖+‖t • b‖ := norm_add_le _ _
       _ = s*‖a‖+t*‖b‖ := by rw [norm_smul,norm_smul,Real.norm_of_nonneg hs,Real.norm_of_nonneg ht]
       _ ≤ s*R+t*R := add_le_add (mul_le_mul_of_nonneg_left hRa hs)
          (mul_le_mul_of_nonneg_left hRb ht)
       _ = R := by rw [← add_mul,hst,one_mul]

theorem exists_selfAdjoint_ball_variational (τ : TracialRepresentation M) (hNM : N ≤ M)
    (x : M.toStarSubalgebra) (R : ℝ) (hR : 0 ≤ R) :
    ∃ c : N.toStarSubalgebra, IsSelfAdjoint c ∧ ‖c‖ ≤ R ∧
      (∀ a : N.toStarSubalgebra, IsSelfAdjoint a → ‖a‖ ≤ R →
        τ.norm₂ (x-coordinateInclusion hNM c) ≤ τ.norm₂ (x-coordinateInclusion hNM a)) ∧
      ∀ a : N.toStarSubalgebra, IsSelfAdjoint a → ‖a‖ ≤ R →
        (inner ℂ (baseVector τ (x-coordinateInclusion hNM c))
          (baseVector τ (coordinateInclusion hNM (a-c)))).re ≤ 0 := by
  let τN := restrictedTrace τ hNM
  let K := selfAdjointTraceBall τN R
  let : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
  obtain ⟨ξ,hξ,hmin⟩ := exists_norm_eq_iInf_of_complete_convex
    (show K.Nonempty from ⟨0,0,IsSelfAdjoint.zero _,by simpa using hR,rfl⟩)
    (selfAdjointTraceBall_closed τN R).isComplete (selfAdjointTraceBall_convex τN R)
    (baseVector τ x)
  obtain ⟨c,hc,hRc,rfl⟩ := hξ
  refine ⟨c,hc,hRc,?_,?_⟩
  · intro a ha hRa
    have h := ciInf_le (show BddBelow (Set.range (fun w : K => ‖baseVector τ x-w.val‖)) from
      ⟨0,by rintro _ ⟨w,rfl⟩; exact norm_nonneg _⟩)
      (⟨baseVector τN a,a,ha,hRa,rfl⟩ : K)
    rw [← hmin] at h
    exact h
  · intro a ha hRa
    have h := (norm_eq_iInf_iff_real_inner_le_zero (selfAdjointTraceBall_convex τN R)
      (show baseVector τN c ∈ K from ⟨c,hc,hRc,rfl⟩)).mp hmin
      (baseVector τN a) ⟨a,ha,hRa,rfl⟩
    exact h

end

/-! Countable determination of a relative commutant from actual L2
separability. Operator norm separability is not required. -/

/-! The unitary metric induced by a faithful trace vector, distinguishing the trace two-norm topology from the operator norm topology. -/
open Filter
open scoped Topology
open UltrapowerBridge

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_SpectralTruncation
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedAlgebraComplexSubtypeMemNonUnitalStarSubalgebra _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instPartialOrderSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Positivity of the tracial pairing does not require the two positive
operators to commute. These estimates will control spectral truncation. -/
section
open scoped CStarAlgebra
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)
local instance tracePairingCStar : CStarAlgebra M.toStarSubalgebra := {}
local instance tracePairingPreorder_r992400_1 : Preorder M.toStarSubalgebra :=
  (CStarAlgebra.spectralOrder _).toPreorder
local instance tracePairingLE : LE M.toStarSubalgebra := (CStarAlgebra.spectralOrder _).toLE

end

/-! Upper spectral truncation of a self-adjoint operator. The truncation
remains in the original operator ball and has a positive discarded part. -/
section
open scoped CStarAlgebra
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
local instance truncationCStar : CStarAlgebra M.toStarSubalgebra := {}

local instance truncationOrder_r992400_1 : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance truncationLE_r992400_1 : LE M.toStarSubalgebra := (CStarAlgebra.spectralOrder _).toLE
local instance truncationStarOrder_r992400_1 : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _
def upperTruncate (a : M.toStarSubalgebra) (C : ℝ) : M.toStarSubalgebra :=
  a-(a-algebraMap ℝ M.toStarSubalgebra C)⁺

end

/-! Spectral truncation forces a self-adjoint least-distance point in a
subalgebra ball to have norm at most the norm of the ambient test operator. -/
section
open scoped CStarAlgebra
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H}
local instance interiorCStar (A : VonNeumannAlgebra H) : CStarAlgebra A.toStarSubalgebra := {}
local instance interiorOrder (A : VonNeumannAlgebra H) : PartialOrder A.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance interiorPreorder (A : VonNeumannAlgebra H) : Preorder A.toStarSubalgebra :=
  (CStarAlgebra.spectralOrder _).toPreorder
local instance interiorLE (A : VonNeumannAlgebra H) : LE A.toStarSubalgebra :=
  (CStarAlgebra.spectralOrder _).toLE
local instance interiorStarOrder (A : VonNeumannAlgebra H) : StarOrderedRing A.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _

theorem included_selfAdjoint (hNM : N ≤ M) (a : N.toStarSubalgebra) (ha : IsSelfAdjoint a) :
    IsSelfAdjoint (coordinateInclusion hNM a) := by
  change star (coordinateInclusion hNM a)=coordinateInclusion hNM a
  rw [← map_star,ha.star_eq]

end

/-! Two-sided spectral clipping and trace-norm control. The auxiliary trace
is explicit; the trace-free construction supplies it on its actual closure. -/
open scoped CStarAlgebra
open UltrapowerBridge

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_Subfactors
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! The actual von Neumann algebra of operators in N commuting with a finite
projection partition. Its double-commutant identity and completeness are
proved, so spectral approximation can be performed inside this algebra. -/

/-! Irreducibility passes to actual corners. Spectral approximation reduces
self-adjoint corner commutants to their projections; no corner-factor or
normalized-trace existence statement is assumed. -/

/-! The relative commutant of a finite block algebra consists of scalars on
each block. This statement is proved from coordinate irreducibility. -/

/-! Orthogonality to the prescribed subalgebra is stronger than global
centering. It is preserved by compressions and conjugations from that
subalgebra and removes every block scalar term exactly. -/
section
open scoped BigOperators
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

def TraceOrthogonal (P : StarSubalgebra ℂ M.toStarSubalgebra) (x : M.toStarSubalgebra) : Prop :=
  ∀ a : P, τ.trace ((a : M.toStarSubalgebra)*x)=0

/-! Quantitative control of the scalar energy that survives compatible
refinement. An orthogonal residual changes none of the block traces. -/

end

/-! A corner whose only projections are zero and its unit is scalar.
The proof constructs spectral approximations; minimality is not a scalar-corner axiom. -/

/-! Diffuseness descends to an irreducible von Neumann subalgebra of a
diffuse finite tracial algebra. Finiteness follows from the actual faithful trace. -/
open UltrapowerBridge

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_Expectations
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.PopaCorner.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! The orthogonal subalgebra representative of a self-adjoint ambient
operator is constructed, with its operator norm bound. -/

/-! A bounded trace-preserving subalgebra projection from self-adjoint least-distance points. Tracial orthogonality gives uniqueness and the bimodule identities. -/
section
open scoped ComplexStarModule
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

namespace TraceOrthogonal
variable {P : StarSubalgebra ℂ M.toStarSubalgebra} {x y : M.toStarSubalgebra}
theorem add (hx : TraceOrthogonal τ P x) (hy : TraceOrthogonal τ P y) :
    TraceOrthogonal τ P (x+y) := by
  intro a
  rw [mul_add,cornerTrace_add,hx a,hy a,add_zero]
theorem smul (hx : TraceOrthogonal τ P x) (z : ℂ) : TraceOrthogonal τ P (z • x) := by
  intro a
  rw [mul_smul_comm,cornerTrace_smul,hx a,mul_zero]
end TraceOrthogonal

end

/-! The constructed expectation preserves adjoints, is a bimodule map,
and is the orthogonal projection for the trace norm. -/

/-! Positivity of the constructed expectation. The negative spectral part
is an actual subalgebra test operator; tracial orthogonality eliminates it. -/

/-! The constructed expectation satisfies the Schwarz inequality and is
contractive in operator norm. -/

/-! Actual nested subalgebras satisfy the expectation tower identity.
The resulting energy identity is the decreasing-subfactor step of A.1.2. -/

/-! Conditional expectations onto a decreasing sequence of actual
subalgebras converge in L2. This supplies the limiting argument in A.1.2;
it does not construct that source's decreasing subfactors. -/
open Filter
open scoped Topology BigOperators
open UltrapowerBridge

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_MatrixAlgebras
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator

/-! Equal-trace finite partitions extend to actual matrix units in the same
factor. The theorem also retains a prescribed corner as the sum of diagonals. -/
open scoped BigOperators

/-! The matrix-unit image in the original represented algebra, with its
finite dimensionality and weak-operator closedness proved. -/
open scoped BigOperators
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace MatrixUnitSystem
variable (E : Generator.MatrixUnitSystem ι M.toStarSubalgebra)

def concreteHom : Matrix ι ι ℂ →⋆ₐ[ℂ] (H →L[ℂ] H) :=
  M.toStarSubalgebra.subtype.comp E.hom

def concreteAlgebra : StarSubalgebra ℂ (H →L[ℂ] H) := E.concreteHom.range

theorem concreteAlgebra_le : E.concreteAlgebra ≤ M.toStarSubalgebra := by
  rintro x ⟨a,rfl⟩
  exact (E.hom a).property

theorem mem_concreteAlgebra (x : M.toStarSubalgebra) :
    x.val ∈ E.concreteAlgebra ↔ x ∈ E.algebra := by
  constructor
  · rintro ⟨a,ha⟩
    exact ⟨a,Subtype.ext ha⟩
  · rintro ⟨a,ha⟩
    exact ⟨a,congrArg Subtype.val ha⟩

end MatrixUnitSystem

end

/-! The actual relative commutant in M is a diffuse scalar-center von
Neumann algebra, with the restricted faithful trace available from M. -/
namespace MatrixUnitSystem

section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (E : MatrixUnitSystem ι M.toStarSubalgebra)

def relativeVonNeumann : VonNeumannAlgebra H where
  toStarSubalgebra := E.relativeStar
  centralizer_centralizer' := E.relativeStar_bicommutant

theorem relativeVonNeumann_le : E.relativeVonNeumann ≤ M := by
  intro x hx
  exact ((E.relativeStar_mem x).mp hx).1

end

/-! Passing an irreducible inclusion through a common finite matrix algebra
preserves irreducibility of the actual relative commutants. -/

open UltrapowerBridge Tracial

end MatrixUnitSystem

/-! Explicit Bell projections in two equal finite matrix factors. -/
open scoped BigOperators

/-! Exact normalized traces of constructed matrix algebras and all their
commuting product refinements. -/
open scoped BigOperators

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_MatrixRefinement
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator

/-! A normal element of a diffuse finite factor has L2 approximations in
constructed full dyadic matrix algebras. No prescribed MASA is needed. -/

/-! Concrete commutants reverse matrix-algebra inclusion. Expectations are
compatible with restriction to an intermediate represented subalgebra. -/
section
namespace MatrixUnitSystem
open UltrapowerBridge Tracial
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem relative_antitone (E : MatrixUnitSystem ι M.toStarSubalgebra)
    (F : MatrixUnitSystem κ M.toStarSubalgebra) (h : E.algebra ≤ F.algebra) :
    F.relativeVonNeumann ≤ E.relativeVonNeumann := by
  intro x hx
  have hx' := (F.relativeStar_mem x).mp hx
  apply (E.relativeStar_mem x).mpr
  refine ⟨hx'.1,?_⟩
  let y : M.toStarSubalgebra := ⟨x,hx'.1⟩
  have hF : ∀ i j,Commute (F.entry i j) y := fun i j => Subtype.ext (hx'.2 i j)
  intro i j
  exact congrArg Subtype.val (((F.commute_algebra_iff y).mpr hF) _ (h (E.entry_mem i j))).eq

end MatrixUnitSystem

end

/-! Quantitative energy descent retaining a prescribed finite matrix algebra
in an irreducible inclusion. All expectations and refinements are constructed. -/

/-! Reindex full matrix units without changing their actual algebra or
relative commutant. This keeps iterated constructions indexed by Fin n. -/
namespace MatrixUnitSystem
open scoped BigOperators
variable {ι κ A : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]

open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H}

theorem map_algebra_mono (E : MatrixUnitSystem ι N.toStarSubalgebra)
    (F : MatrixUnitSystem κ N.toStarSubalgebra) (h : E.algebra ≤ F.algebra)
    (f : N.toStarSubalgebra →⋆ₐ[ℂ] M.toStarSubalgebra) :
    (E.map f).algebra ≤ (F.map f).algebra := by
  apply ((E.map f).algebra_le_iff _).mpr
  intro i j
  obtain ⟨a,ha⟩ := (F.mem_algebra (E.entry i j)).mp (h (E.entry_mem i j))
  change f (E.entry i j) ∈ (F.map f).algebra
  rw [← ha]
  simp only [map_sum,map_smul]
  exact (F.map f).algebra.sum_mem fun k _ =>
    (F.map f).algebra.sum_mem fun l _ => (F.map f).algebra.smul_mem ((F.map f).entry_mem k l) _

end MatrixUnitSystem

/-! An actual full matrix algebra of any positive finite size can be
constructed in the relative commutant. No commuting matrix units are assumed. -/

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_MatrixSequence
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator

/-! Finite matrix stages and a quantified refinement operation, including
zero expectation. Reindexing changes no represented algebra. -/
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace FiniteMatrixStage
open Tracial
variable {N M : VonNeumannAlgebra H}

def commutant (E : FiniteMatrixStage N) (hNM : N ≤ M) : VonNeumannAlgebra H :=
  (E.units.map (coordinateInclusion hNM)).relativeVonNeumann

theorem commutant_le (E : FiniteMatrixStage N) (hNM : N ≤ M) : E.commutant hNM ≤ M :=
  (E.units.map (coordinateInclusion hNM)).relativeVonNeumann_le

theorem commutant_antitone (E F : FiniteMatrixStage N) (hNM : N ≤ M)
    (hEF : E.units.algebra ≤ F.units.algebra) : F.commutant hNM ≤ E.commutant hNM :=
  (E.units.map (coordinateInclusion hNM)).relative_antitone _
    (E.units.map_algebra_mono F.units hEF (coordinateInclusion hNM))

end FiniteMatrixStage

end

/-! Iterated compatible full matrix refinements attain every positive
finite-family commutant expectation budget. The reduction factor is proved. -/

/-! L2 separability supplies a countable centered dense family. The constructed
matrix sequence has scalar common relative commutant in the ambient algebra. -/

/-! The actual weakly closed star algebra generated by the increasing finite
matrix stages. Its ambient relative commutant is scalar. This does not yet
package a diffuse II1 subfactor or derive the representation hypotheses. -/
section
namespace FiniteMatrixStage
open UltrapowerBridge Tracial
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H}

theorem concrete_stage_monotone (A : ℕ → FiniteMatrixStage N)
    (hA : Monotone (fun n => (A n).units.algebra)) :
    Monotone (fun n => (A n).units.concreteAlgebra) := by
  intro i j hij x hx
  let a : N.toStarSubalgebra := ⟨x,(A i).units.concreteAlgebra_le hx⟩
  exact ((A j).units.mem_concreteAlgebra a).mpr
    (hA hij (((A i).units.mem_concreteAlgebra a).mp hx))

end FiniteMatrixStage

end

/-! The constructed matrix-generated weak closure is an actual II1 factor.
Its bundled von Neumann algebra and faithful trace use the same operators. -/

/-! Finite matrix stages strongly approximate the actual weakly generated
algebra. The approximants here have no operator norm bound. -/

end Generator

end

end OAI
end


