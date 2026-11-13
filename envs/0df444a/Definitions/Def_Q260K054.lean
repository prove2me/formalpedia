-- Prove2me | Definitions.Def_Q260K054
-- name    : Q260K054
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-13T04:43:24.712072+00:00
-- url     : https://prove2.me/theorems/53f2417a-b253-495c-97d4-9c90296de9f6
-- title:
--   Definitions bundle Q260K054 of the split of OpenAI, Universal strong Kadison–Kastler stability (result family 289)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KadisonKastler.universal_strong_stability`, carved from OpenAI's openai/math development (OpenAI, *Universal strong Kadison–Kastler stability (result family 289)*, OpenAI Math Release, September 23, 2026, result family 289, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 33 declarations of OpenAI's Lean: 4 definitions and 29 theorems. The definitions and types are `OAI.Generator.Tracial.EquivalentPartition.entry`, `OAI.Generator.Tracial.EquivalentPartition.matrixUnits`, `OAI.Generator.Tracial.EquivalentPartition.matrixVectorFunctional`, `OAI.Generator.Tracial.EquivalentPartition.stateCoefficient`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`FactorGeneration_Dimension`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/FactorGeneration/Dimension.lean), [`FactorGeneration_DyadicComparison`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/FactorGeneration/DyadicComparison.lean), [`FactorGeneration_LocalizedStates`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/FactorGeneration/LocalizedStates.lean), [`FactorGeneration_SpectralDimension`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/FactorGeneration/SpectralDimension.lean).
--
--   **Imports.** It imports the bundle `Q260K053` of this split.
--
--   **Imported by** (directly, in this split): the bundle `Q260K009`; the statements `OAI_KadisonKastler_exists_normalizer_of_smoothed_infDist`, `OAI_KadisonKastler_generated_matrix_spatial_union`, `OAI_KadisonKastler_projectionCentralSpace_scalar` and `OAI_KadisonKastler_spatialMatrix_union_weakUnitBallDense`; the proofs of `OAI_KadisonKastler_exists_normalizer_of_smoothed_infDist`, `OAI_KadisonKastler_expectedMatrixSubfactorModel_of_local_refinement`, `OAI_KadisonKastler_generated_matrix_spatial_union`, `OAI_KadisonKastler_projectionCentralSpace_scalar`, `OAI_KadisonKastler_spatialMatrix_union_weakUnitBallDense`, `OAI_KadisonKastler_uniform_common_action_of_frequency_defects` and `OAI_KadisonKastler_vector_bicentralizer_scalar_of_modular_coisometries`.
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
import Definitions.Def_Q260K053

section
-- module Solutions.OAIQ075_KS.FactorGeneration_DyadicComparison
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.MatrixUnitSystem.concrete_finiteDimensional _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator

/-! Halving every projection in a diffuse factor without a trace.
Maximality leaves no residual corner: a diffuse residual splits into two
nonzero orthogonal projections, and a polar link gives a strict extension. -/

/-! Finite partitions with explicit equivalence witnesses and compatible binary
refinement. The common initial projection is halved once and its two pieces
are transported to every old piece, so all new pieces remain equivalent. -/
section
open scoped BigOperators

/-! Coherent dyadic equivalent partitions and matrix units, constructed from
scalar center and diffuseness without a trace. DyadicIndex is reused as a
finite binary index type; no tracial partition construction is used. -/
open scoped BigOperators
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace Tracial
variable {M : VonNeumannAlgebra H}
namespace EquivalentPartition
variable {p : AlgebraProjection M} {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The matrix entries associated to the explicit common-source legs. -/
def entry (E : EquivalentPartition p ι) (i j : ι) : M.toStarSubalgebra :=
  (E.leg i).val*star (E.leg j).val

theorem entry_star (E : EquivalentPartition p ι) (i j : ι) :
    star (E.entry i j)=E.entry j i := by simp only [entry,star_mul,star_star]

theorem entry_mul [DecidableEq ι] (E : EquivalentPartition p ι) (i j k l : ι) :
    E.entry i j*E.entry k l=if j=k then E.entry i l else 0 := by
  change ((E.leg i).val*star (E.leg j).val)*((E.leg k).val*star (E.leg l).val)=_
  have hr : ((E.leg i).val*star (E.leg j).val)*((E.leg k).val*star (E.leg l).val)=
      (E.leg i).val*(star (E.leg j).val*(E.leg k).val)*star (E.leg l).val := by
    simp only [mul_assoc]
  rw [hr]
  by_cases h : j=k
  · subst k
    rw [ite_eq_left rfl,(E.leg j).initial,E.initial,← E.initial i,(E.leg i).mul_support]
    rfl
  · rw [ite_eq_right h,E.cross j k h,mul_zero,zero_mul]

/-- A partition of the identity yields a unital full matrix-unit system. -/
def matrixUnits [DecidableEq ι] (E : EquivalentPartition p ι) (hp : p.val=1) :
    MatrixUnitSystem ι M.toStarSubalgebra where
  entry := E.entry
  star_entry := E.entry_star
  mul_entry := E.entry_mul
  total := E.total.trans hp

end EquivalentPartition

end Tracial

end

/-! Actual sums of countable orthogonal partial isometries, including least
initial/final support identities. No trace or countable-cofinality premise. -/

/-! Actual finite sums of orthogonal partial isometries and finite subsets of
equivalent partitions. The finite subset is arbitrary, without an index order. -/
open scoped BigOperators

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_Dimension
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing
attribute [-simp] _root_.OAI.Generator.Tracial.CornerPartition.single_pinch _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator

/-! Archimedean comparison for the constructed dyadic reference projections.
Orthogonal sibling corners supply copies for the finite-algebra shift argument. -/

/-! Finite rounding by actual subset projections. A maximal fitting subset
leaves a remainder smaller in comparison than any unused equivalent piece. -/
namespace Tracial

section
open scoped BigOperators
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

/-! The dyadic lower cut on projections below p and its normalized faithful monotone supremum, capped at one. -/

variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)

theorem traceFreeDyadicSup_nonneg (p q : AlgebraProjection M) :
    0 ≤ traceFreeDyadicSup hfactor hdiff p q :=
  le_csSup (traceFreeDyadicCut_bddAbove hfactor hdiff p q)
    (traceFreeDyadicCut_zero_mem hfactor hdiff p q)

theorem traceFreeDyadicSup_equivalent (p : AlgebraProjection M) {q r : AlgebraProjection M}
    (h : q.Equivalent r) :
    traceFreeDyadicSup hfactor hdiff p q=traceFreeDyadicSup hfactor hdiff p r :=
  le_antisymm (traceFreeDyadicSup_mono hfactor hdiff p h.subequivalent)
    (traceFreeDyadicSup_mono hfactor hdiff p (AlgebraProjection.equivalent_symm h).subequivalent)

theorem traceFreeDyadicSup_zero (p q : AlgebraProjection M) (hp : p.val≠0) (hq : q.val=0) :
    traceFreeDyadicSup hfactor hdiff p q=0 := by
  apply le_antisymm ?_ (traceFreeDyadicSup_nonneg hfactor hdiff p q)
  apply csSup_le ⟨0,traceFreeDyadicCut_zero_mem hfactor hdiff p q⟩
  rintro x ⟨n,s,⟨v,hv,ht⟩,rfl⟩
  have htz : v.target.val=0 := by
    change q.val*v.target.val=v.target.val at ht
    rw [hq,zero_mul] at ht
    exact ht.symm
  have hvz : v.val=0 := by
    have h := v.target_mul
    rw [htz,zero_mul] at h
    exact h.symm
  have hsz : ((traceFreeDyadicPartition hfactor hdiff p n).subset s).val=0 := by
    rw [← hv,← v.initial,hvz,star_zero,zero_mul]
  have hs : s ⊆ ∅ :=
    ((traceFreeDyadicPartition hfactor hdiff p n).subset_le_subset_iff hp s ∅).mp (by
      change ((traceFreeDyadicPartition hfactor hdiff p n).subset ∅).val*
        ((traceFreeDyadicPartition hfactor hdiff p n).subset s).val=_
      rw [hsz,mul_zero])
  have he : s=∅ := Finset.eq_empty_iff_forall_notMem.mpr (fun i hi => Finset.notMem_empty i (hs hi))
  simp only [he,dyadicWeight,Finset.card_empty,Nat.cast_zero,zero_div,le_refl]

end

/-! Common refinements compare arbitrary dyadic levels. The supremum takes
the exact dyadic value on every reference subset projection, and finite
rounding bounds every projection with an explicit error at each level. -/

/-! Orthogonal lower approximants fit disjoint collections of the reference
pieces. Equivalent complements and finite cancellation enforce the capacity. -/

/-! Orthogonal additivity of the constructed dyadic dimension. Numerical
rounding errors tend to zero; every lower and upper bound uses actual
partial-isometry witnesses in the original finite diffuse factor. -/
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

include hfinite in
theorem traceFreeDyadicSup_upper_add
    (p q r : AlgebraProjection M) (hp : p.val≠0) (ho : q.val*r.val=0)
    (n : ℕ) (s t : Finset (DyadicIndex n))
    (hs : q.Subequivalent ((traceFreeDyadicPartition hfactor hdiff p n).subset s))
    (ht : r.Subequivalent ((traceFreeDyadicPartition hfactor hdiff p n).subset t)) :
    traceFreeDyadicSup hfactor hdiff p (orthogonalSum q r ho) ≤
      dyadicWeight n s+dyadicWeight n t := by
  by_cases hc : s.card+t.card ≤ Fintype.card (DyadicIndex n)
  · obtain ⟨u,huc,hu⟩ := (traceFreeDyadicPartition hfactor hdiff p n).orthogonal_upper_union
      q r ho s t hs ht hc
    have h := traceFreeDyadicSup_mono hfactor hdiff p hu
    rw [traceFreeDyadicSup_subset hfactor hdiff hfinite p hp] at h
    simpa only [dyadicWeight,huc,Nat.cast_add,add_div] using h
  · apply le_trans (traceFreeDyadicSup_le_one hfactor hdiff p _)
    have hn : 2^n ≤ s.card+t.card := by rw [card_dyadicIndex] at hc; omega
    change 1 ≤ (s.card : ℝ)/2^n+(t.card : ℝ)/2^n
    rw [← add_div]
    apply (le_div_iff₀ (pow_pos (by norm_num : (0 : ℝ)<2) n)).mpr
    simp only [one_mul]
    exact_mod_cast hn

include hfinite in
/-- The dyadic supremum is additive on actual orthogonal projections below p. -/
theorem traceFreeDyadicSup_orthogonal_add
    (p q r : AlgebraProjection M) (hp : p.val≠0) (hqp : q ≤ p) (hrp : r ≤ p)
    (ho : q.val*r.val=0) :
    traceFreeDyadicSup hfactor hdiff p (orthogonalSum q r ho)=
      traceFreeDyadicSup hfactor hdiff p q+traceFreeDyadicSup hfactor hdiff p r := by
  apply eq_of_all_dyadic_errors
  intro n
  obtain ⟨s,t,_,_,hs,ht,hql,hqu,hqe⟩ :=
    traceFreeDyadicSup_rounding hfactor hdiff hfinite p q hp hqp n
  obtain ⟨a,b,_,_,ha,hb,hrl,hru,hre⟩ :=
    traceFreeDyadicSup_rounding hfactor hdiff hfinite p r hp hrp n
  have hlo := traceFreeDyadicSup_lower_add hfactor hdiff hfinite p q r hp hqp hrp ho n s a hs ha
  have hhi := traceFreeDyadicSup_upper_add hfactor hdiff hfinite p q r hp ho n t b ht hb
  rw [show (2 : ℝ)/2^n=2*(1/2^n) by ring]
  apply abs_le.mpr
  constructor <;> linarith

end Tracial

/-! Classification of projection comparison by the constructed finite
dimension, and a wrapper for exactly the original IsII1Factor predicate.
No normality or trace-extension claim is made here. -/

/-! Bounds and concrete dyadic upper approximants for the constructed
projection dimension. These finite estimates do not assume continuity. -/
namespace Tracial
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

theorem traceFreeDimension_nonneg (q : AlgebraProjection M) :
    0 ≤ traceFreeDimension hfactor hdiff q :=
  traceFreeDyadicSup_nonneg hfactor hdiff _ q

theorem traceFreeDimension_le_one (q : AlgebraProjection M) :
    traceFreeDimension hfactor hdiff q ≤ 1 :=
  traceFreeDyadicSup_le_one hfactor hdiff _ q

end Tracial

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_SpectralDimension
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.functionalSubspaceWeakScalarTower _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing
attribute [-simp] _root_.OAI.Generator.Tracial.cyclicCoefficient_apply _root_.OAI.Generator.Tracial.cyclicPredualEvaluation_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Finite spectral weights of the constructed projection dimension obey an
operator-norm bound. No linear trace on noncommuting elements is assumed. -/
section
open scoped BigOperators
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

include hfinite in
theorem traceFreeDimension_finsetSum
    (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    {I : Type*} (q : I → AlgebraProjection M) (s : Finset I)
    (ho : ∀ i ∈ s, ∀ j ∈ s, i≠j → (q i).val*(q j).val=0) :
    traceFreeDimension hfactor hdiff (AlgebraProjection.finsetSum q s ho)=
      ∑ i ∈ s, traceFreeDimension hfactor hdiff (q i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have hz : (AlgebraProjection.finsetSum q ∅ ho).val=0 := by simp [AlgebraProjection.finsetSum]
    simpa only [Finset.sum_empty,traceFreeDimension] using traceFreeDyadicSup_zero hfactor hdiff
      ⟨1,IsStarProjection.one _⟩ _ hunit hz
  | @insert i s hi ih =>
    have hos : ∀ j ∈ s, ∀ k ∈ s, j≠k → (q j).val*(q k).val=0 :=
      fun j hj k hk => ho j (Finset.mem_insert_of_mem hj) k (Finset.mem_insert_of_mem hk)
    let r := AlgebraProjection.finsetSum q s hos
    have hqr : (q i).val*r.val=0 := by
      change (q i).val*(∑ j ∈ s, (q j).val)=0
      rw [Finset.mul_sum]
      exact Finset.sum_eq_zero (fun j hj => ho i (Finset.mem_insert_self _ _) j
        (Finset.mem_insert_of_mem hj) (fun he => hi (he.symm ▸ hj)))
    have he : AlgebraProjection.finsetSum q (insert i s) ho=orthogonalSum (q i) r hqr := by
      apply Subtype.ext
      exact Finset.sum_insert hi
    rw [he,Finset.sum_insert hi]
    have hadd := traceFreeDyadicSup_orthogonal_add hfactor hdiff hfinite
      ⟨1,IsStarProjection.one _⟩ (q i) r hunit (one_mul _) (one_mul _) hqr
    change traceFreeDimension hfactor hdiff (orthogonalSum (q i) r hqr)=
      traceFreeDimension hfactor hdiff (q i)+traceFreeDimension hfactor hdiff r at hadd
    rw [hadd,ih hos]

include hfinite in
theorem traceFreeDimension_sum_of_total
    (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    {I : Type*} [Fintype I] (q : I → AlgebraProjection M)
    (ho : ∀ i j, i≠j → (q i).val*(q j).val=0)
    (p : AlgebraProjection M) (hp : ∑ i, (q i).val=p.val) :
    ∑ i, traceFreeDimension hfactor hdiff (q i)=traceFreeDimension hfactor hdiff p := by
  classical
  have he : AlgebraProjection.finsetSum q Finset.univ (fun i _ j _ => ho i j)=p := Subtype.ext hp
  rw [← he]
  exact (traceFreeDimension_finsetSum hfactor hdiff hfinite hunit q Finset.univ _).symm

include hfinite in
/-- A finite orthogonal spectral value has the required operator-norm bound. -/
theorem traceFreeDimension_spectralWeight_norm_le
    (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    {I : Type*} [Fintype I] (q : I → AlgebraProjection M)
    (ho : ∀ i j, i≠j → (q i).val*(q j).val=0) (c : I → ℂ) :
    ‖∑ i, c i*(traceFreeDimension hfactor hdiff (q i) : ℂ)‖ ≤
      ‖∑ i, c i • (q i).val‖ := by
  classical
  let a : M.toStarSubalgebra := ∑ i, c i • (q i).val
  have hpiece (i : I) : a*(q i).val=c i • (q i).val := by
    dsimp [a]
    rw [Finset.sum_mul]
    apply (Finset.sum_eq_single i ?_ ?_).trans
      (by rw [smul_mul_assoc,(q i).property.isIdempotentElem.eq])
    · intro j _ hji
      rw [smul_mul_assoc,ho j i hji,smul_zero]
    · intro h; exact (h (Finset.mem_univ i)).elim
  have hterm (i : I) : ‖c i*(traceFreeDimension hfactor hdiff (q i) : ℂ)‖ ≤
      ‖a‖*traceFreeDimension hfactor hdiff (q i) := by
    by_cases hz : (q i).val=0
    · have hD := traceFreeDyadicSup_zero hfactor hdiff ⟨1,IsStarProjection.one _⟩ (q i) hunit hz
      change traceFreeDimension hfactor hdiff (q i)=0 at hD
      simp only [hD,Complex.ofReal_zero,mul_zero,norm_zero,le_refl]
    · have hnorm := norm_mul_le a (q i).val
      rw [hpiece i,norm_smul] at hnorm
      have hpos : 0 < ‖(q i).val‖ := norm_pos_iff.mpr hz
      have hci : ‖c i‖ ≤ ‖a‖ := by nlinarith
      rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (traceFreeDimension_nonneg hfactor hdiff _)]
      exact mul_le_mul_of_nonneg_right hci (traceFreeDimension_nonneg hfactor hdiff _)
  have hdim : (∑ i, traceFreeDimension hfactor hdiff (q i)) ≤ 1 := by
    rw [← traceFreeDimension_finsetSum hfactor hdiff hfinite hunit q Finset.univ
      (fun i _ j _ => ho i j)]
    exact traceFreeDimension_le_one hfactor hdiff _
  calc
    ‖∑ i, c i*(traceFreeDimension hfactor hdiff (q i) : ℂ)‖ ≤
        ∑ i, ‖c i*(traceFreeDimension hfactor hdiff (q i) : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ i, ‖a‖*traceFreeDimension hfactor hdiff (q i) := Finset.sum_le_sum (fun i _ => hterm i)
    _ = ‖a‖*(∑ i, traceFreeDimension hfactor hdiff (q i)) := (Finset.mul_sum _ _ _).symm
    _ ≤ ‖a‖ := by nlinarith [norm_nonneg a]

include hfinite in
/-- In a fixed orthogonal partition, the spectral-value map is contractive. -/
theorem traceFreeDimension_spectralWeight_sub_norm_le
    (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    {I : Type*} [Fintype I] (q : I → AlgebraProjection M)
    (ho : ∀ i j, i≠j → (q i).val*(q j).val=0) (c d : I → ℂ) :
    ‖(∑ i, c i*(traceFreeDimension hfactor hdiff (q i) : ℂ))-
      (∑ i, d i*(traceFreeDimension hfactor hdiff (q i) : ℂ))‖ ≤
      ‖(∑ i, c i • (q i).val)-(∑ i, d i • (q i).val)‖ := by
  simpa only [sub_mul,sub_smul,Finset.sum_sub_distrib] using
    traceFreeDimension_spectralWeight_norm_le hfactor hdiff hfinite hunit q ho (fun i => c i-d i)

/-! Spectral dimension weights agree under common commuting refinements.
Contractivity is proved for two commuting partitions, not noncommuting inputs. -/
namespace CornerPartition
variable {p : AlgebraProjection M} (Q R : CornerPartition p)
variable (hc : ∀ i j, Commute (Q.piece i).val (R.piece j).val)

include hfinite in
theorem dimension_joint_row (hunit : (1 : M.toStarSubalgebra) ≠ 0) (i : Fin Q.size) :
    ∑ j, traceFreeDimension hfactor hdiff (Q.jointPiece R hc (i,j))=
      traceFreeDimension hfactor hdiff (Q.piece i) := by
  apply traceFreeDimension_sum_of_total hfactor hdiff hfinite hunit
    (fun j => Q.jointPiece R hc (i,j))
    (fun j k hjk => Q.jointPiece_orthogonal R hc (i,j) (i,k) (fun h => hjk (congrArg Prod.snd h)))
  change (∑ j, (Q.piece i).val*(R.piece j).val)=(Q.piece i).val
  rw [← Finset.mul_sum,R.total,projection_mul_of_le (Q.piece_le i)]

include hfinite in
theorem dimension_joint_column (hunit : (1 : M.toStarSubalgebra) ≠ 0) (j : Fin R.size) :
    ∑ i, traceFreeDimension hfactor hdiff (Q.jointPiece R hc (i,j))=
      traceFreeDimension hfactor hdiff (R.piece j) := by
  apply traceFreeDimension_sum_of_total hfactor hdiff hfinite hunit
    (fun i => Q.jointPiece R hc (i,j))
    (fun i k hik => Q.jointPiece_orthogonal R hc (i,j) (k,j) (fun h => hik (congrArg Prod.fst h)))
  change (∑ i, (Q.piece i).val*(R.piece j).val)=(R.piece j).val
  rw [← Finset.sum_mul,Q.total]
  exact R.piece_le j

include hfinite in
theorem dimension_weight_joint_left (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (c : Fin Q.size → ℂ) :
    (∑ a : Fin Q.size × Fin R.size,
      c a.1*(traceFreeDimension hfactor hdiff (Q.jointPiece R hc a) : ℂ))=
        ∑ i, c i*(traceFreeDimension hfactor hdiff (Q.piece i) : ℂ) := by
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  dsimp only
  rw [← Finset.mul_sum,← Complex.ofReal_sum,dimension_joint_row hfactor hdiff hfinite Q R hc hunit]

include hfinite in
theorem dimension_weight_joint_right (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (c : Fin R.size → ℂ) :
    (∑ a : Fin Q.size × Fin R.size,
      c a.2*(traceFreeDimension hfactor hdiff (Q.jointPiece R hc a) : ℂ))=
        ∑ i, c i*(traceFreeDimension hfactor hdiff (R.piece i) : ℂ) := by
  rw [Fintype.sum_prod_type,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  dsimp only
  rw [← Finset.mul_sum,← Complex.ofReal_sum,dimension_joint_column hfactor hdiff hfinite Q R hc hunit]

include hfinite hc in
/-- Changing between two commuting partitions preserves the norm estimate. -/
theorem dimension_weight_cross_norm_le (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (c : Fin Q.size → ℂ) (d : Fin R.size → ℂ) :
    ‖(∑ i, c i*(traceFreeDimension hfactor hdiff (Q.piece i) : ℂ))-
      (∑ j, d j*(traceFreeDimension hfactor hdiff (R.piece j) : ℂ))‖ ≤
      ‖(∑ i, c i • (Q.piece i).val)-(∑ j, d j • (R.piece j).val)‖ := by
  have h := traceFreeDimension_spectralWeight_sub_norm_le hfactor hdiff hfinite hunit
    (Q.jointPiece R hc) (Q.jointPiece_orthogonal R hc) (fun a => c a.1) (fun a => d a.2)
  rwa [Q.dimension_weight_joint_left hfactor hdiff hfinite R hc hunit c,
    Q.dimension_weight_joint_right hfactor hdiff hfinite R hc hunit d,
    Q.joint_sum_left R hc c,Q.joint_sum_right R hc d] at h

end CornerPartition

end

/-! Construct the unique real spectral dimension value of each self-adjoint
operator by norm approximation. Global noncommuting additivity is not asserted. -/

/-! The constructed spectral value is bounded and extends the actual
projection dimension. These laws do not assert noncommuting additivity. -/

/-! Finite-family tests and real homogeneity for the constructed spectral value.
These statements do not assert additivity for noncommuting operators. -/
open scoped BigOperators

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_LocalizedStates
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.functionalSubspaceWeakScalarTower _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Localization of actual signed vector/dimension values. Fixed strict
sublevel sets, rather than a limiting strict inequality, supply Zorn bounds. -/
open Filter
open scoped Topology

/-! Tight multiplicative localization of an actual Hilbert vector functional
against the constructed projection dimension. The corner is constructed. -/

/-! Positive spectral approximants inside an actual projection corner, and
extension of localized projection inequalities to positive operators. -/
open scoped BigOperators CStarAlgebra

/-! Projection localization yields actual positive-operator inequalities for
bounded linear functionals, and a nearly cyclic functional on the corner. -/
open scoped BigOperators CStarAlgebra

/-! An actual positive normalized vector functional with arbitrarily small
multiplicative failure of cyclicity on a nonzero corner. No trace is assumed. -/
open scoped CStarAlgebra

/-! A full finite matrix partition can be rebased into every nonzero corner.
The legs are constructed partial isometries, not assumed matrix units. -/
open scoped BigOperators
section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
namespace EquivalentPartition
variable {p : AlgebraProjection M} {ι : Type*} [Fintype ι]

theorem compose_base_target (E : EquivalentPartition p ι) (v : PartialIsometry M)
    (hv : v.target=E.base) (i : ι) :
    ((E.leg i).compose v (by rw [hv,E.initial])).target=(E.leg i).target := by
  apply Subtype.ext
  rw [PartialIsometry.compose_target,hv,← E.initial i,(E.leg i).mul_support]
  rfl

theorem base_ne_zero (E : EquivalentPartition p ι) (hp : p.val≠0) : E.base.val≠0 := by
  intro hz
  have hl (i : ι) : (E.leg i).val=0 := by
    have h := (E.leg i).mul_support
    rw [E.initial,hz,mul_zero] at h
    exact h.symm
  have ht := E.total
  have hz' (i : ι) : (E.leg i).target.val=0 := by
    change (E.leg i).val*star (E.leg i).val=0
    rw [hl,zero_mul]
  rw [show (∑ i, (E.leg i).target.val)=0 from Finset.sum_eq_zero (fun i _ => hz' i)] at ht
  exact hp ht.symm

end EquivalentPartition

variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

include hfactor hdiff hfinite in
/-- Every actual finite equivalent partition has the expected base dimension. -/
theorem EquivalentPartition.dimension_base
    (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    {p : AlgebraProjection M} {ι : Type*} [Fintype ι] [Nonempty ι]
    (E : EquivalentPartition p ι) :
    traceFreeDimension hfactor hdiff E.base=traceFreeDimension hfactor hdiff p/Fintype.card ι := by
  have he (i : ι) : traceFreeDimension hfactor hdiff (E.leg i).target=
      traceFreeDimension hfactor hdiff E.base :=
    (traceFreeDyadicSup_equivalent hfactor hdiff ⟨1,IsStarProjection.one _⟩
      (show E.base.Equivalent (E.leg i).target from ⟨E.leg i,E.initial i,rfl⟩)).symm
  have h := traceFreeDimension_sum_of_total hfactor hdiff hfinite hunit
    (fun i => (E.leg i).target) E.orthogonal p E.total
  simp only [he,Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at h
  apply (eq_div_iff (by exact_mod_cast Fintype.card_ne_zero : (Fintype.card ι : ℝ)≠0)).mpr
  linarith

end

/-! Extension of a vector functional through actual matrix-partition legs.
Finite coefficient identities transfer the corner quadratic inequality. -/
open scoped BigOperators CStarAlgebra
section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
namespace EquivalentPartition
variable {p : AlgebraProjection M} {ι : Type*} [Fintype ι]

/-- Matrix coefficient in the common initial corner. -/
def stateCoefficient (Q : EquivalentPartition p ι) (x : M.toStarSubalgebra) (i j : ι) :
    M.toStarSubalgebra := star (Q.leg i).val*x*(Q.leg j).val

theorem stateCoefficient_left (Q : EquivalentPartition p ι) (x : M.toStarSubalgebra) (i j : ι) :
    Q.base.val*Q.stateCoefficient x i j=Q.stateCoefficient x i j := by
  have hs : Q.base.val*star (Q.leg i).val=star (Q.leg i).val := by
    have h := congrArg star (Q.leg i).mul_support
    simpa only [star_mul,Q.initial,Q.base.property.isSelfAdjoint.star_eq] using h
  change Q.base.val*(star (Q.leg i).val*x*(Q.leg j).val)=_
  rw [← mul_assoc,← mul_assoc,hs]
  rfl

theorem stateCoefficient_right (Q : EquivalentPartition p ι) (x : M.toStarSubalgebra) (i j : ι) :
    Q.stateCoefficient x i j*Q.base.val=Q.stateCoefficient x i j := by
  change (star (Q.leg i).val*x*(Q.leg j).val)*Q.base.val=_
  rw [mul_assoc,← Q.initial j,(Q.leg j).mul_support]
  rfl

theorem stateCoefficient_star (Q : EquivalentPartition p ι) (x : M.toStarSubalgebra) (i j : ι) :
    star (Q.stateCoefficient x i j)=Q.stateCoefficient (star x) j i := by
  simp only [stateCoefficient,star_mul,star_star,mul_assoc]

theorem stateCoefficient_mul (Q : EquivalentPartition p ι) (hp : p.val=1)
    (x y : M.toStarSubalgebra) (i j : ι) :
    Q.stateCoefficient (x*y) i j=∑ k, Q.stateCoefficient x i k*Q.stateCoefficient y k j := by
  have he (k : ι) : Q.stateCoefficient x i k*Q.stateCoefficient y k j=
      star (Q.leg i).val*x*(Q.leg k).target.val*y*(Q.leg j).val := by
    simp only [stateCoefficient,PartialIsometry.target,mul_assoc]
  simp only [he]
  rw [← Finset.sum_mul,← Finset.sum_mul,← Finset.mul_sum,Q.total,hp,mul_one]
  simp only [stateCoefficient,mul_assoc]

/-- An actual finite sum of bounded vector functionals. -/
def matrixVectorFunctional (Q : EquivalentPartition p ι) (ξ : H) : M.toStarSubalgebra →L[ℂ] ℂ :=
  ∑ i, vectorFunctional ((Q.leg i).val.val ξ)

theorem matrixVectorFunctional_apply (Q : EquivalentPartition p ι) (ξ : H) (x : M.toStarSubalgebra) :
    Q.matrixVectorFunctional ξ x=∑ i, vectorFunctional ξ (Q.stateCoefficient x i i) := by
  change (∑ i, vectorFunctional ((Q.leg i).val.val ξ)) x=_
  rw [sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  change inner ℂ ((Q.leg i).val.val ξ) (x.val ((Q.leg i).val.val ξ))=
    inner ℂ ξ (star (Q.leg i).val.val (x.val ((Q.leg i).val.val ξ)))
  rw [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_right]

theorem matrixVectorFunctional_one (Q : EquivalentPartition p ι) (ξ : H) :
    Q.matrixVectorFunctional ξ 1=(∑ i, ‖(Q.leg i).val.val ξ‖^2 : ℝ) := by
  simp only [matrixVectorFunctional,sum_apply,vectorFunctional_apply]
  change (∑ i, inner ℂ ((Q.leg i).val.val ξ) ((Q.leg i).val.val ξ))=_
  simp only [inner_self_eq_norm_sq_to_K,Complex.ofReal_sum,Complex.ofReal_pow]
  norm_cast

theorem matrixVectorFunctional_norm_le (Q : EquivalentPartition p ι) (ξ : H) :
    ‖Q.matrixVectorFunctional ξ‖ ≤ ∑ i, ‖(Q.leg i).val.val ξ‖^2 := by
  change ‖∑ i, vectorFunctional (M := M) ((Q.leg i).val.val ξ)‖ ≤ _
  calc ‖∑ i, vectorFunctional (M := M) ((Q.leg i).val.val ξ)‖ ≤
      ∑ i, ‖vectorFunctional (M := M) ((Q.leg i).val.val ξ)‖ :=
        norm_sum_le Finset.univ (fun i : ι => vectorFunctional (M := M) ((Q.leg i).val.val ξ))
    _ ≤ ∑ i, ‖(Q.leg i).val.val ξ‖^2 :=
      Finset.sum_le_sum (fun i _ => vectorFunctional_norm_le (M := M) ((Q.leg i).val.val ξ))

theorem matrixVectorFunctional_nearly_cyclic (Q : EquivalentPartition p ι) (hp : p.val=1)
    (ξ : H) (ε : ℝ)
    (hcorner : ∀ x : M.toStarSubalgebra, Q.base.val*x=x → x*Q.base.val=x →
      (vectorFunctional ξ (star x*x)).re ≤ (1+ε)*(vectorFunctional ξ (x*star x)).re)
    (x : M.toStarSubalgebra) :
    (Q.matrixVectorFunctional ξ (star x*x)).re ≤
      (1+ε)*(Q.matrixVectorFunctional ξ (x*star x)).re := by
  have hl : (Q.matrixVectorFunctional ξ (star x*x)).re=
      ∑ i, ∑ j, (vectorFunctional ξ (star (Q.stateCoefficient x j i)*Q.stateCoefficient x j i)).re := by
    rw [Q.matrixVectorFunctional_apply,Complex.re_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Q.stateCoefficient_mul hp,map_sum,Complex.re_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [Q.stateCoefficient_star]
  have hr : (Q.matrixVectorFunctional ξ (x*star x)).re=
      ∑ i, ∑ j, (vectorFunctional ξ (Q.stateCoefficient x j i*star (Q.stateCoefficient x j i))).re := by
    rw [Q.matrixVectorFunctional_apply,Complex.re_sum]
    simp_rw [Q.stateCoefficient_mul hp,map_sum,Complex.re_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro i _
    rw [Q.stateCoefficient_star]
  rw [hl,hr,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun j _ => hcorner (Q.stateCoefficient x j i)
    (Q.stateCoefficient_left x j i) (Q.stateCoefficient_right x j i))

end EquivalentPartition
end

/-! Globally defined positive unital linear functionals with arbitrarily small multiplicative quadratic trace error. -/
open scoped BigOperators CStarAlgebra

end Generator.Tracial

end

end OAI
end


