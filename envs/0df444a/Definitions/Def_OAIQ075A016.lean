-- Prove2me | Definitions.Def_OAIQ075A016
-- name    : OAIQ075A016
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T08:12:01.105668+00:00
-- url     : https://prove2.me/theorems/618d9c80-050f-4097-854f-350403b31cc8
-- title:
--   Definitions bundle OAIQ075A016 of the split of OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KadisonSimilarity.similarityTheorem`, `OAI.KadisonSimilarity.universalCommutatorTheorem` and `OAI.KadisonSimilarity.universalHyperreflexivity`, carved from OpenAI's openai/math development (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math) at commit 1581d4c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 219 declarations of OpenAI's Lean: 85 definitions, 2 inductive types or structures, 2 instances and 130 theorems. The definitions and types are `OAI.Generator.Tracial.approximationLE`, `OAI.Generator.Tracial.approximationOrder`, `OAI.Generator.Tracial.approximationPreorder`, `OAI.Generator.Tracial.expectationContractiveCStar`, `OAI.Generator.Tracial.expectationContractiveLE`, `OAI.Generator.Tracial.expectationContractiveOrder`, `OAI.Generator.Tracial.expectationContractivePreorder`, `OAI.Generator.Tracial.expectationPosCStar`, `OAI.Generator.Tracial.expectationPosLE`, `OAI.Generator.Tracial.expectationPosOrder`, `OAI.Generator.Tracial.spectralCommutationCStar`, `OAI.Generator.Tracial.spectralCommutationOrder`, `OAI.HochschildMatrixDilation.diagHom`, `OAI.KadisonSimilarity.AlternatingCreationCoordinates`, `OAI.KadisonSimilarity.CenteredTracialLetter`, `OAI.KadisonSimilarity.DihedralSpectralArc.corner`, `OAI.KadisonSimilarity.MatrixHilbertStage.form`, `OAI.KadisonSimilarity.MultiplicityWordSpace`, `OAI.KadisonSimilarity.NestedTracialMatrices.columnFamily`, `OAI.KadisonSimilarity.NestedTracialMatrices.finColumnFamily`, `OAI.KadisonSimilarity.ReducedWordGenerated`, `OAI.KadisonSimilarity.SmallFreeCornerData`, `OAI.KadisonSimilarity.TracialCornerGeometry.FactorsTraciallyGenerate`, `OAI.KadisonSimilarity.TracialCornerGeometry.actionMultiplicityInnerFamily`, `OAI.KadisonSimilarity.TracialCornerGeometry.actionMultiplicityNormedFamily`, `OAI.KadisonSimilarity.TracialCornerGeometry.automorphismIsometry`, `OAI.KadisonSimilarity.TracialCornerGeometry.automorphismRepresentation`, `OAI.KadisonSimilarity.TracialCornerGeometry.automorphismUnitary`, `OAI.KadisonSimilarity.TracialCornerGeometry.baseAction`, `OAI.KadisonSimilarity.TracialCornerGeometry.baseAlgebraVectors`, `OAI.KadisonSimilarity.TracialCornerGeometry.baseCompression`, `OAI.KadisonSimilarity.TracialCornerGeometry.baseGeometry`, `OAI.KadisonSimilarity.TracialCornerGeometry.baseHaarLetter`, `OAI.KadisonSimilarity.TracialCornerGeometry.baseInclusion`, `OAI.KadisonSimilarity.TracialCornerGeometry.baseOperator`, `OAI.KadisonSimilarity.TracialCornerGeometry.baseRepresentation`, `OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace`, `OAI.KadisonSimilarity.TracialCornerGeometry.baseSymmetryLetter`, `OAI.KadisonSimilarity.TracialCornerGeometry.baseVector`, `OAI.KadisonSimilarity.TracialCornerGeometry.conjugation` and 47 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `BoundedHochschild_Corners`, `BoundedHochschild_Dixmier`, `BoundedHochschild_MatrixDilation`, `BoundedHochschild_PartialIsometries`, `BoundedHochschild_PartialUnitaries`, `BoundedHochschild_RelativeQuantization`, `FactorGeneration_Expectations`, `FactorGeneration_MatrixAlgebras`, `FactorGeneration_ProjectionLimits`, `FactorGeneration_SpectralPinching`, `FactorGeneration_Subfactors`, `KadisonSimilarity_Derivation_TracialCornerCyclicity`, `KadisonSimilarity_FreeProduct_ActualArcCompression`, `KadisonSimilarity_FreeProduct_BaseSymmetry`, `KadisonSimilarity_FreeProduct_DihedralWordColumn`, `KadisonSimilarity_FreeProduct_DihedralWordIsometries`, `KadisonSimilarity_FreeProduct_FreeProductAutomorphisms`, `KadisonSimilarity_FreeProduct_FreeProductMatrixExtension`, `KadisonSimilarity_FreeProduct_FreeWordHilbert`, `KadisonSimilarity_FreeProduct_OrthogonalWordLevels`, `KadisonSimilarity_FreeProduct_ReducedWordModel`, `KadisonSimilarity_FreeProduct_SmallFreeCornerData`, `KadisonSimilarity_FreeProduct_SpectralArc`, `KadisonSimilarity_FreeProduct_TracialDihedralColumns`, `KadisonSimilarity_FreeProduct_TracialWordActions`, `KadisonSimilarity_FreeProduct_TracialWordIsometry`, `KadisonSimilarity_FreeProduct_WordBaseCoordinates`, `KadisonSimilarity_FreeProduct_WordLevelClassification`, `KadisonSimilarity_FreeProduct_WordMultiplicities`, `KadisonSimilarity_FreeProduct_WordPrefixRealization`, `KadisonSimilarity_FreeProduct_WordPropagationTransfer`, `KadisonSimilarity_Representation_ReducedCreationBlocks`, `KadisonSimilarity_Tensor_InvariantForms`, `KadisonSimilarity_Tensor_InvariantIntertwiners`, `KadisonSimilarity_Tensor_MultiplicityClassification`, `KadisonSimilarity_Tensor_TensorHeadSlices`, `KadisonSimilarity_Tracial_MatrixConjugateAutomorphism`, `KadisonSimilarity_Tracial_MatrixUnitFamilies`, `KadisonSimilarity_Tracial_TracialAutomorphisms`, `KadisonSimilarity_Tracial_TracialBaseGeometry`, `KadisonSimilarity_Tracial_TracialBaseSpace`, `KadisonSimilarity_Tracial_TracialCornerHilbert`, `KadisonSimilarity_Tracial_TracialCornerRepresentations`, `KadisonSimilarity_Tracial_TracialCreationCoordinates`, `KadisonSimilarity_Tracial_TracialMatrixColumns`, `KadisonSimilarity_Tracial_TracialMatrixRealization`, `KadisonSimilarity_Tracial_TracialMatrixTower`, `KadisonSimilarity_Tracial_TracialSpectralNorm`, `KadisonSimilarity_Tracial_TracialSupportedColumns`.
--
--   **Imports.** It imports the bundles `OAIQ075A007`, `OAIQ075A008` and `OAIQ075A009` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ075A021`, `OAIQ075A022`, `OAIQ075A023`, `OAIQ075A024` and `OAIQ075A025`; the statement `OAI.KadisonSimilarity.TracialCornerGeometry.exists_smallFreeCornerData_of_normal_matrix_tower`; the proof of `OAI.BoundedHochschild.KadisonRingrose.factorization_of_complete_bound`.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 1581d4c

import Mathlib
import Definitions.Def_OAIQ075A007
import Definitions.Def_OAIQ075A008
import Definitions.Def_OAIQ075A009

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_MatrixDilation
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.UltrapowerBridge.instStarTracialQuotient
attribute [-simp] _root_.OAI.HochschildMatrixDilation.diag_pow _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Matrix dilations, tracial matrix algebras and bounded linear maps. -/

noncomputable section

open scoped ComplexOrder
open Filter Topology
namespace HochschildMatrixDilation
noncomputable section
open scoped Matrix ComplexOrder
open Complex
variable {A : Type*} [CStarAlgebra A]


def diagHom : A × A →⋆ₐ[ℂ] Mat A where
  toFun a := diag a.1 a.2
  map_one' := diag_one_one
  map_mul' a b := (diag_mul _ _ _ _).symm
  map_zero' := diag_zero_zero
  map_add' a b := diag_add _ _ _ _
  commutes' z := by
    ext i j; fin_cases i <;> fin_cases j <;>
      rfl
  map_star' a := (star_diag _ _).symm

variable [PartialOrder A] [StarOrderedRing A]

lemma norm_diag_le (a b : A) : ‖diag a b‖ ≤ max ‖a‖ ‖b‖ := by
  exact NonUnitalStarAlgHom.norm_apply_le diagHom (a,b)

omit [PartialOrder A] [StarOrderedRing A] in
lemma offdiag_selfAdjoint (a : A) : IsSelfAdjoint (offdiag a (star a)) := by
  change star (offdiag a (star a)) = _
  simp

lemma offdiag_norm_le_one (a : A) (ha : ‖a‖ ≤ 1) : ‖offdiag a (star a)‖ ≤ 1 := by
  have hsq : ‖offdiag a (star a)‖^2 ≤ 1 := by
    rw [← (offdiag_selfAdjoint a).norm_mul_self, offdiag_mul]
    refine (norm_diag_le _ _).trans (max_le ?_ ?_)
    · calc
        ‖a * star a‖ ≤ ‖a‖ * ‖star a‖ := norm_mul_le _ _
        _ ≤ 1 := by rw [norm_star]; nlinarith [norm_nonneg a]
    · calc
        ‖star a * a‖ ≤ ‖star a‖ * ‖a‖ := norm_mul_le _ _
        _ ≤ 1 := by rw [norm_star]; nlinarith [norm_nonneg a]
  exact (sq_le_one_iff₀ (norm_nonneg _)).mp hsq

end
end HochschildMatrixDilation
end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_Dixmier
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.UltrapowerBridge.instStarTracialQuotient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Hilbert-space averaging and central elements in unitary orbit closures. -/

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
open Filter Topology
open scoped ComplexOrder
namespace HochschildDixmier
open BoundedHochschild HochschildRigidity
variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hL : ∀ b : M, HasPreadjoint e (ContinuousLinearMap.mul ℂ M b))
  (hτ : TraceInPredual e τ)

include e hL hτ in
 

theorem scalar_mem_orbit_closure (h1 : τ 1=1) (htr : ∀ x y : M, τ (x*y)=τ (y*x))
    (hfaith : ∀ x : M, τ (star x*x)=0 → x=0)
    (hfactor : ∀ b : M, (∀ x : M, Commute b x) → ∃ c : ℂ, b=c • (1 : M)) (a : M) :
    gnsVector τ ((τ a) • (1 : M)) ∈ closure (gnsVector τ '' convexHull ℝ
      (Set.range (fun v : unitary M => conjugate v a))) := by
  obtain ⟨b,_hb,hbc,hbK⟩ := exists_central_average e τ hL hτ htr hfaith a
  obtain ⟨c,hc⟩ := hfactor b hbc
  have hbτ := trace_orbit_closure τ h1 htr a b hbK
  have hca : c=τ a := by simpa only [hc,map_smul,h1,smul_eq_mul,mul_one] using hbτ
  simpa only [hc,hca] using hbK

end HochschildDixmier
end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_PartialIsometries
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.UltrapowerBridge.instStarTracialQuotient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Partial isometries and comparison of equal-trace projections. -/

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
open scoped ComplexOrder
namespace HochschildComparison
variable {M : Type*} [CStarAlgebra M]

namespace PartialIso

variable [PartialOrder M]

variable [StarOrderedRing M]

lemma diff_square {v w : PartialIso M} (h : v ≤ w) :
    star ((w : M) - v) * ((w : M) - v) = w.initial - v.initial := by
  simp only [star_sub, sub_mul, mul_sub, star_mul_of_le h, star_mul_of_ge h,
    ]
  simp only [initial]
  abel

end PartialIso
end HochschildComparison

 

 

open Filter Topology
open scoped ComplexOrder
namespace HochschildComparison
open BoundedHochschild HochschildRigidity HochschildDixmier
variable {M X : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hL : ∀ b : M, HasPreadjoint e (ContinuousLinearMap.mul ℂ M b))
  (hτ : TraceInPredual e τ) (htr : ∀ x y : M, τ (x*y)=τ (y*x))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)

namespace PartialIso

include hfaith in
lemma le_of_comparable_trace_le {v w : PartialIso M} (hc : v ≤ w ∨ w ≤ v)
    (ht : (τ v.initial).re ≤ (τ w.initial).re) : v ≤ w := by
  rcases hc with h|h
  · exact h
  · have hr := HochschildDiffuse.projection_le_of_comparable_trace_le τ hfaith
      v.initial_proj w.initial_proj (Or.inr h.1) ht
    have he := eq_of_le_of_initial_eq h (le_antisymm h.1 hr)
    exact le_of_eq he.symm

lemma diff_gns_sq {v w : PartialIso M} (h : v ≤ w) :
    ‖τ.toPreGNS ((w : M)-v)‖^2 = (τ w.initial).re-(τ v.initial).re := by
  have ht := congrArg Complex.re (τ.preGNS_norm_sq (τ.toPreGNS ((w : M)-v)))
  simpa only [PositiveLinearMap.ofPreGNS_toPreGNS, ← Complex.ofReal_pow,
    Complex.ofReal_re,diff_square h,map_sub,Complex.sub_re] using ht

lemma monotone_gns_cauchy (v : ℕ → PartialIso M) (hv : Monotone v) :
    CauchySeq (fun n => τ.toPreGNS (v n : M)) := by
  have hm : Monotone (fun n => (τ (v n).initial).re) := fun i j hij =>
    Complex.re_le_re (τ.monotone (hv hij).1)
  have hb : BddAbove (Set.range (fun n => (τ (v n).initial).re)) :=
    ⟨(τ 1).re, fun _ ⟨n,hn⟩ => hn ▸ Complex.re_le_re (τ.monotone (v n).initial_proj.le_one)⟩
  have hc := (tendsto_atTop_ciSup hm hb).cauchySeq
  apply Metric.cauchySeq_iff'.mpr
  intro ε hε
  obtain ⟨N,hN⟩ := Metric.cauchySeq_iff'.mp hc (ε^2) (sq_pos_of_pos hε)
  refine ⟨N,fun n hn => ?_⟩
  have he := diff_gns_sq τ (hv hn)
  have hdiff := hN n hn
  rw [Real.dist_eq,abs_of_nonneg (sub_nonneg.mpr (hm hn))] at hdiff
  rw [dist_eq_norm,← map_sub]
  nlinarith [norm_nonneg (τ.toPreGNS ((v n : M)-v N))]

include e hL hτ htr hfaith in
lemma exists_monotone_limit (v : ℕ → PartialIso M) (hv : Monotone v) :
    ∃ w : PartialIso M, GNSTendsto τ (fun n => (v n : M)) atTop (w : M) ∧
      (∀ n, v n ≤ w) ∧ ∀ z : PartialIso M, (∀ n, v n ≤ z) → w ≤ z := by
  obtain ⟨w,hw,ht⟩ := exists_bounded_preGNS_limit e τ hL hτ 1
    (fun n => (v n).norm_le_one) (monotone_gns_cauchy τ v hv)
  change GNSTendsto τ (fun n => (v n : M)) atTop w at ht
  have hstar := ht.star τ htr
  have hin := hstar.mul τ htr ht 1 (fun n => by simpa only [norm_star] using (v n).norm_le_one)
  have hfin := ht.mul τ htr hstar 1 (fun n => (v n).norm_le_one)
  have hww : w*star w*w=w := by
    apply GNSTendsto.unique τ hfaith (hfin.mul τ htr ht 1 (fun n => (v n).final_proj.norm_le _))
    simpa only [(v _).mul_star_mul] using ht
  let s : PartialIso M := ⟨w,hww⟩
  change GNSTendsto τ (fun n => (v n).initial) atTop s.initial at hin
  refine ⟨s,ht,?_,?_⟩
  · intro n
    have him : (v n).initial ≤ s.initial := by
      apply ((v n).initial_proj.le_iff_mul_eq_left s.initial_proj).mpr
      apply GNSTendsto.unique τ hfaith
        ((GNSTendsto.const τ (v n).initial atTop).mul τ htr hin 1
          (fun _ => (v n).initial_proj.norm_le _))
      change Tendsto (fun m => ‖τ.toPreGNS ((v n).initial*(v m).initial-(v n).initial)‖) atTop (𝓝 0)
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop n] with m hm
      simp only [((v n).initial_proj.le_iff_mul_eq_left (v m).initial_proj).mp
        (hv hm).1,sub_self,map_zero,norm_zero]
    refine ⟨him,?_⟩
    apply GNSTendsto.unique τ hfaith (ht.mul τ htr (GNSTendsto.const τ (v n).initial atTop)
      1 (fun m => (v m).norm_le_one))
    change Tendsto (fun m => ‖τ.toPreGNS ((v m : M)*(v n).initial-(v n : M))‖) atTop (𝓝 0)
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop n] with m hm
    simp only [(hv hm).2,sub_self,map_zero,norm_zero]
  · intro z hz
    have him : s.initial ≤ z.initial := by
      apply (s.initial_proj.le_iff_mul_eq_left z.initial_proj).mpr
      apply GNSTendsto.unique τ hfaith (hin.mul τ htr (GNSTendsto.const τ z.initial atTop)
        1 (fun m => (v m).initial_proj.norm_le _))
      simpa only [((v _).initial_proj.le_iff_mul_eq_left z.initial_proj).mp (hz _).1]
        using hin
    refine ⟨him,?_⟩
    apply GNSTendsto.unique τ hfaith
      ((GNSTendsto.const τ (z : M) atTop).mul τ htr hin 1 (fun _ => z.norm_le_one))
    simpa only [(hz _).2] using ht

end PartialIso

include e hL hτ htr hfaith in
lemma exists_nonzero_corner (h1 : τ 1=1)
    (hfactor : ∀ b : M, (∀ x : M, Commute b x) → ∃ c : ℂ, b=c • (1 : M))
    {p q : M} (hp : IsStarProjection p) (hq : IsStarProjection q)
    (hp0 : p ≠ 0) (hq0 : q ≠ 0) : ∃ a : M, p*a*q ≠ 0 := by
  classical
  by_contra hex
  push Not at hex
  have hh := scalar_mem_orbit_closure e τ hL hτ h1 htr hfaith hfactor q
  obtain ⟨b,hb,hbt⟩ := mem_closure_iff_seq_limit.mp hh
  choose a ha hab using hb
  have han : ∀ n, p*a n=0 := by
    have hk : convexHull ℝ (Set.range (fun u : unitary M => conjugate u q)) ⊆
        {a : M | p*a=0} := by
      apply convexHull_min
      · rintro _ ⟨u,rfl⟩
        change p*((u : M)*q*star (u : M))=0
        rw [← mul_assoc,← mul_assoc,hex (u : M),zero_mul]
      · intro x hx y hy r t _hr _ht _hrt
        change p*x=0 at hx
        change p*y=0 at hy
        change p*(r • x+t • y)=0
        simp only [mul_add,mul_smul_comm,hx,hy,smul_zero,add_zero]
    exact fun n => hk (ha n)
  have ht : GNSTendsto τ a atTop ((τ q) • (1 : M)) := by
    have hz := tendsto_iff_norm_sub_tendsto_zero.mp hbt
    simpa only [GNSTendsto,← hab,← map_sub,gnsVector_norm] using hz
  have hpq : p*((τ q) • (1 : M))=0 := by
    apply GNSTendsto.unique τ hfaith
      ((GNSTendsto.const τ p atTop).mul τ htr ht 1 (fun _ => hp.norm_le _))
    simpa only [han] using (GNSTendsto.const τ (0 : M) (atTop : Filter ℕ))
  have htq : τ q ≠ 0 := by
    intro hzero
    apply hq0
    apply hfaith q
    simpa only [hq.isSelfAdjoint.star_eq,hq.isIdempotentElem.eq] using hzero
  rw [mul_smul_comm,mul_one,smul_eq_zero] at hpq
  exact hpq.elim htq hp0

end HochschildComparison
end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_Corners
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instPartialOrderSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.cstarCornerSubalgebra_closed _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.algebra_closed _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.UltrapowerBridge.instStarTracialQuotient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Spectral corners, corner preduals and factor structure. -/

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
open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter Topology
open scoped ComplexOrder







open Filter Topology
open scoped ComplexOrder
namespace HochschildCorners
open BoundedHochschild BoundedHochschild.WeakAlgebra HochschildRigidity HochschildSakai
universe u
variable {M : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
variable (p : M) (hp : IsStarProjection p)

section Predual
variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)

lemma cornerPredualEquiv_apply (F : StrongDual ℂ (CornerPredual p hp e)) (z : X) :
    e.symm ((cornerPredualEquiv p hp e F : Corner p hp):M) z=F (Submodule.Quotient.mk z) := by
  change e.symm (e (F.comp (WeakSubspace.preannihilator (weakCorner p hp e)).mkQL)) z=_
  rw [e.symm_apply_apply]
  rfl

lemma cornerPredualEquiv_symm_mk (a : Corner p hp) (z : X) :
    (cornerPredualEquiv p hp e).symm a (Submodule.Quotient.mk z)=e.symm (a:M) z := by
  have h := (cornerPredualEquiv p hp e).apply_symm_apply a
  have hh := congrArg (fun b : Corner p hp => e.symm (b:M) z) h
  rw [cornerPredualEquiv_apply] at hh
  exact hh

end Predual
end HochschildCorners

 

 

open Filter Topology
open scoped ComplexOrder
namespace HochschildCorners
open BoundedHochschild HochschildRigidity HochschildSakai HochschildMatrixSystems
universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (p : M) (hp : IsStarProjection p)

lemma corner_no_minimal (hdiff : HochschildDiffuse.NoMinimalProjections M) :
    HochschildDiffuse.NoMinimalProjections (Corner p hp) := by
  intro q hq hq0
  obtain ⟨r,hr,hrq,hr0,hrne⟩ := hdiff (q:M) (corner_projection_coe p hp hq)
    (fun h => hq0 (Subtype.ext h))
  have hrp := hrq.trans (corner_projection_le p hp hq)
  have hrc : r ∈ corner p hp := ⟨(hr.le_iff_mul_eq_right hp).mp hrp,
    (hr.le_iff_mul_eq_left hp).mp hrp⟩
  refine ⟨⟨r,hrc⟩,⟨Subtype.ext hr.isIdempotentElem.eq,Subtype.ext hr.isSelfAdjoint.star_eq⟩,
    hrq,?_,?_⟩
  · exact fun h => hr0 (congrArg (fun a : Corner p hp => (a:M)) h)
  · exact fun h => hrne (congrArg (fun a : Corner p hp => (a:M)) h)

variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)

lemma cornerTrace_normal (hτ : TraceInPredual e τ) :
    TraceInPredual (cornerPredualEquiv p hp e) (cornerTrace p hp τ) := by
  obtain ⟨z,hz⟩ := hτ
  let zq : CornerPredual p hp e := Submodule.Quotient.mk z
  refine ⟨((τ p).re : ℂ)⁻¹ • zq,fun a => ?_⟩
  rw [map_smul]
  change _ = star (((τ p).re : ℂ)⁻¹ * (cornerPredualEquiv p hp e).symm a (Submodule.Quotient.mk z))
  rw [cornerPredualEquiv_symm_mk]
  rw [cornerTrace_apply,hz a.val,star_mul,star_inv₀]
  simp only [Complex.star_def,Complex.conj_ofReal]
  exact mul_comm _ _

end HochschildCorners

 

 

open Filter Topology
open scoped ComplexOrder
end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_PartialUnitaries
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat
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

lemma le_orthogonalSum (v w : PartialUnitary M) (h : v.support*w.support=0) : v≤v.orthogonalSum w h :=
  PartialIso.le_orthogonalSum v.val w.val h (by simpa only [v.property,w.property] using h)



end PartialUnitary
end HochschildComparison

 

 

open Filter Topology
open scoped ComplexOrder







open scoped ComplexOrder
end

end OAI
end

section
-- module Solutions.OAIQ075_KS.BoundedHochschild_RelativeQuantization
attribute [-instance] _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instPartialOrderSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.cstarCornerSubalgebra_closed _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.algebra_closed _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instStarOrderedRing _root_.OAI.UltrapowerBridge.instStarTracialQuotient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Relative small corners, root phases and weak powers of unitaries. -/

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
open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter Topology
open scoped ComplexOrder
namespace HochschildQuantization
open BoundedHochschild HochschildRigidity HochschildSakai HochschildMatrixSystems HochschildCorners
universe u v
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (p : M) (hp : IsStarProjection p)
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)

lemma corner_norm_sq (a : Corner p hp) :
    ‖(cornerTrace p hp τ).toPreGNS a‖^2=(τ p).re⁻¹*‖τ.toPreGNS (a:M)‖^2 := by
  rw [MatrixSystem.norm_sq,cornerTrace_apply,corner_coe_mul,corner_coe_star,MatrixSystem.norm_sq]
  simp only [← Complex.ofReal_inv,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]

end HochschildQuantization

 

 

 

open scoped BigOperators ComplexConjugate InnerProductSpace





open scoped BigOperators ComplexConjugate InnerProductSpace ComplexOrder







open Filter Topology
open scoped ComplexOrder
end

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_ProjectionLimits
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instRing
attribute [-simp] _root_.OAI.Generator.Tracial.quotientInclusion_mk _root_.OAI.Generator.Tracial.quotientInclusion_trace _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! A nonzero projection in a diffuse tracial algebra contains nonzero projections of arbitrarily small trace. -/

/-! Monotone projection limits with trace bounds, giving chain bounds for prescribed trace cuts. -/

/-! Exact trace cuts in a diffuse coordinate algebra. -/

/-! Algebraic part of Popa 1308.3982v3, Lemma 3.2: adding a supported
partial unitary in the residual corner. The small mixed-word estimates and
the existence of an appropriate patch are separate analytic requirements. -/

/-! Dyadic projections inside a diffuse algebra with faithful trace. -/

/-! Finite spectral sums in the constructed dyadic projection algebras. -/
open scoped BigOperators
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

theorem projection_trace_real (τ : TracialRepresentation M) (p : AlgebraProjection M) :
    τ.trace p.val = ((τ.trace p.val).re : ℂ) := by
  have h := τ.trace_star_mul p.val
  rw [p.property.isSelfAdjoint.star_eq,p.property.isIdempotentElem.eq] at h
  rw [h,← Complex.ofReal_pow,Complex.ofReal_re]

variable {ι : Type*} [Fintype ι]

theorem projectionSum_star (a : ι → AlgebraProjection M) (c : ι → ℂ) :
    star (projectionSum a c)=projectionSum a (fun i => star (c i)) := by
  simp only [projectionSum,star_sum,star_smul,(a _).property.isSelfAdjoint.star_eq]

theorem projectionSum_mul (a : ι → AlgebraProjection M)
    (ha : ∀ i j, i ≠ j → (a i).val*(a j).val=0) (c d : ι → ℂ) :
    projectionSum a c*projectionSum a d=projectionSum a (fun i => c i*d i) := by
  classical
  unfold projectionSum
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  rw [Finset.sum_eq_single i]
  · rw [smul_mul_assoc,mul_smul_comm,smul_smul,(a i).property.isIdempotentElem.eq]
  · intro j _ hji
    rw [smul_mul_assoc,mul_smul_comm,ha i j hji.symm,smul_zero,smul_zero]
  · simp

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_SpectralPinching
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.tupleOrbitClosure_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedAlgebraComplexSubtypeMemNonUnitalStarSubalgebra _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instPartialOrderSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedAlgebra _root_.OAI.PopaCorner.instNormedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Actual sign splitting inside a prescribed residual corner. -/

/-! The constructed spectral splitting preserves the compressed operator.
This is distinct from using that splitting to reduce other operators' energy. -/

/-! Interval bounds propagated through constructed spectral corner splits. -/

/-! Finite dyadic trees of actual spectral interval cuts. -/
section
open scoped CStarAlgebra BigOperators
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

/-! Finite spectral approximations constructed by successive sign cuts.
The approximation bound is proved from the leaf intervals. -/
local instance approximationOrder : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance approximationPreorder : Preorder M.toStarSubalgebra :=
  (CStarAlgebra.spectralOrder _).toPreorder
local instance approximationLE : LE M.toStarSubalgebra := (CStarAlgebra.spectralOrder _).toLE
local instance approximationCStar_r90fc68_1 : CStarAlgebra M.toStarSubalgebra := {}
local instance approximationStarOrder : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _

end

/-! Constructed cuts preserve commutation with other operators. -/
section
open scoped CStarAlgebra
open UltrapowerBridge ContinuousLinearMap LinearMap
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
local instance spectralCommutationCStar : CStarAlgebra M.toStarSubalgebra := {}
local instance spectralCommutationOrder : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance spectralCommutationStarOrder : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _

end

/-! Spectral interval partitions in the commutant of a prescribed operator. -/
open scoped BigOperators
open UltrapowerBridge

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_Subfactors
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instRing
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
section
open scoped BigOperators ComplexStarModule
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)
variable (P : StarSubalgebra ℂ M.toStarSubalgebra) [CompleteSpace P]
variable (hirr : ∀ c : M.toStarSubalgebra,
  (∀ a : P, (a : M.toStarSubalgebra)*c=c*(a : M.toStarSubalgebra)) →
  ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))

omit [CompleteSpace P] in
/-- Taking adjoints preserves the supported relative-commutant condition. -/
theorem corner_commutant_star (p : AlgebraProjection M) (c : M.toStarSubalgebra)
    (hcomm : ∀ a : P, Commute c (p.val*(a : M.toStarSubalgebra)*p.val)) :
    ∀ a : P, Commute (star c) (p.val*(a : M.toStarSubalgebra)*p.val) := by
  intro a
  have h := congrArg star (hcomm (star a)).eq
  change star (c*(p.val*star (a : M.toStarSubalgebra)*p.val)) =
    star ((p.val*star (a : M.toStarSubalgebra)*p.val)*c) at h
  show star c*(p.val*(a : M.toStarSubalgebra)*p.val)=
    (p.val*(a : M.toStarSubalgebra)*p.val)*star c
  simpa only [star_mul,star_star,p.property.isSelfAdjoint.star_eq,
    mul_assoc] using h.symm

end

/-! The relative commutant of a finite block algebra consists of scalars on
each block. This statement is proved from coordinate irreducibility. -/

/-! Orthogonality to the prescribed subalgebra is stronger than global
centering. It is preserved by compressions and conjugations from that
subalgebra and removes every block scalar term exactly. -/

/-! A corner whose only projections are zero and its unit is scalar.
The proof constructs spectral approximations; minimality is not a scalar-corner axiom. -/

/-! Diffuseness descends to an irreducible von Neumann subalgebra of a
diffuse finite tracial algebra. Finiteness follows from the actual faithful trace. -/
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {P M : VonNeumannAlgebra H}

theorem tracial_nonzero (τ : TracialRepresentation M) : (0 : H →L[ℂ] H) ≠ 1 := by
  intro h
  have hzero : τ.vector=0 := by
    have he := congrArg (fun T : H →L[ℂ] H => T τ.vector) h
    exact he.symm
  have hn := τ.norm_vector
  rw [hzero,norm_zero] at hn
  exact zero_ne_one hn

end Generator.Tracial

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.FactorGeneration_Expectations
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedAlgebraComplexSubtypeMemNonUnitalStarSubalgebra _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instPartialOrderSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedAlgebra _root_.OAI.PopaCorner.instNormedRing
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

/-! The constructed expectation preserves adjoints, is a bimodule map,
and is the orthogonal projection for the trace norm. -/

/-! Positivity of the constructed expectation. The negative spectral part
is an actual subalgebra test operator; tracial orthogonality eliminates it. -/
section
open scoped CStarAlgebra
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M)
local instance expectationPosCStar : CStarAlgebra M.toStarSubalgebra := {}
local instance expectationPosOrder : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance expectationPosPreorder_r90fc68_1 : Preorder M.toStarSubalgebra :=
  (CStarAlgebra.spectralOrder _).toPreorder
local instance expectationPosLE : LE M.toStarSubalgebra := (CStarAlgebra.spectralOrder _).toLE
local instance expectationPosStarOrder : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _

end

/-! The constructed expectation satisfies the Schwarz inequality and is
contractive in operator norm. -/
section
open scoped CStarAlgebra
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M)
local instance expectationContractiveCStar : CStarAlgebra M.toStarSubalgebra := {}
local instance expectationContractiveOrder : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance expectationContractivePreorder : Preorder M.toStarSubalgebra :=
  (CStarAlgebra.spectralOrder _).toPreorder
local instance expectationContractiveLE : LE M.toStarSubalgebra := (CStarAlgebra.spectralOrder _).toLE
local instance expectationContractiveStarOrder : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _

end

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
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instRing
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
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

/-! The actual relative commutant in M is a diffuse scalar-center von
Neumann algebra, with the restricted faithful trace available from M. -/

/-! Explicit Bell projections in two equal finite matrix factors. -/
open scoped BigOperators

/-! Exact normalized traces of constructed matrix algebras and all their
commuting product refinements. -/
open scoped BigOperators
namespace MatrixUnitSystem

section
open UltrapowerBridge Tracial
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (E : MatrixUnitSystem ι M.toStarSubalgebra) (τ : TracialRepresentation M)

theorem trace_diagonal_eq (i j : ι) : τ.trace (E.entry i i)=τ.trace (E.entry j j) := by
  have h := τ.trace_mul_comm (E.entry i j) (E.entry j i)
  simpa only [E.mul_entry,ite_true] using h

theorem trace_off_diagonal (i j : ι) (hij : i ≠ j) : τ.trace (E.entry i j)=0 := by
  have h := τ.trace_mul_comm (E.entry i i) (E.entry i j)
  simpa [E.mul_entry,hij,Ne.symm hij,TracialRepresentation.trace] using h

theorem trace_diagonal (o : ι) :
    τ.trace (E.entry o o)=(Fintype.card ι : ℂ)⁻¹ := by
  have h : (Fintype.card ι : ℂ)*τ.trace (E.entry o o)=1 := by
    calc _ = ∑ i, τ.trace (E.entry i i) := by
               simp only [E.trace_diagonal_eq τ _ o,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
         _ = τ.trace (∑ i,E.entry i i) := by
               let t : M.toStarSubalgebra →+ ℂ :=
                 { toFun := τ.trace, map_zero' := by simp [TracialRepresentation.trace],
                   map_add' := τ.trace_add }
               exact (map_sum t _ _).symm
         _ = 1 := by rw [E.total,τ.trace_one]
  exact eq_inv_of_mul_eq_one_right h

theorem trace_hom (_ : ι) (a : Matrix ι ι ℂ) :
    τ.trace (E.hom a)=(Fintype.card ι : ℂ)⁻¹*Matrix.trace a := by
  have hsum (b : ι → M.toStarSubalgebra) : τ.trace (∑ i,b i)=∑ i,τ.trace (b i) := by
    let t : M.toStarSubalgebra →+ ℂ :=
      { toFun := τ.trace, map_zero' := by simp [TracialRepresentation.trace],
                   map_add' := τ.trace_add }
    exact map_sum t _ _
  rw [E.hom_apply,hsum]
  simp only [hsum,τ.trace_smul]
  have hentry (i j : ι) : τ.trace (E.entry i j)=
      if i=j then (Fintype.card ι : ℂ)⁻¹ else 0 := by
    split
    · next h => subst j; exact E.trace_diagonal τ i
    · next h => exact E.trace_off_diagonal τ i j h
  simp only [hentry,mul_ite,mul_zero,Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  rw [Matrix.trace,Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

end

open UltrapowerBridge Tracial

end MatrixUnitSystem

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tensor_InvariantForms
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.UltrapowerBridge.instStarTracialQuotient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The finite-stage coefficient form

The coefficient function used by the invariant argument is proved multilinear
from the linear source letters and conjugate-linear test letters. No finite or
completed coefficient expansion is part of this construction.
-/

noncomputable section
namespace KadisonSimilarity

open scoped ComplexConjugate TensorProduct

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

variable {D : Type*} [AddCommGroup D] [Module ℂ D] {k l : ℕ}

/-- Multilinearity of the actual finite-stage coefficient function. -/
def invariantStageForm
    (Y : EndpointTensor E F k →L[ℂ] EndpointTensor E F l) (Ω : E)
    (testEndpoint : D →ₗ⋆[ℂ] E) (sourceLetter : D →ₗ[ℂ] F)
    (testLetter : D →ₗ⋆[ℂ] F) :
    MultilinearMap ℂ (fun _ : Option (Fin k ⊕ Fin l) => D) ℂ :=
  MultilinearMap.mk' (invariantStageCoefficient Y Ω testEndpoint sourceLetter testLetter)
    (by
      intro v i a b
      cases i with
      | none =>
        have hs (a : D) : pullLetters sourceLetter (@sourceIndex k l) (Function.update v none a) =
            pullLetters sourceLetter sourceIndex v :=
          pullLetters_update_miss sourceLetter sourceIndex v none a (by intro j; simp)
        have ht (a : D) : pullLetters testLetter (@testIndex k l) (Function.update v none a) =
            pullLetters testLetter testIndex v :=
          pullLetters_update_miss testLetter testIndex v none a (by intro j; simp)
        simp only [invariantStageCoefficient, Function.update_self, hs, ht, map_add,
          endpointWord_add_endpoint, inner_add_left]
      | some i =>
        cases i with
        | inl i =>
          have hi : Function.Injective (@sourceIndex k l) := by intro a b h; simpa using h
          have hp (a : D) : pullLetters sourceLetter sourceIndex (Function.update v (sourceIndex i) a) =
              Function.update (pullLetters sourceLetter sourceIndex v) i (sourceLetter a) :=
            pullLetters_update sourceLetter sourceIndex hi v i a
          have hm (a : D) : pullLetters testLetter testIndex (Function.update v (sourceIndex i) a) =
              pullLetters testLetter testIndex v :=
            pullLetters_update_miss testLetter testIndex v (sourceIndex i) a (by intro j; simp)
          have hn (a : D) : Function.update v (sourceIndex i) a none = v none :=
            Function.update_of_ne (by simp) a v
          simp only [invariantStageCoefficient, hn, hp, hm, map_add,
            endpointWord_update_add, inner_add_right]
        | inr i =>
          have hi : Function.Injective (@testIndex k l) := by intro a b h; simpa using h
          have hp (a : D) : pullLetters testLetter testIndex (Function.update v (testIndex i) a) =
              Function.update (pullLetters testLetter testIndex v) i (testLetter a) :=
            pullLetters_update testLetter testIndex hi v i a
          have hm (a : D) : pullLetters sourceLetter sourceIndex (Function.update v (testIndex i) a) =
              pullLetters sourceLetter sourceIndex v :=
            pullLetters_update_miss sourceLetter sourceIndex v (testIndex i) a (by intro j; simp)
          have hn (a : D) : Function.update v (testIndex i) a none = v none :=
            Function.update_of_ne (by simp) a v
          simp only [invariantStageCoefficient, hn, hp, hm, map_add,
            endpointWord_update_add, inner_add_left])
    (by
      intro v i c a
      cases i with
      | none =>
        have hs (a : D) : pullLetters sourceLetter (@sourceIndex k l) (Function.update v none a) =
            pullLetters sourceLetter sourceIndex v :=
          pullLetters_update_miss sourceLetter sourceIndex v none a (by intro j; simp)
        have ht (a : D) : pullLetters testLetter (@testIndex k l) (Function.update v none a) =
            pullLetters testLetter testIndex v :=
          pullLetters_update_miss testLetter testIndex v none a (by intro j; simp)
        simp only [invariantStageCoefficient, Function.update_self, hs, ht, map_smulₛₗ,
          starRingEnd_apply, endpointWord_smul_endpoint, inner_smul_left, star_star, smul_eq_mul]
      | some i =>
        cases i with
        | inl i =>
          have hi : Function.Injective (@sourceIndex k l) := by intro a b h; simpa using h
          have hp (a : D) : pullLetters sourceLetter sourceIndex (Function.update v (sourceIndex i) a) =
              Function.update (pullLetters sourceLetter sourceIndex v) i (sourceLetter a) :=
            pullLetters_update sourceLetter sourceIndex hi v i a
          have hm (a : D) : pullLetters testLetter testIndex (Function.update v (sourceIndex i) a) =
              pullLetters testLetter testIndex v :=
            pullLetters_update_miss testLetter testIndex v (sourceIndex i) a (by intro j; simp)
          have hn (a : D) : Function.update v (sourceIndex i) a none = v none :=
            Function.update_of_ne (by simp) a v
          simp only [invariantStageCoefficient, hn, hp, hm, map_smulₛₗ, RingHom.id_apply,
            endpointWord_update_smul, inner_smul_right, smul_eq_mul]
        | inr i =>
          have hi : Function.Injective (@testIndex k l) := by intro a b h; simpa using h
          have hp (a : D) : pullLetters testLetter testIndex (Function.update v (testIndex i) a) =
              Function.update (pullLetters testLetter testIndex v) i (testLetter a) :=
            pullLetters_update testLetter testIndex hi v i a
          have hm (a : D) : pullLetters sourceLetter sourceIndex (Function.update v (testIndex i) a) =
              pullLetters sourceLetter sourceIndex v :=
            pullLetters_update_miss sourceLetter sourceIndex v (testIndex i) a (by intro j; simp)
          have hn (a : D) : Function.update v (testIndex i) a none = v none :=
            Function.update_of_ne (by simp) a v
          simp only [invariantStageCoefficient, hn, hp, hm, map_smulₛₗ,
            starRingEnd_apply, endpointWord_update_smul, inner_smul_left, star_star, smul_eq_mul])

@[simp] theorem invariantStageForm_apply
    (Y : EndpointTensor E F k →L[ℂ] EndpointTensor E F l) (Ω : E)
    (testEndpoint : D →ₗ⋆[ℂ] E) (sourceLetter : D →ₗ[ℂ] F)
    (testLetter : D →ₗ⋆[ℂ] F) (v : Option (Fin k ⊕ Fin l) → D) :
    invariantStageForm Y Ω testEndpoint sourceLetter testLetter v =
      inner ℂ (endpointWord (testEndpoint (v none)) (fun j => testLetter (v (some (Sum.inr j)))))
        (Y (endpointWord Ω (fun i => sourceLetter (v (some (Sum.inl i)))))) := rfl

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tensor_InvariantIntertwiners
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.UltrapowerBridge.instStarTracialQuotient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Matrix realization of the invariant-intertwiner argument

Finite coefficient forms are constructed from explicit Hilbert-space matrix
realizations. Normalized Hilbert--Schmidt inner products supply the matrix-unit
norms, while left matrix actions supply endpoint transfer. The sole invariant
theory input remains finite-dimensional Schur--Weyl spanning.
-/

noncomputable section
namespace KadisonSimilarity

variable {E F α : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [Fintype α] [DecidableEq α]

variable {k l : ℕ}

def MatrixHilbertStage.form
    (R : MatrixHilbertStage (E := E) (F := F) (α := α)) (J : F →ₗᵢ⋆[ℂ] F)
    (Ω : E) (Y : EndpointTensor E F k →L[ℂ] EndpointTensor E F l) :
    MultilinearMap ℂ (fun _ : Option (Fin k ⊕ Fin l) => Matrix α α ℂ) ℂ :=
  invariantStageForm Y Ω R.testEndpoint R.center (R.testLetter J)

omit [DecidableEq α] in
@[simp] theorem MatrixHilbertStage.form_apply
    (R : MatrixHilbertStage (E := E) (F := F) (α := α)) (J : F →ₗᵢ⋆[ℂ] F)
    (Ω : E) (Y : EndpointTensor E F k →L[ℂ] EndpointTensor E F l)
    (v : Option (Fin k ⊕ Fin l) → Matrix α α ℂ) :
    R.form J Ω Y v =
      inner ℂ (endpointWord (R.full (star (v none)))
        (fun j => J (R.center (v (some (Sum.inr j))))))
      (Y (endpointWord Ω (fun i => R.center (v (some (Sum.inl i)))))) := rfl

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_TracialMatrixRealization
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.UltrapowerBridge.instStarTracialQuotient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Matrix stages inside an actual tracial Hilbert representation

A trace-preserving matrix embedding supplies the normalized Hilbert--Schmidt
geometry, the corner left action, and the centered projection used by the
invariant-intertwiner argument. No invariant-theory conclusion is an input.
-/

noncomputable section
namespace KadisonSimilarity

variable {R E α : Type*} [Ring R] [StarRing R] [Algebra ℂ R]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [Fintype α] [DecidableEq α]

/-- The concrete normalized matrix stage associated to a trace-preserving
matrix star homomorphism and the left tracial representation. -/
def tracialMatrixStage
    (τ : R →ₗ[ℂ] ℂ) (V : R →ₗ[ℂ] E) (L : R →⋆ₐ[ℂ] (E →L[ℂ] E))
    (ι : Matrix α α ℂ →⋆ₐ[ℂ] R)
    (hinner : ∀ a b, inner ℂ (V a) (V b) = τ (star a * b))
    (hleft : ∀ a b, L a (V b) = V (a * b))
    (htrace : ∀ a, τ (ι a) = (Fintype.card α : ℂ)⁻¹ * Matrix.trace a) :
    MatrixHilbertStage (E := E) (F := centeredSubspace (V 1)) (α := α) where
  full := V.comp ι.toLinearMap
  center := (tracialCenter V).comp ι.toLinearMap
  left a := L (ι a)
  inner_full a b := by
    change inner ℂ (V (ι a)) (V (ι b)) = _
    rw [hinner, ← map_star, ← map_mul, htrace]
  norm_center_le a := norm_tracialCenter_le V (ι a)
  left_apply a b := by
    change L (ι a) (V (ι b)) = V (ι (a * b))
    rw [hleft, map_mul ι]
  left_adjoint a := by
    change star (L (ι a)) = L (ι (star a))
    rw [← map_star, ← map_star]

@[simp] theorem tracialMatrixStage_full
    (τ : R →ₗ[ℂ] ℂ) (V : R →ₗ[ℂ] E) (L : R →⋆ₐ[ℂ] (E →L[ℂ] E))
    (ι : Matrix α α ℂ →⋆ₐ[ℂ] R) (hinner : ∀ a b, inner ℂ (V a) (V b) = τ (star a * b))
    (hleft : ∀ a b, L a (V b) = V (a * b))
    (htrace : ∀ a, τ (ι a) = (Fintype.card α : ℂ)⁻¹ * Matrix.trace a) (a : Matrix α α ℂ) :
    (tracialMatrixStage τ V L ι hinner hleft htrace).full a = V (ι a) := rfl

@[simp] theorem tracialMatrixStage_unit
    (τ : R →ₗ[ℂ] ℂ) (V : R →ₗ[ℂ] E) (L : R →⋆ₐ[ℂ] (E →L[ℂ] E))
    (ι : Matrix α α ℂ →⋆ₐ[ℂ] R) (hinner : ∀ a b, inner ℂ (V a) (V b) = τ (star a * b))
    (hleft : ∀ a b, L a (V b) = V (a * b))
    (htrace : ∀ a, τ (ι a) = (Fintype.card α : ℂ)⁻¹ * Matrix.trace a) :
    (tracialMatrixStage τ V L ι hinner hleft htrace).full 1 = V 1 := by
  simp

section Conjugation

variable [StarModule ℂ R]

variable (τ : R →ₗ[ℂ] ℂ) (V : R →ₗ[ℂ] E)
  (hinner : ∀ a b, inner ℂ (V a) (V b) = τ (star a * b))
  (htrace : ∀ a b, τ (a * b) = τ (b * a))
  (hdense : DenseRange V)

@[simp] theorem tracialConjugation_apply_vector (a : R) :
    tracialConjugation τ V hinner htrace hdense (V a) = V (star a) := by
  exact LinearMap.extendOfIsometry_eq _ hdense
    (norm_tracial_star τ V hinner htrace) a

@[simp] theorem tracialConjugation_traceVector :
    tracialConjugation τ V hinner htrace hdense (V 1) = V 1 := by
  simp

/-- Tracial conjugation reverses the Hilbert inner product. -/
theorem inner_tracialConjugation (x y : E) :
    inner ℂ (tracialConjugation τ V hinner htrace hdense x)
      (tracialConjugation τ V hinner htrace hdense y) = inner ℂ y x := by
  refine hdense.induction_on₂ (isClosed_eq (by fun_prop) (by fun_prop)) ?_ x y
  intro a b
  simp only [tracialConjugation_apply_vector, hinner, star_star]
  exact htrace a (star b)

/-- The trace-vector orthogonal complement is stable under actual tracial
conjugation. -/
theorem tracialConjugation_mem_centered (x : centeredSubspace (V 1)) :
    tracialConjugation τ V hinner htrace hdense x ∈ centeredSubspace (V 1) := by
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
  calc
    inner ℂ (V 1) (tracialConjugation τ V hinner htrace hdense (x : E)) =
        inner ℂ (x : E) (V 1) := by
      simpa only [tracialConjugation_traceVector] using
        inner_tracialConjugation τ V hinner htrace hdense (V 1) (x : E)
    _ = 0 := Submodule.mem_orthogonal_singleton_iff_inner_left.mp x.property

/-- Tracial conjugation restricted to the centered Hilbert space. -/
def centeredTracialConjugation :
    centeredSubspace (V 1) →ₗᵢ⋆[ℂ] centeredSubspace (V 1) where
  toFun x := ⟨tracialConjugation τ V hinner htrace hdense x,
    tracialConjugation_mem_centered τ V hinner htrace hdense x⟩
  map_add' x y := by
    apply Subtype.ext
    exact map_add (tracialConjugation τ V hinner htrace hdense) (x : E) (y : E)
  map_smul' c x := by
    apply Subtype.ext
    exact (tracialConjugation τ V hinner htrace hdense).map_smulₛₗ c (x : E)
  norm_map' x := (tracialConjugation τ V hinner htrace hdense).norm_map x

@[simp] theorem coe_centeredTracialConjugation (x : centeredSubspace (V 1)) :
    (centeredTracialConjugation τ V hinner htrace hdense x : E) =
      tracialConjugation τ V hinner htrace hdense x := rfl

end Conjugation

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Derivation_TracialCornerCyclicity
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.UltrapowerBridge.instStarTracialQuotient
attribute [-simp] _root_.OAI.KadisonSimilarity.orbitAction_coe _root_.OAI.KadisonSimilarity.orbitRepresentation_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cyclicity of finite tracial corners from dense algebra vectors and
partial-isometry transport. No corner cyclicity or density is assumed. -/

noncomputable section
namespace KadisonSimilarity

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace TracialCornerGeometry

variable (G : TracialCornerGeometry P H)

def conjugation : H →ₗᵢ⋆[ℂ] H :=
  tracialConjugation G.trace G.vector G.inner_vector G.tracial G.dense_vector

@[simp] theorem conjugation_vector (a : P) : G.conjugation (G.vector a) = G.vector (star a) :=
  tracialConjugation_apply_vector G.trace G.vector G.inner_vector G.tracial G.dense_vector a

/-- Actual right multiplication, obtained from the tracial conjugation. -/
def right (b : P) : H →L[ℂ] H :=
  G.conjugation.toContinuousLinearMap.comp
    ((G.left (star b)).comp G.conjugation.toContinuousLinearMap)

@[simp] theorem right_vector (a b : P) : G.right b (G.vector a) = G.vector (a * b) := by
  change G.conjugation (G.left (star b) (G.conjugation (G.vector a))) = _
  rw [conjugation_vector, G.left_vector, conjugation_vector]
  simp only [star_mul, star_star]

theorem right_mul (a b : P) : G.right (a * b) = (G.right b).comp (G.right a) := by
  ext x
  refine G.dense_vector.induction_on x (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro c
  simp only [ContinuousLinearMap.comp_apply, right_vector, mul_assoc]

theorem right_mul_apply (a b : P) (x : H) :
    G.right (a * b) x = G.right b (G.right a x) :=
  congrArg (fun T : H →L[ℂ] H => T x) (G.right_mul a b)

theorem right_left (a b : P) : (G.right b).comp (G.left a) = (G.left a).comp (G.right b) := by
  ext x
  refine G.dense_vector.induction_on x (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro c
  simp only [ContinuousLinearMap.comp_apply, G.left_vector, right_vector, mul_assoc]

theorem right_adjoint (b : P) : (G.right b).adjoint = G.right (star b) := by
  have hinner (x y : H) : inner ℂ x (G.right (star b) y) = inner ℂ (G.right b x) y := by
    refine G.dense_vector.induction_on₂ (isClosed_eq (by fun_prop) (by fun_prop)) ?_ x y
    intro a c
    simp only [right_vector, G.inner_vector, star_mul]
    simpa only [mul_assoc] using (G.tracial (star b) (star a * c)).symm
  ext y
  apply ext_inner_left ℂ
  intro x
  rw [ContinuousLinearMap.adjoint_inner_right]
  exact (hinner x y).symm

/-- The actual Hilbert corner, defined by its two support equations. -/
def corner (e r : P) : ClosedSubmodule ℂ H where
  toSubmodule := (G.left e - ContinuousLinearMap.id ℂ H).ker ⊓
    (G.right r - ContinuousLinearMap.id ℂ H).ker
  isClosed' := (G.left e - ContinuousLinearMap.id ℂ H).isClosed_ker.inter
    (G.right r - ContinuousLinearMap.id ℂ H).isClosed_ker

@[simp] theorem mem_corner (e r : P) (x : H) :
    x ∈ G.corner e r ↔ G.left e x = x ∧ G.right r x = x := by
  simp only [corner, ClosedSubmodule.mem_mk, Submodule.mem_inf, LinearMap.mem_ker,
    ContinuousLinearMap.coe_coe, sub_apply, ContinuousLinearMap.id_apply, sub_eq_zero]

def cornerProjection (e r : P) : H →L[ℂ] H := (G.left e).comp (G.right r)

@[simp] theorem cornerProjection_vector (e r a : P) :
    G.cornerProjection e r (G.vector a) = G.vector (e * a * r) := by
  simp only [cornerProjection, ContinuousLinearMap.comp_apply, right_vector, G.left_vector,
    mul_assoc]

theorem cornerProjection_mem (e r : P) (he : IsIdempotentElem e) (hr : IsIdempotentElem r)
    (x : H) : G.cornerProjection e r x ∈ G.corner e r := by
  refine G.dense_vector.induction_on x ((G.corner e r).isClosed.preimage
    (G.cornerProjection e r).continuous) ?_
  intro a
  rw [cornerProjection_vector, mem_corner]
  constructor
  · rw [G.left_vector]
    congr 1
    calc
      e * (e * a * r) = (e * e) * a * r := by noncomm_ring
      _ = e * a * r := by rw [he.eq]
  · rw [right_vector]
    congr 1
    calc
      e * a * r * r = e * a * (r * r) := by noncomm_ring
      _ = e * a * r := by rw [hr.eq]

def cornerInto (e r : P) (he : IsIdempotentElem e) (hr : IsIdempotentElem r) :
    H →L[ℂ] G.corner e r :=
  (G.cornerProjection e r).codRestrict (G.corner e r).toSubmodule
    (G.cornerProjection_mem e r he hr)

@[simp] theorem cornerInto_coe (e r : P) (he : IsIdempotentElem e) (hr : IsIdempotentElem r)
    (x : H) : (G.cornerInto e r he hr x : H) = G.cornerProjection e r x := rfl

theorem right_transfer_mem (e r v : P) (hv : star v * v = r) (x : G.corner e r) :
    G.right (star v) x ∈ G.corner e (v * star v) := by
  rw [mem_corner]
  have hx := (G.mem_corner e r x).mp x.property
  constructor
  · have hc := congrArg (fun T : H →L[ℂ] H => T (x : H)) (G.right_left e (star v))
    simp only [ContinuousLinearMap.comp_apply] at hc
    rw [← hc, hx.1]
  · calc
      G.right (v * star v) (G.right (star v) x) =
          G.right (star v * (v * star v)) x := (G.right_mul_apply _ _ _).symm
      _ = G.right (r * star v) x := by rw [← mul_assoc, hv]
      _ = G.right (star v) (G.right r x) := G.right_mul_apply _ _ _
      _ = G.right (star v) x := by rw [hx.2]

theorem right_transfer_back_mem (e r v : P) (hv : star v * v = r)
    (x : G.corner e (v * star v)) : G.right v x ∈ G.corner e r := by
  rw [mem_corner]
  have hx := (G.mem_corner e (v * star v) x).mp x.property
  constructor
  · have hc := congrArg (fun T : H →L[ℂ] H => T (x : H)) (G.right_left e v)
    simp only [ContinuousLinearMap.comp_apply] at hc
    rw [← hc, hx.1]
  · calc
      G.right r (G.right v x) = G.right (v * r) x := (G.right_mul_apply _ _ _).symm
      _ = G.right ((v * star v) * v) x := by rw [← hv, mul_assoc]
      _ = G.right v (G.right (v * star v) x) := G.right_mul_apply _ _ _
      _ = G.right v x := by rw [hx.2]

def rightTransferMap (e r v : P) (hv : star v * v = r) :
    G.corner e r →L[ℂ] G.corner e (v * star v) :=
  ((G.right (star v)).comp (G.corner e r).toSubmodule.subtypeL).codRestrict
    (G.corner e (v * star v)).toSubmodule (G.right_transfer_mem e r v hv)

def rightTransferBack (e r v : P) (hv : star v * v = r) :
    G.corner e (v * star v) →L[ℂ] G.corner e r :=
  ((G.right v).comp (G.corner e (v * star v)).toSubmodule.subtypeL).codRestrict
    (G.corner e r).toSubmodule (G.right_transfer_back_mem e r v hv)

@[simp] theorem rightTransferMap_coe (e r v : P) (hv : star v * v = r) (x : G.corner e r) :
    (G.rightTransferMap e r v hv x : H) = G.right (star v) x := rfl

@[simp] theorem rightTransferBack_coe (e r v : P) (hv : star v * v = r)
    (x : G.corner e (v * star v)) :
    (G.rightTransferBack e r v hv x : H) = G.right v x := rfl

theorem rightTransfer_norm (e r v : P) (hv : star v * v = r) (x : G.corner e r) :
    ‖G.rightTransferMap e r v hv x‖ = ‖x‖ := by
  have hx := (G.mem_corner e r x).mp x.property
  have hi : inner ℂ (G.right (star v) x) (G.right (star v) x) = inner ℂ (x : H) x := by
    rw [← ContinuousLinearMap.adjoint_inner_right, G.right_adjoint, star_star,
      ← G.right_mul_apply, hv, hx.2]
  have hn : ‖G.rightTransferMap e r v hv x‖ ^ 2 = ‖x‖ ^ 2 := by
    change ‖G.right (star v) x‖ ^ 2 = ‖(x : H)‖ ^ 2
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), norm_sq_eq_re_inner (𝕜 := ℂ), hi]
  nlinarith [norm_nonneg (G.rightTransferMap e r v hv x), norm_nonneg x]

theorem rightTransfer_rightInverse (e r v : P) (hv : star v * v = r)
    (x : G.corner e (v * star v)) :
    G.rightTransferMap e r v hv (G.rightTransferBack e r v hv x) = x := by
  apply Subtype.ext
  change G.right (star v) (G.right v x) = x
  rw [← G.right_mul_apply]
  exact ((G.mem_corner e (v * star v) x).mp x.property).2

/-- Right multiplication by `v*` is the actual unitary from `eL²r` onto
`eL²(vv*)`; its inverse is right multiplication by `v`. -/
def rightTransfer (e r v : P) (hv : star v * v = r) :
    G.corner e r ≃ₗᵢ[ℂ] G.corner e (v * star v) :=
  LinearIsometryEquiv.ofSurjective
    { (G.rightTransferMap e r v hv).toLinearMap with norm_map' := G.rightTransfer_norm e r v hv }
    (fun x => ⟨G.rightTransferBack e r v hv x, G.rightTransfer_rightInverse e r v hv x⟩)

@[simp] theorem rightTransfer_coe (e r v : P) (hv : star v * v = r) (x : G.corner e r) :
    (G.rightTransfer e r v hv x : H) = G.right (star v) x := rfl

end TracialCornerGeometry

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_DihedralWordIsometries
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instRing
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normalized dihedral word inclusions on actual tracial Hilbert spaces. -/

noncomputable section
namespace KadisonSimilarity

variable {R : Type*} [Ring R] [Algebra ℂ R] [StarRing R] [StarModule ℂ R]
  {E K : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

variable (τ : R →ₗ[ℂ] ℂ) (hτ : τ 1 = 1)
  (htr : ∀ a b, τ (a * b) = τ (b * a))
  (V : R →ₗ[ℂ] E) (hinner : ∀ a b, inner ℂ (V a) (V b) = τ (star a * b))
  (P Q : StarSubalgebra ℂ R) (hf : ScalarFree τ P Q)
  (d s e : R) (hd : d ∈ P) (hs : s ∈ Q) (he : e ∈ P)
  (hd0 : τ d = 0) (hs0 : τ s = 0)
  (hdd : d * d = 1) (hss : s * s = 1)
  (hdstar : star d = d) (hsstar : star s = s)
  (hestar : star e = e) (hee : e * e = e)

variable (VA : Q →ₗ[ℂ] K)
  (hA : ∀ a b : Q, inner ℂ (VA a) (VA b) = τ (star (a : R) * (b : R)))
  (t : ℝ) (ht : 0 < t) (hte : τ e = (t : ℂ))

@[simp] theorem dihedralWordIsometry_apply (hdense : DenseRange VA) (k : ℕ) (a : Q) :
    dihedralWordIsometry τ hτ htr V hinner P Q hf d s e hd hs he hd0 hs0 hdd hss
      hdstar hsstar hestar hee VA hA t ht hte hdense k (VA a) =
      dihedralNormalization t • V (e * (s * d) ^ k * (a : R)) := by
  exact LinearMap.extendOfIsometry_eq _ hdense
    (norm_normalizedDihedralWordMap τ hτ htr V hinner P Q hf d s e hd hs he hd0 hs0 hdd hss
      hdstar hsstar hestar hee VA hA t ht hte k) a

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_ActualArcCompression
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The narrow-arc finite Fourier compression with actual normalized tracial
dihedral word inclusions. Their formulas and orthogonality are proved. -/

noncomputable section
namespace KadisonSimilarity

variable {R H K : Type*} [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

variable (τ : R →ₗ[ℂ] ℂ) (hτ : τ 1 = 1) (htr : ∀ a b, τ (a * b) = τ (b * a))
  (V : R →ₗ[ℂ] H) (hinner : ∀ a b, inner ℂ (V a) (V b) = τ (star a * b))
  (D A : StarSubalgebra ℂ R) (hf : ScalarFree τ D A)
  (d s : Rˣ) (e : R) (hd : (d : R) ∈ D) (hs : (s : R) ∈ A) (he : e ∈ D)
  (hd0 : τ (d : R) = 0) (hs0 : τ (s : R) = 0)
  (hdinv : d⁻¹ = d) (hsinv : s⁻¹ = s) (hdstar : star d = d) (hsstar : star s = s)
  (hestar : star e = e) (hee : e * e = e)
  (VA : A →ₗ[ℂ] K)
  (hA : ∀ a b : A, inner ℂ (VA a) (VA b) = τ (star (a : R) * (b : R)))
  (hv : DenseRange VA) (t : ℝ) (ht : 0 < t) (hte : τ e = (t : ℂ))

/-- Actual normalized word inclusion for the unit convention of the Fourier
calculation. -/
def actualDihedralInclusion (k : ℕ) : K →ₗᵢ[ℂ] H :=
  dihedralWordIsometry τ hτ htr V hinner D A hf (d : R) (s : R) e hd hs he hd0 hs0
    (involution_unit_val_mul_self d hdinv) (involution_unit_val_mul_self s hsinv)
    (involution_unit_val_star d hdstar) (involution_unit_val_star s hsstar)
    hestar hee VA hA t ht hte hv k

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tensor_MultiplicityClassification
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Hilbert multiplicities in the invariant-intertwiner theorem

Scalar matrix coefficients in the multiplicity Hilbert space are genuine
bounded endpoint intertwiners. Tensor totality reconstructs the full operator
from these slices. Repeated-letter compressions provide the bounded operator
on the multiplicity space used in propagation.
-/

noncomputable section
namespace KadisonSimilarity

open scoped TensorProduct

variable {G H K L : Type*}
  [NormedAddCommGroup G] [InnerProductSpace ℂ G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  [NormedAddCommGroup L] [InnerProductSpace ℂ L]

/-- Insert the first tensor coordinate in a completed Hilbert tensor product. -/
def hilbertTensorInsert (a : G) : H →L[ℂ] HilbertTensor G H :=
  UniformSpace.Completion.toComplL.comp (TensorProduct.mkL ℂ G H a)

@[simp] theorem hilbertTensorInsert_apply (a : G) (x : H) :
    hilbertTensorInsert a x = (a ⊗ₜ[ℂ] x : G ⊗[ℂ] H) := rfl

@[simp] theorem norm_hilbertTensorInsert (a : G) (x : H) :
    ‖hilbertTensorInsert a x‖ = ‖a‖ * ‖x‖ := by
  exact (UniformSpace.Completion.norm_coe (a ⊗ₜ[ℂ] x)).trans
    (TensorProduct.norm_tmul a x)

@[simp] theorem inner_hilbertTensorInsert (a b : G) (x y : H) :
    inner ℂ (hilbertTensorInsert a x) (hilbertTensorInsert b y) =
      inner ℂ a b * inner ℂ x y := by
  exact (UniformSpace.Completion.inner_coe (a ⊗ₜ[ℂ] x) (b ⊗ₜ[ℂ] y)).trans
    (TensorProduct.inner_tmul ℂ a b x y)

/-- Totality of completed elementary Hilbert tensors. -/
theorem continuousLinearMap_ext_hilbertTensorInsert
    (f g : HilbertTensor G H →L[ℂ] L)
    (h : ∀ a x, f (hilbertTensorInsert a x) = g (hilbertTensorInsert a x)) : f = g := by
  apply ContinuousLinearMap.ext
  intro z
  induction z using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq f.continuous g.continuous
  | ih z =>
    induction z using OAI.tensorInductionOn with
    | tmul a x => exact h a x
    | add x y hx hy =>
      change f ((x + y : G ⊗[ℂ] H) : HilbertTensor G H) =
        g ((x + y : G ⊗[ℂ] H) : HilbertTensor G H)
      calc
        _ = f (x : HilbertTensor G H) + f (y : HilbertTensor G H) :=
          (congrArg f (hilbertTensor_coe_add x y)).trans (f.map_add _ _)
        _ = g (x : HilbertTensor G H) + g (y : HilbertTensor G H) :=
          congrArg₂ (· + ·) hx hy
        _ = _ := ((congrArg g (hilbertTensor_coe_add x y)).trans (g.map_add _ _)).symm

/-- The lift of an operator leaving the first tensor coordinate unchanged. -/
def hilbertTensorLift (T : H →L[ℂ] K) : HilbertTensor G H →L[ℂ] HilbertTensor G K :=
  (TensorProduct.mapL (ContinuousLinearMap.id ℂ G) T).completion

@[simp] theorem hilbertTensorLift_insert (T : H →L[ℂ] K) (a : G) (x : H) :
    hilbertTensorLift T (hilbertTensorInsert a x) = hilbertTensorInsert a (T x) := by
  change (TensorProduct.mapL (ContinuousLinearMap.id ℂ G) T).completion
      ((a ⊗ₜ[ℂ] x : G ⊗[ℂ] H) : UniformSpace.Completion (G ⊗[ℂ] H)) =
    ((a ⊗ₜ[ℂ] T x : G ⊗[ℂ] K) : UniformSpace.Completion (G ⊗[ℂ] K))
  simp only [ContinuousLinearMap.completion_apply_coe, TensorProduct.mapL_tmul,
    ContinuousLinearMap.id_apply]

variable [CompleteSpace H] [CompleteSpace K]

@[simp] theorem tensorSlice_insert (a b : G) (x : H) :
    tensorSlice b (hilbertTensorInsert a x) = inner ℂ b a • x := by
  simp only [hilbertTensorInsert_apply, tensorSlice_coe, algebraTensorSlice_tmul]

/-- A scalar matrix coefficient in the multiplicity space. -/
def multiplicitySlice (Y : HilbertTensor G H →L[ℂ] HilbertTensor G K) (a b : G) : H →L[ℂ] K :=
  (tensorSlice b).comp (Y.comp (hilbertTensorInsert a))

omit [CompleteSpace H] in
@[simp] theorem multiplicitySlice_zero (a b : G) :
    multiplicitySlice (0 : HilbertTensor G H →L[ℂ] HilbertTensor G K) a b = 0 := by
  ext x
  simp [multiplicitySlice]

/-- Insert a fixed second tensor vector, leaving the multiplicity variable free. -/
def hilbertTensorRightInsert (w : H) : G →L[ℂ] HilbertTensor G H :=
  UniformSpace.Completion.toComplL.comp ((TensorProduct.mkL ℂ G H).flip w)

omit [CompleteSpace H] in
@[simp] theorem hilbertTensorRightInsert_apply (w : H) (a : G) :
    hilbertTensorRightInsert w a = hilbertTensorInsert a w := rfl

variable [CompleteSpace G]

section EndpointMultiplicity

universe u
variable {E F : Type u}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

omit [CompleteSpace E] in
/-- A unit endpoint and unit repeated letter give a unit vector at every level. -/
theorem norm_endpointWord_constant {n : ℕ} (Ω : E) (r : F)
    (hΩ : ‖Ω‖ = 1) (hr : ‖r‖ = 1) :
    ‖endpointWord Ω (fun _ : Fin n => r)‖ = 1 := by
  simp only [endpointWord, norm_endpointInsert, norm_completedTensorWord, hΩ, hr,
    Finset.prod_const_one, mul_one]

end EndpointMultiplicity

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_WordMultiplicities
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual multiplicity spaces of the alternating tracial words, their
normalized repeated-letter inclusions, and the degree-zero identification. -/

noncomputable section
namespace KadisonSimilarity

universe u
variable {B : Type u} [NormedAddCommGroup B] [InnerProductSpace ℂ B]

/-- The multiplicity of words with `k` centered base-algebra letters. -/
abbrev WordMultiplicity (ΩA : B) (k : ℕ) :=
  HilbertTensor (CompletedTensorWord (centeredSubspace ΩA) k) B

/-- A unit vector in the centered tensor power inserts the base Hilbert space
isometrically into the corresponding multiplicity space. -/
def multiplicityWordInclusion (ΩA : B) {k : ℕ}
    (w : CompletedTensorWord (centeredSubspace ΩA) k) (hw : ‖w‖ = 1) :
    B →ₗᵢ[ℂ] WordMultiplicity ΩA k where
  toLinearMap := (hilbertTensorInsert w).toLinearMap
  norm_map' b := by
    change ‖hilbertTensorInsert w b‖ = ‖b‖
    rw [norm_hilbertTensorInsert, hw, one_mul]

@[simp] theorem multiplicityWordInclusion_apply (ΩA : B) {k : ℕ}
    (w : CompletedTensorWord (centeredSubspace ΩA) k) (hw : ‖w‖ = 1) (b : B) :
    multiplicityWordInclusion ΩA w hw b = hilbertTensorInsert w b := rfl

/-- The repeated centered word `s ⊗ ⋯ ⊗ s`. -/
def repeatedMultiplicityWord (ΩA : B) (s : centeredSubspace ΩA) (k : ℕ) :
    CompletedTensorWord (centeredSubspace ΩA) k :=
  completedTensorWord (fun _ : Fin k => s)

@[simp] theorem norm_repeatedMultiplicityWord (ΩA : B) (s : centeredSubspace ΩA)
    (hs : ‖s‖ = 1) (k : ℕ) : ‖repeatedMultiplicityWord ΩA s k‖ = 1 := by
  simp only [repeatedMultiplicityWord, norm_completedTensorWord, hs, Finset.prod_const_one]

/-- Insertion of a normalized repeated centered letter, with its exact norm. -/
def repeatedMultiplicityInclusion (ΩA : B) (s : centeredSubspace ΩA)
    (hs : ‖s‖ = 1) (k : ℕ) : B →ₗᵢ[ℂ] WordMultiplicity ΩA k :=
  multiplicityWordInclusion ΩA (repeatedMultiplicityWord ΩA s k)
    (norm_repeatedMultiplicityWord ΩA s hs k)

@[simp] theorem repeatedMultiplicityInclusion_apply (ΩA : B) (s : centeredSubspace ΩA)
    (hs : ‖s‖ = 1) (k : ℕ) (b : B) :
    repeatedMultiplicityInclusion ΩA s hs k b =
      hilbertTensorInsert (completedTensorWord (fun _ : Fin k => s)) b := rfl

/-- The empty centered word is the scalar unit in tensor degree zero. -/
def zeroMultiplicityWord (ΩA : B) : CompletedTensorWord (centeredSubspace ΩA) 0 :=
  completedTensorWord (Fin.elim0 : Fin 0 → centeredSubspace ΩA)

@[simp] theorem norm_zeroMultiplicityWord (ΩA : B) : ‖zeroMultiplicityWord ΩA‖ = 1 := by
  simp only [zeroMultiplicityWord, norm_completedTensorWord, Fin.prod_univ_zero]

/-- The canonical degree-zero inclusion of the base Hilbert space. -/
def zeroMultiplicityInclusion (ΩA : B) : B →ₗᵢ[ℂ] WordMultiplicity ΩA 0 :=
  multiplicityWordInclusion ΩA (zeroMultiplicityWord ΩA) (norm_zeroMultiplicityWord ΩA)

@[simp] theorem zeroMultiplicityInclusion_apply (ΩA : B) (b : B) :
    zeroMultiplicityInclusion ΩA b = hilbertTensorInsert (zeroMultiplicityWord ΩA) b := rfl

variable [CompleteSpace B]

/-- In degree zero the slice recovers every tensor, as proved from totality
of the completed empty word and of elementary Hilbert tensors. -/
theorem zeroMultiplicity_slice_inverse (ΩA : B) :
    (zeroMultiplicityInclusion ΩA).toContinuousLinearMap.comp
      (tensorSlice (zeroMultiplicityWord ΩA)) =
        ContinuousLinearMap.id ℂ (WordMultiplicity ΩA 0) := by
  apply continuousLinearMap_ext_hilbertTensorInsert
  intro w b
  have hword :
      ((zeroMultiplicityInclusion ΩA).toContinuousLinearMap.comp
        (tensorSlice (zeroMultiplicityWord ΩA))).comp (hilbertTensorRightInsert b) =
          hilbertTensorRightInsert b := by
    apply continuousLinearMap_ext_completedTensorWords
    intro x
    have hx : completedTensorWord x = zeroMultiplicityWord ΩA := by
      congr 1
      funext i
      exact Fin.elim0 i
    change zeroMultiplicityInclusion ΩA
      (tensorSlice (zeroMultiplicityWord ΩA) (hilbertTensorInsert (completedTensorWord x) b)) =
        hilbertTensorInsert (completedTensorWord x) b
    rw [hx, tensorSlice_insert]
    have hunit : inner ℂ (zeroMultiplicityWord ΩA) (zeroMultiplicityWord ΩA) = 1 := by
      rw [inner_self_eq_norm_sq_to_K, norm_zeroMultiplicityWord]
      norm_num
    rw [hunit, one_smul, zeroMultiplicityInclusion_apply]
  exact congrArg (fun T : CompletedTensorWord (centeredSubspace ΩA) 0 →L[ℂ]
    WordMultiplicity ΩA 0 => T w) hword

/-- No extra scalar tensor factor remains at word degree zero. -/
theorem zeroMultiplicityInclusion_surjective (ΩA : B) :
    Function.Surjective (zeroMultiplicityInclusion ΩA) := by
  intro z
  refine ⟨tensorSlice (zeroMultiplicityWord ΩA) z, ?_⟩
  exact congrArg (fun T : WordMultiplicity ΩA 0 →L[ℂ] WordMultiplicity ΩA 0 => T z)
    (zeroMultiplicity_slice_inverse ΩA)

/-- The actual unitary identification of the base space with multiplicity zero. -/
def zeroMultiplicityEquiv (ΩA : B) : B ≃ₗᵢ[ℂ] WordMultiplicity ΩA 0 :=
  LinearIsometryEquiv.ofSurjective (zeroMultiplicityInclusion ΩA)
    (zeroMultiplicityInclusion_surjective ΩA)

@[simp] theorem zeroMultiplicityEquiv_apply (ΩA : B) (b : B) :
    zeroMultiplicityEquiv ΩA b = hilbertTensorInsert (zeroMultiplicityWord ΩA) b := rfl

/-- Transport the canonical degree-zero block to an operator on the base space. -/
def zeroMultiplicityOperator (ΩA : B) (T : WordMultiplicity ΩA 0 →L[ℂ] WordMultiplicity ΩA 0) :
    B →L[ℂ] B :=
  (zeroMultiplicityEquiv ΩA).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (T.comp (zeroMultiplicityEquiv ΩA).toContinuousLinearEquiv.toContinuousLinearMap)

@[simp] theorem zeroMultiplicityOperator_intertwines (ΩA : B)
    (T : WordMultiplicity ΩA 0 →L[ℂ] WordMultiplicity ΩA 0) (b : B) :
    zeroMultiplicityEquiv ΩA (zeroMultiplicityOperator ΩA T b) =
      T (zeroMultiplicityEquiv ΩA b) := by
  change zeroMultiplicityEquiv ΩA ((zeroMultiplicityEquiv ΩA).symm _) = _
  exact (zeroMultiplicityEquiv ΩA).apply_symm_apply _

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_TracialBaseSpace
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.tupleOrbitClosure_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.UltrapowerBridge.instStarTracialQuotient
attribute [-simp] _root_.OAI.KadisonSimilarity.orbitAction_coe _root_.OAI.KadisonSimilarity.orbitRepresentation_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The completed base Hilbert space of a represented tracial star algebra,
its actual inclusion, and compression of the ambient left action. -/

noncomputable section
namespace KadisonSimilarity

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace TracialCornerGeometry

variable (G : TracialCornerGeometry P H) (A : StarSubalgebra ℂ P)

/-- The algebraic vectors coming from the specified star subalgebra. -/
def baseAlgebraVectors : A →ₗ[ℂ] H := G.vector.comp A.subtype.toLinearMap

@[simp] theorem baseAlgebraVectors_apply (a : A) :
    G.baseAlgebraVectors A a = G.vector (a : P) := rfl

/-- The actual closed base subspace, with no independent density input. -/
def baseSpace : ClosedSubmodule ℂ H := (G.baseAlgebraVectors A).range.closure

instance baseSpace_complete : CompleteSpace (G.baseSpace A).toSubmodule :=
  (G.baseSpace A).isClosed.completeSpace_coe

/-- The dense algebra-vector map into its Hilbert completion. -/
def baseVector : A →ₗ[ℂ] G.baseSpace A :=
  (G.baseAlgebraVectors A).codRestrict (G.baseSpace A).toSubmodule fun a =>
    (G.baseAlgebraVectors A).range.le_topologicalClosure ⟨a, rfl⟩

@[simp] theorem baseVector_coe (a : A) :
    (G.baseVector A a : H) = G.vector (a : P) := rfl

theorem baseVector_dense : DenseRange (G.baseVector A) := by
  change Dense (Set.range (G.baseVector A))
  rw [Subtype.dense_iff, ← Set.range_comp]
  change closure (Set.range (G.baseAlgebraVectors A)) ⊆
    closure (Set.range (G.baseAlgebraVectors A))
  exact Set.Subset.rfl

/-- The canonical isometry from the completed base into the ambient space. -/
def baseInclusion : G.baseSpace A →ₗᵢ[ℂ] H := (G.baseSpace A).toSubmodule.subtypeₗᵢ

@[simp] theorem baseInclusion_apply (x : G.baseSpace A) : G.baseInclusion A x = (x : H) := rfl

@[simp] theorem baseInclusion_vector (a : A) :
    G.baseInclusion A (G.baseVector A a) = G.vector (a : P) := rfl

/-- Compression of an ambient bounded operator to the completed base. -/
def baseOperator (Y : H →L[ℂ] H) : G.baseSpace A →L[ℂ] G.baseSpace A :=
  (G.baseInclusion A).toContinuousLinearMap.adjoint.comp
    (Y.comp (G.baseInclusion A).toContinuousLinearMap)

@[simp] theorem baseOperator_adjoint (Y : H →L[ℂ] H) :
    (G.baseOperator A Y).adjoint = G.baseOperator A Y.adjoint := by
  simp only [baseOperator, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint, ContinuousLinearMap.comp_assoc]

/-- The actual compressed left action on arbitrary ambient algebra elements. -/
def baseCompression : P →ₗ[ℂ] (G.baseSpace A →L[ℂ] G.baseSpace A) where
  toFun x := G.baseOperator A (G.left x)
  map_add' x y := by
    simp only [map_add, baseOperator, ContinuousLinearMap.add_comp,
      ContinuousLinearMap.comp_add]
  map_smul' c x := by
    simp only [map_smul, baseOperator, ContinuousLinearMap.smul_comp,
      ContinuousLinearMap.comp_smul, RingHom.id_apply]

@[simp] theorem baseCompression_apply (x : P) :
    G.baseCompression A x = G.baseOperator A (G.left x) := rfl

/-- The base Hilbert inner product is the original tracial one. -/
theorem baseVector_inner (a b : A) :
    inner ℂ (G.baseVector A a) (G.baseVector A b) =
      G.trace (star (a : P) * (b : P)) := G.inner_vector _ _

/-- Left multiplication by the subalgebra preserves the completed base. -/
theorem baseSpace_invariant (a : A) (x : H) (hx : x ∈ G.baseSpace A) :
    G.left (a : P) x ∈ G.baseSpace A := by
  have hm : Set.MapsTo (G.left (a : P))
      ((G.baseAlgebraVectors A).range : Set H) ((G.baseAlgebraVectors A).range : Set H) := by
    rintro y ⟨b, rfl⟩
    refine ⟨a * b, ?_⟩
    change G.vector ((a : P) * (b : P)) = G.left (a : P) (G.vector (b : P))
    rw [G.left_vector]
  exact hm.closure (G.left (a : P)).continuous hx

def baseAction (a : A) : G.baseSpace A →L[ℂ] G.baseSpace A :=
  (G.left (a : P)).restrict (G.baseSpace_invariant A a)

@[simp] theorem baseAction_coe (a : A) (x : G.baseSpace A) :
    (G.baseAction A a x : H) = G.left (a : P) (x : H) := rfl

/-- The restriction to the star subalgebra is a genuine unital star
representation on the completed base space. -/
def baseRepresentation : A →⋆ₐ[ℂ] (G.baseSpace A →L[ℂ] G.baseSpace A) where
  toFun := G.baseAction A
  map_zero' := by ext x; simp
  map_one' := by ext x; simp
  map_add' a b := by ext x; simp
  map_mul' a b := by ext x; simp [mul_apply_eq_comp]
  commutes' c := by ext x; simp [Algebra.algebraMap_eq_smul_one]
  map_star' a := by
    apply ContinuousLinearMap.ext
    intro x
    apply ext_inner_left ℂ
    intro y
    change inner ℂ (y : H) (G.left (star (a : P)) (x : H)) =
      inner ℂ y ((G.baseAction A a).adjoint x)
    rw [ContinuousLinearMap.adjoint_inner_right]
    change inner ℂ (y : H) (G.left (star (a : P)) (x : H)) =
      inner ℂ (G.left (a : P) (y : H)) (x : H)
    rw [map_star]
    exact ContinuousLinearMap.adjoint_inner_right _ _ _

@[simp] theorem baseRepresentation_coe (a : A) (x : G.baseSpace A) :
    (G.baseRepresentation A a x : H) = G.left (a : P) (x : H) := rfl

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_TracialBaseGeometry
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.tupleOrbitClosure_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.UltrapowerBridge.instStarTracialQuotient
attribute [-simp] _root_.OAI.KadisonSimilarity.orbitAction_coe _root_.OAI.KadisonSimilarity.orbitRepresentation_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The closed base algebra has its actual tracial Hilbert representation
inside the ambient one. Its left, right, and conjugation actions are compatible
with the canonical base inclusion. -/

noncomputable section
namespace KadisonSimilarity

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace TracialCornerGeometry

variable (G : TracialCornerGeometry P H) (A : StarSubalgebra ℂ P)

variable [IsClosed (A : Set P)]

/-- Restrict the trace and left action to the closed base algebra; the Hilbert
space is the closure of its actual ambient algebra vectors. -/
def baseGeometry : TracialCornerGeometry A (G.baseSpace A) where
  trace := G.trace.comp A.subtype.toLinearMap
  vector := G.baseVector A
  left := G.baseRepresentation A
  inner_vector a b := G.baseVector_inner A a b
  tracial a b := G.tracial (a : P) (b : P)
  dense_vector := G.baseVector_dense A
  left_vector a b := by
    apply Subtype.ext
    change G.left (a : P) (G.vector (b : P)) = G.vector ((a : P) * (b : P))
    exact G.left_vector (a : P) (b : P)

@[simp] theorem baseGeometry_trace (a : A) :
    (G.baseGeometry A).trace a = G.trace (a : P) := rfl

@[simp] theorem baseGeometry_vector_coe (a : A) :
    ((G.baseGeometry A).vector a : H) = G.vector (a : P) := rfl

@[simp] theorem baseGeometry_left_coe (a : A) (x : G.baseSpace A) :
    ((G.baseGeometry A).left a x : H) = G.left (a : P) (x : H) := rfl

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_BaseSymmetry
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.tupleOrbitClosure_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing
attribute [-simp] _root_.OAI.KadisonSimilarity.orbitAction_coe _root_.OAI.KadisonSimilarity.orbitRepresentation_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A trace-zero symmetry of the actual base algebra supplies the normalized
centered letter and its represented selfadjoint involution. -/

noncomputable section
namespace KadisonSimilarity

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace TracialCornerGeometry

variable (G : TracialCornerGeometry P H) (A : StarSubalgebra ℂ P)
  [IsClosed (A : Set P)]

/-- A trace-zero base element is an actual centered base Hilbert vector. -/
def baseSymmetryLetter (s : A) (hzero : G.trace (s : P) = 0) :
    centeredSubspace (G.baseVector A 1) :=
  ⟨G.baseVector A s,
    tracial_vector_mem_centered (G.baseGeometry A).trace (G.baseGeometry A).vector
      (G.baseGeometry A).inner_vector s hzero⟩

@[simp] theorem baseSymmetryLetter_coe (s : A) (hzero : G.trace (s : P) = 0) :
    (G.baseSymmetryLetter A s hzero : G.baseSpace A) = G.baseVector A s := rfl

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_WordLevelClassification
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero
attribute [-simp] _root_.OAI.KadisonSimilarity.multiplicityWordInclusion_apply _root_.OAI.KadisonSimilarity.repeatedMultiplicityInclusion_apply _root_.OAI.KadisonSimilarity.zeroMultiplicityEquiv_apply _root_.OAI.KadisonSimilarity.zeroMultiplicityInclusion_apply _root_.OAI.KadisonSimilarity.zeroMultiplicityOperator_intertwines
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Different multiplicities and the orthogonal word-level decomposition

Source and target word levels have independent Hilbert multiplicity spaces.
Their scalar slices are bounded endpoint intertwiners, so unequal degrees
vanish by the completed endpoint classification.
-/

noncomputable section
namespace KadisonSimilarity

open scoped TensorProduct

variable {Gsource Gtarget H K : Type*}
  [NormedAddCommGroup Gsource] [InnerProductSpace ℂ Gsource]
  [NormedAddCommGroup Gtarget] [InnerProductSpace ℂ Gtarget]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- A bounded scalar multiplicity slice with independently typed source and
target multiplicities. -/
def crossMultiplicitySlice
    (Y : HilbertTensor Gsource H →L[ℂ] HilbertTensor Gtarget K)
    (a : Gsource) (b : Gtarget) : H →L[ℂ] K :=
  (tensorSlice b).comp (Y.comp (hilbertTensorInsert a))

@[simp] theorem crossMultiplicitySlice_zero (a : Gsource) (b : Gtarget) :
    crossMultiplicitySlice (0 : HilbertTensor Gsource H →L[ℂ] HilbertTensor Gtarget K) a b = 0 := by
  ext x
  simp [crossMultiplicitySlice]

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_OrthogonalWordLevels
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Orthogonal word-level inclusions turn the proved off-diagonal block
vanishing into actual preservation of each full word level. -/

noncomputable section
namespace KadisonSimilarity

variable {W : ℕ → Type*} [∀ n, NormedAddCommGroup (W n)]
  [∀ n, InnerProductSpace ℂ (W n)] [∀ n, CompleteSpace (W n)]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

section MatrixActions

universe u
variable {E F : Type u}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  {G : ℕ → Type*} [∀ n, NormedAddCommGroup (G n)] [∀ n, InnerProductSpace ℂ (G n)]
  {A : ℕ → Type*} [∀ s, Fintype (A s)] [∀ s, DecidableEq (A s)]
  [∀ s, Nonempty (A s)]

/-- The actual space of one word level, including its degree-dependent
multiplicity. -/
abbrev MultiplicityWordSpace (G : ℕ → Type*) [∀ n, NormedAddCommGroup (G n)]
    [∀ n, InnerProductSpace ℂ (G n)] (E F : Type u)
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] (n : ℕ) :=
  HilbertTensor (G n) (EndpointTensor E F n)

end MatrixActions

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_WordBaseCoordinates
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero
attribute [-simp] _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSymmetryLetter_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Identify the degree-zero multiplicity operator with the actual compression
to the base algebra's tracial Hilbert space. -/

noncomputable section
namespace KadisonSimilarity

universe u
variable {E F : Type u} {B H : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup B] [InnerProductSpace ℂ B] [CompleteSpace B]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The first endpoint with no centered tail letters. -/
def emptyEndpoint (Ω : E) : EndpointTensor E F 0 :=
  endpointWord Ω (Fin.elim0 : Fin 0 → F)

@[simp] theorem norm_emptyEndpoint (Ω : E) : ‖emptyEndpoint (F := F) Ω‖ = ‖Ω‖ := by
  change ‖endpointInsert Ω (completedTensorWord (Fin.elim0 : Fin 0 → F))‖ = ‖Ω‖
  simp only [norm_endpointInsert, norm_completedTensorWord, Fin.prod_univ_zero, mul_one]

variable (ΩA : B)
  (U : OrthogonalWordLevels (MultiplicityWordSpace (WordMultiplicity ΩA) E F) H)
  (ΩD : E) (hΩD : ‖ΩD‖ = 1)

/-- The base Hilbert space embeds as the scalar first endpoint in degree zero. -/
def baseWordInclusion : B →ₗᵢ[ℂ] H where
  toLinearMap := (U.inclusion 0).toLinearMap.comp
    ((hilbertTensorRightInsert (emptyEndpoint (F := F) ΩD)).toLinearMap.comp
      (zeroMultiplicityEquiv ΩA).toLinearMap)
  norm_map' b := by
    change ‖U.inclusion 0 (hilbertTensorInsert (zeroMultiplicityEquiv ΩA b)
      (emptyEndpoint (F := F) ΩD))‖ = ‖b‖
    rw [LinearIsometry.norm_map, norm_hilbertTensorInsert,
      LinearIsometryEquiv.norm_map, norm_emptyEndpoint, hΩD, mul_one]

omit [CompleteSpace H] in
@[simp] theorem baseWordInclusion_apply (b : B) :
    baseWordInclusion ΩA U ΩD hΩD b =
      U.inclusion 0 (hilbertTensorInsert (zeroMultiplicityEquiv ΩA b)
        (emptyEndpoint (F := F) ΩD)) := rfl

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_ReducedWordModel
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The reduced-word part of the published free-product construction.

Ricard–Xu, J. reine angew. Math. 599 (2006), Section 1, pp. 2–3 of
arXiv:math/0505302, constructs the reduced free-product Hilbert space as the
orthogonal sum of alternating centered tensor words. Regrouping the first
and last factors gives the coordinates below. The input is only this word
construction, without any operator invariance or commutator estimate. -/

noncomputable section
namespace KadisonSimilarity

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (G : TracialCornerGeometry P H) (A D : StarSubalgebra ℂ P)
  [IsClosed (A : Set P)] [IsClosed (D : Set P)]

/-- The actual alternating vectors whose span is dense in a reduced product. -/
def reducedWordVectors : Set H := {x | ∃ (n : ℕ) (d : D) (b : A)
    (a : Fin n → A) (c : Fin n → D),
    (∀ i, G.trace (a i : P) = 0) ∧ (∀ i, G.trace (c i : P) = 0) ∧
      x = G.vector ((d : P) * alternatingProduct (fun i => (a i : P))
        (fun i => (c i : P)) * (b : P))}

/-- Being generated in the tracial Hilbert space is a density hypothesis,
not an operator conclusion. -/
def ReducedWordGenerated : Prop :=
  (Submodule.span ℂ (reducedWordVectors G A D)).topologicalClosure = ⊤

/-- The base-algebra part of an elementary word. -/
def tracialMultiplicityWord (n : ℕ) (b : A) (a : Fin n → A)
    (ha : ∀ i, G.trace (a i : P) = 0) : WordMultiplicity (G.baseVector A 1) n :=
  hilbertTensorInsert (completedTensorWord (fun i => G.baseSymmetryLetter A (a i) (ha i)))
    (G.baseVector A b)

/-- The other-factor endpoint and centered internal letters. -/
def tracialEndpointWord (n : ℕ) (d : D) (c : Fin n → D)
    (hc : ∀ i, G.trace (c i : P) = 0) :
    EndpointTensor (G.baseSpace D) (centeredSubspace (G.baseVector D 1)) n :=
  endpointWord (G.baseVector D d) (fun i => G.baseSymmetryLetter D (c i) (hc i))

/-- The tensor product of the base-word and endpoint factors. -/
def tracialWordTensor (n : ℕ) (d : D) (b : A) (a : Fin n → A) (c : Fin n → D)
    (ha : ∀ i, G.trace (a i : P) = 0) (hc : ∀ i, G.trace (c i : P) = 0) :
    MultiplicityWordSpace (WordMultiplicity (G.baseVector A 1)) (G.baseSpace D)
      (centeredSubspace (G.baseVector D 1)) n :=
  hilbertTensorInsert (tracialMultiplicityWord G A n b a ha) (tracialEndpointWord G D n d c hc)

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_WordPropagationTransfer
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing
attribute [-simp] _root_.OAI.KadisonSimilarity.baseWordInclusion_apply _root_.OAI.KadisonSimilarity.multiplicityWordInclusion_apply _root_.OAI.KadisonSimilarity.norm_emptyEndpoint _root_.OAI.KadisonSimilarity.norm_repeatedMultiplicityWord _root_.OAI.KadisonSimilarity.norm_zeroMultiplicityWord _root_.OAI.KadisonSimilarity.repeatedMultiplicityInclusion_apply _root_.OAI.KadisonSimilarity.zeroMultiplicityEquiv_apply _root_.OAI.KadisonSimilarity.zeroMultiplicityInclusion_apply _root_.OAI.KadisonSimilarity.zeroMultiplicityOperator_intertwines
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transfer the multiplicity propagation estimate to the actual orthogonal
word columns used by the finite Fourier test. -/

noncomputable section
namespace KadisonSimilarity

universe u
variable {E F : Type u} {K H : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {J : ℕ → Type*} [∀ n, NormedAddCommGroup (J n)]
  [∀ n, InnerProductSpace ℂ (J n)] [∀ n, CompleteSpace (J n)]

variable (U : OrthogonalWordLevels (MultiplicityWordSpace J E F) H)

/-- The concrete column at a fixed word degree, endpoint, and repeated letter. -/
def repeatedWordInclusion (n : ℕ) (R : K →ₗᵢ[ℂ] J n)
    (d : E) (r : F) (hd : ‖d‖ = 1) (hr : ‖r‖ = 1) : K →ₗᵢ[ℂ] H where
  toLinearMap := (U.inclusion n).toLinearMap.comp
    ((hilbertTensorRightInsert (endpointWord d (fun _ : Fin n => r))).toLinearMap.comp
      R.toLinearMap)
  norm_map' x := by
    change ‖U.inclusion n (hilbertTensorInsert (R x)
      (endpointWord d (fun _ : Fin n => r)))‖ = ‖x‖
    rw [LinearIsometry.norm_map, norm_hilbertTensorInsert, LinearIsometry.norm_map,
      norm_endpointWord_constant d r hd hr, mul_one]

omit [CompleteSpace H] [CompleteSpace K] [∀ n, CompleteSpace (J n)] in
@[simp] theorem repeatedWordInclusion_apply (n : ℕ) (R : K →ₗᵢ[ℂ] J n)
    (d : E) (r : F) (hd : ‖d‖ = 1) (hr : ‖r‖ = 1) (x : K) :
    repeatedWordInclusion U n R d r hd hr x = U.inclusion n
      (hilbertTensorInsert (R x) (endpointWord d (fun _ : Fin n => r))) := rfl

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_TracialDihedralColumns
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.UltrapowerBridge.instStarTracialQuotient
attribute [-simp] _root_.OAI.KadisonSimilarity.dihedralHalfProjection_projectionReflection _root_.OAI.KadisonSimilarity.orbitAction_coe _root_.OAI.KadisonSimilarity.orbitRepresentation_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual dihedral columns and reduced-word columns agree on the completed
tracial base space. Their normalizations are derived from the trace; equality
of the two realizations is needed only on bounded algebra vectors. -/

noncomputable section
namespace KadisonSimilarity

open scoped TensorProduct

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace TracialCornerGeometry

variable (G : TracialCornerGeometry P H) (D : StarSubalgebra ℂ P)

variable (A : StarSubalgebra ℂ P) [IsClosed (A : Set P)] [IsClosed (D : Set P)]
  (hf : ScalarFree G.trace D A) (hτ : G.trace 1 = 1)
  (d : D) (s : A) (e : D)
  (hdstar : star d = d) (hdsq : d * d = 1) (hd0 : G.trace (d : P) = 0)
  (hsstar : star s = s) (hssq : s * s = 1) (hs0 : G.trace (s : P) = 0)
  (he : IsStarProjection e) {t : ℝ} (ht : 0 < t) (hte : G.trace (e : P) = (t : ℂ))

/-- Actual dihedral word inclusion, with all base-space and compression data
supplied by the ambient tracial representation. -/
def tracialDihedralInclusion (k : ℕ) : G.baseSpace A →ₗᵢ[ℂ] H :=
  actualDihedralInclusion G.trace hτ G.tracial G.vector G.inner_vector D A hf
    (symmetryUnit (d : P) (congrArg (fun x : D => (x : P)) hdsq))
    (symmetryUnit (s : P) (congrArg (fun x : A => (x : P)) hssq)) (e : P)
    d.property s.property e.property hd0 hs0 (symmetryUnit_inv _ _) (symmetryUnit_inv _ _)
    (symmetryUnit_star _ _ (congrArg (fun x : D => (x : P)) hdstar))
    (symmetryUnit_star _ _ (congrArg (fun x : A => (x : P)) hsstar))
    (congrArg (fun x : D => (x : P)) he.isSelfAdjoint.star_eq)
    (congrArg (fun x : D => (x : P)) he.isIdempotentElem.eq)
    (G.baseVector A) (G.baseVector_inner A) (G.baseVector_dense A) t ht hte k

omit [IsClosed (A : Set P)] [IsClosed (D : Set P)] in
@[simp] theorem tracialDihedralInclusion_apply (k : ℕ) (b : A) :
    G.tracialDihedralInclusion D A hf hτ d s e hdstar hdsq hd0 hsstar hssq hs0 he ht hte k
      (G.baseVector A b) =
      dihedralNormalization t • G.vector ((e : P) * ((s : P) * (d : P)) ^ k * (b : P)) := by
  simp only [tracialDihedralInclusion, actualDihedralInclusion,
    dihedralWordIsometry_apply, symmetryUnit_coe]

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_DihedralWordColumn
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual normalized dihedral columns agree with the repeated tensor
words on the dense bounded algebra vectors. -/

noncomputable section
namespace KadisonSimilarity

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace TracialCornerGeometry

variable (G : TracialCornerGeometry P H) (D A : StarSubalgebra ℂ P)
  [IsClosed (A : Set P)] [IsClosed (D : Set P)]
  (hτ : G.trace 1 = 1)
  (d : D) (s : A) (e : D)
  (hdstar : star d = d) (hdsq : d * d = 1) (hd0 : G.trace (d : P) = 0)
  (hsstar : star s = s) (hssq : s * s = 1) (hs0 : G.trace (s : P) = 0)
  (he : IsStarProjection e) {t : ℝ} (ht : 0 < t) (hte : G.trace (e : P) = (t : ℂ))

local instance dihedralMultiplicityNormedFamily :
    ∀ n, NormedAddCommGroup (WordMultiplicity (G.baseVector A 1) n) :=
  fun _ => inferInstance

local instance dihedralMultiplicityInnerFamily :
    ∀ n, InnerProductSpace ℂ (WordMultiplicity (G.baseVector A 1) n) :=
  fun _ => inferInstance

attribute [local irreducible] tracialDihedralInclusion

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_FreeProductMatrixExtension
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.UltrapowerBridge.instStarTracialQuotient
attribute [-simp] _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSymmetryLetter_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.tracialDihedralInclusion_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The precise two-factor matrix-automorphism extension input. -/

noncomputable section
namespace KadisonSimilarity
namespace TracialCornerGeometry

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (G : TracialCornerGeometry P H) (D : StarSubalgebra ℂ P)
  {α : Type*} [Fintype α] [DecidableEq α]
  (ι : Matrix α α ℂ →⋆ₐ[ℂ] D) (u : Matrix.unitaryGroup α ℂ)

@[simp] theorem trace_matrixConjugateLetter (c : D) :
    G.trace (matrixConjugateLetter D ι u c : P) = G.trace (c : P) := by
  have huD : star (ι (u : Matrix α α ℂ)) * ι (u : Matrix α α ℂ) = 1 := by
    rw [← map_star, ← map_mul, u.property.1, map_one]
  have huP : star (ι (u : Matrix α α ℂ) : P) * (ι (u : Matrix α α ℂ) : P) = 1 :=
    congrArg (fun x : D => (x : P)) huD
  change G.trace (((ι (u : Matrix α α ℂ) : P) * (c : P)) *
    star (ι (u : Matrix α α ℂ) : P)) = G.trace (c : P)
  rw [G.tracial, ← mul_assoc, huP, one_mul]

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_TracialAutomorphisms
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.PopaCorner.instOne _root_.OAI.UltrapowerBridge.instStarTracialQuotient
attribute [-simp] _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseGeometry_left_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseGeometry_trace _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseGeometry_vector_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSymmetryLetter_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.trace_matrixConjugateLetter _root_.OAI.KadisonSimilarity.TracialCornerGeometry.tracialDihedralInclusion_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Hilbert-space implementation of trace-preserving automorphisms. The
implementation and its covariance are constructed from dense algebra vectors. -/

noncomputable section
namespace KadisonSimilarity

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace TracialCornerGeometry

variable (G : TracialCornerGeometry P H) (θ : P ≃⋆ₐ[ℂ] P)
  (hθ : ∀ a, G.trace (θ a) = G.trace a)

include hθ in
theorem automorphism_vector_norm (a : P) : ‖G.vector (θ a)‖ = ‖G.vector a‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), norm_sq_eq_re_inner (𝕜 := ℂ),
    G.inner_vector, G.inner_vector, ← map_star θ, ← map_mul θ, hθ]

/-- Extension of the automorphism on bounded algebra vectors. -/
def automorphismIsometry : H →ₗᵢ[ℂ] H :=
  (G.vector.comp θ.toAlgEquiv.toLinearMap).extendOfIsometry G.dense_vector
    (G.automorphism_vector_norm θ hθ)

@[simp] theorem automorphismIsometry_vector (a : P) :
    G.automorphismIsometry θ hθ (G.vector a) = G.vector (θ a) :=
  LinearMap.extendOfIsometry_eq _ G.dense_vector (G.automorphism_vector_norm θ hθ) a

include hθ in
theorem trace_symm_automorphism (a : P) : G.trace (θ.symm a) = G.trace a := by
  simpa only [θ.apply_symm_apply] using (hθ (θ.symm a)).symm

theorem automorphismIsometry_surjective : Function.Surjective (G.automorphismIsometry θ hθ) := by
  intro x
  refine ⟨G.automorphismIsometry θ.symm (G.trace_symm_automorphism θ hθ) x, ?_⟩
  refine G.dense_vector.induction_on x (isClosed_eq (by fun_prop) continuous_id) ?_
  intro a
  simp only [automorphismIsometry_vector, θ.apply_symm_apply]

/-- The actual unitary implementation of a trace-preserving automorphism. -/
def automorphismUnitary : H ≃ₗᵢ[ℂ] H :=
  LinearIsometryEquiv.ofSurjective (G.automorphismIsometry θ hθ)
    (G.automorphismIsometry_surjective θ hθ)

@[simp] theorem automorphismUnitary_vector (a : P) :
    G.automorphismUnitary θ hθ (G.vector a) = G.vector (θ a) :=
  G.automorphismIsometry_vector θ hθ a

/-- A trace-preserving algebraic group action gives a unitary representation. -/
def automorphismRepresentation {Γ : Type*} [Group Γ]
    (α : Γ →* (P ≃⋆ₐ[ℂ] P)) (hα : ∀ g a, G.trace (α g a) = G.trace a) :
    Γ →* unitary (H →L[ℂ] H) where
  toFun g := Unitary.linearIsometryEquiv.symm (G.automorphismUnitary (α g) (hα g))
  map_one' := by
    apply Subtype.ext
    apply ContinuousLinearMap.ext
    intro x
    refine G.dense_vector.induction_on x (isClosed_eq (by fun_prop) (by fun_prop)) ?_
    intro a
    change G.automorphismUnitary (α 1) (hα 1) (G.vector a) = G.vector a
    rw [G.automorphismUnitary_vector, map_one]
    rfl
  map_mul' g h := by
    apply Subtype.ext
    apply ContinuousLinearMap.ext
    intro x
    refine G.dense_vector.induction_on x (isClosed_eq (by fun_prop) (by fun_prop)) ?_
    intro a
    change G.automorphismUnitary (α (g * h)) (hα (g * h)) (G.vector a) =
      G.automorphismUnitary (α g) (hα g)
        (G.automorphismUnitary (α h) (hα h) (G.vector a))
    simp only [G.automorphismUnitary_vector, map_mul]
    rfl

@[simp] theorem automorphismRepresentation_vector {Γ : Type*} [Group Γ]
    (α : Γ →* (P ≃⋆ₐ[ℂ] P)) (hα : ∀ g a, G.trace (α g a) = G.trace a)
    (g : Γ) (a : P) :
    (G.automorphismRepresentation α hα g : H →L[ℂ] H) (G.vector a) =
      G.vector (α g a) := G.automorphismUnitary_vector (α g) (hα g) a

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_FreeProductAutomorphisms
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.UltrapowerBridge.instStarTracialQuotient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Algebraic extensions become actual automorphisms by tracial L² density.
The only extension input is the two-factor published embedding specialization. -/

noncomputable section
namespace KadisonSimilarity
namespace TracialCornerGeometry

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (G : TracialCornerGeometry P H)

/-- Ordinary tracial generation by the two factors. This is geometric density
of algebra vectors, independent of any operator intertwining statement. -/
def FactorsTraciallyGenerate (A D : StarSubalgebra ℂ P) : Prop :=
  DenseRange (G.vector.comp (factorAlgebra A D).subtype.toLinearMap)

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_FreeWordHilbert
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.UltrapowerBridge.instStarTracialQuotient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact Gram matrices of the regrouped free-product word vectors. -/

noncomputable section
namespace KadisonSimilarity

attribute [local irreducible] TracialCornerGeometry.baseSpace tensorWordSpace

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace TracialCornerGeometry

variable (G : TracialCornerGeometry P H)

theorem trace_star (x : P) : G.trace (star x) = star (G.trace x) := by
  calc
    _ = inner ℂ (G.vector x) (G.vector 1) := by rw [G.inner_vector, mul_one]
    _ = star (inner ℂ (G.vector 1) (G.vector x)) := (inner_conj_symm _ _).symm
    _ = _ := by rw [G.inner_vector, star_one, one_mul]

end TracialCornerGeometry

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_TracialMatrixTower
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.UltrapowerBridge.instStarTracialQuotient
attribute [-simp] _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSymmetryLetter_coe _root_.OAI.KadisonSimilarity.baseWordInclusion_apply _root_.OAI.KadisonSimilarity.multiplicityWordInclusion_apply _root_.OAI.KadisonSimilarity.norm_repeatedMultiplicityWord _root_.OAI.KadisonSimilarity.norm_zeroMultiplicityWord _root_.OAI.KadisonSimilarity.repeatedMultiplicityInclusion_apply _root_.OAI.KadisonSimilarity.zeroMultiplicityEquiv_apply _root_.OAI.KadisonSimilarity.zeroMultiplicityInclusion_apply _root_.OAI.KadisonSimilarity.zeroMultiplicityOperator_intertwines
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Tracial matrix towers from actual embedded matrix algebras

The matrix-stage geometry is constructed from nested trace-preserving matrix
embeddings in a tracial Hilbert representation. Density of centered trace-zero
stages is derived by orthogonal projection from density of the full stages.
-/

noncomputable section
namespace KadisonSimilarity

universe u v
variable {R : Type v} {E : Type u}
  [Ring R] [StarRing R] [Algebra ℂ R]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  {A : ℕ → Type*} [∀ s, Fintype (A s)] [∀ s, DecidableEq (A s)]
  [∀ s, Nonempty (A s)]

variable (τ : R →ₗ[ℂ] ℂ) (V : R →ₗ[ℂ] E) (L : R →⋆ₐ[ℂ] (E →L[ℂ] E))
  (hinner : ∀ a b, inner ℂ (V a) (V b) = τ (star a * b))
  (hleft : ∀ a b, L a (V b) = V (a * b))
  (M : NestedTracialMatrices (A := A) τ V)

/-- The stage of a nested embedded matrix algebra. -/
def embeddedMatrixStage (s : ℕ) :
    MatrixHilbertStage (E := E) (F := centeredSubspace (V 1)) (α := A s) :=
  tracialMatrixStage τ V L (M.embedding s) hinner hleft (M.trace_embedding s)

omit [∀ s, Nonempty (A s)] in
@[simp] theorem embeddedMatrixStage_full (s : ℕ) (a : Matrix (A s) (A s) ℂ) :
    (embeddedMatrixStage τ V L hinner hleft M s).full a = V (M.embedding s a) := rfl

omit [∀ s, Nonempty (A s)] in
@[simp] theorem embeddedMatrixStage_center (s : ℕ) (a : Matrix (A s) (A s) ℂ) :
    (embeddedMatrixStage τ V L hinner hleft M s).center a =
      tracialCenter V (M.embedding s a) := rfl

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_MatrixUnitFamilies
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.UltrapowerBridge.instStarTracialQuotient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite partial-isometry frames constructed from an actual unital matrix
star homomorphism. No frame-existence assumption is used. -/

noncomputable section
namespace KadisonSimilarity

variable {P α : Type*} [CStarAlgebra P] [Fintype α] [DecidableEq α]

section NestedMatrices

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  {A : ℕ → Type*} [∀ s, Fintype (A s)] [∀ s, DecidableEq (A s)]
  {τ : P →ₗ[ℂ] ℂ} {V : P →ₗ[ℂ] E}

/-- Each actual tracial matrix stage supplies its finite corner frame. -/
def NestedTracialMatrices.columnFamily (M : NestedTracialMatrices (A := A) τ V)
    (s : ℕ) (i₀ : A s) : TracialMatrixUnitColumnFamily τ (A s) :=
  tracialMatrixUnitColumnFamilyOfEmbedding τ (M.embedding s) (M.trace_embedding s) i₀

/-- The same actual frame on `Fin(card(A s))`, as required by finite Hilbert
amplification and the full-column coordinate construction. -/
def NestedTracialMatrices.finColumnFamily (M : NestedTracialMatrices (A := A) τ V)
    (s : ℕ) (i₀ : A s) : TracialMatrixUnitColumnFamily τ (Fin (Fintype.card (A s))) :=
  (M.columnFamily s i₀).reindex (Fintype.equivFin (A s)).symm

@[simp] theorem NestedTracialMatrices.finColumnFamily_corner
    (M : NestedTracialMatrices (A := A) τ V) (s : ℕ) (i₀ : A s) :
    (M.finColumnFamily s i₀).corner = M.embedding s (Matrix.single i₀ i₀ 1) := rfl

@[simp] theorem NestedTracialMatrices.finColumnFamily_column
    (M : NestedTracialMatrices (A := A) τ V) (s : ℕ) (i₀ : A s)
    (i : Fin (Fintype.card (A s))) :
    (M.finColumnFamily s i₀).column i =
      M.embedding s (Matrix.single ((Fintype.equivFin (A s)).symm i) i₀ 1) := rfl

@[simp] theorem NestedTracialMatrices.finColumnFamily_base
    (M : NestedTracialMatrices (A := A) τ V) (s : ℕ) (i₀ : A s) :
    (M.finColumnFamily s i₀).base = Fintype.equivFin (A s) i₀ := rfl

end NestedMatrices

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_SmallFreeCornerData
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The small projection, its full matrix frame, the containing half
projection, and the Haar unitary all belong to the same corner. The matrix
frame is constructed from the tower. Only trace cutting and the local Haar
existence statement are required for the two remaining choices. -/

noncomputable section
namespace KadisonSimilarity

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The exact geometric data used in one application of the free-corner
estimate. None of the fields mentions the operator being estimated. -/
structure SmallFreeCornerData (τ : P →ₗ[ℂ] ℂ) (s : ℝ) where
  size : ℕ
  size_pos : 0 < size
  frame : TracialMatrixUnitColumnFamily τ (Fin size)
  trace : ℝ
  trace_pos : 0 < trace
  trace_lt : trace < s
  corner_trace : τ frame.corner = (trace : ℂ)
  half : HalfTraceProjectionData τ frame.corner
  haar : unitary (CStarCorner frame.corner frame.corner_projection)
  moments : HaarCornerMoments τ haar trace

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_TracialCornerRepresentations
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.tupleOrbitClosure_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.UltrapowerBridge.instStarTracialQuotient
attribute [-simp] _root_.OAI.KadisonSimilarity.CStarCorner.mem_subalgebra _root_.OAI.KadisonSimilarity.CStarCorner.normalizedTrace_apply _root_.OAI.KadisonSimilarity.TracialCornerGeometry.automorphismIsometry_vector _root_.OAI.KadisonSimilarity.TracialCornerGeometry.automorphismRepresentation_vector _root_.OAI.KadisonSimilarity.TracialCornerGeometry.automorphismUnitary_vector _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseAction_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseAlgebraVectors_apply _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseCompression_apply _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseGeometry_left_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseGeometry_trace _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseGeometry_vector_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseInclusion_apply _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseInclusion_vector _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseOperator_adjoint _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseRepresentation_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSymmetryLetter_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseVector_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.trace_matrixConjugateLetter _root_.OAI.KadisonSimilarity.TracialCornerGeometry.tracialDihedralInclusion_apply _root_.OAI.KadisonSimilarity.TracialExpectation.corner_map_coe _root_.OAI.KadisonSimilarity.cornerStarAlgHom_coe _root_.OAI.KadisonSimilarity.haarCornerLetter_mul_support _root_.OAI.KadisonSimilarity.haarCornerPower_mul _root_.OAI.KadisonSimilarity.haarCornerPower_mul_support _root_.OAI.KadisonSimilarity.haarCornerPower_zero _root_.OAI.KadisonSimilarity.mul_haarCornerPower _root_.OAI.KadisonSimilarity.orbitAction_coe _root_.OAI.KadisonSimilarity.orbitRepresentation_coe _root_.OAI.KadisonSimilarity.star_haarCornerLetter _root_.OAI.KadisonSimilarity.star_haarCornerPower _root_.OAI.KadisonSimilarity.support_mul_haarCornerLetter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual corner representations on the completed tracial Hilbert corners. -/

noncomputable section
namespace KadisonSimilarity

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace TracialCornerGeometry

variable (G : TracialCornerGeometry P H) (e : P) (he : IsStarProjection e) (r : P)

/-- Left multiplication by a corner element preserves both support equations. -/
theorem cornerAction_mem (a : CStarCorner e he) (x : H) (hx : x ∈ G.corner e r) :
    G.left (a : P) x ∈ G.corner e r := by
  rw [G.mem_corner] at hx ⊢
  constructor
  · have ha := congrArg (fun b : P => G.left b x) a.property.1
    simpa only [map_mul, mul_apply_eq_comp] using ha
  · have h := congrArg (fun T : H →L[ℂ] H => T x) (G.right_left (a : P) r)
    simpa only [ContinuousLinearMap.comp_apply, hx.2] using h

def cornerAction (a : CStarCorner e he) : G.corner e r →L[ℂ] G.corner e r :=
  (G.left (a : P)).restrict (G.cornerAction_mem e he r a)

@[simp] theorem cornerAction_coe (a : CStarCorner e he) (x : G.corner e r) :
    (G.cornerAction e he r a x : H) = G.left (a : P) x := rfl

/-- The identity of `ePe` is `e`, acting as the identity on `eL²(P)r`. -/
def cornerRepresentation : CStarCorner e he →⋆ₐ[ℂ] (G.corner e r →L[ℂ] G.corner e r) where
  toFun := G.cornerAction e he r
  map_zero' := by
    ext x
    simp
  map_one' := by
    ext x
    change G.left ((1 : CStarCorner e he) : P) (x : H) = x
    rw [CStarCorner.coe_one]
    exact ((G.mem_corner e r x).mp x.property).1
  map_add' a b := by
    ext x
    change G.left ((a : P) + (b : P)) (x : H) = _
    simp
  map_mul' a b := by
    ext x
    change G.left ((a : P) * (b : P)) (x : H) = _
    simp [mul_apply_eq_comp]
  commutes' c := by
    ext x
    change G.left ((algebraMap ℂ (CStarCorner e he) c : CStarCorner e he) : P) (x : H) = _
    rw [Algebra.algebraMap_eq_smul_one]
    change G.left (c • ((1 : CStarCorner e he) : P)) (x : H) = _
    rw [CStarCorner.coe_one, map_smul]
    change c • G.left e (x : H) = c • (x : H)
    rw [((G.mem_corner e r x).mp x.property).1]
  map_star' a := by
    apply ContinuousLinearMap.ext
    intro x
    apply ext_inner_left ℂ
    intro y
    change inner ℂ (y : H) (G.left (star (a : P)) (x : H)) =
      inner ℂ y ((G.cornerAction e he r a).adjoint x)
    rw [ContinuousLinearMap.adjoint_inner_right]
    change inner ℂ (y : H) (G.left (star (a : P)) (x : H)) =
      inner ℂ (G.left (a : P) (y : H)) (x : H)
    rw [map_star]
    exact ContinuousLinearMap.adjoint_inner_right _ _ _

@[simp] theorem cornerRepresentation_coe (a : CStarCorner e he) (x : G.corner e r) :
    (G.cornerRepresentation e he r a x : H) = G.left (a : P) x := rfl

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_TracialCornerHilbert
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.UltrapowerBridge.instStarTracialQuotient
attribute [-simp] _root_.OAI.KadisonSimilarity.TracialCornerGeometry.automorphismIsometry_vector _root_.OAI.KadisonSimilarity.TracialCornerGeometry.automorphismRepresentation_vector _root_.OAI.KadisonSimilarity.TracialCornerGeometry.automorphismUnitary_vector _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseGeometry_left_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseGeometry_trace _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseGeometry_vector_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSymmetryLetter_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.trace_matrixConjugateLetter _root_.OAI.KadisonSimilarity.TracialCornerGeometry.tracialDihedralInclusion_apply _root_.OAI.KadisonSimilarity.cornerStarAlgHom_coe _root_.OAI.KadisonSimilarity.haarCornerLetter_mul_support _root_.OAI.KadisonSimilarity.haarCornerPower_mul _root_.OAI.KadisonSimilarity.haarCornerPower_mul_support _root_.OAI.KadisonSimilarity.haarCornerPower_zero _root_.OAI.KadisonSimilarity.mul_haarCornerPower _root_.OAI.KadisonSimilarity.orbitAction_coe _root_.OAI.KadisonSimilarity.orbitRepresentation_coe _root_.OAI.KadisonSimilarity.star_haarCornerLetter _root_.OAI.KadisonSimilarity.star_haarCornerPower _root_.OAI.KadisonSimilarity.support_mul_haarCornerLetter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The normalized tracial Hilbert representation of an actual C-star corner.
Its density and action are inherited from the ambient tracial representation. -/

noncomputable section
namespace KadisonSimilarity

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace TracialCornerGeometry

variable (G : TracialCornerGeometry P H) (p : P) (hp : IsStarProjection p)

def cornerAlgebraVector : CStarCorner p hp →ₗ[ℂ] G.corner p p where
  toFun a := ⟨G.vector (a : P), by
    rw [G.mem_corner]
    exact ⟨by rw [G.left_vector, a.property.1], by rw [G.right_vector, a.property.2]⟩⟩
  map_add' a b := Subtype.ext (G.vector.map_add (a : P) (b : P))
  map_smul' c a := Subtype.ext (G.vector.map_smul c (a : P))

@[simp] theorem cornerAlgebraVector_coe (a : CStarCorner p hp) :
    (G.cornerAlgebraVector p hp a : H) = G.vector (a : P) := rfl

/-- Rescale the ordinary corner vectors so that their inner product is
the normalized corner trace. -/
def normalizedCornerVector (c : ℂ) : CStarCorner p hp →ₗ[ℂ] G.corner p p :=
  c • G.cornerAlgebraVector p hp

@[simp] theorem normalizedCornerVector_coe (c : ℂ) (a : CStarCorner p hp) :
    (G.normalizedCornerVector p hp c a : H) = c • G.vector (a : P) := rfl

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_SpectralArc
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.UltrapowerBridge.instStarTracialQuotient
attribute [-simp] _root_.OAI.KadisonSimilarity.cornerStarAlgHom_coe _root_.OAI.KadisonSimilarity.dihedralHalfProjection_projectionReflection _root_.OAI.KadisonSimilarity.haarCornerLetter_mul_support _root_.OAI.KadisonSimilarity.haarCornerPower_mul _root_.OAI.KadisonSimilarity.haarCornerPower_mul_support _root_.OAI.KadisonSimilarity.haarCornerPower_zero _root_.OAI.KadisonSimilarity.mul_haarCornerPower _root_.OAI.KadisonSimilarity.star_haarCornerLetter _root_.OAI.KadisonSimilarity.star_haarCornerPower _root_.OAI.KadisonSimilarity.support_mul_haarCornerLetter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The bounded Borel spectral calculus input, specialized to the centered
arc of a Haar rotation in a finite dihedral von Neumann algebra. Blackadar,
Operator Algebras, I.6.2.4 and I.6.2.8, supply the calculus and commutation;
integration against its Haar spectral measure gives the stated moments.

The interface is local to the specified trace and algebra. Its intended
application has the normal finite trace and the von Neumann algebra generated
by the two symmetries. No existence assertion is made for an arbitrary C-star
subalgebra or an arbitrary linear functional. The corner estimates below are
proved from the spectral data, rather than included in the published input. -/

noncomputable section
namespace KadisonSimilarity

variable {P : Type*} [CStarAlgebra P]

namespace DihedralSpectralArc

variable {τ : P →ₗ[ℂ] ℂ} {C : StarSubalgebra ℂ P} {w d : Pˣ} {θ : ℝ}
  (F : DihedralSpectralArc τ C w d θ)

/-- The actual arc element in the normalized half corner. -/
def corner (hp : IsStarProjection (dihedralHalfProjection d)) :
    CStarCorner (dihedralHalfProjection d) hp :=
  ⟨F.element * dihedralHalfProjection d, by
    constructor
    · rw [← mul_assoc, ← F.halfProjection_commutes.eq, mul_assoc,
        hp.isIdempotentElem.eq]
    · rw [mul_assoc, hp.isIdempotentElem.eq]⟩

@[simp] theorem corner_coe (hp : IsStarProjection (dihedralHalfProjection d)) :
    (F.corner hp : P) = F.element * dihedralHalfProjection d := rfl

end DihedralSpectralArc
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_TracialWordActions
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The represented left head action follows from the ordinary product
formula in the reduced-word model. It is not extra covariance data. -/

noncomputable section
namespace KadisonSimilarity

attribute [local irreducible] TracialCornerGeometry.baseSpace tensorWordSpace

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace TracialCornerGeometry

variable (G : TracialCornerGeometry P H) (A D : StarSubalgebra ℂ P)
  [IsClosed (A : Set P)] [IsClosed (D : Set P)]

local instance actionMultiplicityNormedFamily :
    ∀ n, NormedAddCommGroup (WordMultiplicity (G.baseVector A 1) n) :=
  fun _ => inferInstance

local instance actionMultiplicityInnerFamily :
    ∀ n, InnerProductSpace ℂ (WordMultiplicity (G.baseVector A 1) n) :=
  fun _ => inferInstance

end TracialCornerGeometry

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_TracialWordIsometry
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Construction of the completed free-product word inclusions from the
proved Gram identities and totality of elementary tensors. -/

noncomputable section
namespace KadisonSimilarity

attribute [local irreducible] TracialCornerGeometry.baseSpace tensorWordSpace

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (G : TracialCornerGeometry P H) (A D : StarSubalgebra ℂ P)
  [IsClosed (A : Set P)] [IsClosed (D : Set P)]

abbrev CenteredTracialLetter := {a : A // G.trace (a : P) = 0}

abbrev TracialWordParameter (n : ℕ) :=
  ((Fin n → CenteredTracialLetter G A) × A) ×
    (D × (Fin n → CenteredTracialLetter G D))

def tracialTensorFamily (n : ℕ) (p : TracialWordParameter G A D n) :=
  tracialWordTensor G A D n p.2.1 p.1.2 (fun i => (p.1.1 i).1)
    (fun i => (p.2.2 i).1) (fun i => (p.1.1 i).2) (fun i => (p.2.2 i).2)

def tracialAlgebraFamily (n : ℕ) (p : TracialWordParameter G A D n) : H :=
  G.vector ((p.2.1 : P) * alternatingProduct (fun i => ((p.1.1 i).1 : P))
    (fun i => ((p.2.2 i).1 : P)) * (p.1.2 : P))

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_TracialSupportedColumns
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.tupleOrbitClosure_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.UltrapowerBridge.instStarTracialQuotient
attribute [-simp] _root_.OAI.KadisonSimilarity.TracialCornerGeometry.automorphismIsometry_vector _root_.OAI.KadisonSimilarity.TracialCornerGeometry.automorphismRepresentation_vector _root_.OAI.KadisonSimilarity.TracialCornerGeometry.automorphismUnitary_vector _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseAction_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseAlgebraVectors_apply _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseCompression_apply _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseGeometry_left_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseGeometry_trace _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseGeometry_vector_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseInclusion_apply _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseInclusion_vector _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseOperator_adjoint _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseRepresentation_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSymmetryLetter_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseVector_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerAlgebraVector_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.normalizedCornerVector_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.trace_matrixConjugateLetter _root_.OAI.KadisonSimilarity.TracialCornerGeometry.tracialDihedralInclusion_apply _root_.OAI.KadisonSimilarity.orbitAction_coe _root_.OAI.KadisonSimilarity.orbitRepresentation_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Support projections and represented right columns in a concrete tracial
Hilbert space. These are the ambient spaces used by the full-column lemma. -/

noncomputable section
namespace KadisonSimilarity

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace TracialCornerGeometry

variable (G : TracialCornerGeometry P H)

@[simp] theorem right_one : G.right 1 = ContinuousLinearMap.id ℂ H := by
  apply ContinuousLinearMap.ext
  intro x
  refine G.dense_vector.induction_on x (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro a
  simp

@[simp] theorem right_zero : G.right 0 = 0 := by
  apply ContinuousLinearMap.ext
  intro x
  refine G.dense_vector.induction_on x (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro a
  simp

theorem rightColumn_mem (r a : P) (x : H) (hx : x ∈ G.corner 1 r) :
    G.left a x ∈ G.corner 1 r := by
  rw [G.mem_corner] at hx ⊢
  constructor
  · simp
  · have hc := congrArg (fun T : H →L[ℂ] H => T x) (G.right_left a r)
    simpa only [ContinuousLinearMap.comp_apply, hx.2] using hc

def rightColumnAction (r a : P) : G.corner 1 r →L[ℂ] G.corner 1 r :=
  (G.left a).restrict (G.rightColumn_mem r a)

@[simp] theorem rightColumnAction_coe (r a : P) (x : G.corner 1 r) :
    (G.rightColumnAction r a x : H) = G.left a x := rfl

/-- Left multiplication by the full algebra on a right-supported Hilbert
column. No standard-form representation theorem is used here. -/
def rightColumnRepresentation (r : P) : P →⋆ₐ[ℂ] (G.corner 1 r →L[ℂ] G.corner 1 r) where
  toFun := G.rightColumnAction r
  map_zero' := by ext x; simp
  map_one' := by ext x; simp
  map_add' a b := by ext x; simp
  map_mul' a b := by ext x; simp [mul_apply_eq_comp]
  commutes' c := by ext x; simp [Algebra.algebraMap_eq_smul_one]
  map_star' a := by
    apply ContinuousLinearMap.ext
    intro x
    apply ext_inner_left ℂ
    intro y
    change inner ℂ (y : H) (G.left (star a) (x : H)) =
      inner ℂ y ((G.rightColumnAction r a).adjoint x)
    rw [ContinuousLinearMap.adjoint_inner_right]
    change inner ℂ (y : H) (G.left (star a) (x : H)) =
      inner ℂ (G.left a (y : H)) (x : H)
    rw [map_star]
    exact ContinuousLinearMap.adjoint_inner_right _ _ _

@[simp] theorem rightColumnRepresentation_coe (r a : P) (x : G.corner 1 r) :
    (G.rightColumnRepresentation r a x : H) = G.left a x := rfl

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_TracialMatrixColumns
attribute [-instance] _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.UltrapowerBridge.instStarTracialQuotient
attribute [-simp] _root_.OAI.KadisonSimilarity.TracialCornerGeometry.automorphismIsometry_vector _root_.OAI.KadisonSimilarity.TracialCornerGeometry.automorphismRepresentation_vector _root_.OAI.KadisonSimilarity.TracialCornerGeometry.automorphismUnitary_vector _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseAction_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseAlgebraVectors_apply _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseCompression_apply _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseGeometry_left_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseGeometry_trace _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseGeometry_vector_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseInclusion_apply _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseInclusion_vector _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseOperator_adjoint _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseRepresentation_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSymmetryLetter_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseVector_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerAlgebraVector_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.normalizedCornerVector_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.trace_matrixConjugateLetter _root_.OAI.KadisonSimilarity.TracialCornerGeometry.tracialDihedralInclusion_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The matrix-unit column coordinates of a concrete tracial corner. -/

noncomputable section
namespace KadisonSimilarity

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace TracialCornerGeometry

variable (G : TracialCornerGeometry P H) (e : P) (he : IsStarProjection e) (r : P)

/-- Forget only the left support of a two-sided corner. -/
def cornerToRightColumn : G.corner e r →ₗᵢ[ℂ] G.corner 1 r where
  toFun x := ⟨x, by
    rw [G.mem_corner]
    exact ⟨by simp, ((G.mem_corner e r x).mp x.property).2⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' _ := rfl

@[simp] theorem cornerToRightColumn_coe (x : G.corner e r) :
    (G.cornerToRightColumn e r x : H) = x := rfl

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tensor_TensorHeadSlices
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero
attribute [-simp] _root_.OAI.KadisonSimilarity.baseWordInclusion_apply _root_.OAI.KadisonSimilarity.crossMultiplicitySlice_zero _root_.OAI.KadisonSimilarity.multiplicityWordInclusion_apply _root_.OAI.KadisonSimilarity.norm_emptyEndpoint _root_.OAI.KadisonSimilarity.repeatedMultiplicityInclusion_apply _root_.OAI.KadisonSimilarity.repeatedWordInclusion_apply _root_.OAI.KadisonSimilarity.zeroMultiplicityEquiv_apply _root_.OAI.KadisonSimilarity.zeroMultiplicityInclusion_apply _root_.OAI.KadisonSimilarity.zeroMultiplicityOperator_intertwines
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Vacuum coefficients of a head tensor action

The exceptional-projection formula in propagation follows from the actual
head action on the completed tensor product. It does not need to be assumed
separately for every vector or every term of the Haar sequence.
-/

noncomputable section
namespace KadisonSimilarity

open ContinuousLinearMap
open scoped TensorProduct

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- Act on the head factor while leaving the completed tail unchanged. -/
def tensorHeadAction (X : E →L[ℂ] E) : HilbertTensor E F →L[ℂ] HilbertTensor E F :=
  (TensorProduct.mapL X (ContinuousLinearMap.id ℂ F)).completion

omit [CompleteSpace F] in
@[simp] theorem tensorHeadAction_insert (X : E →L[ℂ] E) (a : E) (x : F) :
    tensorHeadAction X (hilbertTensorInsert a x) = hilbertTensorInsert (X a) x := by
  change (TensorProduct.mapL X (ContinuousLinearMap.id ℂ F)).completion
    ((a ⊗ₜ[ℂ] x : TensorProduct ℂ E F) : UniformSpace.Completion (TensorProduct ℂ E F)) =
      ((X a ⊗ₜ[ℂ] x : TensorProduct ℂ E F) : UniformSpace.Completion (TensorProduct ℂ E F))
  simp only [ContinuousLinearMap.completion_apply_coe, TensorProduct.mapL_tmul,
    ContinuousLinearMap.id_apply]

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Representation_ReducedCreationBlocks
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing
attribute [-simp] _root_.OAI.KadisonSimilarity.baseWordInclusion_apply _root_.OAI.KadisonSimilarity.crossMultiplicitySlice_zero _root_.OAI.KadisonSimilarity.multiplicityWordInclusion_apply _root_.OAI.KadisonSimilarity.norm_emptyEndpoint _root_.OAI.KadisonSimilarity.repeatedMultiplicityInclusion_apply _root_.OAI.KadisonSimilarity.repeatedWordInclusion_apply _root_.OAI.KadisonSimilarity.tensorHeadAction_insert _root_.OAI.KadisonSimilarity.zeroMultiplicityEquiv_apply _root_.OAI.KadisonSimilarity.zeroMultiplicityInclusion_apply _root_.OAI.KadisonSimilarity.zeroMultiplicityOperator_intertwines
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The creation and zero-block consequences of the reduced-word action.
Only its action on elementary words is needed; the operator block bounds are
derived by the isometric word coordinates and density. -/

noncomputable section
namespace KadisonSimilarity

variable {E K H : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Insert the centered first letter and then use the reduced-word inclusion. -/
def reducedCreator (C : HilbertTensor E K →ₗᵢ[ℂ] H) (b : E) : K →L[ℂ] H :=
  C.toContinuousLinearMap.comp (hilbertTensorInsert b)

omit [CompleteSpace K] [CompleteSpace H] in
@[simp] theorem reducedCreator_apply (C : HilbertTensor E K →ₗᵢ[ℂ] H) (b : E) (x : K) :
    reducedCreator C b x = C (hilbertTensorInsert b x) := rfl

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_WordPrefixRealization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fixed alternating prefixes in propagation are isometries on the
appropriate reduced-word subspace. This follows by iterating the two
one-letter Fock creation formulas. Their global operator bounds follow from
the algebraic symmetry and normalized corner-unitary relations. -/

noncomputable section
namespace KadisonSimilarity

section Creation

variable {EA ED H : Type*}
  [NormedAddCommGroup EA] [InnerProductSpace ℂ EA]
  [NormedAddCommGroup ED] [InnerProductSpace ℂ ED]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The two elementary creation formulas for reduced words starting in the
opposite free factor. The tensor maps are the usual isometric inclusions of
reduced-word summands, and the specified letters have Hilbert norm one. -/
structure AlternatingCreationCoordinates (EA ED : Type*)
    [NormedAddCommGroup EA] [InnerProductSpace ℂ EA]
    [NormedAddCommGroup ED] [InnerProductSpace ℂ ED]
    (S : H →L[ℂ] H) (X : ℕ → H →L[ℂ] H) (DLead : Submodule ℂ H) where
  ALead : Submodule ℂ H
  s : EA
  x : ℕ → ED
  norm_s : ‖s‖ = 1
  norm_x : ∀ n, ‖x n‖ = 1
  createA : HilbertTensor EA DLead →ₗᵢ[ℂ] H
  createD : HilbertTensor ED ALead →ₗᵢ[ℂ] H
  createA_mem : ∀ w, createA w ∈ ALead
  createD_mem : ∀ w, createD w ∈ DLead
  actionA : ∀ y : DLead, S y = createA (hilbertTensorInsert s y)
  actionD : ∀ n (y : ALead), X n y = createD (hilbertTensorInsert (x n) y)

namespace AlternatingCreationCoordinates

variable {S : H →L[ℂ] H} {X : ℕ → H →L[ℂ] H} {DLead : Submodule ℂ H}
  (C : AlternatingCreationCoordinates EA ED S X DLead)

/-- The first elementary creation step has norm one and the expected range. -/
theorem actionA_isometry (y : H) (hy : y ∈ DLead) :
    S y ∈ C.ALead ∧ ‖S y‖ = ‖y‖ := by
  have h := C.actionA (⟨y, hy⟩ : DLead)
  refine ⟨?_, ?_⟩
  · rw [h]
    exact C.createA_mem _
  · rw [h, LinearIsometry.norm_map, norm_hilbertTensorInsert, C.norm_s, one_mul]
    rfl

/-- The second elementary creation step has norm one and returns to the
subspace of words starting in the other free factor. -/
theorem actionD_isometry (n : ℕ) (y : H) (hy : y ∈ C.ALead) :
    X n y ∈ DLead ∧ ‖X n y‖ = ‖y‖ := by
  have h := C.actionD n (⟨y, hy⟩ : C.ALead)
  refine ⟨?_, ?_⟩
  · rw [h]
    exact C.createD_mem _
  · rw [h, LinearIsometry.norm_map, norm_hilbertTensorInsert, C.norm_x, one_mul]
    rfl

/-- Iterating the elementary formulas proves the fixed alternating-prefix
isometry; no bound on a complete prefix is assumed. -/
theorem prefix_isometry (m n : ℕ) (y : H) (hy : y ∈ DLead) :
    ((S * X n) ^ m * S) y ∈ C.ALead ∧
      ‖((S * X n) ^ m * S) y‖ = ‖y‖ := by
  induction m with
  | zero => simpa only [pow_zero, one_mul] using C.actionA_isometry y hy
  | succ m ih =>
    have hx := C.actionD_isometry n _ ih.1
    have hs := C.actionA_isometry _ hx.1
    rw [pow_succ']
    change S (X n (((S * X n) ^ m * S) y)) ∈ C.ALead ∧
      ‖S (X n (((S * X n) ^ m * S) y))‖ = ‖y‖
    exact ⟨hs.1, hs.2.trans (hx.2.trans ih.2)⟩

end AlternatingCreationCoordinates
end Creation

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_MatrixConjugateAutomorphism
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.UltrapowerBridge.instStarTracialQuotient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Matrix conjugation as an actual star-algebra automorphism of the factor. -/

noncomputable section
namespace KadisonSimilarity.TracialCornerGeometry

variable {P : Type*} [CStarAlgebra P] (D : StarSubalgebra ℂ P)
  {α : Type*} [Fintype α] [DecidableEq α]
  (ι : Matrix α α ℂ →⋆ₐ[ℂ] D) (u : Matrix.unitaryGroup α ℂ)

@[simp] theorem matrixConjugationAut_apply (d : D) :
    matrixConjugationAut D ι u d = matrixConjugateLetter D ι u d := rfl

@[simp] theorem matrixConjugateLetter_one_letter :
    matrixConjugateLetter D ι u 1 = 1 :=
  map_one (matrixConjugationAut D ι u)

@[simp] theorem matrixConjugateLetter_product (a b : D) :
    matrixConjugateLetter D ι u (a * b) =
      matrixConjugateLetter D ι u a * matrixConjugateLetter D ι u b :=
  map_mul (matrixConjugationAut D ι u) a b

@[simp] theorem matrixConjugateLetter_sub (a b : D) :
    matrixConjugateLetter D ι u (a - b) =
      matrixConjugateLetter D ι u a - matrixConjugateLetter D ι u b :=
  map_sub (matrixConjugationAut D ι u) a b

@[simp] theorem matrixConjugateLetter_smul (r : ℂ) (a : D) :
    matrixConjugateLetter D ι u (r • a) = r • matrixConjugateLetter D ι u a :=
  map_smul (matrixConjugationAut D ι u) r a

end KadisonSimilarity.TracialCornerGeometry

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_TracialCreationCoordinates
attribute [-simp] _root_.OAI.KadisonSimilarity.CStarCorner.mem_subalgebra _root_.OAI.KadisonSimilarity.CStarCorner.normalizedTrace_apply _root_.OAI.KadisonSimilarity.DihedralSpectralArc.corner_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.automorphismIsometry_vector _root_.OAI.KadisonSimilarity.TracialCornerGeometry.automorphismRepresentation_vector _root_.OAI.KadisonSimilarity.TracialCornerGeometry.automorphismUnitary_vector _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerAlgebraVector_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.normalizedCornerVector_coe _root_.OAI.KadisonSimilarity.TracialCornerGeometry.trace_matrixConjugateLetter _root_.OAI.KadisonSimilarity.TracialCornerGeometry.tracialDihedralInclusion_apply _root_.OAI.KadisonSimilarity.TracialExpectation.corner_map_coe _root_.OAI.KadisonSimilarity.baseWordInclusion_apply _root_.OAI.KadisonSimilarity.cornerStarAlgHom_coe _root_.OAI.KadisonSimilarity.embeddedMatrixStage_center _root_.OAI.KadisonSimilarity.embeddedMatrixStage_full
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Elementary reduced-word creation in the actual tracial base spaces.
The normalized symmetry and corner Haar vectors are constructed, so the
only word-model inputs are isometric tensor inclusions and their elementary
multiplication and range formulas. -/

noncomputable section
namespace KadisonSimilarity

variable {P H F : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

namespace TracialCornerGeometry

variable (G : TracialCornerGeometry P H) (D : StarSubalgebra ℂ P)
  [IsClosed (D : Set P)] {q : D} {hq : IsStarProjection q}
  (z : unitary (CStarCorner q hq)) {a : ℝ} (ha : 0 < a)
  (htrace : G.trace (q : P) = (a : ℂ))
  (hhaar : HaarCornerMoments (G.baseGeometry D).trace z a)

/-- The actual normalized corner Haar vector in the centered base space. -/
def baseHaarLetter (n : ℕ) : centeredSubspace (G.baseVector D 1) :=
  ⟨G.baseVector D (haarCornerLetter z a n),
    tracial_vector_mem_centered (G.baseGeometry D).trace (G.baseGeometry D).vector
      (G.baseGeometry D).inner_vector _
      (haarCornerLetter_trace_zero (G.baseGeometry D).trace z ha htrace hhaar n)⟩

@[simp] theorem baseHaarLetter_coe (n : ℕ) :
    (G.baseHaarLetter D z ha htrace hhaar n : G.baseSpace D) =
      G.baseVector D (haarCornerLetter z a n) := rfl

end TracialCornerGeometry

end KadisonSimilarity

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_Tracial_TracialSpectralNorm
attribute [-instance] _root_.OAI.UltrapowerBridge.instStarTracialQuotient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The narrow spectral arc has the required small norm in the original
algebra. Its creation model is applied on the closed algebra generated by
the two corner factors, with the normalized restricted trace. -/

noncomputable section
namespace KadisonSimilarity

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace CStarCorner

instance isClosed_subalgebra (p : P) (hp : IsStarProjection p)
    (A : StarSubalgebra ℂ P) (hpA : p ∈ A) [IsClosed (A : Set P)] :
    IsClosed (subalgebra p hp A hpA : Set (CStarCorner p hp)) :=
  (show IsClosed (A : Set P) from inferInstance).preimage continuous_subtype_val

end CStarCorner

end KadisonSimilarity

end

end OAI
end


