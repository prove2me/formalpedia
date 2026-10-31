-- Prove2me | Definitions.Def_OAIQ025S000
-- name    : OAIQ025S000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T21:45:51.299948+00:00
-- url     : https://prove2.me/theorems/99f7c8e1-1024-4869-80d3-f074d6a5b34a
-- title:
--   Definitions bundle OAIQ025S000 of the split of OpenAI, Symmetry of semialgebraic bounded domains with compact quotient (result family 058)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Release061.main`, carved from OpenAI's openai/math development (OpenAI, *Symmetry of semialgebraic bounded domains with compact quotient (result family 058)*, OpenAI Math Release, September 24, 2026, result family 58, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 292 declarations of OpenAI's Lean: 98 definitions, 2 inductive types or structures, 10 instances and 182 theorems. The definitions and types are `OAI.Complexification.imagPart`, `OAI.Complexification.ofReal`, `OAI.Complexification.realPart`, `OAI.LieAlgebra.innerExp`, `OAI.LieAlgebra.leftInner`, `OAI.Release061.ActualCriticalChart`, `OAI.Release061.ActualCriticalChart.ambientCovector`, `OAI.Release061.ActualCriticalChart.fiberAffine`, `OAI.Release061.ActualCriticalChart.maxLocus`, `OAI.Release061.ActualCriticalChart.param`, `OAI.Release061.AnalyticGerm`, `OAI.Release061.AnalyticLift.coefficient`, `OAI.Release061.AnalyticLift.monomial`, `OAI.Release061.AnalyticLift.series`, `OAI.Release061.Biholomorph.ComplexGenerators`, `OAI.Release061.Biholomorph.IsCompleteGenerator`, `OAI.Release061.Biholomorph.ModelIndex`, `OAI.Release061.Biholomorph.WeightedLieModel`, `OAI.Release061.Biholomorph.WeightedLieModel.E`, `OAI.Release061.Biholomorph.WeightedLieModel.H`, `OAI.Release061.Biholomorph.WeightedLieModel.T`, `OAI.Release061.Biholomorph.WeightedLieModel.center`, `OAI.Release061.Biholomorph.WeightedLieModel.complexificationRatLieAlgebra`, `OAI.Release061.Biholomorph.WeightedLieModel.firstJet`, `OAI.Release061.Biholomorph.WeightedLieModel.grade`, `OAI.Release061.Biholomorph.WeightedLieModel.jet`, `OAI.Release061.Biholomorph.WeightedLieModel.lowerHalf`, `OAI.Release061.Biholomorph.WeightedLieModel.lowerOneSquared`, `OAI.Release061.Biholomorph.WeightedLieModel.point`, `OAI.Release061.Biholomorph.WeightedLieModel.u`, `OAI.Release061.Biholomorph.ambientAut`, `OAI.Release061.Biholomorph.ambientFirstJet`, `OAI.Release061.Biholomorph.ambientMap`, `OAI.Release061.Biholomorph.autTransport`, `OAI.Release061.Biholomorph.compactOpenPair`, `OAI.Release061.Biholomorph.completeGeneratorBracket`, `OAI.Release061.Biholomorph.completeGeneratorFirstJet`, `OAI.Release061.Biholomorph.completeGeneratorSpace`, `OAI.Release061.Biholomorph.complexGeneratorField`, `OAI.Release061.Biholomorph.coordinateField` and 60 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `SymmetricDomains_ActionAutomorphismHomRange`, `SymmetricDomains_AdNilpotentPositiveDilations`, `SymmetricDomains_AffineProductCoordinates`, `SymmetricDomains_AmbientInverse`, `SymmetricDomains_AnalyticMulZeroGerm`, `SymmetricDomains_AnalyticNhdDifferentiableAffine`, `SymmetricDomains_AnalyticSecondJetCoordinates`, `SymmetricDomains_Basic`, `SymmetricDomains_BoundaryInjective`, `SymmetricDomains_CartanUniqueness`, `SymmetricDomains_CompactFaithfulIsotropy`, `SymmetricDomains_CompleteGeneratorLieAlgebra`, `SymmetricDomains_ConsistentIteratesTendsto`, `SymmetricDomains_ContinuityPrinciple`, `SymmetricDomains_ContinuousAutTransport`, `SymmetricDomains_ContinuousFderivLocallyUniform`, `SymmetricDomains_CoordinateFieldApply`, `SymmetricDomains_CoordinateFieldLinear`, `SymmetricDomains_CriticalAffineBundleNeighborhood`, `SymmetricDomains_CriticalCountableCharts`, `SymmetricDomains_CurvePowerDisplacement`, `SymmetricDomains_CurveUniformConsistency`, `SymmetricDomains_DiscCompactness`, `SymmetricDomains_DiscRelationCompactLocal`, `SymmetricDomains_DivisibleAutomorphismsSubsequence`, `SymmetricDomains_EulerSpectrum`, `SymmetricDomains_EventuallyImageBallNonzero`, `SymmetricDomains_FieldSecondJet`, `SymmetricDomains_FiniteDimensionalCompleteGenerator`, `SymmetricDomains_FlatWeightedEuler`, `SymmetricDomains_FlowWordFirstJet`, `SymmetricDomains_GeneratorPushForwardLinear`, `SymmetricDomains_HolomorphicLocallyUniformLimit`, `SymmetricDomains_ImagPartLieReal`, `SymmetricDomains_IndependentConormals`, `SymmetricDomains_InfinitesimalGeneratorEquivariant`, `SymmetricDomains_InnerExp`, `SymmetricDomains_IterateAverageCoboundary`, `SymmetricDomains_LocalAutomorphismODEGroup`, `SymmetricDomains_LocalRealHomExtension`, `SymmetricDomains_MaximizerBundleBorel`, `SymmetricDomains_ModelComplexField`, `SymmetricDomains_ModelNormalTranslationAd`, `SymmetricDomains_ModelRotationWeight`, `SymmetricDomains_MontelExpandingDomains`, `SymmetricDomains_OneKernel`, `SymmetricDomains_OneParameterDifferentiableZero`, `SymmetricDomains_OneParameterFderivDeriv`, `SymmetricDomains_OneParameterGeneratorAdd`, `SymmetricDomains_OneParameterJointStrict`, `SymmetricDomains_OneParameterOneGenerator`, `SymmetricDomains_ParameterPeakMaximizer`, `SymmetricDomains_PositiveReal`, `SymmetricDomains_ProductCurveLocalAutomorphism`, `SymmetricDomains_ProductCurveLocalFlow`, `SymmetricDomains_ProjectedJetSequencesNot`, `SymmetricDomains_PushForwardGeneratorDeriv`, `SymmetricDomains_RatLieAlgebra`, `SymmetricDomains_RealCriticalMatrix`, `SymmetricDomains_ScalingExpanding`, `SymmetricDomains_TendstoAmbientLocallyUniformly`, `SymmetricDomains_UniformCurveTaylor`, `SymmetricDomains_VectorLift`, `SymmetricDomains_WeightedTaylorUniformlyCompact`, `SymmetricDomains_WeightedUnscaleC1Error`.
--
--   **Imports.** It imports the published bundle `Def_SymmetricDomains`.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ025S003`; the statements `OAI.Release061.Biholomorph.WeightedLieModel.exists_positive_real`, `OAI.Release061.Biholomorph.exists_actual_aut_chart_unimodular_jacobian`, `OAI.Release061.Biholomorph.hermitian_model_bounded_symmetric`, `OAI.Release061.original_supported_hermitian_model` and `OAI.Release061.prime_boundary_generic_fiber`; the proofs of `OAI.Release061.NashPatch.null_nonsmallgood_generic`, `OAI.Release061.original_small_slope_good_supported_boundary` and `OAI.Release061.prime_boundary_generic_fiber`.
-- source:
--   OpenAI, Symmetry of semialgebraic bounded domains with compact quotient (result family 058), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 58; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symmetry-of-semialgebraic-bounded-domains-with-compact-quotient-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Definitions.Def_SymmetricDomains

section
-- module Solutions.OAIQ025_SD.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    dite p a b = b h := dif_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_Basic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace Release061

theorem exists_compact_orbit_representatives
    {X Γ : Type*} [TopologicalSpace X] [LocallyCompactSpace X]
    [Group Γ] [MulAction Γ X] [ContinuousConstSMul Γ X]
    [CompactSpace (Quotient (MulAction.orbitRel Γ X))] :
    ∃ K : Set X, IsCompact K ∧ ∀ x : X, ∃ y ∈ K, ∃ γ : Γ, γ • y = x := by
  classical
  choose K hK hKn using fun x : X => exists_compact_mem_nhds x
  let q : X → Quotient (MulAction.orbitRel Γ X) := Quotient.mk _
  have hq : IsOpenMap q := MulAction.isOpenQuotientMap_quotientMk.isOpenMap
  have hcover : (Set.univ : Set (Quotient (MulAction.orbitRel Γ X))) ⊆
      ⋃ x : X, q '' interior (K x) := by
    intro a _
    obtain ⟨x, rfl⟩ := Quotient.mk_surjective a
    exact Set.mem_iUnion.mpr ⟨x, ⟨x, mem_interior_iff_mem_nhds.mpr (hKn x), rfl⟩⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun x : X => q '' interior (K x)) (fun _ => hq _ isOpen_interior) hcover
  refine ⟨⋃ x ∈ s, K x, s.finite_toSet.isCompact_biUnion (fun x _ => hK x), ?_⟩
  intro x
  obtain ⟨a, ha⟩ := Set.mem_iUnion.mp (hs (Set.mem_univ (q x)))
  obtain ⟨has, y, hy, hxy⟩ := Set.mem_iUnion.mp ha
  refine ⟨y, Set.mem_iUnion.mpr ⟨a, Set.mem_iUnion.mpr
    ⟨has, interior_subset hy⟩⟩, ?_⟩
  exact MulAction.mem_orbit_iff.mp
    (MulAction.orbitRel_apply.mp (Quotient.eq.mp hxy.symm))

theorem HolomorphicOnSubset.continuous {n m : ℕ} {S : Set (Affine n)}
    {f : S → Affine m} (hf : HolomorphicOnSubset S f) : Continuous f := by
  rw [continuous_iff_continuousAt]
  intro p
  obtain ⟨W, hWo, hpW, F, hF, hFeq⟩ := hf p
  apply ((hF _ hpW).continuousAt.comp continuousAt_subtype_val).congr
  filter_upwards [continuousAt_subtype_val.preimage_mem_nhds (hWo.mem_nhds hpW)] with q hq
  exact hFeq q hq

theorem HolomorphicOnSubset.comp {n m l : ℕ}
    {S : Set (Affine n)} {T : Set (Affine m)}
    {f : S → T} {g : T → Affine l}
    (hg : HolomorphicOnSubset T g)
    (hf : HolomorphicOnSubset S (fun p => (f p : Affine m))) :
    HolomorphicOnSubset S (g ∘ f) := by
  intro p
  obtain ⟨W, hWo, hpW, F, hF, hFeq⟩ := hf p
  obtain ⟨V, hVo, hpV, G, hG, hGeq⟩ := hg (f p)
  have hFp : F p = (f p : Affine m) := hFeq p hpW
  have hFV : F ⁻¹' V ∈ nhds (p : Affine n) :=
    (hF _ hpW).continuousAt.preimage_mem_nhds (by simpa [hFp] using hVo.mem_nhds hpV)
  obtain ⟨O, hOV, hOo, hpO⟩ := mem_nhds_iff.mp hFV
  refine ⟨W ∩ O, hWo.inter hOo, ⟨hpW, hpO⟩, G ∘ F,
    hG.comp (hF.mono Set.inter_subset_left) (fun x hx => hOV hx.2), ?_⟩
  intro q hq
  change G (F q) = g (f q)
  rw [hFeq q hq.1]
  apply hGeq
  simpa [hFeq q hq.1] using hOV hq.2

theorem holomorphicOnSubset_val {n : ℕ} (S : Set (Affine n)) :
    HolomorphicOnSubset S Subtype.val := by
  intro p
  exact ⟨Set.univ, isOpen_univ, Set.mem_univ _, id,
    analyticOnNhd_id, fun _ _ => rfl⟩

namespace Biholomorph

noncomputable def refl {n : ℕ} (S : Set (Affine n)) : Biholomorph S S where
  toHomeomorph := Homeomorph.refl S
  holomorphic_toFun := holomorphicOnSubset_val S
  holomorphic_invFun := holomorphicOnSubset_val S

noncomputable def symm {n m : ℕ} {S : Set (Affine n)} {T : Set (Affine m)}
    (e : Biholomorph S T) : Biholomorph T S where
  toHomeomorph := e.toHomeomorph.symm
  holomorphic_toFun := e.holomorphic_invFun
  holomorphic_invFun := e.holomorphic_toFun

noncomputable def trans {n m l : ℕ} {S : Set (Affine n)} {T : Set (Affine m)}
    {R : Set (Affine l)} (e : Biholomorph S T) (f : Biholomorph T R) :
    Biholomorph S R where
  toHomeomorph := e.toHomeomorph.trans f.toHomeomorph
  holomorphic_toFun := f.holomorphic_toFun.comp e.holomorphic_toFun
  holomorphic_invFun := e.holomorphic_invFun.comp f.holomorphic_invFun

end Biholomorph

end Release061

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_AmbientInverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Release061
open Set Filter Topology
open Set Filter Metric MeasureTheory
open scoped Topology
open Polynomial
open Polynomial Algebra
open scoped nonZeroDivisors
open Polynomial Algebra

theorem holomorphicOnSubset_of_analyticOnNhd {n m : ℕ} {S : Set (Affine n)}
    {F : Affine n → Affine m} (hF : AnalyticOnNhd ℂ F S) :
    HolomorphicOnSubset S (fun x => F x.val) := by
  intro q
  obtain ⟨r,hr,hFr⟩ := (hF q q.property).exists_ball_analyticOnNhd
  exact ⟨Metric.ball q.val r,Metric.isOpen_ball,Metric.mem_ball_self hr,F,hFr,fun _ _ => rfl⟩

noncomputable def biholomorphOfAmbientInverse {n m : ℕ}
    (S : Set (Affine n)) (D : Set (Affine m))
    (F : Affine n → Affine m) (G : Affine m → Affine n)
    (hF : AnalyticOnNhd ℂ F S) (hG : AnalyticOnNhd ℂ G D)
    (hFD : MapsTo F S D) (hGS : MapsTo G D S)
    (hGF : ∀ x ∈ S, G (F x) = x) (hFG : ∀ y ∈ D, F (G y) = y) :
    Biholomorph S D where
  toHomeomorph := {
    toEquiv := {
      toFun := fun x => ⟨F x.val,hFD x.property⟩
      invFun := fun y => ⟨G y.val,hGS y.property⟩
      left_inv := fun x => Subtype.ext (hGF x x.property)
      right_inv := fun y => Subtype.ext (hFG y y.property) }
    continuous_toFun := (continuousOn_iff_continuous_domRestrict.mp hF.continuousOn).subtype_mk _
    continuous_invFun := (continuousOn_iff_continuous_domRestrict.mp hG.continuousOn).subtype_mk _ }
  holomorphic_toFun := holomorphicOnSubset_of_analyticOnNhd hF
  holomorphic_invFun := holomorphicOnSubset_of_analyticOnNhd hG

end Release061

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_DiscRelationCompactLocal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Release061
open Set Filter Topology
open Set Filter Metric MeasureTheory
open scoped Topology
open Polynomial
open Polynomial Algebra
open scoped nonZeroDivisors
open Polynomial Algebra

noncomputable def coordinateEnergy {n : ℕ} (z : Affine n) : ℝ := ∑ i, ‖z i‖ ^ 2

section IntrinsicCompactness
open Set Metric Filter
open scoped Topology Classical

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def DiscRelation (S : Set E) (r : ℝ) (x y : S) : Prop :=
  ∃ f : ℂ → E, DifferentiableOn ℂ f (ball 0 1) ∧ MapsTo f (ball 0 1) S ∧
    ∃ a b : ℂ, ‖a‖ < r ∧ ‖b‖ < r ∧ f a = x.val ∧ f b = y.val

theorem discRelation_symm {S : Set E} {r : ℝ} {x y : S}
    (h : DiscRelation S r x y) : DiscRelation S r y x := by
  obtain ⟨f,hf,hS,a,b,ha,hb,hax,hby⟩ := h
  exact ⟨f,hf,hS,b,a,hb,ha,hby,hax⟩

theorem discRelation_dist_le {S : Set E} {r M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ x ∈ S, ‖x‖ ≤ M) (hr : r ≤ 1/8)
    {x y : S} (h : DiscRelation S r x y) : dist x y ≤ 8*M*r := by
  obtain ⟨f,hf,hS,a,b,ha,hb,hax,hby⟩ := h
  have har : ‖a‖ < 1/8 := ha.trans_le hr
  have hbr : ‖b‖ < 1/8 := hb.trans_le hr
  have haball : ball a (1/2 : ℝ) ⊆ ball (0 : ℂ) 1 := by
    intro z hz
    rw [mem_ball,dist_zero_right]
    have ht := norm_le_norm_sub_add z a
    rw [mem_ball,dist_eq_norm] at hz
    linarith
  have hfa : a ∈ ball (0 : ℂ) 1 := by simpa using (har.trans (by norm_num : (1:ℝ)/8 < 1))
  have hmaps : MapsTo f (ball a (1/2 : ℝ)) (closedBall (f a) (2*M)) := by
    intro z hz
    rw [mem_closedBall,dist_eq_norm]
    exact (norm_sub_le _ _).trans (by linarith [hbound _ (hS (haball hz)),hbound _ (hS hfa)])
  have hba : b ∈ ball a (1/2 : ℝ) := by
    rw [mem_ball,dist_eq_norm]
    exact (norm_sub_le _ _).trans_lt (by linarith)
  have hd := Complex.dist_le_div_mul_dist_of_mapsTo_ball (hf.mono haball) hmaps hba
  have hab : dist b a ≤ 2*r := by
    rw [dist_eq_norm]
    exact (norm_sub_le _ _).trans (by linarith)
  calc
    dist x y = dist (f b) (f a) := by rw [hax,hby]; exact dist_comm _ _
    _ ≤ (2*M/(1/2)) * dist b a := hd
    _ ≤ (2*M/(1/2)) * (2*r) := mul_le_mul_of_nonneg_left hab (by positivity)
    _ = 8*M*r := by ring

theorem bounded_disc_relation_compact_local {S : Set E} [LocallyCompactSpace S]
    (hbounded : Bornology.IsBounded S) {K : Set S} (hK : IsCompact K) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1/8 ∧ ∃ L : Set S, IsCompact L ∧
      ∀ x ∈ K, ∀ y, DiscRelation S r x y → y ∈ L := by
  obtain ⟨ε,hε,hcompact⟩ := hK.exists_isCompact_cthickening
  obtain ⟨M,hM,hbound⟩ := hbounded.exists_pos_norm_le
  let r := min (1/8 : ℝ) (ε/(16*M))
  have hr : 0 < r := lt_min (by norm_num) (div_pos hε (by positivity))
  have hrsmall : r ≤ 1/8 := min_le_left _ _
  have hrε : 8*M*r < ε := by
    have hh : r ≤ ε/(16*M) := min_le_right _ _
    have hh' := (le_div_iff₀ (by positivity : 0 < 16*M)).mp hh
    nlinarith
  refine ⟨r,hr,hrsmall,cthickening ε K,hcompact,?_⟩
  intro x hx y hxy
  apply thickening_subset_cthickening ε K
  apply mem_thickening_iff.mpr
  refine ⟨x,hx,?_⟩
  rw [dist_comm]
  exact (discRelation_dist_le hM.le hbound hrsmall hxy).trans_lt hrε

end IntrinsicCompactness
end Release061

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_DiscCompactness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Release061
open Set Filter Topology
open Set Filter Metric MeasureTheory
open scoped Topology
open Polynomial
open Polynomial Algebra
open scoped nonZeroDivisors
open Polynomial Algebra
section IntrinsicCompactness
open Set Metric Filter
open scoped Topology Classical
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]


theorem HolomorphicOnSubset.differentiableOn_disc_comp {n m : ℕ}
    {S : Set (Affine n)} {g : S → Affine m} (hg : HolomorphicOnSubset S g)
    {f : ℂ → Affine n} (hf : DifferentiableOn ℂ f (ball 0 1))
    (hS : MapsTo f (ball 0 1) S) :
    DifferentiableOn ℂ (fun z => if hz : f z ∈ S then g ⟨f z,hz⟩ else 0) (ball 0 1) := by
  intro z hz
  obtain ⟨W,hW,hzW,G,hG,he⟩ := hg ⟨f z,hS hz⟩
  have hfz := hf.differentiableAt (isOpen_ball.mem_nhds hz)
  have hcomp := (hG (f z) hzW).differentiableAt.comp z hfz
  apply DifferentiableAt.differentiableWithinAt
  apply hcomp.congr_of_eventuallyEq
  filter_upwards [isOpen_ball.mem_nhds hz,
    hfz.continuousAt.preimage_mem_nhds (hW.mem_nhds hzW)] with w hw hwW
  simp only [dite_eq_left (hS hw),Function.comp_apply]
  exact (he ⟨f w,hS hw⟩ hwW).symm

theorem DiscRelation.map {n m : ℕ} {S : Set (Affine n)} {T : Set (Affine m)}
    {g : S → T} (hg : HolomorphicOnSubset S (fun p => (g p).val))
    {r : ℝ} (hr : r ≤ 1) {x y : S} (h : DiscRelation S r x y) :
    DiscRelation T r (g x) (g y) := by
  classical
  obtain ⟨f,hf,hS,a,b,ha,hb,hax,hby⟩ := h
  let F : ℂ → Affine m := fun z => if hz : f z ∈ S then (g ⟨f z,hz⟩).val else 0
  have hF := hg.differentiableOn_disc_comp hf hS
  have ha1 : a ∈ ball (0 : ℂ) 1 := by simpa using ha.trans_le hr
  have hb1 : b ∈ ball (0 : ℂ) 1 := by simpa using hb.trans_le hr
  refine ⟨F,hF,?_,a,b,ha,hb,?_,?_⟩
  · intro z hz
    simpa only [F,dite_eq_left (hS hz)] using (g ⟨f z,hS hz⟩).property
  · have he : (⟨f a,hS ha1⟩ : S) = x := Subtype.ext hax
    simp only [F,dite_eq_left (hS ha1),he]
  · have he : (⟨f b,hS hb1⟩ : S) = y := Subtype.ext hby
    simp only [F,dite_eq_left (hS hb1),he]

theorem DiscRelation.mono {S T : Set E} (hST : S ⊆ T) {r : ℝ} {x y : S}
    (h : DiscRelation S r x y) :
    DiscRelation T r ⟨x.val,hST x.property⟩ ⟨y.val,hST y.property⟩ := by
  obtain ⟨f,hf,hS,a,b,ha,hb,hax,hby⟩ := h
  exact ⟨f,hf,hS.mono_right hST,a,b,ha,hb,hax,hby⟩

theorem discRelation_closedBall {x y : E} {ε r : ℝ} (hε : 0 < ε) (hr : 0 < r)
    (hr1 : r ≤ 1) (hxy : dist y x < ε*r/2) :
    ∃ hx : x ∈ closedBall x ε, ∃ hy : y ∈ closedBall x ε,
      DiscRelation (closedBall x ε) r ⟨x,hx⟩ ⟨y,hy⟩ := by
  let a : ℂ := (r/2 : ℝ)
  have ha : ‖a‖ = r/2 := by simp [a,hr.le]
  have ha0 : a ≠ 0 := by intro h; rw [h,_root_.norm_zero] at ha; linarith
  let v : E := a⁻¹ • (y-x)
  have hv : ‖v‖ < ε := by
    rw [norm_smul,_root_.norm_inv,ha,inv_mul_eq_div]
    apply (div_lt_iff₀ (half_pos hr)).mpr
    rw [← dist_eq_norm]
    nlinarith
  let f : ℂ → E := fun z => x + z • v
  have hf : Differentiable ℂ f := by dsimp [f]; fun_prop
  have hmaps : MapsTo f (ball 0 1) (closedBall x ε) := by
    intro z hz
    rw [mem_ball,dist_zero_right] at hz
    rw [mem_closedBall,dist_eq_norm]
    simp only [f,add_sub_cancel_left,norm_smul]
    exact ((mul_le_mul_of_nonneg_right hz.le (norm_nonneg v)).trans_eq (one_mul _)).trans hv.le
  have hx : x ∈ closedBall x ε := mem_closedBall_self hε.le
  have hy : y ∈ closedBall x ε := by
    rw [mem_closedBall]
    have : ε*r ≤ ε := mul_le_of_le_one_right hε.le hr1
    linarith
  refine ⟨hx,hy,f,hf.differentiableOn,hmaps,0,a,by simpa using hr,by rw [ha]; linarith,?_,?_⟩
  · simp [f]
  · simp [f,v,smul_smul,ha0]

theorem open_small_disc_carrier [ProperSpace E] {S : Set E} (hS : IsOpen S)
    {x : E} (hx : x ∈ S) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ K : Set E, IsCompact K ∧ K ⊆ S ∧ ∃ hxK : x ∈ K,
      ∀ y, dist y x < δ → ∃ hy : y ∈ K,
        DiscRelation K r ⟨x,hxK⟩ ⟨y,hy⟩ := by
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp hS x hx
  let K := closedBall x (ε/2)
  have hK : K ⊆ S := (closedBall_subset_ball (half_lt_self hε)).trans hball
  refine ⟨(ε/2)*r/2,by positivity,K,(isCompact_closedBall _ _),hK,mem_closedBall_self (by positivity),?_⟩
  intro y hy
  obtain ⟨_,hyK,hrel⟩ := discRelation_closedBall (half_pos hε) hr hr1 hy
  exact ⟨hyK,hrel⟩

open scoped Pointwise

theorem compact_relation_step {X G : Type*} [TopologicalSpace X] [TopologicalSpace G]
    [Group G] [DiscreteTopology G] [MulAction G X] [ProperSMul G X]
    [ContinuousConstSMul G X] (R : X → X → Prop)
    (hR : ∀ (g : G) (x y : X), R x y → R (g • x) (g • y))
    (K L : Set X) (hK : IsCompact K) (hL : IsCompact L)
    (hrep : ∀ x : X, ∃ k ∈ K, ∃ g : G, g • k = x)
    (hlocal : ∀ x ∈ K, ∀ y, R x y → y ∈ L)
    {C : Set X} (hC : IsCompact C) :
    ∃ M : Set X, IsCompact M ∧ ∀ x ∈ C, ∀ y, R x y → y ∈ M := by
  classical
  let A : Set G := {g | (g • K ∩ C).Nonempty}
  have hA : A.Finite := isCompact_iff_finite.mp (ProperSMul.isCompact_setOfPred_inter_nonempty hK hC)
  refine ⟨⋃ g ∈ A, g • L, hA.isCompact_biUnion (fun g _ => hL.image (continuous_const_smul g)),?_⟩
  intro x hx y hxy
  obtain ⟨k,hk,g,rfl⟩ := hrep x
  have hg : g ∈ A := ⟨g • k,⟨mem_smul_set.mpr ⟨k,hk,rfl⟩,hx⟩⟩
  have hr : R k (g⁻¹ • y) := by simpa using hR g⁻¹ (g • k) y hxy
  exact mem_iUnion.mpr ⟨g,mem_iUnion.mpr ⟨hg,mem_smul_set.mpr
    ⟨g⁻¹ • y,hlocal k hk _ hr,smul_inv_smul g y⟩⟩⟩

theorem compact_images_of_local_relation {X Y I : Type*}
    [TopologicalSpace X] [PreconnectedSpace X] [TopologicalSpace Y]
    (R : Y → Y → Prop) (hsym : ∀ x y, R x y → R y x)
    (hstep : ∀ C : Set Y, IsCompact C → ∃ M : Set Y,
      IsCompact M ∧ ∀ x ∈ C, ∀ y, R x y → y ∈ M)
    (F : I → X → Y) (l : Filter I) (x₀ : X)
    (hbase : ∃ C : Set Y, IsCompact C ∧ ∀ᶠ i in l, F i x₀ ∈ C)
    (hlocal : ∀ x, ∃ O ∈ 𝓝 x, ∀ᶠ i in l, ∀ y ∈ O, R (F i x) (F i y))
    {E : Set X} (hE : IsCompact E) :
    ∃ M : Set Y, IsCompact M ∧ ∀ᶠ i in l, ∀ x ∈ E, F i x ∈ M := by
  classical
  let P : X → Prop := fun x => ∃ C : Set Y, IsCompact C ∧ ∀ᶠ i in l, F i x ∈ C
  have hforward : ∀ x, P x → ∃ O ∈ 𝓝 x, ∃ M : Set Y,
      IsCompact M ∧ ∀ᶠ i in l, ∀ y ∈ O, F i y ∈ M := by
    intro x hx
    obtain ⟨C,hC,hxc⟩ := hx
    obtain ⟨O,hO,hrel⟩ := hlocal x
    obtain ⟨M,hM,hm⟩ := hstep C hC
    exact ⟨O,hO,M,hM,by
      filter_upwards [hxc,hrel] with i hi hri
      exact fun y hy => hm _ hi _ (hri y hy)⟩
  have hopen : IsOpen {x | P x} := by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    obtain ⟨O,hO,M,hM,hm⟩ := hforward x hx
    apply mem_of_superset hO
    intro y hy
    exact ⟨M,hM,hm.mono (fun _ hi => hi y hy)⟩
  have hclosed : IsClosed {x | P x} := by
    rw [← isOpen_compl_iff,isOpen_iff_mem_nhds]
    intro x hx
    obtain ⟨O,hO,hrel⟩ := hlocal x
    apply mem_of_superset hO
    intro y hy hPy
    obtain ⟨C,hC,hc⟩ := hPy
    obtain ⟨M,hM,hm⟩ := hstep C hC
    apply hx
    refine ⟨M,hM,?_⟩
    filter_upwards [hc,hrel] with i hi hri
    exact hm _ hi _ (hsym _ _ (hri y hy))
  have hall : ∀ x, P x := by
    have he := IsClopen.eq_univ ⟨hclosed,hopen⟩ (show {x | P x}.Nonempty from ⟨x₀,hbase⟩)
    intro x
    change x ∈ {x | P x}
    rw [he]
    trivial
  choose O hO M hM hm using fun x => hforward x (hall x)
  obtain ⟨J,_,hJ⟩ := hE.elim_nhds_subcover O (fun x _ => hO x)
  refine ⟨⋃ x ∈ J, M x,J.finite_toSet.isCompact_biUnion (fun x _ => hM x),?_⟩
  have hev : ∀ᶠ i in l, ∀ x ∈ J, ∀ y ∈ O x, F i y ∈ M x := by
    exact (Filter.eventually_all_finset J).mpr (fun point _ => hm point)
  filter_upwards [hev] with i hi
  intro y hy
  obtain ⟨x,hx,hxy⟩ := mem_iUnion₂.mp (hJ hy)
  exact mem_iUnion₂.mpr ⟨x,hx,hi x hx y hxy⟩

def LocallyEventuallyHolomorphic {d n : ℕ} {I : Type*}
    (S : Set (Affine d)) (U : Set (Affine n)) (F : I → S → U) (l : Filter I) : Prop :=
  ∀ x : S, ∃ W : Set (Affine d), IsOpen W ∧ x.val ∈ W ∧ ∃ hWS : W ⊆ S,
    ∀ᶠ i in l, HolomorphicOnSubset W (fun p => (F i ⟨p.val,hWS p.property⟩).val)

theorem bounded_cocompact_holomorphic_family_compact {d n : ℕ} {I Γ : Type*}
    (S : Set (Affine d)) (_hS : IsOpen S) (hconn : IsPreconnected S)
    (U : Set (Affine n)) [LocallyCompactSpace U]
    (hbounded : Bornology.IsBounded U)
    [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ] [MulAction Γ U] [ProperSMul Γ U]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val))
    (K : Set U) (hK : IsCompact K) (hrep : ∀ x : U, ∃ k ∈ K, ∃ γ : Γ, γ • k = x)
    (F : I → S → U) (l : Filter I) (x₀ : S)
    (hbase : ∃ C : Set U, IsCompact C ∧ ∀ᶠ i in l, F i x₀ ∈ C)
    (hF : LocallyEventuallyHolomorphic S U F l)
    {E : Set S} (hE : IsCompact E) :
    ∃ M : Set U, IsCompact M ∧ ∀ᶠ i in l, ∀ x ∈ E, F i x ∈ M := by
  let : PreconnectedSpace S := isPreconnected_iff_preconnectedSpace.mp hconn
  let : ContinuousConstSMul Γ U := ⟨fun γ => (hhol γ).continuous.subtype_mk _⟩
  obtain ⟨r,hr,hrsmall,L,hL,hlocal⟩ := bounded_disc_relation_compact_local hbounded hK
  have hr1 : r ≤ 1 := hrsmall.trans (by norm_num)
  have hstep : ∀ C : Set U, IsCompact C → ∃ M : Set U, IsCompact M ∧
      ∀ x ∈ C, ∀ y, DiscRelation U r x y → y ∈ M := by
    intro C hC
    exact compact_relation_step (G := Γ) (DiscRelation U r)
      (fun γ x y hxy => hxy.map (hhol γ) hr1) K L hK hL hrep hlocal hC
  apply compact_images_of_local_relation (DiscRelation U r)
    (fun _ _ hxy => discRelation_symm hxy) hstep F l x₀ hbase
    (E := E) (hE := hE)
  intro x
  obtain ⟨W,hW,hxW,hWS,hFW⟩ := hF x
  obtain ⟨δ,hδ,Q,_hQ,hQW,hxQ,hQrel⟩ := open_small_disc_carrier hW hxW hr hr1
  refine ⟨Metric.ball x δ,Metric.ball_mem_nhds x hδ,?_⟩
  filter_upwards [hFW] with i hi
  intro y hy
  obtain ⟨hyQ,hxy⟩ := hQrel y.val (show dist y.val x.val < δ from hy)
  exact (hxy.mono hQW).map (g := fun p : W => F i ⟨p.val,hWS p.property⟩) hi hr1

end IntrinsicCompactness

open Set

end Release061

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_ContinuityPrinciple
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Release061
open Set Filter Topology
open Set Filter Metric MeasureTheory
open scoped Topology
open Polynomial
open Polynomial Algebra
open scoped nonZeroDivisors
open Polynomial Algebra
open Set

theorem bounded_cocompact_holomorphic_family_limit {d n : ℕ} {I Γ : Type*}
    (S : Set (Affine d)) (hS : IsOpen S) (hconn : IsPreconnected S)
    (U : Set (Affine n)) [LocallyCompactSpace U]
    (hbounded : Bornology.IsBounded U)
    [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ] [MulAction Γ U] [ProperSMul Γ U]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val))
    (K : Set U) (hK : IsCompact K) (hrep : ∀ x : U, ∃ k ∈ K, ∃ γ : Γ, γ • k = x)
    (F : I → S → U) (l : Filter I) [l.NeBot] (x₀ : S)
    (hbase : ∃ C : Set U, IsCompact C ∧ ∀ᶠ i in l, F i x₀ ∈ C)
    (hF : LocallyEventuallyHolomorphic S U F l)
    (g : S → Affine n) (hg : ∀ x, Tendsto (fun i => (F i x).val) l (𝓝 (g x))) :
    ∀ x, g x ∈ U := by
  intro x
  obtain ⟨M,hM,hFM⟩ := bounded_cocompact_holomorphic_family_compact S hS hconn U
    hbounded hhol K hK hrep F l x₀ hbase hF (E := {x}) isCompact_singleton
  have hcl : IsClosed ((Subtype.val : U → Affine n) '' M) :=
    (hM.image continuous_subtype_val).isClosed
  have hmem := hcl.mem_of_tendsto (hg x) (hFM.mono fun i hi =>
    mem_image_of_mem Subtype.val (hi x (mem_singleton x)))
  obtain ⟨y,_hy,he⟩ := hmem
  rw [← he]
  exact y.property

theorem HolomorphicOnSubset.locallyEventually {d n : ℕ} {I : Type*}
    {S : Set (Affine d)} {U : Set (Affine n)} (hS : IsOpen S)
    {F : I → S → U} (hF : ∀ i, HolomorphicOnSubset S (fun x => (F i x).val))
    (l : Filter I) : LocallyEventuallyHolomorphic S U F l := by
  intro x
  exact ⟨S,hS,x.property,Subset.rfl,Eventually.of_forall hF⟩

open Filter
open scoped Topology

end Release061

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_BoundaryInjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Metric Complex
open scoped Topology
noncomputable section
namespace Release061.Wiener
open scoped BigOperators ComplexConjugate Topology
open Set Filter

abbrev Poly := AddMonoidAlgebra ℂ ℤ

open MeasureTheory

end Release061.Wiener

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_AnalyticNhdDifferentiableAffine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


open Set Metric Complex
open scoped Topology

namespace Release061

abbrev RadiusCircle (R : ℝ) := {z : ℂ // z ∈ sphere (0 : ℂ) R}

instance radiusCircleCompact (R : ℝ) : CompactSpace (RadiusCircle R) :=
  isCompact_iff_compactSpace.mp (isCompact_sphere (0 : ℂ) R)

noncomputable def circleExtend {R : ℝ} (f : C(RadiusCircle R, ℂ)) (z : ℂ) : ℂ := by
  classical
  exact if h : z ∈ sphere (0 : ℂ) R then f ⟨z, h⟩ else 0

@[simp] theorem circleExtend_on {R : ℝ} (f : C(RadiusCircle R, ℂ))
    (z : RadiusCircle R) : circleExtend f z = f z := by
  simp [circleExtend]

theorem continuousOn_circleExtend {R : ℝ} (f : C(RadiusCircle R, ℂ)) :
    ContinuousOn (circleExtend f) (sphere (0 : ℂ) R) := by
  rw [continuousOn_iff_continuous_domRestrict]
  simpa only [Set.domRestrict_def, circleExtend_on, Set.domRestrict_apply] using f.continuous

noncomputable def circleIntegralLM (R : ℝ) (hR : 0 ≤ R) :
    C(RadiusCircle R, ℂ) →ₗ[ℂ] ℂ where
  toFun f := ∮ z in C(0, R), circleExtend f z
  map_add' f g := by
    rw [show circleExtend (f + g) = fun z => circleExtend f z + circleExtend g z by
      funext z; simp only [circleExtend]; split_ifs <;> simp]
    exact circleIntegral.integral_add
      ((continuousOn_circleExtend f).circleIntegrable hR)
      ((continuousOn_circleExtend g).circleIntegrable hR)
  map_smul' a f := by
    rw [show circleExtend (a • f) = fun z => a • circleExtend f z by
      funext z; simp only [circleExtend]; split_ifs <;> simp]
    exact circleIntegral.integral_smul a _ _ _

noncomputable def circleIntegralCLM (R : ℝ) (hR : 0 ≤ R) :
    C(RadiusCircle R, ℂ) →L[ℂ] ℂ :=
  (circleIntegralLM R hR).mkContinuous (2 * Real.pi * R) (by
    intro f
    exact circleIntegral.norm_integral_le_of_norm_le_const hR (fun z hz => by
      simpa only [circleExtend, dite_eq_left hz] using f.norm_coe_le_norm ⟨z,hz⟩))

@[simp] theorem circleIntegralCLM_apply {R : ℝ} (hR : 0 ≤ R)
    (f : C(RadiusCircle R, ℂ)) :
    circleIntegralCLM R hR f = ∮ z in C(0,R), circleExtend f z := rfl

noncomputable def cauchyFunctional (R : ℝ) (hR : 0 ≤ R) :
    C(RadiusCircle R, ℂ) →L[ℂ] ℂ :=
  (2 * Real.pi * Complex.I : ℂ)⁻¹ • circleIntegralCLM R hR

@[simp] theorem cauchyFunctional_apply {R : ℝ} (hR : 0 ≤ R)
    (f : C(RadiusCircle R, ℂ)) :
    cauchyFunctional R hR f =
      (2 * Real.pi * Complex.I : ℂ)⁻¹ • ∮ z in C(0,R), circleExtend f z := rfl

noncomputable def curryCLM (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y]
    [LocallyCompactSpace (X × Y)] : C(X × Y, ℂ) →L[ℂ] C(X, C(Y, ℂ)) where
  toFun := ContinuousMap.curry
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := ContinuousMap.continuous_curry

theorem continuousMap_ringInverse_apply {X : Type*} [TopologicalSpace X]
    (f : C(X, ℂ)) (hf : ∀ x, f x ≠ 0) (x : X) :
    Ring.inverse f x = (f x)⁻¹ := by
  let u := (ContinuousMap.isUnit_iff_forall_ne_zero f).mpr hf |>.unit
  have hu : (u : C(X,ℂ)) = f := IsUnit.unit_spec _
  rw [← hu, Ring.inverse_unit]
  have hm := congrArg (fun g : C(X,ℂ) => g x) (Units.inv_mul u)
  change (↑u⁻¹ : C(X,ℂ)) x * (u : C(X,ℂ)) x = 1 at hm
  exact eq_inv_of_mul_eq_one_left hm

def joinTorus {R : ℝ} (n : ℕ) :
    C(RadiusCircle R × (Fin n → RadiusCircle R), Fin (n+1) → RadiusCircle R) where
  toFun u := Fin.cons u.1 u.2
  continuous_toFun := by
    apply continuous_pi
    intro j
    induction j using Fin.cases with
    | zero => exact continuous_fst
    | succ i => exact (continuous_apply i).comp continuous_snd

noncomputable def iteratedCauchyFunctional (R : ℝ) (hR : 0 ≤ R) :
    (n : ℕ) → C((Fin n → RadiusCircle R), ℂ) →L[ℂ] ℂ
  | 0 => ContinuousMap.evalCLM ℂ (Fin.elim0)
  | n+1 => (cauchyFunctional R hR).comp
      ((ContinuousLinearMap.compLeftContinuous ℂ (RadiusCircle R)
          (iteratedCauchyFunctional R hR n)).comp
        ((curryCLM (RadiusCircle R) (Fin n → RadiusCircle R)).comp
          (ContinuousMap.compCLM ℂ ℂ (joinTorus n))))

@[simp] theorem iteratedCauchyFunctional_zero (R : ℝ) (hR : 0 ≤ R)
    (f : C((Fin 0 → RadiusCircle R), ℂ)) :
    iteratedCauchyFunctional R hR 0 f = f Fin.elim0 := rfl

@[simp] theorem iteratedCauchyFunctional_succ (R : ℝ) (hR : 0 ≤ R) (n : ℕ)
    (f : C((Fin (n+1) → RadiusCircle R), ℂ)) :
    iteratedCauchyFunctional R hR (n+1) f = cauchyFunctional R hR
      ((ContinuousLinearMap.compLeftContinuous ℂ (RadiusCircle R)
        (iteratedCauchyFunctional R hR n)) ((f.comp (joinTorus n)).curry)) := rfl

lemma fin_cons_differentiable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {n : ℕ} {f : E → ℂ} {g : E → Fin n → ℂ}
    (hf : Differentiable ℂ f) (hg : Differentiable ℂ g) :
    Differentiable ℂ (fun x => (Fin.cons (f x) (g x) : Fin (n+1) → ℂ)) := by
  apply differentiable_pi.mpr
  intro j
  induction j using Fin.cases with
  | zero => exact hf
  | succ j =>
      simpa only [Fin.cons_succ, Function.comp_def] using
        (differentiable_apply j : Differentiable ℂ (fun y : Fin n → ℂ => y j)).comp hg

lemma fin_cons_mem_closedBall {n : ℕ} {R : ℝ} (hR : 0 ≤ R)
    {w : ℂ} {y : Fin n → ℂ} (hw : w ∈ closedBall (0 : ℂ) R)
    (hy : y ∈ closedBall (0 : Fin n → ℂ) R) :
    Fin.cons w y ∈ closedBall (0 : Fin (n+1) → ℂ) R := by
  simp only [mem_closedBall, dist_zero_right] at *
  rw [pi_norm_le_iff_of_nonneg hR] at *
  intro j
  induction j using Fin.cases with
  | zero => exact hw
  | succ j => exact hy j

theorem iteratedCauchy_formula (n : ℕ) {R : ℝ} (hR : 0 < R)
    {f : (Fin n → ℂ) → ℂ} (hf : DifferentiableOn ℂ f (closedBall 0 R))
    {x : Fin n → ℂ} (hx : x ∈ ball 0 R)
    (G : C((Fin n → RadiusCircle R), ℂ))
    (hG : ∀ ζ, G ζ = f (fun j => (ζ j : ℂ)) * ∏ j, ((ζ j : ℂ) - x j)⁻¹) :
    iteratedCauchyFunctional R hR.le n G = f x := by
  induction n with
  | zero =>
      rw [iteratedCauchyFunctional_zero, hG]
      simp only [Finset.univ_eq_empty, Finset.prod_empty, mul_one]
      congr 1
      exact Subsingleton.elim _ _
  | succ n ih =>
      rw [iteratedCauchyFunctional_succ, cauchyFunctional_apply]
      let H := (ContinuousLinearMap.compLeftContinuous ℂ (RadiusCircle R)
        (iteratedCauchyFunctional R hR.le n)) ((G.comp (joinTorus n)).curry)
      have hx' : ∀ j, ‖x j‖ < R := (pi_norm_lt_iff hR).mp (by simpa using hx)
      have htail : Fin.tail x ∈ ball (0 : Fin n → ℂ) R := by
        simpa only [mem_ball, dist_zero_right, pi_norm_lt_iff hR, Fin.tail] using fun j : Fin n => hx' j.succ
      have hslice : ∀ w : RadiusCircle R,
          H w = ((w : ℂ) - x 0)⁻¹ * f (Fin.cons (w : ℂ) (Fin.tail x)) := by
        intro w
        change iteratedCauchyFunctional R hR.le n ((G.comp (joinTorus n)).curry w) = _
        apply ih (f := fun y => ((w : ℂ) - x 0)⁻¹ * f (Fin.cons (w : ℂ) y)) _ htail
        · intro ζ
          change G (Fin.cons w ζ) = _
          rw [hG, Fin.prod_univ_succ]
          simp only [Fin.cons_zero, Fin.cons_succ, Fin.tail]
          have hcast : (fun j : Fin (n+1) => ((Fin.cons w ζ : Fin (n+1) → RadiusCircle R) j : ℂ)) =
              (Fin.cons (w : ℂ) (fun j => (ζ j : ℂ)) : Fin (n+1) → ℂ) := by
            funext j
            induction j using Fin.cases with
            | zero => rfl
            | succ _ => rfl
          rw [hcast]
          ring
        · exact (differentiableOn_const _).mul
            (hf.comp (fin_cons_differentiable (differentiable_const (w : ℂ))
              differentiable_id).differentiableOn
              (fun y hy => fin_cons_mem_closedBall hR.le (sphere_subset_closedBall w.property) hy))
      have hext : EqOn (circleExtend H)
          (fun w : ℂ => (w - x 0)⁻¹ • f (Fin.cons w (Fin.tail x))) (sphere 0 R) := by
        intro w hw
        simpa only [circleExtend, dite_eq_left hw, smul_eq_mul] using hslice ⟨w,hw⟩
      rw [circleIntegral.integral_congr hR.le hext]
      have hd : DifferentiableOn ℂ (fun w => f (Fin.cons w (Fin.tail x))) (closedBall 0 R) :=
        hf.comp (fin_cons_differentiable differentiable_id
          (differentiable_const (Fin.tail x))).differentiableOn
          (fun w hw => fin_cons_mem_closedBall hR.le hw (ball_subset_closedBall htail))
      have hc := hd.mono closure_ball_subset_closedBall |>.diffContOnCl
      have hcf := hc.two_pi_i_inv_smul_circleIntegral_sub_inv_smul (by simpa using hx' 0)
      change _ = f (Fin.cons (x 0) (Fin.tail x)) at hcf
      rw [Fin.cons_self_tail x] at hcf
      exact hcf

def torusVal (n : ℕ) (R : ℝ) : C((Fin n → RadiusCircle R), Fin n → ℂ) where
  toFun ζ j := ζ j
  continuous_toFun := continuous_pi (fun j => continuous_subtype_val.comp (continuous_apply j))

lemma torusVal_mem_closedBall {n : ℕ} {R : ℝ} (hR : 0 ≤ R)
    (ζ : Fin n → RadiusCircle R) : torusVal n R ζ ∈ closedBall 0 R := by
  rw [mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg hR]
  intro j
  exact (by simpa only [mem_sphere, dist_zero_right] using (ζ j).property : ‖(ζ j : ℂ)‖ = R).le

noncomputable def torusBoundary {n : ℕ} {R : ℝ} (hR : 0 ≤ R)
    (f : (Fin n → ℂ) → ℂ) (hf : ContinuousOn f (closedBall 0 R)) :
    C((Fin n → RadiusCircle R), ℂ) :=
  ⟨f ∘ torusVal n R, hf.comp_continuous (torusVal n R).continuous (torusVal_mem_closedBall hR)⟩

def torusCoordinate {n : ℕ} {R : ℝ} (j : Fin n) : C((Fin n → RadiusCircle R), ℂ) :=
  ⟨fun ζ => ζ j, continuous_subtype_val.comp (continuous_apply j)⟩

noncomputable def torusResolvent {n : ℕ} {R : ℝ} (j : Fin n) (x : Fin n → ℂ) :
    C((Fin n → RadiusCircle R), ℂ) :=
  Ring.inverse (torusCoordinate j - ContinuousMap.const _ (x j))

lemma torus_difference_ne_zero {n : ℕ} {R : ℝ} (hR : 0 < R)
    {x : Fin n → ℂ} (hx : x ∈ ball 0 R) (j : Fin n) (ζ : Fin n → RadiusCircle R) :
    ((torusCoordinate (R := R) j - ContinuousMap.const _ (x j)) :
      C((Fin n → RadiusCircle R), ℂ)) ζ ≠ 0 := by
  change (ζ j : ℂ) - x j ≠ 0
  have hxi := (pi_norm_lt_iff hR).mp (by simpa using hx) j
  have hz : ‖(ζ j : ℂ)‖ = R := by simpa only [mem_sphere, dist_zero_right] using (ζ j).property
  intro he
  rw [sub_eq_zero.mp he] at hz
  exact (ne_of_lt hxi) hz

lemma torusResolvent_apply {n : ℕ} {R : ℝ} (hR : 0 < R)
    {x : Fin n → ℂ} (hx : x ∈ ball 0 R) (j : Fin n) (ζ : Fin n → RadiusCircle R) :
    torusResolvent (R := R) j x ζ = ((ζ j : ℂ) - x j)⁻¹ :=
  continuousMap_ringInverse_apply _ (torus_difference_ne_zero hR hx j) ζ

lemma analyticAt_torusResolvent {n : ℕ} {R : ℝ} (hR : 0 < R)
    {x : Fin n → ℂ} (hx : x ∈ ball 0 R) (j : Fin n) :
    AnalyticAt ℂ (torusResolvent (R := R) j) x := by
  have hu := (ContinuousMap.isUnit_iff_forall_ne_zero
    (torusCoordinate (R := R) j - ContinuousMap.const _ (x j))).mpr
    (torus_difference_ne_zero hR hx j)
  have ha : AnalyticAt ℂ
      (fun y : Fin n → ℂ => torusCoordinate (R := R) j - ContinuousMap.const _ (y j)) x :=
    analyticAt_const.sub (((ContinuousLinearMap.const ℂ (Fin n → RadiusCircle R)).comp
      (ContinuousLinearMap.proj j)).analyticAt x)
  have hi : AnalyticAt ℂ Ring.inverse
      (torusCoordinate (R := R) j - ContinuousMap.const _ (x j)) :=
    analyticOnNhd_inverse _ hu
  have hh := hi.comp (f := fun y : Fin n → ℂ => torusCoordinate (R := R) j - ContinuousMap.const _ (y j)) ha
  exact hh

noncomputable def cauchyTransform {n : ℕ} {R : ℝ} (hR : 0 ≤ R)
    (B : C((Fin n → RadiusCircle R), ℂ)) (x : Fin n → ℂ) : ℂ :=
  iteratedCauchyFunctional R hR n (B * ∏ j, torusResolvent j x)

lemma analyticAt_cauchyTransform {n : ℕ} {R : ℝ} (hR : 0 < R)
    (B : C((Fin n → RadiusCircle R), ℂ)) {x : Fin n → ℂ} (hx : x ∈ ball 0 R) :
    AnalyticAt ℂ (cauchyTransform hR.le B) x := by
  have hp : AnalyticAt ℂ (fun y : Fin n → ℂ => ∏ j, torusResolvent (R := R) j y) x := by
    simpa only [Finset.prod_fn] using Finset.univ.analyticAt_prod
      (fun j _ => analyticAt_torusResolvent hR hx j)
  exact ((iteratedCauchyFunctional R hR.le n).analyticAt _).comp (analyticAt_const.mul hp)

lemma cauchyTransform_eq {n : ℕ} {R : ℝ} (hR : 0 < R)
    {f : (Fin n → ℂ) → ℂ} (hf : DifferentiableOn ℂ f (closedBall 0 R))
    {x : Fin n → ℂ} (hx : x ∈ ball 0 R) :
    cauchyTransform hR.le (torusBoundary hR.le f hf.continuousOn) x = f x := by
  apply iteratedCauchy_formula n hR hf hx
  intro ζ
  simp only [ContinuousMap.mul_apply, ContinuousMap.prod_apply, torusResolvent_apply hR hx]
  rfl

theorem analyticAt_of_differentiableOn_closedBall {n : ℕ} {R : ℝ} (hR : 0 < R)
    {f : (Fin n → ℂ) → ℂ} (hf : DifferentiableOn ℂ f (closedBall 0 R))
    {x : Fin n → ℂ} (hx : x ∈ ball 0 R) : AnalyticAt ℂ f x := by
  apply (analyticAt_cauchyTransform hR (torusBoundary hR.le f hf.continuousOn) hx).congr
  filter_upwards [isOpen_ball.mem_nhds hx] with y hy
  exact cauchyTransform_eq hR hf hy

theorem analyticOnNhd_of_differentiableOn_finite {n : ℕ} {S : Set (Fin n → ℂ)}
    (hS : IsOpen S) {f : (Fin n → ℂ) → ℂ} (hf : DifferentiableOn ℂ f S) :
    AnalyticOnNhd ℂ f S := by
  intro x hx
  obtain ⟨r,hr,hrs⟩ := Metric.mem_nhds_iff.mp (hS.mem_nhds hx)
  have hmaps : MapsTo (fun y => x + y) (closedBall (0 : Fin n → ℂ) (r/2)) S := by
    intro y hy
    apply hrs
    rw [mem_ball, dist_eq_norm]
    simpa only [add_sub_cancel_left] using
      lt_of_le_of_lt (by simpa only [mem_closedBall, dist_zero_right] using hy) (by linarith : r/2 < r)
  have hd := hf.comp ((differentiable_const x).add differentiable_id).differentiableOn hmaps
  have ha := analyticAt_of_differentiableOn_closedBall (half_pos hr) hd (mem_ball_self (half_pos hr))
  change AnalyticAt ℂ (fun y => f (x+y)) 0 at ha
  have ha' : AnalyticAt ℂ (fun y => f (x+y)) (x-x) := by simpa only [sub_self] using ha
  have hcomp := ha'.comp (f := fun y => y-x) (analyticAt_id.sub analyticAt_const)
  simpa only [Function.comp_def, add_sub_cancel] using hcomp

theorem analyticOnNhd_of_differentiableOn_affine {n m : ℕ} {S : Set (Fin n → ℂ)}
    (hS : IsOpen S) {f : (Fin n → ℂ) → (Fin m → ℂ)} (hf : DifferentiableOn ℂ f S) :
    AnalyticOnNhd ℂ f S := by
  intro x hx
  apply AnalyticAt.pi
  intro j
  apply analyticOnNhd_of_differentiableOn_finite hS _ x hx
  exact (differentiable_apply j).differentiableOn.comp hf (fun _ _ => mem_univ _)

end Release061

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_MontelExpandingDomains
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace Release061
open Set Filter Metric TopologicalSpace
open scoped Topology

theorem locally_uniform_subsequence_of_eventual_equicontinuity
    {X Y : Type*} [TopologicalSpace X] [SeparableSpace X]
    [MetricSpace Y] [CompleteSpace Y]
    (f : ℕ → X → Y)
    (hequi : ∀ x ε, 0 < ε → ∃ W : Set X, W ∈ 𝓝 x ∧
      ∀ᶠ j in atTop, ∀ y ∈ W, dist (f j y) (f j x) < ε)
    (hcompact : ∀ x, ∃ K : Set Y, IsCompact K ∧ ∀ j, f j x ∈ K) :
    ∃ g : X → Y, Continuous g ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      TendstoLocallyUniformly (fun j => f (φ j)) g atTop := by
  classical
  obtain ⟨D,hD,hdense⟩ := TopologicalSpace.exists_countable_dense X
  let : Countable D := hD.to_subtype
  choose K hK hmem using hcompact
  have hprod : IsCompact (Set.pi univ (fun x : D => K x.val)) :=
    isCompact_univ_pi (fun x : D => hK x.val)
  obtain ⟨gD,_,φ,hφ,hconvD⟩ := hprod.tendsto_subseq
    (fun j => (show (fun x : D => f j x.val) ∈ Set.pi univ (fun x : D => K x.val) from
      fun x _ => hmem x.val j))
  have hcD : ∀ x : D, Tendsto (fun j => f (φ j) x.val) atTop (𝓝 (gD x)) :=
    fun x => (tendsto_pi_nhds.mp hconvD) x
  have he : ∀ x ε, 0 < ε → ∃ W : Set X, W ∈ 𝓝 x ∧
      ∀ᶠ j in atTop, ∀ y ∈ W, dist (f (φ j) y) (f (φ j) x) < ε := by
    intro x ε hε
    obtain ⟨W,hW,he⟩ := hequi x ε hε
    exact ⟨W,hW,hφ.tendsto_atTop he⟩
  have hcau : ∀ x, CauchySeq (fun j => f (φ j) x) := by
    intro x
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨W,hW,heW⟩ := he x (ε/3) (by positivity)
    obtain ⟨d,hdD,hdW⟩ := hdense.inter_nhds_nonempty hW
    obtain ⟨N₁,hN₁⟩ := Metric.cauchySeq_iff.mp (hcD ⟨d,hdD⟩).cauchySeq (ε/3) (by positivity)
    obtain ⟨N₂,hN₂⟩ := eventually_atTop.mp heW
    refine ⟨max N₁ N₂,?_⟩
    intro i hi j hj
    have hi₁ := le_trans (le_max_left N₁ N₂) hi
    have hi₂ := le_trans (le_max_right N₁ N₂) hi
    have hj₁ := le_trans (le_max_left N₁ N₂) hj
    have hj₂ := le_trans (le_max_right N₁ N₂) hj
    have hdi := hN₂ i hi₂ d hdW
    have hdj := hN₂ j hj₂ d hdW
    have hdij := hN₁ i hi₁ j hj₁
    calc
      dist (f (φ i) x) (f (φ j) x) ≤
          dist (f (φ i) x) (f (φ i) d) + dist (f (φ i) d) (f (φ j) d) +
            dist (f (φ j) d) (f (φ j) x) := dist_triangle4 _ _ _ _
      _ < ε := by rw [dist_comm (f (φ i) x) (f (φ i) d)]; linarith
  choose g hg using fun x => cauchySeq_tendsto_of_complete (hcau x)
  have hlimit : ∀ x ε, 0 < ε → ∃ W : Set X, W ∈ 𝓝 x ∧
      (∀ y ∈ W, dist (g y) (g x) ≤ ε) ∧
      ∀ᶠ j in atTop, ∀ y ∈ W, dist (f (φ j) y) (f (φ j) x) < ε := by
    intro x ε hε
    obtain ⟨W,hW,heW⟩ := he x ε hε
    refine ⟨W,hW,?_,heW⟩
    intro y hy
    exact le_of_tendsto ((hg y).dist (hg x))
      (heW.mono (fun j hj => (hj y hy).le))
  have hgc : Continuous g := by
    rw [continuous_iff_continuousAt]
    intro x
    rw [ContinuousAt,Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨W,hW,hlim,_⟩ := hlimit x (ε/2) (by positivity)
    filter_upwards [hW] with y hy
    exact (hlim y hy).trans_lt (by linarith)
  refine ⟨g,hgc,φ,hφ,?_⟩
  rw [Metric.tendstoLocallyUniformly_iff]
  intro ε hε x
  obtain ⟨W,hW,hlim,heW⟩ := hlimit x (ε/3) (by positivity)
  refine ⟨W,hW,?_⟩
  have hpx : ∀ᶠ j in atTop, dist (g x) (f (φ j) x) < ε/3 := by
    simpa only [dist_comm] using (Metric.tendsto_nhds.mp (hg x) (ε/3) (by positivity))
  filter_upwards [heW,hpx] with j hj hx y hy
  calc
    dist (g y) (f (φ j) y) ≤ dist (g y) (g x) + dist (g x) (f (φ j) x) +
        dist (f (φ j) x) (f (φ j) y) := dist_triangle4 _ _ _ _
    _ < ε := by have := hlim y hy; have := hj y hy; rw [dist_comm (f (φ j) x) (f (φ j) y)]; linarith

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem bounded_fderiv_on_half_ball {f : E → F} {c x : E} {R M : ℝ}
    (hR : 0 < R) (hf : DifferentiableOn ℂ f (ball c R))
    (hb : ∀ z ∈ ball c R, ‖f z‖ ≤ M) (hx : x ∈ ball c (R/2)) :
    ‖fderiv ℂ f x‖ ≤ 4*M/R := by
  have hsub : ball x (R/2) ⊆ ball c R := by
    intro z hz
    rw [mem_ball] at hx hz ⊢
    calc
      dist z c ≤ dist z x + dist x c := dist_triangle _ _ _
      _ < R := by linarith
  have hxR : x ∈ ball c R := hsub (mem_ball_self (half_pos hR))
  have hm : MapsTo f (ball x (R/2)) (closedBall (f x) (2*M)) := by
    intro z hz
    rw [mem_closedBall,dist_eq_norm]
    exact (norm_sub_le _ _).trans (by linarith [hb z (hsub hz),hb x hxR])
  have he := Complex.norm_fderiv_le_div_of_mapsTo_ball (hf.mono hsub) hm (half_pos hR)
  convert he using 1 <;> first | rfl | ring

theorem uniformCauchySeqOn_fderiv_of_uniformCauchySeqOn
    {f : ℕ → E → F} {c : E} {R : ℝ} (hR : 0 < R)
    (hf : ∀ j, DifferentiableOn ℂ (f j) (ball c R))
    (hcu : UniformCauchySeqOn f atTop (ball c R)) :
    UniformCauchySeqOn (fun j => fderiv ℂ (f j)) atTop (ball c (R/2)) := by
  rw [Metric.uniformCauchySeqOn_iff] at hcu ⊢
  intro ε hε
  obtain ⟨N,hN⟩ := hcu (ε*R/8) (by positivity)
  refine ⟨N,?_⟩
  intro j hj k hk x hx
  have hb : ∀ z ∈ ball c R, ‖f j z-f k z‖ ≤ ε*R/8 := by
    intro z hz
    exact le_of_lt (by simpa only [dist_eq_norm] using hN j hj k hk z hz)
  have hest := bounded_fderiv_on_half_ball hR ((hf j).sub (hf k)) hb hx
  have hxR : x ∈ ball c R := ball_subset_ball (by linarith) hx
  rw [fderiv_sub ((hf j).differentiableAt (isOpen_ball.mem_nhds hxR))
    ((hf k).differentiableAt (isOpen_ball.mem_nhds hxR))] at hest
  rw [dist_eq_norm]
  apply hest.trans_lt
  field_simp
  nlinarith

theorem differentiableAt_of_uniform_limit_ball [CompleteSpace F]
    {f : ℕ → E → F} {g : E → F} {c : E} {R : ℝ} (hR : 0 < R)
    (hf : ∀ j, DifferentiableOn ℂ (f j) (ball c R))
    (hfg : TendstoUniformlyOn f g atTop (ball c R)) :
    DifferentiableAt ℂ g c := by
  classical
  have hcu := uniformCauchySeqOn_fderiv_of_uniformCauchySeqOn hR hf hfg.uniformCauchySeqOn
  have hpt : ∀ x ∈ ball c (R/2), ∃ L : E →L[ℂ] F,
      Tendsto (fun j => fderiv ℂ (f j) x) atTop (𝓝 L) := by
    intro x hx
    have hcux : CauchySeq (fun j => fderiv ℂ (f j) x) := by
      rw [Metric.cauchySeq_iff]
      intro ε hε
      obtain ⟨N,hN⟩ := Metric.uniformCauchySeqOn_iff.mp hcu ε hε
      exact ⟨N,fun j hj k hk => hN j hj k hk x hx⟩
    exact cauchySeq_tendsto_of_complete hcux
  choose L hL using hpt
  let dg : E → E →L[ℂ] F := fun x => if hx : x ∈ ball c (R/2) then L x hx else 0
  have hder : TendstoUniformlyOn (fun j => fderiv ℂ (f j)) dg atTop (ball c (R/2)) := by
    apply hcu.tendstoUniformlyOn_of_tendsto
    intro x hx
    simpa only [dg,dite_eq_left hx] using hL x hx
  apply (hasFDerivAt_of_tendstoUniformlyOn isOpen_ball hder
    (fun j x hx => ((hf j).differentiableAt
      (isOpen_ball.mem_nhds (ball_subset_ball (by linarith) hx))).hasFDerivAt)
    (fun x hx => hfg.tendsto_at (ball_subset_ball (by linarith) hx))
    (mem_ball_self (half_pos hR))).differentiableAt

theorem differentiableOn_of_locally_uniform_limit [ProperSpace E] [CompleteSpace F]
    {f : ℕ → E → F} {g : E → F} {S : Set E} (hS : IsOpen S)
    (hfg : TendstoLocallyUniformlyOn f g atTop S)
    (hf : ∀ x ∈ S, ∃ W : Set E, W ∈ 𝓝 x ∧
      ∀ᶠ j in atTop, DifferentiableOn ℂ (f j) W) :
    DifferentiableOn ℂ g S := by
  intro x hx
  obtain ⟨W,hW,hhol⟩ := hf x hx
  obtain ⟨R,hR,hRW⟩ := Metric.mem_nhds_iff.mp (inter_mem hW (hS.mem_nhds hx))
  have hsub : closedBall x (R/2) ⊆ W ∩ S :=
    (closedBall_subset_ball (by linarith)).trans hRW
  have hc : TendstoUniformlyOn f g atTop (ball x (R/2)) := by
    apply (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact
      (isCompact_closedBall x (R/2))).mp (hfg.mono (fun y hy => (hsub hy).2)) |>.mono
    exact ball_subset_closedBall
  obtain ⟨N,hN⟩ := eventually_atTop.mp hhol
  have htail : TendstoUniformlyOn (fun j => f (j+N)) g atTop (ball x (R/2)) := by
    intro u hu
    exact (Filter.tendsto_add_atTop_nat N) (hc u hu)
  apply (differentiableAt_of_uniform_limit_ball (half_pos hR)
    (fun j => (hN (j+N) (Nat.le_add_left _ _)).mono
      (fun y hy => (hsub (ball_subset_closedBall hy)).1)) htail).differentiableWithinAt

omit [NormedSpace ℂ F] in

theorem compact_range_of_eventually_norm_le [ProperSpace F]
    {u : ℕ → F} {M : ℝ} (hM : 0 < M)
    (hu : ∀ᶠ j in atTop, ‖u j‖ ≤ M) :
    ∃ K : Set F, IsCompact K ∧ ∀ j, u j ∈ K := by
  obtain ⟨N,hN⟩ := eventually_atTop.mp hu
  let B := M + ∑ j ∈ Finset.range N, ‖u j‖
  refine ⟨closedBall 0 B,isCompact_closedBall _ _,?_⟩
  intro j
  rw [mem_closedBall,dist_zero_right]
  by_cases hj : j < N
  · have hb : ‖u j‖ ≤ ∑ i ∈ Finset.range N, ‖u i‖ :=
      Finset.single_le_sum (fun i _ => norm_nonneg (u i)) (Finset.mem_range.mpr hj)
    dsimp [B]
    linarith
  · exact (hN j (Nat.le_of_not_gt hj)).trans (by dsimp [B]; exact le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ => norm_nonneg (u i))))

theorem montel_expanding_domains [ProperSpace E] [SecondCountableTopology E]
    [ProperSpace F] {S : Set E} (hS : IsOpen S) (f : ℕ → E → F)
    (hlocal : ∀ x ∈ S, ∃ r : ℝ, 0 < r ∧ ∃ M : ℝ, 0 < M ∧
      ball x r ⊆ S ∧ ∀ᶠ j in atTop,
        DifferentiableOn ℂ (f j) (ball x r) ∧ ∀ y ∈ ball x r, ‖f j y‖ ≤ M) :
    ∃ g : E → F, DifferentiableOn ℂ g S ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      TendstoLocallyUniformlyOn (fun j => f (φ j)) g atTop S := by
  classical
  have hequi : ∀ x : S, ∀ ε, 0 < ε → ∃ W : Set S, W ∈ 𝓝 x ∧
      ∀ᶠ j in atTop, ∀ y ∈ W, dist (f j y.val) (f j x.val) < ε := by
    intro x ε hε
    obtain ⟨r,hr,M,_,_,hF⟩ := hlocal x.val x.property
    let W : Set S := {y | y.val ∈ ball x.val r ∧ (2*M/r)*dist y.val x.val < ε}
    have hbase : ∀ᶠ y : S in 𝓝 x, y.val ∈ ball x.val r :=
      continuous_subtype_val.continuousAt.preimage_mem_nhds (ball_mem_nhds _ hr)
    have hsmall : ∀ᶠ y : S in 𝓝 x, (2*M/r)*dist y.val x.val < ε := by
      have ht : Tendsto (fun y : S => (2*M/r)*dist y.val x.val) (𝓝 x) (𝓝 0) := by
        simpa using ((continuous_subtype_val.dist (continuous_const : Continuous (fun _ : S => x.val))).const_mul (2*M/r)).tendsto x
      exact (tendsto_order.mp ht).2 ε hε
    refine ⟨W,hbase.and hsmall,?_⟩
    filter_upwards [hF] with j hj y hy
    have hmaps : MapsTo (f j) (ball x.val r) (closedBall (f j x.val) (2*M)) := by
      intro z hz
      rw [mem_closedBall,dist_eq_norm]
      exact (norm_sub_le _ _).trans (by linarith [hj.2 z hz,hj.2 x.val (mem_ball_self hr)])
    exact (Complex.dist_le_div_mul_dist_of_mapsTo_ball hj.1 hmaps hy.1).trans_lt hy.2
  have hcompact : ∀ x : S, ∃ K : Set F, IsCompact K ∧ ∀ j, f j x.val ∈ K := by
    intro x
    obtain ⟨r,hr,M,hM,_,hF⟩ := hlocal x.val x.property
    exact compact_range_of_eventually_norm_le hM
      (hF.mono (fun _ hj => hj.2 x.val (mem_ball_self hr)))
  obtain ⟨g,hgc,φ,hφ,hconv⟩ :=
    locally_uniform_subsequence_of_eventual_equicontinuity (fun j (x : S) => f j x.val) hequi hcompact
  let G : E → F := fun x => if hx : x ∈ S then g ⟨x,hx⟩ else 0
  have hc : TendstoLocallyUniformlyOn (fun j => f (φ j)) G atTop S := by
    rw [tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe]
    simpa only [Function.comp_def,G,dite_eq_left (Subtype.prop _)] using hconv
  refine ⟨G,?_,φ,hφ,hc⟩
  apply differentiableOn_of_locally_uniform_limit hS hc
  intro x hx
  obtain ⟨r,hr,_,_,_,hF⟩ := hlocal x hx
  exact ⟨ball x r,ball_mem_nhds _ hr,hφ.tendsto_atTop (hF.mono (fun _ hj => hj.1))⟩

end Release061


end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_ContinuousFderivLocallyUniform
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace Release061
open Set Filter Metric
open scoped Topology NNReal
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem tendstoUniformlyOn_fderiv_half_ball
    {f : ℕ → E → F} {g : E → F} {c : E} {R : ℝ} (hR : 0 < R)
    (hf : ∀ᶠ j in atTop, DifferentiableOn ℂ (f j) (ball c R))
    (hg : DifferentiableOn ℂ g (ball c R))
    (hfg : TendstoUniformlyOn f g atTop (ball c R)) :
    TendstoUniformlyOn (fun j => fderiv ℂ (f j)) (fderiv ℂ g) atTop (ball c (R/2)) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [hf,Metric.tendstoUniformlyOn_iff.mp hfg (ε*R/8) (by positivity)] with j hj he
  intro x hx
  have hb : ∀ z ∈ ball c R, ‖f j z-g z‖ ≤ ε*R/8 := by
    intro z hz
    exact le_of_lt (by simpa only [dist_eq_norm,norm_sub_rev] using he z hz)
  have hest := bounded_fderiv_on_half_ball hR (hj.sub hg) hb hx
  have hxR : x ∈ ball c R := ball_subset_ball (by linarith) hx
  rw [fderiv_sub (hj.differentiableAt (isOpen_ball.mem_nhds hxR))
    (hg.differentiableAt (isOpen_ball.mem_nhds hxR))] at hest
  rw [dist_eq_norm,norm_sub_rev]
  apply hest.trans_lt
  field_simp
  nlinarith

theorem tendstoLocallyUniformlyOn_fderiv [ProperSpace E] [CompleteSpace F]
    {S : Set E} (hS : IsOpen S) {f : ℕ → E → F} {g : E → F}
    (hfg : TendstoLocallyUniformlyOn f g atTop S)
    (hf : ∀ x ∈ S, ∃ W ∈ 𝓝 x, ∀ᶠ j in atTop, DifferentiableOn ℂ (f j) W) :
    TendstoLocallyUniformlyOn (fun j => fderiv ℂ (f j)) (fderiv ℂ g) atTop S := by
  have hg := differentiableOn_of_locally_uniform_limit hS hfg hf
  apply tendstoLocallyUniformlyOn_of_forall_exists_nhds
  intro x hx
  obtain ⟨W,hW,hhol⟩ := hf x hx
  obtain ⟨R,hR,hsub⟩ := Metric.mem_nhds_iff.mp (inter_mem hW (hS.mem_nhds hx))
  have hball : ball x (R/2) ⊆ W ∩ S :=
    fun y hy => hsub (ball_subset_ball (by linarith) hy)
  have hc : TendstoUniformlyOn f g atTop (ball x (R/2)) := by
    apply (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact
      (isCompact_closedBall x (R/2))).mp (hfg.mono (fun y hy => ?_)) |>.mono
    · exact ball_subset_closedBall
    · exact (hsub (closedBall_subset_ball (by linarith) hy)).2
  refine ⟨ball x ((R/2)/2),mem_nhdsWithin_of_mem_nhds
    (ball_mem_nhds _ (by positivity)),?_⟩
  exact tendstoUniformlyOn_fderiv_half_ball (half_pos hR)
    (hhol.mono (fun _ hj => hj.mono (fun y hy => (hball hy).1)))
    (hg.mono (fun y hy => (hball hy).2)) hc

theorem continuousAt_fderiv_of_locally_uniform_analytic [ProperSpace E] [CompleteSpace F]
    {S : Set E} (hS : IsOpen S) {f : ℕ → E → F} {g : E → F}
    (hfg : TendstoLocallyUniformlyOn f g atTop S)
    (hf : ∀ x ∈ S, ∃ W ∈ 𝓝 x, ∀ᶠ j in atTop, AnalyticOnNhd ℂ (f j) W)
    {x : E} (hx : x ∈ S) : ContinuousAt (fderiv ℂ g) x := by
  have hdiff : ∀ x ∈ S, ∃ W ∈ 𝓝 x, ∀ᶠ j in atTop, DifferentiableOn ℂ (f j) W := by
    intro x hx
    obtain ⟨W,hW,hF⟩ := hf x hx
    exact ⟨W,hW,hF.mono (fun _ hj => hj.differentiableOn)⟩
  have hconv := tendstoLocallyUniformlyOn_fderiv hS hfg hdiff
  obtain ⟨W,hW,hhol⟩ := hf x hx
  obtain ⟨R,hR,hsub⟩ := Metric.mem_nhds_iff.mp (inter_mem hW (hS.mem_nhds hx))
  have hc : ContinuousOn (fderiv ℂ g) (ball x R) := by
    apply (hconv.mono (fun z hz => (hsub hz).2)).continuousOn
    exact (hhol.mono (fun _ hj => (hj.fderiv.continuousOn.mono
      (fun z hz => (hsub hz).1)))).frequently
  exact hc.continuousAt (ball_mem_nhds _ hR)

end Release061



end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_EventuallyImageBallNonzero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Metric Complex
open scoped Topology
namespace Release061
open Set Filter Metric
open scoped Topology

theorem locallyUniform_postcomp
    {X Y Z ι : Type*} [TopologicalSpace X] [PseudoMetricSpace Y] [PseudoMetricSpace Z]
    {l : Filter ι} {S : Set X} {f : ι → X → Y} {g : X → Y} {H : Y → Z}
    (hfg : TendstoLocallyUniformlyOn f g l S) (hg : ContinuousOn g S)
    (hH : Continuous H) :
    TendstoLocallyUniformlyOn (fun j x => H (f j x)) (fun x => H (g x)) l S := by
  rw [Metric.tendstoLocallyUniformlyOn_iff] at hfg ⊢
  intro ε hε x hx
  obtain ⟨δ,hδ,hδH⟩ := Metric.continuousAt_iff.mp (hH.continuousAt : ContinuousAt H (g x)) (ε/2) (half_pos hε)
  obtain ⟨W,hW,hunif⟩ := hfg (δ/2) (half_pos hδ) x hx
  have hnear : {y | dist (g y) (g x) < δ/2} ∈ 𝓝[S] x :=
    (Metric.tendsto_nhds.mp (hg x hx)) (δ/2) (half_pos hδ)
  refine ⟨W ∩ {y | dist (g y) (g x) < δ/2},inter_mem hW hnear,?_⟩
  filter_upwards [hunif] with j hj y hy
  have hy2 : dist (g y) (g x) < δ/2 := hy.2
  have hfy : dist (f j y) (g x) < δ := by
    calc
      dist (f j y) (g x) ≤ dist (f j y) (g y)+dist (g y) (g x) := dist_triangle _ _ _
      _ < δ := by rw [dist_comm (f j y)]; linarith [hj y hy.1]
  calc
    dist (H (g y)) (H (f j y)) ≤ dist (H (g y)) (H (g x))+dist (H (g x)) (H (f j y)) := dist_triangle _ _ _
    _ < ε := by
      rw [dist_comm (H (g x))]
      linarith [hδH (lt_trans hy.2 (half_lt_self hδ)),hδH hfy]

end Release061

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_HolomorphicLocallyUniformLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Metric
open scoped Topology

noncomputable def ambientExtend {n m : ℕ} {S : Set (Affine n)}
    (f : S → Affine m) (x : Affine n) : Affine m := by
  classical
  exact if hx : x ∈ S then f ⟨x,hx⟩ else 0

lemma ambientExtend_apply {n m : ℕ} {S : Set (Affine n)}
    (f : S → Affine m) (x : S) : ambientExtend f x = f x := by
  classical
  simp only [ambientExtend,dite_eq_left x.property]

theorem HolomorphicOnSubset.analyticOnNhd_extend {n m : ℕ} {S : Set (Affine n)}
    (hS : IsOpen S) {f : S → Affine m} (hf : HolomorphicOnSubset S f) :
    AnalyticOnNhd ℂ (ambientExtend f) S := by
  intro x hx
  obtain ⟨W,hW,hxW,F,hF,he⟩ := hf ⟨x,hx⟩
  apply (hF x hxW).congr
  filter_upwards [hW.mem_nhds hxW, hS.mem_nhds hx] with y hyW hyS
  rw [show ambientExtend f y = f ⟨y,hyS⟩ from ambientExtend_apply f ⟨y,hyS⟩]
  exact he ⟨y,hyS⟩ hyW

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_ScalingExpanding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Metric
open scoped Topology

theorem HolomorphicOnSubset.analyticOnNhd_of_open {n m : ℕ}
    {S : Set (Affine n)} (hS : IsOpen S) {f : Affine n → Affine m}
    (hf : HolomorphicOnSubset S (fun x => f x)) : AnalyticOnNhd ℂ f S := by
  intro x hx
  apply (hf.analyticOnNhd_extend hS x hx).congr
  filter_upwards [hS.mem_nhds hx] with y hy
  exact ambientExtend_apply _ ⟨y,hy⟩

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_DivisibleAutomorphismsSubsequence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Topology Metric
open scoped Classical

theorem bounded_divisible_automorphisms_subsequence {n : ℕ} {U : Set (Affine n)}
    (hU : IsOpen U) (hc : IsPreconnected U) (hb : Bornology.IsBounded U)
    [LocallyCompactSpace U]
    (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
    [MulAction Γ U] [ProperSMul Γ U]
    [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val))
    (b : ℕ → Biholomorph U U) (p : U)
    (hanchor : ∃ K : Set U, IsCompact K ∧ ∀ᶠ j in atTop, (b j).toHomeomorph p ∈ K) :
    ∃ ρ : ℕ → ℕ, StrictMono ρ ∧ ∃ e : Biholomorph U U,
      TendstoLocallyUniformlyOn
        (fun j => ambientExtend (fun x : U => ((b (ρ j)).toHomeomorph x).val))
        (ambientExtend (fun x : U => (e.toHomeomorph x).val)) atTop U ∧
      TendstoLocallyUniformlyOn
        (fun j => ambientExtend (fun x : U => ((b (ρ j)).toHomeomorph.symm x).val))
        (ambientExtend (fun x : U => (e.toHomeomorph.symm x).val)) atTop U := by
  let f : ℕ → Affine n → Affine n := fun j =>
    ambientExtend (fun x : U => ((b j).toHomeomorph x).val)
  let g : ℕ → Affine n → Affine n := fun j =>
    ambientExtend (fun x : U => ((b j).toHomeomorph.symm x).val)
  have hfval (j : ℕ) (x : U) : f j x.val=((b j).toHomeomorph x).val := ambientExtend_apply _ x
  have hgval (j : ℕ) (x : U) : g j x.val=((b j).toHomeomorph.symm x).val := ambientExtend_apply _ x
  have hfa : ∀ j, AnalyticOnNhd ℂ (f j) U := by
    intro j
    apply HolomorphicOnSubset.analyticOnNhd_of_open hU
    simpa only [hfval j] using (b j).holomorphic_toFun
  have hga : ∀ j, AnalyticOnNhd ℂ (g j) U := by
    intro j
    apply HolomorphicOnSubset.analyticOnNhd_of_open hU
    simpa only [hgval j] using (b j).holomorphic_invFun
  have hfm : ∀ j, MapsTo (f j) U U := fun j x hx => by
    rw [hfval j ⟨x,hx⟩]; exact ((b j).toHomeomorph ⟨x,hx⟩).property
  have hgm : ∀ j, MapsTo (g j) U U := fun j x hx => by
    rw [hgval j ⟨x,hx⟩]; exact ((b j).toHomeomorph.symm ⟨x,hx⟩).property
  have hgf : ∀ j x, x ∈ U → g j (f j x)=x := by
    intro j x hx
    rw [hfval j ⟨x,hx⟩,hgval j ((b j).toHomeomorph ⟨x,hx⟩)]
    exact congrArg Subtype.val ((b j).toHomeomorph.symm_apply_apply ⟨x,hx⟩)
  have hfg : ∀ j x, x ∈ U → f j (g j x)=x := by
    intro j x hx
    rw [hgval j ⟨x,hx⟩,hfval j ((b j).toHomeomorph.symm ⟨x,hx⟩)]
    exact congrArg Subtype.val ((b j).toHomeomorph.apply_symm_apply ⟨x,hx⟩)
  obtain ⟨R,hR,hRU⟩ := hb.exists_pos_norm_le
  obtain ⟨P,hPa,ρ,hρ,hP⟩ := montel_expanding_domains hU
      (fun j x => (f j x,g j x)) (by
    intro x hx
    obtain ⟨r,hr,hrU⟩ := isOpen_iff.mp hU x hx
    refine ⟨r,hr,R,hR,hrU,Eventually.of_forall fun j => ?_⟩
    refine ⟨((hfa j).differentiableOn.mono hrU).prodMk ((hga j).differentiableOn.mono hrU),?_⟩
    intro y hy
    exact norm_prod_le_iff.mpr ⟨hRU _ (hfm j (hrU hy)),hRU _ (hgm j (hrU hy))⟩)
  let F : Affine n → Affine n := fun x => (P x).1
  let G : Affine n → Affine n := fun x => (P x).2
  have hFa : AnalyticOnNhd ℂ F U := analyticOnNhd_of_differentiableOn_affine hU hPa.fst
  have hGa : AnalyticOnNhd ℂ G U := analyticOnNhd_of_differentiableOn_affine hU hPa.snd
  have hF : TendstoLocallyUniformlyOn (fun j => f (ρ j)) F atTop U :=
    locallyUniform_postcomp hP hPa.continuousOn continuous_fst
  have hG : TendstoLocallyUniformlyOn (fun j => g (ρ j)) G atTop U :=
    locallyUniform_postcomp hP hPa.continuousOn continuous_snd
  obtain ⟨K,hK,hrep⟩ := exists_compact_orbit_representatives (X := U) (Γ := Γ)
  have hFM : MapsTo F U U := by
    have he := bounded_cocompact_holomorphic_family_limit U hU hc U hb hhol K hK hrep
      (fun j => (b (ρ j)).toHomeomorph) atTop p
      (by obtain ⟨A,hA,ha⟩ := hanchor; exact ⟨A,hA,hρ.tendsto_atTop.eventually ha⟩)
      (HolomorphicOnSubset.locallyEventually hU (fun j => (b (ρ j)).holomorphic_toFun) atTop)
      (fun x => F x.val) (fun x => by simpa only [hfval] using hF.tendsto_at x.property)
    exact fun x hx => he ⟨x,hx⟩
  have hGp : G (F p.val)=p.val := by
    have ht : Tendsto (fun j => f (ρ j) p.val) atTop (𝓝[U] F p.val) :=
      tendsto_nhdsWithin_iff.mpr ⟨hF.tendsto_at p.property,Eventually.of_forall fun j => hfm (ρ j) p.property⟩
    exact tendsto_nhds_unique
      (hG.tendsto_comp (hGa.continuousOn _ (hFM p.property)) (hFM p.property) ht)
      (tendsto_const_nhds.congr' (Eventually.of_forall fun j => (hgf (ρ j) p.val p.property).symm))
  have hGanchor : ∃ A : Set U, IsCompact A ∧ ∀ᶠ j in atTop,
      (b (ρ j)).toHomeomorph.symm ⟨F p.val,hFM p.property⟩ ∈ A := by
    obtain ⟨r,hr,hrU⟩ := isOpen_iff.mp hU p.val p.property
    let A : Set U := Subtype.val ⁻¹' closedBall p.val (r/2)
    have hclosedU : closedBall p.val (r/2) ⊆ U :=
      (closedBall_subset_ball (by linarith)).trans hrU
    have himage : Subtype.val '' A=closedBall p.val (r/2) := by
      ext x
      constructor
      · rintro ⟨y,hy,rfl⟩; exact hy
      · intro hx; exact ⟨⟨x,hclosedU hx⟩,hx,rfl⟩
    refine ⟨A,?_,?_⟩
    · apply Topology.IsEmbedding.subtypeVal.isCompact_iff.mpr
      rw [himage]
      exact isCompact_closedBall _ _
    · have ht : Tendsto (fun j => g (ρ j) (F p.val)) atTop (𝓝 p.val) := by
        simpa only [hGp] using hG.tendsto_at (hFM p.property)
      filter_upwards [ht.eventually (closedBall_mem_nhds p.val (half_pos hr))] with j hj
      change ((b (ρ j)).toHomeomorph.symm ⟨F p.val,hFM p.property⟩).val ∈ closedBall p.val (r/2)
      rw [← hgval (ρ j) ⟨F p.val,hFM p.property⟩]
      exact hj
  have hGM : MapsTo G U U := by
    have he := bounded_cocompact_holomorphic_family_limit U hU hc U hb hhol K hK hrep
      (fun j => (b (ρ j)).toHomeomorph.symm) atTop ⟨F p.val,hFM p.property⟩ hGanchor
      (HolomorphicOnSubset.locallyEventually hU (fun j => (b (ρ j)).holomorphic_invFun) atTop)
      (fun x => G x.val) (fun x => by simpa only [hgval] using hG.tendsto_at x.property)
    exact fun x hx => he ⟨x,hx⟩
  have hGF : ∀ x ∈ U, G (F x)=x := by
    intro x hx
    have ht : Tendsto (fun j => f (ρ j) x) atTop (𝓝[U] F x) :=
      tendsto_nhdsWithin_iff.mpr ⟨hF.tendsto_at hx,Eventually.of_forall fun j => hfm (ρ j) hx⟩
    exact tendsto_nhds_unique
      (hG.tendsto_comp (hGa.continuousOn _ (hFM hx)) (hFM hx) ht)
      (tendsto_const_nhds.congr' (Eventually.of_forall fun j => (hgf (ρ j) x hx).symm))
  have hFG : ∀ x ∈ U, F (G x)=x := by
    intro x hx
    have ht : Tendsto (fun j => g (ρ j) x) atTop (𝓝[U] G x) :=
      tendsto_nhdsWithin_iff.mpr ⟨hG.tendsto_at hx,Eventually.of_forall fun j => hgm (ρ j) hx⟩
    exact tendsto_nhds_unique
      (hF.tendsto_comp (hFa.continuousOn _ (hGM hx)) (hGM hx) ht)
      (tendsto_const_nhds.congr' (Eventually.of_forall fun j => (hfg (ρ j) x hx).symm))
  let e := biholomorphOfAmbientInverse U U F G hFa hGa hFM hGM hGF hFG
  refine ⟨ρ,hρ,e,?_,?_⟩
  · apply hF.congr_right
    intro x hx
    change F x = ambientExtend (fun x : U => F x.val) x
    exact (ambientExtend_apply (fun x : U => F x.val) ⟨x,hx⟩).symm
  · apply hG.congr_right
    intro x hx
    change G x = ambientExtend (fun x : U => G x.val) x
    exact (ambientExtend_apply (fun x : U => G x.val) ⟨x,hx⟩).symm

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_TendstoAmbientLocallyUniformly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Topology TopologicalSpace
open scoped Classical
namespace Biholomorph

@[ext] theorem ext {n m : ℕ} {U : Set (Affine n)} {V : Set (Affine m)}
    {a b : Biholomorph U V} (h : ∀ x, a.toHomeomorph x=b.toHomeomorph x) : a=b := by
  have he := Homeomorph.ext h
  cases a
  cases b
  cases he
  rfl

noncomputable instance automorphismMul {n : ℕ} {U : Set (Affine n)} : Mul (Biholomorph U U) :=
  ⟨fun a b => b.trans a⟩
noncomputable instance automorphismOne {n : ℕ} {U : Set (Affine n)} : One (Biholomorph U U) :=
  ⟨refl U⟩
noncomputable instance automorphismInv {n : ℕ} {U : Set (Affine n)} : Inv (Biholomorph U U) :=
  ⟨symm⟩

@[simp] theorem mul_apply {n : ℕ} {U : Set (Affine n)} (a b : Biholomorph U U) (x : U) :
    (a*b).toHomeomorph x=a.toHomeomorph (b.toHomeomorph x) := rfl
@[simp] theorem one_apply {n : ℕ} {U : Set (Affine n)} (x : U) :
    (1 : Biholomorph U U).toHomeomorph x=x := rfl
@[simp] theorem inv_apply {n : ℕ} {U : Set (Affine n)} (a : Biholomorph U U) (x : U) :
    a⁻¹.toHomeomorph x=a.toHomeomorph.symm x := rfl

noncomputable instance automorphismGroup {n : ℕ} {U : Set (Affine n)} : Group (Biholomorph U U) :=
  Group.ofLeftAxioms (fun _ _ _ => ext (fun _ => rfl)) (fun _ => ext (fun _ => rfl))
    (fun a => ext (fun x => a.toHomeomorph.symm_apply_apply x))

def compactOpenPair {n : ℕ} {U : Set (Affine n)} (a : Biholomorph U U) : C(U,U) × C(U,U) :=
  (⟨a.toHomeomorph,a.toHomeomorph.continuous⟩,
   ⟨a.toHomeomorph.symm,a.toHomeomorph.symm.continuous⟩)

instance automorphismTopology {n : ℕ} {U : Set (Affine n)} : TopologicalSpace (Biholomorph U U) :=
  TopologicalSpace.induced compactOpenPair inferInstance

theorem compactOpenPair_injective {n : ℕ} {U : Set (Affine n)} :
    Function.Injective (compactOpenPair (U := U)) := by
  intro a b h
  exact ext (fun x => congrArg (fun p : C(U,U) × C(U,U) => p.1 x) h)

theorem compactOpenPair_isEmbedding {n : ℕ} {U : Set (Affine n)} :
    IsEmbedding (compactOpenPair (U := U)) := compactOpenPair_injective.isEmbedding_induced

theorem continuous_compactOpenPair {n : ℕ} {U : Set (Affine n)} :
    Continuous (compactOpenPair (U := U)) := compactOpenPair_isEmbedding.continuous

instance automorphismMetrizable {n : ℕ} {U : Set (Affine n)}
    [LocallyCompactSpace U] [SigmaCompactSpace U] : MetrizableSpace (Biholomorph U U) :=
  compactOpenPair_isEmbedding.metrizableSpace

instance automorphismTopologicalGroup {n : ℕ} {U : Set (Affine n)}
    [LocallyCompactSpace U] : IsTopologicalGroup (Biholomorph U U) where
  continuous_mul := by
    apply compactOpenPair_isEmbedding.isInducing.continuous_iff.mpr
    have h1 := (ContinuousMap.continuous_comp' (X := U) (Y := U) (Z := U)).comp
      ((continuous_compactOpenPair.fst.comp continuous_snd).prodMk
       (continuous_compactOpenPair.fst.comp continuous_fst))
    have h2 := (ContinuousMap.continuous_comp' (X := U) (Y := U) (Z := U)).comp
      ((continuous_compactOpenPair.snd.comp continuous_fst).prodMk
       (continuous_compactOpenPair.snd.comp continuous_snd))
    exact h1.prodMk h2
  continuous_inv := by
    apply compactOpenPair_isEmbedding.isInducing.continuous_iff.mpr
    exact continuous_compactOpenPair.snd.prodMk continuous_compactOpenPair.fst

theorem continuous_evaluation {n : ℕ} {U : Set (Affine n)} (p : U) :
    Continuous (fun a : Biholomorph U U => a.toHomeomorph p) := by
  change Continuous (fun a : Biholomorph U U => (compactOpenPair a).1 p)
  exact (continuous_eval_const p).comp continuous_compactOpenPair.fst

theorem tendsto_of_ambient_locallyUniformly {n : ℕ} {U : Set (Affine n)}
    [LocallyCompactSpace U] {ι : Type*} {a : ι → Biholomorph U U}
    {e : Biholomorph U U} {l : Filter ι}
    (hf : TendstoLocallyUniformlyOn
      (fun j => ambientExtend (fun x : U => ((a j).toHomeomorph x).val))
      (ambientExtend (fun x : U => (e.toHomeomorph x).val)) l U)
    (hg : TendstoLocallyUniformlyOn
      (fun j => ambientExtend (fun x : U => ((a j).toHomeomorph.symm x).val))
      (ambientExtend (fun x : U => (e.toHomeomorph.symm x).val)) l U) :
    Tendsto a l (𝓝 e) := by
  apply compactOpenPair_isEmbedding.isInducing.tendsto_nhds_iff.mpr
  let v : C(U,Affine n) := ⟨Subtype.val,continuous_subtype_val⟩
  have hv := ContinuousMap.isInducing_postcomp (X := U) v IsEmbedding.subtypeVal.isInducing
  have h1 : Tendsto (fun j => (compactOpenPair (a j)).1) l (𝓝 (compactOpenPair e).1) := by
    apply hv.tendsto_nhds_iff.mpr
    apply ContinuousMap.tendsto_of_tendstoLocallyUniformly
    change TendstoLocallyUniformly (fun j (x : U) => ((a j).toHomeomorph x).val)
      (fun x : U => (e.toHomeomorph x).val) l
    simpa only [Function.comp_def,ambientExtend_apply] using
      tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe.mp hf
  have h2 : Tendsto (fun j => (compactOpenPair (a j)).2) l (𝓝 (compactOpenPair e).2) := by
    apply hv.tendsto_nhds_iff.mpr
    apply ContinuousMap.tendsto_of_tendstoLocallyUniformly
    change TendstoLocallyUniformly (fun j (x : U) => ((a j).toHomeomorph.symm x).val)
      (fun x : U => (e.toHomeomorph.symm x).val) l
    simpa only [Function.comp_def,ambientExtend_apply] using
      tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe.mp hg
  exact h1.prodMk_nhds h2

end Biholomorph
end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_ActionAutomorphismHomRange
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Topology TopologicalSpace
open scoped Classical

instance Biholomorph.automorphismSecondCountable {n : ℕ} {U : Set (Affine n)}
    [LocallyCompactSpace U] : SecondCountableTopology (Biholomorph U U) :=
  Biholomorph.compactOpenPair_isEmbedding.secondCountableTopology

theorem bounded_divisible_automorphism_evaluation_proper {n : ℕ} {U : Set (Affine n)}
    (hU : IsOpen U) (hc : IsPreconnected U) (hb : Bornology.IsBounded U)
    [LocallyCompactSpace U]
    (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
    [MulAction Γ U] [ProperSMul Γ U]
    [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val)) (p : U) :
    IsProperMap (fun a : Biholomorph U U => a.toHomeomorph p) := by
  refine isProperMap_iff_isCompact_preimage.mpr ⟨Biholomorph.continuous_evaluation p,?_⟩
  intro K hK
  apply isCompact_iff_isSeqCompact.mpr
  intro a ha
  obtain ⟨ρ,hρ,e,hf,hg⟩ := bounded_divisible_automorphisms_subsequence
    hU hc hb Γ hhol a p ⟨K,hK,Eventually.of_forall ha⟩
  have ht := Biholomorph.tendsto_of_ambient_locallyUniformly hf hg
  refine ⟨e,?_,ρ,hρ,ht⟩
  exact hK.isClosed.mem_of_tendsto ((Biholomorph.continuous_evaluation p).tendsto e |>.comp ht)
    (Eventually.of_forall fun j => ha (ρ j))

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_IterateAverageCoboundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Metric
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

noncomputable def iterateAverage (f : E → E) (N : ℕ) (x : E) : E :=
  ((N+1 : ℂ)⁻¹) • ∑ j ∈ Finset.range (N+1), f^[j] x

lemma analyticOnNhd_iterate {S : Set E} {f : E → E}
    (hf : AnalyticOnNhd ℂ f S) (hm : MapsTo f S S) (j : ℕ) :
    AnalyticOnNhd ℂ f^[j] S := by
  induction j with
  | zero => exact analyticOnNhd_id
  | succ j hj =>
    rw [Function.iterate_succ]
    exact hj.comp hf hm

lemma iterateAverage_analytic {S : Set E} {f : E → E}
    (hf : AnalyticOnNhd ℂ f S) (hm : MapsTo f S S) (N : ℕ) :
    AnalyticOnNhd ℂ (iterateAverage f N) S := by
  apply AnalyticOnNhd.const_smul
  apply Finset.analyticOnNhd_fun_sum
  intro j _
  exact analyticOnNhd_iterate hf hm j

lemma iterateAverage_bound {S : Set E} {f : E → E} (hm : MapsTo f S S)
    {M : ℝ} (hb : ∀ x ∈ S, ‖x‖ ≤ M) (N : ℕ) {x : E} (hx : x ∈ S) :
    ‖iterateAverage f N x‖ ≤ M := by
  have hn : (N+1 : ℝ) ≠ 0 := by positivity
  calc
    ‖iterateAverage f N x‖ = (N+1 : ℝ)⁻¹ * ‖∑ j ∈ Finset.range (N+1), f^[j] x‖ := by
      rw [iterateAverage,norm_smul,norm_inv]
      rw [show (N : ℂ)+1 = ((N+1 : ℕ) : ℂ) by simp only [Nat.cast_add, Nat.cast_one],
        Complex.norm_natCast]
      simp only [Nat.cast_add,Nat.cast_one]
    _ ≤ (N+1 : ℝ)⁻¹ * ∑ j ∈ Finset.range (N+1), ‖f^[j] x‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ ≤ (N+1 : ℝ)⁻¹ * ∑ _j ∈ Finset.range (N+1), M := by
      gcongr with j _
      exact hb _ ((hm.iterate j) hx)
    _ = M := by simp [hn]

lemma iterateAverage_deriv_fixed {f : E → E} {p : E}
    (hp : f p = p) (hd : HasFDerivAt f (1 : E →L[ℂ] E) p) (N : ℕ) :
    HasFDerivAt (iterateAverage f N) (1 : E →L[ℂ] E) p := by
  have h : ∀ j : ℕ, HasFDerivAt f^[j] (1 : E →L[ℂ] E) p := fun j => by
    simpa using hd.iterate hp j
  have ha := (HasFDerivAt.sum (fun j (_hj : j ∈ Finset.range (N+1)) => h j)).const_smul
    ((N+1 : ℂ)⁻¹)
  have hnC : (N : ℂ)+1 ≠ 0 := by exact_mod_cast (show (N : ℝ)+1 ≠ 0 by positivity)
  simp only [Finset.sum_const,Finset.card_range, ← Nat.cast_smul_eq_nsmul ℂ,
    Nat.cast_add,Nat.cast_one,smul_smul,inv_mul_cancel₀ hnC,one_smul] at ha
  convert ha using 1
  all_goals try with_reducible_and_instances rfl
  ext x
  simp only [iterateAverage,Pi.smul_apply,Finset.sum_apply]

lemma iterateAverage_coboundary (f : E → E) (N : ℕ) (x : E) :
    iterateAverage f N (f x)-iterateAverage f N x =
      (N+1 : ℂ)⁻¹ • (f^[N+1] x-x) := by
  simp only [iterateAverage,← smul_sub,← Finset.sum_sub_distrib]
  congr 1
  have he : ∀ j, f^[j] (f x) = f^[j+1] x := fun j => (Function.iterate_succ_apply f j x).symm
  simp only [he]
  exact Finset.sum_range_sub (fun j => f^[j] x) (N+1)

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_CartanUniqueness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Metric
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

lemma iterateAverage_coboundary_tendsto {S : Set E} {f : E → E}
    (hm : MapsTo f S S) {M : ℝ} (hb : ∀ x ∈ S, ‖x‖ ≤ M)
    {x : E} (hx : x ∈ S) :
    Tendsto (fun N => iterateAverage f N (f x)-iterateAverage f N x) atTop (𝓝 0) := by
  have he : ∀ N : ℕ, ‖iterateAverage f N (f x)-iterateAverage f N x‖ ≤
      (N+1 : ℝ)⁻¹*(2*M) := by
    intro N
    rw [iterateAverage_coboundary,norm_smul,norm_inv]
    rw [show (N : ℂ)+1 = ((N+1 : ℕ) : ℂ) by push_cast; rfl, Complex.norm_natCast]
    simp only [Nat.cast_add,Nat.cast_one]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact (norm_sub_le _ _).trans (by linarith [hb _ ((hm.iterate (N+1)) hx),hb x hx])
  apply squeeze_zero_norm he
  have hlim : Tendsto (fun N : ℕ => ((N : ℝ)+1)⁻¹) atTop (𝓝 0) :=
    by
      have ht := tendsto_inv_atTop_zero.comp ((tendsto_natCast_atTop_atTop (R := ℝ)).comp
        (Filter.tendsto_add_atTop_nat 1))
      simpa only [Function.comp_def,Nat.cast_add,Nat.cast_one] using ht
  simpa using hlim.mul_const (2*M)

theorem cartan_uniqueness_bounded [ProperSpace E] [SecondCountableTopology E]
    {S : Set E} (hS : IsOpen S) (hconn : IsPreconnected S)
    (hb : Bornology.IsBounded S) {f : E → E}
    (hf : AnalyticOnNhd ℂ f S) (hm : MapsTo f S S)
    {p : E} (hp : p ∈ S) (hfix : f p = p)
    (hd : HasFDerivAt f (1 : E →L[ℂ] E) p) : EqOn f id S := by
  obtain ⟨M,hM,hbM⟩ := hb.exists_pos_norm_le
  obtain ⟨g,hg,φ,hφ,hconv⟩ := montel_expanding_domains hS (iterateAverage f) (by
    intro x hx
    obtain ⟨r,hr,hrs⟩ := Metric.mem_nhds_iff.mp (hS.mem_nhds hx)
    exact ⟨r,hr,M,hM,hrs,Eventually.of_forall (fun N =>
      ⟨(iterateAverage_analytic hf hm N).differentiableOn.mono hrs,
        fun y hy => iterateAverage_bound hm hbM N (hrs hy)⟩)⟩)
  have hhol : ∀ x ∈ S, ∃ W ∈ 𝓝 x, ∀ᶠ j in atTop,
      AnalyticOnNhd ℂ (iterateAverage f (φ j)) W := by
    intro x hx
    exact ⟨S,hS.mem_nhds hx,Eventually.of_forall (fun j => iterateAverage_analytic hf hm (φ j))⟩
  have hdiff : ∀ x ∈ S, ∃ W ∈ 𝓝 x, ∀ᶠ j in atTop,
      DifferentiableOn ℂ (iterateAverage f (φ j)) W := by
    intro x hx
    obtain ⟨W,hW,hw⟩ := hhol x hx
    exact ⟨W,hW,hw.mono (fun _ hj => hj.differentiableOn)⟩
  have hder : fderiv ℂ g p = 1 := by
    have ht := (tendstoLocallyUniformlyOn_fderiv hS hconv hdiff).tendsto_at hp
    have he : (fun j => fderiv ℂ (iterateAverage f (φ j)) p) = fun _ : ℕ => 1 := by
      funext j
      exact (iterateAverage_deriv_fixed hfix hd (φ j)).fderiv
    rw [he] at ht
    exact tendsto_nhds_unique ht tendsto_const_nhds
  have hstrict : HasStrictFDerivAt g (1 : E →L[ℂ] E) p := by
    rw [← hder]
    apply hasStrictFDerivAt_of_hasFDerivAt_of_continuousAt
    · filter_upwards [hS.mem_nhds hp] with x hx
      exact (hg.differentiableAt (hS.mem_nhds hx)).hasFDerivAt
    · exact continuousAt_fderiv_of_locally_uniform_analytic hS hconv hhol hp
  have hgf : EqOn (g ∘ f) g S := by
    intro x hx
    have ht := ((hconv.tendsto_at (hm hx)).sub (hconv.tendsto_at hx))
    have hz := (iterateAverage_coboundary_tendsto hm hbM hx).comp hφ.tendsto_atTop
    exact sub_eq_zero.mp (tendsto_nhds_unique ht hz)
  have hleft := (show HasStrictFDerivAt g
    ((ContinuousLinearEquiv.refl ℂ E) : E →L[ℂ] E) p from by simpa only [ContinuousLinearEquiv.coe_refl,ContinuousLinearMap.one_def] using hstrict).eventually_left_inverse
  have hfc : Tendsto f (𝓝 p) (𝓝 p) := by
    simpa only [hfix] using (hf p hp).continuousAt.tendsto
  have heq : f =ᶠ[𝓝 p] id := by
    filter_upwards [hleft,hfc hleft,hS.mem_nhds hp] with x hx hfx hxs
    simp only [Set.mem_preimage,Set.mem_ofPred_eq] at hfx
    rw [show g (f x) = g x from hgf hxs] at hfx
    exact hfx.symm.trans hx
  exact hf.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_id hconn hp heq

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_AnalyticMulZeroGerm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061

open Set Filter Topology

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]

def analyticGermRing : Subring (Filter.Germ (𝓝 (0 : E)) ℂ) where
  carrier := {g | ∃ f : E → ℂ, AnalyticAt ℂ f 0 ∧ (f : Filter.Germ (𝓝 (0 : E)) ℂ) = g}
  zero_mem' := ⟨0, analyticAt_const, rfl⟩
  one_mem' := ⟨1, analyticAt_const, rfl⟩
  add_mem' := by
    rintro _ _ ⟨f,hf,rfl⟩ ⟨g,hg,rfl⟩
    exact ⟨f+g, hf.add hg, rfl⟩
  neg_mem' := by
    rintro _ ⟨f,hf,rfl⟩
    exact ⟨-f,hf.neg,rfl⟩
  mul_mem' := by
    rintro _ _ ⟨f,hf,rfl⟩ ⟨g,hg,rfl⟩
    exact ⟨f*g,hf.mul hg,rfl⟩

abbrev AnalyticGerm := analyticGermRing E

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_VectorLift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061.AnalyticLift
variable {d j : ℕ} {A : Type*} [NormedCommRing A] [NormedAlgebra ℝ A] [NormOneClass A]

def monomial (σ : Fin j → Fin d) : ContinuousMultilinearMap ℝ (fun _ : Fin j => Fin d → A) A :=
  (ContinuousMultilinearMap.mkPiAlgebraFin ℝ j A).compContinuousLinearMap
    (fun i => ContinuousLinearMap.proj (σ i))

def coefficient (p : ContinuousMultilinearMap ℝ (fun _ : Fin j => Fin d → ℝ) ℝ) :
    ContinuousMultilinearMap ℝ (fun _ : Fin j => Fin d → A) A :=
  ∑ σ : Fin j → Fin d, (p (fun i => Pi.single (σ i) 1)) • monomial σ

def series (p : FormalMultilinearSeries ℝ (Fin d → ℝ) ℝ) :
    FormalMultilinearSeries ℝ (Fin d → A) A := fun j => coefficient (p j)

end Release061.AnalyticLift

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_WeightedTaylorUniformlyCompact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061

open Set Filter Metric Asymptotics
open scoped Topology

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

def weightedScale (t : ℝ) (x : E × F) : E × F :=
  (Real.sqrt t • x.1,t • x.2)

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_CompactFaithfulIsotropy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061

open Set Filter Topology TopologicalSpace
open scoped Classical
namespace Biholomorph
variable {n : ℕ} {U : Set (Affine n)}

def ambientAut (a : Biholomorph U U) : Affine n → Affine n :=
  ambientExtend (fun x : U => (a.toHomeomorph x).val)

@[simp] theorem ambientAut_apply (a : Biholomorph U U) (p : U) :
    a.ambientAut p.val=(a.toHomeomorph p).val := ambientExtend_apply _ p

theorem ambientAut_analytic (hU : IsOpen U) (a : Biholomorph U U) :
    AnalyticOnNhd ℂ a.ambientAut U := a.holomorphic_toFun.analyticOnNhd_extend hU

def derivativeAt (a : Biholomorph U U) (p : U) : Affine n →L[ℂ] Affine n :=
  fderiv ℂ a.ambientAut p.val

theorem derivativeAt_mul (hU : IsOpen U) (a b : Biholomorph U U) (p : U) :
    (a*b).derivativeAt p=(a.derivativeAt (b.toHomeomorph p)).comp (b.derivativeAt p) := by
  have he : (a*b).ambientAut =ᶠ[𝓝 p.val] a.ambientAut ∘ b.ambientAut := by
    filter_upwards [hU.mem_nhds p.property] with x hx
    rw [Function.comp_apply,ambientAut_apply (a*b) ⟨x,hx⟩,
      ambientAut_apply b ⟨x,hx⟩,ambientAut_apply a (b.toHomeomorph ⟨x,hx⟩)]
    rfl
  rw [derivativeAt,he.fderiv_eq]
  have hd := fderiv_comp p.val
    (by simpa only [ambientAut_apply] using
      (a.ambientAut_analytic hU _ (b.toHomeomorph p).property).differentiableAt)
    (b.ambientAut_analytic hU _ p.property).differentiableAt
  simpa only [derivativeAt,ambientAut_apply] using hd

@[simp] theorem derivativeAt_one (hU : IsOpen U) (p : U) :
    (1 : Biholomorph U U).derivativeAt p=1 := by
  have he : (1 : Biholomorph U U).ambientAut =ᶠ[𝓝 p.val] id := by
    filter_upwards [hU.mem_nhds p.property] with x hx
    exact ambientAut_apply 1 ⟨x,hx⟩
  rw [derivativeAt,he.fderiv_eq]
  rw [fderiv_id]
  rfl

theorem eq_one_of_firstJet (hU : IsOpen U) (hc : IsPreconnected U)
    (hb : Bornology.IsBounded U) (a : Biholomorph U U) (p : U)
    (hp : a.toHomeomorph p=p) (hd : a.derivativeAt p=1) : a=1 := by
  have he := cartan_uniqueness_bounded hU hc hb (a.ambientAut_analytic hU)
    (fun x hx => by
      rw [show a.ambientAut x=(a.toHomeomorph ⟨x,hx⟩).val from ambientAut_apply a ⟨x,hx⟩]
      exact (a.toHomeomorph ⟨x,hx⟩).property) p.property
    (by simpa only [ambientAut_apply] using congrArg Subtype.val hp)
    (by
      have h := (a.ambientAut_analytic hU _ p.property).differentiableAt.hasFDerivAt
      rwa [← derivativeAt,hd] at h)
  apply ext
  intro q
  apply Subtype.ext
  simpa only [ambientAut_apply,id_eq,one_apply] using he q.property

def firstJet (p : U) (a : Biholomorph U U) : U × (Affine n →L[ℂ] Affine n) :=
  (a.toHomeomorph p,a.derivativeAt p)

theorem ambientAut_tendstoLocallyUniformly {ι : Type*} [LocallyCompactSpace U]
    {a : ι → Biholomorph U U} {b : Biholomorph U U} {l : Filter ι}
    (h : Tendsto a l (𝓝 b)) :
    TendstoLocallyUniformlyOn (fun j => (a j).ambientAut) b.ambientAut l U := by
  let v : C(U,Affine n) := ⟨Subtype.val,continuous_subtype_val⟩
  have ht := (((ContinuousMap.continuous_postcomp v).comp
    continuous_compactOpenPair.fst).tendsto b).comp h
  have hu := ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp ht
  change TendstoLocallyUniformly (fun j (x : U) => ((a j).toHomeomorph x).val)
    (fun x : U => (b.toHomeomorph x).val) l at hu
  apply tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe.mpr
  simpa only [Function.comp_def,ambientAut_apply] using hu

theorem derivativeAt_continuous (hU : IsOpen U) [LocallyCompactSpace U] (p : U) :
    Continuous (fun a : Biholomorph U U => a.derivativeAt p) := by
  apply continuous_iff_seqContinuous.mpr
  intro a b hab
  apply (tendstoLocallyUniformlyOn_fderiv hU (ambientAut_tendstoLocallyUniformly hab) ?_).tendsto_at
    p.property
  intro x hx
  exact ⟨U,hU.mem_nhds hx,Eventually.of_forall fun j => (a j).ambientAut_analytic hU |>.differentiableOn⟩

end Biholomorph
end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_OneParameterDifferentiableZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061

section
open Set Filter Topology Metric MeasureTheory
open scoped Classical

theorem finite_measure_holomorphic_average_derivative {K : Type*} [TopologicalSpace K]
    [MeasurableSpace K] [BorelSpace K]
    (μ : Measure K) [IsFiniteMeasure μ] {n m : ℕ} {U : Set (Affine n)}
    (hU : IsOpen U) (F : K → Affine n → Affine m)
    (ha : ∀ a, AnalyticOnNhd ℂ (F a) U)
    (hc : ∀ x ∈ U, Continuous (fun a => F a x))
    (hdc : ∀ x ∈ U, Continuous (fun a => fderiv ℂ (F a) x))
    {M : ℝ} (hM : ∀ a, ∀ x ∈ U, ‖F a x‖ ≤ M)
    {p : Affine n} (hp : p ∈ U) :
    HasFDerivAt (fun x => ∫ a, F a x ∂μ) (∫ a, fderiv ℂ (F a) p ∂μ) p := by
  obtain ⟨R,hR,hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hp)
  have hsub : ∀ x ∈ ball p (R/2), ball x (R/2) ⊆ U := by
    intro x hx y hy
    apply hball
    rw [mem_ball] at *
    exact (dist_triangle y x p).trans_lt (by linarith)
  have hbound : ∀ a, ∀ x ∈ ball p (R/2), ‖fderiv ℂ (F a) x‖ ≤ (2*M)/(R/2) := by
    intro a x hx
    apply Complex.norm_fderiv_le_div_of_mapsTo_ball
      ((ha a).differentiableOn.mono (hsub x hx)) _ (by linarith)
    intro y hy
    rw [mem_closedBall,dist_eq_norm]
    have hxU := hsub x hx (mem_ball_self (by linarith))
    exact (norm_sub_le _ _).trans (by linarith [hM a y (hsub x hx hy),hM a x hxU])
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le (bound := fun _ => (2*M)/(R/2))
    (ball_mem_nhds p (by linarith : 0<R/2))
  · filter_upwards [hU.mem_nhds hp] with x hx
    exact (hc x hx).aestronglyMeasurable
  · exact ⟨(hc p hp).aestronglyMeasurable,HasFiniteIntegral.of_bounded (ae_of_all μ (fun a => hM a p hp))⟩
  · exact (hdc p hp).aestronglyMeasurable
  · exact ae_of_all μ hbound
  · exact integrable_const _
  · exact ae_of_all μ (fun a x hx => (ha a _ (hsub x hx (mem_ball_self (by linarith)))).differentiableAt.hasFDerivAt)

end

open Set Filter Topology Metric MeasureTheory
namespace Biholomorph
variable {n : ℕ} {U : Set (Affine n)} (hU : IsOpen U) [LocallyCompactSpace U]
variable (a : ℝ → Biholomorph U U) (ha : Continuous a)

def shortTimeAverage (r : ℝ) (x : Affine n) : Affine n :=
  r⁻¹ • ∫ t in 0..r, (a t).ambientAut x

include ha
omit [LocallyCompactSpace U] in
theorem oneParameter_evaluation_continuous (x : U) :
    Continuous (fun t => (a t).toHomeomorph x) := (continuous_evaluation x).comp ha

include hU
theorem shortTimeAverage_derivative (hb : Bornology.IsBounded U) {r : ℝ} (hr : 0 < r)
    {p : Affine n} (hp : p ∈ U) :
    HasFDerivAt (shortTimeAverage a r)
      (r⁻¹ • ∫ t in 0..r, (a t).derivativeAt ⟨p,hp⟩) p := by
  obtain ⟨M,hM,hMb⟩ := hb.exists_pos_norm_le
  have hv : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) r)) :=
    ⟨by simp [Real.volume_Ioc]⟩
  have hd := finite_measure_holomorphic_average_derivative
    (M := M) (volume.restrict (Ioc (0 : ℝ) r)) hU (fun t => (a t).ambientAut)
    (fun t => (a t).ambientAut_analytic hU)
    (fun x hx => by
      have h := continuous_subtype_val.comp (oneParameter_evaluation_continuous a ha ⟨x,hx⟩)
      simpa only [Function.comp_def,← ambientAut_apply] using h)
    (fun x hx => (derivativeAt_continuous hU ⟨x,hx⟩).comp ha)
    (fun t x hx => by
      rw [ambientAut_apply (a t) ⟨x,hx⟩]
      exact hMb _ ((a t).toHomeomorph ⟨x,hx⟩).property) hp
  unfold shortTimeAverage
  convert! hd.const_smul r⁻¹ using 1 <;> simp only [intervalIntegral.integral_of_le hr.le,derivativeAt]
  rfl

theorem shortTimeAverage_analytic (hb : Bornology.IsBounded U) {r : ℝ} (hr : 0 < r) :
    AnalyticOnNhd ℂ (shortTimeAverage a r) U := by
  apply analyticOnNhd_of_differentiableOn_affine hU
  intro p hp
  exact (shortTimeAverage_derivative hU a ha hb hr hp).differentiableAt.differentiableWithinAt

theorem shortTimeAverage_linear_tendsto (hzero : a 0=1) (p : U) :
    Tendsto (fun r : ℝ => r⁻¹ • ∫ t in 0..r, (a t).derivativeAt p)
      (𝓝[>] 0) (𝓝 (1 : Affine n →L[ℂ] Affine n)) := by
  have hc := (derivativeAt_continuous hU p).comp ha
  have hd := intervalIntegral.integral_hasDerivAt_right
    (hc.intervalIntegrable 0 0) hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  have he : (a 0).derivativeAt p=(1 : Affine n →L[ℂ] Affine n) := by
    rw [hzero,derivativeAt_one hU]
  simpa only [Function.comp_def,zero_add,intervalIntegral.integral_same,sub_zero,he] using hd.tendsto_slope_zero_right

omit hU [LocallyCompactSpace U] in

theorem shortTimeAverage_orbit_derivative
    (hmul : ∀ s t, a (s+t)=a s*a t) (r : ℝ) (p : U) (s : ℝ) :
    HasDerivAt (fun t => shortTimeAverage a r ((a t).toHomeomorph p).val)
      (r⁻¹ • (((a (r+s)).toHomeomorph p).val-((a s).toHomeomorph p).val)) s := by
  let f : ℝ → Affine n := fun t => ((a t).toHomeomorph p).val
  have hc : Continuous f := continuous_subtype_val.comp (oneParameter_evaluation_continuous a ha p)
  have he (t : ℝ) : shortTimeAverage a r ((a t).toHomeomorph p).val =
      r⁻¹ • ∫ v in t..r+t, f v := by
    unfold shortTimeAverage
    congr 1
    have h (u : ℝ) : (a u).ambientAut ((a t).toHomeomorph p).val = f (u+t) := by
      dsimp only [f]
      rw [ambientAut_apply,hmul]
      rfl
    simp_rw [h]
    simpa only [zero_add] using intervalIntegral.integral_comp_add_right (a := 0) (b := r) f t
  simp_rw [he]
  have hd := intervalIntegral.integral_hasFDerivAt (hc.intervalIntegrable s (r+s))
    hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.stronglyMeasurable.stronglyMeasurableAtFilter
    hc.continuousAt hc.continuousAt
  have hg : HasDerivAt (fun t : ℝ => (t,r+t)) (1,1) s :=
    (hasDerivAt_id s).prodMk ((hasDerivAt_id s).const_add r)
  convert! (hd.comp_hasDerivAt s hg).const_smul r⁻¹ using 1
  ·
    simp only [FunLike.coe_sub,Pi.sub_apply,ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.coe_snd',ContinuousLinearMap.coe_fst',one_smul,f]

theorem exists_regular_shortTimeAverage (hb : Bornology.IsBounded U)
    (hzero : a 0=1) (p : U) :
    ∃ (r : ℝ), 0 < r ∧ ∃ e : Affine n ≃L[ℂ] Affine n,
      HasStrictFDerivAt (shortTimeAverage a r) (e : Affine n →L[ℂ] Affine n) p.val := by
  have ht := shortTimeAverage_linear_tendsto hU a ha hzero p
  have hu : ∀ᶠ r : ℝ in 𝓝[>] 0,
      IsUnit (r⁻¹ • ∫ t in 0..r, (a t).derivativeAt p) :=
    ht.eventually (Units.isOpen.mem_nhds isUnit_one)
  have hpos : ∀ᶠ r : ℝ in 𝓝[>] 0, 0 < r := self_mem_nhdsWithin
  obtain ⟨r,hr,hunit⟩ := (hpos.and hu).exists
  have hder := shortTimeAverage_derivative hU a ha hb hr p.property
  have hu' : IsUnit (fderiv ℂ (shortTimeAverage a r) p.val) := by
    rwa [hder.fderiv]
  let e := ContinuousLinearEquiv.unitsEquiv ℂ (Affine n) hu'.unit
  refine ⟨r,hr,e,?_⟩
  have he : (e : Affine n →L[ℂ] Affine n) = fderiv ℂ (shortTimeAverage a r) p.val := hu'.unit_spec
  rw [he]
  exact (shortTimeAverage_analytic hU a ha hb hr _ p.property).hasStrictFDerivAt

omit hU [LocallyCompactSpace U] in

theorem oneParameter_hasDerivAt_of_regular_average
    (hzero : a 0=1) (hmul : ∀ s t, a (s+t)=a s*a t)
    (r : ℝ) (p : U) (e : Affine n ≃L[ℂ] Affine n)
    (hF : HasStrictFDerivAt (shortTimeAverage a r) (e : Affine n →L[ℂ] Affine n) p.val) :
    HasDerivAt (fun t => ((a t).toHomeomorph p).val)
      (e.symm (r⁻¹ • (((a r).toHomeomorph p).val-p.val))) 0 := by
  let F := shortTimeAverage a r
  let ψ := hF.localInverse F e p.val
  have hc : Continuous (fun t => ((a t).toHomeomorph p).val) :=
    continuous_subtype_val.comp (oneParameter_evaluation_continuous a ha p)
  have hp : ((a 0).toHomeomorph p).val=p.val := by rw [hzero,one_apply]
  have hi : ∀ᶠ t : ℝ in 𝓝 0, ψ (F ((a t).toHomeomorph p).val)=((a t).toHomeomorph p).val := by
    apply (show Tendsto (fun t => ((a t).toHomeomorph p).val) (𝓝 0) (𝓝 p.val) by
      simpa only [hp] using hc.tendsto 0) hF.eventually_left_inverse
  have ho : HasDerivAt (fun t => F ((a t).toHomeomorph p).val)
      (r⁻¹ • (((a r).toHomeomorph p).val-p.val)) 0 := by
    simpa only [add_zero,hp] using shortTimeAverage_orbit_derivative a ha hmul r p 0
  have hψ : HasFDerivAt ψ (e.symm : Affine n →L[ℂ] Affine n) (F ((a 0).toHomeomorph p).val) := by
    rw [hp]
    exact hF.to_localInverse.hasFDerivAt
  exact ((hψ.restrictScalars ℝ).comp_hasDerivAt 0 ho).congr_of_eventuallyEq (hi.mono (fun _ h => h.symm))

theorem oneParameter_differentiableAt_zero (hb : Bornology.IsBounded U)
    (hzero : a 0=1) (hmul : ∀ s t, a (s+t)=a s*a t) (p : U) :
    DifferentiableAt ℝ (fun t => ((a t).toHomeomorph p).val) 0 := by
  obtain ⟨r,hr,e,hF⟩ := exists_regular_shortTimeAverage hU a ha hb hzero p
  exact (oneParameter_hasDerivAt_of_regular_average a ha hzero hmul r p e hF).differentiableAt

end Biholomorph
end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_InfinitesimalGeneratorEquivariant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Topology Metric MeasureTheory
namespace Biholomorph

section
variable {n : ℕ} {U : Set (Affine n)} (hU : IsOpen U) [LocallyCompactSpace U]
variable (a : ℝ → Biholomorph U U) (ha : Continuous a)

def infinitesimalGenerator (x : Affine n) : Affine n :=
  deriv (fun t => (a t).ambientAut x) 0

include hU ha

theorem infinitesimalGenerator_formula (hb : Bornology.IsBounded U)
    (hzero : a 0=1) (hmul : ∀ s t, a (s+t)=a s*a t)
    {r : ℝ} (hr : 0 < r) {x : Affine n} (hx : x ∈ U)
    (hu : IsUnit (fderiv ℂ (shortTimeAverage a r) x)) :
    infinitesimalGenerator a x = (Ring.inverse (fderiv ℂ (shortTimeAverage a r) x))
      (r⁻¹ • ((a r).ambientAut x-x)) := by
  let e := ContinuousLinearEquiv.unitsEquiv ℂ (Affine n) hu.unit
  have he : (e : Affine n →L[ℂ] Affine n) = fderiv ℂ (shortTimeAverage a r) x := hu.unit_spec
  have hd : HasStrictFDerivAt (shortTimeAverage a r) (e : Affine n →L[ℂ] Affine n) x := by
    rw [he]
    exact (shortTimeAverage_analytic hU a ha hb hr x hx).hasStrictFDerivAt
  have ht := oneParameter_hasDerivAt_of_regular_average a ha hzero hmul r ⟨x,hx⟩ e hd
  have hi : Ring.inverse (fderiv ℂ (shortTimeAverage a r) x) = (e.symm : Affine n →L[ℂ] Affine n) := by
    rw [← he,ContinuousLinearMap.ringInverse_equiv,ContinuousLinearMap.inverse_equiv]
  rw [hi]
  unfold infinitesimalGenerator
  simp_rw [ambientAut_apply (a _) ⟨x,hx⟩]
  exact ht.deriv

theorem infinitesimalGenerator_analytic (hb : Bornology.IsBounded U)
    (hzero : a 0=1) (hmul : ∀ s t, a (s+t)=a s*a t) :
    AnalyticOnNhd ℂ (infinitesimalGenerator a) U := by
  apply analyticOnNhd_of_differentiableOn_affine hU
  intro x hx
  obtain ⟨r,hr,e,he⟩ := exists_regular_shortTimeAverage hU a ha hb hzero ⟨x,hx⟩
  have hF := shortTimeAverage_analytic hU a ha hb hr x hx
  have hu : IsUnit (fderiv ℂ (shortTimeAverage a r) x) := by
    rw [he.hasFDerivAt.fderiv]
    exact ⟨(ContinuousLinearEquiv.unitsEquiv ℂ (Affine n)).symm e,rfl⟩
  have huN : ∀ᶠ y in 𝓝 x, IsUnit (fderiv ℂ (shortTimeAverage a r) y) :=
    hF.fderiv.continuousAt (Units.isOpen.mem_nhds hu)
  have hInv : AnalyticAt ℂ (fun y => Ring.inverse (fderiv ℂ (shortTimeAverage a r) y)) x := by
    have hi : AnalyticAt ℂ Ring.inverse (fderiv ℂ (shortTimeAverage a r) x) := by
      simpa only [hu.unit_spec] using (analyticAt_inverse (𝕜 := ℂ) hu.unit)
    exact hi.comp hF.fderiv
  have hG : DifferentiableAt ℂ (fun y => r⁻¹ • ((a r).ambientAut y-y)) x :=
    (((a r).ambientAut_analytic hU x hx).differentiableAt.sub (differentiableAt_id)).const_smul r⁻¹
  have hc := hInv.differentiableAt.clm_apply hG
  apply (hc.congr_of_eventuallyEq ?_).differentiableWithinAt
  filter_upwards [huN,hU.mem_nhds hx] with y hy hyU
  exact infinitesimalGenerator_formula hU a ha hb hzero hmul hr hyU hy

end

variable {n : ℕ} {U : Set (Affine n)} (hU : IsOpen U) [LocallyCompactSpace U]
variable (a : ℝ → Biholomorph U U) (ha : Continuous a)
include hU ha

theorem oneParameter_hasDerivAt_zero (hb : Bornology.IsBounded U)
    (hzero : a 0=1) (hmul : ∀ s t, a (s+t)=a s*a t) (p : U) :
    HasDerivAt (fun t => ((a t).toHomeomorph p).val) (infinitesimalGenerator a p.val) 0 := by
  have h := (oneParameter_differentiableAt_zero hU a ha hb hzero hmul p).hasDerivAt
  simpa only [infinitesimalGenerator,ambientAut_apply] using h

theorem oneParameter_orbit_ODE (hb : Bornology.IsBounded U)
    (hzero : a 0=1) (hmul : ∀ s t, a (s+t)=a s*a t) (p : U) (s : ℝ) :
    HasDerivAt (fun t => ((a t).toHomeomorph p).val)
      (infinitesimalGenerator a ((a s).toHomeomorph p).val) s := by
  have h0 := oneParameter_hasDerivAt_zero hU a ha hb hzero hmul ((a s).toHomeomorph p)
  have h1 : HasDerivAt (fun t => ((a t).toHomeomorph ((a s).toHomeomorph p)).val)
      (infinitesimalGenerator a ((a s).toHomeomorph p).val) (s-s) := by simpa using h0
  have he (t : ℝ) : ((a (t-s)).toHomeomorph ((a s).toHomeomorph p)).val = ((a t).toHomeomorph p).val := by
    rw [← mul_apply,← hmul]; simp only [sub_add_cancel]
  simpa only [he] using h1.comp_sub_const s s

theorem infinitesimalGenerator_equivariant (hb : Bornology.IsBounded U)
    (hzero : a 0=1) (hmul : ∀ s t, a (s+t)=a s*a t) (p : U) (s : ℝ) :
    infinitesimalGenerator a ((a s).toHomeomorph p).val =
      (a s).derivativeAt p (infinitesimalGenerator a p.val) := by
  have h0 := oneParameter_hasDerivAt_zero hU a ha hb hzero hmul p
  have hp : ((a 0).toHomeomorph p).val=p.val := by rw [hzero,one_apply]
  have hd : HasFDerivAt (a s).ambientAut ((a s).derivativeAt p) ((a 0).toHomeomorph p).val := by
    rw [hp]
    exact ((a s).ambientAut_analytic hU p.val p.property).differentiableAt.hasFDerivAt
  have hc := (hd.restrictScalars ℝ).comp_hasDerivAt 0 h0
  have he (t : ℝ) : (a s).ambientAut ((a t).toHomeomorph p).val =
      ((a t).toHomeomorph ((a s).toHomeomorph p)).val := by
    rw [ambientAut_apply,← mul_apply,← hmul,← mul_apply,← hmul,add_comm s t]
  have hcomp : HasDerivAt (fun t => ((a t).toHomeomorph ((a s).toHomeomorph p)).val)
      ((a s).derivativeAt p (infinitesimalGenerator a p.val)) 0 := by
    convert! hc using 1
    all_goals try with_reducible_and_instances rfl
    simp only [Function.comp_def,he]
  exact (oneParameter_hasDerivAt_zero hU a ha hb hzero hmul ((a s).toHomeomorph p)).unique hcomp

end Biholomorph
end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_OneParameterJointStrict
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Topology Metric MeasureTheory
namespace Biholomorph
variable {n : ℕ} {U : Set (Affine n)} (hU : IsOpen U) [LocallyCompactSpace U]
include hU

theorem ambientAut_joint_continuousAt {q : Biholomorph U U × Affine n} (hq : q.2 ∈ U) :
    ContinuousAt (fun z : Biholomorph U U × Affine n => z.1.ambientAut z.2) q := by
  apply tendsto_nhds_iff_seq_tendsto.mpr
  intro z hz
  have ha := continuous_fst.tendsto q |>.comp hz
  have hx := continuous_snd.tendsto q |>.comp hz
  have hxu : Tendsto (fun j => (z j).2) atTop (𝓝[U] q.2) :=
    tendsto_nhdsWithin_iff.mpr ⟨hx,hx (hU.mem_nhds hq)⟩
  exact (ambientAut_tendstoLocallyUniformly ha).tendsto_comp
    ((q.1.ambientAut_analytic hU q.2 hq).continuousAt.continuousWithinAt) hq hxu

theorem ambientAut_derivative_joint_continuousAt {q : Biholomorph U U × Affine n} (hq : q.2 ∈ U) :
    ContinuousAt (fun z : Biholomorph U U × Affine n => fderiv ℂ z.1.ambientAut z.2) q := by
  apply tendsto_nhds_iff_seq_tendsto.mpr
  intro z hz
  have ha := continuous_fst.tendsto q |>.comp hz
  have hx := continuous_snd.tendsto q |>.comp hz
  have hxu : Tendsto (fun j => (z j).2) atTop (𝓝[U] q.2) :=
    tendsto_nhdsWithin_iff.mpr ⟨hx,hx (hU.mem_nhds hq)⟩
  have hf := tendstoLocallyUniformlyOn_fderiv hU (ambientAut_tendstoLocallyUniformly ha)
    (fun x hx => ⟨U,hU.mem_nhds hx,Eventually.of_forall
      (fun j => ((z j).1.ambientAut_analytic hU).differentiableOn)⟩)
  exact hf.tendsto_comp (q.1.ambientAut_analytic hU q.2 hq).fderiv.continuousAt.continuousWithinAt hq hxu

variable (a : ℝ → Biholomorph U U) (ha : Continuous a)
include ha

theorem oneParameter_joint_hasStrictFDerivAt (hb : Bornology.IsBounded U)
    (hzero : a 0=1) (hmul : ∀ s t, a (s+t)=a s*a t) (s : ℝ) (x : U) :
    HasStrictFDerivAt (fun z : ℝ × Affine n => (a z.1).ambientAut z.2)
      ((ContinuousLinearMap.toSpanSingleton ℝ (infinitesimalGenerator a ((a s).toHomeomorph x).val)).coprod
        (((a s).derivativeAt x).restrictScalars ℝ)) (s,x.val) := by
  have hn : ∀ᶠ z : ℝ × Affine n in 𝓝 (s,x.val), z.2 ∈ U :=
    continuous_snd.continuousAt (hU.mem_nhds x.property)
  have hj : ContinuousAt (fun z : ℝ × Affine n => (a z.1).ambientAut z.2) (s,x.val) :=
    (ambientAut_joint_continuousAt hU x.property).comp
      ((ha.comp continuous_fst).prodMk continuous_snd).continuousAt
  have hdj : ContinuousAt (fun z : ℝ × Affine n => fderiv ℂ (a z.1).ambientAut z.2) (s,x.val) :=
    (ambientAut_derivative_joint_continuousAt hU x.property).comp
      ((ha.comp continuous_fst).prodMk continuous_snd).continuousAt
  have ht : ContinuousAt (fun z : ℝ × Affine n => infinitesimalGenerator a ((a z.1).ambientAut z.2)) (s,x.val) := by
    have hg : ContinuousAt (infinitesimalGenerator a) ((a s).ambientAut x.val) := by
      simpa only [ambientAut_apply] using
        (infinitesimalGenerator_analytic hU a ha hb hzero hmul
          ((a s).toHomeomorph x).val ((a s).toHomeomorph x).property).continuousAt
    exact hg.comp (x := (s,x.val)) hj
  have h1 : ∀ᶠ z : ℝ × Affine n in 𝓝 (s,x.val), HasFDerivAt
      (fun t => (a t).ambientAut z.2)
      (ContinuousLinearMap.toSpanSingleton ℝ (infinitesimalGenerator a ((a z.1).ambientAut z.2))) z.1 := by
    filter_upwards [hn] with z hz
    simpa only [ambientAut_apply (a _) ⟨z.2,hz⟩] using
      (oneParameter_orbit_ODE hU a ha hb hzero hmul ⟨z.2,hz⟩ z.1).hasFDerivAt
  have h2 : ∀ᶠ z : ℝ × Affine n in 𝓝 (s,x.val), HasFDerivAt
      (fun y => (a z.1).ambientAut y)
      ((fderiv ℂ (a z.1).ambientAut z.2).restrictScalars ℝ) z.2 := by
    filter_upwards [hn] with z hz
    exact ((a z.1).ambientAut_analytic hU z.2 hz).differentiableAt.hasFDerivAt.restrictScalars ℝ
  have h := hasStrictFDerivAt_uncurry_coprod
    (𝕜 := ℝ) (u := (s,x.val)) (f := fun t y => (a t).ambientAut y)
    (f₁ := fun t y => ContinuousLinearMap.toSpanSingleton ℝ
      (infinitesimalGenerator a ((a t).ambientAut y)))
    (f₂ := fun t y => (fderiv ℂ (a t).ambientAut y).restrictScalars ℝ) h1 h2
    ((ContinuousLinearMap.toSpanSingletonCLE (𝕜 := ℝ) (E := Affine n)).continuous.continuousAt.comp ht)
    ((ContinuousLinearMap.continuous_restrictScalars ℝ).continuousAt.comp hdj)
  dsimp only [Function.HasUncurry.uncurry, Function.hasUncurryInduction,
    Function.hasUncurryBase, id_eq] at h
  simpa only [ambientAut_apply,derivativeAt] using h

end Biholomorph
end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_CurvePowerDisplacement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061

namespace Biholomorph

section
open Set Filter Topology Metric MeasureTheory
open scoped NNReal
open scoped NNReal
variable {n : ℕ} {U : Set (Affine n)} (hU : IsOpen U) [LocallyCompactSpace U]
variable (a b : ℝ → Biholomorph U U) (ha : Continuous a) (hb : Continuous b)
include hU ha hb

theorem productCurve_joint_hasStrictFDerivAt (hbd : Bornology.IsBounded U)
    (ha0 : a 0=1) (ham : ∀ s t, a (s+t)=a s*a t)
    (hb0 : b 0=1) (hbm : ∀ s t, b (s+t)=b s*b t) (p : U) :
    HasStrictFDerivAt (fun z : ℝ × Affine n => (a z.1*b z.1).ambientAut z.2)
      ((ContinuousLinearMap.toSpanSingleton ℝ
        (infinitesimalGenerator a p.val+infinitesimalGenerator b p.val)).coprod 1) (0,p.val) := by
  have hA := oneParameter_joint_hasStrictFDerivAt hU a ha hbd ha0 ham 0 p
  have hB := oneParameter_joint_hasStrictFDerivAt hU b hb hbd hb0 hbm 0 p
  rw [ha0,one_apply,derivativeAt_one hU] at hA
  rw [hb0,one_apply,derivativeAt_one hU] at hB
  have hB0 : (b 0).ambientAut p.val=p.val := by rw [hb0,ambientAut_apply,one_apply]
  have he : (fun z : ℝ × Affine n => (a z.1*b z.1).ambientAut z.2) =ᶠ[𝓝 (0,p.val)]
      (fun z : ℝ × Affine n => (a z.1).ambientAut ((b z.1).ambientAut z.2)) := by
    filter_upwards [continuous_snd.continuousAt (hU.mem_nhds p.property)] with z hz
    rw [ambientAut_apply (a z.1*b z.1) ⟨z.2,hz⟩, mul_apply,
      ambientAut_apply (b z.1) ⟨z.2,hz⟩,ambientAut_apply]
  rw [show ((0 : ℝ),p.val)=(0,(b 0).ambientAut p.val) from by rw [hB0]] at hA
  have hC := hA.comp ((0 : ℝ),p.val)
    ((hasStrictFDerivAt_fst (𝕜 := ℝ) (p := ((0 : ℝ),p.val))).prodMk hB)
  have hD :
      (((ContinuousLinearMap.toSpanSingleton ℝ (infinitesimalGenerator a p.val)).coprod
        ((1 : Affine n →L[ℂ] Affine n).restrictScalars ℝ)).comp
        ((ContinuousLinearMap.fst ℝ ℝ (Affine n)).prod
          ((ContinuousLinearMap.toSpanSingleton ℝ (infinitesimalGenerator b p.val)).coprod
            ((1 : Affine n →L[ℂ] Affine n).restrictScalars ℝ)))) =
      ((ContinuousLinearMap.toSpanSingleton ℝ
        (infinitesimalGenerator a p.val+infinitesimalGenerator b p.val)).coprod 1) := by
    apply DFunLike.ext
    intro z
    change z.1 • infinitesimalGenerator a p.val +
      (z.1 • infinitesimalGenerator b p.val+z.2) =
      z.1 • (infinitesimalGenerator a p.val+infinitesimalGenerator b p.val)+z.2
    rw [smul_add,add_assoc]
  rw [hD] at hC
  exact hC.congr_of_eventuallyEq he.symm

end

open Set Filter Topology Metric MeasureTheory
open scoped NNReal
variable {n : ℕ} {U : Set (Affine n)} (hU : IsOpen U)
include hU

theorem curve_uniform_displacement (c : ℝ → Biholomorph U U) (hc0 : c 0=1)
    (p : U) {A : (ℝ × Affine n) →L[ℝ] Affine n}
    (hd : HasStrictFDerivAt (fun z : ℝ × Affine n => (c z.1).ambientAut z.2) A (0,p.val)) :
    ∃ r > (0:ℝ), ∃ L : ℝ≥0, closedBall p.val r ⊆ U ∧
      ∀ t : ℝ, |t| ≤ r → ∀ y ∈ closedBall p.val r,
        ‖(c t).ambientAut y-y‖ ≤ L*|t| := by
  obtain ⟨L,S,hS,hL⟩ := hd.exists_lipschitzOnWith
  obtain ⟨r,hr,hrs⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hS
  obtain ⟨R,hR,hRU⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds p.property)
  refine ⟨min r R,lt_min hr hR,L,fun y hy => hRU (closedBall_subset_closedBall (min_le_right _ _) hy),?_⟩
  intro t ht y hy
  have hyr : dist y p.val ≤ r := (mem_closedBall.mp hy).trans (min_le_left _ _)
  have htr : |t| ≤ r := ht.trans (min_le_left _ _)
  have hts : (t,y) ∈ S := hrs (by simpa only [mem_closedBall,Prod.dist_eq,Real.dist_eq,
    sub_zero,max_le_iff] using And.intro htr hyr)
  have hzs : ((0:ℝ),y) ∈ S := hrs (by simpa only [mem_closedBall,Prod.dist_eq,
    dist_self,max_le_iff] using And.intro hr.le hyr)
  have hyu : y ∈ U := hRU (closedBall_subset_closedBall (min_le_right _ _) hy)
  have h0 : (c 0).ambientAut y=y := by rw [hc0,ambientAut_apply 1 ⟨y,hyu⟩,one_apply]
  have hv := hL.dist_le_mul (x := (t,y)) (y := (0,y)) hts hzs
  simpa [h0,dist_eq_norm,Prod.norm_def] using hv

omit hU

theorem curve_power_displacement (c : ℝ → Biholomorph U U) (p : U)
    {r : ℝ} {L : ℝ≥0}
    (hstep : ∀ t : ℝ, |t| ≤ r → ∀ y ∈ closedBall p.val r,
      ‖(c t).ambientAut y-y‖ ≤ L*|t|)
    {t : ℝ} {N : ℕ} (hN : N ≠ 0) (ht : |t| ≤ r) (hLt : L*|t| ≤ r) :
    ∀ j ≤ N, dist (((c (t/N))^j).toHomeomorph p).val p.val ≤ (j:ℝ)*(L*|t|/(N:ℝ)) := by
  have hNr : (0:ℝ)<N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN)
  have hN1 : (1:ℝ)≤N := Nat.one_le_cast.mpr (Nat.one_le_iff_ne_zero.mpr hN)
  have hdiv : |t/(N:ℝ)| ≤ r := by
    rw [abs_div,abs_of_pos hNr]
    exact (div_le_self (abs_nonneg t) hN1).trans ht
  intro j hj
  induction j with
  | zero => simp [one_apply]
  | succ j ih =>
    have hjN : j≤N := (Nat.le_succ j).trans hj
    have hi := ih hjN
    have hsmall : dist (((c (t/N))^j).toHomeomorph p).val p.val ≤ r := by
      refine hi.trans ((mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hjN)
        (div_nonneg (mul_nonneg L.coe_nonneg (abs_nonneg t)) hNr.le)).trans ?_)
      simpa only [mul_div_cancel₀ _ (ne_of_gt hNr)] using hLt
    have hst := hstep (t/N) hdiv (((c (t/N))^j).toHomeomorph p).val hsmall
    rw [ambientAut_apply] at hst
    have hdist := dist_triangle
      (((c (t/N))^ (j+1)).toHomeomorph p).val
      (((c (t/N))^j).toHomeomorph p).val p.val
    rw [pow_succ',mul_apply]
    rw [pow_succ',mul_apply] at hdist
    refine hdist.trans ?_
    rw [dist_eq_norm]
    refine (add_le_add hst hi).trans_eq ?_
    rw [abs_div,abs_of_pos hNr,Nat.cast_add,Nat.cast_one]
    ring

end Biholomorph
end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_CurveUniformConsistency
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Topology Metric MeasureTheory
open scoped NNReal
namespace Biholomorph

section
variable {n : ℕ} {U : Set (Affine n)} (hU : IsOpen U) [LocallyCompactSpace U]
include hU

theorem productCurve_powers_uniform_compact (hc : IsPreconnected U)
    (hbd : Bornology.IsBounded U)
    (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
    [MulAction Γ U] [ProperSMul Γ U]
    [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val))
    (a b : ℝ → Biholomorph U U) (ha : Continuous a) (hb : Continuous b)
    (ha0 : a 0=1) (ham : ∀ s t, a (s+t)=a s*a t)
    (hb0 : b 0=1) (hbm : ∀ s t, b (s+t)=b s*b t) (p : U) :
    ∃ δ > (0:ℝ), ∃ K : Set (Biholomorph U U), IsCompact K ∧
      ∀ t : ℝ, |t| ≤ δ → ∀ N : ℕ, ∀ j ≤ N+1,
        (a (t/(N+1))*b (t/(N+1)))^j ∈ K := by
  let c : ℝ → Biholomorph U U := fun t => a t*b t
  obtain ⟨r,hr,L,hRU,hstep⟩ := curve_uniform_displacement hU c (by simp [c,ha0,hb0]) p
    (productCurve_joint_hasStrictFDerivAt hU a b ha hb hbd ha0 ham hb0 hbm p)
  let δ : ℝ := min r (r/(L+1))
  have hL1 : 0 < (L:ℝ)+1 := by positivity
  have hδ : 0<δ := lt_min hr (div_pos hr hL1)
  let V : Set U := Subtype.val ⁻¹' closedBall p.val r
  have hV : IsCompact V := by
    apply IsEmbedding.subtypeVal.isCompact_iff.mpr
    simpa only [V,image_preimage_eq_inter_range,Subtype.range_coe_subtype,ofPred_mem_eq,
      inter_eq_left.mpr hRU] using isCompact_closedBall p.val r
  let K : Set (Biholomorph U U) := (fun e : Biholomorph U U => e.toHomeomorph p) ⁻¹' V
  refine ⟨δ,hδ,K,(bounded_divisible_automorphism_evaluation_proper hU hc hbd Γ hhol p).isCompact_preimage hV,?_⟩
  intro t ht N j hj
  have htr : |t| ≤ r := ht.trans (min_le_left _ _)
  have hLt : (L:ℝ)*|t| ≤ r := by
    have hh : |t| *((L:ℝ)+1) ≤ r := (le_div_iff₀ hL1).mp (ht.trans (min_le_right _ _))
    nlinarith [abs_nonneg t]
  have hi := curve_power_displacement c p hstep (Nat.succ_ne_zero N) htr hLt j hj
  have hNr : (0:ℝ)<(N+1:ℕ) := Nat.cast_pos.mpr (Nat.succ_pos N)
  have hbound : (j:ℝ)*(L*|t|/((N+1:ℕ):ℝ)) ≤ r := by
    calc
      _ ≤ ((N+1:ℕ):ℝ)*(L*|t|/((N+1:ℕ):ℝ)) :=
        mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hj)
          (div_nonneg (mul_nonneg L.coe_nonneg (abs_nonneg t)) hNr.le)
      _ = L*|t| := mul_div_cancel₀ _ (ne_of_gt hNr)
      _ ≤ r := hLt
  change dist (((a (t/(N+1))*b (t/(N+1)))^j).toHomeomorph p).val p.val ≤ r
  simpa only [c,Nat.cast_add,Nat.cast_one,Nat.cast_succ] using hi.trans hbound

end

variable {n : ℕ} {U : Set (Affine n)} (hU : IsOpen U)
include hU

theorem curve_uniform_consistency (c : ℝ → Biholomorph U U) (hc0 : c 0=1)
    (X : Affine n → Affine n) (hX : ContinuousOn X U)
    (hd : ∀ p : U, HasStrictFDerivAt (fun z : ℝ × Affine n => (c z.1).ambientAut z.2)
      ((ContinuousLinearMap.toSpanSingleton ℝ (X p.val)).coprod 1) (0,p.val))
    (K : Set (Affine n)) (hK : IsCompact K) (hKU : K⊆U)
    {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ t : ℝ in 𝓝 0, ∀ y ∈ K, ‖(c t).ambientAut y-y-t • X y‖ ≤ ε*|t| := by
  apply hK.eventually_forall_of_forall_eventually
  intro p hp
  have hpu := hKU hp
  have hdiff := (hd ⟨p,hpu⟩).isLittleO.bound (half_pos hε)
  have hm : ContinuousAt (fun z : ℝ × Affine n => (z,((0:ℝ),z.2))) (0,p) := by fun_prop
  have he : ∀ᶠ z : ℝ × Affine n in 𝓝 (0,p),
      ‖(c z.1).ambientAut z.2-(c 0).ambientAut z.2-z.1 • X p‖ ≤ (ε/2)*|z.1| := by
    have hv := hm.tendsto.eventually hdiff
    filter_upwards [hv] with z hz
    simpa [ContinuousLinearMap.coprod_apply,ContinuousLinearMap.toSpanSingleton_apply,
      Prod.norm_def] using hz
  have hXc : ContinuousAt X p := (hX p hpu).continuousAt (hU.mem_nhds hpu)
  have hx : ∀ᶠ z : ℝ × Affine n in 𝓝 (0,p), ‖X p-X z.2‖ ≤ ε/2 := by
    have hv := (hXc.comp (x := ((0:ℝ),p)) continuous_snd.continuousAt)
      (ball_mem_nhds (X p) (half_pos hε))
    filter_upwards [hv] with z hz
    have hz' : dist (X z.2) (X p) < ε/2 := hz
    simpa only [dist_eq_norm,norm_sub_rev] using hz'.le
  have hu : ∀ᶠ z : ℝ × Affine n in 𝓝 (0,p), z.2 ∈ U :=
    continuous_snd.continuousAt (hU.mem_nhds hpu)
  filter_upwards [he,hx,hu] with z hz hzx hzu
  have h0 : (c 0).ambientAut z.2=z.2 := by rw [hc0,ambientAut_apply 1 ⟨z.2,hzu⟩,one_apply]
  rw [h0] at hz
  have heq : (c z.1).ambientAut z.2-z.2-z.1 • X z.2 =
      ((c z.1).ambientAut z.2-z.2-z.1 • X p)+z.1 • (X p-X z.2) := by
    rw [smul_sub]; abel
  rw [heq]
  calc
    _ ≤ ‖(c z.1).ambientAut z.2-z.2-z.1 • X p‖+‖z.1 • (X p-X z.2)‖ := norm_add_le _ _
    _ ≤ (ε/2)*|z.1|+|z.1| *(ε/2) := by
      rw [norm_smul,Real.norm_eq_abs]
      exact add_le_add hz (mul_le_mul_of_nonneg_left hzx (abs_nonneg _))
    _ = ε*|z.1| := by ring

end Biholomorph
end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_UniformCurveTaylor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061

namespace Biholomorph
open Set Filter Topology Metric MeasureTheory
variable {n : ℕ} {U : Set (Affine n)} (hU : IsOpen U) [LocallyCompactSpace U]
include hU

theorem productCurve_uniform_consistency (hbd : Bornology.IsBounded U)
    (a b : ℝ → Biholomorph U U) (ha : Continuous a) (hb : Continuous b)
    (ha0 : a 0=1) (ham : ∀ s t, a (s+t)=a s*a t)
    (hb0 : b 0=1) (hbm : ∀ s t, b (s+t)=b s*b t)
    (K : Set (Affine n)) (hK : IsCompact K) (hKU : K⊆U)
    {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ t : ℝ in 𝓝 0, ∀ y ∈ K,
      ‖(a t*b t).ambientAut y-y-t • (infinitesimalGenerator a y+infinitesimalGenerator b y)‖ ≤ ε*|t| := by
  apply curve_uniform_consistency hU (fun t => a t*b t) (by simp [ha0,hb0])
    (fun y => infinitesimalGenerator a y+infinitesimalGenerator b y) _ _ K hK hKU hε
  · intro x hx
    exact ((infinitesimalGenerator_analytic hU a ha hbd ha0 ham x hx).continuousAt.add
      (infinitesimalGenerator_analytic hU b hb hbd hb0 hbm x hx).continuousAt).continuousWithinAt
  · exact productCurve_joint_hasStrictFDerivAt hU a b ha hb hbd ha0 ham hb0 hbm
end Biholomorph

open Set Filter Topology Metric
open scoped NNReal

theorem finite_euler_error_bound (u : ℕ → ℝ) {N : ℕ} {c b : ℝ}
    (hc : 1 ≤ c) (hb : 0≤b) (h0 : u 0≤0)
    (hs : ∀ j<N, u (j+1) ≤ c*u j+b) :
    ∀ j≤N, u j ≤ (j:ℝ)*b*c^j := by
  intro j hj
  induction j with
  | zero => simpa only [Nat.cast_zero,zero_mul] using h0
  | succ j ih =>
    have hiv := ih (Nat.le_trans (Nat.le_succ j) hj)
    have hp : 1 ≤ c^(j+1) := one_le_pow₀ hc
    have hmul : c * u j ≤ c * ((j:ℝ)*b*c^j) := mul_le_mul_of_nonneg_left hiv (le_trans zero_le_one hc)
    have hbp : b ≤ b * c^(j+1) := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hp hb
    calc
      u (j+1) ≤ c*u j+b := hs j (by omega)
      _ ≤ c*((j:ℝ)*b*c^j)+b := add_le_add hmul le_rfl
      _ ≤ c*((j:ℝ)*b*c^j)+b*c^(j+1) := add_le_add le_rfl hbp
      _ = ((j+1:ℕ):ℝ)*b*c^(j+1) := by rw [Nat.cast_add,Nat.cast_one,pow_succ]; ring

theorem uniform_curve_taylor {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (α v : ℝ → E) (K : Set ℝ) (hK : IsCompact K)
    (hv : ∀ s∈K, ContinuousAt v s) (hd : ∀ s∈K, HasStrictDerivAt α (v s) s)
    {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ h : ℝ in 𝓝 0, ∀ s∈K, ‖α (s+h)-α s-h • v s‖≤ε*|h| := by
  apply hK.eventually_forall_of_forall_eventually
  intro s hs
  have hm : ContinuousAt (fun z : ℝ × ℝ => (z.2+z.1,z.2)) (0,s) := by fun_prop
  have he := hm.tendsto.eventually (by simpa only [add_zero] using (hd s hs).isLittleO.bound (half_pos hε))
  have hv' := ((hv s hs).comp (x := ((0:ℝ),s)) continuous_snd.continuousAt)
    (ball_mem_nhds (v s) (half_pos hε))
  filter_upwards [he,hv'] with z hz hzs
  have hz' : ‖α (z.2+z.1)-α z.2-z.1 • v s‖ ≤ ε/2*|z.1| := by
    simpa using hz
  have hzv : ‖v s-v z.2‖ ≤ ε/2 := by
    have ht : dist (v z.2) (v s) < ε/2 := hzs
    simpa only [dist_eq_norm,norm_sub_rev] using ht.le
  have heq : α (z.2+z.1)-α z.2-z.1 • v z.2 =
      (α (z.2+z.1)-α z.2-z.1 • v s)+z.1 • (v s-v z.2) := by
    rw [smul_sub]; abel
  rw [heq]
  calc
    _ ≤ ‖α (z.2+z.1)-α z.2-z.1 • v s‖+‖z.1 • (v s-v z.2)‖ := norm_add_le _ _
    _ ≤ ε/2*|z.1|+|z.1| *(ε/2) := by
      rw [norm_smul,Real.norm_eq_abs]
      exact add_le_add hz' (mul_le_mul_of_nonneg_left hzv (abs_nonneg _))
    _ = ε*|z.1| := by ring

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_ConsistentIteratesTendsto
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Topology Metric
open scoped NNReal

theorem finite_euler_comparison {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : E → E) (S : Set E) {L : ℝ≥0} (hL : LipschitzOnWith L X S)
    (x y : ℕ → E) {N : ℕ} {h ε : ℝ} (hε : 0≤ε)
    (h0 : x 0=y 0) (hx : ∀ j<N, x j∈S) (hy : ∀ j<N, y j∈S)
    (hxe : ∀ j<N, ‖x (j+1)-x j-h • X (x j)‖≤ε*|h|)
    (hye : ∀ j<N, ‖y (j+1)-y j-h • X (y j)‖≤ε*|h|) :
    ‖x N-y N‖ ≤ (N:ℝ)*(2*ε*|h|)*Real.exp ((N:ℝ)*L*|h|) := by
  have hs (j : ℕ) (hj : j<N) :
      ‖x (j+1)-y (j+1)‖ ≤ (1+L*|h|)*‖x j-y j‖+2*ε*|h| := by
    have heq : x (j+1)-y (j+1) =
        ((x j-y j)+h • (X (x j)-X (y j)))+
        ((x (j+1)-x j-h • X (x j))-(y (j+1)-y j-h • X (y j))) := by
      rw [smul_sub]; abel
    have hl := hL.norm_sub_le (hx j hj) (hy j hj)
    rw [heq]
    calc
      _ ≤ (‖x j-y j‖+‖h • (X (x j)-X (y j))‖)+
          (‖x (j+1)-x j-h • X (x j)‖+‖y (j+1)-y j-h • X (y j)‖) :=
        (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (norm_sub_le _ _))
      _ ≤ (‖x j-y j‖+|h| *(L*‖x j-y j‖))+(ε*|h|+ε*|h|) := by
        rw [norm_smul,Real.norm_eq_abs]
        exact add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_left hl (abs_nonneg _)))
          (add_le_add (hxe j hj) (hye j hj))
      _ = _ := by ring
  have hb : 0≤2*ε*|h| := by positivity
  have hc : 1≤1+(L:ℝ)*|h| := le_add_of_nonneg_right (mul_nonneg L.coe_nonneg (abs_nonneg _))
  have hf := finite_euler_error_bound (fun j => ‖x j-y j‖) hc hb (by simp [h0]) hs N le_rfl
  refine hf.trans (mul_le_mul_of_nonneg_left ?_ (mul_nonneg (Nat.cast_nonneg N) hb))
  calc
    (1+(L:ℝ)*|h|)^N ≤ (Real.exp (L*|h|))^N := by
      exact pow_le_pow_left₀ (by positivity) (by simpa only [add_comm] using Real.add_one_le_exp (L*|h|)) _
    _ = Real.exp ((N:ℝ)*L*|h|) := by rw [← Real.exp_nat_mul]; congr 1; ring

theorem consistent_iterates_tendsto {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (c : ℝ → E → E) (X : E → E) (K : Set E) {L : ℝ≥0}
    (hL : LipschitzOnWith L X K)
    (hcons : ∀ ε : ℝ, 0<ε → ∀ᶠ h : ℝ in 𝓝 0, ∀ x∈K,
      ‖c h x-x-h • X x‖≤ε*|h|)
    (p : E) (α : ℝ → E) (t : ℝ) (hα0 : α 0=p)
    (hαK : ∀ s∈Icc (-|t|) |t|, α s∈K)
    (hαd : ∀ s∈Icc (-|t|) |t|, HasStrictDerivAt α (X (α s)) s)
    (hαv : ∀ s∈Icc (-|t|) |t|, ContinuousAt (fun s => X (α s)) s)
    (hit : ∀ N : ℕ, ∀ j≤N+1, ((c (t/(N+1)))^[j]) p∈K) :
    Tendsto (fun N : ℕ => ((c (t/(N+1)))^[N+1]) p) atTop (𝓝 (α t)) := by
  apply Metric.tendsto_atTop.mpr
  intro η hη
  let C : ℝ := 2*|t| *Real.exp (L*|t|)
  have hC : 0≤C := by dsimp [C]; positivity
  let ε : ℝ := η/(C+1)
  have hε : 0<ε := div_pos hη (by linarith)
  have hεC : ε*C<η := by
    have he : ε*(C+1)=η := div_mul_cancel₀ η (by linarith)
    nlinarith
  have hdiv : Tendsto (fun N : ℕ => t/(N+1:ℕ)) atTop (𝓝 (0:ℝ)) :=
    (tendsto_const_div_atTop_nhds_zero_nat t).comp (tendsto_add_atTop_nat 1)
  have he := hdiv.eventually (hcons ε hε)
  have hy := hdiv.eventually (uniform_curve_taylor α (fun s => X (α s))
    (Icc (-|t|) |t|) isCompact_Icc hαv hαd hε)
  have hev : ∀ᶠ N : ℕ in atTop, dist (((c (t/(N+1)))^[N+1]) p) (α t)<η := by
    filter_upwards [he,hy] with N hN hNy
    have hNr : (0:ℝ)<(N+1:ℕ) := Nat.cast_pos.mpr (Nat.succ_pos N)
    have hNe : ((N+1:ℕ):ℝ)≠0 := ne_of_gt hNr
    let h : ℝ := t/(N+1:ℕ)
    let x : ℕ → E := fun j => ((c h)^[j]) p
    let y : ℕ → E := fun j => α ((j:ℝ)*h)
    have hsj {j : ℕ} (hj : j≤N+1) : (j:ℝ)*h ∈ Icc (-|t|) |t| := by
      have hj0 : (0:ℝ)≤j := Nat.cast_nonneg j
      have hjn : (j:ℝ)≤(N+1:ℕ) := Nat.cast_le.mpr hj
      have ha : |(j:ℝ)*h|≤|t| := by
        rw [abs_mul,abs_of_nonneg hj0,show |h|=|t|/((N+1:ℕ):ℝ) by dsimp [h]; rw [abs_div,abs_of_pos hNr]]
        calc
          _ ≤ ((N+1:ℕ):ℝ)*(|t|/((N+1:ℕ):ℝ)) := mul_le_mul_of_nonneg_right hjn (div_nonneg (abs_nonneg t) hNr.le)
          _ = |t| := mul_div_cancel₀ _ hNe
      exact abs_le.mp ha
    have hxj (j : ℕ) (hj : j<N+1) : x j∈K := by
      simpa only [x,h,Nat.cast_add,Nat.cast_one] using hit N j hj.le
    have hyj (j : ℕ) (hj : j<N+1) : y j∈K := hαK _ (hsj hj.le)
    have hxe (j : ℕ) (hj : j<N+1) : ‖x (j+1)-x j-h • X (x j)‖≤ε*|h| := by
      have he' := hN (x j) (hxj j hj)
      simpa only [x,h,Function.iterate_succ_apply'] using he'
    have hye (j : ℕ) (hj : j<N+1) : ‖y (j+1)-y j-h • X (y j)‖≤ε*|h| := by
      have he' := hNy ((j:ℝ)*h) (hsj hj.le)
      have heq : ((j+1:ℕ):ℝ)*h=(j:ℝ)*h+h := by rw [Nat.cast_add,Nat.cast_one]; ring
      simpa only [y,heq] using he'
    have hv := finite_euler_comparison X K hL x y hε.le (by simp [x,y,hα0]) hxj hyj hxe hye
    have hyend : y (N+1)=α t := by dsimp [y,h]; rw [mul_div_cancel₀ _ hNe]
    have hend : ((N+1:ℕ):ℝ)*(2*ε*|h|)*Real.exp (((N+1:ℕ):ℝ)*L*|h|)=ε*C := by
      have hh : |h|=|t|/((N+1:ℕ):ℝ) := by dsimp [h]; rw [abs_div,abs_of_pos hNr]
      rw [hh]
      have hq : ((N+1:ℕ):ℝ)*(L:ℝ)*(|t|/((N+1:ℕ):ℝ))=L*|t| := by field_simp
      rw [hq]
      dsimp [C]
      field_simp
    rw [hyend,hend] at hv
    simpa only [dist_eq_norm,x,h,Nat.cast_add,Nat.cast_one] using hv.trans_lt hεC
  exact Filter.eventually_atTop.mp hev

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_ProductCurveLocalFlow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Topology Metric
open scoped NNReal

theorem exists_local_integralCurves_in_nhds {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (X : E → E) (p : E) (K : Set E)
    (hK : K∈𝓝 p) (hX : ∀ x∈K, ContinuousAt X x) (hf : ContDiffAt ℝ 1 X p) :
    ∃ r > (0:ℝ), ∃ δ > (0:ℝ), ∃ α : E → ℝ → E,
      (∀ x∈closedBall p r, α x 0=x) ∧
      (∀ x∈closedBall p r, ∀ t∈Icc (-δ) δ, α x t∈K ∧
        HasStrictDerivAt (α x) (X (α x t)) t ∧ ContinuousAt (fun s => X (α x s)) t) ∧
      ContinuousOn (fun z : E × ℝ => α z.1 z.2) (closedBall p r ×ˢ Icc (-δ) δ) := by
  obtain ⟨e,he,a,r₀,L,M,hr₀,hPL⟩ := IsPicardLindelof.of_contDiffAt_one hf
  obtain ⟨β,hβ,hβc⟩ := (hPL 0).exists_forall_mem_closedBall_eq_hasDerivWithinAt_continuousOn
  have hr₀' : (0:ℝ) < r₀ := hr₀
  have hB : closedBall p (r₀:ℝ) ×ˢ Icc (0-e) (0+e)∈𝓝 (p,(0:ℝ)) :=
    prod_mem_nhds (closedBall_mem_nhds p hr₀') (Icc_mem_nhds (by linarith) (by linarith))
  have hpc : ContinuousAt β (p,0) := (hβc (p,0) (mem_of_mem_nhds hB)).continuousAt hB
  have hp0 : β (p,0)=p := (hβ p (mem_closedBall_self hr₀'.le)).1
  have hpre : β ⁻¹' K∈𝓝 (p,(0:ℝ)) := by
    apply hpc
    simpa only [hp0] using hK
  obtain ⟨s,hs,hsp⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hpre
  let r : ℝ := min s (r₀:ℝ)/2
  let δ : ℝ := min s e/2
  have hr : 0 < r := half_pos (lt_min hs hr₀')
  have hδ : 0<δ := half_pos (lt_min hs he)
  have hrs : r≤ s := (half_le_self (le_of_lt (lt_min hs hr₀'))).trans (min_le_left _ _)
  have hrr : r≤(r₀:ℝ) := (half_le_self (le_of_lt (lt_min hs hr₀'))).trans (min_le_right _ _)
  have hδs : δ≤ s := (half_le_self (le_of_lt (lt_min hs he))).trans (min_le_left _ _)
  have hδe : δ<e := (half_lt_self (lt_min hs he)).trans_le (min_le_right _ _)
  have hdom : closedBall p r ×ˢ Icc (-δ) δ ⊆ closedBall p (r₀:ℝ) ×ˢ Icc (0-e) (0+e) := by
    intro z hz
    exact ⟨closedBall_subset_closedBall hrr hz.1,by constructor <;> linarith [hz.2.1,hz.2.2]⟩
  refine ⟨r,hr,δ,hδ,(fun x t => β (x,t)),?_,?_,hβc.mono hdom⟩
  · intro x hx
    exact (hβ x (closedBall_subset_closedBall hrr hx)).1
  · intro x hx t ht
    have hxt : β (x,t)∈K := hsp (by
      simpa only [mem_closedBall,Prod.dist_eq,Real.dist_eq,sub_zero,max_le_iff] using
        And.intro ((mem_closedBall.mp hx).trans hrs) ((abs_le.mpr ht).trans hδs))
    have hdx (s : ℝ) (hs' : s∈Ioo (-e) e) : HasDerivAt (fun u => β (x,u)) (X (β (x,s))) s := by
      have hd := (hβ x (closedBall_subset_closedBall hrr hx)).2 s (by
        constructor <;> linarith [hs'.1,hs'.2])
      exact hd.hasDerivAt (Icc_mem_nhds (by linarith [hs'.1]) (by linarith [hs'.2]))
    have hte : t∈Ioo (-e) e := by constructor <;> linarith [ht.1,ht.2]
    have hvc : ContinuousAt (fun s => X (β (x,s))) t :=
      (hX _ hxt).comp (x := t) (f := fun s : ℝ => β (x,s)) (hdx t hte).continuousAt
    refine ⟨hxt,?_,hvc⟩
    exact hasStrictDerivAt_of_hasDerivAt_of_continuousAt
      (Filter.mem_of_superset (Ioo_mem_nhds hte.1 hte.2) hdx) hvc

namespace Biholomorph
variable {n : ℕ} {U : Set (Affine n)}

@[simp] theorem ambientAut_iterate (a : Biholomorph U U) (p : U) (j : ℕ) :
    (a.ambientAut^[j]) p.val=((a^j).toHomeomorph p).val := by
  induction j with
  | zero => simp [one_apply]
  | succ j ih => rw [Function.iterate_succ_apply',ih,ambientAut_apply,pow_succ',mul_apply]

theorem productCurve_local_flow_limit (hU : IsOpen U) [LocallyCompactSpace U]
    (hbd : Bornology.IsBounded U)
    (a b : ℝ → Biholomorph U U) (ha : Continuous a) (hb : Continuous b)
    (ha0 : a 0=1) (ham : ∀ s t, a (s+t)=a s*a t)
    (hb0 : b 0=1) (hbm : ∀ s t, b (s+t)=b s*b t) (p : U) :
    ∃ r > (0:ℝ), ∃ δ > (0:ℝ), ∃ α : Affine n → ℝ → Affine n,
      closedBall p.val r ⊆ U ∧
      (∀ x∈closedBall p.val r, α x 0=x) ∧
      (∀ x∈closedBall p.val r, ∀ t∈Icc (-δ) δ,
        α x t∈U ∧ HasStrictDerivAt (α x)
          (infinitesimalGenerator a (α x t)+infinitesimalGenerator b (α x t)) t ∧
        Tendsto (fun N : ℕ => ((a (t/(N+1))*b (t/(N+1)))^(N+1)).ambientAut x)
          atTop (𝓝 (α x t))) ∧
      ContinuousOn (fun z : Affine n × ℝ => α z.1 z.2)
        (closedBall p.val r ×ˢ Icc (-δ) δ) := by
  let X : Affine n → Affine n := fun y => infinitesimalGenerator a y+infinitesimalGenerator b y
  let c : ℝ → Biholomorph U U := fun t => a t*b t
  have hX : AnalyticOnNhd ℂ X U := fun y hy =>
    (infinitesimalGenerator_analytic hU a ha hbd ha0 ham y hy).add
      (infinitesimalGenerator_analytic hU b hb hbd hb0 hbm y hy)
  have hf : ContDiffAt ℝ 1 X p.val := (hX p.val p.property).contDiffAt.restrict_scalars ℝ
  obtain ⟨R₀,hR₀,M,hR₀U,hstep⟩ := curve_uniform_displacement hU c (by simp [c,ha0,hb0]) p
    (productCurve_joint_hasStrictFDerivAt hU a b ha hb hbd ha0 ham hb0 hbm p)
  obtain ⟨L,S,hS,hL⟩ := hf.exists_lipschitzOnWith
  obtain ⟨R₁,hR₁,hR₁S⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hS
  let R : ℝ := min R₀ R₁
  have hR : 0<R := lt_min hR₀ hR₁
  let K : Set (Affine n) := closedBall p.val R
  have hKU : K⊆U := (closedBall_subset_closedBall (min_le_left _ _)).trans hR₀U
  have hLK : LipschitzOnWith L X K := hL.mono ((closedBall_subset_closedBall (min_le_right _ _)).trans hR₁S)
  obtain ⟨r₀,hr₀,δ₀,hδ₀,α,hα0,hα,hαc⟩ := exists_local_integralCurves_in_nhds X p.val K
    (closedBall_mem_nhds p.val hR) (fun y hy => (hX y (hKU hy)).continuousAt) hf
  let r : ℝ := min r₀ (R/2)
  let δ : ℝ := min δ₀ (min (R/2) (R/(2*((M:ℝ)+1))))
  have hr : 0 < r := lt_min hr₀ (half_pos hR)
  have hM1 : 0<(M:ℝ)+1 := by positivity
  have hδ : 0<δ := lt_min hδ₀ (lt_min (half_pos hR) (div_pos hR (by positivity)))
  have hrr : r ≤ r₀ := min_le_left _ _
  have hrR : r≤R/2 := min_le_right _ _
  have hδδ : δ≤δ₀ := min_le_left _ _
  have hδR : δ≤R/2 := (min_le_right _ _).trans (min_le_left _ _)
  have hδM : δ≤R/(2*((M:ℝ)+1)) := (min_le_right _ _).trans (min_le_right _ _)
  have hballU : closedBall p.val r ⊆ U :=
    (closedBall_subset_closedBall (hrR.trans (half_le_self hR.le))).trans hKU
  have hdom : closedBall p.val r ×ˢ Icc (-δ) δ ⊆ closedBall p.val r₀ ×ˢ Icc (-δ₀) δ₀ := by
    intro z hz
    exact ⟨closedBall_subset_closedBall hrr hz.1,by constructor <;> linarith [hz.2.1,hz.2.2]⟩
  refine ⟨r,hr,δ,hδ,α,hballU,(fun x hx => hα0 x (closedBall_subset_closedBall hrr hx)),?_,hαc.mono hdom⟩
  intro x hx t ht
  have hxx : x∈closedBall p.val r₀ := closedBall_subset_closedBall hrr hx
  have htt : t∈Icc (-δ₀) δ₀ := by constructor <;> linarith [ht.1,ht.2]
  refine ⟨hKU (hα x hxx t htt).1,(hα x hxx t htt).2.1,?_⟩
  have hta : |t|≤δ := abs_le.mpr ht
  have hsδ {s : ℝ} (hs : s∈Icc (-|t|) |t|) : s∈Icc (-δ₀) δ₀ := by
    constructor <;> linarith [hs.1,hs.2]
  have hlocalstep : ∀ u : ℝ, |u|≤R/2 → ∀ y∈closedBall x (R/2),
      ‖(c u).ambientAut y-y‖≤M*|u| := by
    intro u hu y hy
    apply hstep u (hu.trans ((half_le_self hR.le).trans (min_le_left _ _))) y
    have hd := dist_triangle y x p.val
    have hxp : dist x p.val≤R/2 := (mem_closedBall.mp hx).trans hrR
    exact hd.trans (by linarith [mem_closedBall.mp hy,min_le_left R₀ R₁])
  have hit : ∀ N : ℕ, ∀ j≤N+1, (((fun y => (c (t/(N+1))).ambientAut y))^[j]) x∈K := by
    intro N j hj
    have hMt : (M:ℝ)*|t|≤R/2 := by
      have hh : |t| *(2*((M:ℝ)+1))≤R := (le_div_iff₀ (by positivity)).mp (hta.trans hδM)
      nlinarith [abs_nonneg t]
    have hv := curve_power_displacement c ⟨x,hballU hx⟩ hlocalstep (Nat.succ_ne_zero N)
      (hta.trans hδR) hMt j hj
    have hNr : (0:ℝ)<(N+1:ℕ) := Nat.cast_pos.mpr (Nat.succ_pos N)
    have hbound : (j:ℝ)*(M*|t|/((N+1:ℕ):ℝ))≤R/2 := by
      calc
        _ ≤ ((N+1:ℕ):ℝ)*(M*|t|/((N+1:ℕ):ℝ)) := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hj)
          (div_nonneg (mul_nonneg M.coe_nonneg (abs_nonneg t)) hNr.le)
        _ = M*|t| := mul_div_cancel₀ _ (ne_of_gt hNr)
        _ ≤ R/2 := hMt
    have hx' : (c (t/(N+1))).ambientAut^[j] x =
        (((c (t/(N+1)))^j).toHomeomorph ⟨x,hballU hx⟩).val := ambientAut_iterate _ ⟨x,hballU hx⟩ j
    rw [hx']
    have hd := dist_triangle (((c (t/(N+1)))^j).toHomeomorph ⟨x,hballU hx⟩).val x p.val
    have hv' := hv.trans hbound
    simp only [Nat.cast_succ] at hv'
    exact hd.trans (by linarith [hv',(mem_closedBall.mp hx).trans hrR])
  have hv := consistent_iterates_tendsto (fun t y => (c t).ambientAut y) X K hLK
    (fun ε hε => productCurve_uniform_consistency hU hbd a b ha hb ha0 ham hb0 hbm K
      (isCompact_closedBall _ _) hKU hε) x (α x) t (hα0 x hxx)
    (fun s hs => (hα x hxx s (hsδ hs)).1)
    (fun s hs => (hα x hxx s (hsδ hs)).2.1)
    (fun s hs => (hα x hxx s (hsδ hs)).2.2) hit
  simpa only [ambientAut_iterate (p := ⟨x,hballU hx⟩),ambientAut_apply (p := ⟨x,hballU hx⟩),c] using hv

end Biholomorph
end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_ProductCurveLocalAutomorphism
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Topology Metric
namespace Biholomorph
variable {n : ℕ} {U : Set (Affine n)}

theorem exists_tendsto_of_compact_local_pointwise (hU : IsOpen U) (hc : IsPreconnected U)
    {ι : Type*} (l : Filter ι) [NeBot l] (q : ι → Biholomorph U U)
    (K : Set (Biholomorph U U)) (hK : IsCompact K) (hq : ∀ᶠ i in l, q i∈K)
    (p : U) {r : ℝ} (hr : 0 < r) (hballU : closedBall p.val r⊆U)
    (f : Affine n → Affine n)
    (hf : ∀ x∈closedBall p.val r, Tendsto (fun i => (q i).ambientAut x) l (𝓝 (f x))) :
    ∃ e : Biholomorph U U, Tendsto q l (𝓝 e) ∧ EqOn e.ambientAut f (closedBall p.val r) := by
  have hcluster (d : Biholomorph U U) (hd : MapClusterPt d l q) :
      EqOn d.ambientAut f (closedBall p.val r) := by
    intro x hx
    let xx : U := ⟨x,hballU hx⟩
    have hev : Continuous (fun d : Biholomorph U U => (d.toHomeomorph xx).val) :=
      continuous_subtype_val.comp (continuous_evaluation xx)
    have hd' := hd.continuousAt_comp hev.continuousAt
    have hf' : Tendsto (fun i => ((q i).toHomeomorph xx).val) l (𝓝 (f x)) := by
      have ht := hf x hx
      change Tendsto (fun i => (q i).ambientAut xx.val) l (𝓝 (f x)) at ht
      simpa only [ambientAut_apply] using ht
    have heq : (d.toHomeomorph xx).val=f x := eq_of_nhds_neBot (hd'.clusterPt.mono hf')
    change d.ambientAut xx.val=f x
    simpa only [ambientAut_apply] using heq
  obtain ⟨e,_,he⟩ := hK.exists_mapClusterPt (Filter.le_principal_iff.mpr hq)
  refine ⟨e,hK.tendsto_nhds_of_unique_mapClusterPt hq ?_,hcluster e he⟩
  intro d _ hd
  have hloc : d.ambientAut =ᶠ[𝓝 p.val] e.ambientAut := by
    filter_upwards [closedBall_mem_nhds p.val hr] with x hx
    exact (hcluster d hd hx).trans (hcluster e he hx).symm
  have hall := (d.ambientAut_analytic hU).eqOn_of_preconnected_of_eventuallyEq
    (e.ambientAut_analytic hU) hc p.property hloc
  apply ext
  intro x
  apply Subtype.ext
  simpa only [ambientAut_apply] using hall x.property

theorem eq_of_ambientAut_eventuallyEq (hU : IsOpen U) (hc : IsPreconnected U)
    (p : U) {a b : Biholomorph U U} (hab : a.ambientAut =ᶠ[𝓝 p.val] b.ambientAut) : a=b := by
  have hall := (a.ambientAut_analytic hU).eqOn_of_preconnected_of_eventuallyEq
    (b.ambientAut_analytic hU) hc p.property hab
  apply ext
  intro x
  apply Subtype.ext
  simpa only [ambientAut_apply] using hall x.property

theorem productCurve_local_automorphism_family (hU : IsOpen U) [LocallyCompactSpace U]
    (hc : IsPreconnected U) (hbd : Bornology.IsBounded U)
    (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
    [MulAction Γ U] [ProperSMul Γ U]
    [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val))
    (a b : ℝ → Biholomorph U U) (ha : Continuous a) (hb : Continuous b)
    (ha0 : a 0=1) (ham : ∀ s t, a (s+t)=a s*a t)
    (hb0 : b 0=1) (hbm : ∀ s t, b (s+t)=b s*b t) (p : U) :
    ∃ r > (0:ℝ), ∃ δ > (0:ℝ), ∃ g : ℝ → Biholomorph U U,
      closedBall p.val r ⊆ U ∧ g 0=1 ∧ ContinuousOn g (Icc (-δ) δ) ∧
      (∀ t∈Icc (-δ) δ, Tendsto (fun N : ℕ => (a (t/(N+1))*b (t/(N+1)))^(N+1))
        atTop (𝓝 (g t))) ∧
      ∀ x∈closedBall p.val r, ∀ t∈Ioo (-δ) δ,
        HasStrictDerivAt (fun s => (g s).ambientAut x)
          (infinitesimalGenerator a ((g t).ambientAut x)+
            infinitesimalGenerator b ((g t).ambientAut x)) t := by
  classical
  obtain ⟨r,hr,δ₀,hδ₀,α,hball,hα0,hα,hαc⟩ :=
    productCurve_local_flow_limit hU hbd a b ha hb ha0 ham hb0 hbm p
  obtain ⟨δ₁,hδ₁,K,hK,hpow⟩ := productCurve_powers_uniform_compact
    hU hc hbd Γ hhol a b ha hb ha0 ham hb0 hbm p
  let δ : ℝ := min δ₀ δ₁
  have hδ : 0<δ := lt_min hδ₀ hδ₁
  have hδ0 : δ≤δ₀ := min_le_left _ _
  have hδ1 : δ≤δ₁ := min_le_right _ _
  have ht0 {t : ℝ} (ht : t∈Icc (-δ) δ) : t∈Icc (-δ₀) δ₀ := by
    constructor <;> linarith [ht.1,ht.2]
  have hpK (t : ℝ) (ht : t∈Icc (-δ) δ) (N : ℕ) :
      (a (t/(N+1))*b (t/(N+1)))^(N+1)∈K :=
    hpow t ((abs_le.mpr ht).trans hδ1) N (N+1) le_rfl
  have hex (t : ℝ) : ∃ e : Biholomorph U U, t∈Icc (-δ) δ →
      Tendsto (fun N : ℕ => (a (t/(N+1))*b (t/(N+1)))^(N+1)) atTop (𝓝 e) ∧
      EqOn e.ambientAut (fun x => α x t) (closedBall p.val r) := by
    by_cases ht : t∈Icc (-δ) δ
    · obtain ⟨e,he,heq⟩ := exists_tendsto_of_compact_local_pointwise hU hc atTop
        (fun N : ℕ => (a (t/(N+1))*b (t/(N+1)))^(N+1)) K hK
        (Filter.Eventually.of_forall (hpK t ht)) p hr hball (fun x => α x t)
        (fun x hx => (hα x hx t (ht0 ht)).2.2)
      exact ⟨e,fun _ => ⟨he,heq⟩⟩
    · exact ⟨1,fun h => (ht h).elim⟩
  choose g hg using hex
  have hgK (t : ℝ) (ht : t∈Icc (-δ) δ) : g t∈K :=
    hK.isClosed.mem_of_tendsto (hg t ht).1 (Filter.Eventually.of_forall (hpK t ht))
  have hzero : (0:ℝ)∈Icc (-δ) δ := ⟨by linarith, hδ.le⟩
  have hg0 : g 0=1 := by
    have ht := (hg 0 hzero).1
    have ht' : Tendsto (fun _ : ℕ => (1 : Biholomorph U U)) atTop (𝓝 (g 0)) := by
      simpa only [zero_div,ha0,hb0,one_mul,one_pow] using ht
    exact tendsto_nhds_unique ht' tendsto_const_nhds
  have hgc : ContinuousOn g (Icc (-δ) δ) := by
    intro t ht
    have : NeBot (𝓝[Icc (-δ) δ] t) := nhdsWithin_neBot_of_mem ht
    have hv (x : Affine n) (hx : x∈closedBall p.val r) :
        Tendsto (fun s => (g s).ambientAut x) (𝓝[Icc (-δ) δ] t) (𝓝 (α x t)) := by
      have hpath : ContinuousOn (fun s => α x s) (Icc (-δ) δ) := hαc.comp
        (continuous_const.prodMk continuous_id).continuousOn (fun s hs => ⟨hx,ht0 hs⟩)
      apply (hpath t ht).tendsto.congr'
      filter_upwards [self_mem_nhdsWithin] with s hs
      exact ((hg s hs).2 hx).symm
    obtain ⟨e,he,heq⟩ := exists_tendsto_of_compact_local_pointwise hU hc
      (𝓝[Icc (-δ) δ] t) g K hK (by
        filter_upwards [self_mem_nhdsWithin] with s hs
        exact hgK s hs) p hr hball (fun x => α x t) hv
    have hegt : e=g t := eq_of_ambientAut_eventuallyEq hU hc p (by
      filter_upwards [closedBall_mem_nhds p.val hr] with x hx
      exact (heq hx).trans ((hg t ht).2 hx).symm)
    change Tendsto g (𝓝[Icc (-δ) δ] t) (𝓝 (g t))
    rw [hegt] at he
    exact he
  refine ⟨r,hr,δ,hδ,g,hball,hg0,hgc,(fun t ht => (hg t ht).1),?_⟩
  intro x hx t ht
  have htt : t∈Icc (-δ) δ := Ioo_subset_Icc_self ht
  have hed := (hα x hx t (ht0 htt)).2.1
  have heq : (fun s => α x s) =ᶠ[𝓝 t] (fun s => (g s).ambientAut x) := by
    filter_upwards [Icc_mem_nhds ht.1 ht.2] with s hs
    exact ((hg s hs).2 hx).symm
  have htEq : (g t).ambientAut x=α x t := (hg t htt).2 hx
  rw [← htEq] at hed
  exact hed.congr_of_eventuallyEq heq

end Biholomorph
end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_LocalAutomorphismODEGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Topology Metric
namespace Biholomorph
variable {n : ℕ} {U : Set (Affine n)}

 theorem ambientAut_uniform_at_zero (hU : IsOpen U) [LocallyCompactSpace U]
    (g : ℝ → Biholomorph U U) (hg : ContinuousAt g 0) (hg0 : g 0=1)
    (p : U) {S : Set (Affine n)} (hS : S∈𝓝 p.val) :
    ∃ ε > (0:ℝ), ∀ t, |t|<ε → ∀ x∈ball p.val ε, (g t).ambientAut x∈S := by
  have hh : ContinuousAt (fun z : ℝ × Affine n => (g z.1).ambientAut z.2) (0,p.val) :=
    (ambientAut_joint_continuousAt hU p.property).comp
      ((hg.comp (f := fun z : ℝ × Affine n => z.1) continuous_fst.continuousAt).prodMk continuous_snd.continuousAt)
  have heq : (g 0).ambientAut p.val=p.val := by rw [hg0,ambientAut_apply,one_apply]
  have hhS := hh (show S∈𝓝 ((g 0).ambientAut p.val) from heq.symm ▸ hS)
  obtain ⟨ε,hε,hhε⟩ := Metric.mem_nhds_iff.mp hhS
  refine ⟨ε,hε,?_⟩
  intro t ht x hx
  apply hhε (a := (t,x))
  simpa only [mem_ball,Prod.dist_eq,Real.dist_eq,sub_zero,max_lt_iff] using And.intro ht hx

theorem local_automorphism_ODE_group_law (hU : IsOpen U) [LocallyCompactSpace U]
    (hc : IsPreconnected U) (p : U) (X : Affine n → Affine n)
    (hX : AnalyticOnNhd ℂ X U)
    (g : ℝ → Biholomorph U U) (hg0 : g 0=1)
    {r δ : ℝ} (hr : 0 < r) (hδ : 0<δ) (hball : closedBall p.val r⊆U)
    (hgc : ContinuousOn g (Icc (-δ) δ))
    (hd : ∀ x∈closedBall p.val r, ∀ t∈Ioo (-δ) δ,
      HasStrictDerivAt (fun s => (g s).ambientAut x) (X ((g t).ambientAut x)) t) :
    ∃ ε > (0:ℝ), ε<δ ∧ ∀ s t : ℝ, |s|<ε → |t|<ε → g (s+t)=g s*g t := by
  have hgc0 : ContinuousAt g 0 := (hgc 0 ⟨by linarith,hδ.le⟩).continuousAt
    (Icc_mem_nhds (by linarith) hδ)
  have hf : ContDiffAt ℝ 1 X p.val := (hX p.val p.property).contDiffAt.restrict_scalars ℝ
  obtain ⟨L,K,hK,hL⟩ := hf.exists_lipschitzOnWith
  obtain ⟨ρ,hρ,hρK⟩ := Metric.nhds_basis_ball.mem_iff.mp
    (inter_mem hK (ball_mem_nhds p.val hr))
  obtain ⟨ε₀,hε₀,hstep₀⟩ := ambientAut_uniform_at_zero hU g hgc0 hg0 p
    (ball_mem_nhds p.val hρ)
  obtain ⟨ε₁,hε₁,hstep₁⟩ := ambientAut_uniform_at_zero hU g hgc0 hg0 p
    (ball_mem_nhds p.val hε₀)
  let ε : ℝ := min (δ/3) (min (ε₀/3) ε₁)
  have hε : 0<ε := lt_min (by positivity) (lt_min (by positivity) hε₁)
  have hεδ : ε≤δ/3 := min_le_left _ _
  have hεε₀ : ε≤ε₀/3 := (min_le_right _ _).trans (min_le_left _ _)
  have hεε₁ : ε≤ε₁ := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨ε,hε,by linarith,?_⟩
  intro s t hs ht
  apply eq_of_ambientAut_eventuallyEq hU hc p
  filter_upwards [ball_mem_nhds p.val (lt_min hε₀ (lt_min hε₁ hr))] with x hx
  have hx₀ : x∈ball p.val ε₀ := ball_subset_ball (min_le_left _ _) hx
  have hx₁ : x∈ball p.val ε₁ := ball_subset_ball ((min_le_right _ _).trans (min_le_left _ _)) hx
  have hxr : x∈closedBall p.val r := ball_subset_closedBall
    (ball_subset_ball ((min_le_right _ _).trans (min_le_right _ _)) hx)
  have hxu : x∈U := hball hxr
  have htx : (g t).ambientAut x∈ball p.val ε₀ := hstep₁ t (ht.trans_le hεε₁) x hx₁
  have htxr : (g t).ambientAut x∈closedBall p.val r := ball_subset_closedBall
    (hρK (hstep₀ t (by linarith) x hx₀)).2
  have hs' : s∈Ioo (-ε) ε := abs_lt.mp hs
  have ht' : t∈Ioo (-ε) ε := abs_lt.mp ht
  have hsum {u : ℝ} (hu : u∈Ioo (-ε) ε) : u+t∈Ioo (-δ) δ ∧ |u+t|<ε₀ := by
    have ha := abs_add_le u t
    have hu' : |u|<ε := abs_lt.mpr hu
    constructor
    · constructor <;> linarith [ht'.1,ht'.2,hu.1,hu.2]
    · linarith
  have heq := ODE_solution_unique_of_mem_Ioo
    (v := fun (_ : ℝ) y => X y) (s := fun _ => K) (a := -ε) (b := ε) (t₀ := 0)
    (fun _ _ => hL) (show (0:ℝ)∈Ioo (-ε) ε from ⟨by linarith,hε⟩)
    (f := fun u => (g (u+t)).ambientAut x)
    (g := fun u => (g u).ambientAut ((g t).ambientAut x))
    (fun u hu => ⟨by
      have hshift : HasDerivAt (fun v : ℝ => v+t) 1 u := by simpa only [id_eq] using (hasDerivAt_id u).add_const t
      have hh := (hd x hxr (u+t) (hsum hu).1).hasDerivAt.scomp u hshift
      simpa only [Function.comp_def,one_smul] using hh,
      (hρK (hstep₀ (u+t) (hsum hu).2 x hx₀)).1⟩)
    (fun u hu => ⟨(hd _ htxr u (by constructor <;> linarith [hu.1,hu.2])).hasDerivAt,
      (hρK (hstep₀ u (by have hh := abs_lt.mpr hu; linarith) _ htx)).1⟩)
    (by
      rw [zero_add,hg0]
      rw [ambientAut_apply (g t) ⟨x,hxu⟩,ambientAut_apply,one_apply])
  have hh := heq hs'
  dsimp only at hh
  rw [ambientAut_apply (g t) ⟨x,hxu⟩,ambientAut_apply,
    ← mul_apply,← ambientAut_apply] at hh
  exact hh

end Biholomorph
end Release061

open Set Filter Topology

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_LocalRealHomExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
namespace Release061

theorem local_real_hom_nat_mul {G : Type*} [Group G] (g : ℝ → G) (h0 : g 0=1)
    {ε : ℝ} (hε : 0<ε)
    (hm : ∀ s t : ℝ, |s|<ε → |t|<ε → g (s+t)=g s*g t)
    (n : ℕ) (u : ℝ) (hu : |(n:ℝ)*u|<ε) : g ((n:ℝ)*u)=g u^n := by
  by_cases hn : n=0
  · simp [hn,h0]
  have hnu : |(n:ℝ)*u|=(n:ℝ)*|u| := by rw [abs_mul,abs_of_nonneg (Nat.cast_nonneg n)]
  have hun : |u|<ε := by
    have hn1 : (1:ℝ)≤n := Nat.one_le_cast.mpr (Nat.one_le_iff_ne_zero.mpr hn)
    rw [hnu] at hu
    nlinarith [abs_nonneg u]
  have hh : ∀ j : ℕ, j≤n → g ((j:ℝ)*u)=g u^j := by
    intro j hj
    induction j with
    | zero => simp [h0]
    | succ j ih =>
      have hjn : j≤n := (Nat.le_succ j).trans hj
      have hju : |(j:ℝ)*u|<ε := by
        rw [abs_mul,abs_of_nonneg (Nat.cast_nonneg j)]
        rw [hnu] at hu
        have hc : (j:ℝ)≤n := Nat.cast_le.mpr hjn
        nlinarith [abs_nonneg u]
      rw [Nat.cast_succ,add_mul,one_mul,hm _ _ hju hun,ih hjn,pow_succ]
  exact hh n le_rfl

theorem local_real_hom_subdivision_independent {G : Type*} [Group G]
    (g : ℝ → G) (h0 : g 0=1) {ε : ℝ} (hε : 0<ε)
    (hm : ∀ s t : ℝ, |s|<ε → |t|<ε → g (s+t)=g s*g t)
    (t : ℝ) {n m : ℕ} (hn : 0<n) (hms : 0 < m)
    (htn : |t/n|<ε) (htm : |t/m|<ε) : g (t/n)^n=g (t/m)^m := by
  have hnr : (n:ℝ)≠0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  have hmr : (m:ℝ)≠0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hms)
  let u : ℝ := t/((n:ℝ)*m)
  have hen : (m:ℝ)*u=t/n := by
    dsimp [u]
    field_simp [hnr,hmr]
  have hem : (n:ℝ)*u=t/m := by
    dsimp [u]
    field_simp [hnr,hmr]
  have hgn := local_real_hom_nat_mul g h0 hε hm m u (by simpa only [hen] using htn)
  have hgm := local_real_hom_nat_mul g h0 hε hm n u (by simpa only [hem] using htm)
  rw [hen] at hgn
  rw [hem] at hgm
  rw [hgn,hgm,← pow_mul,← pow_mul,Nat.mul_comm m n]

theorem local_real_hom_extension {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (g : ℝ → G) (h0 : g 0=1) (hc : ContinuousAt g 0) {ε : ℝ} (hε : 0<ε)
    (hm : ∀ s t : ℝ, |s|<ε → |t|<ε → g (s+t)=g s*g t) :
    ∃ H : ℝ → G, H 0=1 ∧ Continuous H ∧ (∀ s t, H (s+t)=H s*H t) ∧
      ∀ t, |t|<ε → H t=g t := by
  have hex (t : ℝ) : ∃ n : ℕ, 0<n ∧ |t/n|<ε := by
    obtain ⟨n,hn⟩ := exists_nat_gt (max 1 (|t|/ε))
    have hnn : (1:ℝ)<n := (le_max_left _ _).trans_lt hn
    have hpos : 0<n := Nat.cast_pos.mp (by linarith : (0:ℝ)<n)
    refine ⟨n,hpos,?_⟩
    rw [abs_div,abs_of_pos (show 0 < (n:ℝ) from Nat.cast_pos.mpr hpos)]
    apply (div_lt_iff₀ (Nat.cast_pos.mpr hpos)).mpr
    have hs := (div_lt_iff₀ hε).mp ((le_max_right _ _).trans_lt hn)
    nlinarith
  have hchoose := hex
  choose N hN using hchoose
  let H : ℝ → G := fun t => g (t/N t)^(N t)
  have hspec (t : ℝ) (n : ℕ) (hn : 0<n) (ht : |t/n|<ε) : H t=g (t/n)^n :=
    local_real_hom_subdivision_independent g h0 hε hm t (hN t).1 hn (hN t).2 ht
  have hlocal (t : ℝ) (ht : |t|<ε) : H t=g t := by
    simpa only [Nat.cast_one,div_one,pow_one] using hspec t 1 (by decide) (by simpa using ht)
  have hH0 : H 0=1 := (hlocal 0 (by simpa using hε)).trans h0
  have hadd (s t : ℝ) : H (s+t)=H s*H t := by
    obtain ⟨n,hn,hnt⟩ := hex (max |s| (max |t| |s+t|))
    have hnpos : (0:ℝ)<n := Nat.cast_pos.mpr hn
    have hmax : 0 ≤ max |s| (max |t| |s+t|) := (abs_nonneg s).trans (le_max_left _ _)
    rw [abs_div,abs_of_nonneg hmax,abs_of_pos hnpos] at hnt
    have hs : |s/n|<ε := by
      rw [abs_div,abs_of_pos hnpos]
      exact (div_le_div_of_nonneg_right (le_max_left _ _) hnpos.le).trans_lt hnt
    have ht : |t/n|<ε := by
      rw [abs_div,abs_of_pos hnpos]
      exact (div_le_div_of_nonneg_right ((le_max_left _ _).trans (le_max_right _ _)) hnpos.le).trans_lt hnt
    have hst : |(s+t)/n|<ε := by
      rw [abs_div,abs_of_pos hnpos]
      exact (div_le_div_of_nonneg_right ((le_max_right _ _).trans (le_max_right _ _)) hnpos.le).trans_lt hnt
    have hcom : Commute (g (s/n)) (g (t/n)) := by
      change g (s/n)*g (t/n)=g (t/n)*g (s/n)
      rw [← hm _ _ hs ht,← hm _ _ ht hs,add_comm]
    rw [hspec (s+t) n hn hst,hspec s n hn hs,hspec t n hn ht,add_div,hm _ _ hs ht]
    exact hcom.mul_pow n
  have hHc0 : ContinuousAt H 0 := hc.congr (show g=ᶠ[𝓝 0] H from by
    filter_upwards [Metric.ball_mem_nhds (0:ℝ) hε] with t ht
    exact (hlocal t (by simpa only [Metric.mem_ball,Real.dist_eq,sub_zero] using ht)).symm)
  have hHc : Continuous H := by
    apply continuous_iff_continuousAt.mpr
    intro t
    have h0t : ContinuousAt H (t-t) := by simpa only [sub_self] using hHc0
    have hsub : ContinuousAt (fun s : ℝ => s-t) t := continuousAt_id.sub continuousAt_const
    have hh : ContinuousAt (fun s : ℝ => H t*H (s-t)) t := continuousAt_const.mul
      (h0t.comp (f := fun s : ℝ => s-t) hsub)
    have he : (fun s : ℝ => H t*H (s-t))=H := by
      funext s
      rw [← hadd]
      congr 1
      ring
    rwa [he] at hh
  exact ⟨H,hH0,hHc,hadd,hlocal⟩
end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_OneParameterGeneratorAdd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
namespace Release061
open Set Filter Topology Metric
namespace Biholomorph
variable {n : ℕ} {U : Set (Affine n)}

theorem exists_oneParameter_of_local_ODE (hU : IsOpen U) [LocallyCompactSpace U]
    (hc : IsPreconnected U) (hbd : Bornology.IsBounded U) (p : U)
    (X : Affine n → Affine n) (hX : AnalyticOnNhd ℂ X U)
    (g : ℝ → Biholomorph U U) (hg0 : g 0=1)
    {r δ : ℝ} (hr : 0 < r) (hδ : 0<δ) (hball : closedBall p.val r⊆U)
    (hgc : ContinuousOn g (Icc (-δ) δ))
    (hd : ∀ x∈closedBall p.val r, ∀ t∈Ioo (-δ) δ,
      HasStrictDerivAt (fun s => (g s).ambientAut x) (X ((g t).ambientAut x)) t) :
    ∃ H : ℝ → Biholomorph U U, H 0=1 ∧ Continuous H ∧
      (∀ s t, H (s+t)=H s*H t) ∧ EqOn (infinitesimalGenerator H) X U := by
  obtain ⟨ε,hε,_,hm⟩ := local_automorphism_ODE_group_law hU hc p X hX g hg0 hr hδ hball hgc hd
  have hgc0 : ContinuousAt g 0 := (hgc 0 ⟨by linarith,hδ.le⟩).continuousAt
    (Icc_mem_nhds (by linarith) hδ)
  obtain ⟨H,hH0,hHc,hHm,hHloc⟩ := local_real_hom_extension g hg0 hgc0 hε hm
  refine ⟨H,hH0,hHc,hHm,?_⟩
  apply (infinitesimalGenerator_analytic hU H hHc hbd hH0 hHm).eqOn_of_preconnected_of_eventuallyEq
    hX hc p.property
  filter_upwards [closedBall_mem_nhds p.val hr] with x hx
  have hdx := hd x hx 0 ⟨by linarith,hδ⟩
  have heq : (fun t => (g t).ambientAut x)=ᶠ[𝓝 (0:ℝ)] (fun t => (H t).ambientAut x) := by
    filter_upwards [Metric.ball_mem_nhds (0:ℝ) hε] with t ht
    rw [hHloc t (by simpa only [Metric.mem_ball,Real.dist_eq,sub_zero] using ht)]
  have hdH := hdx.congr_of_eventuallyEq heq
  have heq0 : (g 0).ambientAut x=x := by rw [hg0,ambientAut_apply 1 ⟨x,hball hx⟩,one_apply]
  change deriv (fun t => (H t).ambientAut x) 0=X x
  simpa only [heq0] using hdH.hasDerivAt.deriv

theorem exists_oneParameter_generator_add (hU : IsOpen U) [LocallyCompactSpace U]
    (hc : IsConnected U) (hbd : Bornology.IsBounded U)
    (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
    [MulAction Γ U] [ProperSMul Γ U]
    [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val))
    (a b : ℝ → Biholomorph U U) (ha : Continuous a) (hb : Continuous b)
    (ha0 : a 0=1) (ham : ∀ s t, a (s+t)=a s*a t)
    (hb0 : b 0=1) (hbm : ∀ s t, b (s+t)=b s*b t) :
    ∃ H : ℝ → Biholomorph U U, H 0=1 ∧ Continuous H ∧
      (∀ s t, H (s+t)=H s*H t) ∧ ∀ x∈U,
        infinitesimalGenerator H x=infinitesimalGenerator a x+infinitesimalGenerator b x := by
  obtain ⟨p,hp⟩ := hc.nonempty
  obtain ⟨r,hr,δ,hδ,g,hball,hg0,hgc,_,hgd⟩ := productCurve_local_automorphism_family
    hU hc.isPreconnected hbd Γ hhol a b ha hb ha0 ham hb0 hbm ⟨p,hp⟩
  exact exists_oneParameter_of_local_ODE hU hc.isPreconnected hbd ⟨p,hp⟩
    (fun x => infinitesimalGenerator a x+infinitesimalGenerator b x)
    (fun x hx => (infinitesimalGenerator_analytic hU a ha hbd ha0 ham x hx).add
      (infinitesimalGenerator_analytic hU b hb hbd hb0 hbm x hx)) g hg0 hr hδ hball hgc hgd

end Biholomorph
end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_OneParameterOneGenerator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Topology Metric MeasureTheory
namespace Biholomorph

section
variable {n : ℕ} {U : Set (Affine n)} (hU : IsOpen U) [LocallyCompactSpace U]
variable (a : ℝ → Biholomorph U U) (ha : Continuous a)
include hU ha

theorem oneParameter_fixed_of_generator_zero (hb : Bornology.IsBounded U)
    (hzero : a 0=1) (hmul : ∀ s t, a (s+t)=a s*a t) (p : U)
    (hX : infinitesimalGenerator a p.val=0) (t : ℝ) :
    (a t).toHomeomorph p=p := by
  have hd (s : ℝ) : HasDerivAt (fun t => ((a t).toHomeomorph p).val) 0 s := by
    have hs := oneParameter_orbit_ODE hU a ha hb hzero hmul p s
    rwa [infinitesimalGenerator_equivariant hU a ha hb hzero hmul p s,hX,map_zero] at hs
  apply Subtype.ext
  have hc := is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt) (fun s => (hd s).deriv) t 0
  simpa only [hzero,one_apply] using hc

end

variable {n : ℕ} {U : Set (Affine n)} (hU : IsOpen U) [LocallyCompactSpace U]
variable (a : ℝ → Biholomorph U U) (ha : Continuous a)
include hU ha

theorem derivativeAt_eq_one_of_generator_zero_jet (hb : Bornology.IsBounded U)
    (hzero : a 0=1) (hmul : ∀ s t, a (s+t)=a s*a t) (p : U)
    (hX : infinitesimalGenerator a p.val=0)
    (hdX : fderiv ℂ (infinitesimalGenerator a) p.val=0)
    {r : ℝ} (hr : 0 < r) (hu : IsUnit (fderiv ℂ (shortTimeAverage a r) p.val)) :
    (a r).derivativeAt p=1 := by
  have hF := shortTimeAverage_analytic hU a ha hb hr p.val p.property
  have huN : ∀ᶠ y in 𝓝 p.val, IsUnit (fderiv ℂ (shortTimeAverage a r) y) :=
    hF.fderiv.continuousAt (Units.isOpen.mem_nhds hu)
  have hprod := hF.fderiv.differentiableAt.hasFDerivAt.clm_apply
    ((infinitesimalGenerator_analytic hU a ha hb hzero hmul p.val p.property).differentiableAt.hasFDerivAt)
  have he : (fun y => (fderiv ℂ (shortTimeAverage a r) y) (infinitesimalGenerator a y)) =ᶠ[𝓝 p.val]
      (fun y => r⁻¹ • ((a r).ambientAut y-y)) := by
    filter_upwards [huN,hU.mem_nhds p.property] with y hy hyU
    rw [infinitesimalGenerator_formula hU a ha hb hzero hmul hr hyU hy]
    change ((fderiv ℂ (shortTimeAverage a r) y * Ring.inverse (fderiv ℂ (shortTimeAverage a r) y))
      (r⁻¹ • ((a r).ambientAut y-y))) = _
    rw [Ring.mul_inverse_cancel _ hy,one_apply_eq_self]
  have hprod0 : HasFDerivAt (fun y => r⁻¹ • ((a r).ambientAut y-y)) (0 : Affine n →L[ℂ] Affine n) p.val := by
    have hd := hprod.congr_of_eventuallyEq (he.mono (fun _ h => h.symm))
    simpa only [hX,hdX,ContinuousLinearMap.comp_zero,map_zero,add_zero] using hd
  have hV : HasFDerivAt (fun y => r⁻¹ • ((a r).ambientAut y-y))
      (r⁻¹ • ((a r).derivativeAt p-1)) p.val := by
    have hd := (((a r).ambientAut_analytic hU p.val p.property).differentiableAt.hasFDerivAt.sub
      (hasFDerivAt_id p.val)).const_smul r⁻¹
    convert! hd using 1
    all_goals try with_reducible_and_instances rfl
  have hz := hV.unique hprod0
  exact sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_left (inv_ne_zero hr.ne'))

theorem oneParameter_eq_one_of_generator_zero_jet
    (hc : IsPreconnected U) (hb : Bornology.IsBounded U)
    (hzero : a 0=1) (hmul : ∀ s t, a (s+t)=a s*a t) (p : U)
    (hX : infinitesimalGenerator a p.val=0)
    (hdX : fderiv ℂ (infinitesimalGenerator a) p.val=0) (t : ℝ) :
    a t=1 := by
  have hu : ∀ᶠ r : ℝ in 𝓝[>] 0,
      IsUnit (r⁻¹ • ∫ s in 0..r, (a s).derivativeAt p) :=
    (shortTimeAverage_linear_tendsto hU a ha hzero p).eventually (Units.isOpen.mem_nhds isUnit_one)
  have hpos : ∀ᶠ r : ℝ in 𝓝[>] 0, 0 < r := self_mem_nhdsWithin
  have hid : ∀ᶠ r : ℝ in 𝓝[>] 0, a r=1 := by
    filter_upwards [hpos,hu] with r hr hur
    have hunit : IsUnit (fderiv ℂ (shortTimeAverage a r) p.val) := by
      rwa [(shortTimeAverage_derivative hU a ha hb hr p.property).fderiv]
    exact eq_one_of_firstJet hU hc hb (a r) p
      (oneParameter_fixed_of_generator_zero hU a ha hb hzero hmul p hX r)
      (derivativeAt_eq_one_of_generator_zero_jet hU a ha hb hzero hmul p hX hdX hr hunit)
  have hXall (q : U) : infinitesimalGenerator a q.val=0 := by
    have ht := (oneParameter_hasDerivAt_zero hU a ha hb hzero hmul q).tendsto_slope_zero_right
    have he : (fun r : ℝ => r⁻¹ • (((a (0+r)).toHomeomorph q).val-((a 0).toHomeomorph q).val)) =ᶠ[𝓝[>] 0]
        (fun _ => (0 : Affine n)) := by
      filter_upwards [hid] with r hr
      simp only [zero_add,hr,hzero,one_apply,sub_self,smul_zero]
    exact tendsto_nhds_unique ht (tendsto_const_nhds.congr' (he.mono (fun _ h => h.symm)))
  apply ext
  intro q
  simpa only [one_apply] using oneParameter_fixed_of_generator_zero hU a ha hb hzero hmul q (hXall q) t

end Biholomorph
end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_FiniteDimensionalCompleteGenerator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
namespace Release061
open Set Filter Topology Metric
namespace Biholomorph
variable {n : ℕ} {U : Set (Affine n)}

@[simp] theorem infinitesimalGenerator_of_not_mem (a : ℝ → Biholomorph U U)
    {x : Affine n} (hx : x∉U) : infinitesimalGenerator a x=0 := by
  simp [infinitesimalGenerator,ambientAut,ambientExtend,hx]

@[simp] theorem infinitesimalGenerator_one :
    infinitesimalGenerator (fun _ : ℝ => (1 : Biholomorph U U))=0 := by
  funext x
  exact deriv_const (0:ℝ) ((1 : Biholomorph U U).ambientAut x)

theorem infinitesimalGenerator_hasDerivAt (hU : IsOpen U) [LocallyCompactSpace U]
    (hbd : Bornology.IsBounded U) (a : ℝ → Biholomorph U U) (ha : Continuous a)
    (ha0 : a 0=1) (ham : ∀ s t, a (s+t)=a s*a t) (x : Affine n) :
    HasDerivAt (fun t => (a t).ambientAut x) (infinitesimalGenerator a x) 0 := by
  by_cases hx : x∈U
  · simpa only [ambientAut_apply (p := ⟨x,hx⟩)] using
      oneParameter_hasDerivAt_zero hU a ha hbd ha0 ham ⟨x,hx⟩
  · simpa only [infinitesimalGenerator_of_not_mem a hx,ambientAut,ambientExtend,dite_eq_right hx]
      using hasDerivAt_const (0:ℝ) (0 : Affine n)

theorem infinitesimalGenerator_time_smul (hU : IsOpen U) [LocallyCompactSpace U]
    (hbd : Bornology.IsBounded U) (a : ℝ → Biholomorph U U) (ha : Continuous a)
    (ha0 : a 0=1) (ham : ∀ s t, a (s+t)=a s*a t) (c : ℝ) :
    infinitesimalGenerator (fun t => a (c*t))=c • infinitesimalGenerator a := by
  funext x
  have hd := infinitesimalGenerator_hasDerivAt hU hbd a ha ha0 ham x
  have htime : HasDerivAt (fun t : ℝ => c*t) c 0 := by
    simpa only [mul_one,id_eq] using (hasDerivAt_id (0:ℝ)).const_mul c
  have hd' : HasDerivAt (fun t => (a t).ambientAut x) (infinitesimalGenerator a x) (c*0) := by
    simpa only [mul_zero] using hd
  exact (hd'.scomp 0 htime).deriv

def IsCompleteGenerator (U : Set (Affine n)) (X : Affine n → Affine n) : Prop :=
  ∃ a : ℝ → Biholomorph U U, Continuous a ∧ a 0=1 ∧
    (∀ s t, a (s+t)=a s*a t) ∧ infinitesimalGenerator a=X

lemma IsCompleteGenerator.analyticOnNhd (hU : IsOpen U) [LocallyCompactSpace U]
    (hbd : Bornology.IsBounded U) {X : Affine n → Affine n} (hX : IsCompleteGenerator U X) :
    AnalyticOnNhd ℂ X U := by
  obtain ⟨a,ha,ha0,ham,rfl⟩ := hX
  exact infinitesimalGenerator_analytic hU a ha hbd ha0 ham

lemma IsCompleteGenerator.eq_zero_of_not_mem {X : Affine n → Affine n}
    (hX : IsCompleteGenerator U X) {x : Affine n} (hx : x∉U) : X x=0 := by
  obtain ⟨a,_,_,_,rfl⟩ := hX
  exact infinitesimalGenerator_of_not_mem a hx

variable (hU : IsOpen U) [LocallyCompactSpace U] (hc : IsConnected U)
    (hbd : Bornology.IsBounded U)
    (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
    [MulAction Γ U] [ProperSMul Γ U]
    [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val))

def completeGeneratorSpace : Submodule ℝ (Affine n → Affine n) where
  carrier := {X | IsCompleteGenerator U X}
  zero_mem' := ⟨fun _ => 1,continuous_const,rfl,(by intro s t; simp),infinitesimalGenerator_one⟩
  add_mem' := by
    rintro X Y ⟨a,ha,ha0,ham,rfl⟩ ⟨b,hb,hb0,hbm,rfl⟩
    obtain ⟨H,hH0,hHc,hHm,hHX⟩ := exists_oneParameter_generator_add hU hc hbd Γ hhol a b ha hb ha0 ham hb0 hbm
    refine ⟨H,hHc,hH0,hHm,funext fun x => ?_⟩
    by_cases hx : x∈U
    · exact hHX x hx
    · simp only [Pi.add_apply,infinitesimalGenerator_of_not_mem _ hx,add_zero]
  smul_mem' := by
    rintro c X ⟨a,ha,ha0,ham,rfl⟩
    refine ⟨fun t => a (c*t),ha.comp (continuous_const.mul continuous_id),by simpa using ha0,?_,
      infinitesimalGenerator_time_smul hU hbd a ha ha0 ham c⟩
    intro s t
    dsimp only
    rw [mul_add,ham]

def completeGeneratorFirstJet (p : U) : completeGeneratorSpace hU hc hbd Γ hhol →ₗ[ℝ]
    Affine n × (Affine n →L[ℂ] Affine n) where
  toFun X := (X.val p.val,fderiv ℂ X.val p.val)
  map_add' X Y := by
    change (X.val p.val+Y.val p.val,fderiv ℂ (X.val+Y.val) p.val)=
      (X.val p.val+Y.val p.val,fderiv ℂ X.val p.val+fderiv ℂ Y.val p.val)
    rw [fderiv_add ((X.property.analyticOnNhd hU hbd) p.val p.property).differentiableAt
      ((Y.property.analyticOnNhd hU hbd) p.val p.property).differentiableAt]
  map_smul' c X := by
    change (c • X.val p.val,fderiv ℂ (c • X.val) p.val)=
      (c • X.val p.val,c • fderiv ℂ X.val p.val)
    rw [fderiv_const_smul ((X.property.analyticOnNhd hU hbd) p.val p.property).differentiableAt]

theorem completeGeneratorFirstJet_injective (p : U) :
    Function.Injective (completeGeneratorFirstJet hU hc hbd Γ hhol p) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro X hX
  obtain ⟨a,ha,ha0,ham,heq⟩ := X.property
  have hvalue : infinitesimalGenerator a p.val=0 := by
    have h := congrArg Prod.fst hX
    change X.val p.val=0 at h
    rwa [heq]
  have hderiv : fderiv ℂ (infinitesimalGenerator a) p.val=0 := by
    have h := congrArg Prod.snd hX
    change fderiv ℂ X.val p.val=0 at h
    rwa [heq]
  have haone : a=(fun _ => 1) := funext fun t => oneParameter_eq_one_of_generator_zero_jet
    hU a ha hc.isPreconnected hbd ha0 ham p hvalue hderiv t
  apply Subtype.ext
  change X.val=0
  rw [← heq,haone,infinitesimalGenerator_one]

theorem finiteDimensional_completeGeneratorSpace :
    FiniteDimensional ℝ (completeGeneratorSpace hU hc hbd Γ hhol) := by
  obtain ⟨p,hp⟩ := hc.nonempty
  exact FiniteDimensional.of_injective (completeGeneratorFirstJet hU hc hbd Γ hhol ⟨p,hp⟩)
    (completeGeneratorFirstJet_injective hU hc hbd Γ hhol ⟨p,hp⟩)

end Biholomorph
end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_GeneratorPushForwardLinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
namespace Release061
open Set Filter Topology Metric
open scoped Classical
namespace Biholomorph
variable {n : ℕ} {U : Set (Affine n)}

def pushForwardGenerator (q : Biholomorph U U) (X : Affine n → Affine n)
    (x : Affine n) : Affine n :=
  if hx : x∈U then q.derivativeAt (q.toHomeomorph.symm ⟨x,hx⟩)
    (X (q.toHomeomorph.symm ⟨x,hx⟩).val) else 0

@[simp] theorem pushForwardGenerator_apply (q : Biholomorph U U) (X : Affine n → Affine n) (x : U) :
    pushForwardGenerator q X x.val=q.derivativeAt (q.toHomeomorph.symm x) (X (q.toHomeomorph.symm x).val) := by
  simp only [pushForwardGenerator,dite_eq_left x.property]

theorem infinitesimalGenerator_conjugate (hU : IsOpen U) [LocallyCompactSpace U]
    (hbd : Bornology.IsBounded U) (a : ℝ → Biholomorph U U) (ha : Continuous a)
    (ha0 : a 0=1) (ham : ∀ s t, a (s+t)=a s*a t) (q : Biholomorph U U) :
    infinitesimalGenerator (fun t => q*a t*q⁻¹)=pushForwardGenerator q (infinitesimalGenerator a) := by
  funext x
  by_cases hx : x∈U
  · let y : U := q.toHomeomorph.symm ⟨x,hx⟩
    have hy : (a 0).ambientAut y.val=y.val := by rw [ha0,ambientAut_apply,one_apply]
    have hq : HasFDerivAt q.ambientAut ((q.derivativeAt y).restrictScalars ℝ) ((a 0).ambientAut y.val) := by
      rw [hy]
      exact ((q.ambientAut_analytic hU y.val y.property).differentiableAt.hasFDerivAt).restrictScalars ℝ
    have hcomp := hq.comp_hasDerivAt 0 (infinitesimalGenerator_hasDerivAt hU hbd a ha ha0 ham y.val)
    have heq : (fun t => q.ambientAut ((a t).ambientAut y.val))=
        (fun t => (q*a t*q⁻¹).ambientAut x) := by
      funext t
      rw [ambientAut_apply (q*a t*q⁻¹) ⟨x,hx⟩,mul_apply,mul_apply,
        ambientAut_apply,ambientAut_apply]
      rfl
    have hcomp' : HasDerivAt (fun t => (q*a t*q⁻¹).ambientAut x)
        ((q.derivativeAt y) (infinitesimalGenerator a y.val)) 0 := by
      change HasDerivAt (fun t => q.ambientAut ((a t).ambientAut y.val))
        ((q.derivativeAt y) (infinitesimalGenerator a y.val)) 0 at hcomp
      rwa [heq] at hcomp
    change deriv (fun t => (q*a t*q⁻¹).ambientAut x) 0=pushForwardGenerator q (infinitesimalGenerator a) x
    rw [hcomp'.deriv,pushForwardGenerator,dite_eq_left hx]
  · rw [infinitesimalGenerator_of_not_mem _ hx,pushForwardGenerator,dite_eq_right hx]

theorem IsCompleteGenerator.pushForward (hU : IsOpen U) [LocallyCompactSpace U]
    (hbd : Bornology.IsBounded U) {X : Affine n → Affine n}
    (hX : IsCompleteGenerator U X) (q : Biholomorph U U) :
    IsCompleteGenerator U (pushForwardGenerator q X) := by
  obtain ⟨a,ha,ha0,ham,rfl⟩ := hX
  refine ⟨fun t => q*a t*q⁻¹,continuous_const.mul ha |>.mul continuous_const,by simp [ha0],?_,
    infinitesimalGenerator_conjugate hU hbd a ha ha0 ham q⟩
  intro s t
  dsimp only
  rw [ham]
  group

variable (hU : IsOpen U) [LocallyCompactSpace U] (hc : IsConnected U)
    (hbd : Bornology.IsBounded U)
    (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
    [MulAction Γ U] [ProperSMul Γ U]
    [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val))

 theorem completeGeneratorSpace_isClosed :
    IsClosed (completeGeneratorSpace hU hc hbd Γ hhol : Set (Affine n → Affine n)) := by
  have := finiteDimensional_completeGeneratorSpace hU hc hbd Γ hhol
  exact Submodule.closed_of_finiteDimensional _

include hU hc hbd Γ hhol in

theorem isCompleteGenerator_of_tendsto {ι : Type*} {l : Filter ι} [NeBot l]
    (X : ι → Affine n → Affine n) (Y : Affine n → Affine n)
    (hX : ∀ᶠ i in l, IsCompleteGenerator U (X i))
    (ht : ∀ x, Tendsto (fun i => X i x) l (𝓝 (Y x))) : IsCompleteGenerator U Y := by
  exact (completeGeneratorSpace_isClosed hU hc hbd Γ hhol).mem_of_tendsto
    (tendsto_pi_nhds.mpr ht) hX

end Biholomorph
end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_OneParameterFderivDeriv
attribute [-simp] _root_.OAI.Release061.Biholomorph.pushForwardGenerator_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
namespace Release061
open Set Filter Metric
open scoped Topology NNReal
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem tendstoUniformlyOn_fderiv_half_ball_filter
    {ι : Type*} {l : Filter ι} {f : ι → E → F} {g : E → F} {c : E} {R : ℝ} (hR : 0 < R)
    (hf : ∀ᶠ j in l, DifferentiableOn ℂ (f j) (ball c R))
    (hg : DifferentiableOn ℂ g (ball c R))
    (hfg : TendstoUniformlyOn f g l (ball c R)) :
    TendstoUniformlyOn (fun j => fderiv ℂ (f j)) (fderiv ℂ g) l (ball c (R/2)) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [hf,Metric.tendstoUniformlyOn_iff.mp hfg (ε*R/8) (by positivity)] with j hj he
  intro x hx
  have hb : ∀ z ∈ ball c R, ‖f j z-g z‖ ≤ ε*R/8 := by
    intro z hz
    exact le_of_lt (by simpa only [dist_eq_norm,norm_sub_rev] using he z hz)
  have hest := bounded_fderiv_on_half_ball hR (hj.sub hg) hb hx
  have hxR : x ∈ ball c R := ball_subset_ball (by linarith) hx
  rw [fderiv_sub (hj.differentiableAt (isOpen_ball.mem_nhds hxR))
    (hg.differentiableAt (isOpen_ball.mem_nhds hxR))] at hest
  rw [dist_eq_norm,norm_sub_rev]
  apply hest.trans_lt
  field_simp
  nlinarith

namespace Biholomorph
variable {n : ℕ} {U : Set (Affine n)} (hU : IsOpen U) [LocallyCompactSpace U]
    (hbd : Bornology.IsBounded U)
    (a : ℝ → Biholomorph U U) (ha : Continuous a)
    (ha0 : a 0=1) (ham : ∀ s t, a (s+t)=a s*a t)
include hU hbd ha ha0 ham

theorem infinitesimalGenerator_uniform_slope (K : Set (Affine n))
    (hK : IsCompact K) (hKU : K⊆U) :
    TendstoUniformlyOn (fun t : ℝ => fun x => t⁻¹ • ((a t).ambientAut x-x))
      (infinitesimalGenerator a) (𝓝[≠] 0) K := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have he := productCurve_uniform_consistency hU hbd a (fun _ => 1) ha continuous_const
    ha0 ham rfl (by intro s t; simp) K hK hKU (half_pos hε)
  filter_upwards [he.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with t ht ht0
  have ht0' : t≠0 := ht0
  intro x hx
  have hh := ht x hx
  simp only [mul_one,infinitesimalGenerator_one,Pi.zero_apply,add_zero] at hh
  have heq : t⁻¹ • ((a t).ambientAut x-x)-infinitesimalGenerator a x=
      t⁻¹ • ((a t).ambientAut x-x-t • infinitesimalGenerator a x) := by
    simp only [smul_sub,smul_smul,inv_mul_cancel₀ ht0',one_smul]
  rw [dist_eq_norm,norm_sub_rev,heq,norm_smul,Real.norm_eq_abs,abs_inv]
  calc
    _ ≤ |t|⁻¹ *((ε/2)*|t|) := mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr (abs_nonneg t))
    _ = ε/2 := by field_simp
    _ < ε := by linarith

theorem oneParameter_fderiv_hasDerivAt_zero (x : Affine n) (hx : x∈U) :
    HasDerivAt (fun t : ℝ => fderiv ℂ (a t).ambientAut x)
      (fderiv ℂ (infinitesimalGenerator a) x) 0 := by
  obtain ⟨R,hR,hRU⟩ := Metric.isOpen_iff.mp hU x hx
  let f : ℝ → Affine n → Affine n := fun t z => t⁻¹ • ((a t).ambientAut z-z)
  have hconv : TendstoUniformlyOn f (infinitesimalGenerator a) (𝓝[≠] 0) (ball x (R/2)) := by
    exact (infinitesimalGenerator_uniform_slope hU hbd a ha ha0 ham
      (closedBall x (R/2)) (isCompact_closedBall _ _)
      (fun y hy => hRU (closedBall_subset_ball (by linarith) hy))).mono ball_subset_closedBall
  have hf : ∀ᶠ t : ℝ in 𝓝[≠] 0, DifferentiableOn ℂ (f t) (ball x (R/2)) := by
    filter_upwards [] with t z hz
    exact ((((a t).ambientAut_analytic hU z (hRU (ball_subset_ball (by linarith) hz))).differentiableAt.sub
      differentiableAt_id).const_smul t⁻¹).differentiableWithinAt
  have hg : DifferentiableOn ℂ (infinitesimalGenerator a) (ball x (R/2)) := by
    intro z hz
    exact (infinitesimalGenerator_analytic hU a ha hbd ha0 ham z
      (hRU (ball_subset_ball (by linarith) hz))).differentiableAt.differentiableWithinAt
  have hd := (tendstoUniformlyOn_fderiv_half_ball_filter (half_pos hR) hf hg hconv).tendsto_at
    (show x∈ball x ((R/2)/2) by simp [hR])
  rw [hasDerivAt_iff_tendsto_slope]
  apply hd.congr'
  filter_upwards [] with t
  change fderiv ℂ ((t⁻¹:ℝ) • ((a t).ambientAut-id)) x = _
  rw [fderiv_const_smul (((a t).ambientAut_analytic hU x hx).differentiableAt.sub differentiableAt_id),
    fderiv_sub ((a t).ambientAut_analytic hU x hx).differentiableAt differentiableAt_id,fderiv_id]
  simp only [slope_def_module,sub_zero,ha0]
  change t⁻¹ • (fderiv ℂ (a t).ambientAut x-1)=t⁻¹ • (fderiv ℂ (a t).ambientAut x-(1 : Biholomorph U U).derivativeAt ⟨x,hx⟩)
  rw [derivativeAt_one hU]
end Biholomorph
end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_PushForwardGeneratorDeriv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
namespace Release061
open Set Filter Topology Metric
namespace Biholomorph
variable {n : ℕ} {U : Set (Affine n)} (hU : IsOpen U) [LocallyCompactSpace U]
    (hbd : Bornology.IsBounded U)
    (a : ℝ → Biholomorph U U) (ha : Continuous a)
    (ha0 : a 0=1) (ham : ∀ s t, a (s+t)=a s*a t)
include hU hbd ha ha0 ham

theorem pushForwardGenerator_hasDerivAt_zero
    (Y : Affine n → Affine n) (hY : AnalyticOnNhd ℂ Y U)
    (x : Affine n) (hx : x∈U) :
    HasDerivAt (fun t : ℝ => pushForwardGenerator (a t) Y x)
      (-VectorField.lieBracket ℂ (infinitesimalGenerator a) Y x) 0 := by
  let X := infinitesimalGenerator a
  let y : ℝ → Affine n := fun t => (a (-t)).ambientAut x
  let A : ℝ → Affine n →L[ℂ] Affine n := fun t => fderiv ℂ (a (-t)).ambientAut x
  let B : ℝ → Affine n →L[ℂ] Affine n := fun t => fderiv ℂ (a t).ambientAut (y t)
  have hneg (t : ℝ) : a (-t)=(a t)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← ham,neg_add_cancel,ha0]
  have hy0 : y 0=x := by simp [y,ha0,ambientAut_apply (1 : Biholomorph U U) ⟨x,hx⟩]
  have hA0 : A 0=1 := by
    simpa only [A,neg_zero,ha0,derivativeAt] using derivativeAt_one hU (⟨x,hx⟩ : U)
  have hB0 : B 0=1 := by simpa only [B,hy0,ha0,derivativeAt] using derivativeAt_one hU (⟨x,hx⟩ : U)
  have hdy : HasDerivAt y (-X x) 0 := by
    have hh : HasDerivAt (fun t => (a t).ambientAut x) (X x) (-(0:ℝ)) := by
      simpa only [neg_zero] using infinitesimalGenerator_hasDerivAt hU hbd a ha ha0 ham x
    have ht := hh.scomp 0 ((hasDerivAt_id (0:ℝ)).neg)
    simpa only [Function.comp_def,neg_zero,neg_smul,one_smul] using ht
  have hdA : HasDerivAt A (-fderiv ℂ X x) 0 := by
    have hh : HasDerivAt (fun t => fderiv ℂ (a t).ambientAut x) (fderiv ℂ X x) (-(0:ℝ)) := by
      simpa only [neg_zero] using oneParameter_fderiv_hasDerivAt_zero hU hbd a ha ha0 ham x hx
    have ht := hh.scomp 0 ((hasDerivAt_id (0:ℝ)).neg)
    simpa only [Function.comp_def,neg_zero,neg_smul,one_smul] using ht
  have hdY : HasDerivAt (fun t => Y (y t)) (-(fderiv ℂ Y x) (X x)) 0 := by
    have hcomp := (((hY x hx).differentiableAt.hasFDerivAt).restrictScalars ℝ)
    rw [← hy0] at hcomp
    have ht := hcomp.comp_hasDerivAt 0 hdy
    change HasDerivAt (fun t => Y (y t)) ((fderiv ℂ Y (y 0)) (-X x)) 0 at ht
    simpa only [hy0,map_neg] using ht
  have hdAY : HasDerivAt (fun t => A t (Y x)) (-(fderiv ℂ X x) (Y x)) 0 := by
    have hl := ((ContinuousLinearMap.apply ℂ (Affine n) (Y x)).restrictScalars ℝ).hasFDerivAt (x := A 0)
    have ht := hl.comp_hasDerivAt 0 hdA
    exact ht
  let r : ℝ → Affine n := fun t => Y (y t)-A t (Y x)
  have hr0 : r 0=0 := by simp [r,hy0,hA0]
  have hdr : HasDerivAt r (-VectorField.lieBracket ℂ X Y x) 0 := by
    have ht := hdY.sub hdAY
    have heq : -(fderiv ℂ Y x) (X x) - (-(fderiv ℂ X x) (Y x)) =
        -VectorField.lieBracket ℂ X Y x := by
      dsimp only [VectorField.lieBracket]
      abel
    rw [heq] at ht
    exact ht
  have hB : ContinuousAt B 0 := by
    have ht := (ambientAut_derivative_joint_continuousAt hU (q := (a 0,y 0)) (hy0 ▸ hx)).comp (f := fun t : ℝ => (a t,y t)) (x := (0:ℝ))
      (ha.continuousAt.prodMk hdy.continuousAt)
    exact ht
  have he (t : ℝ) : B t (A t (Y x))=Y x := by
    have hprod := derivativeAt_mul hU (a t) (a (-t)) (⟨x,hx⟩ : U)
    rw [hneg,mul_inv_cancel,derivativeAt_one hU] at hprod
    have hh := congrArg (fun L : Affine n →L[ℂ] Affine n => L (Y x)) hprod
    change Y x = (fderiv ℂ (a t).ambientAut ((a t)⁻¹.toHomeomorph ⟨x,hx⟩).val)
      (fderiv ℂ (a t)⁻¹.ambientAut x (Y x)) at hh
    simpa only [B,A,y,hneg,ambientAut_apply (a t)⁻¹ ⟨x,hx⟩] using hh.symm
  have hp (t : ℝ) : pushForwardGenerator (a t) Y x=B t (Y (y t)) := by
    rw [pushForwardGenerator,dite_eq_left hx]
    dsimp only [B,y]
    rw [hneg,ambientAut_apply (a t)⁻¹ ⟨x,hx⟩]
    rfl
  have hp0 : pushForwardGenerator (a 0) Y x=Y x := by rw [hp,hB0,hy0]; rfl
  rw [hasDerivAt_iff_tendsto_slope]
  have hc : Tendsto (fun t : ℝ => B t (slope r 0 t)) (𝓝[≠] 0)
      (𝓝 (-VectorField.lieBracket ℂ X Y x)) := by
    have hbt : Tendsto B (𝓝[≠] (0:ℝ)) (𝓝 (B 0)) := hB.tendsto.mono_left nhdsWithin_le_nhds
    have heval : Continuous (fun p : (Affine n →L[ℂ] Affine n) × Affine n => p.1 p.2) :=
      continuous_fst.clm_apply continuous_snd
    have ht := heval.continuousAt.tendsto.comp (hbt.prodMk_nhds hdr.tendsto_slope)
    rw [hB0] at ht
    change Tendsto (fun t : ℝ => B t (slope r 0 t)) (𝓝[≠] 0)
      (𝓝 ((1 : Affine n →L[ℂ] Affine n) (-VectorField.lieBracket ℂ X Y x))) at ht
    exact ht
  apply hc.congr'
  filter_upwards [] with t
  rw [slope_def_module,slope_def_module,sub_zero,hr0,sub_zero,hp0,hp]
  dsimp only [r]
  rw [ContinuousLinearMap.map_smul_of_tower,map_sub,he]
end Biholomorph
end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_CompleteGeneratorLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
namespace Release061
open Set Filter Topology Metric
namespace Biholomorph
variable {n : ℕ} {U : Set (Affine n)} (hU : IsOpen U) [LocallyCompactSpace U]
    (hc : IsConnected U) (hbd : Bornology.IsBounded U)
    (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
    [MulAction Γ U] [ProperSMul Γ U]
    [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val))
include hU hc hbd Γ hhol

theorem IsCompleteGenerator.lieBracket {X Y : Affine n → Affine n}
    (hX : IsCompleteGenerator U X) (hY : IsCompleteGenerator U Y) :
    IsCompleteGenerator U (VectorField.lieBracket ℂ X Y) := by
  obtain ⟨a,ha,ha0,ham,rfl⟩ := hX
  let S := completeGeneratorSpace hU hc hbd Γ hhol
  let Z : ℝ → Affine n → Affine n := fun t =>
    t⁻¹ • (pushForwardGenerator (a t) Y-pushForwardGenerator (a 0) Y)
  have hZ : ∀ t, Z t∈S := by
    intro t
    exact S.smul_mem t⁻¹ (S.sub_mem (hY.pushForward hU hbd (a t)) (hY.pushForward hU hbd (a 0)))
  have hz : IsCompleteGenerator U (-VectorField.lieBracket ℂ (infinitesimalGenerator a) Y) := by
    apply isCompleteGenerator_of_tendsto hU hc hbd Γ hhol (l := 𝓝[≠] (0:ℝ)) Z _ (Eventually.of_forall hZ)
    intro x
    have hd : HasDerivAt (fun t : ℝ => pushForwardGenerator (a t) Y x)
        (-VectorField.lieBracket ℂ (infinitesimalGenerator a) Y x) 0 := by
      by_cases hx : x∈U
      · exact pushForwardGenerator_hasDerivAt_zero hU hbd a ha ha0 ham Y
          (hY.analyticOnNhd hU hbd) x hx
      · have hbr := VectorField.lieBracket_eq_zero_of_eq_zero (𝕜 := ℂ)
          (infinitesimalGenerator_of_not_mem a hx) (hY.eq_zero_of_not_mem hx)
        simpa only [pushForwardGenerator,dite_eq_right hx,hbr,neg_zero] using hasDerivAt_const (0:ℝ) (0 : Affine n)
    apply hd.tendsto_slope.congr'
    filter_upwards [] with t
    change (t-(0:ℝ))⁻¹ • (pushForwardGenerator (a t) Y x - pushForwardGenerator (a 0) Y x) =
      t⁻¹ • (pushForwardGenerator (a t) Y x - pushForwardGenerator (a 0) Y x)
    rw [sub_zero]
  have hz' : -(-VectorField.lieBracket ℂ (infinitesimalGenerator a) Y)∈S := S.neg_mem hz
  change IsCompleteGenerator U (-(-VectorField.lieBracket ℂ (infinitesimalGenerator a) Y)) at hz'
  simpa only [neg_neg] using hz'

def completeGeneratorBracket (X Y : completeGeneratorSpace hU hc hbd Γ hhol) :
    completeGeneratorSpace hU hc hbd Γ hhol :=
  ⟨VectorField.lieBracket ℂ X.val Y.val,X.property.lieBracket hU hc hbd Γ hhol Y.property⟩

end Biholomorph
end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_ProjectedJetSequencesNot
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
namespace Release061
open Set Filter Topology Metric
namespace Biholomorph
variable {n : ℕ} {U : Set (Affine n)}

def ambientFirstJet (p : U) (a : Biholomorph U U) :
    Affine n × (Affine n →L[ℂ] Affine n) := (a.ambientAut p.val,a.derivativeAt p)

end Biholomorph
end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_FlowWordFirstJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
namespace Release061
open Set Filter Topology Metric
namespace Biholomorph

section
variable {n : ℕ} {U : Set (Affine n)} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι : Type*}

def flowWord (a : ι → ℝ → Biholomorph U U) (l : ι → E →L[ℝ] ℝ) :
    List ι → E → Biholomorph U U
  | [],_ => 1
  | i::is,t => a i (l i t)*flowWord a l is t

end

end Biholomorph
end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_ContinuousAutTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
namespace Release061

namespace Biholomorph

open Set Filter Topology

variable {n m : ℕ} {U : Set (Affine n)} {D : Set (Affine m)}

def autTransport (e : Biholomorph U D) (a : Biholomorph U U) : Biholomorph D D :=
  (e.symm.trans a).trans e

@[simp] theorem autTransport_apply (e : Biholomorph U D) (a : Biholomorph U U) (p : D) :
    (autTransport e a).toHomeomorph p=
      e.toHomeomorph (a.toHomeomorph (e.toHomeomorph.symm p)) := rfl

@[simp] theorem autTransport_one (e : Biholomorph U D) : autTransport e 1=1 := by
  apply Biholomorph.ext
  intro p
  exact e.toHomeomorph.apply_symm_apply p

@[simp] theorem autTransport_mul (e : Biholomorph U D) (a b : Biholomorph U U) :
    autTransport e (a*b)=autTransport e a*autTransport e b := by
  apply Biholomorph.ext
  intro p
  simp only [autTransport_apply,mul_apply,e.toHomeomorph.symm_apply_apply]

@[simp] theorem autTransport_inv (e : Biholomorph U D) (a : Biholomorph U U) :
    autTransport e a⁻¹=(autTransport e a)⁻¹ := rfl

@[simp] theorem autTransport_symm_cancel (e : Biholomorph U D) (a : Biholomorph U U) :
    autTransport e.symm (autTransport e a)=a := by
  apply Biholomorph.ext
  intro p
  change e.toHomeomorph.symm (e.toHomeomorph (a.toHomeomorph
    (e.toHomeomorph.symm (e.toHomeomorph p))))=a.toHomeomorph p
  simp only [e.toHomeomorph.symm_apply_apply]

end Biholomorph
end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_AdNilpotentPositiveDilations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
namespace Release061
open Set Filter Topology
namespace Biholomorph
variable {n : ℕ} {D : Set (Affine n)}

def translationAut (v : Affine n)
    (hD : ∀ t : ℝ, ∀ x, x+t • v ∈ D ↔ x∈D) (t : ℝ) : Biholomorph D D :=
  biholomorphOfAmbientInverse D D (fun x => x+t • v) (fun x => x+(-t) • v)
    (fun x _ => analyticAt_id.add analyticAt_const)
    (fun x _ => analyticAt_id.add analyticAt_const)
    (fun _ hx => (hD t _).mpr hx) (fun _ hx => (hD (-t) _).mpr hx)
    (by intro x _; simp [add_assoc]) (by intro x _; simp [add_assoc])

@[simp] theorem translationAut_apply (v : Affine n)
    (hD : ∀ t : ℝ, ∀ x, x+t • v ∈ D ↔ x∈D) (t : ℝ) (x : D) :
    ((translationAut v hD t).toHomeomorph x).val=x.val+t • v := rfl

@[simp] theorem translationAut_inv_apply (v : Affine n)
    (hD : ∀ t : ℝ, ∀ x, x+t • v ∈ D ↔ x∈D) (t : ℝ) (x : D) :
    ((translationAut v hD t).toHomeomorph.symm x).val=x.val+(-t) • v := rfl

@[simp] theorem translationAut_zero (v : Affine n)
    (hD : ∀ t : ℝ, ∀ x, x+t • v ∈ D ↔ x∈D) : translationAut v hD 0=1 := by
  apply Biholomorph.ext
  intro x
  apply Subtype.ext
  simp only [translationAut_apply,zero_smul,add_zero,one_apply]

def linearAut (L : Affine n ≃L[ℂ] Affine n) (hL : ∀ x, L x∈D ↔ x∈D) :
    Biholomorph D D :=
  biholomorphOfAmbientInverse D D L L.symm
    (fun x _ => L.toContinuousLinearMap.analyticAt x)
    (fun x _ => L.symm.toContinuousLinearMap.analyticAt x)
    (fun _ hx => (hL _).mpr hx)
    (fun _ hx => (hL _).mp (by simpa only [L.apply_symm_apply] using hx))
    (fun x _ => L.symm_apply_apply x) (fun x _ => L.apply_symm_apply x)

@[simp] theorem linearAut_apply (L : Affine n ≃L[ℂ] Affine n)
    (hL : ∀ x, L x∈D ↔ x∈D) (x : D) :
    ((linearAut L hL).toHomeomorph x).val=L x.val := rfl

@[simp] theorem linearAut_inv_apply (L : Affine n ≃L[ℂ] Affine n)
    (hL : ∀ x, L x∈D ↔ x∈D) (x : D) :
    ((linearAut L hL).toHomeomorph.symm x).val=L.symm x.val := rfl

end Biholomorph
end Release061

open Filter Topology

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_AffineProductCoordinates
attribute [-instance] _root_.OAI.Release061.Biholomorph.automorphismGroup _root_.OAI.Release061.Biholomorph.automorphismInv _root_.OAI.Release061.Biholomorph.automorphismMetrizable _root_.OAI.Release061.Biholomorph.automorphismMul _root_.OAI.Release061.Biholomorph.automorphismOne _root_.OAI.Release061.Biholomorph.automorphismSecondCountable _root_.OAI.Release061.Biholomorph.automorphismTopologicalGroup _root_.OAI.Release061.Biholomorph.automorphismTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set

def affineProductCoordinates (m k : ℕ) : (Affine m × Affine k) ≃L[ℂ] Affine (m+k) :=
  ((LinearEquiv.sumArrowLequivProdArrow (Fin m) (Fin k) ℂ ℂ).symm.trans
    (LinearEquiv.piCongrLeft ℂ (fun _ : Fin (m+k) => ℂ) finSumFinEquiv)).toContinuousLinearEquiv

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_CoordinateFieldApply
attribute [-simp] _root_.OAI.Release061.Biholomorph.linearAut_apply _root_.OAI.Release061.Biholomorph.linearAut_inv_apply _root_.OAI.Release061.Biholomorph.translationAut_apply _root_.OAI.Release061.Biholomorph.translationAut_inv_apply _root_.OAI.Release061.Biholomorph.translationAut_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
open Filter Topology
namespace Release061
open Set Filter Topology
namespace Biholomorph
open scoped Classical
variable {n m : ℕ} {U : Set (Affine n)} {D : Set (Affine m)}

def ambientMap (e : Biholomorph U D) : Affine n → Affine m :=
  ambientExtend (fun p => (e.toHomeomorph p).val)

@[simp] theorem ambientMap_apply (e : Biholomorph U D) (p : U) :
    e.ambientMap p.val=(e.toHomeomorph p).val := ambientExtend_apply _ p

 theorem ambientMap_analytic (hU : IsOpen U) (e : Biholomorph U D) :
    AnalyticOnNhd ℂ e.ambientMap U := e.holomorphic_toFun.analyticOnNhd_extend hU

 def mapDerivative (e : Biholomorph U D) (p : U) : Affine n →L[ℂ] Affine m :=
  fderiv ℂ e.ambientMap p.val

 theorem mapDerivative_symm_comp (hU : IsOpen U) (hD : IsOpen D)
    (e : Biholomorph U D) (p : U) :
    (e.symm.mapDerivative (e.toHomeomorph p)).comp (e.mapDerivative p)=
      ContinuousLinearMap.id ℂ (Affine n) := by
  have hi := (e.symm.ambientMap_analytic hD _ (e.toHomeomorph p).property).differentiableAt.hasFDerivAt
  rw [←ambientMap_apply e p] at hi
  have hcomp := hi.comp p.val ((e.ambientMap_analytic hU _ p.property).differentiableAt.hasFDerivAt)
  have heq : e.symm.ambientMap ∘ e.ambientMap =ᶠ[𝓝 p.val] id := by
    filter_upwards [hU.mem_nhds p.property] with x hx
    rw [Function.comp_apply,ambientMap_apply _ ⟨x,hx⟩,ambientMap_apply]
    exact congrArg Subtype.val (e.toHomeomorph.symm_apply_apply ⟨x,hx⟩)
  have hh := hcomp.congr_of_eventuallyEq heq.symm
  simpa only [ambientMap_apply,Function.comp_def,mapDerivative] using hh.unique (hasFDerivAt_id p.val)

def mapDerivativeEquiv (hU : IsOpen U) (hD : IsOpen D)
    (e : Biholomorph U D) (p : U) : Affine n ≃L[ℂ] Affine m :=
  ContinuousLinearEquiv.equivOfInverse (e.mapDerivative p)
    (e.symm.mapDerivative (e.toHomeomorph p))
    (by
      intro v
      exact congrArg (fun L : Affine n →L[ℂ] Affine n => L v)
        (mapDerivative_symm_comp hU hD e p))
    (by
        intro v
        have h := mapDerivative_symm_comp hD hU e.symm (e.toHomeomorph p)
        change (e.mapDerivative (e.toHomeomorph.symm (e.toHomeomorph p))).comp
          (e.symm.mapDerivative (e.toHomeomorph p))=ContinuousLinearMap.id ℂ (Affine m) at h
        rw [e.toHomeomorph.symm_apply_apply] at h
        exact congrArg (fun L : Affine m →L[ℂ] Affine m => L v) h)

@[simp] theorem mapDerivativeEquiv_apply (hU : IsOpen U) (hD : IsOpen D)
    (e : Biholomorph U D) (p : U) (v : Affine n) :
    mapDerivativeEquiv hU hD e p v=e.mapDerivative p v := rfl

def coordinateField (e : Biholomorph U D) (X : Affine n → Affine n)
    (x : Affine m) : Affine m :=
  if hx : x∈D then e.mapDerivative (e.toHomeomorph.symm ⟨x,hx⟩)
    (X (e.toHomeomorph.symm ⟨x,hx⟩).val) else 0

@[simp] theorem coordinateField_apply (e : Biholomorph U D) (X : Affine n → Affine n)
    (p : D) : coordinateField e X p.val=
      e.mapDerivative (e.toHomeomorph.symm p) (X (e.toHomeomorph.symm p).val) := by
  simp only [coordinateField,dite_eq_left p.property]

end Biholomorph
end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_FieldSecondJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
open Filter Topology
namespace Release061
open Set Filter Topology
namespace Biholomorph

def rotationScalar (t : ℝ) : ℂ := Complex.exp ((t : ℂ)*Complex.I)
@[simp] theorem rotationScalar_zero : rotationScalar 0=1 := by simp [rotationScalar]
@[simp] theorem rotationScalar_add (s t : ℝ) : rotationScalar (s+t)=rotationScalar s*rotationScalar t := by
  simp [rotationScalar,add_mul,Complex.exp_add]
@[simp] theorem rotationScalar_mul_neg (t : ℝ) : rotationScalar t*rotationScalar (-t)=1 := by
  rw [←rotationScalar_add,add_neg_cancel,rotationScalar_zero]
@[simp] theorem rotationScalar_norm (t : ℝ) : ‖rotationScalar t‖=1 := Complex.norm_exp_ofReal_mul_I t

def tangentialRotation (r k : ℕ) (t : ℝ) :
    (Affine r × Affine k) ≃L[ℂ] (Affine r × Affine k) :=
  ContinuousLinearEquiv.equivOfInverse
    (((rotationScalar t) • ContinuousLinearMap.fst ℂ (Affine r) (Affine k)).prod
      (ContinuousLinearMap.snd ℂ (Affine r) (Affine k)))
    (((rotationScalar (-t)) • ContinuousLinearMap.fst ℂ (Affine r) (Affine k)).prod
      (ContinuousLinearMap.snd ℂ (Affine r) (Affine k)))
    (by intro p; ext i <;> simp [smul_smul,←rotationScalar_add])
    (by intro p; ext i <;> simp [smul_smul,←rotationScalar_add])

def flatTangentialRotation (r k : ℕ) (t : ℝ) : Affine (r+k) ≃L[ℂ] Affine (r+k) :=
  ((affineProductCoordinates r k).symm.trans (tangentialRotation r k t)).trans
    (affineProductCoordinates r k)

@[simp] theorem flatTangentialRotation_apply (r k : ℕ) (t : ℝ) (x : Affine (r+k)) :
    flatTangentialRotation r k t x=affineProductCoordinates r k
      (rotationScalar t • ((affineProductCoordinates r k).symm x).1,
        ((affineProductCoordinates r k).symm x).2) := rfl

def flatTangentialInfinitesimal (r k : ℕ) : Affine (r+k) →L[ℂ] Affine (r+k) :=
  (affineProductCoordinates r k).toContinuousLinearMap.comp
    (((Complex.I • ContinuousLinearMap.fst ℂ (Affine r) (Affine k)).prod 0).comp
      (affineProductCoordinates r k).symm.toContinuousLinearMap)

end Biholomorph
end Release061

open Filter Topology

open Filter Topology

section
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [CompleteSpace G]

def ZeroSecondJet (f : E → F) (p : E) : Prop :=
  f p=0 ∧ fderiv ℂ f p=0 ∧ fderiv ℂ (fderiv ℂ f) p=0

 omit [CompleteSpace E] [CompleteSpace F] in
 theorem ZeroSecondJet.congr {f g : E → F} {p : E}
    (h : f =ᶠ[𝓝 p] g) (hf : ZeroSecondJet f p) : ZeroSecondJet g p := by
  simpa only [ZeroSecondJet,←h.eq_of_nhds,←h.fderiv_eq,←h.fderiv.fderiv_eq] using hf
end

open Filter Topology

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

 theorem fderiv_fderiv_add_of_analytic {V W : E → E} {p : E}
    (hV : AnalyticAt ℂ V p) (hW : AnalyticAt ℂ W p) :
    fderiv ℂ (fderiv ℂ (V+W)) p=fderiv ℂ (fderiv ℂ V) p+fderiv ℂ (fderiv ℂ W) p := by
  have he : fderiv ℂ (V+W) =ᶠ[𝓝 p] fun x => fderiv ℂ V x+fderiv ℂ W x := by
    filter_upwards [hV.eventually_analyticAt,hW.eventually_analyticAt] with x hx hy
    exact fderiv_add hx.differentiableAt hy.differentiableAt
  rw [he.fderiv_eq]
  exact fderiv_add hV.fderiv.differentiableAt hW.fderiv.differentiableAt

 theorem fderiv_fderiv_smul_of_analytic {V : E → E} {p : E}
    (hV : AnalyticAt ℂ V p) (c : ℂ) :
    fderiv ℂ (fderiv ℂ (c • V)) p=c • fderiv ℂ (fderiv ℂ V) p := by
  have he : fderiv ℂ (c • V) =ᶠ[𝓝 p] fun x => c • fderiv ℂ V x := by
    filter_upwards [hV.eventually_analyticAt] with x hx
    exact fderiv_const_smul hx.differentiableAt c
  rw [he.fderiv_eq]
  exact fderiv_const_smul hV.fderiv.differentiableAt c

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
    (F : V →ₗ[ℂ] (E → E)) (p : E) (hF : ∀ X, AnalyticAt ℂ (F X) p)

def fieldFirstJet : V →ₗ[ℂ] E →L[ℂ] E where
  toFun X := fderiv ℂ (F X) p
  map_add' X Y := by
    rw [map_add]
    exact fderiv_add (hF X).differentiableAt (hF Y).differentiableAt
  map_smul' c X := by
    rw [map_smul]
    exact fderiv_const_smul (hF X).differentiableAt c

def fieldSecondJet : V →ₗ[ℂ] E →L[ℂ] E →L[ℂ] E where
  toFun X := fderiv ℂ (fderiv ℂ (F X)) p
  map_add' X Y := by
    rw [map_add]
    exact fderiv_fderiv_add_of_analytic (hF X) (hF Y)
  map_smul' c X := by
    rw [map_smul]
    exact fderiv_fderiv_smul_of_analytic (hF X) c

end

open Polynomial

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_AnalyticSecondJetCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
open Filter Topology
open Filter Topology
open Filter Topology
open Filter Topology
open Polynomial

open Filter Topology

abbrev SecondJetIndex (ι : Type*) := ι ⊕ ((ι × ι) ⊕ (ι × ι × ι))

def secondJetWeight {ι : Type*} (w : ι → ℂ) : SecondJetIndex ι → ℂ
  | .inl i => -w i
  | .inr (.inl (i,j)) => w j-w i
  | .inr (.inr (i,j,k)) => w j+w k-w i

variable {E V ι : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    [AddCommGroup V] [Module ℂ V]
    (F : V →ₗ[ℂ] (E → E)) (p : E) (hF : ∀ X, AnalyticAt ℂ (F X) p)
    (b : Module.Basis ι ℂ E)

def analyticSecondJetCoordinates : V →ₗ[ℂ] (SecondJetIndex ι → ℂ) where
  toFun X j := match j with
    | .inl i => b.repr (F X p) i
    | .inr (.inl (i,j)) => b.repr (fieldFirstJet F p hF X (b j)) i
    | .inr (.inr (i,j,k)) => b.repr (fieldSecondJet F p hF X (b j) (b k)) i
  map_add' X Y := by
    funext j
    rcases j with i | (⟨i,j⟩ | ⟨i,j,k⟩) <;>
      simp only [map_add,Pi.add_apply,add_apply,Finsupp.add_apply]
  map_smul' c X := by
    funext j
    rcases j with i | (⟨i,j⟩ | ⟨i,j,k⟩) <;>
      simp only [map_smul,Pi.smul_apply,smul_apply,Finsupp.smul_apply,
        RingHom.id_apply,smul_eq_mul]

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_CoordinateFieldLinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
open Filter Topology
namespace Release061
open Set Filter Topology
namespace Biholomorph
open scoped Classical
variable {n m : ℕ} {U : Set (Affine n)} {D : Set (Affine m)}

def coordinateFieldLinear (e : Biholomorph U D) :
    (Affine n → Affine n) →ₗ[ℝ] (Affine m → Affine m) where
  toFun := coordinateField e
  map_add' X Y := by
    funext x
    by_cases hx : x∈D
    · simp only [coordinateField,dite_eq_left hx,Pi.add_apply,map_add]
    · simp only [coordinateField,dite_eq_right hx,Pi.add_apply,add_zero]
  map_smul' c X := by
    funext x
    by_cases hx : x∈D
    · simp only [coordinateField,dite_eq_left hx,Pi.smul_apply,
        ContinuousLinearMap.map_smul_of_tower,Real.ringHom_apply]
    · simp only [coordinateField,dite_eq_right hx,Pi.smul_apply,smul_zero,Real.ringHom_apply]

end Biholomorph
end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_CriticalAffineBundleNeighborhood
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Topology
open scoped Classical

variable {E X K : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  [NormedAddCommGroup K] [NormedSpace ℝ K] [FiniteDimensional ℝ K]

noncomputable def criticalBundleLinear (A : X → E →L[ℝ] X) (e : E ≃L[ℝ] X × K) (x : X) :
    E →L[ℝ] X × K := (A x).prod ((ContinuousLinearMap.snd ℝ X K).comp e.toContinuousLinearMap)

noncomputable def criticalBundleParam (A : X → E →L[ℝ] X) (e : E ≃L[ℝ] X × K)
    (b : X → X) (p : X × K) : E := (criticalBundleLinear A e p.1).inverse (b p.1,p.2)

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_ParameterPeakMaximizer
attribute [-instance] _root_.OAI.Release061.Biholomorph.automorphismGroup _root_.OAI.Release061.Biholomorph.automorphismInv _root_.OAI.Release061.Biholomorph.automorphismMetrizable _root_.OAI.Release061.Biholomorph.automorphismMul _root_.OAI.Release061.Biholomorph.automorphismOne _root_.OAI.Release061.Biholomorph.automorphismSecondCountable _root_.OAI.Release061.Biholomorph.automorphismTopologicalGroup _root_.OAI.Release061.Biholomorph.automorphismTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Complex Filter Metric
open scoped Topology
def parameterPotential {n : ℕ} (P : MvPolynomial (Fin n) ℂ)
    (a : Affine n →L[ℂ] ℂ) (q : Affine n) : ℝ :=
  ‖MvPolynomial.eval q P‖ * Real.exp (coordinateEnergy q + (a q).re)

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_RealCriticalMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Topology
open scoped Classical

noncomputable def realCriticalMatrix {d N : ℕ}
    (q : (Fin d → ℝ) → (Fin N → ℂ)) (x : Fin d → ℝ) :
    ((Fin N → ℂ) →L[ℂ] ℂ) →L[ℝ] (Fin d → ℝ) :=
  (ContinuousLinearEquiv.piRing (𝕜 := ℝ) (E := ℝ) (Fin d)).toContinuousLinearMap.comp
    (((ContinuousLinearMap.compL ℝ (Fin d → ℝ) (Fin N → ℂ) ℝ).flip (fderiv ℝ q x)).comp
      (StrongDual.extendRCLikeL (𝕜 := ℂ) (F := Fin N → ℂ)).symm.toContinuousLinearMap)

noncomputable def realCriticalConstant {d : ℕ} (f : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) :
    Fin d → ℝ := -(ContinuousLinearEquiv.piRing (𝕜 := ℝ) (E := ℝ) (Fin d)) (fderiv ℝ f x)

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_MaximizerBundleBorel
attribute [-instance] _root_.OAI.Release061.Biholomorph.automorphismGroup _root_.OAI.Release061.Biholomorph.automorphismInv _root_.OAI.Release061.Biholomorph.automorphismMetrizable _root_.OAI.Release061.Biholomorph.automorphismMul _root_.OAI.Release061.Biholomorph.automorphismOne _root_.OAI.Release061.Biholomorph.automorphismSecondCountable _root_.OAI.Release061.Biholomorph.automorphismTopologicalGroup _root_.OAI.Release061.Biholomorph.automorphismTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Topology MeasureTheory
open scoped Classical ContDiff

noncomputable def parameterLogBase {N : ℕ} (P : MvPolynomial (Fin N) ℂ) (z : Affine N) : ℝ :=
  Real.log ‖MvPolynomial.eval z P‖ + coordinateEnergy z

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_CriticalCountableCharts
attribute [-instance] _root_.OAI.Release061.Biholomorph.automorphismGroup _root_.OAI.Release061.Biholomorph.automorphismInv _root_.OAI.Release061.Biholomorph.automorphismMetrizable _root_.OAI.Release061.Biholomorph.automorphismMul _root_.OAI.Release061.Biholomorph.automorphismOne _root_.OAI.Release061.Biholomorph.automorphismSecondCountable _root_.OAI.Release061.Biholomorph.automorphismTopologicalGroup _root_.OAI.Release061.Biholomorph.automorphismTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Topology MeasureTheory
open scoped Classical

structure ActualCriticalChart {d N : ℕ} (P : MvPolynomial (Fin N) ℂ)
    (q : (Fin d → ℝ) → Affine N) where
  fiberDim : ℕ
  split : (Affine N →L[ℂ] ℂ) ≃L[ℝ] ((Fin d → ℝ) × (Fin fiberDim → ℝ))
  base : Set (Fin d → ℝ)
  isOpen_base : IsOpen base
  continuous_q : ContinuousOn q base
  smooth_param : ContDiffOn ℝ 1 (criticalBundleParam (realCriticalMatrix q) split
    (realCriticalConstant (parameterLogBase P ∘ q))) (base ×ˢ univ)
  range_param : ∀ x ∈ base, range (fun k => criticalBundleParam (realCriticalMatrix q) split
    (realCriticalConstant (parameterLogBase P ∘ q)) (x,k)) =
    {a | fderiv ℝ (fun y => parameterLogBase P (q y) + (a (q y)).re) x = 0}

namespace ActualCriticalChart
variable {d N : ℕ} {P : MvPolynomial (Fin N) ℂ} {q : (Fin d → ℝ) → Affine N}
noncomputable def param (c : ActualCriticalChart P q) :
    (Fin d → ℝ) × (Fin c.fiberDim → ℝ) → (Affine N →L[ℂ] ℂ) :=
  criticalBundleParam (realCriticalMatrix q) c.split
    (realCriticalConstant (parameterLogBase P ∘ q))

def maxLocus (c : ActualCriticalChart P q) (K : Set (Affine N)) :
    Set ((Fin d → ℝ) × (Fin c.fiberDim → ℝ)) :=
  {p | p.1 ∈ c.base ∧ q p.1 ∈ K ∧ IsMaxOn (parameterPotential P (c.param p)) K (q p.1)}

end ActualCriticalChart

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_ImagPartLieReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
open Filter Topology
open Filter Topology
open Filter Topology
open Filter Topology
open Polynomial
open Filter Topology
open scoped TensorProduct
open Set Filter Topology
open scoped TensorProduct
open scoped TensorProduct
namespace Complexification
section Linear
variable {V : Type*} [AddCommGroup V] [Module ℝ V]

def realPart : (ℂ ⊗[ℝ] V) →ₗ[ℝ] V :=
  (TensorProduct.lid ℝ V).toLinearMap.comp
    (TensorProduct.map Complex.reLm (LinearMap.id : V →ₗ[ℝ] V))
def imagPart : (ℂ ⊗[ℝ] V) →ₗ[ℝ] V :=
  (TensorProduct.lid ℝ V).toLinearMap.comp
    (TensorProduct.map Complex.imLm (LinearMap.id : V →ₗ[ℝ] V))
def ofReal : V →ₗ[ℝ] (ℂ ⊗[ℝ] V) := TensorProduct.mk ℝ ℂ V 1

@[simp] theorem realPart_tmul (z : ℂ) (X : V) : realPart (z ⊗ₜ[ℝ] X)=z.re • X := rfl
@[simp] theorem imagPart_tmul (z : ℂ) (X : V) : imagPart (z ⊗ₜ[ℝ] X)=z.im • X := rfl
@[simp] theorem ofReal_apply (X : V) : ofReal X=1 ⊗ₜ[ℝ] X := rfl
@[simp] theorem realPart_ofReal (X : V) : realPart (ofReal X)=X := by simp
@[simp] theorem imagPart_ofReal (X : V) : imagPart (ofReal X)=0 := by simp

end Linear
variable {V : Type*} [LieRing V] [LieAlgebra ℝ V]
@[simp] theorem ofReal_lie (X Y : V) : ofReal ⁅X,Y⁆=⁅ofReal X,ofReal Y⁆ := by
  simp [ofReal,LieAlgebra.ExtendScalars.bracket_tmul]

theorem ad_ofReal_baseChange (X : V) :
    LieAlgebra.ad ℂ (ℂ ⊗[ℝ] V) (ofReal X)=
    (LieAlgebra.ad ℝ V X).baseChange ℂ := by
  exact LieModule.toEnd_baseChange ℝ ℂ V V X

theorem ad_ofReal_nilpotent (X : V) (hX : IsNilpotent (LieAlgebra.ad ℝ V X)) :
    IsNilpotent (LieAlgebra.ad ℂ (ℂ ⊗[ℝ] V) (ofReal X)) := by
  rw [ad_ofReal_baseChange]
  exact hX.map (Module.End.baseChangeHom ℝ ℂ V)

end Complexification

open Filter Topology

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_InnerExp
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
open Filter Topology
open Filter Topology
open Filter Topology
open Filter Topology
open Polynomial
open Filter Topology
open scoped TensorProduct
open Set Filter Topology
namespace Release061
namespace Biholomorph
variable {n : ℕ} {U : Set (Affine n)} (hU : IsOpen U) [LocallyCompactSpace U]
    (hc : IsConnected U) (hbd : Bornology.IsBounded U)
    (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
    [MulAction Γ U] [ProperSMul Γ U]
    [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val))

abbrev ComplexGenerators := ℂ ⊗[ℝ] completeGeneratorSpace hU hc hbd Γ hhol

def complexGeneratorField : ComplexGenerators hU hc hbd Γ hhol →ₗ[ℂ] (Affine n → Affine n) :=
  TensorProduct.AlgebraTensorModule.lift
    (LinearMap.toSpanSingleton ℂ _ (completeGeneratorSpace hU hc hbd Γ hhol).subtype)

@[simp] theorem complexGeneratorField_tmul (z : ℂ) (X : completeGeneratorSpace hU hc hbd Γ hhol) :
    complexGeneratorField hU hc hbd Γ hhol (z ⊗ₜ[ℝ] X)=z • X.val := rfl

end Biholomorph
end Release061

open scoped TensorProduct
namespace LieAlgebra
open scoped _root_.LieAlgebra
variable {L : Type*} [LieRing L] [LieAlgebra ℂ L]

def leftInner (T : L) : LieDerivation ℂ L L where
  toLinearMap := LieAlgebra.ad ℂ L T
  leibniz' a b := by
    change ⁅T,⁅a,b⁆⁆=⁅a,⁅T,b⁆⁆-⁅b,⁅T,a⁆⁆
    rw [leibniz_lie,←lie_skew ⁅T,a⁆ b]
    abel

@[simp] theorem leftInner_apply (T X : L) : leftInner T X=⁅T,X⁆ := rfl

@[simp] theorem leftInner_toLinearMap (T : L) :
    (leftInner T).toLinearMap=LieAlgebra.ad ℂ L T := rfl

variable [LieAlgebra ℚ L]

def innerExp (T : L) (hT : IsNilpotent (LieAlgebra.ad ℂ L T)) (c : ℂ) : L ≃ₗ⁅ℂ⁆ L :=
  (c • leftInner T).exp (hT.smul c)

end LieAlgebra

open scoped TensorProduct

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_WeightedUnscaleC1Error
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Metric
open scoped Topology NNReal
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def weightedUnscale (t : ℝ) (x : E × F) : E × F :=
  ((Real.sqrt t)⁻¹ • x.1,t⁻¹ • x.2)

lemma weightedUnscale_scale {t : ℝ} (ht : 0 < t) (x : E × F) :
    weightedUnscale t (weightedScale t x) = x := by
  ext <;> simp [weightedUnscale,weightedScale,ht.ne',(Real.sqrt_pos.mpr ht).ne']

lemma weightedScale_unscale {t : ℝ} (ht : 0 < t) (x : E × F) :
    weightedScale t (weightedUnscale t x) = x := by
  ext <;> simp [weightedUnscale,weightedScale,ht.ne',(Real.sqrt_pos.mpr ht).ne']

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_ModelNormalTranslationAd
attribute [-simp] _root_.OAI.Release061.Biholomorph.ambientMap_apply _root_.OAI.Release061.Biholomorph.complexGeneratorField_tmul _root_.OAI.Release061.Biholomorph.coordinateField_apply _root_.OAI.Release061.Biholomorph.flatTangentialRotation_apply _root_.OAI.Release061.Biholomorph.mapDerivativeEquiv_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
open Filter Topology
namespace Release061
open Set Filter Topology
namespace Biholomorph

def weightedScaleCLE {r k : ℕ} {t : ℝ} (ht : 0<t) :
    (Affine r × Affine k) ≃L[ℂ] (Affine r × Affine k) :=
  ContinuousLinearEquiv.equivOfInverse
    ((Real.sqrt t • ContinuousLinearMap.fst ℂ (Affine r) (Affine k)).prod
      (t • ContinuousLinearMap.snd ℂ (Affine r) (Affine k)))
    (((Real.sqrt t)⁻¹ • ContinuousLinearMap.fst ℂ (Affine r) (Affine k)).prod
      (t⁻¹ • ContinuousLinearMap.snd ℂ (Affine r) (Affine k)))
    (weightedUnscale_scale ht) (weightedScale_unscale ht)

@[simp] theorem weightedScaleCLE_apply {r k : ℕ} {t : ℝ} (ht : 0<t)
    (p : Affine r × Affine k) : weightedScaleCLE ht p=(Real.sqrt t • p.1,t • p.2) := rfl

def flatWeightedScale {r k : ℕ} {t : ℝ} (ht : 0<t) :
    Affine (r+k) ≃L[ℂ] Affine (r+k) :=
  ((affineProductCoordinates r k).symm.trans (weightedScaleCLE ht)).trans
    (affineProductCoordinates r k)

def flatNormalVector (r k : ℕ) (a : Fin k → ℝ) : Affine (r+k) :=
  affineProductCoordinates r k (0,fun i => (a i : ℂ))

 theorem flatNormal_translation_mem {r k : ℕ} (D : Set (Affine r × Affine k))
    (htr : ∀ p : Affine r × Affine k, ∀ a : Fin k → ℝ,
      (p.1,fun i => p.2 i+(a i : ℂ)) ∈ D ↔ p∈D)
    (a : Fin k → ℝ) (t : ℝ) (x : Affine (r+k)) :
    x+t • flatNormalVector r k a∈(affineProductCoordinates r k) '' D ↔
      x∈(affineProductCoordinates r k) '' D := by
  let e : (Affine r × Affine k) ≃L[ℂ] Affine (r+k) := affineProductCoordinates r k
  have hi (y : Affine (r+k)) : y∈e '' D ↔ e.symm y∈D := by
    constructor
    · rintro ⟨p,hp,rfl⟩; simpa only [e.symm_apply_apply] using hp
    · intro h; exact ⟨e.symm y,h,e.apply_symm_apply y⟩
  rw [hi,hi]
  have he : e.symm (x+t • flatNormalVector r k a)=
      ((e.symm x).1,fun i => (e.symm x).2 i+((t*a i : ℝ) : ℂ)) := by
    rw [map_add,show e.symm (t • flatNormalVector r k a)=
      t • e.symm (flatNormalVector r k a) from (e.symm.toContinuousLinearMap.restrictScalars ℝ).map_smul t (flatNormalVector r k a)]
    simp only [flatNormalVector,e,ContinuousLinearEquiv.symm_apply_apply]
    ext i <;> simp [Complex.real_smul]
  rw [he]
  exact htr (e.symm x) (fun i => t*a i)

end Biholomorph
end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_FlatWeightedEuler
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
open Filter Topology
namespace Release061
open Set Filter Topology
namespace Biholomorph

def flatWeightedEuler (r k : ℕ) : Affine (r+k) →L[ℂ] Affine (r+k) :=
  (affineProductCoordinates r k).toContinuousLinearMap.comp
    ((((1/2 : ℂ) • ContinuousLinearMap.fst ℂ (Affine r) (Affine k)).prod
      (ContinuousLinearMap.snd ℂ (Affine r) (Affine k))).comp
      (affineProductCoordinates r k).symm.toContinuousLinearMap)

end Biholomorph
end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_ModelRotationWeight
attribute [-simp] _root_.OAI.Release061.Biholomorph.complexGeneratorField_tmul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
open Filter Topology
open Filter Topology
open Filter Topology
open Filter Topology
open Polynomial
open Filter Topology
namespace Release061
namespace Biholomorph

abbrev ModelIndex (r k : ℕ) := Fin r ⊕ Fin k

def modelBasis (r k : ℕ) : Module.Basis (ModelIndex r k) ℂ (Affine (r+k)) :=
  ((Pi.basisFun ℂ (Fin r)).prod (Pi.basisFun ℂ (Fin k))).map
    (affineProductCoordinates r k).toLinearEquiv

 theorem flatWeightedEuler_normal {r k : ℕ} (a : Fin k → ℝ) :
    flatWeightedEuler r k (flatNormalVector r k a)=flatNormalVector r k a := by
  simp [flatWeightedEuler,flatNormalVector]

end Biholomorph
end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_EulerSpectrum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
open Filter Topology
open Filter Topology
open Filter Topology
open Filter Topology
open Polynomial
open Filter Topology
open scoped TensorProduct
open Set Filter Topology
open scoped TensorProduct
open scoped TensorProduct
open Filter Topology
open Filter Topology
open scoped TensorProduct
namespace Release061.Biholomorph

structure WeightedLieModel (r k : ℕ) (G : Type*) [LieRing G] [LieAlgebra ℝ G] where
  field : (ℂ ⊗[ℝ] G) →ₗ[ℂ] (Affine (r+k) → Affine (r+k))
  normal : Fin k → ℝ
  euler : G
  translation : G
  rotation : G
  analytic : ∀ X, AnalyticAt ℂ (field X) (Complex.I • flatNormalVector r k normal)
  jet_injective : ∀ X, ZeroSecondJet (field X) (Complex.I • flatNormalVector r k normal) → X=0
  lie : ∀ X Y, field ⁅X,Y⁆=VectorField.lieBracket ℂ (field X) (field Y)
  euler_germ : field (Complexification.ofReal euler) =ᶠ[𝓝 (Complex.I • flatNormalVector r k normal)]
    fun x => flatWeightedEuler r k x
  translation_germ : field (Complexification.ofReal translation) =ᶠ[𝓝 (Complex.I • flatNormalVector r k normal)]
    fun _ => flatNormalVector r k normal
  rotation_germ : field (Complexification.ofReal rotation) =ᶠ[𝓝 (Complex.I • flatNormalVector r k normal)]
    fun x => flatTangentialInfinitesimal r k x
  nilpotent : IsNilpotent (LieAlgebra.ad ℝ G translation)
  isotropy_real : ∀ X Y : G,
    field (Complexification.ofReal X) (Complex.I • flatNormalVector r k normal)=0 →
    field (Complexification.ofReal Y) (Complex.I • flatNormalVector r k normal)=0 →
    fderiv ℂ (field (Complexification.ofReal Y)) (Complex.I • flatNormalVector r k normal)=
      Complex.I • fderiv ℂ (field (Complexification.ofReal X)) (Complex.I • flatNormalVector r k normal) → X=0

namespace WeightedLieModel
variable {r k : ℕ} {G : Type*} [LieRing G] [LieAlgebra ℝ G]
    (M : WeightedLieModel r k G)

local instance complexificationRatLieAlgebra : LieAlgebra ℚ (ℂ ⊗[ℝ] G) where
  lie_smul scalar left right := by
    rw [←IsScalarTower.algebraMap_smul ℂ scalar right]
    exact (LieAlgebra.lie_smul (R := ℂ) ((algebraMap ℚ ℂ) scalar) left right).trans
      (IsScalarTower.algebraMap_smul ℂ scalar ⁅left,right⁆)

abbrev point : Affine (r+k) := Complex.I • flatNormalVector r k M.normal
abbrev u : Affine (r+k) := flatNormalVector r k M.normal
abbrev E : ℂ ⊗[ℝ] G := Complexification.ofReal M.euler
abbrev T : ℂ ⊗[ℝ] G := Complexification.ofReal M.translation
abbrev H : ℂ ⊗[ℝ] G := Complexification.ofReal M.rotation

theorem eq_of_germ {X Y : ℂ ⊗[ℝ] G} (h : M.field X =ᶠ[𝓝 M.point] M.field Y) : X=Y := by
  apply sub_eq_zero.mp
  apply M.jet_injective
  have he : M.field (X-Y) =ᶠ[𝓝 M.point] (0 : Affine (r+k) → Affine (r+k)) := by
    filter_upwards [h] with x hx
    simp only [map_sub,Pi.sub_apply,hx,sub_self,Pi.zero_apply]
  apply ZeroSecondJet.congr he.symm
  simp [ZeroSecondJet]

theorem lie_germ {X Y : ℂ ⊗[ℝ] G} {f g : Affine (r+k) → Affine (r+k)}
    (hf : M.field X =ᶠ[𝓝 M.point] f) (hg : M.field Y =ᶠ[𝓝 M.point] g) :
    M.field ⁅X,Y⁆ =ᶠ[𝓝 M.point] VectorField.lieBracket ℂ f g := by
  rw [M.lie]
  filter_upwards [hf.eventually_nhds,hg.eventually_nhds] with x hx hy
  have hx' : M.field X =ᶠ[𝓝 x] f := hx
  have hy' : M.field Y =ᶠ[𝓝 x] g := hy
  simp only [VectorField.lieBracket,hx'.eq_of_nhds,hy'.eq_of_nhds,hx'.fderiv_eq,hy'.fderiv_eq]

theorem translation_euler : ⁅M.T,M.E⁆=M.T := by
  apply M.eq_of_germ
  apply (M.lie_germ M.translation_germ M.euler_germ).trans
  filter_upwards [M.translation_germ] with x hx
  rw [hx,VectorField.lieBracket,(flatWeightedEuler r k).fderiv,fderiv_const_apply]
  simp only [zero_apply,sub_zero,flatWeightedEuler_normal]

def center : (ℂ ⊗[ℝ] G) ≃ₗ⁅ℂ⁆ (ℂ ⊗[ℝ] G) :=
  LieAlgebra.innerExp M.T (Complexification.ad_ofReal_nilpotent M.translation M.nilpotent) (-Complex.I)

end WeightedLieModel
end Release061.Biholomorph

open Filter Topology
open scoped TensorProduct

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_IndependentConormals
attribute [-instance] _root_.OAI.Release061.Biholomorph.automorphismGroup _root_.OAI.Release061.Biholomorph.automorphismInv _root_.OAI.Release061.Biholomorph.automorphismMetrizable _root_.OAI.Release061.Biholomorph.automorphismMul _root_.OAI.Release061.Biholomorph.automorphismOne _root_.OAI.Release061.Biholomorph.automorphismSecondCountable _root_.OAI.Release061.Biholomorph.automorphismTopologicalGroup _root_.OAI.Release061.Biholomorph.automorphismTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Topology MeasureTheory
open scoped Classical

namespace ActualCriticalChart
variable {d N : ℕ} {P : MvPolynomial (Fin N) ℂ} {q : (Fin d → ℝ) → Affine N}

noncomputable def fiberAffine (c : ActualCriticalChart P q) (x : Fin d → ℝ) :
    (Fin c.fiberDim → ℝ) →ᵃ[ℝ] (Affine N →L[ℂ] ℂ) :=
  ((criticalBundleLinear (realCriticalMatrix q) c.split x).inverse.toLinearMap.toAffineMap).comp
    ((AffineMap.const ℝ _ (realCriticalConstant (parameterLogBase P ∘ q) x)).prod (AffineMap.id ℝ _))

noncomputable def ambientCovector (c : ActualCriticalChart P q) (x : Fin d → ℝ) :
    (Fin c.fiberDim → ℝ) →ᵃ[ℝ] Module.Dual ℝ (Affine N) :=
  AffineMap.const ℝ _ (fderiv ℝ (parameterLogBase P) (q x)).toLinearMap +
    ((ContinuousLinearMap.coeLM ℝ).toAffineMap).comp
      (((StrongDual.extendRCLikeL (𝕜 := ℂ) (F := Affine N)).symm.toLinearMap.toAffineMap).comp
        (c.fiberAffine x))

end ActualCriticalChart
end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_ModelComplexField
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
open Filter Topology
open Filter Topology
open Filter Topology
open Filter Topology
open Polynomial
open Filter Topology
open scoped TensorProduct
open Set Filter Topology
open scoped TensorProduct
open scoped TensorProduct
open Filter Topology
open Filter Topology
open scoped TensorProduct
open Filter Topology
open scoped TensorProduct
open scoped TensorProduct
open scoped TensorProduct
open Filter Topology
open scoped TensorProduct
namespace Release061
open Set Filter Topology
open scoped TensorProduct
namespace Biholomorph

section
variable {n m : ℕ} {U : Set (Affine n)} {D : Set (Affine m)}

def coordinateFieldComplexLinear (e : Biholomorph U D) :
    (Affine n → Affine n) →ₗ[ℂ] (Affine m → Affine m) where
  toFun := coordinateField e
  map_add' X Y := (coordinateFieldLinear e).map_add X Y
  map_smul' c X := by
    funext x
    by_cases hx : x∈D
    · simp only [coordinateField,dite_eq_left hx,Pi.smul_apply,map_smul,RingHom.id_apply]
    · simp only [coordinateField,dite_eq_right hx,Pi.smul_apply,smul_zero,RingHom.id_apply]

end

open scoped Classical

end Biholomorph
end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_OneKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
open Filter Topology
open Filter Topology
open Filter Topology
open Filter Topology
open Polynomial
open Filter Topology
open scoped TensorProduct
open Set Filter Topology
open scoped TensorProduct
open scoped TensorProduct
open Filter Topology
open Filter Topology
open scoped TensorProduct
open Filter Topology
open scoped TensorProduct
namespace Release061.Biholomorph.WeightedLieModel
variable {r k : ℕ} {G : Type*} [LieRing G] [LieAlgebra ℝ G]
    (M : WeightedLieModel r k G)

attribute [local instance] complexificationRatLieAlgebra

def jet := analyticSecondJetCoordinates M.field M.point M.analytic (modelBasis r k)
def firstJet := fieldFirstJet M.field M.point M.analytic

theorem bracket_translation_eigen {X : ℂ ⊗[ℝ] G} {μ : ℂ}
    (hX : ⁅M.E,X⁆=μ • X) : ⁅M.E,⁅M.T,X⁆⁆=(μ-1) • ⁅M.T,X⁆ := by
  have het : ⁅M.E,M.T⁆= -M.T := by rw [←lie_skew M.E M.T,M.translation_euler]
  rw [leibniz_lie,het,hX,neg_lie,LieAlgebra.lie_smul μ M.T X,sub_smul,one_smul]
  abel

end Release061.Biholomorph.WeightedLieModel

open scoped TensorProduct

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_RatLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
open Filter Topology
open Filter Topology
open Filter Topology
open Filter Topology
open Polynomial
open Filter Topology
open scoped TensorProduct
open Set Filter Topology
open scoped TensorProduct
open scoped TensorProduct
open Filter Topology

open Filter Topology
open scoped TensorProduct

instance Complexification.ratLieAlgebra {G : Type*} [LieRing G] [LieAlgebra ℝ G] :
    LieAlgebra ℚ (ℂ ⊗[ℝ] G) where
  lie_smul t x y := by
    rw [←IsScalarTower.algebraMap_smul ℂ t y]
    exact (LieAlgebra.lie_smul (R := ℂ) ((algebraMap ℚ ℂ) t) x y).trans
      (IsScalarTower.algebraMap_smul ℂ t ⁅x,y⁆)

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_PositiveReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
open Filter Topology
open Filter Topology
open Filter Topology
open Filter Topology
open Polynomial
open Filter Topology
open scoped TensorProduct
open Set Filter Topology
open scoped TensorProduct
open scoped TensorProduct
open Filter Topology
open Filter Topology
open scoped TensorProduct
open Filter Topology
open scoped TensorProduct
open scoped TensorProduct
namespace Release061.Biholomorph.WeightedLieModel
variable {r k : ℕ} {G : Type*} [LieRing G] [LieAlgebra ℝ G]
    (M : WeightedLieModel r k G)

abbrev grade (μ : ℂ) := (LieAlgebra.ad ℂ (ℂ ⊗[ℝ] G) M.E).eigenspace μ

def lowerHalf : M.grade (1/2) →ₗ[ℂ] M.grade (-(1/2)) where
  toFun X := ⟨⁅M.T,X.val⁆,by
    rw [Module.End.mem_eigenspace_iff]
    have he := M.bracket_translation_eigen (Module.End.mem_eigenspace_iff.mp X.property)
    convert he using 1 <;> norm_num⟩
  map_add' X Y := Subtype.ext (by simp [LieRing.lie_add])
  map_smul' c X := Subtype.ext (by
    change ⁅M.T,c • X.val⁆=c • ⁅M.T,X.val⁆
    exact LieAlgebra.lie_smul c M.T X.val)

def lowerOneSquared : M.grade 1 →ₗ[ℂ] M.grade (-1) where
  toFun X := ⟨⁅M.T,⁅M.T,X.val⁆⁆,by
    rw [Module.End.mem_eigenspace_iff]
    have he := M.bracket_translation_eigen
      (M.bracket_translation_eigen (Module.End.mem_eigenspace_iff.mp X.property))
    convert he using 1 <;> norm_num⟩
  map_add' X Y := Subtype.ext (by simp [LieRing.lie_add])
  map_smul' c X := Subtype.ext (by
    change ⁅M.T,⁅M.T,c • X.val⁆⁆=c • ⁅M.T,⁅M.T,X.val⁆⁆
    rw [LieAlgebra.lie_smul c M.T X.val,LieAlgebra.lie_smul c M.T ⁅M.T,X.val⁆])

end Release061.Biholomorph.WeightedLieModel

open scoped TensorProduct

end

end OAI
end


