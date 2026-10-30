-- Prove2me | Definitions.Def_OAIQ115N006
-- name    : OAIQ115N006
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T00:25:32.700276+00:00
-- url     : https://prove2.me/theorems/79da0d97-8b44-4f80-8f1b-9aec76aca973
-- title:
--   Definitions bundle OAIQ115N006 of the split of OpenAI, A counterexample to Naimark's problem in ZFC
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.NaimarkZFC.main`, carved from OpenAI's openai/math development (OpenAI, *A counterexample to Naimark's problem in ZFC*, OpenAI Math Release, September 24, 2026, result family 297, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 48 declarations of OpenAI's Lean: 1 definition, 4 instances and 43 theorems. The definitions and types are `OAI.NaimarkZFC.KOS.projectionSwitch`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Naimark_Amalgamation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Naimark/Amalgamation.lean), [`Naimark_Basic`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Naimark/Basic.lean), [`Naimark_CAR`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Naimark/CAR.lean), [`Naimark_Dependencies`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Naimark/Dependencies.lean), [`Naimark_DirectLimit`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Naimark/DirectLimit.lean), [`Naimark_HNN`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Naimark/HNN.lean), [`Naimark_Omission`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Naimark/Omission.lean), [`Naimark_Recursion`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Naimark/Recursion.lean), [`Naimark_Representations`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Naimark/Representations.lean), [`Naimark_Stages`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Naimark/Stages.lean).
--
--   **Imports.** It imports the published bundle `Def_Naimark`; the bundles `OAIQ115N000`, `OAIQ115N001`, `OAIQ115N002` and `OAIQ115N003` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ115N008` and `OAIQ115N009`.
-- source:
--   OpenAI, A counterexample to Naimark's problem in ZFC, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 297; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-counterexample-to-Naimarks-problem-in-ZFC-September-24-2026/naimark-counterexample-zfc.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Definitions.Def_Naimark
import Definitions.Def_OAIQ115N000
import Definitions.Def_OAIQ115N001
import Definitions.Def_OAIQ115N002
import Definitions.Def_OAIQ115N003

section
-- module Solutions.OAIQ115_Naimark.Naimark_Basic
attribute [-instance] _root_.OAI.NaimarkZFC.CStarCompletion.instCStarAlgebraCompletionOfCStarRingOfStarModuleComplex_solutions _root_.OAI.NaimarkZFC.CStarCompletion.instNormedAlgebraComplexCompletion_solutions _root_.OAI.NaimarkZFC.CStarCompletion.instStarCompletion_solutions _root_.OAI.NaimarkZFC.CStarCompletion.instStarRingCompletion_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

universe u v w
namespace NaimarkZFC


section GNS

open scoped ComplexOrder InnerProductSpace
open UniformSpace

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem state_contraction_face (f g : A →L[ℂ] ℂ) (hf : IsState f) (hg : IsState g)
    (x : A) (hx : 0 ≤ x) (hn : ‖x‖ ≤ 1) (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hab : a + b = 1) (heq : (a • f + b • g) x = 1) : f x = 1 ∧ g x = 1 := by
  have hfim : (f x).im = 0 := (state_nonneg f hf hx).2.symm
  have hgim : (g x).im = 0 := (state_nonneg g hg hx).2.symm
  have hfr : (f x).re ≤ 1 :=
    (Complex.re_le_norm _).trans ((state_norm_apply_le f hf x).trans hn)
  have hgr : (g x).re ≤ 1 :=
    (Complex.re_le_norm _).trans ((state_norm_apply_le g hg x).trans hn)
  have heqr := congrArg Complex.re heq
  simp only [add_apply, smul_apply, Complex.add_re, Complex.smul_re,
    Complex.one_re, smul_eq_mul] at heqr
  have hfr' : (f x).re = 1 := by nlinarith
  have hgr' : (g x).re = 1 := by nlinarith
  exact ⟨Complex.ext hfr' hfim, Complex.ext hgr' hgim⟩

theorem state_excision_error (f g : A →L[ℂ] ℂ) (hg : IsState g) (a x : A)
    (hx : 0 ≤ x) (hn : ‖x‖ ≤ 1) (hgx : g x = 1) :
    ‖g a - f a‖ ≤ ‖x * (a - f a • (1 : A)) * x‖ := by
  have hcomp := state_compression g hg x hn (IsSelfAdjoint.of_nonneg hx) hgx
  calc
    ‖g a - f a‖ = ‖g (a - f a • (1 : A))‖ := by
      rw [map_sub, map_smul, ((isState_iff g).mp hg).1, smul_eq_mul, mul_one]
    _ = ‖g (x * (a - f a • (1 : A)) * x)‖ := congrArg norm (hcomp _).symm
    _ ≤ ‖x * (a - f a • (1 : A)) * x‖ := state_norm_apply_le g hg _

theorem pure_of_dense_excision (f : A →L[ℂ] ℂ) (hf : IsState f)
    (D : Set A) (hD : Dense D)
    (hexc : ∀ a ∈ D, ∀ ε : ℝ, 0 < ε → ∃ x : A,
      0 ≤ x ∧ ‖x‖ ≤ 1 ∧ f x = 1 ∧ ‖x * (a - f a • (1 : A)) * x‖ < ε) :
    IsPureState f := by
  rw [IsPureState, mem_extremePoints]
  refine ⟨hf, ?_⟩
  intro g hg h hh hseg
  obtain ⟨a, b, ha, hb, hab, heq⟩ := hseg
  have hvals : ∀ z ∈ D, g z = f z ∧ h z = f z := by
    intro z hz
    have hsmall (ε : ℝ) (hε : 0 < ε) : ‖g z - f z‖ < ε ∧ ‖h z - f z‖ < ε := by
      obtain ⟨x, hx, hn, hfx, herr⟩ := hexc z hz ε hε
      have hface := state_contraction_face g h hg hh x hx hn a b ha hb hab
        (by rw [heq]; exact hfx)
      exact ⟨(state_excision_error f g hg z x hx hn hface.1).trans_lt herr,
        (state_excision_error f h hh z x hx hn hface.2).trans_lt herr⟩
    have hg0 : ‖g z - f z‖ ≤ 0 := by
      apply le_of_forall_pos_le_add
      intro ε hε
      simpa only [zero_add] using (hsmall ε hε).1.le
    have hh0 : ‖h z - f z‖ ≤ 0 := by
      apply le_of_forall_pos_le_add
      intro ε hε
      simpa only [zero_add] using (hsmall ε hε).2.le
    exact ⟨eq_of_norm_sub_eq_zero (le_antisymm hg0 (norm_nonneg _)),
      eq_of_norm_sub_eq_zero (le_antisymm hh0 (norm_nonneg _))⟩
  exact ⟨ContinuousLinearMap.ext (congrFun (g.continuous.ext_on hD f.continuous
      (fun z hz => (hvals z hz).1))),
    ContinuousLinearMap.ext (congrFun (h.continuous.ext_on hD f.continuous
      (fun z hz => (hvals z hz).2)))⟩

variable {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

theorem isState_restrict (φ : A →⋆ₐ[ℂ] B) (f : B →L[ℂ] ℂ) (hf : IsState f) :
    IsState (restrictState φ f) := by
  apply (isState_iff _).mpr
  refine ⟨?_, ?_⟩
  · simp only [restrictState_apply, map_one, ((isState_iff f).mp hf).1]
  · intro a
    simpa only [restrictState_apply, map_mul, map_star] using hf.2 (φ a)

omit [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B] in

theorem restrictState_convex (φ : A →⋆ₐ[ℂ] B) (f g : B →L[ℂ] ℂ) (a b : ℝ) :
    restrictState φ (a • f + b • g) = a • restrictState φ f + b • restrictState φ g := by
  ext x
  rfl

theorem unique_lift_pure (φ : A →⋆ₐ[ℂ] B) (f : A →L[ℂ] ℂ) (hf : IsPureState f)
    (F : B →L[ℂ] ℂ) (hF : IsState F) (hres : restrictState φ F = f)
    (hunique : ∀ G : B →L[ℂ] ℂ, IsState G → restrictState φ G = f → G = F) :
    IsPureState F := by
  rw [IsPureState, mem_extremePoints] at hf ⊢
  refine ⟨hF, ?_⟩
  intro G hG H hH hseg
  obtain ⟨a, b, ha, hb, hab, heq⟩ := hseg
  have hseg' : f ∈ openSegment ℝ (restrictState φ G) (restrictState φ H) := by
    refine ⟨a, b, ha, hb, hab, ?_⟩
    rw [← restrictState_convex, heq, hres]
  obtain ⟨hGres, hHres⟩ := hf.2 _ (isState_restrict φ G hG) _
    (isState_restrict φ H hH) hseg'
  exact ⟨hunique G hG hGres, hunique H hH hHres⟩

variable {A : Type u} [CStarAlgebra A]
    {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable [PartialOrder A] [StarOrderedRing A]

variable {A : Type u} [CStarAlgebra A]
    {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem dominatedGNS_intertwines (f g : A →ₚ[ℂ] ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hdom : ∀ a : A, (g (star a * a)).re ≤ C * (f (star a * a)).re) (a : A) :
    (dominatedGNS f g C hC hdom).comp (f.gnsStarAlgHom a) =
      (g.gnsStarAlgHom a).comp (dominatedGNS f g C hC hdom) := by
  apply DFunLike.coe_injective
  apply (gnsVector_cyclic f).equalizer (by fun_prop) (by fun_prop)
  funext b
  change dominatedGNS f g C hC hdom (f.gnsStarAlgHom a (f.gnsStarAlgHom b (gnsVector f))) =
    g.gnsStarAlgHom a (dominatedGNS f g C hC hdom (f.gnsStarAlgHom b (gnsVector f)))
  simp only [gns_apply_vector, gns_apply_coe, dominatedGNS_apply_coe]

end GNS

section WordSpans

open Topology
variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
  (φ : A →⋆ₐ[ℂ] B) (v : Bool → B) (K : Bool → A → Prop)

theorem hnn_kernel_mem_closure_reducedSpan (E : B →L[ℂ] A)
    (hbase : ∀ a, E (φ a) = a)
    (hred : ∀ (w : HNNWord A) (a : A), w.Reduced K → E (φ a*w.eval φ v) = 0)
    (hd : Dense (hnnWordSpan φ v K : Set B)) {x : B} (hx : E x = 0) :
    x ∈ closure (hnnReducedSpan φ v K : Set B) := by
  let P : B →L[ℂ] B := ContinuousLinearMap.id ℂ B - (starAlgHomCLM φ).comp E
  have hP : ∀ y, P y ∈ closure (hnnReducedSpan φ v K : Set B) := by
    intro y
    have hall : closure (hnnWordSpan φ v K : Set B) ⊆
        P ⁻¹' closure (hnnReducedSpan φ v K : Set B) :=
      closure_minimal (fun z hz => subset_closure (hnnWordSpan_center_mem φ v K E hbase hred hz))
        (isClosed_closure.preimage P.continuous)
    exact hall (hd y)
  simpa only [P,sub_apply,ContinuousLinearMap.id_apply,
    ContinuousLinearMap.comp_apply,starAlgHomCLM_apply,hx,map_zero,sub_zero] using hP x

end WordSpans

open Topology
variable {A B C D : Type*} [CStarAlgebra A] [CStarAlgebra B]
  [CStarAlgebra C] [CStarAlgebra D]

theorem hnn_expectation_intertwines
    (φ : A →⋆ₐ[ℂ] B) (ψ : A →⋆ₐ[ℂ] C) (ι : A →⋆ₐ[ℂ] D)
    (v : Bool → B) (w : Bool → C) (F : B →⋆ₐ[ℂ] C)
    (hbase : ∀ a, F (φ a) = ψ a) (hletter : ∀ i, F (v i) = w i)
    (hv : ∀ i, star (v i) = v (!i)) (K : Bool → A → Prop) (center r : Bool → A → A)
    (hc : ∀ i a, K i (center i a))
    (hr : ∀ i a, v i*φ a*v (!i) = v i*φ (center i a)*v (!i) + φ (r i a))
    (E : B →L[ℂ] A) (G : C →L[ℂ] D)
    (hE : ∀ a, E (φ a) = a) (hG : ∀ a, G (ψ a) = ι a)
    (hEr : ∀ (u : HNNWord A) a, u.Reduced K → E (φ a*u.eval φ v) = 0)
    (hGr : ∀ (u : HNNWord A) a, u.Reduced K → G (ψ a*u.eval ψ w) = 0)
    (hd : Dense (StarAlgebra.adjoin ℂ (Set.range φ ∪ Set.range v) : Set B)) (b : B) :
    G (F b) = ι (E b) := by
  have hd' := hnnWordSpan_dense φ v K hv center r hc hr hd
  have hs : ∀ z ∈ hnnWordSpan φ v K, G (F z) = ι (E z) := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      rcases hz with ⟨a,rfl⟩ | ⟨u,a,hu,rfl⟩
      · rw [hbase,hG,hE]
      · rw [map_mul,hbase,HNNWord.eval_hom φ ψ v w F hbase hletter u,
          hGr u a hu,hEr u a hu,map_zero]
    | zero => simp only [map_zero]
    | add x y hx hy ix iy => simp only [map_add,ix,iy]
    | smul c x hx ix => simp only [map_smul,ix]
  exact (isClosed_eq (G.continuous.comp (starAlgHomCLM F).continuous)
    ((starAlgHomCLM ι).continuous.comp E.continuous)).closure_subset_iff.mpr hs (hd' b)

end NaimarkZFC

end

end OAI
end

section
-- module Solutions.OAIQ115_Naimark.Naimark_Representations
attribute [-instance] _root_.OAI.NaimarkZFC.CStarCompletion.instCStarAlgebraCompletionOfCStarRingOfStarModuleComplex_solutions _root_.OAI.NaimarkZFC.CStarCompletion.instNormedAlgebraComplexCompletion_solutions _root_.OAI.NaimarkZFC.CStarCompletion.instStarCompletion_solutions _root_.OAI.NaimarkZFC.CStarCompletion.instStarRingCompletion_solutions _root_.OAI.NaimarkZFC.centeredColumnComplete _root_.OAI.NaimarkZFC.centeredRowComplete _root_.OAI.NaimarkZFC.projectionRowComplete _root_.OAI.NaimarkZFC.traceColumnComplete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace NaimarkZFC

open scoped ComplexStarModule InnerProductSpace
variable {A : Type*} [CStarAlgebra A]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {ι : Type*} [Fintype ι]

open scoped ComplexStarModule CStarAlgebra
variable {A : Type*} [CStarAlgebra A]

open scoped InnerProductSpace ComplexStarModule
variable {A : Type*} [CStarAlgebra A]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

open scoped InnerProductSpace ComplexStarModule
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

open scoped InnerProductSpace ComplexStarModule
variable {A : Type*} [CStarAlgebra A]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

open scoped InnerProductSpace ComplexStarModule
open Filter Topology
variable {A : Type*} [CStarAlgebra A]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

open scoped InnerProductSpace ComplexStarModule CStarAlgebra
variable {A : Type*} [CStarAlgebra A]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem exists_selfAdjoint_operator_vector (d w : H) (hd : d ≠ 0)
    (hw : (⟪d, w⟫_ℂ).im = 0) :
    ∃ T : H →L[ℂ] H, IsSelfAdjoint T ∧ T d = w := by
  let r : ℝ := ‖d‖ ^ 2
  let c : ℝ := (⟪d, w⟫_ℂ).re
  have hr : r ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hd)
  have hdd : ⟪d, d⟫_ℂ = (r : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]
    exact (Complex.ofReal_pow ‖d‖ 2).symm
  have hdw : ⟪d, w⟫_ℂ = (c : ℂ) := Complex.ext rfl hw
  have hwd : ⟪w, d⟫_ℂ = (c : ℂ) := by rw [← inner_conj_symm, hdw]; simp
  let T : H →L[ℂ] H := r⁻¹ • (InnerProductSpace.rankOne ℂ w d +
    InnerProductSpace.rankOne ℂ d w - (c / r) • InnerProductSpace.rankOne ℂ d d)
  refine ⟨T, ?_, ?_⟩
  · change star T = T
    simp only [T, star_smul, star_trivial, star_sub, star_add,
      ContinuousLinearMap.star_eq_adjoint, InnerProductSpace.adjoint_rankOne]
    rw [add_comm]
  · simp only [T, smul_apply, sub_apply, add_apply, InnerProductSpace.rankOne_apply,
      hdd, hwd, Complex.coe_smul, smul_smul, div_mul_cancel₀ c hr,
      add_sub_cancel_right, inv_mul_cancel₀ hr, one_smul]

theorem saCayley_eq (a : A) (ha : IsSelfAdjoint a) :
    saCayley a = saResolvent a (-Complex.I) * (a - Complex.I • (1 : A)) := by
  rw [saCayley, cfc_mul _ _ a
    (saResolvent_continuousOn a ha (-Complex.I) (by simp)) (by fun_prop)]
  rw [cfc_sub _ _ a, cfc_id' ℂ a ha.isStarNormal, cfc_const Complex.I a ha.isStarNormal]
  rw [Algebra.algebraMap_eq_smul_one]
  rfl

theorem saCayley_unitary (a : A) (ha : IsSelfAdjoint a) : saCayley a ∈ unitary A := by
  apply (cfc_unitary_iff _ a ha.isStarNormal
    ((saResolvent_continuousOn a ha (-Complex.I) (by simp)).mul
      (continuous_id.sub continuous_const).continuousOn)).mpr
  intro t ht
  change star ((t - (-Complex.I))⁻¹ * (t - Complex.I)) *
    ((t - (-Complex.I))⁻¹ * (t - Complex.I)) = 1
  have htstar : star t = t := by rw [ha.mem_spectrum_eq_re ht]; simp
  have hp := sa_spectrum_sub_ne_zero a ha Complex.I (by simp) t ht
  have hm := sa_spectrum_sub_ne_zero a ha (-Complex.I) (by simp) t ht
  simp only [star_mul, star_inv₀, star_sub, htstar, star_neg,
    Complex.star_def, Complex.conj_I, neg_neg]
  field_simp [hp, hm]

open scoped InnerProductSpace ComplexStarModule CStarAlgebra ComplexOrder
universe u v w

variable {A : Type*} [CStarAlgebra A]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]

variable [PartialOrder A] [StarOrderedRing A]

open scoped InnerProductSpace ComplexStarModule
variable {A : Type*} [CStarAlgebra A]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

open scoped CStarAlgebra InnerProductSpace ComplexStarModule
open Filter Topology
variable {A : Type*} [CStarAlgebra A]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable [PartialOrder A] [StarOrderedRing A]

open scoped InnerProductSpace ComplexStarModule CStarAlgebra
open Filter Topology
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

open scoped InnerProductSpace ComplexStarModule
open Filter Topology
variable {B : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [StarOrderedRing B] in
theorem approximateUnit_strong
    (ρ : B →⋆ₙₐ[ℂ] (H →L[ℂ] H)) {l : Filter B}
    (hl : IsIncreasingApproximateUnit l)
    (hker : ∀ ξ : H, (∀ b : B, ρ b ξ = 0) → ξ = 0) (ξ : H) :
    Tendsto (fun e : B => ρ e ξ) l (𝓝 ξ) := by
  classical
  let M : Submodule ℂ H :=
    { carrier := {x | Tendsto (fun e : B => ρ e x) l (𝓝 x)}
      zero_mem' := by simpa only [Set.mem_ofPred_eq, map_zero] using (tendsto_const_nhds (x := (0 : H)))
      add_mem' := by
        intro x y hx hy
        simpa only [Set.mem_ofPred_eq, map_add] using hx.add hy
      smul_mem' := by
        intro z x hx
        simpa only [Set.mem_ofPred_eq, map_smul] using hx.const_smul z }
  have hclosed : IsClosed (M : Set H) := by
    let T (e : B) : H →L[ℂ] H := if ‖e‖ ≤ 1 then ρ e else 0
    have hT (e : B) : ‖T e‖ ≤ 1 := by
      dsimp only [T]
      split_ifs with he
      · exact (NonUnitalStarAlgHom.norm_apply_le ρ e).trans he
      · simp
    have hEq : Equicontinuous (fun e x => T e x) :=
      (LipschitzWith.uniformEquicontinuous _ 1
        (fun e => ContinuousLinearMap.lipschitzWith_of_opNorm_le (hT e))).equicontinuous
    have hE (x : H) : (fun e => T e x) =ᶠ[l] (fun e => ρ e x) := by
      filter_upwards [hl.eventually_norm] with e he
      simp only [T, ite_eq_left he]
    have hc := hEq.isClosed_setOfPred_tendsto (l := l) continuous_id
    convert hc using 1
    all_goals try with_reducible_and_instances rfl
    ext x
    exact (tendsto_congr' (hE x)).symm
  have hr (b : B) (x : H) : ρ b x ∈ M := by
    have hc : Continuous (fun b : B => ρ b x) :=
      (ContinuousLinearMap.apply ℂ H x).continuous.comp (map_continuous ρ)
    have ht := (hc.tendsto b).comp (hl.tendsto_mul_right b)
    change Tendsto (fun e => ρ e (ρ b x)) l (𝓝 (ρ b x))
    simpa only [Function.comp_def, map_mul, mul_apply_eq_comp] using ht
  have hbot : Mᗮ = ⊥ := by
    apply (Submodule.eq_bot_iff _).mpr
    intro x hx
    apply hker x
    intro b
    have hh := (M.mem_orthogonal x).mp hx (ρ (star b) (ρ b x)) (hr _ _)
    rw [map_star, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_inner_left] at hh
    exact inner_self_eq_zero.mp hh
  let : IsClosed (M : Set H) := hclosed
  have htop : M = ⊤ := Submodule.orthogonal_eq_bot_iff.mp hbot
  exact show ξ ∈ M from htop ▸ Submodule.mem_top

open scoped InnerProductSpace ComplexStarModule CStarAlgebra ComplexOrder
open Filter Topology
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

open Filter Topology
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

open Filter Topology

namespace ExcisionIndex
variable {B : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
instance instIsDirectedOrder : IsDirectedOrder (ExcisionIndex B) := ⟨by
  intro x y
  obtain ⟨z, hz, hxz, hyz⟩ := CStarAlgebra.directedOn_nonneg_ball
    (A := B) x.val (by simpa using x.property) y.val (by simpa using y.property)
  exact ⟨⟨z, by simpa using hz⟩, hxz, hyz⟩⟩

end ExcisionIndex

open scoped InnerProductSpace ComplexStarModule CStarAlgebra ComplexOrder
open Filter Topology
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

open scoped InnerProductSpace ComplexStarModule
open Filter Topology
variable {B : Type*} [NonUnitalCStarAlgebra B]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

open scoped InnerProductSpace ComplexStarModule CStarAlgebra ComplexOrder
open Filter Topology
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    {ι : Type*} {l : Filter ι}

open scoped ComplexOrder ComplexStarModule
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

open Filter Topology
open scoped ComplexOrder

open Filter Topology
open scoped ComplexOrder ComplexStarModule OnePoint InnerProductSpace
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {p : ℕ → A} {f : A →L[ℂ] ℂ} (hp : Peaks p f) (hp0 : p 0 = 1)
variable (τ : A →L[ℂ] ℂ) (hτ : IsState τ) (hpos : ∀ n, 0 < (τ (peakAtom p n)).re)

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {ι : Type*} {l : Filter ι}

open scoped InnerProductSpace ComplexStarModule CStarAlgebra ComplexOrder
open Filter Topology
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma state_norm_sq_le (τ : A →L[ℂ] ℂ) (hτ : IsState τ) (a : A) :
    ‖τ a‖ ^ 2 ≤ (τ (star a * a)).re := by
  let g := positiveOfSquares τ hτ.2
  have h1 : g 1 = 1 := (isState_iff τ).mp hτ |>.1
  have hv : ‖gnsVector g‖ = 1 := gnsVector_norm_eq_one g h1
  have hc := norm_inner_le_norm (𝕜 := ℂ) (gnsVector g) (g.gnsStarAlgHom a (gnsVector g))
  rw [gnsVector_coefficient, hv, one_mul] at hc
  have hs : ‖g.gnsStarAlgHom a (gnsVector g)‖ ^ 2 = (τ (star a * a)).re := by
    have hh := gnsVector_coefficient g (star a * a)
    rw [map_mul, map_star, mul_apply_eq_comp, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_inner_right] at hh
    calc
      _ = (⟪g.gnsStarAlgHom a (gnsVector g), g.gnsStarAlgHom a (gnsVector g)⟫_ℂ).re :=
        (inner_self_eq_norm_sq (𝕜 := ℂ) _).symm
      _ = _ := congrArg Complex.re hh
  change ‖τ a‖ ≤ _ at hc
  nlinarith [norm_nonneg (τ a), norm_nonneg (g.gnsStarAlgHom a (gnsVector g))]

lemma trace_excision_square_bound (τ : A →L[ℂ] ℂ) (hτ : IsState τ)
    (htr : ∀ a b : A, τ (a*b) = τ (b*a))
    {x q : A} (hx : 0 ≤ x) (hxn : ‖x‖ ≤ 1) (hq : IsStarProjection q) :
    (τ (x*x)).re ≤ (τ q).re + ‖x * (1-q) * x‖ := by
  have hxs := IsSelfAdjoint.of_nonneg hx
  have hxl : x*x ≤ 1 := (positive_contraction_square_le hx hxn).trans
    ((CStarAlgebra.norm_le_one_iff_of_nonneg x hx).mp hxn)
  have hqxx : q*x*x*q ≤ q := by
    have hh := hq.isSelfAdjoint.conjugate_le_conjugate hxl
    simpa only [mul_one, hq.isIdempotentElem.eq, mul_assoc] using hh
  have hmono := (positiveOfSquares τ hτ.2).monotone hqxx
  have hcyc : τ (x*q*x) = τ (q*x*x*q) := by
    have h1 := htr x (q*x)
    have h2 := htr (q*x*x) q
    simp only [mul_assoc] at h1 h2 ⊢
    rw [← mul_assoc q q, hq.isIdempotentElem.eq] at h2
    exact h1.trans h2.symm
  have hsum : τ (x*x) = τ (x*q*x) + τ (x*(1-q)*x) := by
    rw [← map_add]
    congr 1
    noncomm_ring
  rw [hsum, Complex.add_re, hcyc]
  exact add_le_add hmono.1 ((Complex.re_le_norm _).trans
    (state_norm_apply_le τ hτ _))

theorem excision_trace_null_of_small_projections
    {ι : Type*} {l : Filter ι} (x : ι → A) (f : A → ℂ)
    (hx : ∀ i, 0 ≤ x i) (hxn : ∀ i, ‖x i‖ ≤ 1)
    (hexc : ∀ a : A, Tendsto (fun i => x i * (a - f a • (1 : A)) * x i) l (𝓝 0))
    (τ : A →L[ℂ] ℂ) (hτ : IsState τ) (htr : ∀ a b : A, τ (a*b) = τ (b*a))
    (hq : ∀ ε : ℝ, 0 < ε → ∃ q : A, IsStarProjection q ∧ f q = 1 ∧ (τ q).re < ε) :
    Tendsto (fun i => τ (x i)) l (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hδ : 0 < ε^2/2 := by positivity
  obtain ⟨q, hqp, hqf, hqt⟩ := hq (ε^2/2) hδ
  have hs : Tendsto (fun i => x i * (1-q) * x i) l (𝓝 0) := by
    have ht := (hexc q).neg
    have hh (i : ι) : -(x i * (q - 1) * x i) = x i * (1 - q) * x i := by
      noncomm_ring
    simpa only [hqf, one_smul, hh, neg_zero] using ht
  have he : ∀ᶠ i in l, ‖x i * (1-q) * x i‖ < ε^2/2 := by
    simpa only [dist_zero_right] using (Metric.tendsto_nhds.mp hs) _ hδ
  filter_upwards [he] with i hi
  simp only [dist_zero_right, norm_norm]
  have hb := trace_excision_square_bound τ hτ htr (hx i) (hxn i) hqp
  have hc := state_norm_sq_le τ hτ (x i)
  rw [(IsSelfAdjoint.of_nonneg (hx i)).star_eq] at hc
  nlinarith [norm_nonneg (τ (x i))]

open Filter Topology
open scoped ComplexOrder ComplexStarModule InnerProductSpace

end NaimarkZFC

end

end OAI
end

section
-- module Solutions.OAIQ115_Naimark.Naimark_Amalgamation
attribute [-instance] _root_.OAI.NaimarkZFC.CStarCompletion.instCStarAlgebraCompletionOfCStarRingOfStarModuleComplex_solutions _root_.OAI.NaimarkZFC.CStarCompletion.instNormedAlgebraComplexCompletion_solutions _root_.OAI.NaimarkZFC.CStarCompletion.instStarCompletion_solutions _root_.OAI.NaimarkZFC.CStarCompletion.instStarRingCompletion_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace NaimarkZFC

attribute [local instance] Classical.propDecidable

open scoped ComplexOrder InnerProductSpace
open UniformSpace

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

open Filter
open scoped Topology

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

open Filter
open scoped Topology
variable {A V : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

open scoped InnerProductSpace
variable {V : Type*} {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H]

open scoped InnerProductSpace
variable {V A H : Type*} [CStarAlgebra A] [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H]

open scoped InnerProductSpace lp

variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {A V : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

open scoped InnerProductSpace lp
variable {A V : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

open Filter Topology
variable {A V : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

open Filter Topology
open scoped InnerProductSpace lp
variable {A V : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem traceColumn_vacuum_cyclic (τ : A →ₚ[ℂ] ℂ) (hτ : IsTracialPositive τ)
    (q : {q : A // IsStarProjection q}) :
    DenseRange (fun a : A => traceColumnRepresentation τ hτ q a (columnVacuum τ hτ q)) := by
  let P : τ.GNS →L[ℂ] TraceColumn τ hτ q := (gnsRight τ hτ q.1).rangeRestrict
  have hP : Function.Surjective P := by
    rintro ⟨x, y, hy⟩
    exact ⟨y, Subtype.ext hy⟩
  have hd := hP.denseRange.comp
    (Completion.denseRange_coe.comp τ.toPreGNS.surjective.denseRange (Completion.continuous_coe _))
    P.continuous
  have he (a : A) : P (τ.toPreGNS a : τ.GNS) =
      traceColumnRepresentation τ hτ q a (columnVacuum τ hτ q) := by
    apply Subtype.ext
    exact (gnsRight_coe τ hτ q.1 a).trans (columnVacuum_action τ hτ q a).symm
  simpa only [Function.comp_def, he] using hd

theorem traceColumn_unit_cyclic (τ : A →ₚ[ℂ] ℂ) (hτ : IsTracialPositive τ)
    (q : {q : A // IsStarProjection q}) (ht : 0 < (τ q.1).re) :
    DenseRange (fun a : A => traceColumnRepresentation τ hτ q a (columnUnit τ hτ q)) := by
  have hn : (Real.sqrt (τ q.1).re : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr ht).ne'
  have he : Set.range (fun a : A => traceColumnRepresentation τ hτ q a (columnUnit τ hτ q)) =
      Set.range (fun a : A => traceColumnRepresentation τ hτ q a (columnVacuum τ hτ q)) := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      refine ⟨((Real.sqrt (τ q.1).re)⁻¹ : ℂ) • a, ?_⟩
      simp only [columnUnit, map_smul, smul_apply]
    · rintro ⟨a, rfl⟩
      refine ⟨(Real.sqrt (τ q.1).re : ℂ) • a, ?_⟩
      simp only [columnUnit, map_smul, smul_apply, smul_smul,
        inv_mul_cancel₀ hn, one_smul]
  change Dense (Set.range _)
  rw [he]
  exact traceColumn_vacuum_cyclic τ hτ q

attribute [local instance] Classical.propDecidable

open scoped InnerProductSpace ENNReal lp

open scoped InnerProductSpace ENNReal lp

open scoped InnerProductSpace ENNReal lp

open scoped InnerProductSpace lp

open scoped InnerProductSpace lp

open scoped InnerProductSpace ComplexOrder

open Filter Topology
open scoped lp

open scoped InnerProductSpace

open scoped InnerProductSpace

open scoped InnerProductSpace

open scoped CStarAlgebra

open scoped ComplexOrder CStarAlgebra

open scoped CStarAlgebra

open scoped ComplexOrder CStarAlgebra

open scoped ComplexOrder CStarAlgebra

open scoped ComplexOrder CStarAlgebra

end NaimarkZFC

end

end OAI
end

section
-- module Solutions.OAIQ115_Naimark.Naimark_DirectLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open UniformSpace Topology
namespace NaimarkZFC
section DirectLimit
universe u v
variable {I : Type u} [Preorder I] [IsDirectedOrder I] [Nonempty I]
  (A : I → Type v) [∀ i, CStarAlgebra (A i)]
  (f : ∀ i j, i ≤ j → A i →⋆ₐ[ℂ] A j)
  [DirectedSystem A (f · · ·)]

variable [IsometricStarSystem A f]

theorem directLimitInclude_isometry (i : I) : Isometry (directLimitInclude A f i) := by
  apply AddMonoidHomClass.isometry_of_norm
  intro a
  exact directLimit_norm_mk A f i a

end DirectLimit

section Completion
universe u v w
variable {I : Type u} [Preorder I] [IsDirectedOrder I] [Nonempty I]
  (A : I → Type v) [∀ i, CStarAlgebra (A i)]
  (f : ∀ i j, i ≤ j → A i →⋆ₐ[ℂ] A j)
  [DirectedSystem A (f · · ·)] [IsometricStarSystem A f]

theorem cstarDirectLimitInclude_isometry (i : I) :
    Isometry (cstarDirectLimitInclude A f i) :=
  (CStarCompletion.include_isometry _).comp (directLimitInclude_isometry A f i)

theorem cstarDirectLimitInclude_dense :
    Dense (⋃ i, Set.range (cstarDirectLimitInclude A f i)) := by
  apply (CStarCompletion.include_dense (DirectLimit A f)).mono
  rintro x ⟨a,rfl⟩
  induction a using DirectLimit.induction f with
  | ih i a => exact Set.mem_iUnion.mpr ⟨i,a,rfl⟩

theorem cstarDirectLimit_induction {P : CStarDirectLimit A f → Prop}
    (hP : IsClosed {x | P x})
    (hs : ∀ i a, P (cstarDirectLimitInclude A f i a)) (x) : P x := by
  have h := cstarDirectLimitInclude_dense A f x
  exact (closure_minimal (by
    intro y hy
    obtain ⟨i,a,rfl⟩ := Set.mem_iUnion.mp hy
    exact hs i a) hP) h

end Completion
end NaimarkZFC

end

end OAI
end

section
-- module Solutions.OAIQ115_Naimark.Naimark_HNN
attribute [-instance] _root_.OAI.NaimarkZFC.CStarCompletion.instCStarAlgebraCompletionOfCStarRingOfStarModuleComplex_solutions _root_.OAI.NaimarkZFC.CStarCompletion.instNormedAlgebraComplexCompletion_solutions _root_.OAI.NaimarkZFC.CStarCompletion.instStarCompletion_solutions _root_.OAI.NaimarkZFC.CStarCompletion.instStarRingCompletion_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace NaimarkZFC

open scoped CStarAlgebra ComplexOrder

open scoped CStarAlgebra Matrix

open scoped CStarAlgebra

open scoped CStarAlgebra ComplexOrder

open scoped CStarAlgebra ComplexOrder

open scoped CStarAlgebra ComplexOrder

open scoped CStarAlgebra

open scoped InnerProductSpace lp

open scoped CStarAlgebra ComplexOrder

open scoped CStarAlgebra ComplexOrder

open scoped CStarAlgebra ComplexOrder

open scoped CStarAlgebra ComplexOrder

open scoped CStarAlgebra

open scoped CStarAlgebra ComplexOrder

open Topology
open scoped CStarAlgebra ComplexOrder

open Topology
open scoped CStarAlgebra ComplexOrder

open scoped CStarAlgebra ComplexOrder InnerProductSpace ComplexStarModule

open scoped CStarAlgebra ComplexOrder

open Filter Topology
open scoped CStarAlgebra ComplexOrder InnerProductSpace

open Filter Topology
open scoped CStarAlgebra ComplexOrder

open Filter Topology
open scoped CStarAlgebra ComplexOrder InnerProductSpace

open Filter Topology
open scoped CStarAlgebra ComplexOrder

open scoped CStarAlgebra ComplexOrder InnerProductSpace ComplexStarModule

open Filter Topology
open scoped CStarAlgebra ComplexOrder InnerProductSpace

open scoped CStarAlgebra ComplexOrder

open scoped CStarAlgebra ComplexOrder InnerProductSpace

open scoped CStarAlgebra ComplexOrder InnerProductSpace

open scoped CStarAlgebra ComplexOrder

open scoped ComplexOrder

open scoped CStarAlgebra ComplexOrder

open scoped CStarAlgebra ComplexOrder InnerProductSpace
open UniformSpace

open scoped CStarAlgebra ComplexOrder

open scoped CStarAlgebra ComplexOrder

open scoped CStarAlgebra ComplexOrder

open scoped CStarAlgebra ComplexOrder

open scoped CStarAlgebra ComplexOrder

open Topology

open scoped CStarAlgebra ComplexOrder

open Topology

open Topology

open Topology

open Filter Topology
open scoped InnerProductSpace ComplexOrder ComplexStarModule CStarAlgebra
section
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [PartialOrder A] [StarOrderedRing A] in

theorem mixed_zero_of_state_cross_decay {ι : Type*} {l : Filter ι} [l.NeBot]
    (f g : A →L[ℂ] ℂ) (x y : ι → A)
    (hx : ∀ i, IsSelfAdjoint (x i)) (hxn : ∀ i, ‖x i‖ ≤ 1) (hyn : ∀ i, ‖y i‖ ≤ 1)
    (hxv : ∀ i, f (x i) = 1) (hyv : ∀ i, g (y i) = 1)
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (ξ η : H) (hξ : ‖ξ‖ = 1) (hη : ‖η‖ = 1)
    (hcξ : ∀ a, ⟪ξ,π a ξ⟫_ℂ = f a) (hcη : ∀ a, ⟪η,π a η⟫_ℂ = g a)
    (a : A) (hdec : Tendsto (fun i => x i*a*y i) l (𝓝 0)) :
    ⟪ξ,π a η⟫_ℂ = 0 := by
  let L : A →L[ℂ] ℂ := (innerSL ℂ ξ).comp (orbitCLM π η)
  have he (i) : L (x i*a*y i) = L a :=
    representation_coefficient_compression π ξ η _ _ _ (hx i)
      (representation_fix_of_coefficient_one π ξ hξ _ (hxn i) ((hcξ _).trans (hxv i)))
      (representation_fix_of_coefficient_one π η hη _ (hyn i) ((hcη _).trans (hyv i)))
  have ht : Tendsto (fun _ : ι => L a) l (𝓝 0) := by
    simpa only [Function.comp_def,he,map_zero] using (L.continuous.tendsto 0).comp hdec
  exact tendsto_nhds_unique tendsto_const_nhds ht

end

open Topology

open scoped CStarAlgebra ComplexOrder

open Filter Topology
open scoped CStarAlgebra ComplexOrder

open Topology
open scoped CStarAlgebra ComplexOrder

open Topology
open scoped CStarAlgebra ComplexOrder

open Filter Topology
open scoped CStarAlgebra ComplexOrder OnePoint

open Topology

end NaimarkZFC

end

end OAI
end

section
-- module Solutions.OAIQ115_Naimark.Naimark_CAR
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace NaimarkZFC

open scoped CStarAlgebra

instance carStageNontrivial : ∀ n, Nontrivial (CARStage n)
  | 0 => inferInstanceAs (Nontrivial ℂ)
  | n+1 => by
    let := carStageNontrivial n
    exact inferInstanceAs (Nontrivial (CStarMatrix Bool Bool (CARStage n)))

instance carStageSimple : ∀ n, IsSimpleRing (CARStage n)
  | 0 => inferInstanceAs (IsSimpleRing ℂ)
  | n+1 => by
    let := carStageSimple n
    change IsSimpleRing (Matrix Bool Bool (CARStage n))
    infer_instance

open scoped ComplexOrder CStarAlgebra

instance carStageFinite : ∀ n, Module.Finite ℂ (CARStage n)
  | 0 => inferInstanceAs (Module.Finite ℂ ℂ)
  | n+1 => by
    let := carStageFinite n
    change Module.Finite ℂ (Matrix Bool Bool (CARStage n))
    infer_instance

theorem carStage_finrank (n : ℕ) : Module.finrank ℂ (CARStage n) = 4^n := by
  induction n with
  | zero => exact Module.finrank_self ℂ
  | succ n ih =>
    change Module.finrank ℂ (Matrix Bool Bool (CARStage n)) = _
    rw [Module.finrank_matrix,ih]
    simp [pow_succ]
    omega

open scoped ComplexOrder CStarAlgebra

open scoped ComplexOrder CStarAlgebra

open scoped ComplexOrder CStarAlgebra

open scoped ComplexOrder CStarAlgebra

open Filter Topology
open scoped ComplexOrder CStarAlgebra

end NaimarkZFC

end

end OAI
end

section
-- module Solutions.OAIQ115_Naimark.Naimark_Dependencies
attribute [-instance] _root_.OAI.NaimarkZFC.constructionIndex_noMax _root_.OAI.NaimarkZFC.constructionIndex_nonempty _root_.OAI.NaimarkZFC.constructionIndex_orderBot
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace NaimarkZFC

open Topology
section
variable {A ι : Type*} [CStarAlgebra A]

theorem generatedFamily_separable (base : Set A) (v : ι → A)
    (hbase : TopologicalSpace.IsSeparable base) {S : Set ι} (hS : S.Countable) :
    TopologicalSpace.IsSeparable (generatedFamily base v S : Set A) :=
  (separable_starAdjoin _ (hbase.union (hS.image v).isSeparable)).closure

theorem starAdjoin_countable_support (base : Set A) (v : ι → A) (T : Set ι)
    {a : A} (ha : a ∈ StarAlgebra.adjoin ℂ (base ∪ v '' T)) :
    ∃ S : Set ι, S.Countable ∧ S ⊆ T ∧ a ∈ generatedFamily base v S := by
  induction ha using StarAlgebra.adjoin_induction with
  | mem x hx =>
    rcases hx with hx | ⟨j,hj,rfl⟩
    · exact ⟨∅,Set.countable_empty,Set.empty_subset _,generatedFamily_contains_base base v ∅ hx⟩
    · exact ⟨{j},Set.countable_singleton _,Set.singleton_subset_iff.mpr hj,
        generatedFamily_contains base v (Set.mem_singleton j)⟩
  | algebraMap r =>
    exact ⟨∅,Set.countable_empty,Set.empty_subset _,(generatedFamily base v ∅).algebraMap_mem r⟩
  | add x y hx hy ix iy =>
    obtain ⟨S,hSc,hST,hS⟩ := ix
    obtain ⟨R,hRc,hRT,hR⟩ := iy
    exact ⟨S ∪ R,hSc.union hRc,Set.union_subset hST hRT,
      (generatedFamily base v (S ∪ R)).add_mem
        (generatedFamily_mono base v Set.subset_union_left hS)
        (generatedFamily_mono base v Set.subset_union_right hR)⟩
  | mul x y hx hy ix iy =>
    obtain ⟨S,hSc,hST,hS⟩ := ix
    obtain ⟨R,hRc,hRT,hR⟩ := iy
    exact ⟨S ∪ R,hSc.union hRc,Set.union_subset hST hRT,
      (generatedFamily base v (S ∪ R)).mul_mem
        (generatedFamily_mono base v Set.subset_union_left hS)
        (generatedFamily_mono base v Set.subset_union_right hR)⟩
  | star x hx ix =>
    obtain ⟨S,hSc,hST,hS⟩ := ix
    exact ⟨S,hSc,hST,star_mem hS⟩

theorem generatedFamily_countable_support (base : Set A) (v : ι → A) (T : Set ι)
    {a : A} (ha : a ∈ generatedFamily base v T) :
    ∃ S : Set ι, S.Countable ∧ S ⊆ T ∧ a ∈ generatedFamily base v S := by
  obtain ⟨u,hu,hlim⟩ := mem_closure_iff_seq_limit.mp ha
  choose S hSc hST hS using fun n => starAdjoin_countable_support base v T (hu n)
  refine ⟨⋃ n, S n,Set.countable_iUnion hSc,Set.iUnion_subset hST,?_⟩
  apply (generatedFamily_isClosed base v (⋃ n, S n)).mem_of_tendsto hlim
  exact Filter.Eventually.of_forall fun n =>
    generatedFamily_mono base v (Set.subset_iUnion S n) (hS n)

theorem generatedFamily_iUnion (base : Set A) (v : ι → A) (N : ℕ → Set ι)
    (hN : Monotone N) :
    (generatedFamily base v (⋃ n, N n) : Set A) ⊆
      closure (⋃ n, (generatedFamily base v (N n) : Set A)) := by
  let C : StarSubalgebra ℂ A := (⨆ n, generatedFamily base v (N n)).topologicalClosure
  have hd : Directed (· ≤ ·) (fun n => generatedFamily base v (N n)) :=
    ((generatedFamily_mono base v).comp hN).directed_le
  have hcoe : (C : Set A) = closure (⋃ n, (generatedFamily base v (N n) : Set A)) := by
    change closure (((⨆ n, generatedFamily base v (N n)) : StarSubalgebra ℂ A) : Set A) = _
    rw [StarSubalgebra.coe_iSup_of_directed hd]
  rw [← hcoe]
  change generatedFamily base v (⋃ n, N n) ≤ C
  apply StarSubalgebra.topologicalClosure_minimal _ (show IsClosed (C : Set A) from isClosed_closure)
  apply StarAlgebra.adjoin_le
  intro x hx
  rcases hx with hx | ⟨j,hj,rfl⟩
  · exact subset_closure ((le_iSup (fun n => generatedFamily base v (N n)) 0)
      (generatedFamily_contains_base base v (N 0) hx))
  · obtain ⟨n,hn⟩ := Set.mem_iUnion.mp hj
    exact subset_closure ((le_iSup (fun n => generatedFamily base v (N n)) n)
      (generatedFamily_contains base v hn))

end

open Filter Topology
open scoped CStarAlgebra ComplexOrder InnerProductSpace

section
variable {ι : Type*}

theorem dependencyClosure_closed (I : ι → Set ι) (S : Set ι) :
    DependencyClosed I (dependencyClosure I S) := by
  intro j hj k hk
  obtain ⟨n,hn⟩ := Set.mem_iUnion.mp hj
  apply Set.mem_iUnion.mpr
  refine ⟨n+1,?_⟩
  rw [Function.iterate_succ_apply']
  exact Or.inr (Set.mem_iUnion.mpr ⟨j,Set.mem_iUnion.mpr ⟨hn,hk⟩⟩)

theorem DependencyClosed.iUnion {I : ι → Set ι} {κ : Type*} {S : κ → Set ι}
    (h : ∀ k, DependencyClosed I (S k)) : DependencyClosed I (⋃ k, S k) := by
  intro j hj l hl
  obtain ⟨k,hk⟩ := Set.mem_iUnion.mp hj
  exact Set.mem_iUnion.mpr ⟨k,h k j hk hl⟩

end

open Topology
section
variable {ι X : Type*} [PseudoMetricSpace X]

theorem countable_witness_closure
    (I : ι → Set ι) (hI : ∀ j, (I j).Countable)
    (B : Set ι → Set X) (hmono : Monotone B)
    (hsep : ∀ S, S.Countable → TopologicalSpace.IsSeparable (B S))
    (hsupp : ∀ x, ∃ S, S.Countable ∧ x ∈ B S)
    (hlim : ∀ N : ℕ → Set ι, Monotone N →
      B (⋃ n, N n) ⊆ closure (⋃ n, B (N n)))
    (w : X → ℕ → X) :
    ∃ S : Set ι, S.Countable ∧ DependencyClosed I S ∧
      ∃ D : Set X, D.Countable ∧ D ⊆ B S ∧ B S ⊆ closure D ∧
        ∀ a ∈ D, ∀ m, w a m ∈ B S := by
  classical
  choose supp hsuppc hsuppmem using hsupp
  have hex D (hD : D.Countable) := (hsep D hD).exists_countable_dense_subset
  choose d hdsub hdc hddense using hex
  let C := {S : Set ι // S.Countable ∧ DependencyClosed I S}
  let add (S : C) : Set ι := S.1 ∪ ⋃ a ∈ d S.1 S.2.1, ⋃ m : ℕ, supp (w a m)
  have hadd (S : C) : (add S).Countable :=
    S.2.1.union ((hdc S.1 S.2.1).biUnion (fun a _ => Set.countable_iUnion (fun m => hsuppc (w a m))))
  let step (S : C) : C := ⟨dependencyClosure I (add S),
    dependencyClosure_countable I hI (hadd S),dependencyClosure_closed I (add S)⟩
  have hstep (S : C) : S.1 ⊆ (step S).1 :=
    Set.subset_union_left.trans (subset_dependencyClosure I (add S))
  let N : ℕ → C := fun n => step^[n] ⟨∅,Set.countable_empty,by intro j hj; exact hj.elim⟩
  have hNsucc (n : ℕ) : N (n+1) = step (N n) := by
    exact Function.iterate_succ_apply' step n _
  have hNmono : Monotone (fun n => (N n).1) := monotone_nat_of_le_succ (fun n => by
    rw [hNsucc]; exact hstep (N n))
  let S : Set ι := ⋃ n, (N n).1
  let D : Set X := ⋃ n, d (N n).1 (N n).2.1
  have hNS (n : ℕ) : (N n).1 ⊆ S := by
    intro j hj
    exact Set.mem_iUnion.mpr ⟨n,hj⟩
  refine ⟨S,Set.countable_iUnion (fun n => (N n).2.1),
    DependencyClosed.iUnion (fun n => (N n).2.2),D,
    Set.countable_iUnion (fun n => hdc (N n).1 (N n).2.1),?_,?_,?_⟩
  · intro a ha
    obtain ⟨n,hn⟩ := Set.mem_iUnion.mp ha
    exact hmono (hNS n) (hdsub (N n).1 (N n).2.1 hn)
  · apply (hlim _ hNmono).trans
    apply closure_minimal _ isClosed_closure
    intro a ha
    obtain ⟨n,hn⟩ := Set.mem_iUnion.mp ha
    exact closure_mono (Set.subset_iUnion _ n) (hddense (N n).1 (N n).2.1 hn)
  · intro a ha m
    obtain ⟨n,hn⟩ := Set.mem_iUnion.mp ha
    apply hmono (hNS (n+1))
    rw [hNsucc]
    apply hmono (subset_dependencyClosure I (add (N n)))
    apply hmono (show supp (w a m) ⊆ add (N n) from ?_)
    · exact hsuppmem (w a m)
    · intro j hj
      exact Or.inr (Set.mem_iUnion.mpr ⟨a,Set.mem_iUnion.mpr ⟨hn,
        Set.mem_iUnion.mpr ⟨m,hj⟩⟩⟩)

end

open Topology
open scoped CStarAlgebra ComplexOrder

open scoped ComplexOrder CStarAlgebra

open scoped ComplexOrder CStarAlgebra InnerProductSpace
section
universe u v w
variable {A : Type u} [CStarAlgebra A]
    {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {K : Type w} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem UnitarilyEquivalent.isIrreducible
    {π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)} {ρ : A →⋆ₙₐ[ℂ] (K →L[ℂ] K)}
    (he : UnitarilyEquivalent π ρ) (hπ : IsIrreducible π) : IsIrreducible ρ := by
  obtain ⟨U,hU⟩ := he
  refine ⟨?_,fun M hM hinv => ?_⟩
  · intro hz
    apply hπ.1
    ext a x
    apply U.injective
    simpa only [hz,NonUnitalStarAlgHom.zero_apply,zero_apply,map_zero] using hU a x
  · let N : Submodule ℂ H := M.comap U.toLinearEquiv.toLinearMap
    have hN : IsClosed (N : Set H) := hM.preimage U.continuous
    have hNi (a : A) (x : H) (hx : x ∈ N) : π a x ∈ N := by
      change U (π a x) ∈ M
      rw [hU]
      exact hinv a (U x) hx
    rcases hπ.2 N hN hNi with hb | ht
    · left
      apply bot_unique
      intro y hy
      change y = 0
      have hx : U.symm y ∈ N := by
        change U (U.symm y) ∈ M
        simpa only [U.apply_symm_apply] using hy
      have hz : U.symm y = 0 := by simpa only [hb,Submodule.mem_bot] using hx
      rw [← U.apply_symm_apply y,hz,map_zero]
    · right
      apply top_unique
      intro y _
      have hx : U.symm y ∈ N := by rw [ht]; trivial
      change U (U.symm y) ∈ M at hx
      simpa only [U.apply_symm_apply] using hx

end

open Filter Topology
open scoped CStarAlgebra

open Topology
open scoped CStarAlgebra ComplexOrder

open Filter Topology

open Filter Topology

open Filter Topology
open scoped InnerProductSpace ComplexStarModule CStarAlgebra

open Filter Topology
open scoped InnerProductSpace

open Topology
section
variable {A ι κ : Type*} [CStarAlgebra A]

universe u

theorem generatedFamily_ordinal_continuous (base : Set A) (v : Ordinal.{u} → A)
    (S : Set Ordinal.{u}) (j : Ordinal.{u}) (hj : Order.IsSuccLimit j) :
    (generatedFamily base v (S ∪ Set.Iio j) : Set A) =
      closure (⋃ k : {k : Ordinal.{u} // k < j},
        (generatedFamily base v (S ∪ Set.Iio k.val) : Set A)) := by
  let K := {k : Ordinal.{u} // k < j}
  have h0 : (0 : Ordinal.{u}) < j := hj.ne_bot.bot_lt
  let : Nonempty K := ⟨⟨0,h0⟩⟩
  have hd : Directed (· ⊆ ·) (fun k : K => S ∪ Set.Iio k.val) := by
    intro k l
    refine ⟨⟨max k.val l.val,max_lt k.property l.property⟩,?_,?_⟩
    · apply Set.union_subset_union_right
      intro x hx
      change x < max k.val l.val
      exact lt_of_lt_of_le hx (le_max_left k.val l.val)
    · apply Set.union_subset_union_right
      intro x hx
      change x < max k.val l.val
      exact lt_of_lt_of_le hx (le_max_right k.val l.val)
  have he : (⋃ k : K, S ∪ Set.Iio k.val) = S ∪ Set.Iio j := by
    ext x
    constructor
    · intro hx
      obtain ⟨k,hk⟩ := Set.mem_iUnion.mp hx
      rcases hk with hs | hx
      · exact Or.inl hs
      · exact Or.inr (hx.trans k.property)
    · intro hx
      rcases hx with hs | hx
      · exact Set.mem_iUnion.mpr ⟨⟨0,h0⟩,Or.inl hs⟩
      · exact Set.mem_iUnion.mpr ⟨⟨Order.succ x,hj.succ_lt hx⟩,Or.inr (Order.lt_succ x)⟩
  rw [← he]
  exact generatedFamily_iUnion_directed base v _ hd

end

open Topology
section
attribute [local instance] generatedFamily_isClosed
universe u
variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (base : Set A) (v : Ordinal.{u} → A) (S : Set Ordinal.{u})

attribute [local instance] OAI.NaimarkZFC.retainedOrdinalAlgebra_order
attribute [local instance] OAI.NaimarkZFC.retainedOrdinalAlgebra_starOrder
omit [PartialOrder A] [StarOrderedRing A] in
theorem retainedOrdinalInclusion_continuous (j : Ordinal.{u}) (hj : Order.IsSuccLimit j) :
    Dense (⋃ k : {k : Ordinal.{u} // k < j},
      Set.range (retainedOrdinalInclusion base v S k.property.le)) :=
  dense_iUnion_starSubalgebra_inclusions _ _ _ (generatedFamily_ordinal_continuous base v S j hj)

omit [PartialOrder A] [StarOrderedRing A] in
theorem retainedOrdinalInclusion_refl (j : Ordinal.{u}) :
    retainedOrdinalInclusion base v S (le_refl j) =
      StarAlgHom.id ℂ (retainedOrdinalAlgebra base v S j) := by
  ext x
  rfl

end

open scoped InnerProductSpace ComplexStarModule CStarAlgebra

end NaimarkZFC

end

end OAI
end

section
-- module Solutions.OAIQ115_Naimark.Naimark_Stages
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace NaimarkZFC

open Topology

open scoped CStarAlgebra ComplexOrder

open scoped InnerProductSpace

open scoped InnerProductSpace

open scoped InnerProductSpace

open scoped InnerProductSpace ComplexStarModule CStarAlgebra

open scoped InnerProductSpace
namespace KOS
variable {A : Type*} [CStarAlgebra A]

def projectionSwitch (a : A) : A := (-Complex.I) • saCayley (a+a-1)

end KOS

open scoped InnerProductSpace

open scoped InnerProductSpace
namespace KOS
variable {A : Type*} [CStarAlgebra A]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {ι : Type*} [Fintype ι]

lemma rowAverage_apply_one (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hπ : IsIrreducible π)
    (x : ι → A) (v : H) :
    π (rowAverage x 1) v = ∑ i, π (x i) (π (star (x i)) v) := by
  simp only [rowAverage_apply,irreducible_map_one π hπ,one_apply_eq_self]

lemma rowAverage_error (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hπ : IsIrreducible π)
    (x : ι → A) (a : A) (v : H) (ε : ℝ)
    (he : ∀ i, ‖π a (π (star (x i)) v) - π (star (x i)) v‖ ≤ ε) :
    ‖π (rowAverage x a) v - π (rowAverage x 1) v‖ ≤ (∑ i, ‖x i‖)*ε := by
  rw [rowAverage_apply,rowAverage_apply_one π hπ,← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i, ‖π (x i) (π a (π (star (x i)) v)-π (star (x i)) v)‖ := by
      simpa only [map_sub] using norm_sum_le Finset.univ
        (fun i => π (x i) (π a (π (star (x i)) v))-π (x i) (π (star (x i)) v))
    _ ≤ ∑ i, ‖x i‖*ε := by
      apply Finset.sum_le_sum
      intro i _
      exact ((π (x i)).le_opNorm _).trans
        (mul_le_mul (NonUnitalStarAlgHom.norm_apply_le π _) (he i) (norm_nonneg _) (norm_nonneg _))
    _ = _ := Finset.sum_mul _ _ _ |>.symm

end KOS

open scoped InnerProductSpace ComplexStarModule

open scoped InnerProductSpace
namespace KOS
variable {A : Type*} [CStarAlgebra A] [partialOrderA : PartialOrder A] [starOrderedRingA : StarOrderedRing A]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {ι : Type*} [Fintype ι]

omit partialOrderA starOrderedRingA in
lemma rowAverage_pair_error_approx [PartialOrder A] [StarOrderedRing A]
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hπ : IsIrreducible π)
    (x : ι → A) (a : A) (ξ η : H) (ε : ℝ)
    (hd : ∀ i, ‖π a (π (star (x i)) ξ-π (star (x i)) η)-
      (π (star (x i)) ξ-π (star (x i)) η)‖ ≤ ε)
    (hs : ∀ i, ‖π a (π (star (x i)) ξ+π (star (x i)) η)‖ ≤ ε) :
    ‖π (rowAverage x a) (ξ-η)-(ξ-η)‖ + ‖π (rowAverage x a) (ξ+η)‖ ≤
      2*(∑ i, ‖x i‖)*ε + ‖π (rowAverage x 1) ξ-ξ‖ +
        ‖π (rowAverage x 1) η-η‖ := by
  have hd' := rowAverage_error π hπ x a (ξ-η) ε (by simpa only [map_sub] using hd)
  have hs' := rowAverage_small π x a (ξ+η) ε (by simpa only [map_add] using hs)
  have hb : ‖π (rowAverage x 1) (ξ-η)-(ξ-η)‖ ≤
      ‖π (rowAverage x 1) ξ-ξ‖ + ‖π (rowAverage x 1) η-η‖ := by
    rw [map_sub]
    calc
      _ = ‖(π (rowAverage x 1) ξ-ξ)-(π (rowAverage x 1) η-η)‖ := by congr 1; abel
      _ ≤ _ := norm_sub_le _ _
  have hn := norm_sub_le_norm_sub_add_norm_sub (π (rowAverage x a) (ξ-η))
    (π (rowAverage x 1) (ξ-η)) (ξ-η)
  linarith

end KOS

open scoped InnerProductSpace

open scoped InnerProductSpace

open scoped InnerProductSpace CStarAlgebra

open scoped InnerProductSpace

open scoped InnerProductSpace

open scoped InnerProductSpace

end NaimarkZFC

end

end OAI
end

section
-- module Solutions.OAIQ115_Naimark.Naimark_Omission
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace NaimarkZFC

open Topology
open scoped CStarAlgebra ComplexOrder

open Topology
open scoped CStarAlgebra ComplexOrder

open Topology

open Topology
open scoped CStarAlgebra ComplexOrder

open Topology

open Topology

open Topology

open Topology

open Topology

open Topology

open Topology

section
open Topology
universe u
attribute [local instance] generatedFamily_isClosed
variable {A : Type} [CStarAlgebra A]

lemma retainedOrdinal_endpoint (base : Set A) (v : Ordinal.{u} → A)
    (S : Set Ordinal.{u}) (δ : Ordinal.{u}) (hS : S ⊆ Set.Iio δ) :
    retainedOrdinalAlgebra base v S δ = generatedFamily base v (Set.Iio δ) := by
  apply congrArg (generatedFamily base v)
  exact Set.union_eq_right.mpr hS

end

open Topology

open Topology

open Topology

open Topology

open Topology
section
universe u v
attribute [local instance] generatedFamily_isClosed
variable {A : Type} [CStarAlgebra A]

lemma generatedFamily_map {B : Type*} [CStarAlgebra B] {J : Type*}
    (base : Set A) (z : J → A) (S : Set J) (φ : A →⋆ₐ[ℂ] B)
    (hφ : Function.Injective φ) :
    (generatedFamily base z S).map φ = generatedFamily (φ '' base) (φ ∘ z) S := by
  rw [generatedFamily,← StarSubalgebra.topologicalClosure_map _ φ
    (NonUnitalStarAlgHom.isometry φ hφ).isClosedEmbedding.isClosedMap
    (NonUnitalStarAlgHom.isometry φ hφ).continuous,StarAlgHom.map_adjoin,generatedFamily]
  congr 2
  rw [Set.image_union,Set.image_image]
  rfl

end

open Cardinal Topology TopologicalSpace

open Cardinal Topology TopologicalSpace
section
attribute [local instance] generatedFamily_isClosed
variable {A : Type} [CStarAlgebra A]

theorem exists_pureState_list (K : Type) (hK : 𝔠 ≤ #K)
    (hcount : #({f : A →L[ℂ] ℂ // IsPureState f}) ≤ 𝔠)
    (f : A →L[ℂ] ℂ) (hf : IsPureState f) :
    ∃ l : K → A →L[ℂ] ℂ, (∀ k, IsPureState (l k)) ∧
      ∀ g : A →L[ℂ] ℂ, IsPureState g → ∃ k, l k = g := by
  classical
  let P := {g : A →L[ℂ] ℂ // IsPureState g}
  let : Nonempty P := ⟨⟨f,hf⟩⟩
  obtain ⟨e⟩ := (Cardinal.le_def P K).mp (hcount.trans hK)
  let l : K → P := Function.invFun e
  have hl : Function.Surjective l := Function.invFun_surjective e.injective
  refine ⟨fun k => (l k).val,fun k => (l k).property,fun g hg => ?_⟩
  obtain ⟨k,hk⟩ := hl ⟨g,hg⟩
  exact ⟨k,congrArg Subtype.val hk⟩

end

end NaimarkZFC

end

end OAI
end

section
-- module Solutions.OAIQ115_Naimark.Naimark_Recursion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace NaimarkZFC

open Topology

open Topology
section
variable {A B : Type} [CStarAlgebra A] [CStarAlgebra B]

lemma generatedFamily_congr_on {ι : Type*} (b : Set A) (x y : ι → A) (S : Set ι)
    (h : ∀ k ∈ S, x k = y k) : generatedFamily b x S = generatedFamily b y S := by
  unfold generatedFamily
  congr 2
  exact congrArg (b ∪ ·) (Set.image_congr h)

end

open Topology

open Topology

section
attribute [local instance] generatedFamily_isClosed
attribute [local instance] PeakingPairData.ambientSubalgebraOrder PeakingPairData.ambientSubalgebraStarOrder

attribute [local instance] OAI.NaimarkZFC.instDecidableEqOrdinal_solutions_1
lemma generatedFamily_update_before {A : Type} [CStarAlgebra A] (b : Set A)
    (x : Ordinal.{0} → A) (δ : Ordinal.{0}) (z : A) (S : Set Ordinal.{0})
    (hS : S ⊆ Set.Iio δ) :
    generatedFamily b (Function.update x δ z) S = generatedFamily b x S := by
  exact generatedFamily_congr_on _ _ _ _ (fun k hk => Function.update_of_ne (hS hk).ne _ _)

end

open Topology

open Topology

open CategoryTheory

open CategoryTheory

open CategoryTheory Topology

open CategoryTheory CategoryTheory.Category CategoryTheory.SmallObject
open CategoryTheory.Limits
open CategoryTheory.SmallObject.SuccStruct

open CategoryTheory CategoryTheory.Category CategoryTheory.SmallObject
open CategoryTheory.Limits Opposite
open CategoryTheory.SmallObject.SuccStruct

open CategoryTheory CategoryTheory.Category CategoryTheory.SmallObject
open CategoryTheory.Limits Opposite
open CategoryTheory.SmallObject.SuccStruct

open CategoryTheory Cardinal Classical

open CategoryTheory CategoryTheory.Category CategoryTheory.SmallObject Opposite Cardinal
open CategoryTheory.SmallObject.SuccStruct

open Cardinal Ordinal

open CategoryTheory Topology

open CategoryTheory Cardinal

universe u v w

end NaimarkZFC

end

end OAI
end


