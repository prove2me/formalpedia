-- Prove2me | Definitions.Def_OAIQ115N008
-- name    : OAIQ115N008
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T00:31:24.541668+00:00
-- url     : https://prove2.me/theorems/e7e4d08f-d218-46f5-9384-ce73b6810af9
-- title:
--   Definitions bundle OAIQ115N008 of the split of OpenAI, A counterexample to Naimark's problem in ZFC
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.NaimarkZFC.main`, carved from OpenAI's openai/math development (OpenAI, *A counterexample to Naimark's problem in ZFC*, OpenAI Math Release, September 24, 2026, result family 297, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 80 declarations of OpenAI's Lean: 13 definitions, 3 instances and 64 theorems. The definitions and types are `OAI.NaimarkZFC.bridgeCenter`, `OAI.NaimarkZFC.cyclicFactorAlgebra`, `OAI.NaimarkZFC.cyclicOrbit`, `OAI.NaimarkZFC.cyclicOrbitLinear`, `OAI.NaimarkZFC.cyclicRepresentation`, `OAI.NaimarkZFC.cyclicSpan`, `OAI.NaimarkZFC.factorCompression`, `OAI.NaimarkZFC.matrixDiagonalExpectation`, `OAI.NaimarkZFC.matrixDiagonalHom`, `OAI.NaimarkZFC.matrixTrace`, `OAI.NaimarkZFC.normalizedMatrixTrace`, `OAI.NaimarkZFC.operatorCompression`, `OAI.NaimarkZFC.restrictedVectorFunctional`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Naimark_Amalgamation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Naimark/Amalgamation.lean), [`Naimark_Peaking`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Naimark/Peaking.lean), [`Naimark_Representations`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Naimark/Representations.lean), [`Naimark_States`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Naimark/States.lean).
--
--   **Imports.** It imports the published bundle `Def_Naimark`; the bundles `OAIQ115N004`, `OAIQ115N005` and `OAIQ115N006` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ115N010` and `OAIQ115N011`.
-- source:
--   OpenAI, A counterexample to Naimark's problem in ZFC, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 297; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-counterexample-to-Naimarks-problem-in-ZFC-September-24-2026/naimark-counterexample-zfc.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Definitions.Def_Naimark
import Definitions.Def_OAIQ115N004
import Definitions.Def_OAIQ115N005
import Definitions.Def_OAIQ115N006

section
-- module Solutions.OAIQ115_Naimark.Naimark_States
attribute [-instance] _root_.OAI.NaimarkZFC.CStarCompletion.instCStarAlgebraCompletionOfCStarRingOfStarModuleComplex_solutions _root_.OAI.NaimarkZFC.CStarCompletion.instNormedAlgebraComplexCompletion_solutions _root_.OAI.NaimarkZFC.CStarCompletion.instStarCompletion_solutions _root_.OAI.NaimarkZFC.CStarCompletion.instStarRingCompletion_solutions _root_.OAI.NaimarkZFC.centeredColumnComplete _root_.OAI.NaimarkZFC.centeredRowComplete _root_.OAI.NaimarkZFC.omittedAlgebra_isClosed _root_.OAI.NaimarkZFC.projectionRowComplete _root_.OAI.NaimarkZFC.retainedOrdinalAlgebra_isClosed _root_.OAI.NaimarkZFC.traceColumnComplete _root_.OAI.NaimarkZFC.vectorNullAlgebra_closed _root_.OAI.NaimarkZFC.vectorNullAlgebra_order _root_.OAI.NaimarkZFC.retainedOrdinalAlgebra_cstar _root_.OAI.NaimarkZFC.hnnGeneratedCStar _root_.OAI.NaimarkZFC.omittedAlgebra_cstar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace NaimarkZFC

variable {A : Type*} [CStarAlgebra A] (e : A) (he : IsStarProjection e)

instance cornerStarOrderedRing : StarOrderedRing (CStarCorner e he) :=
  CStarAlgebra.spectralOrderedRing _

open scoped ComplexOrder InnerProductSpace
open UniformSpace
open Filter Topology
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

open scoped ComplexOrder ComplexStarModule
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

omit [PartialOrder A] [StarOrderedRing A] in

theorem exists_state_extension_subalgebra
    (S : StarSubalgebra ℂ A) [IsClosed (S : Set A)]
    (f : S →L[ℂ] ℂ) (hf : IsState f) :
    ∃ F : A →L[ℂ] ℂ, IsState F ∧ ∀ a : S, F (a : A) = f a := by
  let : PartialOrder A := CStarAlgebra.spectralOrder A
  let : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  let : PartialOrder S := CStarAlgebra.spectralOrder S
  let : StarOrderedRing S := CStarAlgebra.spectralOrderedRing S
  let g : selfAdjointSubspace S →L[ℝ] ℝ :=
    Complex.reCLM.comp ((f.restrictScalars ℝ).comp (selfAdjointSubspaceInclusion S))
  have hg : ‖g‖ ≤ 1 := by
    apply g.opNorm_le_bound zero_le_one
    intro a
    change ‖(f (selfAdjointSubspaceInclusion S a)).re‖ ≤ 1 * ‖a‖
    calc
      _ ≤ ‖f (selfAdjointSubspaceInclusion S a)‖ := by simpa only [Real.norm_eq_abs] using Complex.abs_re_le_norm _
      _ ≤ ‖selfAdjointSubspaceInclusion S a‖ := state_norm_apply_le f hf _
      _ = 1 * ‖a‖ := by simp [selfAdjointSubspaceInclusion]; rfl
  obtain ⟨G₀, hG₀, hnG₀⟩ := exists_extension_norm_eq (selfAdjointSubspace S) g
  let sa : selfAdjoint A →L[ℝ] A :=
    ((selfAdjoint.submodule ℝ A).subtype).mkContinuous 1 (fun a => by simp)
  let G := G₀.comp sa
  have hGn : ‖G‖ ≤ 1 := by
    apply G.opNorm_le_bound zero_le_one
    intro a
    calc
      ‖G a‖ ≤ ‖G₀‖ * ‖sa a‖ := G₀.le_opNorm _
      _ ≤ 1 * ‖a‖ := mul_le_mul_of_nonneg_right (hnG₀.trans_le hg) (norm_nonneg _)
  have hG1 : G 1 = 1 := by
    let e : selfAdjointSubspace S := ⟨1, S.one_mem, IsSelfAdjoint.one A⟩
    have he := hG₀ e
    change G 1 = (f 1).re at he
    simpa only [(isState_iff f).mp hf |>.1, Complex.one_re] using he
  let F := positiveCLM (selfAdjointPositive G hGn hG1)
  have hF : IsState F := by
    apply (isState_iff _).mpr
    refine ⟨selfAdjointPositive_one G hGn hG1, fun a => ?_⟩
    exact ⟨((selfAdjointPositive G hGn hG1).map_nonneg
      (star_mul_self_nonneg a)).2.symm,
      ((selfAdjointPositive G hGn hG1).map_nonneg
      (star_mul_self_nonneg a)).1⟩
  refine ⟨F, hF, ?_⟩
  have hs (a : S) (ha : IsSelfAdjoint a) : F (a : A) = f a := by
    let b : selfAdjointSubspace S := ⟨(a : A), a.property, by
      change star (a : A) = (a : A)
      exact congrArg Subtype.val ha.star_eq⟩
    let bsa : selfAdjoint A := ⟨(a : A), b.property.2⟩
    have hfb : (f a).im = 0 := by
      have hh := state_map_star f hf a
      rw [ha.star_eq] at hh
      exact Complex.conj_eq_iff_im.mp hh.symm
    change selfAdjointPositive G hGn hG1 (bsa : A) = f a
    rw [selfAdjointPositive_coe]
    change (G₀ b : ℂ) = f a
    rw [hG₀ b]
    change ((f a).re : ℂ) = f a
    exact Complex.ext (by simp) (by simpa using hfb.symm)
  intro a
  have hdecomp := realPart_add_I_smul_imaginaryPart a
  rw [← hdecomp]
  change F (((realPart a : S) : A) + Complex.I • ((imaginaryPart a : S) : A)) = _
  simp only [map_add, map_smul]
  rw [hs _ (realPart a).property, hs _ (imaginaryPart a).property]

omit [PartialOrder A] [StarOrderedRing A] in

theorem exists_norming_state [Nontrivial A] (a : A) [IsStarNormal a] :
    ∃ f : A →L[ℂ] ℂ, IsState f ∧ ‖f a‖ = ‖a‖ := by
  let S := StarAlgebra.elemental ℂ a
  have : IsClosed (S : Set A) := StarAlgebra.elemental.isClosed ℂ a
  let b : S := ⟨a, StarAlgebra.elemental.self_mem ℂ a⟩
  obtain ⟨z, hz, hnz⟩ :=
    (IsometricContinuousFunctionalCalculus.isGreatest_norm_spectrum (𝕜 := ℂ) b).1
  obtain ⟨φ, hφ⟩ := WeakDual.CharacterSpace.mem_spectrum_iff_exists.mp hz
  obtain ⟨f, hf, hrest⟩ := exists_state_extension_subalgebra S
    (WeakDual.toStrongDual (φ : WeakDual ℂ S)) (character_isState φ)
  refine ⟨f, hf, ?_⟩
  change ‖f (b : A)‖ = ‖b‖
  rw [hrest b]
  change ‖φ b‖ = ‖b‖
  rw [hφ]
  exact hnz

open scoped ComplexOrder InnerProductSpace ComplexStarModule
open UniformSpace

open scoped Topology
open Filter

variable {A : Type*} [CStarAlgebra A] {ι : Type*}

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

open scoped ComplexOrder MatrixOrder CStarAlgebra
open Matrix

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

open scoped CStarAlgebra
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

open Filter Topology
open scoped ComplexOrder ComplexStarModule
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem exists_supported_norming_state (f : A →L[ℂ] ℂ) (hf : IsState f)
    (p : A) (hp : IsStarProjection p) (hfp : f p = 1)
    (a : A) (ha : IsSelfAdjoint a) :
    ∃ g : A →L[ℂ] ℂ, IsState g ∧ g p = 1 ∧ ‖g a‖ = ‖p * a * p‖ := by
  have : Nontrivial A := nontrivial_of_state f hf
  let b := p * a * p
  have hb : IsSelfAdjoint b := by
    change star (p * a * p) = p * a * p
    rw [star_mul, star_mul, hp.isSelfAdjoint.star_eq, ha.star_eq, mul_assoc]
  by_cases hz : b = 0
  · refine ⟨f, hf, hfp, ?_⟩
    rw [← state_compression f hf p (hp.norm_le _) hp.isSelfAdjoint hfp a]
    change ‖f b‖ = ‖b‖
    simp only [hz, map_zero, norm_zero]
  · let : IsStarNormal b := hb.isStarNormal
    obtain ⟨g, hg, hgn⟩ := exists_norming_state b
    have hpb : p * b * p = b := by
      calc
        p * b * p = (p * p) * a * (p * p) := by dsimp [b]; noncomm_ring
        _ = b := by rw [hp.isIdempotentElem.eq]
    have hbound := state_corner_bound g hg p hp b
    rw [hpb, hgn] at hbound
    have hpos : 0 < ‖b‖ := norm_pos_iff.mpr hz
    have hle : (g p).re ≤ 1 := (Complex.re_le_norm _).trans
      ((state_norm_apply_le g hg p).trans (hp.norm_le _))
    have heqr : (g p).re = 1 := by nlinarith
    have hgp : g p = 1 := by
      rw [state_projection_real g hg p hp, heqr, Complex.ofReal_one]
    refine ⟨g, hg, hgp, ?_⟩
    rw [← state_compression g hg p (hp.norm_le _) hp.isSelfAdjoint hgp a]
    exact hgn

theorem Peaks.excision_selfAdjoint {p : ℕ → A} {f : A →L[ℂ] ℂ} (hp : Peaks p f)
    (a : A) (ha : IsSelfAdjoint a) :
    Tendsto (fun n => ‖p n * (a - f a • (1 : A)) * p n‖) atTop (𝓝 0) := by
  let b := a - f a • (1 : A)
  have hb : IsSelfAdjoint b := by
    change star (a - f a • (1 : A)) = a - f a • (1 : A)
    rw [star_sub, ha.star_eq, star_smul, star_one, ← state_map_star f hp.2.2.1 a,
      ha.star_eq]
  have hfb : f b = 0 := by
    simp only [b, map_sub, map_smul, (isState_iff f).mp hp.2.2.1 |>.1,
      smul_eq_mul, mul_one, sub_self]
  choose g hg hgp hgn using fun n => exists_supported_norming_state f hp.2.2.1
    (p n) (hp.1 n) (hp.2.2.2.1 n) b hb
  have ht := (hp.tendsto_supported_apply g hg hgp b).norm
  simpa only [hfb, norm_zero, hgn] using ht

theorem Peaks.excision {p : ℕ → A} {f : A →L[ℂ] ℂ} (hp : Peaks p f) (a : A) :
    Tendsto (fun n => ‖p n * (a - f a • (1 : A)) * p n‖) atTop (𝓝 0) := by
  let r : A := realPart a
  let s : A := imaginaryPart a
  have hr := hp.excision_selfAdjoint r (realPart a).property
  have hs := hp.excision_selfAdjoint s (imaginaryPart a).property
  have ha : a = r + Complex.I • s := (realPart_add_I_smul_imaginaryPart a).symm
  have hdecomp (n : ℕ) : p n * (a - f a • (1 : A)) * p n =
      p n * (r - f r • (1 : A)) * p n +
      Complex.I • (p n * (s - f s • (1 : A)) * p n) := by
    conv_lhs => rw [ha]
    simp only [map_add, map_smul, add_smul, smul_smul, mul_add, add_mul,
      mul_sub, sub_mul, smul_mul_assoc, mul_smul_comm, smul_sub, mul_one]
    module
  have hbound (n : ℕ) : ‖p n * (a - f a • (1 : A)) * p n‖ ≤
      ‖p n * (r - f r • (1 : A)) * p n‖ +
      ‖p n * (s - f s • (1 : A)) * p n‖ := by
    rw [hdecomp n]
    simpa only [norm_smul, Complex.norm_I, one_mul] using norm_add_le
      (p n * (r - f r • (1 : A)) * p n)
      (Complex.I • (p n * (s - f s • (1 : A)) * p n))
  exact squeeze_zero (fun _ => norm_nonneg _) hbound (by simpa using hr.add hs)

end NaimarkZFC

end

end OAI
end

section
-- module Solutions.OAIQ115_Naimark.Naimark_Representations
attribute [-instance] _root_.OAI.NaimarkZFC.CStarCompletion.instCStarAlgebraCompletionOfCStarRingOfStarModuleComplex_solutions _root_.OAI.NaimarkZFC.CStarCompletion.instNormedAlgebraComplexCompletion_solutions _root_.OAI.NaimarkZFC.CStarCompletion.instStarCompletion_solutions _root_.OAI.NaimarkZFC.CStarCompletion.instStarRingCompletion_solutions _root_.OAI.NaimarkZFC.KOS.krylovSpace_finite _root_.OAI.NaimarkZFC.omittedAlgebra_isClosed _root_.OAI.NaimarkZFC.retainedOrdinalAlgebra_isClosed
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

theorem irreducible_selfAdjoint_vector
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hπ : IsIrreducible π)
    (d w : H) (hd : d ≠ 0) (hw : (⟪d, w⟫_ℂ).im = 0) :
    ∃ a : A, IsSelfAdjoint a ∧ π a d = w := by
  obtain ⟨T, hT, hTd⟩ := exists_selfAdjoint_operator_vector d w hd hw
  obtain ⟨a, ha, _, hM⟩ := irreducible_selfAdjoint_transitivity π hπ
    (Submodule.span ℂ {d}) T hT
  exact ⟨a, ha, (hM d (Submodule.subset_span (Set.mem_singleton d))).trans hTd⟩

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

lemma vectorNullAlgebra_coe_nonneg
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (ξ : H)
    (e : vectorNullAlgebra π ξ)
    (he : @LE.le _ (vectorNullAlgebra_order π ξ).toLE 0 e) : 0 ≤ (e : A) := by
  obtain ⟨v, hv⟩ := (CStarAlgebra.nonneg_iff_eq_star_mul_self
    (A := vectorNullAlgebra π ξ)).mp he
  have hh := congrArg (fun b : vectorNullAlgebra π ξ => (b : A)) hv
  change (e : A) = star (v : A) * (v : A) at hh
  rw [hh]
  exact star_mul_self_nonneg _

theorem vectorNull_approximateUnit_annihilates
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (ξ : H) {a : A} (ha : π a ξ = 0) :
    Tendsto (fun e : vectorNullAlgebra π ξ => a * (1 - (e : A)))
      (CStarAlgebra.approximateUnit (vectorNullAlgebra π ξ)) (𝓝 0) := by
  let B := vectorNullAlgebra π ξ
  let j : B →⋆ₙₐ[ℂ] A := NonUnitalStarSubalgebraClass.subtype B
  let l := CStarAlgebra.approximateUnit B
  have hl := CStarAlgebra.increasingApproximateUnit B
  let b : B := ⟨star a * a, star_mul_self_mem_vectorNullAlgebra π ξ ha⟩
  have hb : Tendsto (fun e : B => (star a * a) * (e : A)) l (𝓝 (star a * a)) := by
    exact show Tendsto (fun e : B => j (b * e)) l (𝓝 (j b)) from
      (map_continuous j).tendsto b |>.comp (hl.tendsto_mul_left b)
  have hd : Tendsto (fun e : B => ‖star a * a - star a * a * (e : A)‖) l (𝓝 0) := by
    simpa only [sub_self, norm_zero] using ((tendsto_const_nhds (x := star a * a)).sub hb).norm
  have hbs : ∀ᶠ e : B in l,
      ‖a * (1 - (e : A))‖ ≤ Real.sqrt ‖star a * a - star a * a * (e : A)‖ := by
    filter_upwards [hl.eventually_nonneg, hl.eventually_norm] with e he hen
    have heA : 0 ≤ (e : A) := vectorNullAlgebra_coe_nonneg π ξ e he
    have hle : (e : A) ≤ 1 := (CStarAlgebra.norm_le_one_iff_of_nonneg _ heA).mp hen
    have hx : 0 ≤ 1 - (e : A) := sub_nonneg.mpr hle
    have hxn : ‖1 - (e : A)‖ ≤ 1 :=
      (CStarAlgebra.norm_le_one_iff_of_nonneg _ hx).mpr (sub_le_self _ heA)
    apply (Real.le_sqrt (norm_nonneg _) (norm_nonneg _)).mpr
    calc
      ‖a * (1 - (e : A))‖ ^ 2 =
          ‖star (a * (1 - (e : A))) * (a * (1 - (e : A)))‖ := by
        rw [CStarRing.norm_star_mul_self, pow_two]
      _ = ‖(1 - (e : A)) * (star a * a - star a * a * (e : A))‖ := by
        congr 1
        simp only [star_mul, star_sub, star_one, (IsSelfAdjoint.of_nonneg heA).star_eq]
        noncomm_ring
      _ ≤ ‖1 - (e : A)‖ * ‖star a * a - star a * a * (e : A)‖ := norm_mul_le _ _
      _ ≤ 1 * ‖star a * a - star a * a * (e : A)‖ := by gcongr
      _ = _ := one_mul _
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) hbs
  simpa only [Function.comp_def, Real.sqrt_zero] using Real.continuous_sqrt.continuousAt.tendsto.comp hd

open scoped InnerProductSpace ComplexStarModule CStarAlgebra
open Filter Topology
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem vectorNull_complement_properties
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hone : π 1 = 1) (ξ : H) :
    ∀ᶠ e : vectorNullAlgebra π ξ in
      CStarAlgebra.approximateUnit (vectorNullAlgebra π ξ),
      0 ≤ 1 - (e : A) ∧ ‖1 - (e : A)‖ ≤ 1 ∧ π (1 - (e : A)) ξ = ξ := by
  have hl := CStarAlgebra.increasingApproximateUnit (vectorNullAlgebra π ξ)
  filter_upwards [hl.eventually_nonneg, hl.eventually_norm] with e he hen
  have heA : 0 ≤ (e : A) := vectorNullAlgebra_coe_nonneg π ξ e he
  have hle : (e : A) ≤ 1 := (CStarAlgebra.norm_le_one_iff_of_nonneg _ heA).mp hen
  have hx : 0 ≤ 1 - (e : A) := sub_nonneg.mpr hle
  refine ⟨hx, (CStarAlgebra.norm_le_one_iff_of_nonneg _ hx).mpr
    (sub_le_self _ heA), ?_⟩
  simp only [map_sub, sub_apply, hone, one_apply_eq_self, e.property.1, sub_zero]

open scoped InnerProductSpace ComplexStarModule
open Filter Topology
variable {B : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

open scoped InnerProductSpace ComplexStarModule CStarAlgebra ComplexOrder
open Filter Topology
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

open Filter Topology
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

open Filter Topology

open scoped InnerProductSpace ComplexStarModule CStarAlgebra ComplexOrder
open Filter Topology
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

lemma vectorNullAlgebra_coe_le
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (ξ : H)
    (e d : vectorNullAlgebra π ξ)
    (hed : @LE.le _ (vectorNullAlgebra_order π ξ).toLE e d) : (e : A) ≤ (d : A) := by
  have hdiff : @LE.le _ (vectorNullAlgebra_order π ξ).toLE 0 (d-e) := by
    simpa +instances only [vectorNullAlgebra_order, CStarAlgebra.spectralOrder, sub_zero]
      using hed
  exact sub_nonneg.mp (vectorNullAlgebra_coe_nonneg π ξ (d - e) hdiff)

lemma pureExcisionNet_nonneg (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (ξ : H)
    (e : ExcisionIndex (vectorNullAlgebra π ξ)) : 0 ≤ pureExcisionNet π ξ e := by
  have he := vectorNullAlgebra_coe_nonneg π ξ e.val e.property.1
  exact sub_nonneg.mpr ((CStarAlgebra.norm_le_one_iff_of_nonneg _ he).mp e.property.2.le)

lemma pureExcisionNet_norm (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (ξ : H)
    (e : ExcisionIndex (vectorNullAlgebra π ξ)) : ‖pureExcisionNet π ξ e‖ ≤ 1 := by
  exact (CStarAlgebra.norm_le_one_iff_of_nonneg _ (pureExcisionNet_nonneg π ξ e)).mpr
    (sub_le_self _ (vectorNullAlgebra_coe_nonneg π ξ e.val e.property.1))

lemma pureExcisionNet_antitone (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (ξ : H) :
    Antitone (pureExcisionNet π ξ) := by
  intro e d hed
  exact sub_le_sub_left (vectorNullAlgebra_coe_le π ξ e.val d.val hed) 1

omit [PartialOrder A] [StarOrderedRing A] in
lemma pureExcisionNet_fixes (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hone : π 1 = 1) (ξ : H)
    (e : ExcisionIndex (vectorNullAlgebra π ξ)) : π (pureExcisionNet π ξ e) ξ = ξ := by
  simp only [pureExcisionNet, map_sub, sub_apply, hone, one_apply_eq_self,
    e.val.property.1, sub_zero]

open scoped InnerProductSpace ComplexStarModule
open Filter Topology

open scoped InnerProductSpace ComplexStarModule CStarAlgebra ComplexOrder
open Filter Topology

open scoped ComplexOrder ComplexStarModule

open Filter Topology
open scoped ComplexOrder

open Filter Topology
open scoped ComplexOrder ComplexStarModule OnePoint InnerProductSpace

open scoped InnerProductSpace ComplexStarModule CStarAlgebra ComplexOrder
open Filter Topology

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

section
open scoped InnerProductSpace lp
variable {A V : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (τ : A →ₚ[ℂ] ℂ) (hτ : IsTracialPositive τ)
  (e : V → {a : A // IsStarProjection a})
  (horth : ∀ l k, l ≠ k → (e l).1 * (e k).1 = 0)
  (hmass : HasSum (fun l => (τ (e l).1).re) (τ 1).re)
  (hpos : ∀ l, 0 < (τ (e l).1).re)

theorem indexedColumnRepresentation_vacuum_norm (r : V)
    [DecidableEq (Option (Σ l, CenteredColumnIndex τ hτ e l r))] (a : A) :
    ‖indexedColumnRepresentation τ hτ e horth hmass hpos r a (lp.single 2 none 1)‖ ^ 2 =
      (τ ((e r).1 * (star a * a) * (e r).1)).re / (τ (e r).1).re := by
  let b := tracialColumnBasis τ hτ e horth hmass hpos r
  change ‖b.repr (traceColumnRepresentation τ hτ (e r) a
    (b.repr.symm (lp.single 2 none 1)))‖ ^ 2 = _
  rw [b.repr.norm_map, b.repr_symm_single]
  change ‖traceColumnRepresentation τ hτ (e r) a
    (tracialColumnBasis τ hτ e horth hmass hpos r none)‖ ^ 2 = _
  rw [tracialColumnBasis_none, columnUnit_action_norm_sq τ hτ (e r) (hpos r)]

end

open Filter Topology
variable {A V : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

open Filter Topology
open scoped InnerProductSpace lp
variable {A V : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

attribute [local instance] Classical.propDecidable

open scoped InnerProductSpace ENNReal lp

variable {ι κ : Type*} {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H]

variable {ι : Type*} {J : ι → Type*} {H : ι → Type*}
  [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℂ (H i)]
  [∀ i, CompleteSpace (H i)]

open scoped InnerProductSpace ENNReal lp

variable {ι : Type*} {H K : ι → Type*}
  [∀ i, NormedAddCommGroup (H i)] [∀ i, NormedAddCommGroup (K i)]
  [∀ i, InnerProductSpace ℂ (H i)] [∀ i, InnerProductSpace ℂ (K i)]

theorem hilbertSumMap_norm_le (T : ∀ i, H i →L[ℂ] K i) (C : ℝ) (hC : 0 ≤ C)
    (hT : ∀ i, ‖T i‖ ≤ C) : ‖hilbertSumMap T C hC hT‖ ≤ C :=
  LinearMap.mkContinuous_norm_le _ hC _

variable [∀ i, CompleteSpace (H i)] [∀ i, CompleteSpace (K i)]

variable {A : Type*} [CStarAlgebra A]

open scoped InnerProductSpace ENNReal lp
variable {I V : Type*} (L : I → V → V → Type*) [DecidableEq I]

variable {A : I → Type*} [∀ i, CStarAlgebra (A i)]

open scoped InnerProductSpace lp
variable {I V : Type*} (L : I → V → V → Type*) [DecidableEq I]

variable {A : I → Type*} [∀ i, CStarAlgebra (A i)]

section
open scoped InnerProductSpace lp
variable {I V : Type*} (L : I → V → V → Type*) [DecidableEq I]

theorem fockStartProjection_norm_le (i : I) : ‖fockStartProjection L i‖ ≤ 1 :=
  hilbertSumMap_norm_le _ _ _ _

end

open scoped InnerProductSpace lp
variable {V J : Type*}

open scoped InnerProductSpace ComplexOrder
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem operatorVectorFunctional_star_mul (ξ : H) (T : H →L[ℂ] H) :
    operatorVectorFunctional ξ (star T * T) = (‖T ξ‖ ^ 2 : ℝ) := by
  change inner ℂ ξ (T.adjoint (T ξ)) = _
  rw [ContinuousLinearMap.adjoint_inner_right, inner_self_eq_norm_sq_to_K]
  exact (Complex.ofReal_pow _ _).symm

theorem operatorVectorFunctional_norm (ξ : H) (hξ : ‖ξ‖ = 1) : ‖operatorVectorFunctional ξ‖ = 1 := by
  apply le_antisymm
  · apply (operatorVectorFunctional ξ).opNorm_le_bound (show (0 : ℝ) ≤ 1 by norm_num)
    intro T
    calc
      ‖operatorVectorFunctional ξ T‖ ≤ ‖ξ‖ * ‖T ξ‖ := norm_inner_le_norm _ _
      _ ≤ ‖ξ‖ * (‖T‖ * ‖ξ‖) := mul_le_mul_of_nonneg_left (T.le_opNorm ξ) (norm_nonneg _)
      _ = 1 * ‖T‖ := by rw [hξ]; ring
  · have hn := (operatorVectorFunctional ξ).le_opNorm (1 : H →L[ℂ] H)
    have hn1 : operatorVectorFunctional ξ 1 = 1 := by simp [inner_self_eq_norm_sq_to_K, hξ]
    rw [hn1, norm_one] at hn
    have hid : ‖(1 : H →L[ℂ] H)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
    have hh := mul_le_mul_of_nonneg_left hid (norm_nonneg (operatorVectorFunctional ξ))
    simpa only [mul_one] using hn.trans hh

section

variable {V B : Type*} [Ring B] [Algebra ℂ B]

variable (q : V → B)
variable (hq : ∀ r, q r * q r = q r)
variable (ho : ∀ r t, r ≠ t → q r * q t = 0)

include hq ho in
theorem finiteAtomicDiagonal_eigen {s : Finset V} {a : B}
    (ha : a ∈ finiteAtomicDiagonal q hq ho s) (r : V) :
    ∃ z : ℂ, q r * a = z • q r ∧ a * q r = z • q r := by
  classical
  change a ∈ finiteAtomicSpan q s at ha
  induction ha using Submodule.span_induction with
  | mem a ha =>
    rcases ha with ⟨t, _, rfl⟩
    by_cases ht : r = t
    · subst t
      exact ⟨1, by rw [hq, one_smul], by rw [hq, one_smul]⟩
    · exact ⟨0, by rw [ho r t ht, zero_smul], by rw [ho t r (Ne.symm ht), zero_smul]⟩
  | zero => exact ⟨0, by simp, by simp⟩
  | add a b _ _ ha hb =>
    rcases ha with ⟨z, hz, hz'⟩
    rcases hb with ⟨w, hw, hw'⟩
    exact ⟨z+w, by rw [mul_add, hz, hw, add_smul], by rw [add_mul, hz', hw', add_smul]⟩
  | smul c a _ ha =>
    rcases ha with ⟨z, hz, hz'⟩
    exact ⟨c*z, by rw [mul_smul_comm, hz, smul_smul], by rw [smul_mul_assoc, hz', smul_smul]⟩

variable (φ : B →ₗ[ℂ] ℂ)

theorem finiteAtomExpectation_mem (s : Finset V) (a : B) :
    finiteAtomExpectation q φ s a ∈ finiteAtomicDiagonal q hq ho s := by
  change (∑ r ∈ s, _) ∈ finiteAtomicSpan q s
  apply Submodule.sum_mem
  intro r hr
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨r, hr, rfl⟩)

end

variable {B : Type*} [NormedRing B] [NormedAlgebra ℂ B]

open Filter Topology
open scoped lp
variable {J V : Type*} [DecidableEq V]

variable [DecidableEq J]

section
open Filter Topology
open scoped InnerProductSpace lp
variable {I V : Type*} {A : I → Type*} [∀ i, CStarAlgebra (A i)]
  [∀ i, PartialOrder (A i)] [∀ i, StarOrderedRing (A i)]
variable (d : ∀ i, AtomicTraceData (A i) V) [DecidableEq I]

instance instIsClosedAtomicOperatorsCoeStarSubalgebraComplexAtomicCStarAlgebra : IsClosed (atomicCStarAlgebra d : Set (AtomicOperators d)) := isClosed_closure

end

open scoped InnerProductSpace
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def operatorCompression (M : Submodule ℂ H) [CompleteSpace M] :
    (H →L[ℂ] H) →L[ℂ] (M →L[ℂ] M) where
  toFun T := M.orthogonalProjectionOnto.comp (T.comp M.subtypeL)
  map_add' := by intros; ext x; simp
  map_smul' := by intros; ext x; simp
  cont := by fun_prop

@[simp] theorem operatorCompression_apply (M : Submodule ℂ H) [CompleteSpace M]
    (T : H →L[ℂ] H) (x : M) :
    operatorCompression M T x = M.orthogonalProjectionOnto (T (x : H)) := rfl

@[simp] theorem operatorCompression_one (M : Submodule ℂ H) [CompleteSpace M] :
    operatorCompression M 1 = 1 := by
  ext x
  simp

theorem operatorCompression_inner (M : Submodule ℂ H) [CompleteSpace M]
    (T : H →L[ℂ] H) (x y : M) :
    inner ℂ x (operatorCompression M T y) = inner ℂ (x : H) (T (y : H)) :=
  M.inner_orthogonalProjectionOnto_eq_of_mem_left x _

theorem operatorCompression_zero_of_dense {J : Type*}
    (M : Submodule ℂ H) [CompleteSpace M] (v : J → M) (hv : DenseRange v)
    (T : H →L[ℂ] H)
    (hT : ∀ i j, inner ℂ (v i : H) (T (v j : H)) = 0) :
    operatorCompression M T = 0 := by
  apply ContinuousLinearMap.ext
  intro y
  apply (inner_self_eq_zero (𝕜 := ℂ)).mp
  have hleft (i : J) : inner ℂ (v i) (operatorCompression M T y) = 0 := by
    refine hv.induction_on (p := fun z : M => inner ℂ (v i) (operatorCompression M T z) = 0)
      y (isClosed_eq (by fun_prop) continuous_const) ?_
    intro j
    rw [operatorCompression_inner]
    exact hT i j
  exact hv.induction_on (p := fun z : M => inner ℂ z (operatorCompression M T y) = 0)
    (operatorCompression M T y) (isClosed_eq (by fun_prop) continuous_const) hleft

variable [CompleteSpace H]

@[simp] theorem operatorCompression_star (M : Submodule ℂ H) [CompleteSpace M]
    (T : H →L[ℂ] H) : operatorCompression M (star T) = star (operatorCompression M T) := by
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  rw [← inner_conj_symm, operatorCompression_inner]
  change star (inner ℂ (y : H) (T.adjoint (x : H))) = _
  rw [ContinuousLinearMap.adjoint_inner_right]
  change (starRingEnd ℂ) (inner ℂ (T (y : H)) (x : H)) = _
  rw [inner_conj_symm, operatorCompression_inner]

variable {A : Type*} [CStarAlgebra A]

@[simp] theorem representationInverse_apply_map (π : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hπ : Function.Injective π) (x : A) :
    representationInverse π hπ ⟨π x, ⟨x,rfl⟩⟩ = x :=
  (StarAlgEquiv.ofInjective π hπ).symm_apply_apply x

@[simp] theorem representation_map_inverse (π : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hπ : Function.Injective π) (x : π.range) :
    π (representationInverse π hπ x) = x :=
  congrArg Subtype.val ((StarAlgEquiv.ofInjective π hπ).apply_symm_apply x)

open scoped InnerProductSpace
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {A : Type*} [CStarAlgebra A]

def cyclicOrbitLinear (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H) : A →ₗ[ℂ] H where
  toFun a := π a ξ
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

def cyclicSpan (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H) : Submodule ℂ H :=
  (cyclicOrbitLinear π ξ).range.topologicalClosure

instance cyclicSpanComplete (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H) :
    CompleteSpace (cyclicSpan π ξ) := isClosed_closure.completeSpace_coe

theorem cyclicSpan_invariant (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H)
    (a : A) (x : H) (hx : x ∈ cyclicSpan π ξ) : π a x ∈ cyclicSpan π ξ := by
  apply map_mem_closure (π a).continuous hx
  rintro y ⟨b,rfl⟩
  refine ⟨a*b, ?_⟩
  simp [cyclicOrbitLinear, map_mul]

theorem cyclicSpan_vector_mem (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H) : ξ ∈ cyclicSpan π ξ := by
  apply subset_closure
  refine ⟨1, ?_⟩
  simp [cyclicOrbitLinear]

def cyclicOrbit (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H) (a : A) : cyclicSpan π ξ :=
  ⟨π a ξ, subset_closure ⟨a,rfl⟩⟩

theorem cyclicOrbit_dense (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H) :
    DenseRange (cyclicOrbit π ξ) := by
  have h := ((denseRange_inclusion_iff (subset_closure
    (s := Set.range (fun a : A => π a ξ)))).2 Set.Subset.rfl).comp
    Set.rangeFactorization_surjective.denseRange (continuous_inclusion subset_closure)
  exact h

def cyclicRepresentation (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H) :
    A →⋆ₐ[ℂ] ((cyclicSpan π ξ) →L[ℂ] (cyclicSpan π ξ)) :=
  restrictRepresentation π (cyclicSpan π ξ) (cyclicSpan_invariant π ξ)

@[simp] theorem cyclicRepresentation_apply (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H)
    (a : A) (x : cyclicSpan π ξ) : (cyclicRepresentation π ξ a x : H) = π a (x : H) := rfl

theorem cyclicRepresentation_injective (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H)
    (hsep : ∀ a : A, π a ξ = 0 → a = 0) : Function.Injective (cyclicRepresentation π ξ) := by
  intro a b h
  apply sub_eq_zero.mp
  apply hsep
  have he := congrArg (fun T => (T ⟨ξ, cyclicSpan_vector_mem π ξ⟩ : H)) h
  simpa only [cyclicRepresentation_apply, map_sub, sub_apply,
    sub_eq_zero] using he

open scoped InnerProductSpace
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def restrictedVectorFunctional (B : StarSubalgebra ℂ (H →L[ℂ] H)) (ξ : H) :
    B →L[ℂ] ℂ where
  toFun b := operatorVectorFunctional ξ b
  map_add' _ _ := (operatorVectorFunctional ξ).map_add _ _
  map_smul' _ _ := (operatorVectorFunctional ξ).map_smul _ _
  cont := (operatorVectorFunctional ξ).continuous.comp continuous_subtype_val

@[simp] theorem restrictedVectorFunctional_apply (B : StarSubalgebra ℂ (H →L[ℂ] H))
    (ξ : H) (b : B) : restrictedVectorFunctional B ξ b = operatorVectorFunctional ξ b := rfl

@[simp] theorem restrictedVectorFunctional_norm (B : StarSubalgebra ℂ (H →L[ℂ] H))
    (ξ : H) (hξ : ‖ξ‖ = 1) : ‖restrictedVectorFunctional B ξ‖ = 1 := by
  apply le_antisymm
  · apply (restrictedVectorFunctional B ξ).opNorm_le_bound zero_le_one
    intro b
    change ‖operatorVectorFunctional ξ (b : H →L[ℂ] H)‖ ≤ 1 * ‖(b : H →L[ℂ] H)‖
    simpa only [operatorVectorFunctional_norm ξ hξ]
      using (operatorVectorFunctional ξ).le_opNorm (b : H →L[ℂ] H)
  · have h := (restrictedVectorFunctional B ξ).le_opNorm (1 : B)
    have he : restrictedVectorFunctional B ξ 1 = 1 := by
      simp [inner_self_eq_norm_sq_to_K, hξ]
    rw [he, norm_one] at h
    have hn : ‖(1 : B)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
    have hh := mul_le_mul_of_nonneg_left hn (norm_nonneg (restrictedVectorFunctional B ξ))
    exact h.trans (by simpa using hh)

section
open scoped InnerProductSpace
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (B : StarSubalgebra ℂ (H →L[ℂ] H))
variable {I : Type*} {A : I → Type*} [∀ i, CStarAlgebra (A i)]
variable (ι : ∀ i, A i →⋆ₐ[ℂ] B) (ξ : H)

def factorCompression (i : I) :
    B →L[ℂ] ((cyclicSpan (ambientFactor B ι i) ξ) →L[ℂ]
      (cyclicSpan (ambientFactor B ι i) ξ)) where
  toFun b := operatorCompression (cyclicSpan (ambientFactor B ι i) ξ) b
  map_add' _ _ := (operatorCompression _).map_add _ _
  map_smul' _ _ := (operatorCompression _).map_smul _ _
  cont := (operatorCompression _).continuous.comp continuous_subtype_val

@[simp] theorem factorCompression_apply (i : I) (b : B) :
    factorCompression B ι ξ i b =
      operatorCompression (cyclicSpan (ambientFactor B ι i) ξ) b := rfl

@[simp] theorem factorCompression_factor (i : I) (a : A i) :
    factorCompression B ι ξ i (ι i a) = cyclicRepresentation (ambientFactor B ι i) ξ a := by
  ext x
  change ((cyclicSpan (ambientFactor B ι i) ξ).orthogonalProjectionOnto
      ((ambientFactor B ι i a) (x : H)) : H) = _
  rw [Submodule.coe_orthogonalProjectionOnto_apply]
  exact Submodule.starProjection_eq_self_iff.mpr
    (cyclicSpan_invariant (ambientFactor B ι i) ξ a x x.property)

theorem factor_word_coefficient (i : I) (a b : A i) (w : B) :
    inner ℂ ((ambientFactor B ι i a) ξ) ((w : H →L[ℂ] H) ((ambientFactor B ι i b) ξ)) =
      restrictedVectorFunctional B ξ (star (ι i a) * w * ι i b) := by
  change inner ℂ ((ambientFactor B ι i a) ξ)
      ((w : H →L[ℂ] H) ((ambientFactor B ι i b) ξ)) =
    inner ℂ ξ ((((star (ι i a) * w * ι i b : B) : H →L[ℂ] H)) ξ)
  rw [← ContinuousLinearMap.adjoint_inner_right]
  rfl

end

section
open scoped InnerProductSpace
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (B : StarSubalgebra ℂ (H →L[ℂ] H))
variable {I : Type*} {A : I → Type*} [∀ i, CStarAlgebra (A i)]
variable (ι : ∀ i, A i →⋆ₐ[ℂ] B) (ξ : H)

@[simp] theorem factorCompression_star (i : I) (b : B) :
    factorCompression B ι ξ i (star b) = star (factorCompression B ι ξ i b) := by
  change operatorCompression (cyclicSpan (ambientFactor B ι i) ξ) (star (b : H →L[ℂ] H)) =
    star (operatorCompression (cyclicSpan (ambientFactor B ι i) ξ) (b : H →L[ℂ] H))
  exact operatorCompression_star (cyclicSpan (ambientFactor B ι i) ξ) (b : H →L[ℂ] H)

def cyclicFactorAlgebra (i : I) : StarSubalgebra ℂ
    ((cyclicSpan (ambientFactor B ι i) ξ) →L[ℂ] (cyclicSpan (ambientFactor B ι i) ξ)) :=
  (cyclicRepresentation (ambientFactor B ι i) ξ).range

end

open scoped CStarAlgebra

section
open scoped InnerProductSpace lp
variable {I V : Type*} {A : I → Type*} [∀ i, CStarAlgebra (A i)]
  [∀ i, PartialOrder (A i)] [∀ i, StarOrderedRing (A i)]
variable (d : ∀ i, AtomicTraceData (A i) V) [DecidableEq I] [DecidableEq V]

theorem atomicCommonAtom_separate (k : I) (T U : AtomicOperators d)
    (h : ∀ r, atomicCommonAtom d k r * T = atomicCommonAtom d k r * U) : T = U := by
  ext x j
  have hh := congrArg (fun W : AtomicOperators d => W x j) (h j.2.1)
  simpa only [mul_apply_eq_comp, atomicCommonAtom_apply, ite_eq_left rfl, ite_true, if_true] using hh

variable {Δ : Type*} [CStarAlgebra Δ]
variable (δ : ∀ i, Δ →⋆ₐ[ℂ] A i) (χ : Δ → V → ℂ)
variable (hatom : ∀ i x r, ((d i).atom r).1 * δ i x = χ x r • ((d i).atom r).1)
include hatom

theorem atomicLeft_diagonal_agree (i k : I) (x : Δ) :
    atomicLeft d i (δ i x) = atomicLeft d k (δ k x) := by
  apply atomicCommonAtom_separate d k
  intro r
  change atomicLeft d k ((d k).atom r).1 * atomicLeft d i (δ i x) = _
  rw [← atomicLeft_atoms d i k r, ← map_mul, hatom i x r, map_smul]
  rw [atomicLeft_atoms d i k r]
  change χ x r • atomicLeft d k ((d k).atom r).1 =
    atomicLeft d k ((d k).atom r).1 * atomicLeft d k (δ k x)
  rw [← map_mul, hatom k x r, map_smul]

end

open scoped ComplexOrder CStarAlgebra
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {n : Type*} [Fintype n] [DecidableEq n]

def matrixTrace (τ : A →ₚ[ℂ] ℂ) : CStarMatrix n n A →ₚ[ℂ] ℂ :=
  PositiveLinearMap.mk₀
    { toFun := fun M => ∑ i, τ (M i i)
      map_add' M N := by simp [Finset.sum_add_distrib]
      map_smul' z M := by simp [Finset.mul_sum] }
    (by
      intro M hM
      apply AddSubmonoid.closure_induction
        (motive := fun M _ => 0 ≤ ∑ i, τ (M i i)) ?_ ?_ ?_
        (StarOrderedRing.nonneg_iff.mp hM)
      · rintro M ⟨N,rfl⟩
        simp only [CStarMatrix.mul_apply, CStarMatrix.star_apply, map_sum]
        exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
          τ.map_nonneg (star_mul_self_nonneg _)
      · simp
      · intro M N _ _ hM hN
        simpa only [CStarMatrix.add_apply, map_add, Finset.sum_add_distrib] using add_nonneg hM hN)

omit [DecidableEq n] in
@[simp] theorem matrixTrace_apply (τ : A →ₚ[ℂ] ℂ) (M : CStarMatrix n n A) :
    matrixTrace τ M = ∑ i, τ (M i i) := rfl

omit [DecidableEq n] in

theorem matrixTrace_tracial (τ : A →ₚ[ℂ] ℂ) (hτ : ∀ a b, τ (a*b) = τ (b*a))
    (M N : CStarMatrix n n A) : matrixTrace τ (M*N) = matrixTrace τ (N*M) := by
  simp only [matrixTrace_apply, CStarMatrix.mul_apply, map_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact hτ _ _

omit [DecidableEq n] in

theorem matrixTrace_faithful (τ : A →ₚ[ℂ] ℂ)
    (hf : ∀ a, τ (star a*a) = 0 → a = 0) (M : CStarMatrix n n A)
    (hM : matrixTrace τ (star M * M) = 0) : M = 0 := by
  simp only [matrixTrace_apply, CStarMatrix.mul_apply, CStarMatrix.star_apply, map_sum] at hM
  have hn (i j : n) : 0 ≤ τ (star (M i j)*M i j) := τ.map_nonneg (star_mul_self_nonneg _)
  ext i j
  apply hf
  have hj := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ =>
    Finset.sum_nonneg (fun l _ => hn l k))).mp hM j (Finset.mem_univ j)
  exact (Finset.sum_eq_zero_iff_of_nonneg (fun l _ => hn l j)).mp hj i (Finset.mem_univ i)

@[simp] theorem matrixTrace_one (τ : A →ₚ[ℂ] ℂ) :
    matrixTrace (n := n) τ 1 = (Fintype.card n : ℂ) * τ 1 := by
  simp only [matrixTrace_apply, CStarMatrix.one_apply_eq, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]

def normalizedMatrixTrace (τ : A →ₚ[ℂ] ℂ) : CStarMatrix n n A →ₚ[ℂ] ℂ :=
  PositiveLinearMap.mk₀ ((Fintype.card n : ℝ)⁻¹ • (matrixTrace τ).toLinearMap)
    (by
      intro M hM
      change 0 ≤ (Fintype.card n : ℝ)⁻¹ • matrixTrace τ M
      exact smul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) ((matrixTrace τ).map_nonneg hM))

omit [DecidableEq n] in
@[simp] theorem normalizedMatrixTrace_apply (τ : A →ₚ[ℂ] ℂ) (M : CStarMatrix n n A) :
    normalizedMatrixTrace τ M = (Fintype.card n : ℝ)⁻¹ • matrixTrace τ M := rfl

omit [DecidableEq n] in
theorem normalizedMatrixTrace_tracial (τ : A →ₚ[ℂ] ℂ) (hτ : ∀ a b, τ (a*b) = τ (b*a))
    (M N : CStarMatrix n n A) : normalizedMatrixTrace τ (M*N) = normalizedMatrixTrace τ (N*M) := by
  simp only [normalizedMatrixTrace_apply, matrixTrace_tracial τ hτ M N]

omit [DecidableEq n] in
theorem normalizedMatrixTrace_faithful [Nonempty n] (τ : A →ₚ[ℂ] ℂ)
    (hf : ∀ a, τ (star a*a) = 0 → a = 0) (M : CStarMatrix n n A)
    (hM : normalizedMatrixTrace τ (star M*M) = 0) : M = 0 := by
  apply matrixTrace_faithful τ hf M
  rw [normalizedMatrixTrace_apply] at hM
  exact (smul_eq_zero.mp hM).resolve_left
    (inv_ne_zero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero))

theorem normalizedMatrixTrace_one [Nonempty n] (τ : A →ₚ[ℂ] ℂ) (hn : τ 1 = 1) :
    normalizedMatrixTrace (n := n) τ 1 = 1 := by
  rw [normalizedMatrixTrace_apply, matrixTrace_one, hn, mul_one]
  change (Fintype.card n : ℝ)⁻¹ * (Fintype.card n : ℂ) = 1
  rw [Complex.ofReal_inv, Complex.ofReal_natCast, inv_mul_cancel₀]
  exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero

open scoped CStarAlgebra
variable {A B n : Type*} [CStarAlgebra A] [CStarAlgebra B] [Fintype n] [DecidableEq n]

omit [Fintype n] in
@[simp] theorem matrixSingle_apply (i j k l : n) (a : A) :
    matrixSingle i j a k l = if i = k ∧ j = l then a else 0 := rfl

omit [Fintype n] in
@[simp] theorem matrixSingle_star (i j : n) (a : A) :
    star (matrixSingle i j a) = matrixSingle j i (star a) := by
  change (Matrix.single i j a).conjTranspose = Matrix.single j i (star a)
  exact Matrix.conjTranspose_single _ _ _

@[simp] theorem matrixSingle_mul (i j k : n) (a b : A) :
    matrixSingle i j a * matrixSingle j k b = matrixSingle i k (a*b) := by
  change Matrix.single i j a * Matrix.single j k b = Matrix.single i k (a*b)
  exact Matrix.single_mul_single_same a i j k b

theorem matrixSingle_mul_of_ne (i j k l : n) (a b : A) (h : j ≠ k) :
    matrixSingle i j a * matrixSingle k l b = 0 := by
  change Matrix.single i j a * Matrix.single k l b = 0
  exact Matrix.single_mul_single_of_ne a i j k h b

omit [Fintype n] in
@[simp] theorem matrixSingle_zero (i j : n) : matrixSingle i j (0 : A) = 0 := by
  ext; simp

omit [Fintype n] in
@[simp] theorem matrixSingle_smul (i j : n) (a : A) (z : ℂ) :
    matrixSingle i j (z • a) = z • matrixSingle i j a := by
  ext k l
  by_cases h : i = k ∧ j = l <;> simp [h]

theorem matrixSingle_projection (i : n) (a : A) (ha : IsStarProjection a) :
    IsStarProjection (matrixSingle i i a) := by
  refine ⟨?_, ?_⟩
  · simp only [IsIdempotentElem, matrixSingle_mul, ha.isIdempotentElem.eq]
  · simp only [IsSelfAdjoint, matrixSingle_star, ha.isSelfAdjoint.star_eq]

@[simp] theorem matrixSingle_compress (i j : n) (a b : A) (M : CStarMatrix n n A) :
    matrixSingle i i a * M * matrixSingle j j b = matrixSingle i j (a * M i j * b) := by
  change Matrix.single i i a * CStarMatrix.ofMatrix.symm M * Matrix.single j j b = _
  exact Matrix.single_mul_mul_single i i j j a _ b

def matrixDiagonalHom (δ : n → B →⋆ₐ[ℂ] A) : (n → B) →⋆ₐ[ℂ] CStarMatrix n n A where
  toFun x := CStarMatrix.ofMatrix (Matrix.diagonal (fun i => δ i (x i)))
  map_zero' := by
    change Matrix.diagonal (fun i => δ i 0) = 0
    simp
  map_one' := by
    change Matrix.diagonal (fun i => δ i 1) = (1 : Matrix n n A)
    simp
  map_add' x y := by
    change Matrix.diagonal (fun i => δ i (x i + y i)) =
      Matrix.diagonal (fun i => δ i (x i)) + Matrix.diagonal (fun i => δ i (y i))
    simp only [map_add, Matrix.diagonal_add]
  map_mul' x y := by
    change CStarMatrix.ofMatrix (Matrix.diagonal (fun i => δ i (x i * y i))) = _
    change Matrix.diagonal (fun i => δ i (x i * y i)) =
      Matrix.diagonal (fun i => δ i (x i)) * Matrix.diagonal (fun i => δ i (y i))
    rw [Matrix.diagonal_mul_diagonal]
    congr 1; funext i; exact map_mul _ _ _
  commutes' z := by
    change Matrix.diagonal (fun i => δ i (algebraMap ℂ B z)) = algebraMap ℂ (Matrix n n A) z
    rw [Matrix.algebraMap_eq_diagonal]
    congr 1
    funext i
    exact (δ i).commutes z
  map_star' x := by
    change Matrix.diagonal (fun i => δ i (star (x i))) =
      (Matrix.diagonal (fun i => δ i (x i))).conjTranspose
    rw [Matrix.diagonal_conjTranspose]
    congr 1
    funext i
    exact map_star (δ i) (x i)

@[simp] theorem matrixDiagonalHom_apply (δ : n → B →⋆ₐ[ℂ] A) (x : n → B) (i j : n) :
    matrixDiagonalHom δ x i j = if i = j then δ i (x i) else 0 := by
  simp [matrixDiagonalHom, Matrix.diagonal_apply]

@[simp] theorem matrixDiagonalHom_mul_apply (δ : n → B →⋆ₐ[ℂ] A) (x : n → B)
    (M : CStarMatrix n n A) (i j : n) :
    (matrixDiagonalHom δ x * M) i j = δ i (x i) * M i j := by
  exact Matrix.diagonal_mul _ _ _ _

@[simp] theorem matrixSingle_diagonal (δ : n → B →⋆ₐ[ℂ] A) (x : n → B) (i : n) (a : A) :
    matrixSingle i i a * matrixDiagonalHom δ x = matrixSingle i i (a * δ i (x i)) := by
  ext k l
  change (Matrix.single i i a * Matrix.diagonal (fun j => δ j (x j))) k l = _
  rw [Matrix.mul_diagonal]
  by_cases h : i = k ∧ i = l
  · rcases h with ⟨rfl,rfl⟩; simp
  · simp [matrixSingle_apply, h]

variable [PartialOrder A] [StarOrderedRing A]

def matrixDiagonalExpectation (E : n → A →L[ℂ] B) (hE : ∀ i a, ‖E i a‖ ≤ ‖a‖) :
    CStarMatrix n n A →L[ℂ] (n → B) :=
  LinearMap.mkContinuous
    { toFun := fun M i => E i (M i i)
      map_add' M N := by ext i; simp
      map_smul' z M := by ext i; simp }
    1 (fun M => by
      change ‖fun i => E i (M i i)‖ ≤ 1 * ‖M‖
      rw [one_mul]
      exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun i =>
        (hE i _).trans CStarMatrix.norm_entry_le_norm)

omit [DecidableEq n] in
@[simp] theorem matrixDiagonalExpectation_apply (E : n → A →L[ℂ] B)
    (hE : ∀ i a, ‖E i a‖ ≤ ‖a‖) (M : CStarMatrix n n A) (i : n) :
    matrixDiagonalExpectation E hE M i = E i (M i i) := rfl

open scoped ComplexOrder CStarAlgebra
variable {A V n : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [Fintype n] [DecidableEq n]

@[simp] theorem matrixTrace_single (τ : A →ₚ[ℂ] ℂ) (i : n) (a : A) :
    matrixTrace τ (matrixSingle i i a) = τ a := by
  simp only [matrixTrace_apply, matrixSingle_apply, and_self]
  simp_rw [apply_ite τ, map_zero]
  simp

@[simp] theorem normalizedMatrixTrace_single (τ : A →ₚ[ℂ] ℂ) (i : n) (a : A) :
    normalizedMatrixTrace τ (matrixSingle i i a) = (Fintype.card n : ℝ)⁻¹ • τ a := by
  rw [normalizedMatrixTrace_apply, matrixTrace_single]

open scoped ComplexOrder CStarAlgebra

open scoped ComplexOrder CStarAlgebra

end NaimarkZFC

end

end OAI
end

section
-- module Solutions.OAIQ115_Naimark.Naimark_Peaking
attribute [-instance] _root_.OAI.NaimarkZFC.CStarCompletion.instCStarAlgebraCompletionOfCStarRingOfStarModuleComplex_solutions _root_.OAI.NaimarkZFC.CStarCompletion.instNormedAlgebraComplexCompletion_solutions _root_.OAI.NaimarkZFC.CStarCompletion.instStarCompletion_solutions _root_.OAI.NaimarkZFC.CStarCompletion.instStarRingCompletion_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace NaimarkZFC

open scoped ComplexOrder CStarAlgebra

open Filter Topology
open scoped ComplexOrder CStarAlgebra OnePoint

open Filter Topology
open scoped ComplexOrder

open Filter Topology

open Filter Topology
open scoped CStarAlgebra ComplexOrder OnePoint

open Filter Topology

open Filter Topology

section
open scoped CStarAlgebra
variable {A D Z : Type*} [CStarAlgebra A] [CStarAlgebra D] [CStarAlgebra Z]
  [PartialOrder A] [StarOrderedRing A]
  [PartialOrder D] [StarOrderedRing D]
  (φ : CStarMatrix Bool Bool A →⋆ₐ[ℂ] Z)
  (ψ : CStarMatrix Bool Bool D →⋆ₐ[ℂ] Z)
  (δ : Bool → D →⋆ₐ[ℂ] A)
  (hd : ∀ x, φ (matrixDiagonalHom δ x) =
    ψ (matrixDiagonalHom (fun _ => StarAlgHom.id ℂ D) x))

variable (E : CStarMatrix Bool Bool A →L[ℂ] (Bool → D))
  (hE : ∀ x, E (matrixDiagonalHom δ x) = x)

def bridgeCenter (a : CStarMatrix Bool Bool A) : CStarMatrix Bool Bool A :=
  a - matrixDiagonalHom δ (E a)

include hE in
omit [PartialOrder A] [StarOrderedRing A] [PartialOrder D] [StarOrderedRing D] in
theorem bridgeCenter_centered (a : CStarMatrix Bool Bool A) : E (bridgeCenter δ E a) = 0 := by
  rw [bridgeCenter,map_sub,hE,sub_self]

end

open Filter Topology
open scoped OnePoint ComplexOrder CStarAlgebra

open Filter Topology
open scoped CStarAlgebra ComplexOrder OnePoint

open Filter Topology
open scoped CStarAlgebra ComplexOrder

open scoped InnerProductSpace ComplexStarModule CStarAlgebra ComplexOrder

open Filter Topology
open scoped InnerProductSpace ComplexStarModule CStarAlgebra ComplexOrder

open Filter Topology

open Filter Topology
open scoped CStarAlgebra ComplexOrder

open Filter Topology
open scoped CStarAlgebra ComplexOrder

open Filter Topology
open scoped InnerProductSpace ComplexOrder ComplexStarModule

open Filter Topology
open scoped CStarAlgebra ComplexOrder

open Filter Topology
open scoped CStarAlgebra ComplexOrder InnerProductSpace

open Filter Topology
open scoped CStarAlgebra ComplexOrder InnerProductSpace

open Filter Topology
open scoped CStarAlgebra ComplexOrder InnerProductSpace

open scoped CStarAlgebra ComplexOrder InnerProductSpace

open Filter Topology
open scoped CStarAlgebra ComplexOrder

open scoped CStarAlgebra ComplexOrder

end NaimarkZFC

end

end OAI
end


