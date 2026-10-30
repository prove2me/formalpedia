-- Prove2me | Definitions.Def_OAIQ115N001
-- name    : OAIQ115N001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T00:22:47.294459+00:00
-- url     : https://prove2.me/theorems/933ff751-2fbb-4107-87fa-4c56fda611fe
-- title:
--   Definitions bundle OAIQ115N001 of the split of OpenAI, A counterexample to Naimark's problem in ZFC
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.NaimarkZFC.main`, carved from OpenAI's openai/math development (OpenAI, *A counterexample to Naimark's problem in ZFC*, OpenAI Math Release, September 24, 2026, result family 297, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 191 declarations of OpenAI's Lean: 67 definitions, 4 inductive types or structures, 8 instances and 112 theorems. The definitions and types are `OAI.NaimarkZFC.BridgeCore`, `OAI.NaimarkZFC.BridgeCore.Centered`, `OAI.NaimarkZFC.BridgeCore.cons`, `OAI.NaimarkZFC.BridgeCore.eval`, `OAI.NaimarkZFC.BridgeCore.left`, `OAI.NaimarkZFC.BridgeCore.right`, `OAI.NaimarkZFC.BridgeCore.snoc`, `OAI.NaimarkZFC.BridgeDecayData`, `OAI.NaimarkZFC.CStarCorner`, `OAI.NaimarkZFC.CenteredDecomposition`, `OAI.NaimarkZFC.ExcisionIndex`, `OAI.NaimarkZFC.IsCenteredWord`, `OAI.NaimarkZFC.IsPureState`, `OAI.NaimarkZFC.Peaks`, `OAI.NaimarkZFC.SequenceDiagonal`, `OAI.NaimarkZFC.StronglyApproximable`, `OAI.NaimarkZFC.ambientFactor`, `OAI.NaimarkZFC.amplificationBlock`, `OAI.NaimarkZFC.atomCornerFunctional`, `OAI.NaimarkZFC.atomicWeightVector`, `OAI.NaimarkZFC.columnVertex`, `OAI.NaimarkZFC.coordinateInclusion`, `OAI.NaimarkZFC.cornerCompression`, `OAI.NaimarkZFC.cornerFunctional`, `OAI.NaimarkZFC.cornerState`, `OAI.NaimarkZFC.cornerSubalgebra`, `OAI.NaimarkZFC.cyclicPreGNS`, `OAI.NaimarkZFC.diagonalOperator`, `OAI.NaimarkZFC.dominatedGNS`, `OAI.NaimarkZFC.dominatedPreGNS`, `OAI.NaimarkZFC.factorAlgebra`, `OAI.NaimarkZFC.finiteAtomExpectation`, `OAI.NaimarkZFC.finiteAtomicSpan`, `OAI.NaimarkZFC.gnsVector`, `OAI.NaimarkZFC.hilbertBasisReindex`, `OAI.NaimarkZFC.idealSelfAdjointSubspace`, `OAI.NaimarkZFC.irreducibleUnitalRepresentation`, `OAI.NaimarkZFC.l2Basis`, `OAI.NaimarkZFC.leftStabilizer`, `OAI.NaimarkZFC.matrixEntryCLM` and 31 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Naimark_Amalgamation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Naimark/Amalgamation.lean), [`Naimark_Basic`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Naimark/Basic.lean), [`Naimark_HNN`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Naimark/HNN.lean), [`Naimark_Peaking`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Naimark/Peaking.lean), [`Naimark_Representations`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Naimark/Representations.lean), [`Naimark_States`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Naimark/States.lean).
--
--   **Imports.** It imports the published bundle `Def_Naimark`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ115N004`, `OAIQ115N005` and `OAIQ115N006`.
-- source:
--   OpenAI, A counterexample to Naimark's problem in ZFC, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 297; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-counterexample-to-Naimarks-problem-in-ZFC-September-24-2026/naimark-counterexample-zfc.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Definitions.Def_Naimark

section
-- module Solutions.OAIQ115_Naimark.Naimark_Basic
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

def gnsVector (f : A →ₚ[ℂ] ℂ) : f.GNS := (f.toPreGNS 1 : f.GNS)

@[simp] theorem gns_apply_vector (f : A →ₚ[ℂ] ℂ) (a : A) :
    f.gnsStarAlgHom a (gnsVector f) = (f.toPreGNS a : f.GNS) := by
  simp [gnsVector]

theorem gnsVector_cyclic (f : A →ₚ[ℂ] ℂ) :
    DenseRange (fun a : A => f.gnsStarAlgHom a (gnsVector f)) := by
  simp only [gns_apply_vector]
  exact Completion.denseRange_coe.comp f.toPreGNS.surjective.denseRange (Completion.continuous_coe _)

@[simp] theorem gnsVector_coefficient (f : A →ₚ[ℂ] ℂ) (a : A) :
    ⟪gnsVector f, f.gnsStarAlgHom a (gnsVector f)⟫_ℂ = f a := by
  simp [gnsVector, Completion.inner_coe, PositiveLinearMap.preGNS_inner_def]

@[simp] theorem gnsVector_norm_sq (f : A →ₚ[ℂ] ℂ) :
    ‖gnsVector f‖ ^ 2 = (f 1).re := by
  simp only [gnsVector, Completion.norm_coe,
    PositiveLinearMap.preGNS_norm_def, PositiveLinearMap.ofPreGNS_toPreGNS,
    star_one, one_mul]
  exact Real.sq_sqrt (f.map_nonneg (show (0 : A) ≤ 1 from zero_le_one)).1

theorem positive_norm_apply_le (f : A →ₚ[ℂ] ℂ) (a : A) :
    ‖f a‖ ≤ (f 1).re * ‖a‖ := by
  calc
    ‖f a‖ = ‖⟪gnsVector f, f.gnsStarAlgHom a (gnsVector f)⟫_ℂ‖ :=
      congrArg norm (gnsVector_coefficient f a).symm
    _ ≤ ‖gnsVector f‖ * ‖f.gnsStarAlgHom a (gnsVector f)‖ := norm_inner_le_norm _ _
    _ ≤ ‖gnsVector f‖ * (‖f.gnsStarAlgHom a‖ * ‖gnsVector f‖) := by
      gcongr
      exact (f.gnsStarAlgHom a).le_opNorm _
    _ ≤ ‖gnsVector f‖ * (‖a‖ * ‖gnsVector f‖) := by
      gcongr
      exact NonUnitalStarAlgHom.norm_apply_le f.gnsStarAlgHom a
    _ = (f 1).re * ‖a‖ := by rw [← gnsVector_norm_sq]; ring

def positiveCLM (f : A →ₚ[ℂ] ℂ) : A →L[ℂ] ℂ :=
  f.toLinearMap.mkContinuous (f 1).re (positive_norm_apply_le f)

@[simp] theorem positiveCLM_apply (f : A →ₚ[ℂ] ℂ) (a : A) : positiveCLM f a = f a := rfl

theorem positiveCLM_norm (f : A →ₚ[ℂ] ℂ) : ‖positiveCLM f‖ = (f 1).re := by
  have hpos : 0 ≤ f 1 := f.map_nonneg zero_le_one
  apply le_antisymm
  · exact (positiveCLM f).opNorm_le_bound hpos.1 (positive_norm_apply_le f)
  · calc
      (f 1).re = ‖f 1‖ := Complex.re_eq_norm.mpr hpos
      _ = ‖positiveCLM f 1‖ := rfl
      _ ≤ ‖positiveCLM f‖ * ‖(1 : A)‖ := (positiveCLM f).le_opNorm 1
      _ ≤ ‖positiveCLM f‖ * 1 := by
        gcongr
        exact (IsStarProjection.one A).norm_le _
      _ = ‖positiveCLM f‖ := mul_one _

def positiveOfSquares (f : A →L[ℂ] ℂ)
    (hf : ∀ a : A, (f (star a * a)).im = 0 ∧ 0 ≤ (f (star a * a)).re) :
    A →ₚ[ℂ] ℂ :=
  PositiveLinearMap.mk₀ f.toLinearMap fun x hx => by
    have hx' := StarOrderedRing.nonneg_iff.mp hx
    refine AddSubmonoid.closure_induction (fun x hx => ?_) (by simp)
      (fun x y _ _ hx hy => ?_) hx'
    · obtain ⟨a, rfl⟩ := hx
      exact ⟨(hf a).2, (hf a).1.symm⟩
    · simpa only [map_add] using add_nonneg hx hy

@[simp] theorem positiveOfSquares_apply (f : A →L[ℂ] ℂ)
    (hf : ∀ a : A, (f (star a * a)).im = 0 ∧ 0 ≤ (f (star a * a)).re) (a : A) :
    positiveOfSquares f hf a = f a := rfl

@[simp] theorem positiveCLM_positiveOfSquares (f : A →L[ℂ] ℂ)
    (hf : ∀ a : A, (f (star a * a)).im = 0 ∧ 0 ≤ (f (star a * a)).re) :
    positiveCLM (positiveOfSquares f hf) = f := by ext; rfl

theorem isState_iff (f : A →L[ℂ] ℂ) :
    IsState f ↔ f 1 = 1 ∧
      ∀ a : A, (f (star a * a)).im = 0 ∧ 0 ≤ (f (star a * a)).re := by
  constructor
  · rintro ⟨hnorm, hpos⟩
    refine ⟨?_, hpos⟩
    have hre : (f 1).re = 1 := by
      rw [← positiveOfSquares_apply f hpos 1, ← positiveCLM_norm,
        positiveCLM_positiveOfSquares, hnorm]
    have him : (f 1).im = 0 := by simpa using (hpos 1).1
    exact Complex.ext hre him
  · rintro ⟨hone, hpos⟩
    refine ⟨?_, hpos⟩
    have hn := positiveCLM_norm (positiveOfSquares f hpos)
    simpa only [positiveCLM_positiveOfSquares, positiveOfSquares_apply, hone,
      Complex.one_re] using hn

theorem gnsVector_norm_eq_one (f : A →ₚ[ℂ] ℂ) (hf : f 1 = 1) : ‖gnsVector f‖ = 1 := by
  have hs := gnsVector_norm_sq f
  rw [hf, Complex.one_re] at hs
  nlinarith [norm_nonneg (gnsVector f)]

theorem gns_fix_of_value_one (f : A →ₚ[ℂ] ℂ) (hf : f 1 = 1)
    (x : A) (hx : ‖x‖ ≤ 1) (hfx : f x = 1) :
    f.gnsStarAlgHom x (gnsVector f) = gnsVector f := by
  have hn := gnsVector_norm_eq_one f hf
  have hy : ‖f.gnsStarAlgHom x (gnsVector f)‖ ≤ 1 := by
    calc
      _ ≤ ‖f.gnsStarAlgHom x‖ * ‖gnsVector f‖ := (f.gnsStarAlgHom x).le_opNorm _
      _ ≤ ‖x‖ * 1 := by
        gcongr
        · exact NonUnitalStarAlgHom.norm_apply_le f.gnsStarAlgHom x
        · exact hn.le
      _ ≤ 1 := by simpa using hx
  have hd := norm_sub_sq (𝕜 := ℂ) (gnsVector f) (f.gnsStarAlgHom x (gnsVector f))
  rw [gnsVector_coefficient, hfx, hn] at hd
  have hz : ‖gnsVector f - f.gnsStarAlgHom x (gnsVector f)‖ = 0 := by
    simp only [RCLike.re_to_complex, Complex.one_re, one_pow] at hd
    nlinarith [norm_nonneg (gnsVector f - f.gnsStarAlgHom x (gnsVector f)),
      norm_nonneg (f.gnsStarAlgHom x (gnsVector f))]
  exact (sub_eq_zero.mp (norm_eq_zero.mp hz)).symm

theorem positive_compression (f : A →ₚ[ℂ] ℂ) (hf : f 1 = 1)
    (x : A) (hx : ‖x‖ ≤ 1) (hself : IsSelfAdjoint x) (hfx : f x = 1) (a : A) :
    f (x * a * x) = f a := by
  have hfix := gns_fix_of_value_one f hf x hx hfx
  have hsa : ContinuousLinearMap.adjoint (f.gnsStarAlgHom x) = f.gnsStarAlgHom x := by
    change star (f.gnsStarAlgHom x) = f.gnsStarAlgHom x
    rw [← map_star, hself.star_eq]
  calc
    f (x * a * x) = ⟪gnsVector f,
        f.gnsStarAlgHom x (f.gnsStarAlgHom a (f.gnsStarAlgHom x (gnsVector f)))⟫_ℂ := by
      rw [← gnsVector_coefficient f (x * a * x)]
      simp only [map_mul, mul_apply_eq_comp]
    _ = ⟪gnsVector f, f.gnsStarAlgHom a (gnsVector f)⟫_ℂ := by
      rw [hfix, ← ContinuousLinearMap.adjoint_inner_left, hsa, hfix]
    _ = f a := gnsVector_coefficient f a

omit [PartialOrder A] [StarOrderedRing A] in

theorem state_norm_apply_le (f : A →L[ℂ] ℂ) (hf : IsState f) (a : A) : ‖f a‖ ≤ ‖a‖ := by
  simpa [hf.1] using f.le_opNorm a

theorem state_compression (f : A →L[ℂ] ℂ) (hf : IsState f)
    (x : A) (hx : ‖x‖ ≤ 1) (hself : IsSelfAdjoint x) (hfx : f x = 1) (a : A) :
    f (x * a * x) = f a :=
  positive_compression (positiveOfSquares f hf.2) ((isState_iff f).mp hf).1 x hx hself hfx a

def IsPureState (f : A →L[ℂ] ℂ) : Prop :=
  f ∈ Set.extremePoints ℝ {g : A →L[ℂ] ℂ | IsState g}

omit [PartialOrder A] [StarOrderedRing A] in

theorem state_projection_face (f g : A →L[ℂ] ℂ) (hf : IsState f) (hg : IsState g)
    (p : A) (hp : IsStarProjection p) (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hab : a + b = 1) (heq : (a • f + b • g) p = 1) : f p = 1 ∧ g p = 1 := by
  have hfim : (f p).im = 0 := by
    simpa only [hp.isSelfAdjoint.star_eq, hp.isIdempotentElem.eq] using (hf.2 p).1
  have hgim : (g p).im = 0 := by
    simpa only [hp.isSelfAdjoint.star_eq, hp.isIdempotentElem.eq] using (hg.2 p).1
  have hfr : (f p).re ≤ 1 :=
    (Complex.re_le_norm _).trans ((state_norm_apply_le f hf p).trans (hp.norm_le _))
  have hgr : (g p).re ≤ 1 :=
    (Complex.re_le_norm _).trans ((state_norm_apply_le g hg p).trans (hp.norm_le _))
  have heqr := congrArg Complex.re heq
  simp only [add_apply, smul_apply,
    Complex.add_re, Complex.smul_re, Complex.one_re, smul_eq_mul] at heqr
  have hfr' : (f p).re = 1 := by nlinarith
  have hgr' : (g p).re = 1 := by nlinarith
  exact ⟨Complex.ext hfr' hfim, Complex.ext hgr' hgim⟩

def Peaks (p : ℕ → A) (f : A →L[ℂ] ℂ) : Prop :=
  (∀ n, IsStarProjection (p n)) ∧ Antitone p ∧ IsState f ∧
    (∀ n, f (p n) = 1) ∧
    ∀ g : A →L[ℂ] ℂ, IsState g → (∀ n, g (p n) = 1) → g = f

omit [StarOrderedRing A] in

theorem Peaks.isPureState {p : ℕ → A} {f : A →L[ℂ] ℂ} (hp : Peaks p f) :
    IsPureState f := by
  rw [IsPureState, mem_extremePoints]
  refine ⟨hp.2.2.1, ?_⟩
  intro g hg h hh hseg
  obtain ⟨a, b, ha, hb, hab, heq⟩ := hseg
  have hfaces : ∀ n, g (p n) = 1 ∧ h (p n) = 1 := by
    intro n
    apply state_projection_face g h hg hh (p n) (hp.1 n) a b ha hb hab
    rw [heq]
    exact hp.2.2.2.1 n
  exact ⟨hp.2.2.2.2 g hg (fun n => (hfaces n).1),
    hp.2.2.2.2 h hh (fun n => (hfaces n).2)⟩

theorem state_nonneg (f : A →L[ℂ] ℂ) (hf : IsState f) {x : A} (hx : 0 ≤ x) :
    0 ≤ f x := (positiveOfSquares f hf.2).map_nonneg hx

variable {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

def starAlgHomCLM (φ : A →⋆ₐ[ℂ] B) : A →L[ℂ] B :=
  φ.toAlgHom.toLinearMap.mkContinuous 1 (fun a => by
    change ‖φ a‖ ≤ 1 * ‖a‖
    simpa only [one_mul] using NonUnitalStarAlgHom.norm_apply_le φ a)

omit [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B] in
@[simp] theorem starAlgHomCLM_apply (φ : A →⋆ₐ[ℂ] B) (a : A) :
    starAlgHomCLM φ a = φ a := rfl

def restrictState (φ : A →⋆ₐ[ℂ] B) (f : B →L[ℂ] ℂ) : A →L[ℂ] ℂ :=
  f.comp (starAlgHomCLM φ)

omit [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B] in
@[simp] theorem restrictState_apply (φ : A →⋆ₐ[ℂ] B) (f : B →L[ℂ] ℂ) (a : A) :
    restrictState φ f a = f (φ a) := rfl

variable {A : Type u} [CStarAlgebra A]
    {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem irreducible_map_one (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hπ : IsIrreducible π) :
    π 1 = 1 := by
  have hp : IsIdempotentElem (π 1) := by
    change π 1 * π 1 = π 1
    rw [← map_mul, one_mul]
  have hr (a : A) (x : H) : π a x ∈ (π 1).range := by
    refine ⟨π a x, ?_⟩
    change (π 1 * π a) x = π a x
    rw [← map_mul, one_mul]
  rcases hπ.2 (π 1).range (ContinuousLinearMap.IsIdempotentElem.isClosed_range hp) (fun a x _ => hr a x) with hz | ht
  · exfalso
    apply hπ.1
    ext a x
    have h := hr a x
    rw [hz] at h
    exact h
  · ext x
    have hx : x ∈ (π 1).range := by rw [ht]; trivial
    obtain ⟨y, rfl⟩ := hx
    change (π 1 * π 1) y = π 1 y
    rw [hp]

def orbitMap (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (x : H) : A →ₗ[ℂ] H where
  toFun a := π a x
  map_add' a b := by simp
  map_smul' c a := by simp

@[simp] theorem orbitMap_apply (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (x : H) (a : A) :
    orbitMap π x a = π a x := rfl

def orbitCLM (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (x : H) : A →L[ℂ] H :=
  (orbitMap π x).mkContinuous ‖x‖ fun a => by
    calc
      ‖π a x‖ ≤ ‖π a‖ * ‖x‖ := (π a).le_opNorm x
      _ ≤ ‖a‖ * ‖x‖ := mul_le_mul_of_nonneg_right (NonUnitalStarAlgHom.norm_apply_le π a) (norm_nonneg x)
      _ = ‖x‖ * ‖a‖ := mul_comm _ _

def vectorFunctional (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (x : H) : A →L[ℂ] ℂ :=
  (innerSL ℂ x).comp (orbitCLM π x)

@[simp] theorem vectorFunctional_apply (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (x : H) (a : A) :
    vectorFunctional π x a = ⟪x, π a x⟫_ℂ := rfl

variable [PartialOrder A] [StarOrderedRing A]

variable {A : Type u} [CStarAlgebra A]
    {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def dominatedPreGNS (f g : A →ₚ[ℂ] ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hdom : ∀ a : A, (g (star a * a)).re ≤ C * (f (star a * a)).re) :
    f.PreGNS →L[ℂ] g.PreGNS :=
  (g.toPreGNS.toLinearMap.comp f.ofPreGNS.toLinearMap).mkContinuous (Real.sqrt C) fun x => by
    change √(g (star (f.ofPreGNS x) * f.ofPreGNS x)).re ≤
      √C * √(f (star (f.ofPreGNS x) * f.ofPreGNS x)).re
    rw [← Real.sqrt_mul hC]
    exact Real.sqrt_le_sqrt (hdom _)

@[simp] theorem dominatedPreGNS_apply (f g : A →ₚ[ℂ] ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hdom : ∀ a : A, (g (star a * a)).re ≤ C * (f (star a * a)).re) (a : A) :
    dominatedPreGNS f g C hC hdom (f.toPreGNS a) = g.toPreGNS a := rfl

def dominatedGNS (f g : A →ₚ[ℂ] ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hdom : ∀ a : A, (g (star a * a)).re ≤ C * (f (star a * a)).re) :
    f.GNS →L[ℂ] g.GNS := (dominatedPreGNS f g C hC hdom).completion

@[simp] theorem dominatedGNS_apply_coe (f g : A →ₚ[ℂ] ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hdom : ∀ a : A, (g (star a * a)).re ≤ C * (f (star a * a)).re) (a : A) :
    dominatedGNS f g C hC hdom (f.toPreGNS a : f.GNS) = (g.toPreGNS a : g.GNS) := by
  simp [dominatedGNS]

@[simp] theorem dominatedGNS_apply_vector (f g : A →ₚ[ℂ] ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hdom : ∀ a : A, (g (star a * a)).re ≤ C * (f (star a * a)).re) :
    dominatedGNS f g C hC hdom (gnsVector f) = gnsVector g := by
  simp [gnsVector]

variable {A : Type u} [CStarAlgebra A]
    {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {K : Type w} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def cyclicPreGNS (f : A →ₚ[ℂ] ℂ) (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (ξ : H)
    (hcoeff : ∀ a : A, f a = ⟪ξ, π a ξ⟫_ℂ) : f.PreGNS →ₗᵢ[ℂ] H where
  toLinearMap := (orbitMap π ξ).comp f.ofPreGNS.toLinearMap
  norm_map' x := by
    change ‖π (f.ofPreGNS x) ξ‖ = √(f (star (f.ofPreGNS x) * f.ofPreGNS x)).re
    rw [hcoeff, map_mul, map_star]
    change ‖π (f.ofPreGNS x) ξ‖ =
      √(⟪ξ, (π (f.ofPreGNS x)).adjoint (π (f.ofPreGNS x) ξ)⟫_ℂ).re
    rw [ContinuousLinearMap.adjoint_inner_right, inner_self_eq_norm_sq_to_K]
    rw [← RCLike.ofReal_pow]
    change ‖π (f.ofPreGNS x) ξ‖ = √(‖π (f.ofPreGNS x) ξ‖ ^ 2)
    exact (Real.sqrt_sq (norm_nonneg _)).symm

end GNS

open Topology

end NaimarkZFC

end

end OAI
end

section
-- module Solutions.OAIQ115_Naimark.Naimark_States
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace NaimarkZFC

variable {A : Type*} [CStarAlgebra A] (e : A) (he : IsStarProjection e)

def cornerSubalgebra : NonUnitalStarSubalgebra ℂ A where
  carrier := {a | e * a = a ∧ a * e = a}
  zero_mem' := by simp
  add_mem' := by
    rintro a b ⟨ha,ha'⟩ ⟨hb,hb'⟩
    simp [mul_add, add_mul, ha, hb, ha', hb']
  mul_mem' := by
    rintro a b ⟨ha,ha'⟩ ⟨hb,hb'⟩
    exact ⟨by rw [← mul_assoc, ha], by rw [mul_assoc, hb']⟩
  smul_mem' := by
    rintro z a ⟨ha,ha'⟩
    exact ⟨by rw [mul_smul_comm, ha], by rw [smul_mul_assoc, ha']⟩
  star_mem' := by
    rintro a ⟨ha,ha'⟩
    constructor
    · simpa only [star_mul, he.isSelfAdjoint.star_eq] using congrArg star ha'
    · simpa only [star_mul, he.isSelfAdjoint.star_eq] using congrArg star ha

instance cornerClosed : IsClosed (cornerSubalgebra e he : Set A) := by
  exact (isClosed_eq (continuous_const.mul continuous_id) continuous_id).inter
    (isClosed_eq (continuous_id.mul continuous_const) continuous_id)

abbrev CStarCorner := cornerSubalgebra e he

instance cornerOne : One (CStarCorner e he) :=
  ⟨⟨e, he.isIdempotentElem.eq, he.isIdempotentElem.eq⟩⟩

@[simp] theorem corner_coe_one : ((1 : CStarCorner e he) : A) = e := rfl

instance cornerRing : Ring (CStarCorner e he) := {
  (inferInstance : NonUnitalRing (CStarCorner e he)) with
  one := 1
  one_mul a := Subtype.ext a.2.1
  mul_one a := Subtype.ext a.2.2
  natCast n := n • (1 : CStarCorner e he)
  natCast_zero := zero_nsmul _
  natCast_succ n := succ_nsmul _ _
  intCast z := z • (1 : CStarCorner e he)
  intCast_ofNat n := ofNat_zsmul _ _
  intCast_negSucc n := by
    change (Int.negSucc n) • (1 : CStarCorner e he) = -((n+1) • (1 : CStarCorner e he))
    rw [Int.negSucc_eq, neg_zsmul]
    congr 1
    exact ofNat_zsmul (1 : CStarCorner e he) (n+1) }

instance cornerNormedRing : NormedRing (CStarCorner e he) := {
  (inferInstance : NonUnitalNormedRing (CStarCorner e he)), cornerRing e he with }

instance cornerAlgebra : Algebra ℂ (CStarCorner e he) :=
  Algebra.ofModule smul_mul_assoc mul_smul_comm

instance cornerCStarAlgebra : CStarAlgebra (CStarCorner e he) := {
  (inferInstance : NonUnitalCStarAlgebra (CStarCorner e he)),
  cornerNormedRing e he, cornerAlgebra e he with }

def cornerCompression : A →L[ℂ] CStarCorner e he where
  toFun a := ⟨e*a*e, by
    constructor
    · rw [← mul_assoc, ← mul_assoc, he.isIdempotentElem.eq]
    · rw [mul_assoc (e*a), he.isIdempotentElem.eq]⟩
  map_add' a b := Subtype.ext (by
    change e*(a+b)*e = e*a*e+e*b*e
    simp only [mul_add, add_mul])
  map_smul' z a := Subtype.ext (by
    change e*(z • a)*e = z • (e*a*e)
    simp only [mul_smul_comm, smul_mul_assoc])
  cont := by
    apply Continuous.subtype_mk
    exact (continuous_const.mul continuous_id).mul continuous_const

@[simp] theorem cornerCompression_coe (a : A) :
    (cornerCompression e he a : A) = e*a*e := rfl

@[simp] theorem cornerCompression_corner (a : CStarCorner e he) :
    cornerCompression e he (a : A) = a := by
  apply Subtype.ext
  exact (congrArg (· * e) a.2.1).trans a.2.2

open scoped ComplexOrder InnerProductSpace
open UniformSpace
open Filter Topology
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def weakStates (A : Type*) [CStarAlgebra A] : Set (WeakDual ℂ A) :=
  {f | IsState f.toStrongDual}

theorem isClosed_weakStates : IsClosed (weakStates A) := by
  have hone : IsClosed {f : WeakDual ℂ A | f 1 = 1} :=
    isClosed_eq (WeakDual.eval_continuous 1) continuous_const
  have hpos (a : A) : IsClosed {f : WeakDual ℂ A |
      (f (star a * a)).im = 0 ∧ 0 ≤ (f (star a * a)).re} :=
    (isClosed_eq (Complex.continuous_im.comp (WeakDual.eval_continuous _)) continuous_const).inter
      (isClosed_le continuous_const (Complex.continuous_re.comp (WeakDual.eval_continuous _)))
  have h := hone.inter (isClosed_iInter hpos)
  simpa only [weakStates, isState_iff, WeakDual.toStrongDual_apply, Set.ofPred_and,
    Set.ofPred_forall] using h

theorem isCompact_weakStates : IsCompact (weakStates A) := by
  apply (WeakDual.isCompact_closedBall (0 : StrongDual ℂ A) 1).of_isClosed_subset
    isClosed_weakStates
  intro f hf
  change f.toStrongDual ∈ Metric.closedBall 0 1
  simp only [Metric.mem_closedBall, dist_zero_right]
  exact le_of_eq hf.1

theorem state_eq_one_of_projection_le (f : A →L[ℂ] ℂ) (hf : IsState f)
    (p q : A) (hq : IsStarProjection q) (hpq : p ≤ q) (hfp : f p = 1) : f q = 1 := by
  have hmono := (positiveOfSquares f hf.2).monotone
  apply le_antisymm
  · have hh := hmono hq.le_one
    change f q ≤ f 1 at hh
    rwa [((isState_iff f).mp hf).1] at hh
  · have hh := hmono hpq
    change f p ≤ f q at hh
    rwa [hfp] at hh

theorem Peaks.tendsto_supported {p : ℕ → A} {f : A →L[ℂ] ℂ} (hp : Peaks p f)
    (g : ℕ → A →L[ℂ] ℂ) (hg : ∀ n, IsState (g n)) (hgn : ∀ n, g n (p n) = 1) :
    Tendsto (fun n => StrongDual.toWeakDual (g n)) atTop (𝓝 (StrongDual.toWeakDual f)) := by
  apply isCompact_weakStates.tendsto_nhds_of_unique_mapClusterPt
    (Filter.Eventually.of_forall hg)
  intro k hk hcluster
  apply WeakDual.toStrongDual.injective
  apply hp.2.2.2.2 _ hk
  intro m
  have hclosed : IsClosed {z : WeakDual ℂ A | z (p m) = 1} :=
    isClosed_eq (WeakDual.eval_continuous _) continuous_const
  apply hclosed.mem_of_mapClusterPt hcluster
  filter_upwards [eventually_ge_atTop m] with n hn
  exact state_eq_one_of_projection_le (g n) (hg n) (p n) (p m) (hp.1 m) (hp.2.1 hn) (hgn n)

theorem Peaks.tendsto_supported_apply {p : ℕ → A} {f : A →L[ℂ] ℂ} (hp : Peaks p f)
    (g : ℕ → A →L[ℂ] ℂ) (hg : ∀ n, IsState (g n)) (hgn : ∀ n, g n (p n) = 1) (a : A) :
    Tendsto (fun n => g n a) atTop (𝓝 (f a)) :=
  ((WeakDual.eval_continuous a).tendsto _).comp (hp.tendsto_supported g hg hgn)

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def cornerFunctional (f : A →L[ℂ] ℂ) (p : A) : A →L[ℂ] ℂ :=
  f.comp (ContinuousLinearMap.mulLeftRight ℂ A p p)

omit [PartialOrder A] [StarOrderedRing A] in
@[simp] theorem cornerFunctional_apply (f : A →L[ℂ] ℂ) (p a : A) :
    cornerFunctional f p a = f (p * a * p) := rfl

def cornerState (f : A →L[ℂ] ℂ) (p : A) : A →L[ℂ] ℂ :=
  (f p).re⁻¹ • cornerFunctional f p

omit [PartialOrder A] [StarOrderedRing A] in
@[simp] theorem cornerState_apply (f : A →L[ℂ] ℂ) (p a : A) :
    cornerState f p a = (f p).re⁻¹ • f (p * a * p) := rfl

omit [PartialOrder A] [StarOrderedRing A] in
theorem state_projection_real (f : A →L[ℂ] ℂ) (hf : IsState f)
    (p : A) (hp : IsStarProjection p) : f p = ((f p).re : ℂ) := by
  apply Complex.ext
  · rfl
  · simpa only [hp.isSelfAdjoint.star_eq, hp.isIdempotentElem.eq, Complex.ofReal_im]
      using (hf.2 p).1

theorem cornerState_isState (f : A →L[ℂ] ℂ) (hf : IsState f)
    (p : A) (hp : IsStarProjection p) (hpos : 0 < (f p).re) : IsState (cornerState f p) := by
  apply (isState_iff _).mpr
  constructor
  · rw [cornerState_apply, mul_one, hp.isIdempotentElem.eq, state_projection_real f hf p hp]
    simp only [Complex.ofReal_re]
    rw [Complex.real_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ (ne_of_gt hpos), Complex.ofReal_one]
  · intro a
    have heq : p * (star a * a) * p = star (a * p) * (a * p) := by
      rw [star_mul, hp.isSelfAdjoint.star_eq]
      noncomm_ring
    rw [cornerState_apply, heq]
    simp only [Complex.smul_im, Complex.smul_re, smul_eq_mul,
      (hf.2 (a * p)).1, mul_zero, true_and]
    exact mul_nonneg (inv_nonneg.mpr (le_of_lt hpos)) (hf.2 (a * p)).2

theorem cornerState_eq_one (f : A →L[ℂ] ℂ) (hf : IsState f)
    (q p : A) (hq : IsStarProjection q) (hp : IsStarProjection p) (hqp : q ≤ p)
    (hpos : 0 < (f q).re) : cornerState f q p = 1 := by
  rw [cornerState_apply, (hq.le_iff_mul_eq_left hp).mp hqp, hq.isIdempotentElem.eq,
    state_projection_real f hf q hq]
  simp only [Complex.ofReal_re]
  rw [Complex.real_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ (ne_of_gt hpos), Complex.ofReal_one]

def peakAtom (p : ℕ → A) (n : ℕ) : A := p n - p (n + 1)

theorem Peaks.peakAtom_projection {p : ℕ → A} {f : A →L[ℂ] ℂ} (hp : Peaks p f) (n : ℕ) :
    IsStarProjection (peakAtom p n) :=
  ((hp.1 (n+1)).le_iff_sub (hp.1 n)).mp (hp.2.1 (Nat.le_succ n))

theorem Peaks.peakAtom_le {p : ℕ → A} {f : A →L[ℂ] ℂ} (hp : Peaks p f) (n : ℕ) :
    peakAtom p n ≤ p n := by
  exact sub_le_self _ (hp.1 (n+1)).nonneg

theorem Peaks.tendsto_atomState {p : ℕ → A} {f : A →L[ℂ] ℂ} (hp : Peaks p f)
    (τ : A →L[ℂ] ℂ) (hτ : IsState τ) (hpos : ∀ n, 0 < (τ (peakAtom p n)).re) (a : A) :
    Tendsto (fun n => cornerState τ (peakAtom p n) a) atTop (𝓝 (f a)) := by
  apply hp.tendsto_supported_apply
  · intro n
    exact cornerState_isState τ hτ _ (hp.peakAtom_projection n) (hpos n)
  · intro n
    exact cornerState_eq_one τ hτ _ _ (hp.peakAtom_projection n) (hp.1 n)
      (hp.peakAtom_le n) (hpos n)

open scoped ComplexOrder ComplexStarModule
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem selfAdjoint_nonneg_of_norm_one (g : selfAdjoint A →L[ℝ] ℝ)
    (hg : ‖g‖ ≤ 1) (h1 : g 1 = 1) (a : selfAdjoint A) (ha : 0 ≤ (a : A)) :
    0 ≤ g a := by
  have hau : (a : A) ≤ ‖a‖ • (1 : A) := by
    change (a : A) ≤ ‖(a : A)‖ • (1 : A)
    simpa only [Algebra.algebraMap_eq_smul_one] using
      (CStarAlgebra.norm_le_iff_le_algebraMap (a : A) (norm_nonneg _) ha).mp le_rfl
  have hpos : 0 ≤ ‖a‖ • (1 : A) - (a : A) := sub_nonneg.mpr hau
  have hnorm : ‖‖a‖ • (1 : selfAdjoint A) - a‖ ≤ ‖a‖ := by
    change ‖‖a‖ • (1 : A) - (a : A)‖ ≤ ‖a‖
    apply (CStarAlgebra.norm_le_iff_le_algebraMap _ (norm_nonneg _) hpos).mpr
    simpa only [Algebra.algebraMap_eq_smul_one] using sub_le_self (‖a‖ • (1 : A)) ha
  have hb := g.le_opNorm (‖a‖ • (1 : selfAdjoint A) - a)
  have hc : ‖g (‖a‖ • (1 : selfAdjoint A) - a)‖ ≤ ‖a‖ :=
    hb.trans ((mul_le_mul_of_nonneg_right hg (norm_nonneg _)).trans (by simpa using hnorm))
  rw [map_sub, map_smul, h1, smul_eq_mul, mul_one, Real.norm_eq_abs] at hc
  have h := (le_abs_self _).trans hc
  linarith

def selfAdjointComplexify (g : selfAdjoint A →ₗ[ℝ] ℝ) : A →ₗ[ℂ] ℂ where
  toFun a := (g (realPart a) : ℂ) + Complex.I * (g (imaginaryPart a) : ℂ)
  map_add' a b := by simp only [map_add, Complex.ofReal_add, mul_add]; ring
  map_smul' z a := by
    simp only [realPart_smul, imaginaryPart_smul, map_sub, map_add, map_smul,
      Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_mul, smul_eq_mul]
    apply Complex.ext <;> simp

omit [PartialOrder A] [StarOrderedRing A] in
@[simp] theorem selfAdjointComplexify_coe (g : selfAdjoint A →ₗ[ℝ] ℝ) (a : selfAdjoint A) :
    selfAdjointComplexify g (a : A) = (g a : ℂ) := by
  simp [selfAdjointComplexify]

def selfAdjointPositive (g : selfAdjoint A →L[ℝ] ℝ) (hg : ‖g‖ ≤ 1) (h1 : g 1 = 1) :
    A →ₚ[ℂ] ℂ :=
  PositiveLinearMap.mk₀ (selfAdjointComplexify g.toLinearMap) fun a ha => by
    let x : selfAdjoint A := ⟨a, ha.isSelfAdjoint⟩
    change 0 ≤ selfAdjointComplexify g.toLinearMap (x : A)
    rw [selfAdjointComplexify_coe]
    exact ⟨selfAdjoint_nonneg_of_norm_one g hg h1 x ha, by simp⟩

@[simp] theorem selfAdjointPositive_coe (g : selfAdjoint A →L[ℝ] ℝ)
    (hg : ‖g‖ ≤ 1) (h1 : g 1 = 1) (a : selfAdjoint A) :
    selfAdjointPositive g hg h1 (a : A) = (g a : ℂ) :=
  selfAdjointComplexify_coe _ _

@[simp] theorem selfAdjointPositive_one (g : selfAdjoint A →L[ℝ] ℝ)
    (hg : ‖g‖ ≤ 1) (h1 : g 1 = 1) : selfAdjointPositive g hg h1 1 = 1 := by
  simpa only [selfAdjoint.val_one, h1, Complex.ofReal_one] using selfAdjointPositive_coe g hg h1 1

open scoped ComplexOrder InnerProductSpace ComplexStarModule
open UniformSpace

open scoped Topology
open Filter

variable {A : Type*} [CStarAlgebra A] {ι : Type*}

theorem orthogonalProjection_commute (p : ι → A)
    (horth : Pairwise (fun i j => p i * p j = 0)) (i j : ι) : Commute (p i) (p j) := by
  by_cases h : i = j
  · subst j; exact Commute.refl _
  · exact (horth h).trans (horth (Ne.symm h)).symm

theorem normal_orthogonalProjection_sum (p : ι → A) (hp : ∀ i, IsStarProjection (p i))
    (horth : Pairwise (fun i j => p i * p j = 0)) (c : ι → ℂ) (s : Finset ι) :
    IsStarNormal (∑ i ∈ s, c i • p i) := by
  constructor
  rw [star_sum]
  apply Commute.sum_left
  intro i hi
  apply Commute.sum_right
  intro j hj
  rw [star_smul, (hp i).isSelfAdjoint.star_eq]
  exact (orthogonalProjection_commute p horth i j).smul_left (star (c i)) |>.smul_right (c j)

theorem norm_orthogonalProjection_sum_le (p : ι → A) (hp : ∀ i, IsStarProjection (p i))
    (horth : Pairwise (fun i j => p i * p j = 0)) (c : ι → ℂ) (s : Finset ι)
    (C : ℝ) (hC : 0 ≤ C) (hc : ∀ i ∈ s, ‖c i‖ ≤ C) : ‖∑ i ∈ s, c i • p i‖ ≤ C := by
  classical
  induction s using Finset.induction with
  | empty => simpa using hC
  | @insert i s his ih =>
    rw [Finset.sum_insert his]
    have hn : IsStarNormal (c i • p i) := by
      let : IsStarNormal (p i) := (hp i).isSelfAdjoint.isStarNormal
      infer_instance
    have hs := normal_orthogonalProjection_sum p hp horth c s
    have hab : (c i • p i) * (∑ j ∈ s, c j • p j) = 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_eq_zero
      intro j hj
      simp only [smul_mul_assoc, mul_smul_comm, horth (ne_of_mem_of_not_mem hj his).symm,
        smul_zero]
    have hcomm : Commute (c i • p i) (∑ j ∈ s, c j • p j) := by
      apply Commute.sum_right
      intro j hj
      exact (orthogonalProjection_commute p horth i j).smul_left _ |>.smul_right _
    rw [hn.norm_add_eq_max hs hcomm hab]
    apply max_le
    · calc
        ‖c i • p i‖ = ‖c i‖ * ‖p i‖ := norm_smul _ _
        _ ≤ ‖c i‖ * 1 := mul_le_mul_of_nonneg_left ((hp i).norm_le _) (norm_nonneg _)
        _ ≤ C := by simpa using hc i (Finset.mem_insert_self _ _)
    · exact ih (fun j hj => hc j (Finset.mem_insert_of_mem hj))

theorem summable_orthogonalProjection (p : ℕ → A) (hp : ∀ i, IsStarProjection (p i))
    (horth : Pairwise (fun i j => p i * p j = 0)) (c : ℕ → ℂ)
    (hc : Tendsto c atTop (𝓝 0)) : Summable (fun i => c i • p i) := by
  apply summable_iff_vanishing_norm.mpr
  intro ε hε
  have hsmall := (tendsto_zero_iff_norm_tendsto_zero.mp hc).eventually
    (Iio_mem_nhds (half_pos hε))
  obtain ⟨N, hN⟩ := eventually_atTop.mp hsmall
  refine ⟨Finset.range N, fun s hs => ?_⟩
  apply lt_of_le_of_lt (norm_orthogonalProjection_sum_le p hp horth c s (ε/2)
    (le_of_lt (half_pos hε)) ?_) (half_lt_self hε)
  intro i hi
  apply le_of_lt (hN i _)
  by_contra h
  have hin : i ∈ Finset.range N := Finset.mem_range.mpr (lt_of_not_ge h)
  exact Finset.disjoint_left.mp hs hi hin

theorem orthogonalProjection_mul_tsum (p : ℕ → A) (hp : ∀ i, IsStarProjection (p i))
    (horth : Pairwise (fun i j => p i * p j = 0)) (c : ℕ → ℂ)
    (hc : Tendsto c atTop (𝓝 0)) (k : ℕ) :
    p k * (∑' i, c i • p i) = c k • p k := by
  rw [← (summable_orthogonalProjection p hp horth c hc).tsum_mul_left]
  apply Eq.trans (tsum_eq_single k ?_) ?_
  · intro i hik
    simp only [mul_smul_comm, horth (Ne.symm hik), smul_zero]
  · rw [mul_smul_comm, (hp k).isIdempotentElem.eq]

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem Peaks.peakAtom_mul_peak {p : ℕ → A} {f : A →L[ℂ] ℂ} (hp : Peaks p f)
    {i n : ℕ} (hin : i < n) : peakAtom p i * p n = 0 := by
  have h₁ := ((hp.1 n).le_iff_mul_eq_right (hp.1 i)).mp (hp.2.1 (Nat.le_of_lt hin))
  have h₂ := ((hp.1 n).le_iff_mul_eq_right (hp.1 (i+1))).mp (hp.2.1 hin)
  simp only [peakAtom, sub_mul, h₁, h₂, sub_self]

theorem Peaks.peak_mul_peakAtom {p : ℕ → A} {f : A →L[ℂ] ℂ} (hp : Peaks p f)
    {i n : ℕ} (hin : i < n) : p n * peakAtom p i = 0 := by
  simpa only [star_mul, (hp.1 n).isSelfAdjoint.star_eq,
    (hp.peakAtom_projection i).isSelfAdjoint.star_eq, star_zero]
    using congrArg star (hp.peakAtom_mul_peak hin)

theorem Peaks.peakAtom_orthogonal {p : ℕ → A} {f : A →L[ℂ] ℂ} (hp : Peaks p f) :
    Pairwise (fun i j => peakAtom p i * peakAtom p j = 0) := by
  intro i j hij
  rcases lt_or_gt_of_ne hij with h | h
  · change peakAtom p i * (p j - p (j+1)) = 0
    rw [mul_sub, hp.peakAtom_mul_peak h, hp.peakAtom_mul_peak (h.trans_le (Nat.le_succ j)),
      sub_self]
  · change (p i - p (i+1)) * peakAtom p j = 0
    rw [sub_mul, hp.peak_mul_peakAtom h, hp.peak_mul_peakAtom (h.trans_le (Nat.le_succ i)),
      sub_self]

omit [PartialOrder A] [StarOrderedRing A] in

theorem peakAtom_sum (p : ℕ → A) (n : ℕ) :
    ∑ i ∈ Finset.range n, peakAtom p i = p 0 - p n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih, peakAtom]; abel

def peakDiagonal (p : ℕ → A) (c : ℂ) (b : ℕ → ℂ) : A :=
  c • (1 : A) + ∑' i, (b i - c) • peakAtom p i

omit [PartialOrder A] [StarOrderedRing A] in

theorem peakDiagonal_partial {p : ℕ → A} (hp0 : p 0 = 1)
    (c : ℂ) (b : ℕ → ℂ) (n : ℕ) :
    c • (1 : A) + ∑ i ∈ Finset.range n, (b i - c) • peakAtom p i =
      (∑ i ∈ Finset.range n, b i • peakAtom p i) + c • p n := by
  simp_rw [sub_smul]
  rw [Finset.sum_sub_distrib, ← Finset.smul_sum, peakAtom_sum, hp0, smul_sub]
  abel

theorem Peaks.norm_peakDiagonal_partial_le {p : ℕ → A} {f : A →L[ℂ] ℂ} (hp : Peaks p f)
    (hp0 : p 0 = 1) (c : ℂ) (b : ℕ → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hc : ‖c‖ ≤ C) (hb : ∀ i, ‖b i‖ ≤ C) (n : ℕ) :
    ‖c • (1 : A) + ∑ i ∈ Finset.range n, (b i - c) • peakAtom p i‖ ≤ C := by
  rw [peakDiagonal_partial hp0]
  have hs := normal_orthogonalProjection_sum _ hp.peakAtom_projection hp.peakAtom_orthogonal
    b (Finset.range n)
  have hn : IsStarNormal (c • p n) := by
    let : IsStarNormal (p n) := (hp.1 n).isSelfAdjoint.isStarNormal
    infer_instance
  have hzero : (∑ i ∈ Finset.range n, b i • peakAtom p i) * (c • p n) = 0 := by
    rw [Finset.sum_mul]
    apply Finset.sum_eq_zero
    intro i hi
    simp only [smul_mul_assoc, mul_smul_comm, hp.peakAtom_mul_peak (Finset.mem_range.mp hi),
      smul_zero]
  have hzero' : (c • p n) * (∑ i ∈ Finset.range n, b i • peakAtom p i) = 0 := by
    rw [Finset.mul_sum]
    apply Finset.sum_eq_zero
    intro i hi
    simp only [smul_mul_assoc, mul_smul_comm, hp.peak_mul_peakAtom (Finset.mem_range.mp hi),
      smul_zero]
  rw [hs.norm_add_eq_max hn (hzero.trans hzero'.symm) hzero]
  apply max_le
  · exact norm_orthogonalProjection_sum_le _ hp.peakAtom_projection hp.peakAtom_orthogonal
      b _ C hC (fun i _ => hb i)
  · calc
      ‖c • p n‖ = ‖c‖ * ‖p n‖ := norm_smul _ _
      _ ≤ ‖c‖ * 1 := mul_le_mul_of_nonneg_left ((hp.1 n).norm_le _) (norm_nonneg _)
      _ ≤ C := by simpa using hc

theorem Peaks.tendsto_peakDiagonal {p : ℕ → A} {f : A →L[ℂ] ℂ} (hp : Peaks p f)
    (c : ℂ) (b : ℕ → ℂ) (hb : Tendsto b atTop (𝓝 c)) :
    Tendsto (fun n => c • (1 : A) + ∑ i ∈ Finset.range n, (b i - c) • peakAtom p i)
      atTop (𝓝 (peakDiagonal p c b)) := by
  apply tendsto_const_nhds.add
  exact (summable_orthogonalProjection _ hp.peakAtom_projection hp.peakAtom_orthogonal
    (fun i => b i - c) (by simpa using hb.sub_const c)).hasSum.tendsto_sum_nat

theorem Peaks.norm_peakDiagonal_le {p : ℕ → A} {f : A →L[ℂ] ℂ} (hp : Peaks p f)
    (hp0 : p 0 = 1) (c : ℂ) (b : ℕ → ℂ) (hb : Tendsto b atTop (𝓝 c))
    (C : ℝ) (hC : 0 ≤ C) (hc : ‖c‖ ≤ C) (hbc : ∀ i, ‖b i‖ ≤ C) :
    ‖peakDiagonal p c b‖ ≤ C := by
  apply le_of_tendsto (hp.tendsto_peakDiagonal c b hb).norm
  exact Filter.Eventually.of_forall (hp.norm_peakDiagonal_partial_le hp0 c b C hC hc hbc)

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem Peaks.summable_expectationTail {p : ℕ → A} {f : A →L[ℂ] ℂ} (hp : Peaks p f)
    (τ : A →L[ℂ] ℂ) (hτ : IsState τ) (hpos : ∀ n, 0 < (τ (peakAtom p n)).re) (a : A) :
    Summable (fun n => (cornerState τ (peakAtom p n) a - f a) • peakAtom p n) :=
  summable_orthogonalProjection _ hp.peakAtom_projection hp.peakAtom_orthogonal _
    (by simpa using (hp.tendsto_atomState τ hτ hpos a).sub_const (f a))

def peakingExpectationFun (p : ℕ → A) (f τ : A →L[ℂ] ℂ) (a : A) : A :=
  peakDiagonal p (f a) (fun n => cornerState τ (peakAtom p n) a)

theorem Peaks.peakingExpectationFun_add {p : ℕ → A} {f : A →L[ℂ] ℂ} (hp : Peaks p f)
    (τ : A →L[ℂ] ℂ) (hτ : IsState τ) (hpos : ∀ n, 0 < (τ (peakAtom p n)).re) (a b : A) :
    peakingExpectationFun p f τ (a + b) =
      peakingExpectationFun p f τ a + peakingExpectationFun p f τ b := by
  have heq (n : ℕ) :
      (cornerState τ (peakAtom p n) (a+b) - f (a+b)) • peakAtom p n =
        (cornerState τ (peakAtom p n) a - f a) • peakAtom p n +
        (cornerState τ (peakAtom p n) b - f b) • peakAtom p n := by
    rw [map_add, map_add, add_sub_add_comm, add_smul]
  simp only [peakingExpectationFun, peakDiagonal]
  simp_rw [heq]
  rw [(hp.summable_expectationTail τ hτ hpos a).tsum_add
    (hp.summable_expectationTail τ hτ hpos b), map_add, add_smul]
  abel

omit [PartialOrder A] [StarOrderedRing A] in

theorem peakingExpectationFun_smul (p : ℕ → A) (f τ : A →L[ℂ] ℂ) (c : ℂ) (a : A) :
    peakingExpectationFun p f τ (c • a) = c • peakingExpectationFun p f τ a := by
  simp only [peakingExpectationFun, peakDiagonal, map_smul, ← smul_sub]
  simp_rw [smul_assoc]
  rw [tsum_const_smul'', smul_add]

theorem Peaks.norm_peakingExpectationFun_le {p : ℕ → A} {f : A →L[ℂ] ℂ} (hp : Peaks p f)
    (hp0 : p 0 = 1) (τ : A →L[ℂ] ℂ) (hτ : IsState τ)
    (hpos : ∀ n, 0 < (τ (peakAtom p n)).re) (a : A) :
    ‖peakingExpectationFun p f τ a‖ ≤ ‖a‖ := by
  exact hp.norm_peakDiagonal_le hp0 _ _ (hp.tendsto_atomState τ hτ hpos a) _ (norm_nonneg _)
    (state_norm_apply_le _ hp.2.2.1 _)
    (fun n => state_norm_apply_le _ (cornerState_isState _ hτ _ (hp.peakAtom_projection n)
      (hpos n)) _)

def peakingExpectation {p : ℕ → A} {f : A →L[ℂ] ℂ} (hp : Peaks p f)
    (hp0 : p 0 = 1) (τ : A →L[ℂ] ℂ) (hτ : IsState τ)
    (hpos : ∀ n, 0 < (τ (peakAtom p n)).re) : A →L[ℂ] A :=
  LinearMap.mkContinuous
    { toFun := peakingExpectationFun p f τ
      map_add' := hp.peakingExpectationFun_add τ hτ hpos
      map_smul' := peakingExpectationFun_smul p f τ }
    1 (fun a => by
      change ‖peakingExpectationFun p f τ a‖ ≤ 1 * ‖a‖
      simpa only [one_mul] using hp.norm_peakingExpectationFun_le hp0 τ hτ hpos a)

@[simp] theorem peakingExpectation_apply {p : ℕ → A} {f : A →L[ℂ] ℂ} (hp : Peaks p f)
    (hp0 : p 0 = 1) (τ : A →L[ℂ] ℂ) (hτ : IsState τ)
    (hpos : ∀ n, 0 < (τ (peakAtom p n)).re) (a : A) :
    peakingExpectation hp hp0 τ hτ hpos a = peakingExpectationFun p f τ a := rfl

theorem peakingExpectation_one {p : ℕ → A} {f : A →L[ℂ] ℂ} (hp : Peaks p f)
    (hp0 : p 0 = 1) (τ : A →L[ℂ] ℂ) (hτ : IsState τ)
    (hpos : ∀ n, 0 < (τ (peakAtom p n)).re) :
    peakingExpectation hp hp0 τ hτ hpos 1 = 1 := by
  have hf1 := ((isState_iff f).mp hp.2.2.1).1
  have hc1 (n : ℕ) := ((isState_iff _).mp
    (cornerState_isState _ hτ _ (hp.peakAtom_projection n) (hpos n))).1
  simp only [peakingExpectation_apply, peakingExpectationFun, peakDiagonal, hf1, hc1,
    sub_self, zero_smul, tsum_zero, add_zero, one_smul]

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem Peaks.mul_peak {p : ℕ → A} {f : A →L[ℂ] ℂ} (hp : Peaks p f) (m n : ℕ) :
    p m * p n = p (max m n) := by
  rcases le_total m n with h | h
  · rw [max_eq_right h]
    exact ((hp.1 n).le_iff_mul_eq_right (hp.1 m)).mp (hp.2.1 h)
  · rw [max_eq_left h]
    exact ((hp.1 m).le_iff_mul_eq_left (hp.1 n)).mp (hp.2.1 h)

def peakSpanAlgebra {p : ℕ → A} {f : A →L[ℂ] ℂ} (hp : Peaks p f) (hp0 : p 0 = 1) :
    StarSubalgebra ℂ A where
  carrier := Submodule.span ℂ (Set.range p)
  zero_mem' := Submodule.zero_mem _
  add_mem' := Submodule.add_mem _
  algebraMap_mem' c := by
    rw [Algebra.algebraMap_eq_smul_one]
    apply Submodule.smul_mem
    exact Submodule.subset_span ⟨0, hp0⟩
  mul_mem' := by
    intro a b ha hb
    induction ha using Submodule.span_induction with
    | mem a ha =>
      obtain ⟨m, rfl⟩ := ha
      induction hb using Submodule.span_induction with
      | mem b hb =>
        obtain ⟨n, rfl⟩ := hb
        rw [hp.mul_peak]
        exact Submodule.subset_span (Set.mem_range_self _)
      | zero => simp only [mul_zero]; exact Submodule.zero_mem _
      | add b c _ _ hb hc => rw [mul_add]; exact Submodule.add_mem _ hb hc
      | smul c b _ hb => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hb
    | zero => rw [zero_mul]; exact Submodule.zero_mem _
    | add a c _ _ ha hc => rw [add_mul]; exact Submodule.add_mem _ ha hc
    | smul c a _ ha => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c ha
  star_mem' := by
    intro a ha
    induction ha using Submodule.span_induction with
    | mem a ha =>
      obtain ⟨n, rfl⟩ := ha
      rw [(hp.1 n).isSelfAdjoint.star_eq]
      exact Submodule.subset_span (Set.mem_range_self _)
    | zero => rw [star_zero]; exact Submodule.zero_mem _
    | add a b _ _ ha hb => rw [star_add]; exact Submodule.add_mem _ ha hb
    | smul c a _ ha => rw [star_smul]; exact Submodule.smul_mem _ (star c) ha

omit [PartialOrder A] [StarOrderedRing A] in

def peakAlgebra (p : ℕ → A) : StarSubalgebra ℂ A :=
  (StarAlgebra.adjoin ℂ (Set.range p)).topologicalClosure

omit [PartialOrder A] [StarOrderedRing A] in
theorem peak_mem_peakAlgebra (p : ℕ → A) (n : ℕ) : p n ∈ peakAlgebra p :=
  StarSubalgebra.le_topologicalClosure _ (StarAlgebra.subset_adjoin ℂ _ (Set.mem_range_self n))

omit [PartialOrder A] [StarOrderedRing A] in
theorem peakAtom_mem_peakAlgebra (p : ℕ → A) (n : ℕ) : peakAtom p n ∈ peakAlgebra p :=
  (peakAlgebra p).sub_mem (peak_mem_peakAlgebra p n) (peak_mem_peakAlgebra p (n+1))

theorem peakAlgebra_eq_spanClosure {p : ℕ → A} {f : A →L[ℂ] ℂ} (hp : Peaks p f)
    (hp0 : p 0 = 1) : peakAlgebra p = (peakSpanAlgebra hp hp0).topologicalClosure := by
  apply le_antisymm
  · apply StarSubalgebra.topologicalClosure_mono
    apply StarAlgebra.adjoin_le
    intro a ha
    exact Submodule.subset_span ha
  · apply StarSubalgebra.topologicalClosure_minimal _ (StarSubalgebra.isClosed_topologicalClosure _)
    intro a ha
    have hs : Submodule.span ℂ (Set.range p) ≤ (peakAlgebra p).toSubmodule := by
      apply Submodule.span_le.mpr
      intro x hx
      exact StarSubalgebra.le_topologicalClosure _ (StarAlgebra.subset_adjoin ℂ _ hx)
    exact hs ha

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

omit [StarOrderedRing A] in

theorem Peaks.apply_peakAtom {p : ℕ → A} {f : A →L[ℂ] ℂ} (hp : Peaks p f) (n : ℕ) :
    f (peakAtom p n) = 0 := by
  simp only [peakAtom, map_sub, hp.2.2.2.1, sub_self]

theorem cornerState_peakAtom_of_ne {p : ℕ → A} {f : A →L[ℂ] ℂ} (hp : Peaks p f)
    (τ : A →L[ℂ] ℂ) {n m : ℕ} (hnm : n ≠ m) :
    cornerState τ (peakAtom p n) (peakAtom p m) = 0 := by
  simp only [cornerState_apply, hp.peakAtom_orthogonal hnm, zero_mul, map_zero, smul_zero]

theorem peakingExpectation_peakAtom {p : ℕ → A} {f : A →L[ℂ] ℂ} (hp : Peaks p f)
    (hp0 : p 0 = 1) (τ : A →L[ℂ] ℂ) (hτ : IsState τ)
    (hpos : ∀ n, 0 < (τ (peakAtom p n)).re) (m : ℕ) :
    peakingExpectation hp hp0 τ hτ hpos (peakAtom p m) = peakAtom p m := by
  change peakDiagonal p (f (peakAtom p m)) (fun n => cornerState τ (peakAtom p n) (peakAtom p m)) = _
  rw [peakDiagonal, hp.apply_peakAtom]
  simp only [zero_smul, zero_add, sub_zero]
  rw [tsum_eq_single m]
  · rw [cornerState_eq_one τ hτ _ _ (hp.peakAtom_projection m) (hp.peakAtom_projection m) le_rfl (hpos m), one_smul]
  · intro n hnm
    rw [cornerState_peakAtom_of_ne hp τ hnm, zero_smul]

theorem peakingExpectation_peak {p : ℕ → A} {f : A →L[ℂ] ℂ} (hp : Peaks p f)
    (hp0 : p 0 = 1) (τ : A →L[ℂ] ℂ) (hτ : IsState τ)
    (hpos : ∀ n, 0 < (τ (peakAtom p n)).re) (m : ℕ) :
    peakingExpectation hp hp0 τ hτ hpos (p m) = p m := by
  have hm : p m = 1 - ∑ i ∈ Finset.range m, peakAtom p i := by
    rw [peakAtom_sum, hp0]; abel
  calc
    peakingExpectation hp hp0 τ hτ hpos (p m) =
        1 - ∑ i ∈ Finset.range m, peakAtom p i := by
      conv_lhs => rw [hm]
      rw [map_sub, map_sum, peakingExpectation_one hp hp0 τ hτ hpos]
      simp_rw [peakingExpectation_peakAtom hp hp0 τ hτ hpos]
    _ = p m := hm.symm

theorem peakingExpectation_fixes {p : ℕ → A} {f : A →L[ℂ] ℂ} (hp : Peaks p f)
    (hp0 : p 0 = 1) (τ : A →L[ℂ] ℂ) (hτ : IsState τ)
    (hpos : ∀ n, 0 < (τ (peakAtom p n)).re) (a : A) (ha : a ∈ peakAlgebra p) :
    peakingExpectation hp hp0 τ hτ hpos a = a := by
  rw [peakAlgebra_eq_spanClosure hp hp0] at ha
  have hc : IsClosed {a : A | peakingExpectation hp hp0 τ hτ hpos a = a} :=
    isClosed_eq (peakingExpectation hp hp0 τ hτ hpos).continuous continuous_id
  apply closure_minimal (t := {a : A | peakingExpectation hp hp0 τ hτ hpos a = a}) ?_ hc ha
  intro a ha
  change a ∈ Submodule.span ℂ (Set.range p) at ha
  induction ha using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨n, rfl⟩ := ha
    exact peakingExpectation_peak hp hp0 τ hτ hpos n
  | zero => exact map_zero _
  | add a b _ _ ha hb =>
    change _ = _ at ha hb ⊢
    rw [map_add, ha, hb]
  | smul c a _ ha =>
    change _ = _ at ha ⊢
    rw [map_smul, ha]

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem Peaks.apply_peakAtom_mul {p : ℕ → A} {f : A →L[ℂ] ℂ} (hp : Peaks p f)
    (n : ℕ) (a : A) : f (peakAtom p n * a) = 0 := by
  have hc := state_compression f hp.2.2.1 (p (n+1)) ((hp.1 _).norm_le _)
    (hp.1 _).isSelfAdjoint (hp.2.2.2.1 _) (peakAtom p n*a)
  have hmul : p (n+1)*peakAtom p n=0 := by
    have h := congrArg star (hp.peakAtom_mul_peak (Nat.lt_succ_self n))
    simpa [(hp.1 _).isSelfAdjoint.star_eq, (hp.peakAtom_projection n).isSelfAdjoint.star_eq] using h
  rw [← hc, ← mul_assoc (p (n+1)), hmul, zero_mul, zero_mul, map_zero]

theorem peakingExpectation_peakAtom_mul {p : ℕ → A} {f : A →L[ℂ] ℂ} (hp : Peaks p f)
    (hp0 : p 0 = 1) (τ : A →L[ℂ] ℂ) (hτ : IsState τ)
    (hpos : ∀ n, 0 < (τ (peakAtom p n)).re) (m : ℕ) (a : A) :
    peakingExpectation hp hp0 τ hτ hpos (peakAtom p m*a) =
      cornerState τ (peakAtom p m) a • peakAtom p m := by
  change peakDiagonal p (f (peakAtom p m*a)) (fun n => cornerState τ (peakAtom p n) (peakAtom p m*a)) = _
  rw [peakDiagonal, hp.apply_peakAtom_mul]
  simp only [zero_smul, zero_add, sub_zero]
  rw [tsum_eq_single m]
  · congr 1
    simp only [cornerState_apply, ← mul_assoc, (hp.peakAtom_projection m).isIdempotentElem.eq]
  · intro n hnm
    simp only [cornerState_apply, ← mul_assoc, hp.peakAtom_orthogonal hnm, zero_mul, map_zero, smul_zero,
      zero_smul]

theorem peakAtom_mul_peakingExpectation {p : ℕ → A} {f : A →L[ℂ] ℂ} (hp : Peaks p f)
    (hp0 : p 0 = 1) (τ : A →L[ℂ] ℂ) (hτ : IsState τ)
    (hpos : ∀ n, 0 < (τ (peakAtom p n)).re) (m : ℕ) (a : A) :
    peakAtom p m * peakingExpectation hp hp0 τ hτ hpos a =
      cornerState τ (peakAtom p m) a • peakAtom p m := by
  change peakAtom p m * (f a • (1 : A) + ∑' n,
    (cornerState τ (peakAtom p n) a - f a) • peakAtom p n) = _
  rw [mul_add, mul_smul_comm, mul_one]
  have hsum := (hp.summable_expectationTail τ hτ hpos a).hasSum.map
    (ContinuousLinearMap.mul ℂ A (peakAtom p m)) (ContinuousLinearMap.mul ℂ A (peakAtom p m)).continuous
  have heq : peakAtom p m * ∑' n, (cornerState τ (peakAtom p n) a - f a) • peakAtom p n =
      (cornerState τ (peakAtom p m) a - f a) • peakAtom p m := by
    change HasSum (fun n => peakAtom p m * ((cornerState τ (peakAtom p n) a - f a) • peakAtom p n))
      (peakAtom p m * ∑' n, (cornerState τ (peakAtom p n) a - f a) • peakAtom p n) at hsum
    rw [← hsum.tsum_eq, tsum_eq_single m]
    · simp only [mul_smul_comm,
        (hp.peakAtom_projection m).isIdempotentElem.eq]
    · intro n hnm
      simp only [mul_smul_comm,
        hp.peakAtom_orthogonal hnm.symm, smul_zero]
  rw [heq, ← add_smul, add_sub_cancel]

open scoped ComplexOrder MatrixOrder CStarAlgebra
open Matrix

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

open scoped CStarAlgebra
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem peakingExpectation_peak_mul {p : ℕ → A} {f : A →L[ℂ] ℂ} (hp : Peaks p f)
    (hp0 : p 0 = 1) (τ : A →L[ℂ] ℂ) (hτ : IsState τ)
    (hpos : ∀ n, 0 < (τ (peakAtom p n)).re) (m : ℕ) (a : A) :
    peakingExpectation hp hp0 τ hτ hpos (p m*a) =
      p m*peakingExpectation hp hp0 τ hτ hpos a := by
  have hm : p m = 1 - ∑ i ∈ Finset.range m, peakAtom p i := by
    rw [peakAtom_sum, hp0]; abel
  have hq (n : ℕ) : peakingExpectation hp hp0 τ hτ hpos (peakAtom p n*a) =
      peakAtom p n*peakingExpectation hp hp0 τ hτ hpos a := by
    rw [peakingExpectation_peakAtom_mul, peakAtom_mul_peakingExpectation]
  rw [hm, sub_mul, sub_mul, one_mul, one_mul, Finset.sum_mul, Finset.sum_mul, map_sub, map_sum]
  simp_rw [hq]

theorem peakingExpectation_leftBimodule {p : ℕ → A} {f : A →L[ℂ] ℂ} (hp : Peaks p f)
    (hp0 : p 0 = 1) (τ : A →L[ℂ] ℂ) (hτ : IsState τ)
    (hpos : ∀ n, 0 < (τ (peakAtom p n)).re) (d a : A) (hd : d ∈ peakAlgebra p) :
    peakingExpectation hp hp0 τ hτ hpos (d*a) =
      d*peakingExpectation hp hp0 τ hτ hpos a := by
  rw [peakAlgebra_eq_spanClosure hp hp0] at hd
  have hc : IsClosed {d : A | peakingExpectation hp hp0 τ hτ hpos (d*a) =
      d*peakingExpectation hp hp0 τ hτ hpos a} := isClosed_eq (by fun_prop) (by fun_prop)
  apply closure_minimal (t := {d : A | peakingExpectation hp hp0 τ hτ hpos (d*a) =
      d*peakingExpectation hp hp0 τ hτ hpos a}) ?_ hc hd
  intro d hd
  change d ∈ Submodule.span ℂ (Set.range p) at hd
  induction hd using Submodule.span_induction with
  | mem d hd =>
    obtain ⟨n, rfl⟩ := hd
    exact peakingExpectation_peak_mul hp hp0 τ hτ hpos n a
  | zero => simp only [Set.mem_ofPred_eq, zero_mul, map_zero]
  | add d e _ _ hd he =>
    change _ = _ at hd he ⊢
    rw [add_mul, add_mul, map_add, hd, he]
  | smul c d _ hd =>
    change _ = _ at hd ⊢
    rw [smul_mul_assoc, smul_mul_assoc, map_smul, hd]

open Filter Topology
open scoped ComplexOrder ComplexStarModule

end NaimarkZFC

end

end OAI
end

section
-- module Solutions.OAIQ115_Naimark.Naimark_Representations
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

def diagonalOperator (T : H →L[ℂ] H) :
    PiLp 2 (fun _ : ι => H) →L[ℂ] PiLp 2 (fun _ : ι => H) :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι => H)).symm.toContinuousLinearMap.comp
    ((ContinuousLinearMap.piMap (fun _ : ι => T)).comp
      (PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι => H)).toContinuousLinearMap)

omit [CompleteSpace H] [Fintype ι] in
@[simp] theorem diagonalOperator_apply (T : H →L[ℂ] H)
    (x : PiLp 2 (fun _ : ι => H)) (i : ι) : diagonalOperator T x i = T (x i) := rfl

def coordinateInclusion [DecidableEq ι] (i : ι) :
    H →L[ℂ] PiLp 2 (fun _ : ι => H) :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι => H)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.single ℂ (fun _ : ι => H) i)

omit [CompleteSpace H] [Fintype ι] in
@[simp] theorem coordinateInclusion_apply [DecidableEq ι] (i : ι) (x : H) :
    coordinateInclusion i x = PiLp.single 2 i x := rfl

omit [CompleteSpace H] [Fintype ι] in
@[simp] theorem diagonalOperator_coordinateInclusion [DecidableEq ι]
    (T : H →L[ℂ] H) (i : ι) (x : H) :
    diagonalOperator T (coordinateInclusion i x) = coordinateInclusion i (T x) := by
  ext j
  simp only [diagonalOperator_apply, coordinateInclusion_apply, PiLp.single_apply]
  split_ifs <;> simp

def amplificationBlock [DecidableEq ι]
    (P : PiLp 2 (fun _ : ι => H) →L[ℂ] PiLp 2 (fun _ : ι => H)) (i j : ι) :
    H →L[ℂ] H :=
  (PiLp.proj 2 (fun _ : ι => H) i).comp (P.comp (coordinateInclusion j))

omit [CompleteSpace H] [Fintype ι] in
@[simp] theorem amplificationBlock_apply [DecidableEq ι]
    (P : PiLp 2 (fun _ : ι => H) →L[ℂ] PiLp 2 (fun _ : ι => H)) (i j : ι) (x : H) :
    amplificationBlock P i j x = P (coordinateInclusion j x) i := rfl

open scoped ComplexStarModule CStarAlgebra
variable {A : Type*} [CStarAlgebra A]

def saResolvent (a : A) (z : ℂ) : A := cfc (fun t : ℂ => (t - z)⁻¹) a

def saBoundedTransform (a : A) : A := saResolvent a Complex.I + saResolvent a (-Complex.I)

open scoped InnerProductSpace ComplexStarModule
variable {A : Type*} [CStarAlgebra A]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def irreducibleUnitalRepresentation
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hπ : IsIrreducible π) : A →⋆ₐ[ℂ] (H →L[ℂ] H) where
  toFun := π
  map_one' := irreducible_map_one π hπ
  map_zero' := map_zero π
  map_add' := map_add π
  map_mul' := map_mul π
  map_star' := map_star π
  commutes' z := by
    rw [Algebra.algebraMap_eq_smul_one, map_smul, irreducible_map_one π hπ,
      Algebra.algebraMap_eq_smul_one]

@[simp] theorem irreducibleUnitalRepresentation_apply
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hπ : IsIrreducible π) (a : A) :
    irreducibleUnitalRepresentation π hπ a = π a := rfl

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

open scoped InnerProductSpace ComplexStarModule CStarAlgebra ComplexOrder
universe u v w

variable {A : Type*} [CStarAlgebra A]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]

@[refl] theorem UnitarilyEquivalent.refl (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) :
    UnitarilyEquivalent π π := ⟨LinearIsometryEquiv.refl ℂ H, fun _ _ => rfl⟩

@[symm] theorem UnitarilyEquivalent.symm
    {π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)} {ρ : A →⋆ₙₐ[ℂ] (K →L[ℂ] K)}
    (h : UnitarilyEquivalent π ρ) : UnitarilyEquivalent ρ π := by
  obtain ⟨U, hU⟩ := h
  refine ⟨U.symm, fun a y => ?_⟩
  apply U.injective
  simpa only [U.apply_symm_apply] using (hU a (U.symm y)).symm

@[trans] theorem UnitarilyEquivalent.trans
    {π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)} {ρ : A →⋆ₙₐ[ℂ] (K →L[ℂ] K)}
    {σ : A →⋆ₙₐ[ℂ] (L →L[ℂ] L)}
    (h : UnitarilyEquivalent π ρ) (k : UnitarilyEquivalent ρ σ) :
    UnitarilyEquivalent π σ := by
  obtain ⟨U, hU⟩ := h
  obtain ⟨V, hV⟩ := k
  exact ⟨U.trans V, fun a x => by simp only [LinearIsometryEquiv.trans_apply, hU, hV]⟩

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

open scoped InnerProductSpace ComplexStarModule CStarAlgebra ComplexOrder
open Filter Topology
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

open Filter Topology
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

open Filter Topology

def ExcisionIndex (B : Type*) [NonUnitalCStarAlgebra B] [PartialOrder B]
    [StarOrderedRing B] := {b : B // 0 ≤ b ∧ ‖b‖ < 1}

namespace ExcisionIndex
variable {B : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
instance instPartialOrder : PartialOrder (ExcisionIndex B) := inferInstanceAs (PartialOrder {b : B // 0 ≤ b ∧ ‖b‖ < 1})
instance instInhabited : Inhabited (ExcisionIndex B) := ⟨⟨0, by simp⟩⟩

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

abbrev SequenceDiagonal := C(OnePoint ℕ, ℂ)
variable {p : ℕ → A} {f : A →L[ℂ] ℂ} (hp : Peaks p f) (hp0 : p 0 = 1)
variable (τ : A →L[ℂ] ℂ) (hτ : IsState τ) (hpos : ∀ n, 0 < (τ (peakAtom p n)).re)

def peakingCoefficientsFun (a : A) : SequenceDiagonal :=
  OnePoint.continuousMapMkNat (fun n => cornerState τ (peakAtom p n) a) (f a)
    (hp.tendsto_atomState τ hτ hpos a)

@[simp] theorem peakingCoefficientsFun_nat (a : A) (n : ℕ) :
    peakingCoefficientsFun hp τ hτ hpos a n = cornerState τ (peakAtom p n) a := rfl

@[simp] theorem peakingCoefficientsFun_infty (a : A) :
    peakingCoefficientsFun hp τ hτ hpos a ∞ = f a := rfl

theorem peakingCoefficientsFun_norm_le (a : A) :
    ‖peakingCoefficientsFun hp τ hτ hpos a‖ ≤ ‖a‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
  intro x
  induction x using OnePoint.rec with
  | infty => exact state_norm_apply_le _ hp.2.2.1 a
  | coe n =>
    exact state_norm_apply_le _
      (cornerState_isState τ hτ _ (hp.peakAtom_projection n) (hpos n)) a

def peakingCoefficients : A →L[ℂ] SequenceDiagonal :=
  LinearMap.mkContinuous
    { toFun := peakingCoefficientsFun hp τ hτ hpos
      map_add' a b := by
        ext x
        induction x using OnePoint.rec with
        | infty => exact map_add f a b
        | coe n => exact map_add (cornerState τ (peakAtom p n)) a b
      map_smul' z a := by
        ext x
        induction x using OnePoint.rec with
        | infty => exact f.map_smul z a
        | coe n => exact (cornerState τ (peakAtom p n)).map_smul z a }
    1 (fun a => by
      change ‖peakingCoefficientsFun hp τ hτ hpos a‖ ≤ 1 * ‖a‖
      simpa only [one_mul] using peakingCoefficientsFun_norm_le hp τ hτ hpos a)

@[simp] theorem peakingCoefficients_nat (a : A) (n : ℕ) :
    peakingCoefficients hp τ hτ hpos a n = cornerState τ (peakAtom p n) a := rfl

@[simp] theorem peakingCoefficients_infty (a : A) :
    peakingCoefficients hp τ hτ hpos a ∞ = f a := rfl

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {ι : Type*} {l : Filter ι}

open scoped InnerProductSpace ComplexStarModule CStarAlgebra ComplexOrder
open Filter Topology
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

open Filter Topology
open scoped ComplexOrder ComplexStarModule InnerProductSpace
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {ι : Type*} {l : Filter ι}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def pureGNS (f : A →L[ℂ] ℂ) (hf : IsPureState f) :=
  (positiveOfSquares f hf.1.2).gnsNonUnitalStarAlgHom

end NaimarkZFC

end

end OAI
end

section
-- module Solutions.OAIQ115_Naimark.Naimark_Amalgamation
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

def columnVertex {J : V → Type*} (r : V) : Option (Σ l, J l) → V
  | none => r
  | some ⟨l,_⟩ => l

open scoped InnerProductSpace lp
variable {A V : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

open Filter Topology
variable {A V : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

open Filter Topology
open scoped InnerProductSpace lp
variable {A V : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

attribute [local instance] Classical.propDecidable

open scoped InnerProductSpace ENNReal lp

variable {ι κ : Type*} {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H]

def hilbertBasisReindex (b : HilbertBasis ι ℂ H) (e : ι ≃ κ) : HilbertBasis κ ℂ H :=
  HilbertBasis.mk (b.orthonormal.comp e.symm e.symm.injective) (by
    have hr : Set.range (fun j => b (e.symm j)) = Set.range b := by
      rw [← Function.comp_def, Set.range_comp, e.symm.surjective.range_eq, Set.image_univ]
    simp only [Function.comp_def]
    rw [hr]
    exact b.dense_span.symm.le)

def l2Basis (ι : Type*) : HilbertBasis ι ℂ ℓ²(ι, ℂ) :=
  HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ _)

variable {ι : Type*} {J : ι → Type*} {H : ι → Type*}
  [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℂ (H i)]
  [∀ i, CompleteSpace (H i)]

open scoped InnerProductSpace ENNReal lp

variable {ι : Type*} {H K : ι → Type*}
  [∀ i, NormedAddCommGroup (H i)] [∀ i, NormedAddCommGroup (K i)]
  [∀ i, InnerProductSpace ℂ (H i)] [∀ i, InnerProductSpace ℂ (K i)]

variable [∀ i, CompleteSpace (H i)] [∀ i, CompleteSpace (K i)]

variable {A : Type*} [CStarAlgebra A]

open scoped InnerProductSpace ENNReal lp
variable {I V : Type*} (L : I → V → V → Type*) [DecidableEq I]

variable {A : I → Type*} [∀ i, CStarAlgebra (A i)]

open scoped InnerProductSpace lp
variable {I V : Type*} (L : I → V → V → Type*) [DecidableEq I]

variable {A : I → Type*} [∀ i, CStarAlgebra (A i)]

open scoped InnerProductSpace lp
variable {V J : Type*}

section
open scoped lp InnerProductSpace ENNReal
variable {V : Type*} (w : V → ℝ) (hw : ∀ r, 0 ≤ w r) (hm : HasSum w 1)

def atomicWeightVector : ℓ²(V, ℂ) := ⟨fun r => (Real.sqrt (w r) : ℂ), by
  apply memℓp_gen
  convert hm.summable using 1
  all_goals try with_reducible_and_instances rfl
  ext r
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (hw r)]⟩

end

open scoped InnerProductSpace ComplexOrder
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

section

variable {I B : Type*} [Ring B] [Algebra ℂ B]

structure IsCenteredWord (K : I → Submodule ℂ B) (w : List (I × B)) : Prop where
  centered : ∀ x ∈ w, x.2 ∈ K x.1
  alternating : w.IsChain (fun x y => x.1 ≠ y.1)

def wordValue (w : List (I × B)) : B := (w.map Prod.snd).prod

theorem IsCenteredWord.tail {K : I → Submodule ℂ B} {x : I × B} {w : List (I × B)}
    (h : IsCenteredWord K (x :: w)) : IsCenteredWord K w :=
  ⟨fun _ hx => h.centered _ (List.mem_cons_of_mem _ hx), h.alternating.tail⟩

theorem IsCenteredWord.modify_head {K : I → Submodule ℂ B}
    {x : I × B} {w : List (I × B)} (h : IsCenteredWord K (x :: w))
    {b : B} (hb : b ∈ K x.1) : IsCenteredWord K ((x.1, b) :: w) := by
  refine ⟨?_, List.IsChain.imp_head (x := x) (y := (x.1, b)) (fun hh => hh) h.alternating⟩
  intro y hy
  rcases List.mem_cons.mp hy with rfl | hy
  · exact hb
  · exact h.centered y (List.mem_cons_of_mem x hy)

theorem IsCenteredWord.prepend {K : I → Submodule ℂ B}
    {x : I × B} {w : List (I × B)} (h : IsCenteredWord K (x :: w))
    {i : I} {b : B} (hb : b ∈ K i) (hi : i ≠ x.1) :
    IsCenteredWord K ((i, b) :: x :: w) := by
  refine ⟨?_, List.isChain_cons_cons.mpr ⟨hi, h.alternating⟩⟩
  intro y hy
  rcases List.mem_cons.mp hy with rfl | hy
  · exact hb
  · exact h.centered y hy

variable (D : NonUnitalSubalgebra ℂ B) (F : I → NonUnitalSubalgebra ℂ B) (K : I → Submodule ℂ B)

structure CenteredDecomposition : Prop where
  diagonal_le : ∀ i, D ≤ F i
  centered_le : ∀ i, K i ≤ (F i).toSubmodule
  decompose : ∀ i a, a ∈ F i → ∃ d ∈ D, ∃ c ∈ K i, a = d + c
  diagonal_mul : ∀ i d c, d ∈ D → c ∈ K i → d * c ∈ K i

variable {D F K}

def leftStabilizer (W : Submodule ℂ B) : Subalgebra ℂ B where
  carrier := {a | ∀ w ∈ W, a * w ∈ W}
  mul_mem' ha hb w hw := by simpa only [mul_assoc] using ha _ (hb w hw)
  add_mem' ha hb w hw := by simpa only [add_mul] using W.add_mem (ha w hw) (hb w hw)
  algebraMap_mem' c w hw := by simpa only [Algebra.smul_def] using W.smul_mem c hw

variable (φ : B →ₗ[ℂ] ℂ)
variable (hfree : ∀ w, IsCenteredWord K w → w ≠ [] → φ (wordValue w) = 0)

include hfree

omit hfree

variable [StarRing B]

def starWord (w : List (I × B)) : List (I × B) :=
  w.reverse.map (fun x => (x.1, star x.2))

end

section

variable {V B : Type*} [Ring B] [Algebra ℂ B]

variable (q : V → B)
variable (hq : ∀ r, q r * q r = q r)
variable (ho : ∀ r t, r ≠ t → q r * q t = 0)

def finiteAtomicSpan (s : Finset V) : Submodule ℂ B :=
  Submodule.span ℂ (q '' (s : Set V))

variable (φ : B →ₗ[ℂ] ℂ)

def atomCornerFunctional (r : V) : B →ₗ[ℂ] ℂ where
  toFun a := φ (q r * a * q r)
  map_add' a b := by simp only [mul_add, add_mul, map_add]
  map_smul' c a := by simp only [mul_smul_comm, smul_mul_assoc, map_smul, RingHom.id_apply]

def finiteAtomExpectation (s : Finset V) (a : B) : B :=
  ∑ r ∈ s, (φ (q r * a * q r) / φ (q r)) • q r

end

section
open Filter Topology
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
variable {ι : Type*} {l : Filter ι}

theorem strong_apply_tendsto (S : ι → H →L[ℂ] H) (T : H →L[ℂ] H)
    (C : ℝ) (hS : ∀ i, ‖S i‖ ≤ C)
    (hlim : ∀ x, Tendsto (fun i => S i x) l (𝓝 (T x)))
    {x : ι → H} {y : H} (hx : Tendsto x l (𝓝 y)) :
    Tendsto (fun i => S i (x i)) l (𝓝 (T y)) := by
  have hz : Tendsto (fun i => S i (x i-y)) l (𝓝 0) := by
    apply squeeze_zero_norm (fun i => (S i).le_opNorm (x i-y) |>.trans
      (mul_le_mul_of_nonneg_right (hS i) (norm_nonneg _)))
    simpa only [sub_self, norm_zero, mul_zero] using
      (tendsto_const_nhds (x := C) (f := l)).mul
        ((hx.sub (tendsto_const_nhds (x := y) (f := l))).norm)
  have hh := hz.add (hlim y)
  simpa only [← map_add, sub_add_cancel, zero_add] using hh

theorem strong_mul_tendsto (S R : ι → H →L[ℂ] H) (T U : H →L[ℂ] H)
    (C : ℝ) (hS : ∀ i, ‖S i‖ ≤ C)
    (hlimS : ∀ x, Tendsto (fun i => S i x) l (𝓝 (T x)))
    (hlimR : ∀ x, Tendsto (fun i => R i x) l (𝓝 (U x))) (x : H) :
    Tendsto (fun i => (S i * R i) x) l (𝓝 ((T*U) x)) :=
  strong_apply_tendsto S T C hS hlimS (hlimR x)

def StronglyApproximable (F : ι → Subalgebra ℂ (H →L[ℂ] H)) (l : Filter ι)
    (T : H →L[ℂ] H) : Prop :=
  ∃ S : ι → H →L[ℂ] H, ∃ C : ℝ, 0 ≤ C ∧ (∀ i, S i ∈ F i) ∧
    (∀ i, ‖S i‖ ≤ C) ∧ ∀ x, Tendsto (fun i => S i x) l (𝓝 (T x))

variable (F : ι → Subalgebra ℂ (H →L[ℂ] H)) (l : Filter ι)

theorem StronglyApproximable.constant {T : H →L[ℂ] H} (hT : ∀ i, T ∈ F i) :
    StronglyApproximable F l T :=
  ⟨fun _ => T, ‖T‖, norm_nonneg _, hT, fun _ => le_rfl, fun _ => tendsto_const_nhds⟩

theorem StronglyApproximable.add {T U : H →L[ℂ] H}
    (hT : StronglyApproximable F l T) (hU : StronglyApproximable F l U) :
    StronglyApproximable F l (T + U) := by
  rcases hT with ⟨S, C, hC, hSF, hS, hlimS⟩
  rcases hU with ⟨R, D, hD, hRF, hR, hlimR⟩
  exact ⟨fun i => S i + R i, C+D, add_nonneg hC hD,
    fun i => (F i).add_mem (hSF i) (hRF i),
    fun i => (norm_add_le _ _).trans (add_le_add (hS i) (hR i)),
    fun x => (hlimS x).add (hlimR x)⟩

theorem StronglyApproximable.mul {T U : H →L[ℂ] H}
    (hT : StronglyApproximable F l T) (hU : StronglyApproximable F l U) :
    StronglyApproximable F l (T * U) := by
  rcases hT with ⟨S, C, hC, hSF, hS, hlimS⟩
  rcases hU with ⟨R, D, hD, hRF, hR, hlimR⟩
  exact ⟨fun i => S i * R i, C*D, mul_nonneg hC hD,
    fun i => (F i).mul_mem (hSF i) (hRF i),
    fun i => (norm_mul_le _ _).trans (mul_le_mul (hS i) (hR i) (norm_nonneg _) hC),
    strong_mul_tendsto S R T U C hS hlimS hlimR⟩

def stronglyApproximableAlgebra : Subalgebra ℂ (H →L[ℂ] H) where
  carrier := StronglyApproximable F l
  mul_mem' := StronglyApproximable.mul F l
  add_mem' := StronglyApproximable.add F l
  algebraMap_mem' c := StronglyApproximable.constant F l fun i => (F i).algebraMap_mem c

end

section
open Filter Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {ι : Type*} (F : ι → Subalgebra ℂ (H →L[ℂ] H)) (l : Filter ι)

theorem StronglyApproximable.vector_trace (ξ : H)
    (htr : ∀ i a b, a ∈ F i → b ∈ F i → inner ℂ ξ ((a*b) ξ) = inner ℂ ξ ((b*a) ξ))
    [l.NeBot] {T U : H →L[ℂ] H} (hT : StronglyApproximable F l T)
    (hU : StronglyApproximable F l U) :
    inner ℂ ξ ((T*U) ξ) = inner ℂ ξ ((U*T) ξ) := by
  rcases hT with ⟨S, C, _, hSF, hS, hlimS⟩
  rcases hU with ⟨R, D, _, hRF, hR, hlimR⟩
  have hleft := ((innerSL ℂ ξ).continuous.tendsto ((T*U) ξ)).comp
    (strong_mul_tendsto S R T U C hS hlimS hlimR ξ)
  have hright := ((innerSL ℂ ξ).continuous.tendsto ((U*T) ξ)).comp
    (strong_mul_tendsto R S U T D hR hlimR hlimS ξ)
  simp only [Function.comp_def, innerSL_apply_apply] at hleft hright
  apply tendsto_nhds_unique hleft
  have heq : (fun i => inner ℂ ξ ((S i * R i) ξ)) =
      (fun i => inner ℂ ξ ((R i * S i) ξ)) := by
    funext i
    exact htr i (S i) (R i) (hSF i) (hRF i)
  rw [heq]
  exact hright

end

variable {B : Type*} [NormedRing B] [NormedAlgebra ℂ B]

theorem continuous_trace_closure (φ : B →L[ℂ] ℂ) (s : Set B)
    (h : ∀ a ∈ s, ∀ b ∈ s, φ (a*b) = φ (b*a))
    {a b : B} (ha : a ∈ closure s) (hb : b ∈ closure s) :
    φ (a*b) = φ (b*a) := by
  have hleft (b : B) (hb : b ∈ s) : ∀ a ∈ closure s, φ (a*b) = φ (b*a) := by
    apply closure_minimal (fun a ha => h a ha b hb)
    exact isClosed_eq (by fun_prop) (by fun_prop)
  have hright : closure s ⊆ {b | φ (a*b) = φ (b*a)} := by
    apply closure_minimal (fun b hb => hleft b hb a ha)
    exact isClosed_eq (by fun_prop) (by fun_prop)
  exact hright hb

open Filter Topology
open scoped lp
variable {J V : Type*} [DecidableEq V]

variable [DecidableEq J]

open scoped InnerProductSpace
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

variable [CompleteSpace H]

variable {A : Type*} [CStarAlgebra A]

theorem faithfulRepresentation_range_closed (π : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hπ : Function.Injective π) : IsClosed (Set.range π) :=
  (NonUnitalStarAlgHom.isometry π hπ).isClosedEmbedding.isClosed_range

def representationInverse (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (hπ : Function.Injective π) :
    π.range →L[ℂ] A :=
  (StarAlgEquiv.ofInjective π hπ).symm.toAlgEquiv.toLinearMap.mkContinuous 1 (by
    intro x
    rw [one_mul]
    exact le_of_eq (by
      have he : π ((StarAlgEquiv.ofInjective π hπ).symm x) = x :=
        congrArg Subtype.val ((StarAlgEquiv.ofInjective π hπ).apply_symm_apply x)
      rw [← NonUnitalStarAlgHom.norm_map π hπ]
      change ‖π ((StarAlgEquiv.ofInjective π hπ).symm x)‖ = ‖(x : H →L[ℂ] H)‖
      rw [he]))

open scoped InnerProductSpace
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {A : Type*} [CStarAlgebra A]

open scoped InnerProductSpace
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

section
open scoped InnerProductSpace
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (B : StarSubalgebra ℂ (H →L[ℂ] H))
variable {I : Type*} {A : I → Type*} [∀ i, CStarAlgebra (A i)]
variable (ι : ∀ i, A i →⋆ₐ[ℂ] B) (ξ : H)

def ambientFactor (i : I) : A i →⋆ₐ[ℂ] (H →L[ℂ] H) := B.subtype.comp (ι i)

def factorAlgebra (i : I) : NonUnitalSubalgebra ℂ B :=
  (ι i).range.toSubalgebra.toNonUnitalSubalgebra

end

open scoped CStarAlgebra

open scoped ComplexOrder CStarAlgebra
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {n : Type*} [Fintype n] [DecidableEq n]

open scoped CStarAlgebra
variable {A B n : Type*} [CStarAlgebra A] [CStarAlgebra B] [Fintype n] [DecidableEq n]

def matrixSingle (i j : n) (a : A) : CStarMatrix n n A :=
  CStarMatrix.ofMatrix (Matrix.single i j a)

variable [PartialOrder A] [StarOrderedRing A]

open scoped ComplexOrder CStarAlgebra
variable {A V n : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [Fintype n] [DecidableEq n]

variable [Nonempty n]

open scoped ComplexOrder CStarAlgebra
variable {B n V : Type*} [CStarAlgebra B] [Fintype n] [DecidableEq n] [Nonempty n]

variable {I : Type*}
  {A : I → Type*}
  [∀ i, CStarAlgebra (A i)]
  [∀ i, PartialOrder (A i)]
  [∀ i, StarOrderedRing (A i)]
  (χ : B → V → ℂ)

section
open Filter Topology
open scoped ComplexOrder CStarAlgebra OnePoint
variable {A V : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem SequenceDiagonal.tendsto (g : SequenceDiagonal) :
    Tendsto (fun n : ℕ => g n) atTop (𝓝 (g ∞)) := by
  apply g.continuous.continuousAt.tendsto.comp
  simpa only [coclosedCompact_eq_cocompact, Filter.cocompact_eq_cofinite,
    Nat.cofinite_eq_atTop] using (OnePoint.tendsto_coe_infty (X := ℕ))

variable {p : ℕ → A} {f : A →L[ℂ] ℂ} (hp : Peaks p f) (hp0 : p 0 = 1)

def sequenceDiagonalMap (p : ℕ → A) (g : SequenceDiagonal) : A :=
  peakDiagonal p (g ∞) (fun n => g n)

include hp in

theorem sequenceDiagonalMap_mem (g : SequenceDiagonal) :
    sequenceDiagonalMap p g ∈ peakAlgebra p := by
  apply (StarSubalgebra.isClosed_topologicalClosure _).mem_of_tendsto
    (hp.tendsto_peakDiagonal (g ∞) (fun n => g n) g.tendsto)
  apply Filter.Eventually.of_forall
  intro n
  exact (peakAlgebra p).add_mem ((peakAlgebra p).smul_mem (one_mem _) _)
    ((peakAlgebra p).sum_mem fun r _ => (peakAlgebra p).smul_mem
      (peakAtom_mem_peakAlgebra p r) _)

end

section
open Filter Topology
open scoped ComplexOrder CStarAlgebra OnePoint
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {p : ℕ → A} {f : A →L[ℂ] ℂ} (hp : Peaks p f) (hp0 : p 0 = 1)
variable (τ : A →L[ℂ] ℂ) (hτ : IsState τ) (hpos : ∀ n, 0 < (τ (peakAtom p n)).re)

theorem peakingCoefficients_zero_corners (a : A)
    (ha : peakingCoefficients hp τ hτ hpos a = 0) (n : ℕ) :
    τ (peakAtom p n * a * peakAtom p n) = 0 := by
  have h := congrArg (fun g : SequenceDiagonal => g n) ha
  change (τ (peakAtom p n)).re⁻¹ • τ (peakAtom p n * a * peakAtom p n) = 0 at h
  exact (smul_eq_zero.mp h).resolve_left (inv_ne_zero (ne_of_gt (hpos n)))

end

open scoped ComplexOrder CStarAlgebra
variable {A B V : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

def positivePullback (τ : A →ₚ[ℂ] ℂ) (φ : B →⋆ₐ[ℂ] A) : B →ₚ[ℂ] ℂ :=
  PositiveLinearMap.mk₀ (τ.toLinearMap.comp φ.toLinearMap) (by
    intro b hb
    obtain ⟨c, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hb
    change 0 ≤ τ (φ (star c*c))
    rw [map_mul, map_star]
    exact τ.map_nonneg (star_mul_self_nonneg _))

section
open Filter Topology
open scoped OnePoint ComplexOrder CStarAlgebra
variable {A n : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [Fintype n] [DecidableEq n] [Nonempty n]

theorem positiveCLM_isState (τ : A →ₚ[ℂ] ℂ) (hn : τ 1 = 1) : IsState (positiveCLM τ) := by
  rw [isState_iff]
  refine ⟨hn, fun a => ?_⟩
  have h := τ.map_nonneg (star_mul_self_nonneg a)
  exact ⟨h.2.symm,h.1⟩

end

section
open Filter Topology
open scoped OnePoint ComplexOrder CStarAlgebra
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {p : ℕ → A} {f : A →L[ℂ] ℂ} (hp : Peaks p f) (hp0 : p 0 = 1)
variable (τ : A →L[ℂ] ℂ) (hτ : IsState τ) (hpos : ∀ v, 0 < (τ (peakAtom p v)).re)

def sequenceAtom (v : ℕ) : SequenceDiagonal := peakingCoefficients hp τ hτ hpos (peakAtom p v)

end

end NaimarkZFC

end

end OAI
end

section
-- module Solutions.OAIQ115_Naimark.Naimark_Peaking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace NaimarkZFC

open scoped ComplexOrder CStarAlgebra
section
variable {A n : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [Fintype n] [DecidableEq n]

def matrixEntryPositive (i : n) : CStarMatrix n n A →ₚ[ℂ] A :=
  PositiveLinearMap.mk₀
    { toFun := fun M => M i i
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
    (by
      intro M hM
      apply AddSubmonoid.closure_induction
        (motive := fun M _ => 0 ≤ M i i) ?_ ?_ ?_
        (StarOrderedRing.nonneg_iff.mp hM)
      · rintro M ⟨N,rfl⟩
        simp only [CStarMatrix.mul_apply,CStarMatrix.star_apply]
        exact Finset.sum_nonneg fun j _ => star_mul_self_nonneg _
      · exact le_rfl
      · intro M N _ _ hM hN; exact add_nonneg hM hN)

def matrixEntryCLM (i : n) : CStarMatrix n n A →L[ℂ] A :=
  (matrixEntryPositive i).toLinearMap.mkContinuous 1 (fun M => by
    change ‖M i i‖ ≤ 1 * ‖M‖
    simpa only [one_mul] using (CStarMatrix.norm_entry_le_norm (M := M) (i := i) (j := i)))

def matrixState (f : A →L[ℂ] ℂ) (i : n) : CStarMatrix n n A →L[ℂ] ℂ :=
  f.comp (matrixEntryCLM i)

end

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

inductive BridgeCore (F : Type*)
  | single (i : Bool)
  | double (i : Bool) (a : F) (j : Bool)
  | flank (i : Bool) (a : F) (w : BridgeCore F) (c : F) (j : Bool)

namespace BridgeCore
variable {F B : Type*}
def left : BridgeCore F → Bool
  | .single i | .double i _ _ | .flank i _ _ _ _ => i

def right : BridgeCore F → Bool
  | .single i | .double _ _ i | .flank _ _ _ _ i => !i

def Centered (K : F → Prop) : BridgeCore F → Prop
  | .single _ => True
  | .double _ a _ => K a
  | .flank _ a w c _ => K a ∧ w.Centered K ∧ K c

variable [Monoid B]
def eval (φ : F → B) (b : Bool → B) : BridgeCore F → B
  | .single i => b i
  | .double i a j => b i * φ a * b j
  | .flank i a w c j => b i * φ a * w.eval φ b * φ c * b j

def cons (i : Bool) (a : F) : BridgeCore F → BridgeCore F
  | .single j => .double i a j
  | .double j c k => .flank i a (.single j) c k
  | .flank j c w d k => .flank i a (w.cons j c) d k

theorem eval_cons (φ : F → B) (b : Bool → B) (i : Bool) (a : F) (w : BridgeCore F) :
    (w.cons i a).eval φ b = b i * φ a * w.eval φ b := by
  induction w generalizing i a with
  | single j => rfl
  | double j c k => simp only [cons,eval,mul_assoc]
  | flank j c w d k ih => simp only [cons,eval,ih,mul_assoc]

theorem centered_cons (K : F → Prop) (i : Bool) (a : F) (w : BridgeCore F)
    (ha : K a) (hw : w.Centered K) : (w.cons i a).Centered K := by
  induction w generalizing i a with
  | single j => exact ha
  | double j c k => exact ⟨ha,trivial,hw⟩
  | flank j c w d k ih => exact ⟨ha,ih j c hw.1 hw.2.1,hw.2.2⟩

def snoc (a : F) (j : Bool) : BridgeCore F → BridgeCore F
  | .single i => .double i a j
  | .double i c k => .flank i c (.single k) a j
  | .flank i c w d k => .flank i c (w.snoc d k) a j

theorem eval_snoc (φ : F → B) (b : Bool → B) (a : F) (j : Bool) (w : BridgeCore F) :
    (w.snoc a j).eval φ b = w.eval φ b * φ a * b j := by
  induction w generalizing a j with
  | single i => rfl
  | double i c k => simp only [snoc,eval,mul_assoc]
  | flank i c w d k ih => simp only [snoc,eval,ih,mul_assoc]

theorem centered_snoc (K : F → Prop) (a : F) (j : Bool) (w : BridgeCore F)
    (ha : K a) (hw : w.Centered K) : (w.snoc a j).Centered K := by
  induction w generalizing a j with
  | single i => exact ha
  | double i c k => exact ⟨hw,trivial,ha⟩
  | flank i c w d k ih => exact ⟨hw.1,ih d k hw.2.2 hw.2.1,ha⟩

end BridgeCore

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
section
variable {F B γ : Type*} [CStarAlgebra F] [CStarAlgebra B] {l : Filter γ}
  (φ : F →⋆ₐ[ℂ] B) (b e : Bool → B) (P : B) (hP : IsStarProjection P)
  (hel : ∀ i, e i*b i = b i) (her : ∀ i, b i*e (!i) = b i)
  (hen : ∀ i, ‖e i‖ ≤ 1) (K : F → Prop)
  (hz : ∀ w : BridgeCore F, w.Centered K → (1-P)*w.eval φ b*(1-P) = 0)
include hel her hen hz hP

omit hel her hen hz hP

structure BridgeDecayData (f : Bool → F →L[ℂ] ℂ) (x y : γ → B)
    (px py : Bool → γ → B) (tx ty : Option Bool) : Prop where
  normX : ∀ k, ‖x k‖ ≤ 1
  normY : ∀ k, ‖y k‖ ≤ 1
  normPX : ∀ i k, ‖px i k‖ ≤ 1
  normPY : ∀ i k, ‖py i k‖ ≤ 1
  normState : ∀ i, f i 1 = 1
  matchedX : ∀ i, tx = some i → ∀ k, x k = px i k
  matchedY : ∀ i, ty = some i → ∀ k, y k = py i k
  transferX : ∀ i k, px i k*b i = b i*px (!i) k
  transferY : ∀ i k, b i*py (!i) k = py i k*b i
  exclude : ∀ i, tx = some i → ty ≠ some (!i)
  cutX : ∀ i a, (tx ≠ some i ∨ f i a = 0) →
    Tendsto (fun k => x k*φ a*e i*P) l (𝓝 0)
  cutY : ∀ i a, (ty ≠ some i ∨ f i a = 0) →
    Tendsto (fun k => P*(e i*φ a*y k)) l (𝓝 0)
  cutPX : ∀ j i a, K a → Tendsto (fun k => px j k*φ a*e i*P) l (𝓝 0)
  cutPY : ∀ j i a, K a → Tendsto (fun k => P*(e i*φ a*py j k)) l (𝓝 0)
  crossX : ∀ i a, tx = some i → ty ≠ some (!i) →
    Tendsto (fun k => px (!i) k*φ a*y k) l (𝓝 0)
  crossY : ∀ i a, ty = some (!i) → tx ≠ some i →
    Tendsto (fun k => x k*φ a*py i k) l (𝓝 0)
  rectangle : ∀ i a, K a → Tendsto (fun k => px i k*φ a*py i k) l (𝓝 0)

end

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
section

variable {A C : Type*} [CStarAlgebra A] [CStarAlgebra C]

theorem simple_nonzeroStarHom_injective (hA : IsSimpleCStar A)
    (φ : A →⋆ₙₐ[ℂ] C) (hne : φ ≠ 0) : Function.Injective φ := by
  have hc : IsClosed (TwoSidedIdeal.ker φ : Set A) := by
    have he : (TwoSidedIdeal.ker φ : Set A) = {a : A | φ a = 0} := by
      ext a; exact TwoSidedIdeal.mem_ker φ
    rw [he]
    exact isClosed_eq (map_continuous φ) continuous_const
  rcases hA.2 (TwoSidedIdeal.ker φ) hc with hb | ht
  · exact (TwoSidedIdeal.ker_eq_bot φ).mp hb
  · exfalso
    apply hne
    ext a
    apply (TwoSidedIdeal.mem_ker φ).mp
    rw [ht]
    exact TwoSidedIdeal.mem_top _

end

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

section
-- module Solutions.OAIQ115_Naimark.Naimark_HNN
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
section
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def idealSelfAdjointSubspace (J : TwoSidedIdeal A) : Submodule ℝ (selfAdjoint A) where
  carrier := {a | (a:A) ∈ J}
  zero_mem' := J.zero_mem
  add_mem' ha hb := J.add_mem ha hb
  smul_mem' r a ha := by
    change r • (a:A) ∈ J
    rw [Algebra.smul_def]
    exact J.mul_mem_left _ _ ha

end

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


