-- Prove2me | Definitions.Def_Development_WeilBound_ThetaLifts_EigenvalueEndgame_SignatureSplitting_ConvCont
-- name    : Development_WeilBound_ThetaLifts_EigenvalueEndgame_SignatureSplitting_ConvCont
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T03:55:00.363926+00:00
-- url     : https://prove2.me/theorems/90fd5c58-68c8-4922-a62c-f3bbfed32778
-- title:
--   Conv Cont
-- statement:
--   Definitions and structural lemmas for Conv Cont, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/EigenvalueEndgame/SignatureSplitting/ConvCont.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
set_option linter.unusedSectionVars false
namespace PositivityTheory.ThKEnd.Two
open MeasureTheory Topology Filter
open scoped Pointwise
variable {G X : Type} [Group G] [TopologicalSpace G]
structure Bump (V : Set G) (η : G → ℝ) : Prop where
  cont : Continuous η
  cpt : HasCompactSupport η
  sub : tsupport η ⊆ V
  nonneg : ∀ y, 0 ≤ η y
  one : η 1 ≠ 0
structure Cusp (Γ : Subgroup G) (n : X → G) (a : G) : Prop where
  siegel : ∃ Ω, IsCompact Ω ∧ ∀ g, ∃ γ ∈ Γ, ∃ k : ℕ, ∃ κ ∈ Ω, γ * g = a ^ k * κ
  lip : ∀ V ∈ 𝓝 (1 : G), ∃ η, Bump V η ∧ ∀ Ω : Set G, IsCompact Ω → ∃ (D : ℝ) (Ω' : Set G), IsCompact Ω' ∧ ∀ x (k : ℕ),
    ∃ γ ∈ Γ, ∃ u ∈ Ω', γ * n x * a ^ k = a ^ k * u ∧ ∀ κ ∈ Ω, ∀ y, |η (κ⁻¹ * (u⁻¹ * y)) - η (κ⁻¹ * y)| ≤ D / 2 ^ k
def Gr (a : G) (m : ℕ) (φ : G → ℂ) : Prop := ∀ Ω : Set G, IsCompact Ω → ∃ C : ℝ, ∀ k : ℕ, ∀ κ ∈ Ω, ‖φ (a ^ k * κ)‖ ≤ C * (2 ^ k) ^ m
structure Dat [MeasurableSpace X] (Γ : Subgroup G) (n : X → G) (a : G) (lam : Measure X) (l : ℂ) (φ c : G → ℂ) : Prop where
  cont : Continuous φ
  inv : ∀ γ ∈ Γ, ∀ g, φ (γ * g) = φ g
  contc : Continuous c
  av : ∀ g, c g = ∫ x, φ (n x * g) ∂lam
  law : ∀ g, c (a * (a * g)) - c (a * g) = l * (c (a * g) - c g)
def conv [MeasurableSpace G] (μ : Measure G) (η : G → ℝ) (φ : G → ℂ) : G → ℂ := fun g => ∫ y, φ (g * y) * η y ∂μ
variable [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G]
  [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] {Γ : Subgroup G} {n : X → G} {a : G} {lam : Measure X}
  [IsProbabilityMeasure lam] {l : ℂ} {φ c : G → ℂ} {V : Set G} {η : G → ℝ} (μ : Measure G) [μ.IsHaarMeasure]
theorem Bump.int (h : Bump V η) (hφ : Continuous φ) (g : G) : Integrable (fun y => φ (g * y) * η y) μ := by
  have := h.cont
  exact Continuous.integrable_of_hasCompactSupport (by fun_prop)
    (HasCompactSupport.mul_left (h.cpt.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)))
theorem Bump.conv_cont (h : Bump V η) (hφ : Continuous φ) : Continuous (conv μ η φ) := by
  have := h.cont
  have e : conv μ η φ = fun g => ∫ y in tsupport η, φ (g * y) * η y ∂μ := funext fun g =>
    (setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => by simp [image_eq_zero_of_notMem_tsupport hy]).symm
  rw [e]
  exact continuous_parametric_integral_of_continuous (by fun_prop) h.cpt
omit [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [TopologicalSpace X]
  [OpensMeasurableSpace X] [IsProbabilityMeasure lam] in
theorem Dat.bound (hC : Cusp Γ n a) (h : Dat Γ n a lam l φ c) {K : Set G} (hK : IsCompact K) :
    ∃ M, ∀ x, ∀ g ∈ K, ‖φ (n x * g)‖ ≤ M := by
  obtain ⟨η, -, h2⟩ := hC.lip _ univ_mem
  obtain ⟨D, Ω', h3, h4⟩ := h2 ∅ isCompact_empty
  obtain ⟨M, hM⟩ := (h3.mul hK).exists_bound_of_continuousOn h.cont.continuousOn
  refine ⟨M, fun x g hg => ?_⟩
  obtain ⟨γ, h5, u, h6, h7, -⟩ := h4 x 0
  rw [pow_zero, mul_one, one_mul] at h7
  rw [← h.inv γ h5, ← mul_assoc, h7]
  exact hM _ (Set.mul_mem_mul h6 hg)
theorem Dat.conv (hC : Cusp Γ n a) (hn : Continuous n) (h : Dat Γ n a lam l φ c) (hη : Bump V η) :
    Dat Γ n a lam l (conv μ η φ) (conv μ η c) := by
  refine ⟨hη.conv_cont μ h.cont, fun γ hγ g => ?_, hη.conv_cont μ h.contc, fun g => ?_, fun g => ?_⟩
  · simp only [Two.conv, mul_assoc, h.inv γ hγ]
  · simp only [Two.conv, h.av, ← integral_mul_const, mul_assoc]
    refine integral_integral_swap ?_
    obtain ⟨M, hM⟩ := h.bound hC (hη.cpt.isCompact.image (continuous_const_mul g))
    have := h.cont
    have := hη.cont
    refine Integrable.mono' ((hη.cont.integrable_of_hasCompactSupport hη.cpt).mul_prod (integrable_const M))
      (Continuous.aestronglyMeasurable (by fun_prop)) (.of_forall fun z => ?_)
    by_cases hy : z.1 ∈ tsupport η
    · simp only [Function.uncurry, norm_mul, Complex.norm_real, Real.norm_of_nonneg (hη.nonneg _)]
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_left (hM _ _ ⟨_, hy, rfl⟩) (hη.nonneg _)
    · simp [Function.uncurry, image_eq_zero_of_notMem_tsupport hy]
  · simp only [Two.conv]
    rw [← integral_sub (hη.int μ h.contc _) (hη.int μ h.contc _), ← integral_sub (hη.int μ h.contc _) (hη.int μ h.contc _),
      ← integral_const_mul]
    congr 1
    funext y
    have := h.law (g * y)
    simp only [mul_assoc]
    linear_combination (η y : ℂ) * this
end PositivityTheory.ThKEnd.Two
end


