-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Slopes
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Slopes
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:47:17.279421+00:00
-- url     : https://prove2.me/theorems/19a01129-b0e0-4aac-84ce-6acbf6c0b54e
-- title:
--   Slopes
-- statement:
--   Definitions and structural lemmas for Slopes, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/Slopes.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HermitianLattice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Heights₂.Heights
open NumberField TensorProduct ComplexAt
noncomputable section
namespace HermitianBundle
variable {K : Type*} [Field K] [NumberField K] (E : HermitianBundle K)
def gramDet (σ : K →+* ℂ) {r : ℕ} (f : Fin r → E.carrier) : ℂ :=
  Matrix.det (Matrix.of fun i j ↦ (E.metric.form σ).inner
    ((1 : ComplexAt σ) ⊗ₜ[𝓞 K] f i) ((1 : ComplexAt σ) ⊗ₜ[𝓞 K] f j))
def rank (F : Submodule (𝓞 K) E.carrier) : ℕ := Module.finrank (𝓞 K) F
def degreeWith (F : Submodule (𝓞 K) E.carrier) {r : ℕ} (f : Fin r → F) : ℝ :=
  Real.log (Nat.card (F ⧸ Submodule.span (𝓞 K) (Set.range f))) -
    (1 / 2) * ∑ σ : K →+* ℂ, Real.log ‖gramDet E σ (fun i ↦ (f i : E.carrier))‖
theorem exists_linearIndependent_rank (F : Submodule (𝓞 K) E.carrier) :
    ∃ f : Fin (rank E F) → F, LinearIndependent (𝓞 K) f :=
  exists_linearIndependent_of_le_finrank le_rfl
def degree (F : Submodule (𝓞 K) E.carrier) : ℝ :=
  degreeWith E F (exists_linearIndependent_rank E F).choose
def normDegree (F : Submodule (𝓞 K) E.carrier) : ℝ := degree E F / Module.finrank ℚ K
def slope (F : Submodule (𝓞 K) E.carrier) : ℝ := normDegree E F / rank E F
def slopeMax : EReal :=
  ⨆ (F : Submodule (𝓞 K) E.carrier) (_ : F ≠ ⊥), ((slope E F : ℝ) : EReal)
def Saturated (F : Submodule (𝓞 K) E.carrier) : Prop :=
  ∀ (a : 𝓞 K) (x : E.carrier), a ≠ 0 → a • x ∈ F → x ∈ F
end HermitianBundle
variable {K : Type*} [Field K] [NumberField K]
structure HermitianExtension (E' E E'' : HermitianBundle K) where

  incl : E'.carrier →ₗ[𝓞 K] E.carrier

  proj : E.carrier →ₗ[𝓞 K] E''.carrier
  incl_injective : Function.Injective incl
  proj_surjective : Function.Surjective proj
  exact : Function.Exact incl proj
  incl_isometric : ∀ (σ : K →+* ℂ) (x y : Fibre σ E'.carrier),
    (E.metric.form σ).inner (incl.lTensor (ComplexAt σ) x) (incl.lTensor (ComplexAt σ) y) =
      (E'.metric.form σ).inner x y
  proj_coisometric : ∀ (σ : K →+* ℂ) (x y : Fibre σ E.carrier),
    (∀ w, (E.metric.form σ).inner (incl.lTensor (ComplexAt σ) w) x = 0) →
    (∀ w, (E.metric.form σ).inner (incl.lTensor (ComplexAt σ) w) y = 0) →
    (E''.metric.form σ).inner (proj.lTensor (ComplexAt σ) x) (proj.lTensor (ComplexAt σ) y) =
      (E.metric.form σ).inner x y
abbrev firstIncl (K : Type*) [Field K] : 𝓞 K →ₗ[𝓞 K] (Fin 2 → 𝓞 K) :=
  LinearMap.single (𝓞 K) (fun _ : Fin 2 ↦ 𝓞 K) 0
abbrev secondProj (K : Type*) [Field K] : (Fin 2 → 𝓞 K) →ₗ[𝓞 K] 𝓞 K :=
  LinearMap.proj 1
theorem integers_inner_eq (σ : K →+* ℂ) (x y : Fibre σ (𝓞 K)) :
    ((HermitianMetric.integers K).form σ).inner x y =
      starRingEnd ℂ (integersCoord K σ x) * integersCoord K σ y := by
  rw [mul_comm]
  rfl
omit [NumberField K] in
theorem standardCoord_firstIncl (σ : K →+* ℂ) (x : Fibre σ (𝓞 K)) (i : Fin 2) :
    standardCoord K σ (Fin 2) ((firstIncl K).lTensor (ComplexAt σ) x) i =
      if i = 0 then integersCoord K σ x else 0 := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul z a =>
    rw [LinearMap.lTensor_tmul, standardCoord_tmul, integersCoord_tmul]
    by_cases hi : i = 0
    · subst hi; simp
    · simp [hi]
  | add x y hx hy =>
    rw [map_add, map_add, PiLp.add_apply, hx, hy, map_add]
    split_ifs <;> simp
omit [NumberField K] in
theorem integersCoord_secondProj (σ : K →+* ℂ) (x : Fibre σ (Fin 2 → 𝓞 K)) :
    integersCoord K σ ((secondProj K).lTensor (ComplexAt σ) x) = standardCoord K σ (Fin 2) x 1 := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul z a => rw [LinearMap.lTensor_tmul, standardCoord_tmul, integersCoord_tmul]; rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, PiLp.add_apply]
omit [NumberField K] in
theorem firstIncl_injective : Function.Injective (firstIncl K) :=
  fun a b h ↦ by simpa using congrFun h 0
omit [NumberField K] in
theorem firstIncl_exact : Function.Exact (firstIncl K) (secondProj K) := by
  intro y
  constructor
  · intro hy
    have hy1 : y 1 = 0 := hy
    refine ⟨y 0, funext fun i ↦ ?_⟩
    fin_cases i
    · simp
    · simp [hy1]
  · rintro ⟨a, rfl⟩
    simp
omit [NumberField K] in
theorem secondProj_surjective : Function.Surjective (secondProj K) :=
  fun a ↦ ⟨Pi.single 1 a, by simp⟩
theorem firstIncl_isometric (σ : K →+* ℂ) (x y : Fibre σ (𝓞 K)) :
    ((HermitianMetric.standard K (Fin 2)).form σ).inner ((firstIncl K).lTensor (ComplexAt σ) x)
      ((firstIncl K).lTensor (ComplexAt σ) y) = ((HermitianMetric.integers K).form σ).inner x y := by
  rw [HermitianMetric.standard_inner, integers_inner_eq, Fin.sum_univ_two,
    standardCoord_firstIncl, standardCoord_firstIncl, standardCoord_firstIncl,
    standardCoord_firstIncl]
  simp
theorem standardCoord_zero_of_orthogonal (σ : K →+* ℂ) (v : Fibre σ (Fin 2 → 𝓞 K))
    (hv : ∀ w : Fibre σ (𝓞 K), ((HermitianMetric.standard K (Fin 2)).form σ).inner
      ((firstIncl K).lTensor (ComplexAt σ) w) v = 0) :
    standardCoord K σ (Fin 2) v 0 = 0 := by
  have h := hv ((1 : ComplexAt σ) ⊗ₜ (1 : 𝓞 K))
  rw [HermitianMetric.standard_inner, Fin.sum_univ_two, standardCoord_firstIncl,
    standardCoord_firstIncl, integersCoord_tmul] at h
  simpa using h
theorem secondProj_coisometric (σ : K →+* ℂ) (x y : Fibre σ (Fin 2 → 𝓞 K))
    (hx : ∀ w : Fibre σ (𝓞 K), ((HermitianMetric.standard K (Fin 2)).form σ).inner
      ((firstIncl K).lTensor (ComplexAt σ) w) x = 0)
    (hy : ∀ w : Fibre σ (𝓞 K), ((HermitianMetric.standard K (Fin 2)).form σ).inner
      ((firstIncl K).lTensor (ComplexAt σ) w) y = 0) :
    ((HermitianMetric.integers K).form σ).inner ((secondProj K).lTensor (ComplexAt σ) x)
      ((secondProj K).lTensor (ComplexAt σ) y) =
      ((HermitianMetric.standard K (Fin 2)).form σ).inner x y := by
  rw [integers_inner_eq, HermitianMetric.standard_inner, Fin.sum_univ_two,
    standardCoord_zero_of_orthogonal σ x hx, standardCoord_zero_of_orthogonal σ y hy,
    integersCoord_secondProj, integersCoord_secondProj]
  simp
variable (K) in

def HermitianExtension.standardSplit :
    HermitianExtension (HermitianBundle.integers K) (HermitianBundle.standard K 2)
      (HermitianBundle.integers K) where
  incl := firstIncl K
  proj := secondProj K
  incl_injective := firstIncl_injective
  proj_surjective := secondProj_surjective
  exact := firstIncl_exact
  incl_isometric σ x y := firstIncl_isometric σ x y
  proj_coisometric σ x y hx hy := secondProj_coisometric σ x y hx hy
variable (K) in

def standardFlag : Fin 3 → Submodule (𝓞 K) (HermitianBundle.standard K 2).carrier :=
  ![⊥, LinearMap.range (firstIncl K), ⊤]
end
end GroundTheory.Heights₂.Heights


