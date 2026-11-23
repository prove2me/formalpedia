-- Prove2me | Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_ChartSymmEventuallyEq
-- name    : ReciprocityTheory_L2DbarEstimates_ChartDerivatives_ChartSymmEventuallyEq
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:05:59.118321+00:00
-- url     : https://prove2.me/theorems/055223ca-6f3d-4fc1-8d75-0a9539b81610
-- title:
--   Chart Symm Eventually Eq
-- statement:
--   Definitions and structural lemmas for Chart Symm Eventually Eq, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/ChartSymmEventuallyEq.lean

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_HoloSmooth
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.L2DbarEstimates
open Filter Topology Set
open scoped ContDiff
noncomputable section
theorem chart_z_symm {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (e : OpenPartialHomeomorph M (V n)) (he : IsChart n z e) (y : V n) (hy : y ∈ e.target) :
    z (e.symm y) = y := by
  rw [he (e.map_target hy), e.right_inv hy]
theorem chart_symm_eventuallyEq {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (e₁ e₂ : OpenPartialHomeomorph M (V n)) (h₁ : IsChart n z e₁) (h₂ : IsChart n z e₂)
    (x : M) (hx₁ : x ∈ e₁.source) (hx₂ : x ∈ e₂.source) :
    (e₁.symm : V n → M) =ᶠ[𝓝 (z x)] e₂.symm := by
  have h1 : z x = e₁ x := h₁ hx₁
  have h2 : z x = e₂ x := h₂ hx₂
  have t1 : ∀ᶠ y in 𝓝 (z x), e₁.symm y ∈ e₂.source := by
    rw [h1]
    refine (e₁.continuousAt_symm (e₁.map_source hx₁)).preimage_mem_nhds ?_
    rw [e₁.left_inv hx₁]
    exact e₂.open_source.mem_nhds hx₂
  have t2 : ∀ᶠ y in 𝓝 (z x), y ∈ e₁.target := by
    rw [h1]; exact e₁.open_target.mem_nhds (e₁.map_source hx₁)
  have t3 : ∀ᶠ y in 𝓝 (z x), y ∈ e₂.target := by
    rw [h2]; exact e₂.open_target.mem_nhds (e₂.map_source hx₂)
  filter_upwards [t1, t2, t3] with y hy1 hy2 hy3
  apply e₂.injOn hy1 (e₂.map_target hy3)
  rw [e₂.right_inv hy3, ← h₂ hy1, h₁ (e₁.map_target hy2), e₁.right_inv hy2]
theorem wd_congr (n : ℕ) (j : Fin n) (g₁ g₂ : V n → ℂ) (y : V n) (h : g₁ =ᶠ[𝓝 y] g₂) :
    wd n j g₁ y = wd n j g₂ y := by
  simp only [wd, h.fderiv_eq]
theorem wdb_congr (n : ℕ) (j : Fin n) (g₁ g₂ : V n → ℂ) (y : V n) (h : g₁ =ᶠ[𝓝 y] g₂) :
    wdb n j g₁ y = wdb n j g₂ y := by
  simp only [wdb, h.fderiv_eq]
theorem d_eq_wd {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (e : OpenPartialHomeomorph M (V n)) (he : IsChart n z e) (j : Fin n) (f : M → ℂ) (x : M)
    (hx : x ∈ e.source) :
    d n z j f x = wd n j (f ∘ e.symm) (z x) := by
  have h : ∃ e : OpenPartialHomeomorph M (V n), IsChart n z e ∧ x ∈ e.source := ⟨e, he, hx⟩
  unfold d
  rw [dif_pos h]
  apply wd_congr
  have := chart_symm_eventuallyEq n z _ e (Classical.choose_spec h).1 he x (Classical.choose_spec h).2 hx
  filter_upwards [this] with y hy
  simp only [Function.comp_apply, hy]
theorem db_eq_wdb {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (e : OpenPartialHomeomorph M (V n)) (he : IsChart n z e) (j : Fin n) (f : M → ℂ) (x : M)
    (hx : x ∈ e.source) :
    db n z j f x = wdb n j (f ∘ e.symm) (z x) := by
  have h : ∃ e : OpenPartialHomeomorph M (V n), IsChart n z e ∧ x ∈ e.source := ⟨e, he, hx⟩
  unfold db
  rw [dif_pos h]
  apply wdb_congr
  have := chart_symm_eventuallyEq n z _ e (Classical.choose_spec h).1 he x (Classical.choose_spec h).2 hx
  filter_upwards [this] with y hy
  simp only [Function.comp_apply, hy]
theorem d_comp_symm {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (e : OpenPartialHomeomorph M (V n)) (he : IsChart n z e) (j : Fin n) (f : M → ℂ)
    (y : V n) (hy : y ∈ e.target) :
    d n z j f (e.symm y) = wd n j (f ∘ e.symm) y := by
  rw [d_eq_wd n z e he j f (e.symm y) (e.map_target hy), chart_z_symm n z e he y hy]
theorem db_comp_symm {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (e : OpenPartialHomeomorph M (V n)) (he : IsChart n z e) (j : Fin n) (f : M → ℂ)
    (y : V n) (hy : y ∈ e.target) :
    db n z j f (e.symm y) = wdb n j (f ∘ e.symm) y := by
  rw [db_eq_wdb n z e he j f (e.symm y) (e.map_target hy), chart_z_symm n z e he y hy]
theorem contDiffOn_fderiv_apply_of_contDiffOn_infty {n : ℕ} {U : Set (V n)} (hU : IsOpen U) {g : V n → ℂ}
    (hg : ContDiffOn ℝ ∞ g U) (v : V n) : ContDiffOn ℝ ∞ (fun y => fderiv ℝ g y v) U :=
  ((contDiffOn_infty_iff_fderiv_of_isOpen hU).1 hg).2.clm_apply contDiffOn_const
theorem contDiffOn_wd_wdb_of_contDiffOn_infty {n : ℕ} {U : Set (V n)} (hU : IsOpen U) {g : V n → ℂ}
    (hg : ContDiffOn ℝ ∞ g U) (j : Fin n) :
    ContDiffOn ℝ ∞ (wd n j g) U ∧ ContDiffOn ℝ ∞ (wdb n j g) U := by
  constructor
  · unfold wd
    exact ((contDiffOn_fderiv_apply_of_contDiffOn_infty hU hg _).sub
      (contDiffOn_const.mul (contDiffOn_fderiv_apply_of_contDiffOn_infty hU hg _))).div_const 2
  · unfold wdb
    exact ((contDiffOn_fderiv_apply_of_contDiffOn_infty hU hg _).add
      (contDiffOn_const.mul (contDiffOn_fderiv_apply_of_contDiffOn_infty hU hg _))).div_const 2
theorem Smooth.d {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (j : Fin n)
    (f : M → ℂ) (hf : Smooth n z f) : Smooth n z (d n z j f) := by
  intro e he
  exact (contDiffOn_wd_wdb_of_contDiffOn_infty e.open_target (hf e he) j).1.congr fun y hy => d_comp_symm n z e he j f y hy
theorem Smooth.db {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (j : Fin n)
    (f : M → ℂ) (hf : Smooth n z f) : Smooth n z (db n z j f) := by
  intro e he
  exact (contDiffOn_wd_wdb_of_contDiffOn_infty e.open_target (hf e he) j).2.congr fun y hy => db_comp_symm n z e he j f y hy
end
end ReciprocityTheory.L2DbarEstimates


