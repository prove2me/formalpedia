-- Prove2me | solution 1 for ArrowDebreu.ThmII.XhatPrime_YhatPrime_bounded
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-18T07:43:27.398033+00:00
-- url     : https://prove2.me/submissions/f6bd70f9-bb6c-4eac-b56a-2570c924b8aa

import Mathlib
import Definitions.Def_ArrowDebreu_Shared_Economy
import Definitions.Def_ArrowDebreu_Shared_IsCompetitiveEquilibrium
import Definitions.Def_ArrowDebreu_ThmII_AssumptionsII
import Definitions.Def_ArrowDebreu_Shared_AbstractEconomy
import Definitions.Def_ArrowDebreu_ThmII_economyEeps
open ArrowDebreu.Shared

set_option autoImplicit false

-- The set of production profiles with `y_j ∈ Y_j` and `Σ_j y_j ≥ b` is bounded
-- (Assumptions I.a, I.b, I.c), by the normalized-sequence argument of §3.3.1.
open ArrowDebreu.Shared ArrowDebreu.ThmII Filter Topology in
theorem P2Me334_K_bounded {l m n : ℕ} (E : Economy l m n) (hIa : AssumptionIa E)
    (hIb : AssumptionIb E) (hIc : AssumptionIc E) (b : Fin l → ℝ) :
    Bornology.IsBounded {y : Fin n → Fin l → ℝ | (∀ j, y j ∈ E.Y j) ∧ b ≤ ∑ j, y j} := by
  set K := {y : Fin n → Fin l → ℝ | (∀ j, y j ∈ E.Y j) ∧ b ≤ ∑ j, y j} with hK
  by_contra hnb
  have hex : ∀ k : ℕ, ∃ y ∈ K, (k : ℝ) + 1 ≤ ‖y‖ := by
    intro k
    by_contra hk
    simp only [not_exists, not_and, not_le] at hk
    apply hnb
    rw [Metric.isBounded_iff_subset_closedBall 0]
    exact ⟨(k : ℝ) + 1, fun y hy => by simpa using (hk y hy).le⟩
  choose y hyK hyn using hex
  have hpos : ∀ k, 0 < ‖y k‖ := fun k => lt_of_lt_of_le (by positivity) (hyn k)
  set w : ℕ → Fin n → Fin l → ℝ := fun k => ‖y k‖⁻¹ • y k with hw
  have hwn : ∀ k, ‖w k‖ = 1 := by
    intro k
    simp only [hw, norm_smul, norm_inv, norm_norm]
    exact inv_mul_cancel₀ (hpos k).ne'
  have hwb : ∀ k, w k ∈ Metric.closedBall (0 : Fin n → Fin l → ℝ) 1 := by
    intro k
    simp [hwn k]
  obtain ⟨w0, -, φ, hφ, hlim⟩ := tendsto_subseq_of_bounded Metric.isBounded_closedBall hwb
  have hw0n : ‖w0‖ = 1 := by
    have h0 := (continuous_norm.tendsto w0).comp hlim
    have h1 : ((fun v : Fin n → Fin l → ℝ => ‖v‖) ∘ (w ∘ φ)) = fun _ => (1 : ℝ) :=
      funext fun k => hwn _
    rw [h1] at h0
    exact (tendsto_nhds_unique tendsto_const_nhds h0).symm
  have hinv : Tendsto (fun k => ‖y (φ k)‖⁻¹) atTop (𝓝 0) := by
    have h1 : Tendsto (fun k : ℕ => ‖y k‖) atTop atTop :=
      tendsto_atTop_mono hyn (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
    exact (tendsto_inv_atTop_zero.comp h1).comp hφ.tendsto_atTop
  have hmemY : ∀ j, w0 j ∈ E.Y j := by
    intro j
    have hc : Tendsto (fun k => w (φ k) j) atTop (𝓝 (w0 j)) :=
      ((continuous_apply j).tendsto w0).comp hlim
    refine (hIa j).1.mem_of_tendsto hc (Eventually.of_forall fun k => ?_)
    show ‖y (φ k)‖⁻¹ • y (φ k) j ∈ E.Y j
    refine (hIa j).2.1.smul_mem_of_zero_mem (hIa j).2.2 ((hyK (φ k)).1 j) ⟨by positivity, ?_⟩
    have h1 : (1 : ℝ) ≤ ‖y (φ k)‖ :=
      le_trans (by linarith [Nat.cast_nonneg (α := ℝ) (φ k)]) (hyn _)
    exact inv_le_one_of_one_le₀ h1
  have hsum : 0 ≤ ∑ j, w0 j := by
    intro h
    have hcont : Continuous fun v : Fin n → Fin l → ℝ => ∑ j, v j h := by
      fun_prop
    have hc : Tendsto (fun k => ∑ j, w (φ k) j h - ‖y (φ k)‖⁻¹ * b h) atTop
        (𝓝 (∑ j, w0 j h - 0 * b h)) :=
      Tendsto.sub ((hcont.tendsto w0).comp hlim) (hinv.mul_const _)
    have hge : ∀ k, 0 ≤ ∑ j, w (φ k) j h - ‖y (φ k)‖⁻¹ * b h := by
      intro k
      have hb := (hyK (φ k)).2 h
      simp only [Finset.sum_apply] at hb
      have h2 := mul_le_mul_of_nonneg_left hb (inv_nonneg.2 (hpos (φ k)).le)
      have h3 : ∑ j, w (φ k) j h = ‖y (φ k)‖⁻¹ * ∑ j, y (φ k) j h := by
        simp only [hw, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      rw [h3]
      linarith
    have h4 := ge_of_tendsto' hc hge
    simp only [zero_mul, sub_zero] at h4
    simpa [Finset.sum_apply] using h4
  have hagg : ∑ j, w0 j ∈ aggProd E := ⟨w0, hmemY, rfl⟩
  have hzero : ∑ j, w0 j = 0 := by
    have h1 : ∑ j, w0 j ∈ aggProd E ∩ Ω l := ⟨hagg, hsum⟩
    rw [hIb] at h1
    exact h1
  have hall : ∀ j0, w0 j0 = 0 := by
    intro j0
    have h1 : w0 j0 ∈ aggProd E := by
      refine ⟨Pi.single j0 (w0 j0), fun j => ?_, ?_⟩
      · by_cases hj : j = j0
        · subst hj
          simp [hmemY]
        · simp [hj, (hIa j).2.2]
      · simp
    have h2 : w0 j0 ∈ negSet (aggProd E) := by
      show -(w0 j0) ∈ aggProd E
      refine ⟨w0 - Pi.single j0 (w0 j0), fun j => ?_, ?_⟩
      · by_cases hj : j = j0
        · subst hj
          simp [(hIa j).2.2]
        · simp [hj, hmemY]
      · simp only [Pi.sub_apply, Finset.sum_sub_distrib, hzero]
        simp
    have h3 : w0 j0 ∈ aggProd E ∩ negSet (aggProd E) := ⟨h1, h2⟩
    rw [hIc] at h3
    exact h3
  have h0 : w0 = 0 := funext hall
  rw [h0, norm_zero] at hw0n
  exact zero_ne_one hw0n

open ArrowDebreu.Shared ArrowDebreu.ThmII in
theorem solution {l m n : ℕ} (E : Economy l m n) (hE : AssumptionsIIexceptV E)
    (ξ : Fin m → Fin l → ℝ) (hξ : ∀ i, ∀ x ∈ E.X i, ξ i ≤ x) :
    (∀ i, Bornology.IsBounded (XhatPrime E ξ i)) ∧ ∀ j, Bornology.IsBounded (YhatPrime E ξ j) := by
  have hK := P2Me334_K_bounded E hE.Ia hE.Ib hE.Ic (∑ i, ξ i - zetaPrime E ξ)
  obtain ⟨L, hL⟩ := hK.bddBelow
  obtain ⟨U, hU⟩ := hK.bddAbove
  have key : ∀ (x : Fin m → Fin l → ℝ) (y : Fin n → Fin l → ℝ), (∀ i, x i ∈ E.X i) →
      (∀ j, y j ∈ E.Y j) → ∑ i, x i - ∑ j, y j ≤ zetaPrime E ξ → L ≤ y ∧ y ≤ U := by
    intro x y hx hy hle
    have hmem : y ∈ {y : Fin n → Fin l → ℝ |
        (∀ j, y j ∈ E.Y j) ∧ ∑ i, ξ i - zetaPrime E ξ ≤ ∑ j, y j} := by
      refine ⟨hy, fun h => ?_⟩
      have h1 : ∑ i, ξ i ≤ ∑ i, x i := Finset.sum_le_sum fun i _ => hξ i _ (hx i)
      have h2 := h1 h
      have h3 := hle h
      simp only [Pi.sub_apply] at h2 h3 ⊢
      linarith
    exact ⟨hL hmem, hU hmem⟩
  refine ⟨fun i => ?_, fun j => ?_⟩
  · refine (Metric.isBounded_Icc (ξ i) (ξ i + zetaPrime E ξ + ∑ j, U j - ∑ i', ξ i')).subset ?_
    rintro xi ⟨hxi, x, y, rfl, hx, hy, hle⟩
    obtain ⟨-, hyU⟩ := key x y hx hy hle
    refine ⟨hξ i _ hxi, fun h => ?_⟩
    have h1 : x i h - ξ i h ≤ ∑ i', (x i' h - ξ i' h) :=
      Finset.single_le_sum (f := fun i' => x i' h - ξ i' h)
        (fun i' _ => sub_nonneg.2 (hξ i' _ (hx i') h)) (Finset.mem_univ i)
    have h2 : ∑ j, y j h ≤ ∑ j, U j h := Finset.sum_le_sum fun j _ => hyU j h
    have h3 := hle h
    simp only [Pi.sub_apply, Pi.add_apply, Finset.sum_apply, Finset.sum_sub_distrib] at h1 h2 h3 ⊢
    linarith
  · refine (Metric.isBounded_Icc (L j) (U j)).subset ?_
    rintro yj ⟨hyj, x, y, rfl, hx, hy, hle⟩
    obtain ⟨hyL, hyU⟩ := key x y hx hy hle
    exact ⟨hyL j, hyU j⟩
