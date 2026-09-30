-- Prove2me | solution 1 for ArrowDebreu.ThmI.Yhat_bounded
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T21:40:51.257474+00:00
-- url     : https://prove2.me/submissions/2d883947-9aed-4a81-95f4-01503510f949

import Mathlib
import Definitions.Def_ArrowDebreu_Shared_Economy
import Definitions.Def_ArrowDebreu_ThmI_AssumptionsItoIV
import Definitions.Def_ArrowDebreu_Shared_IsCompetitiveEquilibrium
import Definitions.Def_ArrowDebreu_Shared_AbstractEconomy
import Definitions.Def_ArrowDebreu_ThmI_economyE
open ArrowDebreu.Shared

open Filter Topology

namespace ArrowDebreu.ThmI

namespace YhatAux

variable {l m n : ℕ}

/-- The attainable production tuples `(y_1, ⋯, y_n)`: `y_j ∈ Y_j` for all `j`, completed by some
`x_i ∈ X_i` with `z ≦ 0`. -/
def attainableProd (E : Economy l m n) : Set (Fin n → Fin l → ℝ) :=
  {y | (∀ j, y j ∈ E.Y j) ∧
    ∃ x : Fin m → Fin l → ℝ, (∀ i, x i ∈ E.X i) ∧ excessDemand E x y ≤ 0}

/-- A vector of `Y_j` lies in the aggregate production set (the other producers do nothing). -/
theorem mem_aggProd_of_mem (E : Economy l m n) (hIa : AssumptionIa E) (j : Fin n)
    {v : Fin l → ℝ} (hv : v ∈ E.Y j) : v ∈ aggProd E := by
  classical
  refine ⟨Pi.single j v, fun j' => ?_, ?_⟩
  · by_cases h : j' = j
    · subst h; simpa using hv
    · rw [Pi.single_eq_of_ne h]; exact (hIa j').2.2
  · simp

/-- If `Σ_j w_j = 0` with `w_j ∈ Y_j`, then `−w_j = Σ_{j' ≠ j} w_{j'}` lies in `Y`. -/
theorem neg_mem_aggProd (E : Economy l m n) (hIa : AssumptionIa E) (w : Fin n → Fin l → ℝ)
    (hw : ∀ j, w j ∈ E.Y j) (hsum : ∑ j, w j = 0) (j : Fin n) : -w j ∈ aggProd E := by
  classical
  refine ⟨Function.update w j 0, fun j' => ?_, ?_⟩
  · by_cases h : j' = j
    · subst h; simpa using (hIa j').2.2
    · rw [Function.update_of_ne h]; exact hw j'
  · rw [Finset.sum_update_of_mem (Finset.mem_univ j), zero_add]
    have h := Finset.sum_eq_add_sum_sdiff_singleton_of_mem (Finset.mem_univ j) w
    rw [hsum] at h
    exact (eq_neg_of_add_eq_zero_right h.symm).symm

/-- **§3.3.1**: the set of attainable production tuples is bounded. -/
theorem attainableProd_bounded (E : Economy l m n) (hIa : AssumptionIa E) (hIb : AssumptionIb E)
    (hIc : AssumptionIc E) (hII : AssumptionII E) :
    Bornology.IsBounded (attainableProd E) := by
  classical
  choose ξ hξ using fun i => (hII i).2.2
  set L : Fin l → ℝ := ∑ i, ξ i - ∑ i, E.ζ i with hL
  have hlow : ∀ y ∈ attainableProd E, ∀ h, L h ≤ ∑ j, y j h := by
    rintro y ⟨_, x, hx, hz⟩ h
    have h1 : ∑ i, ξ i h ≤ ∑ i, x i h :=
      Finset.sum_le_sum (fun i _ => hξ i (x i) (hx i) h)
    have h2 := hz h
    simp only [excessDemand, Pi.sub_apply, Finset.sum_apply, Pi.zero_apply] at h2
    simp only [hL, Pi.sub_apply, Finset.sum_apply]
    linarith
  by_contra hnb
  rw [isBounded_iff_forall_norm_le] at hnb
  have hnb' : ∀ C : ℝ, ∃ y ∈ attainableProd E, C < ‖y‖ := by
    intro C
    by_contra hcon
    apply hnb
    refine ⟨C, fun x hx => ?_⟩
    by_contra hlt
    exact hcon ⟨x, hx, not_le.1 hlt⟩
  choose y hyT hyn using fun k : ℕ => hnb' ((k:ℝ) + 1)
  set μ : ℕ → ℝ := fun k => ‖y k‖ with hμ
  have hμge : ∀ k : ℕ, (k:ℝ) + 1 ≤ μ k := fun k => (hyn k).le
  have hμpos : ∀ k : ℕ, 0 < μ k := fun k => lt_of_lt_of_le (by positivity) (hμge k)
  have hμ1 : ∀ k : ℕ, 1 ≤ μ k := fun k => le_trans (by linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]) (hμge k)
  set w : ℕ → Fin n → Fin l → ℝ := fun k => (μ k)⁻¹ • y k with hw
  have hwnorm : ∀ k, ‖w k‖ = 1 := by
    intro k
    show ‖(μ k)⁻¹ • y k‖ = 1
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos (hμpos k)]
    exact inv_mul_cancel₀ (hμpos k).ne'
  have hwball : ∀ k, w k ∈ Metric.closedBall (0 : Fin n → Fin l → ℝ) 1 := by
    intro k
    rw [Metric.mem_closedBall, dist_zero_right, hwnorm]
  obtain ⟨w₀, -, φ, hφ, hlim⟩ :=
    (isCompact_closedBall (0 : Fin n → Fin l → ℝ) 1).tendsto_subseq hwball
  have hw₀norm : ‖w₀‖ = 1 := by
    have h1 : Tendsto (fun k => ‖(w ∘ φ) k‖) atTop (𝓝 ‖w₀‖) := hlim.norm
    have h2 : Tendsto (fun k => ‖(w ∘ φ) k‖) atTop (𝓝 1) := by
      have : (fun k => ‖(w ∘ φ) k‖) = fun _ => (1:ℝ) := funext (fun k => hwnorm (φ k))
      rw [this]
      exact tendsto_const_nhds
    exact tendsto_nhds_unique h1 h2
  -- coordinates of the limit lie in the production sets
  have hw₀Y : ∀ j, w₀ j ∈ E.Y j := by
    intro j
    refine (hIa j).1.mem_of_tendsto (tendsto_pi_nhds.1 hlim j) (Eventually.of_forall fun k => ?_)
    show (μ (φ k))⁻¹ • y (φ k) j ∈ E.Y j
    have hinv1 : (μ (φ k))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (hμ1 (φ k))
    have := (hIa j).2.1 ((hyT (φ k)).1 j) (hIa j).2.2 (inv_nonneg.2 (hμpos _).le)
      (sub_nonneg.2 hinv1) (add_sub_cancel _ _)
    simpa using this
  -- the sum of the limit is nonnegative
  have hμφ : Tendsto (fun k => μ (φ k)) atTop atTop := by
    refine tendsto_atTop_mono (fun k => ?_) tendsto_natCast_atTop_atTop
    have : (k:ℝ) ≤ φ k := by exact_mod_cast hφ.id_le k
    linarith [hμge (φ k)]
  have hμinv : Tendsto (fun k => (μ (φ k))⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hμφ
  have hw₀sum : ∀ h, 0 ≤ (∑ j, w₀ j) h := by
    intro h
    rw [Finset.sum_apply]
    have hS : Tendsto (fun k => ∑ j, (w ∘ φ) k j h) atTop (𝓝 (∑ j, w₀ j h)) :=
      tendsto_finsetSum _ (fun j _ => tendsto_pi_nhds.1 (tendsto_pi_nhds.1 hlim j) h)
    have hLk : Tendsto (fun k => (μ (φ k))⁻¹ * L h) atTop (𝓝 0) := by
      simpa using hμinv.mul_const (L h)
    refine le_of_tendsto_of_tendsto' hLk hS (fun k => ?_)
    have hb := hlow (y (φ k)) (hyT (φ k)) h
    have hsum : ∑ j, (w ∘ φ) k j h = (μ (φ k))⁻¹ * ∑ j, y (φ k) j h := by
      rw [Finset.mul_sum]
      rfl
    rw [hsum]
    exact mul_le_mul_of_nonneg_left hb (inv_nonneg.2 (hμpos _).le)
  have hsum0 : ∑ j, w₀ j = 0 := by
    have hmem : ∑ j, w₀ j ∈ aggProd E ∩ Ω l := ⟨⟨w₀, hw₀Y, rfl⟩, fun h => hw₀sum h⟩
    rw [hIb] at hmem
    exact hmem
  have hzero : ∀ j, w₀ j = 0 := by
    intro j
    have hmem : w₀ j ∈ aggProd E ∩ negSet (aggProd E) :=
      ⟨mem_aggProd_of_mem E hIa j (hw₀Y j), neg_mem_aggProd E hIa w₀ hw₀Y hsum0 j⟩
    rw [hIc] at hmem
    exact hmem
  have : w₀ = 0 := funext hzero
  rw [this, norm_zero] at hw₀norm
  exact zero_ne_one hw₀norm

end YhatAux

end ArrowDebreu.ThmI

open ArrowDebreu.ThmI ArrowDebreu.ThmI.YhatAux
open ArrowDebreu.Shared

theorem solution {l m n : ℕ} (E : Economy l m n) (hIa : AssumptionIa E) (hIb : AssumptionIb E)
    (hIc : AssumptionIc E) (hII : AssumptionII E) :
    ∀ j, Bornology.IsBounded (Yhat E j) := by
  intro j
  obtain ⟨C, hC⟩ :=
    isBounded_iff_forall_norm_le.1 (attainableProd_bounded E hIa hIb hIc hII)
  refine isBounded_iff_forall_norm_le.2 ⟨C, fun yj hyj => ?_⟩
  obtain ⟨_, x, y, rfl, hx, hy, hz⟩ := hyj
  exact le_trans (norm_le_pi_norm y j) (hC y ⟨hy, x, hx, hz⟩)

