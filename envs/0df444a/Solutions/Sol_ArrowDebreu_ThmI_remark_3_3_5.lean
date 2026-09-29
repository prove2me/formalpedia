-- Prove2me | solution 1 for ArrowDebreu.ThmI.remark_3_3_5
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T04:23:45.502889+00:00
-- url     : https://prove2.me/submissions/8bd40c3e-0070-4455-83ba-c0c35937e986

import Mathlib
import Definitions.Def_ArrowDebreu_Shared_Economy
import Definitions.Def_ArrowDebreu_ThmI_AssumptionsItoIV
import Definitions.Def_ArrowDebreu_Shared_IsCompetitiveEquilibrium
import Definitions.Def_ArrowDebreu_Shared_AbstractEconomy
import Definitions.Def_ArrowDebreu_ThmI_economyE
open ArrowDebreu.Shared

namespace ArrowDebreu.ThmI

open AbstractEconomy Filter Topology

lemma aux_rm335_dot {l : ℕ} {f g : ℕ → Fin l → ℝ} {p x : Fin l → ℝ}
    (hf : Tendsto f atTop (𝓝 p)) (hg : Tendsto g atTop (𝓝 x)) :
    Tendsto (fun k => f k ⬝ᵥ g k) atTop (𝓝 (p ⬝ᵥ x)) := by
  simp only [dotProduct]
  exact tendsto_finsetSum _ fun h _ => (tendsto_pi_nhds.1 hf h).mul (tendsto_pi_nhds.1 hg h)

lemma aux_rm335_seq {l : ℕ} {F : ℕ → Set (Fin l → ℝ)} {b₀ : Fin l → ℝ}
    (hne : ∀ k, (F k).Nonempty)
    (h : ∀ ε > 0, ∀ᶠ k in atTop, ∃ x ∈ F k, dist x b₀ < ε) :
    ∃ t : ℕ → Fin l → ℝ, Tendsto t atTop (𝓝 b₀) ∧ ∀ k, t k ∈ F k := by
  have hd : Tendsto (fun k => Metric.infDist b₀ (F k)) atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := eventually_atTop.1 (h ε hε)
    refine ⟨N, fun k hk => ?_⟩
    obtain ⟨x, hx, hdx⟩ := hN k hk
    rw [Real.dist_eq, sub_zero, abs_of_nonneg Metric.infDist_nonneg]
    exact lt_of_le_of_lt (Metric.infDist_le_dist_of_mem hx) (by rwa [dist_comm])
  have hex : ∀ k : ℕ, ∃ x ∈ F k, dist b₀ x < Metric.infDist b₀ (F k) + 1 / ((k : ℝ) + 1) :=
    fun k => (Metric.infDist_lt_iff (hne k)).1
      (by linarith [show (0 : ℝ) < 1 / ((k : ℝ) + 1) by positivity])
  choose t ht hdt using hex
  refine ⟨t, ?_, ht⟩
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero (fun k => dist_nonneg)
    (fun k => (dist_comm (t k) b₀).le.trans (hdt k).le) ?_
  simpa using hd.add tendsto_one_div_add_atTop_nhds_zero_nat

lemma aux_rm335_cube_convex (l : ℕ) (c : ℝ) : Convex ℝ (cube l c) := by
  intro x hx y hy a b ha hb hab h
  simp only [cube, Set.mem_ofPred_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hx hy ⊢
  calc |a * x h + b * y h| ≤ |a * x h| + |b * y h| := abs_add_le _ _
    _ = a * |x h| + b * |y h| := by rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
    _ ≤ a * c + b * c := by gcongr <;> [exact hx h; exact hy h]
    _ = c := by rw [← add_mul, hab, one_mul]

end ArrowDebreu.ThmI

open ArrowDebreu.ThmI
open ArrowDebreu.Shared.AbstractEconomy Filter Topology

theorem solution {l m n : ℕ} (E : Economy l m n) (hII : AssumptionII E) (c : ℝ) (i : Fin m)
    (hne : ∀ b, (economyEtilde E c).OthersIn (Sum.inl i) b →
      ((economyEtilde E c).constr (Sum.inl i) b).Nonempty)
    (a : Player m n → Fin l → ℝ) (ha : (economyEtilde E c).OthersIn (Sum.inl i) a)
    (hmin : ∃ x' ∈ E.X i ∩ cube l c, priceOf a ⬝ᵥ x' < priceOf a ⬝ᵥ E.ζ i) :
    (economyEtilde E c).ConstrContinuousAt (Sum.inl i) a := by
  intro b₀ hb₀ s hs hconv
  obtain ⟨x', hx'X, hx'lt⟩ := hmin
  have hmem : ∀ (b : Player m n → Fin l → ℝ) (x : Fin l → ℝ),
      x ∈ (economyEtilde E c).constr (Sum.inl i) b ↔
        x ∈ E.X i ∩ cube l c ∧ priceOf b ⬝ᵥ x ≤
          priceOf b ⬝ᵥ E.ζ i + max 0 (∑ j, E.α i j * (priceOf b ⬝ᵥ prodOf b j)) :=
    fun b x => Iff.rfl
  have hconvX : Convex ℝ (E.X i ∩ cube l c) := (hII i).2.1.inter (aux_rm335_cube_convex l c)
  have hb₀' := (hmem a b₀).1 hb₀
  refine aux_rm335_seq (fun k => hne (s k) (hs k)) ?_
  intro ε hε
  set v := x' - b₀ with hv
  have hcont : Tendsto (fun μ : ℝ => b₀ + μ • v) (𝓝[>] 0) (𝓝 b₀) := by
    have : Continuous (fun μ : ℝ => b₀ + μ • v) := by fun_prop
    have h0 := this.tendsto 0
    simp only [zero_smul, add_zero] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  obtain ⟨μ, hball, hμ0, hμ1⟩ :=
    ((hcont.eventually (Metric.ball_mem_nhds b₀ hε)).and (Ioo_mem_nhdsGT one_pos)).exists
  have hxμX : b₀ + μ • v ∈ E.X i ∩ cube l c :=
    hconvX.add_smul_sub_mem hb₀'.1 hx'X ⟨hμ0.le, hμ1.le⟩
  have hstrict : priceOf a ⬝ᵥ (b₀ + μ • v) <
      priceOf a ⬝ᵥ E.ζ i + max 0 (∑ j, E.α i j * (priceOf a ⬝ᵥ prodOf a j)) := by
    have h1 := hb₀'.2
    have h2 : 0 ≤ max 0 (∑ j, E.α i j * (priceOf a ⬝ᵥ prodOf a j)) := le_max_left _ _
    have heq : priceOf a ⬝ᵥ (b₀ + μ • v) =
        priceOf a ⬝ᵥ b₀ + μ * (priceOf a ⬝ᵥ x' - priceOf a ⬝ᵥ b₀) := by
      simp [hv, dotProduct_add, dotProduct_smul, dotProduct_sub]
    rw [heq]
    nlinarith
  have hp : Tendsto (fun k => priceOf (s k)) atTop (𝓝 (priceOf a)) :=
    hconv (Sum.inr (Sum.inr ())) (by simp)
  have hy : ∀ j, Tendsto (fun k => prodOf (s k) j) atTop (𝓝 (prodOf a j)) :=
    fun j => hconv (Sum.inr (Sum.inl j)) (by simp)
  have hL : Tendsto (fun k => priceOf (s k) ⬝ᵥ (b₀ + μ • v)) atTop
      (𝓝 (priceOf a ⬝ᵥ (b₀ + μ • v))) := aux_rm335_dot hp tendsto_const_nhds
  have hR : Tendsto (fun k => priceOf (s k) ⬝ᵥ E.ζ i +
      max 0 (∑ j, E.α i j * (priceOf (s k) ⬝ᵥ prodOf (s k) j))) atTop
      (𝓝 (priceOf a ⬝ᵥ E.ζ i + max 0 (∑ j, E.α i j * (priceOf a ⬝ᵥ prodOf a j)))) := by
    refine (aux_rm335_dot hp tendsto_const_nhds).add (tendsto_const_nhds.max ?_)
    exact tendsto_finsetSum _ fun j _ => tendsto_const_nhds.mul (aux_rm335_dot hp (hy j))
  filter_upwards [hL.eventually_lt hR hstrict] with k hk
  exact ⟨b₀ + μ • v, (hmem _ _).2 ⟨hxμX, hk.le⟩, hball⟩
