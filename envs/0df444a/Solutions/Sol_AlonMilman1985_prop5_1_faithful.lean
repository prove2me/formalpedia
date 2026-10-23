-- Prove2me | solution 1 for AlonMilman1985.prop5_1_faithful
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T05:51:25.81686+00:00
-- url     : https://prove2.me/submissions/25a51ba1-7cf7-4ae8-a145-36bb504e9a9c

import Mathlib
import Definitions.Def_AlonMilman_Diameter_lambda1
import Theorems.Thm_AlonMilman_Diameter_diameter_le_of_lambda1

open Classical

namespace AP87

variable {H : Type} [Group H] [Fintype H] [DecidableEq H]

lemma adj_iff (γ : Finset H) (hγinv : ∀ g ∈ γ, g⁻¹ ∈ γ) (u w : H) :
    (SimpleGraph.fromRel (fun u v : H => u * v⁻¹ ∈ γ)).Adj u w → w * u⁻¹ ∈ γ ∧ u ≠ w := by
  intro h
  rw [SimpleGraph.fromRel_adj] at h
  obtain ⟨hne, h | h⟩ := h
  · refine ⟨?_, hne⟩
    have := hγinv _ h
    simpa using this
  · exact ⟨h, hne⟩

lemma walk_word (γ : Finset H) (hγinv : ∀ g ∈ γ, g⁻¹ ∈ γ) {u v : H}
    (p : (SimpleGraph.fromRel (fun u v : H => u * v⁻¹ ∈ γ)).Walk u v) :
    ∃ l : List H, (∀ x ∈ l, x ∈ γ) ∧ l.prod = v * u⁻¹ ∧ l.length = p.length := by
  induction p with
  | nil => exact ⟨[], by simp, by simp, by simp⟩
  | @cons a b c hadj q ih =>
    obtain ⟨l, hl, hp, hlen⟩ := ih
    refine ⟨l ++ [b * a⁻¹], ?_, ?_, ?_⟩
    · intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · exact hl x hx
      · simp only [List.mem_singleton] at hx
        subst hx; exact (adj_iff γ hγinv a b hadj).1
    · simp [List.prod_append, hp, mul_assoc]
    · simp [hlen]

lemma degree_le (γ : Finset H) (hγinv : ∀ g ∈ γ, g⁻¹ ∈ γ) (h1 : (1 : H) ∈ γ) (v : H) :
    (SimpleGraph.fromRel (fun u v : H => u * v⁻¹ ∈ γ)).degree v ≤ γ.card - 1 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  have : ((SimpleGraph.fromRel (fun u v : H => u * v⁻¹ ∈ γ)).neighborFinset v).card ≤
      (γ.erase 1).card := by
    apply Finset.card_le_card_of_injOn (fun w => w * v⁻¹)
    · intro w hw
      rw [Finset.mem_coe, SimpleGraph.mem_neighborFinset] at hw
      obtain ⟨hmem, hne⟩ := adj_iff γ hγinv v w hw
      rw [Finset.mem_coe, Finset.mem_erase]
      refine ⟨?_, hmem⟩
      intro h; apply hne; rw [mul_inv_eq_one] at h; exact h.symm
    · intro a _ b _ hab
      simpa using hab
  rw [Finset.card_erase_of_mem h1] at this
  exact this

end AP87

theorem solution {H : Type} [Group H] [Fintype H] [DecidableEq H]
    (γ : Finset H) (hγinv : ∀ g ∈ γ, g⁻¹ ∈ γ) (h1 : (1 : H) ∈ γ)
    (hgen : Subgroup.closure (γ : Set H) = ⊤) (hn : 1 < Fintype.card H) :
    ∀ h : H, ∃ l : List H, (∀ x ∈ l, x ∈ γ) ∧ l.prod = h ∧
      l.length ≤ 2 * ⌊Real.sqrt (2 * ((γ.card - 1 : ℕ) : ℝ) /
          AlonMilman.Diameter.lambda1 (SimpleGraph.fromRel (fun u v : H => u * v⁻¹ ∈ γ))) *
        Real.logb 2 (Fintype.card H : ℝ)⌋₊ := by
  set G := SimpleGraph.fromRel (fun u v : H => u * v⁻¹ ∈ γ) with hGdef
  -- connectivity: every element is reachable from 1
  have hreach : ∀ h : H, G.Reachable 1 h := by
    intro h
    have hmem : h ∈ Subgroup.closure (γ : Set H) := by rw [hgen]; trivial
    induction hmem using Subgroup.closure_induction with
    | mem x hx =>
      by_cases hx1 : x = 1
      · subst hx1; rfl
      · refine SimpleGraph.Adj.reachable ?_
        rw [hGdef, SimpleGraph.fromRel_adj]
        refine ⟨fun h => hx1 h.symm, Or.inr ?_⟩
        simpa using hx
    | one => rfl
    | mul x y _ _ hx hy =>
      -- right multiplication by y is a graph automorphism
      have hauto : ∀ a b : H, G.Adj a b → G.Adj (a * y) (b * y) := by
        intro a b hab
        rw [hGdef, SimpleGraph.fromRel_adj] at hab ⊢
        obtain ⟨hne, hr⟩ := hab
        refine ⟨fun h => hne (mul_right_cancel h), ?_⟩
        simpa [mul_inv_rev, mul_assoc] using hr
      have hy' : G.Reachable y (x * y) := by
        obtain ⟨p⟩ := hx
        let f : G →g G := ⟨fun a => a * y, fun {a b} h => hauto a b h⟩
        have : G.Reachable (f 1) (f x) := ⟨p.map f⟩
        simp [f] at this
        exact this
      exact hy.trans hy'
    | inv x _ hx =>
      obtain ⟨p⟩ := hx
      have hauto : ∀ a b : H, G.Adj a b → G.Adj (a * x⁻¹) (b * x⁻¹) := by
        intro a b hab
        rw [hGdef, SimpleGraph.fromRel_adj] at hab ⊢
        obtain ⟨hne, hr⟩ := hab
        refine ⟨fun h => hne (mul_right_cancel h), ?_⟩
        simpa [mul_inv_rev, mul_assoc] using hr
      let f : G →g G := ⟨fun a => a * x⁻¹, fun {a b} h => hauto a b h⟩
      have : G.Reachable (f 1) (f x) := ⟨p.map f⟩
      simp [f] at this
      exact this.symm
  have hconn : G.Connected := by
    have : Nonempty H := ⟨1⟩
    exact SimpleGraph.Connected.mk (fun a b => (hreach a).symm.trans (hreach b))
  intro h
  obtain ⟨p, hp⟩ := (hreach h).exists_walk_length_eq_dist
  obtain ⟨l, hl, hprod, hlen⟩ := AP87.walk_word γ hγinv p
  refine ⟨l, hl, by simpa using hprod, ?_⟩
  have hd := AlonMilman.Diameter.diameter_le_of_lambda1 G hconn hn 1 h
  rw [hlen, hp]
  refine hd.trans ?_
  apply Nat.mul_le_mul_left
  apply Nat.floor_le_floor
  have hlog : 0 ≤ Real.logb 2 (Fintype.card H : ℝ) := by
    apply Real.logb_nonneg (by norm_num)
    exact_mod_cast hn.le
  apply mul_le_mul_of_nonneg_right _ hlog
  have hdeg : (G.maxDegree : ℝ) ≤ ((γ.card - 1 : ℕ) : ℝ) := by
    exact_mod_cast G.maxDegree_le_of_forall_degree_le _ (AP87.degree_le γ hγinv h1)
  rcases le_or_gt (AlonMilman.Diameter.lambda1 G) 0 with hl0 | hl0
  · have e1 : 2 * (G.maxDegree : ℝ) / AlonMilman.Diameter.lambda1 G ≤ 0 :=
      div_nonpos_of_nonneg_of_nonpos (by positivity) hl0
    rw [Real.sqrt_eq_zero'.2 e1]
    exact Real.sqrt_nonneg _
  · apply Real.sqrt_le_sqrt
    apply div_le_div_of_nonneg_right _ hl0.le
    linarith
