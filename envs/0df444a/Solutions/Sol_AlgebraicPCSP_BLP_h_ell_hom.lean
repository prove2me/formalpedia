-- Prove2me | solution 1 for AlgebraicPCSP.BLP.h_ell_hom
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-31T00:05:07.354839+00:00
-- url     : https://prove2.me/submissions/da59b647-f968-46e7-93bf-1b3980335ba8

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting
import Definitions.Def_AlgebraicPCSP_BLP_LP
import Theorems.Thm_PCSPBLPAff_Symmetric_rounding_satisfies

open PCSPBLPAff.Symmetric AlgebraicPCSP.BLP

lemma filter_cons_card {A : Type} [DecidableEq A] {L : ℕ} (a₀ : A) (x' : Fin L → A) (a : A) :
    (Finset.univ.filter (fun l : Fin (L + 1) => Fin.cons (α := fun _ => A) a₀ x' l = a)).card =
      (if a₀ = a then 1 else 0) + (Finset.univ.filter (fun l : Fin L => x' l = a)).card := by
  simp only [Finset.card_filter, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]

lemma exists_hasCounts {A : Type} [Fintype A] [DecidableEq A] :
    ∀ {L : ℕ} (W : A → ℕ), ∑ a, W a = L → ∃ x : Fin L → A, HasCounts x W
  | 0, W, hW => by
    have h0 : ∀ a, W a = 0 := fun a =>
      Nat.eq_zero_of_le_zero ((Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)).trans hW.le)
    refine ⟨Fin.elim0, fun a => ?_⟩
    rw [h0 a]
    simp
  | L + 1, W, hW => by
    have hex : ∃ a₀ : A, 0 < W a₀ := by
      by_contra! hle
      have h0 : ∑ a, W a = 0 := Finset.sum_eq_zero (fun a _ => Nat.eq_zero_of_le_zero (hle a))
      omega
    obtain ⟨a₀, ha₀⟩ := hex
    let W' : A → ℕ := Function.update W a₀ (W a₀ - 1)
    have hW' : ∑ a, W' a = L := by
      have hsum1 := Finset.add_sum_erase Finset.univ W (Finset.mem_univ a₀)
      have hsum2 := Finset.add_sum_erase Finset.univ W' (Finset.mem_univ a₀)
      have heq : ∑ a ∈ Finset.univ.erase a₀, W' a = ∑ a ∈ Finset.univ.erase a₀, W a := by
        refine Finset.sum_congr rfl (fun a ha => ?_)
        simp [W', Finset.ne_of_mem_erase ha]
      have ha₀' : W' a₀ = W a₀ - 1 := by simp [W']
      omega
    obtain ⟨x', hx'⟩ := exists_hasCounts W' hW'
    refine ⟨Fin.cons a₀ x', fun a => ?_⟩
    rw [filter_cons_card, hx' a]
    dsimp [W']
    by_cases h : a = a₀
    · subst h
      simp only [ ↓reduceIte, Function.update_self]
      omega
    · have h' : a₀ ≠ a := Ne.symm h
      simp [h, h']

lemma scale_sum_eq {ι : Type} [Fintype ι] {ℓ : ℕ} (hℓ : 0 < ℓ) (f : ι → ℚ) (q : ι → ℕ)
    (hq : ∀ i, f i = (q i : ℚ) / ℓ) (hsum : ∑ i, f i = 1) :
    ∑ i, q i = ℓ := by
  have hℓ0 : (ℓ : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hℓ)
  have h1 : (∑ i, (q i : ℚ)) / (ℓ : ℚ) = 1 := by
    rw [Finset.sum_div]
    simp_rw [← hq]
    exact hsum
  have h2 : (∑ i, q i : ℚ) = (ℓ : ℚ) := by
    have h1' := (div_eq_iff hℓ0).mp h1
    linarith
  exact_mod_cast h2

/-- Proof of Theorem 7.9, p. 48 (arXiv:1811.00970v3): for `ℓ ≥ 1`, if `Pol(𝔸, 𝔹)` contains a
symmetric function `s_ℓ` of arity `ℓ`, then `LP_ℓ(𝔸)` maps homomorphically to `𝔹` (the paper's
`h_ℓ(ϕ) = s_ℓ(a₁, …, a_ℓ)`, each `a` appearing `ϕ(a)ℓ` times, is such a homomorphism). -/
theorem solution {τ : Type} {ar : τ → ℕ} {A B : Type} [Fintype A] [DecidableEq A]
    (𝔸 : RelStruct τ ar A) (𝔹 : RelStruct τ ar B) (ℓ : ℕ) (hℓ : 0 < ℓ)
    (hs : ∃ s : (Fin ℓ → A) → B, IsPolymorphism 𝔸 𝔹 s ∧ IsSymmetric s) :
    ∃ h : LPellDist A ℓ → B, IsHom (LPell 𝔸 ℓ) 𝔹 h := by
  classical
  obtain ⟨s, hpoly, hsym⟩ := hs
  have hW_exists : ∀ ϕ : LPellDist A ℓ, ∃ W : A → ℕ, (∀ a, ϕ.1 a = (W a : ℚ) / ℓ) ∧ ∑ a, W a = ℓ := by
    intro ϕ
    let W : A → ℕ := fun a => Classical.choose (ϕ.2.1 a)
    have hW1 : ∀ a, ϕ.1 a = (W a : ℚ) / ℓ := fun a => (Classical.choose_spec (ϕ.2.1 a)).2
    have hW2 : ∑ a, W a = ℓ := scale_sum_eq hℓ ϕ.1 W hW1 ϕ.2.2
    exact ⟨W, hW1, hW2⟩
  let W_of : LPellDist A ℓ → A → ℕ := fun ϕ => Classical.choose (hW_exists ϕ)
  have hW_eq : ∀ (ϕ : LPellDist A ℓ) (a : A), ϕ.1 a = (W_of ϕ a : ℚ) / ℓ :=
    fun ϕ => (Classical.choose_spec (hW_exists ϕ)).1
  have hW_sum : ∀ ϕ : LPellDist A ℓ, ∑ a, W_of ϕ a = ℓ :=
    fun ϕ => (Classical.choose_spec (hW_exists ϕ)).2
  let x_of : LPellDist A ℓ → Fin ℓ → A :=
    fun ϕ => Classical.choose (exists_hasCounts (W_of ϕ) (hW_sum ϕ))
  have hx_of : ∀ ϕ : LPellDist A ℓ, HasCounts (x_of ϕ) (W_of ϕ) :=
    fun ϕ => Classical.choose_spec (exists_hasCounts (W_of ϕ) (hW_sum ϕ))
  refine ⟨fun ϕ => s (x_of ϕ), ?_⟩
  intro R t ht
  obtain ⟨γ, hγ_denom, hγ_supp, hγ_sum, hγ_marg⟩ := ht
  let P₀ : (Fin (ar R) → A) → ℕ := fun r => Classical.choose (hγ_denom r)
  have hP₀_eq : ∀ r, γ r = (P₀ r : ℚ) / ℓ := fun r => (Classical.choose_spec (hγ_denom r)).2
  have hℓ0 : (ℓ : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hℓ)
  let X : Instance τ ar := {
    n := ar R
    m := 1
    sym := fun _ => R
    scope := fun _ k => k
  }
  let W : Fin X.n → A → ℕ := fun k => W_of (t k)
  let P : (j : Fin X.m) → (Fin (ar (X.sym j)) → A) → ℕ := fun _ => P₀
  have hPsupp : ∀ j y, y ∉ 𝔸.rel (X.sym j) → P j y = 0 := by
    intro j y hy
    have h0 : γ y = 0 := hγ_supp y hy
    have h1 : (P₀ y : ℚ) / ℓ = 0 := by rw [← hP₀_eq y, h0]
    have h2 : (P₀ y : ℚ) = 0 := (div_eq_zero_iff.mp h1).resolve_right hℓ0
    exact_mod_cast h2
  have hPsum : ∀ j, ∑ y, P j y = ℓ := by
    intro j
    exact scale_sum_eq hℓ γ P₀ hP₀_eq hγ_sum
  have h9 : ∀ (j : Fin X.m) (k : Fin (ar (X.sym j))) (a : A),
      W (X.scope j k) a =
        ∑ y ∈ Finset.univ.filter (fun y : Fin (ar (X.sym j)) → A => y k = a), P j y := by
    intro j k a
    have hm := hγ_marg k a
    rw [hW_eq (t k) a] at hm
    simp_rw [hP₀_eq] at hm
    rw [← Finset.sum_div] at hm
    have hq : (∑ y ∈ Finset.univ.filter (fun y : Fin (ar R) → A => y k = a), (P₀ y : ℚ)) =
        (W_of (t k) a : ℚ) := by
      exact (div_left_inj' hℓ0).mp hm
    exact_mod_cast hq.symm
  have hsat := rounding_satisfies 𝔸 𝔹 X s hpoly hsym W P hPsupp hPsum h9 (fun k => x_of (t k))
    (fun k => hx_of (t k)) 0
  exact hsat
