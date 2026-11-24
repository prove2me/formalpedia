-- Prove2me | solution 1 for ArithmeticKakeya.lemm_sums_differences_barrier
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-24T22:50:19.679603+00:00
-- url     : https://prove2.me/submissions/1f0aa840-e287-4056-98b3-a39a2ba3a542
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_ArithmeticKakeya_grid
import Definitions.Def_ArithmeticKakeya_forcing
import Theorems.Thm_LefebvreVariations_sums_differences_lemm_witness

set_option autoImplicit false

open ArithmeticKakeya

/-!
# Reduction of `ArithmeticKakeya.lemm_sums_differences_barrier` to Lemm's counterexample

Everything is proved except `LefebvreVariations.sums_differences_lemm_witness` (a finite set `G`
with `|A -_G B|^50000 > max(|A|,|B|,|A +_G B|)^88949`, the content of Lemm's theorem
`¬SD(0,1,∞;α)` for some `α > 1.77898`).
* `count_main`, `forces_inj`, `sound`: for any forcing constructible proof with labels in `X` and
  any finite `S ⊂ ℤ²` on which `g ↦ g.1 - g.2` is injective, `|S|^n ≤ N^(m+r) |S|^t`, where
  `N ≥ |x·S|` for `x ∈ X` (same proof as for `constructible_proof_implies_AK`).
* Apply it to a section of the difference map in Lemm's set: `|S| = |A -_G B|`, `N = max`.
-/


private lemma foldr_eq_flatMap {α β : Type} (f : α → List β) (l : List α) :
    l.foldr (fun a acc => f a ++ acc) [] = l.flatMap f := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.foldr, ih, List.flatMap_cons]

private lemma grid_nil : grid [] = [[]] := rfl

private lemma grid_cons (d : ℕ) (ds : List ℕ) :
    grid (d :: ds) = (List.range' 1 d).flatMap (fun a => (grid ds).map (fun t => a :: t)) := by
  rw [grid, foldr_eq_flatMap]

private lemma grid_append (l₁ l₂ : List ℕ) :
    grid (l₁ ++ l₂) = (grid l₁).flatMap (fun a => (grid l₂).map (fun t => a ++ t)) := by
  induction l₁ with
  | nil => simp [grid_nil]
  | cons d ds ih =>
    rw [List.cons_append, grid_cons, grid_cons, ih, List.flatMap_assoc]
    congr 1; funext a
    rw [List.map_flatMap, List.flatMap_map]
    simp [Function.comp_def]

private lemma mem_grid_cons (d : ℕ) (ds : List ℕ) (e : List ℕ) :
    e ∈ grid (d :: ds) ↔ ∃ a t, e = a :: t ∧ 1 ≤ a ∧ a ≤ d ∧ t ∈ grid ds := by
  rw [grid_cons]
  simp only [List.mem_flatMap, List.mem_range'_1, List.mem_map]
  constructor
  · rintro ⟨a, ⟨h1, h2⟩, t, ht, rfl⟩; exact ⟨a, t, rfl, h1, by omega, ht⟩
  · rintro ⟨a, t, rfl, h1, h2, ht⟩; exact ⟨a, ⟨h1, by omega⟩, t, ht, rfl⟩

private lemma mem_grid_append (l₁ l₂ : List ℕ) (e : List ℕ) :
    e ∈ grid (l₁ ++ l₂) ↔ ∃ a t, e = a ++ t ∧ a ∈ grid l₁ ∧ t ∈ grid l₂ := by
  rw [grid_append]
  simp only [List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨a, ha, t, ht, rfl⟩; exact ⟨a, t, rfl, ha, ht⟩
  · rintro ⟨a, t, rfl, ha, ht⟩; exact ⟨a, ha, t, ht, rfl⟩

private lemma mem_grid_single (d : ℕ) (e : List ℕ) :
    e ∈ grid [d] ↔ ∃ j, e = [j] ∧ 1 ≤ j ∧ j ≤ d := by
  rw [mem_grid_cons]
  constructor
  · rintro ⟨a, t, rfl, h1, h2, ht⟩
    simp [grid_nil] at ht; subst ht; exact ⟨a, rfl, h1, h2⟩
  · rintro ⟨j, rfl, h1, h2⟩; exact ⟨j, [], rfl, h1, h2, by simp [grid_nil]⟩

private lemma mem_grid_snoc (ds : List ℕ) (d : ℕ) (e : List ℕ) :
    e ∈ grid (ds ++ [d]) ↔ ∃ a j, e = a ++ [j] ∧ a ∈ grid ds ∧ 1 ≤ j ∧ j ≤ d := by
  rw [mem_grid_append]
  constructor
  · rintro ⟨a, t, rfl, ha, ht⟩
    obtain ⟨j, rfl, h1, h2⟩ := (mem_grid_single d t).1 ht
    exact ⟨a, j, rfl, ha, h1, h2⟩
  · rintro ⟨a, j, rfl, ha, h1, h2⟩
    exact ⟨a, [j], rfl, ha, (mem_grid_single d _).2 ⟨j, rfl, h1, h2⟩⟩

private lemma length_of_mem_grid : ∀ (ds e : List ℕ), e ∈ grid ds → e.length = ds.length
  | [], e, h => by simp [grid_nil] at h; simp [h]
  | d :: ds, e, h => by
    obtain ⟨a, t, rfl, -, -, ht⟩ := (mem_grid_cons d ds e).1 h
    simp [length_of_mem_grid ds t ht]

private lemma grid_nodup : ∀ ds : List ℕ, (grid ds).Nodup
  | [] => by simp [grid_nil]
  | d :: ds => by
    rw [grid_cons, List.nodup_flatMap]
    refine ⟨fun a _ => (grid_nodup ds).map (fun x y h => by simpa using h), ?_⟩
    refine List.Pairwise.imp_of_mem ?_ (List.nodup_range' (step := 1) (by omega))
    intro a b _ _ hab
    simp only [Function.onFun, List.disjoint_iff_ne, List.mem_map]
    rintro _ ⟨t, _, rfl⟩ _ ⟨u, _, rfl⟩ h
    exact hab (List.cons.inj h).1
open Finset

/-- Jensen for `log`: `Σ log z ≤ |s| log (Σ z / |s|)`. -/
private lemma sum_log_le {ι : Type} (s : Finset ι) (hs : s.Nonempty) (z : ι → ℝ)
    (hz : ∀ i ∈ s, 0 < z i) :
    ∑ i ∈ s, Real.log (z i) ≤ (s.card : ℝ) * Real.log ((∑ i ∈ s, z i) / s.card) := by
  have hc : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
  have h := (strictConcaveOn_log_Ioi.concaveOn).le_map_sum (t := s) (w := fun _ => 1 / (s.card : ℝ))
    (p := z) (fun _ _ => by positivity) (by simp [Finset.sum_const]; field_simp)
    (fun i hi => hz i hi)
  simp only [smul_eq_mul] at h
  rw [← Finset.mul_sum, ← Finset.mul_sum] at h
  have e : (s.card : ℝ)⁻¹ * ∑ i ∈ s, z i = (∑ i ∈ s, z i) / s.card := by
    rw [div_eq_inv_mul]
  rw [one_div, e] at h
  calc ∑ i ∈ s, Real.log (z i) = s.card * ((s.card : ℝ)⁻¹ * ∑ i ∈ s, Real.log (z i)) := by
        field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left h hc.le

/-- Fiber swap: `Σ_{y} (1/a y) Σ_{x ∈ fib y} g x = Σ_x g x`. -/
private lemma fiber_swap {β γ : Type} [DecidableEq γ] (C : Finset β) (F : β → γ) (g : β → ℝ) :
    ∑ y ∈ C, (1 / ((C.filter (fun x => F x = F y)).card : ℝ)) *
      ∑ x ∈ C.filter (fun x => F x = F y), g x = ∑ x ∈ C, g x := by
  simp_rw [Finset.mul_sum, Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun x hx => ?_)
  have : ∀ y ∈ C, (if F x = F y then 1 / ((C.filter (fun x' => F x' = F y)).card : ℝ) * g x else 0)
      = if F y = F x then 1 / ((C.filter (fun x' => F x' = F x)).card : ℝ) * g x else 0 := by
    intro y _
    by_cases h : F x = F y
    · rw [if_pos h, if_pos h.symm, h]
    · rw [if_neg h, if_neg (Ne.symm h)]
  rw [Finset.sum_congr rfl this, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have hpos : (0 : ℝ) < (C.filter (fun x' => F x' = F x)).card := by
    exact_mod_cast Finset.card_pos.2 ⟨x, by simp [hx]⟩
  field_simp

/-- `Σ_y 1/|fib y| = |F(C)|`. -/
private lemma sum_inv_fiber {β γ : Type} [DecidableEq γ] (C : Finset β) (F : β → γ) :
    ∑ y ∈ C, (1 / ((C.filter (fun x => F x = F y)).card : ℝ)) = (C.image F).card := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := F) (t := C.image F)
    (fun y hy => Finset.mem_image_of_mem F hy)]
  rw [Finset.card_eq_sum_ones, Nat.cast_sum]
  refine Finset.sum_congr rfl (fun z hz => ?_)
  obtain ⟨x0, hx0, rfl⟩ := Finset.mem_image.1 hz
  have : ∀ y ∈ C.filter (fun y => F y = F x0),
      (1 / ((C.filter (fun x => F x = F y)).card : ℝ)) =
        1 / ((C.filter (fun x => F x = F x0)).card : ℝ) := by
    intro y hy; rw [(Finset.mem_filter.1 hy).2]
  rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul]
  have hpos : (0 : ℝ) < (C.filter (fun x => F x = F x0)).card := by
    exact_mod_cast Finset.card_pos.2 ⟨x0, by simp [hx0]⟩
  field_simp; simp

/-- The abstract chain bound. -/
private lemma chain_bound {β γ : Type} [DecidableEq γ] (C : Finset β) (hC : C.Nonempty)
    (F : ℕ → β → γ) (cnt : ℕ → β → ℕ) (B : ℕ → ℕ)
    (h1 : ∀ ψ ∈ C, 1 ≤ cnt 1 ψ)
    (hrec : ∀ j, 1 ≤ j → ∀ ψ' ∈ C,
      ∑ ψ ∈ C.filter (fun ψ => F j ψ = F j ψ'), cnt j ψ ≤ cnt (j + 1) ψ')
    (hB : ∀ j, (C.image (F j)).card ≤ B j) :
    ∀ d, 1 ≤ d → (C.card : ℝ) ^ d ≤ (∑ ψ ∈ C, (cnt d ψ : ℝ)) * ∏ j ∈ Finset.Ico 1 d, (B j : ℝ) := by
  set c : ℝ := (C.card : ℝ) with hc_def
  have hc : 0 < c := by rw [hc_def]; exact_mod_cast hC.card_pos
  have hBpos : ∀ j, (0 : ℝ) < B j := by
    intro j
    have := hB j
    have : 0 < (C.image (F j)).card := Finset.card_pos.2 (hC.image _)
    exact_mod_cast (by omega : 0 < B j)
  -- main invariant
  have key : ∀ j, 1 ≤ j → (∀ ψ ∈ C, 1 ≤ cnt j ψ) ∧
      ∑ j' ∈ Finset.Ico 1 j, c * Real.log (c / B j') ≤ ∑ ψ ∈ C, Real.log (cnt j ψ) := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base =>
      refine ⟨h1, ?_⟩
      simp only [Finset.Ico_self, Finset.sum_empty]
      exact Finset.sum_nonneg (fun ψ hψ => Real.log_nonneg (by exact_mod_cast h1 ψ hψ))
    | succ j hj ih =>
      obtain ⟨hpos, hL⟩ := ih
      set fib : β → Finset β := fun ψ' => C.filter (fun ψ => F j ψ = F j ψ') with hfib
      have hmem : ∀ ψ' ∈ C, ψ' ∈ fib ψ' := fun ψ' h => by simp [hfib, h]
      have hpos' : ∀ ψ' ∈ C, 1 ≤ cnt (j + 1) ψ' := by
        intro ψ' hψ'
        calc 1 ≤ cnt j ψ' := hpos ψ' hψ'
          _ ≤ ∑ ψ ∈ fib ψ', cnt j ψ :=
              Finset.single_le_sum (f := fun ψ => cnt j ψ) (fun _ _ => Nat.zero_le _) (hmem ψ' hψ')
          _ ≤ _ := hrec j hj ψ' hψ'
      refine ⟨hpos', ?_⟩
      -- pointwise bound
      have pt : ∀ ψ' ∈ C, Real.log ((fib ψ').card) +
          (1 / ((fib ψ').card : ℝ)) * ∑ ψ ∈ fib ψ', Real.log (cnt j ψ) ≤
            Real.log (cnt (j + 1) ψ') := by
        intro ψ' hψ'
        have hne : (fib ψ').Nonempty := ⟨ψ', hmem ψ' hψ'⟩
        have ha : (0 : ℝ) < (fib ψ').card := by exact_mod_cast hne.card_pos
        have hcp : ∀ ψ ∈ fib ψ', (0 : ℝ) < cnt j ψ := fun ψ h => by
          have := hpos ψ (Finset.mem_filter.1 h).1; exact_mod_cast (by omega : 0 < cnt j ψ)
        have hJ := sum_log_le (fib ψ') hne (fun ψ => (cnt j ψ : ℝ)) hcp
        have hsum : (0 : ℝ) < ∑ ψ ∈ fib ψ', (cnt j ψ : ℝ) := Finset.sum_pos hcp hne
        have hle : (∑ ψ ∈ fib ψ', (cnt j ψ : ℝ)) ≤ cnt (j + 1) ψ' := by
          exact_mod_cast hrec j hj ψ' hψ'
        rw [Real.log_div hsum.ne' ha.ne'] at hJ
        have h2 : Real.log (∑ ψ ∈ fib ψ', (cnt j ψ : ℝ)) ≤ Real.log (cnt (j + 1) ψ') :=
          Real.log_le_log hsum hle
        have h3 : (1 / ((fib ψ').card : ℝ)) * ∑ ψ ∈ fib ψ', Real.log (cnt j ψ) ≤
            Real.log (∑ ψ ∈ fib ψ', (cnt j ψ : ℝ)) - Real.log ((fib ψ').card) := by
          rw [one_div, inv_mul_le_iff₀ ha]; linarith
        linarith
      have hsumpt := Finset.sum_le_sum pt
      rw [Finset.sum_add_distrib, fiber_swap C (F j) (fun ψ => Real.log (cnt j ψ))] at hsumpt
      -- Σ log a ≥ c log (c / B j)
      have hA : c * Real.log (c / B j) ≤ ∑ ψ' ∈ C, Real.log ((fib ψ').card) := by
        have hz : ∀ ψ' ∈ C, (0 : ℝ) < 1 / ((fib ψ').card : ℝ) := fun ψ' h => by
          have : (0 : ℝ) < (fib ψ').card := by exact_mod_cast Finset.card_pos.2 ⟨ψ', hmem ψ' h⟩
          positivity
        have hJ := sum_log_le C hC (fun ψ' => 1 / ((fib ψ').card : ℝ)) hz
        rw [sum_inv_fiber C (F j)] at hJ
        simp only [one_div, Real.log_inv, Finset.sum_neg_distrib] at hJ
        have him : (0 : ℝ) < (C.image (F j)).card := by exact_mod_cast (hC.image _).card_pos
        have hle : Real.log ((C.image (F j)).card / c) ≤ Real.log (B j / c) :=
          Real.log_le_log (by positivity) (by
            apply div_le_div_of_nonneg_right _ hc.le; exact_mod_cast hB j)
        have : Real.log (c / B j) = - Real.log (B j / c) := by
          rw [← Real.log_inv, inv_div]
        rw [this]
        nlinarith
      rw [Finset.sum_Ico_succ_top hj]
      linarith
  intro d hd
  obtain ⟨hpos, hL⟩ := key d hd
  have hcp : ∀ ψ ∈ C, (0 : ℝ) < cnt d ψ := fun ψ h => by
    have := hpos ψ h; exact_mod_cast (by omega : 0 < cnt d ψ)
  have hJ := sum_log_le C hC (fun ψ => (cnt d ψ : ℝ)) hcp
  have hS : (0 : ℝ) < ∑ ψ ∈ C, (cnt d ψ : ℝ) := Finset.sum_pos hcp hC
  have hP : (0 : ℝ) < ∏ j ∈ Finset.Ico 1 d, (B j : ℝ) := Finset.prod_pos (fun j _ => hBpos j)
  -- log (c^d / ∏ B) ≤ log Σ
  have hlog : Real.log (c ^ d / ∏ j ∈ Finset.Ico 1 d, (B j : ℝ)) ≤
      Real.log (∑ ψ ∈ C, (cnt d ψ : ℝ)) := by
    rw [Real.log_div (by positivity) hP.ne', Real.log_pow, Real.log_prod (fun j _ => (hBpos j).ne')]
    have e1 : ∑ j' ∈ Finset.Ico 1 d, c * Real.log (c / B j') =
        c * (((d : ℝ) - 1) * Real.log c - ∑ j ∈ Finset.Ico 1 d, Real.log (B j)) := by
      rw [← Finset.mul_sum]; congr 1
      simp_rw [Real.log_div hc.ne' (hBpos _).ne']
      rw [Finset.sum_sub_distrib, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
      push_cast [Nat.cast_sub hd]; ring
    rw [e1] at hL
    rw [Real.log_div hS.ne' hc.ne'] at hJ
    have : c * (((d : ℝ) - 1) * Real.log c - ∑ j ∈ Finset.Ico 1 d, Real.log (B j)) ≤
        c * (Real.log (∑ ψ ∈ C, (cnt d ψ : ℝ)) - Real.log c) := by linarith
    have := le_of_mul_le_mul_left this hc
    linarith
  have := (Real.log_le_log_iff (by positivity) hS).1 hlog
  rwa [div_le_iff₀ hP] at this

/-! ## Copies of a constructible graph -/

private def dot (x g : ℤ × ℤ) : ℤ := x.1 * g.1 + x.2 * g.2

private def dD (dims : List ℕ) (i : ℕ) : List ℕ := dims.take i ++ [dims.getD i 0 - 1]

private def sL (a : List ℕ) : List ℕ := a.dropLast ++ [a.getLastD 0 + 1]

private lemma sL_snoc (a : List ℕ) (j : ℕ) : sL (a ++ [j]) = a ++ [j + 1] := by
  simp [sL]

private def IsCopy (S : Finset (ℤ × ℤ)) (lab : ℕ → List ℕ → ℤ × ℤ) (dims : List ℕ)
    (φ : List ℕ → ℤ × ℤ) : Prop :=
  (∀ e ∈ grid dims, φ e ∈ S) ∧ (∀ e, e ∉ grid dims → φ e = 0) ∧
  ∀ i < dims.length, ∀ a ∈ grid (dD dims i), ∀ c ∈ grid (dims.drop (i + 1)),
    dot (lab i a) (φ (a ++ c)) = dot (lab i a) (φ (sL a ++ c))

open Classical in
private noncomputable def Copies (S : Finset (ℤ × ℤ)) (lab : ℕ → List ℕ → ℤ × ℤ)
    (dims : List ℕ) : Finset (List ℕ → ℤ × ℤ) :=
  ((Finset.pi (grid dims).toFinset (fun _ => S)).image
    (fun g e => if h : e ∈ (grid dims).toFinset then g e h else 0)).filter (IsCopy S lab dims)

private lemma mem_Copies {S : Finset (ℤ × ℤ)} {lab : ℕ → List ℕ → ℤ × ℤ} {dims : List ℕ}
    {φ : List ℕ → ℤ × ℤ} : φ ∈ Copies S lab dims ↔ IsCopy S lab dims φ := by
  classical
  unfold Copies
  rw [Finset.mem_filter]
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  rw [Finset.mem_image]
  refine ⟨fun e _ => φ e, ?_, ?_⟩
  · rw [Finset.mem_pi]; intro e he; exact h.1 e (List.mem_toFinset.1 he)
  · funext e
    split_ifs with he
    · rfl
    · exact (h.2.1 e (fun h' => he (List.mem_toFinset.2 h'))).symm

private lemma dD_snoc_lt (ds : List ℕ) (d i : ℕ) (hi : i < ds.length) :
    dD (ds ++ [d]) i = dD ds i := by
  simp only [dD]
  rw [List.take_append_of_le_length hi.le, List.getD_append _ _ _ _ hi]

private lemma dD_snoc_eq (ds : List ℕ) (d : ℕ) : dD (ds ++ [d]) ds.length = ds ++ [d - 1] := by
  simp [dD]

private lemma drop_snoc_lt (ds : List ℕ) (d i : ℕ) (hi : i < ds.length) :
    (ds ++ [d]).drop (i + 1) = ds.drop (i + 1) ++ [d] := by
  rw [List.drop_append_of_le_length (by omega)]

private lemma snoc_ne_nil_mem {ds : List ℕ} {a : List ℕ} {j : ℕ} (d : ℕ) (h : a ++ [j] ∈ grid (ds ++ [d])) :
    a ∈ grid ds ∧ 1 ≤ j ∧ j ≤ d := by
  obtain ⟨a', j', he, ha, h1, h2⟩ := (mem_grid_snoc ds d _).1 h
  obtain ⟨rfl, hj⟩ := List.append_inj' he rfl
  simp at hj; subst hj; exact ⟨ha, h1, h2⟩

/-- edge endpoints are vertices, and distinct -/
private lemma edge_mem (dims : List ℕ) (i : ℕ) (hi : i < dims.length) (a c : List ℕ)
    (ha : a ∈ grid (dD dims i)) (hc : c ∈ grid (dims.drop (i + 1))) :
    a ++ c ∈ grid dims ∧ sL a ++ c ∈ grid dims ∧ a ++ c ≠ sL a ++ c := by
  have hsplit : dims = dims.take i ++ [dims.getD i 0] ++ dims.drop (i + 1) := by
    rw [List.getD_eq_getElem _ _ hi]
    simp
  simp only [dD] at ha
  obtain ⟨a', j, rfl, ha', h1, h2⟩ := (mem_grid_snoc _ _ _).1 ha
  rw [sL_snoc]
  refine ⟨?_, ?_, ?_⟩
  · rw [hsplit, mem_grid_append]
    exact ⟨a' ++ [j], c, rfl, (mem_grid_snoc _ _ _).2 ⟨a', j, rfl, ha', h1, by omega⟩, hc⟩
  · rw [hsplit, mem_grid_append]
    exact ⟨a' ++ [j + 1], c, rfl, (mem_grid_snoc _ _ _).2 ⟨a', j + 1, rfl, ha', by omega, by omega⟩, hc⟩
  · intro h
    simp at h

/-- the last layer of a copy is a copy -/
private lemma layer_copy {S : Finset (ℤ × ℤ)} {lab : ℕ → List ℕ → ℤ × ℤ} {ds : List ℕ} {j : ℕ}
    {φ : List ℕ → ℤ × ℤ} (h : IsCopy S lab (ds ++ [j]) φ) (j' : ℕ) (h1 : 1 ≤ j') (h2 : j' ≤ j) :
    IsCopy S lab ds (fun a => φ (a ++ [j'])) := by
  obtain ⟨hS, hz, hc⟩ := h
  refine ⟨fun a ha => hS _ ((mem_grid_snoc _ _ _).2 ⟨a, j', rfl, ha, h1, h2⟩),
    fun a ha => hz _ (fun h' => ha (snoc_ne_nil_mem j h').1), ?_⟩
  intro i hi a ha c hc'
  have := hc i (by simp; omega) a (by rw [dD_snoc_lt _ _ _ hi]; exact ha) (c ++ [j'])
    (by rw [drop_snoc_lt _ _ _ hi]; exact (mem_grid_snoc _ _ _).2 ⟨c, j', rfl, hc', h1, h2⟩)
  simpa [List.append_assoc] using this

/-- extension of a copy by one more layer -/
private def extL (φ ψ : List ℕ → ℤ × ℤ) (j : ℕ) : List ℕ → ℤ × ℤ := fun e =>
  if e.getLast? = some (j + 1) then ψ e.dropLast else φ e

private lemma extL_snoc (φ ψ : List ℕ → ℤ × ℤ) (j : ℕ) (a : List ℕ) (j' : ℕ) :
    extL φ ψ j (a ++ [j']) = if j' = j + 1 then ψ a else φ (a ++ [j']) := by
  simp [extL]

private lemma grid_snoc_mono {ds : List ℕ} {j : ℕ} {e : List ℕ} (h : e ∈ grid (ds ++ [j])) :
    e ∈ grid (ds ++ [j + 1]) := by
  obtain ⟨a, j', rfl, ha, h1, h2⟩ := (mem_grid_snoc _ _ _).1 h
  exact (mem_grid_snoc _ _ _).2 ⟨a, j', rfl, ha, h1, by omega⟩

private lemma extL_copy {S : Finset (ℤ × ℤ)} {lab : ℕ → List ℕ → ℤ × ℤ} {ds : List ℕ} {j : ℕ}
    {φ ψ : List ℕ → ℤ × ℤ} (hφ : IsCopy S lab (ds ++ [j]) φ) (hψ : IsCopy S lab ds ψ)
    (hF : 1 ≤ j → ∀ a ∈ grid ds, dot (lab ds.length (a ++ [j])) (φ (a ++ [j])) =
      dot (lab ds.length (a ++ [j])) (ψ a)) :
    IsCopy S lab (ds ++ [j + 1]) (extL φ ψ j) := by
  obtain ⟨hS, hz, hc⟩ := hφ
  obtain ⟨hS', hz', hc'⟩ := hψ
  refine ⟨?_, ?_, ?_⟩
  · intro e he
    obtain ⟨a, j', rfl, ha, h1, h2⟩ := (mem_grid_snoc _ _ _).1 he
    rw [extL_snoc]
    split_ifs with hj
    · exact hS' a ha
    · exact hS _ ((mem_grid_snoc _ _ _).2 ⟨a, j', rfl, ha, h1, by omega⟩)
  · intro e he
    unfold extL
    split_ifs with hl
    · apply hz'
      intro ha
      apply he
      have : e = e.dropLast ++ [j + 1] := (List.dropLast_append_getLast? (j + 1) hl).symm
      have hm : e.dropLast ++ [j + 1] ∈ grid (ds ++ [j + 1]) :=
        (mem_grid_snoc _ _ _).2 ⟨_, j + 1, rfl, ha, by omega, le_rfl⟩
      rwa [← this] at hm
    · exact hz e (fun h' => he (grid_snoc_mono h'))
  · intro i hi a ha c hcm
    simp only [List.length_append, List.length_singleton] at hi
    rcases Nat.lt_or_ge i ds.length with hi' | hi'
    · rw [dD_snoc_lt _ _ _ hi'] at ha
      rw [drop_snoc_lt _ _ _ hi'] at hcm
      obtain ⟨c', j', rfl, hc'm, h1, h2⟩ := (mem_grid_snoc _ _ _).1 hcm
      rw [← List.append_assoc, ← List.append_assoc, extL_snoc, extL_snoc]
      split_ifs with hj
      · exact hc' i hi' a ha c' hc'm
      · have := hc i (by simp; omega) a (by rw [dD_snoc_lt _ _ _ hi']; exact ha) (c' ++ [j'])
          (by rw [drop_snoc_lt _ _ _ hi']; exact (mem_grid_snoc _ _ _).2 ⟨c', j', rfl, hc'm, h1, by omega⟩)
        simpa [List.append_assoc] using this
    · have hik : i = ds.length := by omega
      subst hik
      rw [dD_snoc_eq] at ha
      obtain ⟨a', j', rfl, ha', h1, h2⟩ := (mem_grid_snoc _ _ _).1 ha
      have hcn : c = [] := by
        simp [grid_nil] at hcm; exact hcm
      subst hcn
      simp only [List.append_nil, sL_snoc, extL_snoc]
      have hj'ne : j' ≠ j + 1 := by omega
      rw [if_neg hj'ne]
      split_ifs with hj
      · have hjj : j' = j := by omega
        subst hjj
        exact hF h1 a' ha'
      · have := hc ds.length (by simp) (a' ++ [j'])
          (by rw [dD_snoc_eq]; exact (mem_grid_snoc _ _ _).2 ⟨a', j', rfl, ha', h1, by omega⟩) []
          (by simp [grid_nil])
        simpa [sL_snoc] using this

private lemma extL_layer (φ ψ : List ℕ → ℤ × ℤ) (j : ℕ) :
    (fun a => extL φ ψ j (a ++ [j + 1])) = ψ := by
  funext a; simp [extL_snoc]

private lemma extL_inj {S : Finset (ℤ × ℤ)} {lab : ℕ → List ℕ → ℤ × ℤ} {ds : List ℕ} {j : ℕ}
    {φ₁ φ₂ ψ : List ℕ → ℤ × ℤ} (h₁ : IsCopy S lab (ds ++ [j]) φ₁)
    (h₂ : IsCopy S lab (ds ++ [j]) φ₂) (h : extL φ₁ ψ j = extL φ₂ ψ j) : φ₁ = φ₂ := by
  funext e
  by_cases hl : e.getLast? = some (j + 1)
  · have hne : e ∉ grid (ds ++ [j]) := by
      intro he
      obtain ⟨a, j', rfl, -, -, h2⟩ := (mem_grid_snoc _ _ _).1 he
      simp at hl; omega
    rw [h₁.2.1 e hne, h₂.2.1 e hne]
  · have := congrFun h e
    simpa [extL, hl] using this

/-! ## The counting lemma for constructible graphs -/

private noncomputable def mm (lab : ℕ → List ℕ → ℤ × ℤ) (dims : List ℕ) : ℕ :=
  ∑ i ∈ Finset.range dims.length,
    ((grid (dD dims i)).filter (fun a => decide (lab i a ≠ (0, 0)))).length *
      (dims.drop (i + 1)).prod

private lemma filter_flatMap_len (p : List ℕ → Bool) (l : List ℕ) :
    ∀ A : List (List ℕ),
      ((A.flatMap (fun a => l.map (fun j => a ++ [j]))).filter p).length =
        (l.map (fun j => (A.filter (fun a => p (a ++ [j]))).length)).sum
  | [] => by simp
  | a :: A => by
    rw [List.flatMap_cons, List.filter_append, List.length_append, filter_flatMap_len p l A]
    have h1 : ((l.map (fun j => a ++ [j])).filter p).length =
        (l.map (fun j => if p (a ++ [j]) then 1 else 0)).sum := by
      induction l with
      | nil => simp
      | cons j l ih =>
        simp only [List.map_cons, List.filter_cons, List.sum_cons]
        split_ifs with h <;> simp [ih]; omega
    rw [h1, ← List.sum_map_add]
    congr 1
    apply List.map_congr_left
    intro j _
    simp only [List.filter_cons]
    split_ifs with h <;> simp [Nat.add_comm]

private lemma list_sum_range'_eq (f : ℕ → ℕ) : ∀ d : ℕ, 1 ≤ d →
    ((List.range' 1 (d - 1)).map f).sum = ∑ j ∈ Finset.Ico 1 d, f j := by
  intro d hd
  induction d, hd using Nat.le_induction with
  | base => simp
  | succ d hd ih =>
    rw [Finset.sum_Ico_succ_top hd, ← ih]
    have : d + 1 - 1 = (d - 1) + 1 := by omega
    rw [this, List.range'_concat, List.map_append, List.sum_append]
    simp; congr 1; omega

private lemma grid_single (e : ℕ) : grid [e] = (List.range' 1 e).map (fun j => [j]) := by
  rw [grid_cons]
  simp [grid_nil, List.map_eq_flatMap]

private lemma mm_snoc (lab : ℕ → List ℕ → ℤ × ℤ) (ds : List ℕ) (d : ℕ) (hd : 1 ≤ d) :
    mm lab (ds ++ [d]) = d * mm lab ds + ∑ j ∈ Finset.Ico 1 d,
      ((grid ds).filter (fun a => decide (lab ds.length (a ++ [j]) ≠ (0, 0)))).length := by
  unfold mm
  rw [List.length_append, List.length_singleton, Finset.sum_range_succ, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [Finset.mem_range] at hi
    rw [dD_snoc_lt _ _ _ hi, drop_snoc_lt _ _ _ hi, List.prod_append]
    simp; ring
  · rw [dD_snoc_eq, grid_append, grid_single]
    have : (ds ++ [d]).drop (ds.length + 1) = [] := by simp
    rw [this, List.prod_nil, mul_one]
    have h := filter_flatMap_len (fun a => decide (lab ds.length a ≠ (0, 0))) (List.range' 1 (d - 1)) (grid ds)
    simp only [List.map_map, Function.comp_def] at h ⊢
    rw [show (fun a => (List.range' 1 (d - 1)).map (fun x => a ++ [x])) =
      (fun a => (List.range' 1 (d - 1)).map (fun j => a ++ [j])) from rfl]
    rw [h, list_sum_range'_eq _ d hd]

private lemma zero_copy (S : Finset (ℤ × ℤ)) (lab : ℕ → List ℕ → ℤ × ℤ) (ds : List ℕ) :
    IsCopy S lab (ds ++ [0]) 0 := by
  have hg : ∀ e, e ∉ grid (ds ++ [0]) := fun e he => by
    obtain ⟨_, _, _, _, h1, h2⟩ := (mem_grid_snoc _ _ _).1 he; omega
  exact ⟨fun e he => absurd he (hg e), fun _ _ => rfl, fun _ _ _ _ _ _ => rfl⟩

open Classical in
private lemma image_F_card (S : Finset (ℤ × ℤ)) (hS : S.Nonempty) (lab : ℕ → List ℕ → ℤ × ℤ)
    (N : ℕ) (hN1 : 1 ≤ N) (hN : ∀ i a, lab i a ≠ (0, 0) → (S.image (dot (lab i a))).card ≤ N)
    (ds : List ℕ) (j : ℕ) :
    ((Copies S lab ds).image (fun ψ a => dot (lab ds.length (a ++ [j])) (ψ a))).card ≤
      N ^ ((grid ds).filter (fun a => decide (lab ds.length (a ++ [j]) ≠ (0, 0)))).length := by
  classical
  set V := (grid ds).toFinset
  set P := Finset.pi V (fun a => S.image (dot (lab ds.length (a ++ [j]))))
  have hsub : (Copies S lab ds).image (fun ψ a => dot (lab ds.length (a ++ [j])) (ψ a)) ⊆
      P.image (fun g a => if h : a ∈ V then g a h else 0) := by
    intro x hx
    obtain ⟨ψ, hψ, rfl⟩ := Finset.mem_image.1 hx
    have hc := mem_Copies.1 hψ
    rw [Finset.mem_image]
    refine ⟨fun a _ => dot (lab ds.length (a ++ [j])) (ψ a), ?_, ?_⟩
    · rw [Finset.mem_pi]; intro a ha
      exact Finset.mem_image_of_mem _ (hc.1 a (List.mem_toFinset.1 ha))
    · funext a
      split_ifs with ha
      · rfl
      · rw [hc.2.1 a (fun h => ha (List.mem_toFinset.2 h))]; simp [dot]
  refine (Finset.card_le_card hsub).trans (Finset.card_image_le.trans ?_)
  rw [Finset.card_pi]
  calc ∏ a ∈ V, (S.image (dot (lab ds.length (a ++ [j])))).card
      ≤ ∏ a ∈ V, (if lab ds.length (a ++ [j]) ≠ (0, 0) then N else 1) := by
        apply Finset.prod_le_prod' 
        intro a _
        split_ifs with h
        · exact hN _ _ h
        · rw [ne_eq, not_not] at h
          rw [h]
          apply Finset.card_le_one.2
          intro x hx y hy
          obtain ⟨_, _, rfl⟩ := Finset.mem_image.1 hx
          obtain ⟨_, _, rfl⟩ := Finset.mem_image.1 hy
          simp [dot]
    _ = N ^ (V.filter (fun a => lab ds.length (a ++ [j]) ≠ (0, 0))).card := by
        rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]
    _ = _ := by
        congr 1
        rw [← List.toFinset_card_of_nodup ((grid_nodup ds).filter _)]
        congr 1
        ext a; simp [V]

private lemma count_main (S : Finset (ℤ × ℤ)) (hS : S.Nonempty) (lab : ℕ → List ℕ → ℤ × ℤ)
    (N : ℕ) (hN1 : 1 ≤ N) (hN : ∀ i a, lab i a ≠ (0, 0) → (S.image (dot (lab i a))).card ≤ N)
    (dims : List ℕ) :
    S.card ^ dims.prod ≤ (Copies S lab dims).card * N ^ mm lab dims := by
  classical
  induction dims using List.reverseRecOn with
  | nil =>
    simp only [List.prod_nil, pow_one, mm, List.length_nil, Finset.range_zero, Finset.sum_empty,
      pow_zero, mul_one]
    apply Finset.card_le_card_of_injOn (fun s e => if e = [] then s else 0)
    · intro s hs
      rw [Finset.mem_coe, mem_Copies]
      refine ⟨?_, ?_, ?_⟩
      · intro e he; simp [grid_nil] at he; subst he; simpa using hs
      · intro e he
        have : e ≠ [] := fun h => he (by simp [h, grid_nil])
        simp [this]
      · intro i hi; simp at hi
    · intro s _ t _ h
      have := congrFun h []
      simpa using this
  | append_singleton ds d ih =>
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · have h0 : (0 : List ℕ → ℤ × ℤ) ∈ Copies S lab (ds ++ [0]) := mem_Copies.2 (zero_copy S lab ds)
      simp only [List.prod_append, List.prod_cons, List.prod_nil, mul_zero, mul_one, pow_zero]
      have : 1 ≤ (Copies S lab (ds ++ [0])).card := Finset.card_pos.2 ⟨_, h0⟩
      have : 1 ≤ N ^ mm lab (ds ++ [0]) := Nat.one_le_pow _ _ hN1
      nlinarith
    · set k := ds.length with hk
      set C := Copies S lab ds with hCdef
      set F : ℕ → (List ℕ → ℤ × ℤ) → (List ℕ → ℤ) :=
        fun j ψ a => dot (lab k (a ++ [j])) (ψ a) with hFdef
      set cnt : ℕ → (List ℕ → ℤ × ℤ) → ℕ := fun j ψ =>
        ((Copies S lab (ds ++ [j])).filter (fun φ => (fun a => φ (a ++ [j])) = ψ)).card with hcnt
      set s : ℕ → ℕ := fun j =>
        ((grid ds).filter (fun a => decide (lab k (a ++ [j]) ≠ (0, 0)))).length with hsdef
      have hSpos : 0 < S.card := hS.card_pos
      have hC : C.Nonempty := by
        apply Finset.card_pos.1
        have : 0 < S.card ^ ds.prod := pow_pos hSpos _
        rcases Nat.eq_zero_or_pos C.card with h | h
        · rw [h, zero_mul] at ih; omega
        · exact h
      have h1 : ∀ ψ ∈ C, 1 ≤ cnt 1 ψ := by
        intro ψ hψ
        apply Finset.card_pos.2
        refine ⟨extL 0 ψ 0, ?_⟩
        rw [Finset.mem_filter, mem_Copies]
        exact ⟨extL_copy (zero_copy S lab ds) (mem_Copies.1 hψ) (fun h => absurd h (by omega)),
          extL_layer _ _ _⟩
      have hrec : ∀ j, 1 ≤ j → ∀ ψ' ∈ C,
          ∑ ψ ∈ C.filter (fun ψ => F j ψ = F j ψ'), cnt j ψ ≤ cnt (j + 1) ψ' := by
        intro j hj ψ' hψ'
        set A := (Copies S lab (ds ++ [j])).filter
          (fun φ => F j (fun a => φ (a ++ [j])) = F j ψ') with hA
        have e1 : ∑ ψ ∈ C.filter (fun ψ => F j ψ = F j ψ'), cnt j ψ = A.card := by
          rw [Finset.card_eq_sum_card_fiberwise (f := fun φ => fun a => φ (a ++ [j]))
            (t := C.filter (fun ψ => F j ψ = F j ψ'))]
          · refine Finset.sum_congr rfl (fun ψ hψ => ?_)
            simp only [hcnt]
            congr 1
            ext φ
            simp only [hA, Finset.mem_filter]
            constructor
            · rintro ⟨hφ, rfl⟩; exact ⟨⟨hφ, (Finset.mem_filter.1 hψ).2⟩, rfl⟩
            · rintro ⟨⟨hφ, _⟩, h⟩; exact ⟨hφ, h⟩
          · intro φ hφ
            simp only [hA, Finset.mem_filter, Finset.mem_coe] at hφ ⊢
            exact ⟨mem_Copies.2 (layer_copy (mem_Copies.1 hφ.1) j hj le_rfl), hφ.2⟩
        rw [e1]
        apply Finset.card_le_card_of_injOn (fun φ => extL φ ψ' j)
        · intro φ hφ
          simp only [hA, Finset.mem_filter, Finset.mem_coe] at hφ ⊢
          refine ⟨mem_Copies.2 (extL_copy (mem_Copies.1 hφ.1) (mem_Copies.1 hψ')
            (fun _ a _ => congrFun hφ.2 a)), extL_layer _ _ _⟩
        · intro φ₁ h₁ φ₂ h₂ h
          simp only [hA, Finset.mem_filter, Finset.mem_coe] at h₁ h₂
          exact extL_inj (mem_Copies.1 h₁.1) (mem_Copies.1 h₂.1) h
      have hB : ∀ j, (C.image (F j)).card ≤ N ^ s j :=
        fun j => image_F_card S hS lab N hN1 hN ds j
      have hmain := chain_bound C hC F cnt (fun j => N ^ s j) h1 hrec hB d hd
      have hsum : ∑ ψ ∈ C, cnt d ψ = (Copies S lab (ds ++ [d])).card := by
        rw [Finset.card_eq_sum_card_fiberwise (f := fun φ => fun a => φ (a ++ [d])) (t := C)]
        intro φ hφ
        rw [Finset.mem_coe] at hφ
        exact mem_Copies.2 (layer_copy (mem_Copies.1 hφ) d hd le_rfl)
      have hmainN : C.card ^ d ≤ (Copies S lab (ds ++ [d])).card *
          N ^ ∑ j ∈ Finset.Ico 1 d, s j := by
        rw [← Finset.prod_pow_eq_pow_sum, ← hsum]
        exact_mod_cast hmain
      rw [mm_snoc lab ds d hd, List.prod_append, List.prod_singleton, pow_mul]
      calc (S.card ^ ds.prod) ^ d ≤ (C.card * N ^ mm lab ds) ^ d := Nat.pow_le_pow_left ih d
        _ = C.card ^ d * N ^ (d * mm lab ds) := by rw [mul_pow, ← pow_mul, mul_comm (mm lab ds)]
        _ ≤ (Copies S lab (ds ++ [d])).card * N ^ (∑ j ∈ Finset.Ico 1 d, s j) *
              N ^ (d * mm lab ds) := Nat.mul_le_mul_right _ hmainN
        _ = _ := by rw [pow_add]; simp only [hsdef, hk]; ring

/-! ## Soundness of forcing -/

private noncomputable def eval (V : List (List ℕ)) (f : List ℕ → ℤ × ℤ) (φ : List ℕ → ℤ × ℤ) : ℤ :=
  ∑ e ∈ V.toFinset, dot (f e) (φ e)

private def labG {X : Finset (ℤ × ℤ)} (G : ConstructibleGraph X) : ℕ → List ℕ → ℤ × ℤ :=
  fun i a => if h : i < G.dims.length then G.f ⟨i, h⟩ a else (0, 0)

private lemma dD_eq_domainDims (dims : List ℕ) (i : Fin dims.length) :
    domainDims dims i = dD dims i.val := by
  simp [domainDims, dD]

private lemma dot_neg (x g : ℤ × ℤ) : dot (-x) g = - dot x g := by
  simp [dot]; ring

private lemma dot_zero_left (g : ℤ × ℤ) : dot (0, 0) g = 0 := by simp [dot]

private lemma dot_sub_left (x y g : ℤ × ℤ) : dot (x - y) g = dot x g - dot y g := by
  simp [dot]; ring

private lemma eval_edge {X : Finset (ℤ × ℤ)} (G : ConstructibleGraph X) (S : Finset (ℤ × ℤ))
    {φ : List ℕ → ℤ × ℤ} (hφ : IsCopy S (labG G) G.dims φ) (i : Fin G.dims.length) (a c : List ℕ)
    (ha : a ∈ grid (domainDims G.dims i)) (hc : c ∈ grid (G.dims.drop (i.val + 1))) :
    eval (grid G.dims) (edgeFn G i a c) φ = 0 := by
  classical
  rw [dD_eq_domainDims] at ha
  obtain ⟨h1, h2, hne⟩ := edge_mem G.dims i.val i.isLt a c ha hc
  have he2 : a.dropLast ++ [a.getLastD 0 + 1] ++ c = sL a ++ c := by simp [sL]
  have hlab : labG G i.val a = G.f i a := by simp [labG]
  have hcop := hφ.2.2 i.val i.isLt a ha c hc
  rw [hlab] at hcop
  unfold eval
  rw [Finset.sum_eq_add (a ++ c) (sL a ++ c) hne]
  · simp only [edgeFn, he2, if_pos rfl, if_neg hne.symm, if_true]
    rw [dot_neg, hcop]; ring
  · intro g _ hg
    simp only [edgeFn, he2, if_neg hg.1, if_neg hg.2, dot_zero_left]
  · intro h; exact absurd (List.mem_toFinset.2 h1) h
  · intro h; exact absurd (List.mem_toFinset.2 h2) h

private lemma forces_inj {X : Finset (ℤ × ℤ)} (G : ConstructibleGraph X) (S : Finset (ℤ × ℤ))
    (hinj : Set.InjOn (fun g : ℤ × ℤ => g.1 - g.2) S) {R : List (List ℕ → ℤ × ℤ)}
    {T : List (List ℕ)} (hF : Forces G R T) :
    ∀ φ ψ, IsCopy S (labG G) G.dims φ → IsCopy S (labG G) G.dims ψ →
      (∀ f ∈ R, eval (grid G.dims) f φ = eval (grid G.dims) f ψ) →
      (∀ e ∈ T, φ e = ψ e) → φ = ψ := by
  classical
  induction hF with
  | done hT =>
    intro φ ψ hφ hψ _ hTe
    funext e
    by_cases he : e ∈ grid G.dims
    · exact hTe e (hT e he)
    · rw [hφ.2.1 e he, hψ.2.1 e he]
  | edge i a c ha hc _ ih =>
    intro φ ψ hφ hψ hR hTe
    refine ih φ ψ hφ hψ ?_ hTe
    intro f hf
    rcases List.mem_cons.1 hf with rfl | hf
    · rw [eval_edge G S hφ i a c ha hc, eval_edge G S hψ i a c ha hc]
    · exact hR f hf
  | @vertex R' T' f hf e he a ha hfe hsupp _ ih =>
    intro φ ψ hφ hψ hR hTe
    refine ih φ ψ hφ hψ hR ?_
    intro e' he'
    rcases List.mem_cons.1 he' with rfl | he'
    · have h := hR f hf
      unfold eval at h
      have h2 : ∑ g ∈ (grid G.dims).toFinset, (dot (f g) (φ g) - dot (f g) (ψ g)) = 0 := by
        rw [Finset.sum_sub_distrib, h, sub_self]
      rw [Finset.sum_eq_single e'] at h2
      · rw [hfe] at h2
        simp only [dot] at h2
        have hd : (φ e').1 - (φ e').2 = (ψ e').1 - (ψ e').2 := by
          have : a * ((φ e').1 - (φ e').2) = a * ((ψ e').1 - (ψ e').2) := by linarith
          exact mul_left_cancel₀ ha this
        exact hinj (hφ.1 e' he) (hψ.1 e' he) hd
      · intro g hg hge
        have hg' := List.mem_toFinset.1 hg
        by_cases hgT : g ∈ T'
        · rw [hTe g hgT, sub_self]
        · rw [hsupp g hg' hgT hge, dot_zero_left, dot_zero_left, sub_self]
      · intro h; exact absurd (List.mem_toFinset.2 he) h
    · exact hTe e' he'
  | diff f g hf hg _ ih =>
    intro φ ψ hφ hψ hR hTe
    refine ih φ ψ hφ hψ ?_ hTe
    intro h hh
    rcases List.mem_cons.1 hh with rfl | hh
    · unfold eval
      simp only [Pi.sub_apply, dot_sub_left, Finset.sum_sub_distrib]
      have h1 := hR f hf
      have h2 := hR g hg
      unfold eval at h1 h2
      rw [h1, h2]
    · exact hR h hh

private lemma copies_le {X : Finset (ℤ × ℤ)} (G : ConstructibleGraph X)
    (R : List (List ℕ → ℤ × ℤ)) (T : List (List ℕ)) (hXT : IsXSet G R T) (hF : Forces G R T)
    (S : Finset (ℤ × ℤ)) (hinj : Set.InjOn (fun g : ℤ × ℤ => g.1 - g.2) S) (N : ℕ)
    (hN : ∀ x ∈ X, (S.image (dot x)).card ≤ N) :
    (Copies S (labG G) G.dims).card ≤ N ^ R.length * S.card ^ T.length := by
  classical
  set C := Copies S (labG G) G.dims
  set V := grid G.dims
  let κ : (List ℕ → ℤ × ℤ) → (Fin R.length → ℤ) × (Fin T.length → ℤ × ℤ) :=
    fun φ => (fun j => eval V R[j] φ, fun j => φ T[j])
  have hT1 : ∀ j : Fin R.length, (C.image (fun φ => eval V R[j] φ)).card ≤ N := by
    intro j
    obtain ⟨x, g, hx, _, hg, hf⟩ := hXT.2.2.1 R[j] (List.getElem_mem _)
    have : C.image (fun φ => eval V R[j] φ) ⊆ S.image (dot x) := by
      intro z hz
      obtain ⟨φ, hφ, rfl⟩ := Finset.mem_image.1 hz
      have hc := mem_Copies.1 hφ
      have : eval V R[j] φ = dot x (φ g) := by
        unfold eval
        rw [Finset.sum_eq_single g]
        · rw [hf]; simp
        · intro b _ hb; rw [hf]; simp [hb, dot_zero_left]
        · intro h; exact absurd (List.mem_toFinset.2 hg) h
      rw [this]
      exact Finset.mem_image_of_mem _ (hc.1 g hg)
    exact (Finset.card_le_card this).trans (hN x hx)
  calc C.card ≤ ((Fintype.piFinset fun j : Fin R.length => C.image (fun φ => eval V R[j] φ)) ×ˢ
        (Fintype.piFinset fun _ : Fin T.length => S)).card := by
        apply Finset.card_le_card_of_injOn κ
        · intro φ hφ
          rw [Finset.mem_coe] at hφ
          rw [Finset.mem_coe, Finset.mem_product, Fintype.mem_piFinset, Fintype.mem_piFinset]
          refine ⟨fun j => Finset.mem_image_of_mem _ hφ, fun j => ?_⟩
          exact (mem_Copies.1 hφ).1 _ (hXT.2.2.2 _ (List.getElem_mem _))
        · intro φ hφ ψ hψ h
          rw [Finset.mem_coe] at hφ hψ
          have h1 := congrArg Prod.fst h
          have h2 := congrArg Prod.snd h
          apply forces_inj G S hinj hF φ ψ (mem_Copies.1 hφ) (mem_Copies.1 hψ)
          · intro f hf
            obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hf
            exact congrFun h1 ⟨j, hj⟩
          · intro e he
            obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem he
            exact congrFun h2 ⟨j, hj⟩
    _ ≤ N ^ R.length * S.card ^ T.length := by
        rw [Finset.card_product, Fintype.card_piFinset, Fintype.card_piFinset]
        simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        apply Nat.mul_le_mul_right
        calc ∏ j : Fin R.length, (C.image (fun φ => eval V R[j] φ)).card
            ≤ ∏ _j : Fin R.length, N := Finset.prod_le_prod' (fun j _ => hT1 j)
          _ = N ^ R.length := by simp

private lemma mm_labG {X : Finset (ℤ × ℤ)} (G : ConstructibleGraph X) :
    mm (labG G) G.dims = m G := by
  unfold mm m
  rw [Finset.sum_range (fun i => ((grid (dD G.dims i)).filter
    (fun a => decide (labG G i a ≠ (0, 0)))).length * (G.dims.drop (i + 1)).prod)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [dD_eq_domainDims]
  congr 3
  funext a
  simp [labG]

private lemma sound {X : Finset (ℤ × ℤ)} (G : ConstructibleGraph X)
    (R : List (List ℕ → ℤ × ℤ)) (T : List (List ℕ)) (hXT : IsXSet G R T) (hF : Forces G R T)
    (S : Finset (ℤ × ℤ)) (hS : S.Nonempty) (hinj : Set.InjOn (fun g : ℤ × ℤ => g.1 - g.2) S)
    (N : ℕ) (hN1 : 1 ≤ N) (hN : ∀ x ∈ X, (S.image (dot x)).card ≤ N) :
    S.card ^ n G ≤ N ^ (m G + R.length) * S.card ^ T.length := by
  have hlab : ∀ i a, labG G i a ≠ (0, 0) → (S.image (dot (labG G i a))).card ≤ N := by
    intro i a h
    unfold labG at h ⊢
    split_ifs at h ⊢ with hi
    · exact hN _ (G.f_support _ _ h).2
    · exact absurd rfl h
  have h1 := count_main S hS (labG G) N hN1 hlab G.dims
  have h2 := copies_le G R T hXT hF S hinj N hN
  rw [mm_labG] at h1
  calc S.card ^ n G = S.card ^ G.dims.prod := rfl
    _ ≤ (Copies S (labG G) G.dims).card * N ^ m G := h1
    _ ≤ N ^ R.length * S.card ^ T.length * N ^ m G := Nat.mul_le_mul_right _ h2
    _ = _ := by ring

/-! ## From the counting inequality to `AK` -/

/-- A section of the difference map: a subset of `G0` with injective differences and the same
number of differences. -/
private lemma exists_section (G0 : Finset (ℤ × ℤ)) :
    ∃ S ⊆ G0, Set.InjOn (fun g : ℤ × ℤ => g.1 - g.2) S ∧
      S.card = (G0.image (fun g => g.1 - g.2)).card := by
  classical
  set D := G0.image (fun g : ℤ × ℤ => g.1 - g.2)
  have hch : ∀ v ∈ D, ∃ g ∈ G0, g.1 - g.2 = v := fun v hv => by
    simpa [D] using hv
  let σ : ℤ → ℤ × ℤ := fun v => if h : ∃ g ∈ G0, g.1 - g.2 = v then h.choose else 0
  have hσ : ∀ v ∈ D, σ v ∈ G0 ∧ (σ v).1 - (σ v).2 = v := by
    intro v hv
    have h := hch v hv
    simp only [σ, dif_pos h]
    exact h.choose_spec
  refine ⟨D.image σ, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hg
    exact (hσ v hv).1
  · intro g hg g' hg' h
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hg)
    obtain ⟨v', hv', rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hg')
    simp only at h
    rw [(hσ v hv).2, (hσ v' hv').2] at h
    rw [h]
  · apply Finset.card_image_of_injOn
    intro v hv v' hv' h
    have := congrArg (fun g : ℤ × ℤ => g.1 - g.2) h
    rwa [(hσ v hv).2, (hσ v' hv').2] at this



theorem solution
    (G : ConstructibleGraph ({(1, 0), (0, 1), (1, 1)} : Finset (ℤ × ℤ)))
    (R : List (List ℕ → ℤ × ℤ)) (T : List (List ℕ))
    (hXT : IsXSet G R T) (hF : Forces G R T) (ht : T.length < n G) :
    88949 * (n G - T.length) < 50000 * (m G + R.length) := by
  classical
  obtain ⟨G0, hG0⟩ := LefebvreVariations.sums_differences_lemm_witness
  have hG0ne : G0.Nonempty := by
    rcases G0.eq_empty_or_nonempty with rfl | h
    · simp at hG0
    · exact h
  set N := max (max (G0.image Prod.fst).card (G0.image Prod.snd).card)
    (G0.image (fun g => g.1 + g.2)).card with hNdef
  set Dc := (G0.image (fun g : ℤ × ℤ => g.1 - g.2)).card with hDc
  obtain ⟨S, hSG, hinj, hcard⟩ := exists_section G0
  have hSne : S.Nonempty := by
    apply Finset.card_pos.1; rw [hcard]; exact Finset.card_pos.2 (hG0ne.image _)
  have hN1 : 1 ≤ N :=
    le_max_of_le_right (Finset.card_pos.2 (hG0ne.image _))
  have hN : ∀ x ∈ ({(1, 0), (0, 1), (1, 1)} : Finset (ℤ × ℤ)), (S.image (dot x)).card ≤ N := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · calc (S.image (dot (1, 0))).card ≤ (G0.image (dot (1, 0))).card :=
            Finset.card_le_card (Finset.image_subset_image hSG)
        _ = (G0.image Prod.fst).card := by
            congr 1; apply Finset.image_congr; intro g _; simp [dot]
        _ ≤ N := le_max_of_le_left (le_max_left _ _)
    · calc (S.image (dot (0, 1))).card ≤ (G0.image (dot (0, 1))).card :=
            Finset.card_le_card (Finset.image_subset_image hSG)
        _ = (G0.image Prod.snd).card := by
            congr 1; apply Finset.image_congr; intro g _; simp [dot]
        _ ≤ N := le_max_of_le_left (le_max_right _ _)
    · calc (S.image (dot (1, 1))).card ≤ (G0.image (dot (1, 1))).card :=
            Finset.card_le_card (Finset.image_subset_image hSG)
        _ = (G0.image (fun g => g.1 + g.2)).card := by
            congr 1; apply Finset.image_congr; intro g _; simp [dot]
        _ ≤ N := le_max_right _ _
  have h := sound G R T hXT hF S hSne hinj N hN1 hN
  rw [hcard] at h
  set q := n G - T.length with hq
  have hqpos : 0 < q := by omega
  have hD1 : 1 ≤ Dc := Finset.card_pos.2 (hG0ne.image _)
  have hDq : Dc ^ q ≤ N ^ (m G + R.length) := by
    have e : n G = q + T.length := by omega
    rw [e, pow_add] at h
    exact Nat.le_of_mul_le_mul_right h (pow_pos hD1 _)
  by_contra hcon
  push Not at hcon
  have h1 : (Dc ^ 50000) ^ q ≤ (N ^ 88949) ^ q := by
    calc (Dc ^ 50000) ^ q = (Dc ^ q) ^ 50000 := by rw [← pow_mul, ← pow_mul, mul_comm]
      _ ≤ (N ^ (m G + R.length)) ^ 50000 := Nat.pow_le_pow_left hDq _
      _ = N ^ (50000 * (m G + R.length)) := by rw [← pow_mul, mul_comm]
      _ ≤ N ^ (88949 * q) := Nat.pow_le_pow_right hN1 hcon
      _ = (N ^ 88949) ^ q := by rw [pow_mul]
  have h2 := (Nat.pow_le_pow_iff_left hqpos.ne').1 h1
  exact absurd hG0 (not_lt.2 h2)
