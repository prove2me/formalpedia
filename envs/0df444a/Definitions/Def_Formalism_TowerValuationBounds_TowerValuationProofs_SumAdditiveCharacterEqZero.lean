-- Prove2me | Definitions.Def_Formalism_TowerValuationBounds_TowerValuationProofs_SumAdditiveCharacterEqZero
-- name    : Formalism_TowerValuationBounds_TowerValuationProofs_SumAdditiveCharacterEqZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T08:21:16.834801+00:00
-- url     : https://prove2.me/theorems/5915c148-e7f4-4ad0-9bb4-433dcced5b4d
-- title:
--   Sum Additive Character Eq Zero
-- statement:
--   Definitions and structural lemmas for Sum Additive Character Eq Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TowerValuationBounds/TowerValuationProofs/SumAdditiveCharacterEqZero.lean

import Definitions.Def_Formalism_TowerValuationBounds_HermitianSumValuationBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.ValuationGridEstimates
open Finset
section aux
variable {G : Type} [CommGroup G] {v : G → ℝ}
lemma additive_map_one (hv : ∀ x y, v (x * y) = v x + v y) : v 1 = 0 := by
  have := hv 1 1
  rw [mul_one] at this
  linarith
lemma additive_map_inv (hv : ∀ x y, v (x * y) = v x + v y) (x : G) : v x⁻¹ = -v x := by
  have := hv x x⁻¹
  rw [mul_inv_cancel, additive_map_one hv] at this
  linarith
lemma additive_map_div (hv : ∀ x y, v (x * y) = v x + v y) (x y : G) : v (x / y) = v x - v y := by
  rw [div_eq_mul_inv, hv, additive_map_inv hv]; ring
lemma additive_map_prod (hv : ∀ x y, v (x * y) = v x + v y) {ι : Type} (s : Finset ι) (f : ι → G) :
    v (∏ i ∈ s, f i) = ∑ i ∈ s, v (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using additive_map_one hv
  | insert a s ha ih => rw [prod_insert ha, sum_insert ha, hv, ih]
end aux
theorem height_bound_alt : AbsValuationSumBound := by
  intro W E _ lam val δ absx Wx Bδ hlam hsupp hpf
  classical
  have habs : ∀ x : ℝ, |x| = x + 2 * max 0 (-x) := by
    intro x
    rcases le_total 0 x with h | h
    · rw [abs_of_nonneg h, max_eq_left (by linarith)]; ring
    · rw [abs_of_nonpos h, max_eq_right (by linarith)]; ring
  have h1 : ∑ w ∈ Wx, lam w * |val w| =
      (∑ σ, Real.log (absx σ)) / Fintype.card E + 2 * ∑ w ∈ Wx, lam w * max 0 (-val w) := by
    rw [← hpf, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply sum_congr rfl
    intro w _
    rw [habs]; ring
  have hmean : (∑ σ, Real.log (absx σ)) / Fintype.card E ≤
      (∑ σ, Real.posLog (absx σ)) / Fintype.card E := by
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    apply sum_le_sum
    intro σ _
    rw [Real.posLog_def]
    exact le_max_right _ _
  refine ⟨h1, by rw [h1]; linarith, ?_⟩
  intro hδ hden hB F
  have h2 : ∑ w ∈ F, lam w * |val w| ≤ ∑ w ∈ Wx, lam w * |val w| := by
    calc ∑ w ∈ F, lam w * |val w| ≤ ∑ w ∈ F ∪ Wx, lam w * |val w| :=
          sum_le_sum_of_subset_of_nonneg subset_union_left
            (fun w _ _ => mul_nonneg (hlam w) (abs_nonneg _))
      _ = ∑ w ∈ Wx, lam w * |val w| := by
          symm
          apply sum_subset subset_union_right
          intro w _ hw
          rw [hsupp w hw]; simp
  have h3 : ∑ w ∈ Wx, lam w * max 0 (-val w) ≤ 3 * Bδ := by
    calc ∑ w ∈ Wx, lam w * max 0 (-val w) ≤ ∑ w ∈ Wx, 3 * (lam w * δ w) := by
          apply sum_le_sum
          intro w _
          have : max 0 (-val w) ≤ 3 * δ w := max_le (by linarith [hδ w]) (by linarith [hden w])
          nlinarith [hlam w]
      _ = 3 * ∑ w ∈ Wx, lam w * δ w := by rw [Finset.mul_sum]
      _ ≤ 3 * Bδ := by linarith [hB Wx]
  linarith
theorem tower_bound : TowerProductFormula := by
  intro K _ L c u p q e hL hbe hal
  have be : ∀ n, n ≤ q → c 0 0 * ∏ k ∈ Icc 1 n, L (e + k) = (∏ j ∈ range n, u 0 j) * c 0 n := by
    intro n
    induction n with
    | zero => intro _; simp
    | succ n ih =>
      intro hn
      rw [Finset.prod_Icc_succ_top (by omega), prod_range_succ, ← mul_assoc, ih (by omega)]
      have := hbe n (by omega)
      have e1 : L (e + ((n + 1 : ℕ) : ℤ)) = L (e + n + 1) := by congr 1; push_cast; ring
      rw [e1, mul_assoc, this]; ring
  have al : ∀ n, n ≤ p → c 0 q =
      (∏ i ∈ range n, u i q) * (∏ k ∈ Icc 1 n, L (e + q - k + 1)) * c n q := by
    intro n
    induction n with
    | zero => intro _; simp
    | succ n ih =>
      intro hn
      rw [Finset.prod_Icc_succ_top (by omega), prod_range_succ, ih (by omega), hal n (by omega)]
      have e1 : L (e + q - ((n + 1 : ℕ) : ℤ) + 1) = L (e - n + q) := by congr 1; push_cast; ring
      rw [e1]; ring
  have hne : ∏ k ∈ Icc 1 q, L (e + k) ≠ 0 := by
    apply prod_ne_zero_iff.mpr
    intro k hk
    rw [mem_Icc] at hk
    exact hL k hk.1 hk.2
  rw [eq_div_iff hne, be q le_rfl, al p le_rfl]
  ring
theorem lemma_c_gauss_sum : HermitianSumValuationBound := by
  intro K _ v vc conj hconj ι κ _ X z z' gm c0 δ hc0 hz hint hg
  have gen : ∀ (y : ι → κ → K) (t : WithTop ℝ),
      (∀ x ∈ X, ∀ k, t ≤ v (y x k)) → (∀ x ∈ X, ∀ k, ((-δ : ℝ) : WithTop ℝ) ≤ vc (y x k)) →
      t + ((-δ : ℝ) : WithTop ℝ) + ((-δ : ℝ) : WithTop ℝ) ≤
        v (∑ x ∈ X, ∑ k, ∑ l, y x k * conj (y x l) * gm x k l) := by
    intro y t h1 h2
    apply AddValuation.map_le_sum
    intro x hx
    apply AddValuation.map_le_sum
    intro k _
    apply AddValuation.map_le_sum
    intro l _
    rw [AddValuation.map_mul, AddValuation.map_mul, hconj]
    exact add_le_add (add_le_add (h1 x hx k) (h2 x hx l)) (hg x hx k l)
  have hinv : v c0 + v c0⁻¹ = 0 := by
    rw [← AddValuation.map_mul, mul_inv_cancel₀ hc0, AddValuation.map_one]
  obtain ⟨r, hr⟩ : ∃ r : ℝ, v c0 = (r : WithTop ℝ) := by
    have : v c0 ≠ ⊤ := by
      intro h; exact hc0 ((AddValuation.top_iff v).mp h)
    exact ⟨(v c0).untop this, (WithTop.coe_untop _ this).symm⟩
  have hr' : v c0⁻¹ = ((-r : ℝ) : WithTop ℝ) := by
    have : v c0⁻¹ ≠ ⊤ := by
      intro h; exact (inv_ne_zero hc0) ((AddValuation.top_iff v).mp h)
    obtain ⟨r', hr'⟩ : ∃ r' : ℝ, v c0⁻¹ = (r' : WithTop ℝ) := ⟨_, (WithTop.coe_untop _ this).symm⟩
    rw [hr, hr', ← WithTop.coe_add, ← WithTop.coe_zero, WithTop.coe_eq_coe] at hinv
    rw [hr']; congr 1; linarith
  have shift : ∀ (s : ℝ) (T : WithTop ℝ),
      ((s - δ : ℝ) : WithTop ℝ) + ((-δ : ℝ) : WithTop ℝ) + ((-δ : ℝ) : WithTop ℝ) ≤ T →
      (s : WithTop ℝ) ≤ T + ((3 * δ : ℝ) : WithTop ℝ) := by
    intro s T h
    induction T using WithTop.recTopCoe with
    | top => simp
    | coe T =>
      rw [← WithTop.coe_add, ← WithTop.coe_add, WithTop.coe_le_coe] at h
      rw [← WithTop.coe_add, WithTop.coe_le_coe]; linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hr]
    apply shift
    apply gen z _ _ (fun x hx k => (hint x hx k).2.1)
    intro x hx k
    rw [hz x hx k, AddValuation.map_mul, hr, sub_eq_add_neg, WithTop.coe_add]
    exact add_le_add le_rfl (hint x hx k).2.2.1
  · rw [hr']
    apply shift
    apply gen z' _ _ (fun x hx k => (hint x hx k).2.2.2)
    intro x hx k
    have : z' x k = c0⁻¹ * z x k := by rw [hz x hx k, inv_mul_cancel_left₀ hc0]
    rw [this, AddValuation.map_mul, hr', sub_eq_add_neg, WithTop.coe_add]
    exact add_le_add le_rfl (hint x hx k).1
  · have := gen z _ (fun x hx k => (hint x hx k).1) (fun x hx k => (hint x hx k).2.1)
    refine le_trans (le_of_eq ?_) this
    rw [← WithTop.coe_add, ← WithTop.coe_add]; congr 1; ring
  · have := gen z' _ (fun x hx k => (hint x hx k).2.2.1) (fun x hx k => (hint x hx k).2.2.2)
    refine le_trans (le_of_eq ?_) this
    rw [← WithTop.coe_add, ← WithTop.coe_add]; congr 1; ring
section gauss
variable {R : Type} [CommRing R] [Fintype R] [DecidableEq R] (I : Ideal R) (ψ : AddChar R ℂ)
def d9u (hI : ∀ y ∈ I, ∀ y' ∈ I, y * y' = 0) (y : I) : Rˣ :=
  ⟨1 + y, 1 - y, by have := hI y y.2 y y.2; linear_combination -this,
    by have := hI y y.2 y y.2; linear_combination -this⟩
omit [Fintype R] [DecidableEq R] in
lemma sum_additive_character_eq_zero [Fintype I] (z : R) (hz : ∃ y ∈ I, ψ (z * y) ≠ 1) : ∑ y : I, ψ (z * (y : R)) = 0 := by
  obtain ⟨y0, hy0, hne⟩ := hz
  have h1 : ∑ y : I, ψ (z * (y : R)) = ∑ y : I, ψ (z * ((y + ⟨y0, hy0⟩ : I) : R)) :=
    (Equiv.sum_comp (Equiv.addRight (⟨y0, hy0⟩ : I)) (fun y : I => ψ (z * (y : R)))).symm
  have h2 : ∑ y : I, ψ (z * ((y + ⟨y0, hy0⟩ : I) : R)) = (∑ y : I, ψ (z * (y : R))) * ψ (z * y0) := by
    rw [sum_mul]
    apply sum_congr rfl
    intro y _
    rw [← AddChar.map_add_eq_mul]
    congr 1
    push_cast; ring
  rw [h2] at h1
  have h3 : (∑ y : I, ψ (z * (y : R))) * (1 - ψ (z * y0)) = 0 := by linear_combination h1
  rcases mul_eq_zero.mp h3 with h | h
  · exact h
  · exact absurd (by linear_combination -h) hne
omit [Fintype R] [DecidableEq R] in
lemma gauss_sum_translate_unit (hI : ∀ y ∈ I, ∀ y' ∈ I, y * y' = 0) (χ : Rˣ →* ℂˣ) (c : R)
    (hχ : ∀ u : Rˣ, (u : R) - 1 ∈ I → ((χ u : ℂˣ) : ℂ) = ψ (c * ((u : R) - 1))) (x : Rˣ) (y : I) :
    (((χ (x * d9u I hI y))⁻¹ : ℂˣ) : ℂ) * ψ ((x * d9u I hI y : Rˣ) : R) =
      (((χ x)⁻¹ : ℂˣ) : ℂ) * ψ (x : R) * ψ (((x : R) - c) * (y : R)) := by
  have hu : ((d9u I hI y : Rˣ) : R) = 1 + y := rfl
  have h1 : ((χ (d9u I hI y) : ℂˣ) : ℂ) = ψ (c * (y : R)) := by
    rw [hχ _ (by rw [hu]; simp)]
    rw [hu]; congr 1; ring
  have h2 : ψ ((x * d9u I hI y : Rˣ) : R) = ψ (x : R) * ψ ((x : R) * y) := by
    rw [← AddChar.map_add_eq_mul]; congr 1; rw [Units.val_mul, hu]; ring
  have h3 : ψ (((x : R) - c) * (y : R)) = ψ ((x : R) * y) * (ψ (c * (y : R)))⁻¹ := by
    rw [← AddChar.map_neg_eq_inv, ← AddChar.map_add_eq_mul]; congr 1; ring
  rw [map_mul, mul_inv, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, h1, h2, h3]
  ring
open scoped Classical in
lemma gauss_sum_localize (hI : ∀ y ∈ I, ∀ y' ∈ I, y * y' = 0) (hψ : ∀ z : R, (∀ y ∈ I, ψ (z * y) = 1) → z ∈ I)
    (χ : Rˣ →* ℂˣ) (c : R)
    (hχ : ∀ u : Rˣ, (u : R) - 1 ∈ I → ((χ u : ℂˣ) : ℂ) = ψ (c * ((u : R) - 1))) :
    ∑ x : Rˣ, (((χ x)⁻¹ : ℂˣ) : ℂ) * ψ (x : R) =
      ∑ x : Rˣ, if (x : R) - c ∈ I then (((χ x)⁻¹ : ℂˣ) : ℂ) * ψ (x : R) else 0 := by
  classical
  have : Fintype I := Fintype.ofFinite I
  set t : Rˣ → ℂ := fun x => (((χ x)⁻¹ : ℂˣ) : ℂ) * ψ (x : R) with ht
  have hcard : (Fintype.card I : ℂ) ≠ 0 := by
    have : 0 < Fintype.card I := Fintype.card_pos
    exact_mod_cast this.ne'
  have h1 : (Fintype.card I : ℂ) * ∑ x : Rˣ, t x = ∑ y : I, ∑ x : Rˣ, t (x * d9u I hI y) := by
    have : ∀ y : I, ∑ x : Rˣ, t (x * d9u I hI y) = ∑ x : Rˣ, t x :=
      fun y => Equiv.sum_comp (Equiv.mulRight (d9u I hI y)) t
    simp only [this, sum_const, card_univ, nsmul_eq_mul]
  have h2 : ∑ y : I, ∑ x : Rˣ, t (x * d9u I hI y) =
      ∑ x : Rˣ, t x * ∑ y : I, ψ (((x : R) - c) * (y : R)) := by
    rw [sum_comm]
    apply sum_congr rfl
    intro x _
    rw [mul_sum]
    apply sum_congr rfl
    intro y _
    exact gauss_sum_translate_unit I ψ hI χ c hχ x y
  have h3 : ∀ x : Rˣ, t x * ∑ y : I, ψ (((x : R) - c) * (y : R)) =
      (Fintype.card I : ℂ) * (if (x : R) - c ∈ I then t x else 0) := by
    intro x
    by_cases hx : (x : R) - c ∈ I
    · rw [if_pos hx]
      have : ∀ y : I, ψ (((x : R) - c) * (y : R)) = 1 := by
        intro y; rw [hI _ hx _ y.2, AddChar.map_zero_eq_one]
      simp only [this, sum_const, card_univ, nsmul_eq_mul, mul_one]
      ring
    · rw [if_neg hx, mul_zero, sum_additive_character_eq_zero I ψ _ ?_, mul_zero]
      by_contra hcon
      push Not at hcon
      exact hx (hψ _ hcon)
  rw [h2] at h1
  simp only [h3] at h1
  rw [← mul_sum] at h1
  exact mul_left_cancel₀ hcard h1
end gauss
theorem gauss_sum_ratio : GaussSumTwist := by
  intro R _ _ _ I ψ ν dl c x0 hI hψ hν hdl hx0
  classical
  have : Fintype I := Fintype.ofFinite I

  have hrep : ∀ x : Rˣ, (x : R) - c ∈ I → ((x0⁻¹ * x : Rˣ) : R) - 1 ∈ I := by
    intro x hx
    have : ((x0⁻¹ * x : Rˣ) : R) - 1 = ((x0⁻¹ : Rˣ) : R) * (((x : R) - c) - ((x0 : R) - c)) := by
      rw [Units.val_mul]
      have : ((x0⁻¹ : Rˣ) : R) * (x0 : R) = 1 := by rw [← Units.val_mul]; simp
      linear_combination this
    rw [this]
    exact I.mul_mem_left _ (I.sub_mem hx hx0)
  constructor
  · rw [gauss_sum_localize I ψ hI hψ ν c hν, Nat.card_eq_fintype_card]

    have hbij : ∑ x : Rˣ, (if (x : R) - c ∈ I then (((ν x)⁻¹ : ℂˣ) : ℂ) * ψ (x : R) else 0) =
        ∑ y : I, (((ν (x0 * d9u I hI y))⁻¹ : ℂˣ) : ℂ) * ψ ((x0 * d9u I hI y : Rˣ) : R) := by
      rw [← sum_filter]
      symm
      apply sum_bij (fun (y : I) _ => x0 * d9u I hI y)
      · intro y _
        rw [mem_filter]
        refine ⟨mem_univ _, ?_⟩
        have : ((x0 * d9u I hI y : Rˣ) : R) - c = ((x0 : R) - c) + (x0 : R) * y := by
          rw [Units.val_mul]; show (x0 : R) * (1 + y) - c = _; ring
        rw [this]
        exact I.add_mem hx0 (I.mul_mem_left _ y.2)
      · intro y _ y' _ h
        have h' := mul_left_cancel h
        have h'' : ((d9u I hI y : Rˣ) : R) = ((d9u I hI y' : Rˣ) : R) := by rw [h']
        have : (1 : R) + y = 1 + y' := h''
        exact Subtype.ext (add_left_cancel this)
      · intro x hx
        rw [mem_filter] at hx
        refine ⟨⟨((x0⁻¹ * x : Rˣ) : R) - 1, hrep x hx.2⟩, mem_univ _, ?_⟩
        apply Units.ext
        rw [Units.val_mul]
        show (x0 : R) * (1 + (((x0⁻¹ * x : Rˣ) : R) - 1)) = x
        rw [Units.val_mul]
        have : (x0 : R) * ((x0⁻¹ : Rˣ) : R) = 1 := by rw [← Units.val_mul]; simp
        linear_combination (x : R) * this
      · intro y _; rfl
    rw [hbij]
    have : ∀ y : I, (((ν (x0 * d9u I hI y))⁻¹ : ℂˣ) : ℂ) * ψ ((x0 * d9u I hI y : Rˣ) : R) =
        (((ν x0)⁻¹ : ℂˣ) : ℂ) * ψ (x0 : R) := by
      intro y
      rw [gauss_sum_translate_unit I ψ hI ν c hν x0 y, hI _ hx0 _ y.2, AddChar.map_zero_eq_one, mul_one]
    simp only [this, sum_const, card_univ, nsmul_eq_mul]
  · have hνd : ∀ u : Rˣ, (u : R) - 1 ∈ I → (((ν * dl) u : ℂˣ) : ℂ) = ψ (c * ((u : R) - 1)) := by
      intro u hu
      rw [MonoidHom.mul_apply, hdl u hu, mul_one, hν u hu]
    rw [gauss_sum_localize I ψ hI hψ (ν * dl) c hνd, gauss_sum_localize I ψ hI hψ ν c hν, mul_sum]
    apply sum_congr rfl
    intro x _
    by_cases hx : (x : R) - c ∈ I
    · rw [if_pos hx, if_pos hx]
      have hd : dl x = dl x0 := by
        have := hdl _ (hrep x hx)
        rw [map_mul, map_inv, inv_mul_eq_one] at this
        exact this.symm
      rw [MonoidHom.mul_apply, hd, mul_inv, Units.val_mul]
      ring
    · rw [if_neg hx, if_neg hx, mul_zero]
theorem valuation_ratio_bound : TowerValuationBound := by
  intro G _ v hv a a' d h p q e h1 h2 h3 h4 h5 T Td Tdp ρ E N0 ε δ σ hN hε hR1 hR2 c0 c00 A A0 A0'
    hC1 hC2 hCor ub ua hub hua r hr
  classical
  set f : ℤ → ℝ := fun s => |v (T s)| + |v (Td s)| with hf
  have hf0 : ∀ s, 0 ≤ f s := fun s => add_nonneg (abs_nonneg _) (abs_nonneg _)
  set S : ℝ := ∑ s ∈ Icc (1 : ℤ) h, f s with hS
  have up : ∀ s : ℤ, 1 ≤ s → s ≤ h → v (ρ s) ≤ f s + ε := by
    intro s a1 a2
    obtain ⟨b1, b2, b3⟩ := hR1 s a1 a2
    rw [b1, additive_map_div hv]
    have := le_abs_self (v (Td s))
    have := neg_abs_le (v (T s))
    simp only [hf]; linarith
  have lo : ∀ s : ℤ, 1 ≤ s → s ≤ h → -v (ρ s) ≤ f s + N0 := by
    intro s a1 a2
    obtain ⟨b1, b2, b3⟩ := hR1 s a1 a2
    rw [b1, additive_map_div hv]
    have := le_abs_self (v (T s))
    have := abs_nonneg (v (Td s))
    simp only [hf]; linarith
  have gen : ∀ {ι : Type} (I : Finset ι) (φ : ι → ℤ) (w : ι → ℝ) (c : ℝ), Set.InjOn φ I →
      (∀ k ∈ I, 1 ≤ φ k ∧ φ k ≤ h) → (∀ k ∈ I, w k ≤ f (φ k) + c) →
      ∑ k ∈ I, w k ≤ S + I.card * c := by
    intro ι I φ w c hinj hran hw
    classical
    calc ∑ k ∈ I, w k ≤ ∑ k ∈ I, (f (φ k) + c) := sum_le_sum hw
      _ = ∑ s ∈ I.image φ, f s + I.card * c := by
          rw [sum_add_distrib, sum_const, nsmul_eq_mul, sum_image hinj]
      _ ≤ S + I.card * c := by
          have : ∑ s ∈ I.image φ, f s ≤ S := by
            apply sum_le_sum_of_subset_of_nonneg
            · intro s hs
              rw [mem_image] at hs
              obtain ⟨k, hk, rfl⟩ := hs
              rw [mem_Icc]; exact hran k hk
            · intro s _ _; exact hf0 s
          linarith

  have n1 : ∑ s ∈ Icc (1 - ((e : ℤ) + q - p)) 0, v (ρ s) ≤ S + ((e : ℝ) + q - p) * ε := by
    have hc : ((Icc (1 - ((e : ℤ) + q - p)) 0).card : ℝ) = (e : ℝ) + q - p := by
      rw [Int.card_Icc]
      have : (0 + 1 - (1 - ((e : ℤ) + q - p))).toNat = e + q - p := by omega
      rw [this, Nat.cast_sub (by omega)]; push_cast; ring
    rw [← hc]
    apply gen _ (fun s => 1 - s)
    · intro x _ y _ hxy; simp only at hxy; omega
    · intro s hs; rw [mem_Icc] at hs; constructor <;> omega
    · intro s hs; rw [mem_Icc] at hs
      obtain ⟨b1, b2⟩ := hR2 s hs.1 hs.2
      rw [b1, hv, b2, zero_add]
      exact up _ (by omega) (by omega)
  have n2 : ∑ s ∈ Icc (1 : ℤ) ((h : ℤ) - (p + q)), v (ρ s) ≤ S + ((h : ℝ) - (p + q)) * ε := by
    have hc : ((Icc (1 : ℤ) ((h : ℤ) - (p + q))).card : ℝ) = (h : ℝ) - (p + q) := by
      rw [Int.card_Icc]
      have : ((h : ℤ) - (p + q) + 1 - 1).toNat = h - (p + q) := by omega
      rw [this, Nat.cast_sub (by omega)]; push_cast; ring
    rw [← hc]
    apply gen _ (fun s => s)
    · intro x _ y _ hxy; exact hxy
    · intro s hs; rw [mem_Icc] at hs; constructor <;> omega
    · intro s hs; rw [mem_Icc] at hs
      exact up _ (by omega) (by omega)
  have n3 : ∑ k ∈ Icc 1 p, v (ρ ((e : ℤ) + q - k + 1)) ≤ S + (p : ℝ) * ε := by
    have hc : ((Icc 1 p).card : ℝ) = (p : ℝ) := by rw [Nat.card_Icc]; simp
    rw [← hc]
    apply gen _ (fun k : ℕ => (e : ℤ) + q - k + 1)
    · intro x _ y _ hxy; simp only at hxy; omega
    · intro k hk; rw [mem_Icc] at hk; constructor <;> omega
    · intro k hk; rw [mem_Icc] at hk
      exact up _ (by omega) (by omega)
  have n4 : ∑ k ∈ Icc 1 q, -v (ρ ((e : ℤ) + k)) ≤ S + (q : ℝ) * N0 := by
    have hc : ((Icc 1 q).card : ℝ) = (q : ℝ) := by rw [Nat.card_Icc]; simp
    rw [← hc]
    apply gen _ (fun k : ℕ => (e : ℤ) + k)
    · intro x _ y _ hxy; simp only at hxy; omega
    · intro k hk; rw [mem_Icc] at hk; constructor <;> omega
    · intro k hk; rw [mem_Icc] at hk
      exact lo _ (by omega) (by omega)
  have hsplit : ∑ s ∈ Icc (1 - ((e : ℤ) + q - p)) ((h : ℤ) - (p + q)), v (ρ s) =
      ∑ s ∈ Icc (1 - ((e : ℤ) + q - p)) 0, v (ρ s) + ∑ s ∈ Icc (1 : ℤ) ((h : ℤ) - (p + q)), v (ρ s) := by
    rw [← sum_union]
    · congr 1
      ext s; simp only [mem_Icc, mem_union]; omega
    · rw [disjoint_left]; intro s hs hs'; rw [mem_Icc] at hs hs'; omega
  have hA : v A = v A0 + ∑ s ∈ Icc (1 - ((e : ℤ) + q - p)) ((h : ℤ) - (p + q)), v (ρ s) := by
    have := congrArg v hCor
    rw [additive_map_div hv, additive_map_prod hv] at this
    linarith
  have u1 : ∑ j ∈ range q, v (ub j) ≤ (q : ℝ) * σ := by
    have := sum_le_card_nsmul (range q) (fun j => v (ub j)) σ (fun j hj => hub j (mem_range.mp hj))
    simpa using this
  have u2 : ∑ i ∈ range p, v (ua i) ≤ (p : ℝ) * σ := by
    have := sum_le_card_nsmul (range p) (fun j => v (ua j)) σ (fun j hj => hua j (mem_range.mp hj))
    simpa using this
  have hvr : v r = ∑ j ∈ range q, v (ub j) + ∑ i ∈ range p, v (ua i) + (v c0 - v c00) +
      ∑ k ∈ Icc 1 p, v (ρ ((e : ℤ) + q - k + 1)) + ∑ k ∈ Icc 1 q, -v (ρ ((e : ℤ) + k)) := by
    rw [hr, hv, hv, hv, hv, additive_map_inv hv, additive_map_div hv, additive_map_prod hv, additive_map_prod hv, additive_map_prod hv,
      additive_map_prod hv, sum_neg_distrib]
  have b1 := le_abs_self (v A0)
  have b2 := le_abs_self (v A0')
  have hd : (d : ℝ) = 2 * h := by exact_mod_cast h3
  have hh : (h : ℝ) = a' + e := by
    have : h = a' + e := by omega
    exact_mod_cast this
  have hq' : (q : ℝ) ≤ d := by
    have : q ≤ d := by omega
    exact_mod_cast this
  have hcnt : ((e : ℝ) + q - p) + ((h : ℝ) - (p + q)) + p ≤ d := by
    have : (0 : ℝ) ≤ p := Nat.cast_nonneg _
    have : (0 : ℝ) ≤ a' := Nat.cast_nonneg _
    linarith
  have t1 : (((e : ℝ) + q - p) + ((h : ℝ) - (p + q)) + p) * ε ≤ d * ε :=
    mul_le_mul_of_nonneg_right hcnt hε
  have t2 : (q : ℝ) * N0 ≤ d * N0 := mul_le_mul_of_nonneg_right hq' hN
  rw [hvr]
  push_cast
  nlinarith
lemma log_div_sq_le_difference (m : ℕ) (hm : 4 ≤ m) :
    Real.log ((m + 1 : ℕ) : ℝ) / (((m + 1 : ℕ) : ℝ)) ^ 2 ≤
      (1 + Real.log m) / m - (1 + Real.log ((m + 1 : ℕ) : ℝ)) / ((m + 1 : ℕ) : ℝ) := by
  have hx : (4 : ℝ) ≤ m := by exact_mod_cast hm
  push_cast
  set x : ℝ := (m : ℝ) with hxdef
  have hx0 : 0 < x := by linarith
  set L1 := Real.log (x + 1) with hL1
  set L0 := Real.log x with hL0
  have hdiff : L1 - L0 ≤ 1 / x := by
    have h1 : L1 - L0 = Real.log ((x + 1) / x) := by
      rw [Real.log_div (by linarith) (by linarith)]
    have h2 := Real.log_le_sub_one_of_pos (show 0 < (x + 1) / x by positivity)
    have h3 : (x + 1) / x - 1 = 1 / x := by field_simp; ring
    linarith
  have hbig : (5 : ℝ) / 4 ≤ L1 := by
    have h4 : Real.log 4 ≤ L1 := Real.log_le_log (by norm_num) (by linarith)
    have h5 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    have := Real.log_two_gt_d9
    linarith
  have e1 : (1 + L1) / (x * (x + 1)) - 1 / x ^ 2 - L1 / (x + 1) ^ 2 =
      (L1 * x - x - 1) / (x ^ 2 * (x + 1) ^ 2) := by
    field_simp; ring
  have e2 : (1 + L0) / x - (1 + L1) / (x + 1) - ((1 + L1) / (x * (x + 1)) - 1 / x ^ 2) =
      (L0 - L1 + 1 / x) / x := by
    field_simp; ring
  have p1 : 0 ≤ (L1 * x - x - 1) / (x ^ 2 * (x + 1) ^ 2) :=
    div_nonneg (by nlinarith) (by positivity)
  have p2 : 0 ≤ (L0 - L1 + 1 / x) / x := div_nonneg (by linarith) hx0.le
  linarith
lemma sum_log_div_sq_telescoping (M : ℕ) (hM : 4 ≤ M) :
    ∑ n ∈ Icc 5 M, Real.log n / (n : ℝ) ^ 2 ≤ (1 + Real.log 4) / 4 - (1 + Real.log M) / M := by
  induction M, hM using Nat.le_induction with
  | base => simp
  | succ M hM ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have := log_div_sq_le_difference M hM
    linarith
theorem prime_sum_bound : PrimeLogSquareSumLtOne := by
  intro P hP
  set M : ℕ := max (P.sup id) 4 with hMdef
  have hM : 4 ≤ M := le_max_right _ _
  have hsub : P ⊆ {2, 3} ∪ Icc 5 M := by
    intro l hl
    have hp := hP l hl
    have h2 := hp.two_le
    have hle : l ≤ M := le_trans (Finset.le_sup (f := id) hl) (le_max_left _ _)
    have h4 : l ≠ 4 := by
      rintro rfl; exact absurd hp (by norm_num)
    simp only [mem_union, mem_insert, mem_singleton, mem_Icc]
    omega
  have hnn : ∀ n : ℕ, 0 ≤ Real.log n / (n : ℝ) ^ 2 := by
    intro n; exact div_nonneg (Real.log_natCast_nonneg n) (by positivity)
  have h1 : ∑ l ∈ P, Real.log l / (l : ℝ) ^ 2 ≤ ∑ l ∈ {2, 3} ∪ Icc 5 M, Real.log l / (l : ℝ) ^ 2 :=
    sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => hnn n)
  have hd : Disjoint ({2, 3} : Finset ℕ) (Icc 5 M) := by
    rw [disjoint_left]; intro x hx hx'
    simp only [mem_insert, mem_singleton] at hx; rw [mem_Icc] at hx'; omega
  rw [sum_union hd, sum_pair (by norm_num)] at h1
  have h2 := sum_log_div_sq_telescoping M hM
  have h3 : 0 ≤ (1 + Real.log M) / M :=
    div_nonneg (by have := Real.log_natCast_nonneg M; linarith) (Nat.cast_nonneg _)
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have h5 : Real.log 3 ≤ Real.log 4 := Real.log_le_log (by norm_num) (by norm_num)
  have h6 := Real.log_two_lt_d9
  push_cast at h1
  linarith
theorem prime_budget_bound : PrimeLogBudget := by
  intro N0 BN0 h P hP
  have h1 := h P hP
  have h2 := prime_sum_bound P hP
  have e : ∑ l ∈ P, (N0 l + ((l : ℝ) ^ 2)⁻¹) * Real.log l =
      ∑ l ∈ P, N0 l * Real.log l + ∑ l ∈ P, Real.log l / (l : ℝ) ^ 2 := by
    rw [← sum_add_distrib]; apply sum_congr rfl; intro l _; rw [div_eq_mul_inv]; ring
  rw [e]; linarith
theorem grid_bound : GridValuationBound := by
  intro W X S m N lam δ ell N0 vr vx XX ch dd yy S0 cc ee qq vq H B BN Bδ W0 hlam hδ hN0 hvq hprime
    hfib hdd hyy hcc hsq hH hBN hBδ hq
  classical
  set t : W → ℝ := fun w => N0 (ell w) + ((ell w : ℝ) ^ 2)⁻¹ with ht
  set uu : W → ℝ := fun w => ∑ s ∈ S0, (cc s : ℝ) * vq w s with huu
  have ht0 : ∀ w, 0 ≤ t w := fun w => add_nonneg (hN0 _) (by positivity)
  have hu0 : ∀ w, 0 ≤ uu w := fun w => sum_nonneg (fun s _ => mul_nonneg (Nat.cast_nonneg _) (hvq w s))
  set Q : ℝ := ∑ s ∈ S0, (ee s : ℝ) * Real.log (qq s) with hQ
  have hlogq : ∀ s ∈ S0, 0 ≤ Real.log (qq s) := fun s _ => Real.log_natCast_nonneg _
  have hQ0 : 0 ≤ Q := sum_nonneg (fun s hs => mul_nonneg (Nat.cast_nonneg _) (hlogq s hs))
  have hcard : ((Finset.univ : Finset (Fin m × Fin m)).card : ℝ) = (m : ℝ) ^ 2 := by
    rw [card_univ, Fintype.card_prod, Fintype.card_fin]; push_cast; ring

  have hpt : ∀ w ∈ W0, lam w * ∑ ij, vr w ij ≤
      ∑ ij, ∑ b, ∑ x ∈ XX ij b, lam w * |vx w x| +
        (m : ℝ) ^ 2 * (2 * N * (lam w * t w) + 6 * (lam w * δ w) + 2 * m * (lam w * uu w)) := by
    intro w hw
    have h1 : ∑ ij, vr w ij ≤ ∑ ij, (∑ b, ∑ x ∈ XX ij b, |vx w x| +
        (2 * N * t w + 6 * δ w + 2 * m * uu w)) := by
      apply sum_le_sum
      intro ij _
      have a1 := hsq w hw ij
      have a2 : ∑ x ∈ XX ij (ch w), |vx w x| ≤ ∑ b, ∑ x ∈ XX ij b, |vx w x| :=
        Finset.single_le_sum (f := fun b => ∑ x ∈ XX ij b, |vx w x|)
          (fun b _ => sum_nonneg (fun x _ => abs_nonneg _)) (mem_univ (ch w))
      have a3 : (dd ij : ℝ) * t w ≤ 2 * N * t w := by
        apply mul_le_mul_of_nonneg_right _ (ht0 w)
        exact_mod_cast hdd ij
      have a4 : 2 * (yy ij : ℝ) * uu w ≤ 2 * m * uu w := by
        apply mul_le_mul_of_nonneg_right _ (hu0 w)
        have : (yy ij : ℝ) ≤ m := by exact_mod_cast hyy ij
        linarith
      linarith
    rw [sum_add_distrib, sum_const, nsmul_eq_mul, hcard] at h1
    have h2 := mul_le_mul_of_nonneg_left h1 (hlam w)
    refine h2.trans (le_of_eq ?_)
    rw [mul_add, mul_sum]
    congr 1
    · apply sum_congr rfl; intro ij _
      rw [mul_sum]; apply sum_congr rfl; intro b _
      rw [mul_sum]
    · ring
  have hsum := sum_le_sum hpt
  rw [sum_add_distrib, ← mul_sum, sum_add_distrib, sum_add_distrib, ← mul_sum, ← mul_sum, ← mul_sum]
    at hsum

  have hX : ∑ w ∈ W0, ∑ ij, ∑ b, ∑ x ∈ XX ij b, lam w * |vx w x| ≤ ∑ ij, ∑ b, ∑ x ∈ XX ij b, H x := by
    rw [sum_comm]
    apply sum_le_sum; intro ij _
    rw [sum_comm]
    apply sum_le_sum; intro b _
    rw [sum_comm]
    apply sum_le_sum; intro x _
    exact hH x W0

  have hT : ∑ w ∈ W0, lam w * t w ≤ BN := by
    have hmaps : ∀ w ∈ W0, ell w ∈ W0.image ell := fun w hw => mem_image_of_mem _ hw
    rw [← sum_fiberwise_of_maps_to hmaps]
    refine le_trans (sum_le_sum ?_) (hBN (W0.image ell) ?_)
    · intro l _
      have e1 : ∑ w ∈ W0 with ell w = l, lam w * t w =
          (N0 l + ((l : ℝ) ^ 2)⁻¹) * ∑ w ∈ W0 with ell w = l, lam w := by
        rw [mul_sum]
        apply sum_congr rfl
        intro w hw
        rw [mem_filter] at hw
        simp only [ht, hw.2]; ring
      rw [e1]
      apply mul_le_mul_of_nonneg_left
      · exact hfib l _ (fun w hw => (mem_filter.mp hw).2)
      · exact add_nonneg (hN0 _) (by positivity)
    · intro l hl
      rw [mem_image] at hl
      obtain ⟨w, _, rfl⟩ := hl
      exact hprime w

  have hU : ∑ w ∈ W0, lam w * uu w ≤ Q := by
    have e1 : ∑ w ∈ W0, lam w * uu w = ∑ s ∈ S0, (cc s : ℝ) * ∑ w ∈ W0, lam w * vq w s := by
      simp only [huu, mul_sum]
      rw [sum_comm]
      apply sum_congr rfl; intro s _
      apply sum_congr rfl; intro w _
      ring
    rw [e1]
    apply sum_le_sum
    intro s hs
    have c1 : (cc s : ℝ) ≤ ee s := by exact_mod_cast hcc s hs
    calc (cc s : ℝ) * ∑ w ∈ W0, lam w * vq w s ≤ (cc s : ℝ) * Real.log (qq s) :=
          mul_le_mul_of_nonneg_left (hq s hs W0) (Nat.cast_nonneg _)
      _ ≤ (ee s : ℝ) * Real.log (qq s) := mul_le_mul_of_nonneg_right c1 (hlogq s hs)
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hNn : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hin : 2 * N * ∑ w ∈ W0, lam w * t w + 6 * ∑ w ∈ W0, lam w * δ w +
      2 * m * ∑ w ∈ W0, lam w * uu w ≤ 2 * N * BN + 6 * Bδ + 4 * m * Q := by
    have z1 : 2 * N * ∑ w ∈ W0, lam w * t w ≤ 2 * N * BN :=
      mul_le_mul_of_nonneg_left hT (by positivity)
    have z2 := hBδ W0
    have z3 : 2 * m * ∑ w ∈ W0, lam w * uu w ≤ 2 * m * Q :=
      mul_le_mul_of_nonneg_left hU (by positivity)
    have z4 : 0 ≤ m * Q := mul_nonneg hm0 hQ0
    linarith
  have hmain : ∑ w ∈ W0, lam w * ∑ ij, vr w ij ≤
      (∑ ij, ∑ b, ∑ x ∈ XX ij b, H x) + (m : ℝ) ^ 2 * (2 * N * BN + 6 * Bδ + 4 * m * Q) := by
    have := mul_le_mul_of_nonneg_left hin (show (0 : ℝ) ≤ (m : ℝ) ^ 2 by positivity)
    linarith
  refine ⟨hmain, ?_⟩
  intro hB0 hHB hXc
  have hHH : ∑ ij, ∑ b, ∑ x ∈ XX ij b, H x ≤ (m : ℝ) ^ 2 * (2 * (2 + 8 * N) * B) := by
    have : ∀ ij b, ∑ x ∈ XX ij b, H x ≤ (2 + 8 * N) * B := by
      intro ij b
      have k1 := sum_le_card_nsmul (XX ij b) H B (fun x _ => hHB x)
      rw [nsmul_eq_mul] at k1
      have k2 : ((XX ij b).card : ℝ) ≤ 2 + 8 * N := by exact_mod_cast hXc ij b
      exact k1.trans (mul_le_mul_of_nonneg_right k2 hB0)
    calc ∑ ij, ∑ b, ∑ x ∈ XX ij b, H x ≤ ∑ _ij : Fin m × Fin m, ∑ _b : Bool, (2 + 8 * (N : ℝ)) * B :=
          sum_le_sum (fun ij _ => sum_le_sum (fun b _ => this ij b))
      _ = (m : ℝ) ^ 2 * (2 * (2 + 8 * N) * B) := by
          simp only [sum_const, nsmul_eq_mul, card_univ, Fintype.card_bool, Fintype.card_prod, Fintype.card_fin]
          push_cast; ring
  have hfin : ∑ w ∈ W0, lam w * ∑ ij, vr w ij ≤
      (m : ℝ) ^ 2 * (2 * (2 + 8 * N) * B + 2 * N * BN + 6 * Bδ + 4 * m * Q) := by
    have e : (m : ℝ) ^ 2 * (2 * (2 + 8 * N) * B + 2 * N * BN + 6 * Bδ + 4 * m * Q) =
        (m : ℝ) ^ 2 * (2 * (2 + 8 * N) * B) + (m : ℝ) ^ 2 * (2 * N * BN + 6 * Bδ + 4 * m * Q) := by ring
    rw [e]; linarith
  refine ⟨hfin, ?_⟩
  have e : ∑ w ∈ W0, lam w * ((∑ ij, vr w ij) + δ w) =
      ∑ w ∈ W0, lam w * ∑ ij, vr w ij + ∑ w ∈ W0, lam w * δ w := by
    rw [← sum_add_distrib]; apply sum_congr rfl; intro w _; ring
  rw [e]
  have := hBδ W0
  linarith
theorem grid_squares_bound : GridValuationBoundSquares := by
  intro W S m N lam δ ell N0 vr vA vA' vT vTd ch dd hh yy S0 cc ee qq vq B BN Bδ W0 hlam hδ hN0 hvq
    hprime hfib hdh hdd hyy hcc hsq hA hA' hT hTd hBN hBδ hq
  classical
  by_cases hm : m = 0
  · subst hm
    simp
  let vx : W → ((Fin m × Fin m) × Bool) × (Bool ⊕ (Fin 4 × ℤ × Bool)) → ℝ := fun w x =>
    match x.2 with
    | Sum.inl false => vA w x.1.1
    | Sum.inl true => vA' w x.1.1
    | Sum.inr (_, s, false) => vT w x.1.1 s
    | Sum.inr (_, s, true) => vTd w x.1.1 x.1.2 s
  let XX : Fin m × Fin m → Bool → Finset (((Fin m × Fin m) × Bool) × (Bool ⊕ (Fin 4 × ℤ × Bool))) := fun ij b =>
    ({(ij, b)} : Finset ((Fin m × Fin m) × Bool)) ×ˢ
      ((Finset.univ : Finset Bool).disjSum
        ((Finset.univ : Finset (Fin 4)) ×ˢ (Icc (1 : ℤ) (hh ij) ×ˢ (Finset.univ : Finset Bool))))
  have hB0 : 0 ≤ B := by
    have ij : Fin m × Fin m := (⟨0, by omega⟩, ⟨0, by omega⟩)
    simpa using hA ij ∅
  have hsumXX : ∀ w ij b, ∑ x ∈ XX ij b, |vx w x| = |vA w ij| + |vA' w ij| +
      4 * (∑ s ∈ Icc (1 : ℤ) (hh ij), (|vT w ij s| + |vTd w ij b s|)) := by
    intro w ij b
    simp only [XX, sum_product, sum_singleton, sum_disjSum, Fintype.sum_bool, vx, sum_const,
      card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    have : ∑ s ∈ Icc (1 : ℤ) (hh ij), (|vTd w ij b s| + |vT w ij s|) =
        ∑ s ∈ Icc (1 : ℤ) (hh ij), (|vT w ij s| + |vTd w ij b s|) :=
      sum_congr rfl (fun s _ => add_comm _ _)
    rw [this]; ring
  have hcardXX : ∀ ij b, (XX ij b).card ≤ 2 + 8 * N := by
    intro ij b
    simp only [XX, card_product, card_singleton, card_disjSum, card_univ, Fintype.card_bool,
      Fintype.card_fin, Int.card_Icc]
    have h1 := hdh ij
    have h2 := hdd ij
    have : ((hh ij : ℤ) + 1 - 1).toNat = hh ij := by omega
    rw [this]; omega
  refine ((grid_bound W _ S m N lam δ ell N0 vr vx XX ch dd yy S0 cc ee qq vq (fun _ => B) B BN Bδ W0
    hlam hδ hN0 hvq hprime hfib hdd hyy hcc ?_ ?_ hBN hBδ hq).2 hB0 (fun _ => le_rfl) hcardXX).1
  · intro w hw ij
    rw [hsumXX]
    have := hsq w hw ij
    linarith
  · rintro ⟨⟨ij, b⟩, (t | ⟨k, s, t⟩)⟩ F
    · cases t
      · exact hA ij F
      · exact hA' ij F
    · cases t
      · exact hT ij s F
      · exact hTd ij b s F
section tests
example : (6 : ℚ) = ((∏ j ∈ range 1, (if j = 0 then (2 : ℚ) else 3)) * ∏ _i ∈ range 1, (3 : ℚ)) * 1 *
    (∏ k ∈ Icc 1 1, (((6 : ℤ) + (1 : ℕ) - (k : ℕ) + 1 : ℤ) : ℚ)) / ∏ k ∈ Icc 1 1, (((6 : ℤ) + (k : ℕ) : ℤ) : ℚ) := by
  have := tower_bound ℚ (fun s => (s : ℚ))
    (fun i j => if i = 0 ∧ j = 0 then 6 else if i = 0 ∧ j = 1 then 21 else 1)
    (fun _ j => if j = 0 then 2 else 3) 1 1 6
    (by intro k h1 h2; obtain rfl : k = 1 := by omega
        norm_num)
    (by intro j hj; obtain rfl : j = 0 := by omega
        norm_num)
    (by intro i hi; obtain rfl : i = 0 := by omega
        norm_num)
  simpa using this
example : ((6 : ℤ) : ℝ) ≤ |((0 : ℤ) : ℝ)| + |((0 : ℤ) : ℝ)| +
      4 * (∑ _s ∈ Icc (1 : ℤ) ((12 : ℕ) : ℤ), (|((0 : ℤ) : ℝ)| + |((0 : ℤ) : ℝ)|)) +
      ((24 : ℕ) : ℝ) * ((0 : ℝ) + 0) + 6 * (1 : ℝ) + ((1 + 1 : ℕ) : ℝ) * (0 : ℝ) ∧
    |((0 : ℤ) : ℝ)| + |((0 : ℤ) : ℝ)| +
      4 * (∑ _s ∈ Icc (1 : ℤ) ((12 : ℕ) : ℤ), (|((0 : ℤ) : ℝ)| + |((0 : ℤ) : ℝ)|)) +
      ((24 : ℕ) : ℝ) * ((0 : ℝ) + 0) + 6 * (1 : ℝ) + ((1 + 1 : ℕ) : ℝ) * (0 : ℝ) = ((6 : ℤ) : ℝ) := by
  refine ⟨?_, by simp⟩
  exact valuation_ratio_bound (Multiplicative ℤ) (fun x => ((Multiplicative.toAdd x : ℤ) : ℝ))
    (by intro x y; simp) 18 6 24 12 1 1 6 rfl rfl rfl (by norm_num) (by norm_num)
    (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1) 0 0 1 0 le_rfl le_rfl
    (by intro s _ _; simp) (by intro s _ _; simp)
    (Multiplicative.ofAdd 3) (Multiplicative.ofAdd (-3)) 1 1 1 (by simp) (by simp) (by simp)
    (fun _ => 1) (fun _ => 1) (by simp) (by simp) (Multiplicative.ofAdd 6)
    (by simp only [prod_const_one, one_mul, mul_one, inv_one]; rfl)
example : (2 : ℝ) ^ (1 * 1 * 1) * (∏ i ∈ Icc 1 (1 + 1), (1 - ((2 : ℝ) ^ i)⁻¹)) /
    ((∏ i ∈ Icc 1 1, (1 - ((2 : ℝ) ^ i)⁻¹)) * ∏ i ∈ Icc 1 1, (1 - ((2 : ℝ) ^ i)⁻¹)) = 3 := by
  rw [Finset.prod_Icc_succ_top (by norm_num)]
  simp only [Icc_self, prod_singleton]
  norm_num
def trivialValuationRat : AddValuation ℚ (WithTop ℝ) :=
  AddValuation.of (fun x => if x = 0 then ⊤ else 0) (by simp) (by simp)
    (by
      intro x y
      by_cases hx : x = 0
      · simp [hx]
      · by_cases hy : y = 0
        · simp [hy]
        · by_cases hxy : x + y = 0 <;> simp [hx, hy, hxy])
    (by
      intro x y
      by_cases hx : x = 0
      · simp [hx]
      · by_cases hy : y = 0
        · simp [hy]
        · simp [hx, hy])
example : trivialValuationRat (1 : ℚ) ≤ trivialValuationRat (∑ _x ∈ ({()} : Finset Unit), ∑ _k : Unit, ∑ _l : Unit,
    (1 : ℚ) * (RingHom.id ℚ) 1 * 1) + ((3 * 0 : ℝ) : WithTop ℝ) :=
  (lemma_c_gauss_sum ℚ trivialValuationRat trivialValuationRat (RingHom.id ℚ) (fun _ => rfl) Unit Unit {()} (fun _ _ => 1)
    (fun _ _ => 1) (fun _ _ _ => 1) 1 0 one_ne_zero (by simp) (by simp) (by simp)).1
example : ∑ _w ∈ ({()} : Finset Unit), Real.log 2 * |(1 : ℝ)| =
    (∑ _σ : Unit, Real.log 2) / Fintype.card Unit + 2 * ∑ _w ∈ ({()} : Finset Unit), Real.log 2 * max 0 (-(1 : ℝ)) :=
  (height_bound_alt Unit Unit (fun _ => Real.log 2) (fun _ => 1) (fun _ => 0) (fun _ => 2) {()} 0
    (fun _ => Real.log_nonneg (by norm_num)) (by simp) (by simp)).1
example : ∑ _w ∈ ({()} : Finset Unit), Real.log 2 * ∑ _ij : Fin 1 × Fin 1, (1 / 2 : ℝ) ≤
    (∑ _ij : Fin 1 × Fin 1, ∑ _b : Bool, ∑ _x ∈ (∅ : Finset Empty), (0 : ℝ)) +
      ((1 : ℕ) : ℝ) ^ 2 * (2 * ((1 : ℕ) : ℝ) * 1 + 6 * 0 +
        4 * ((1 : ℕ) : ℝ) * ∑ _s ∈ (∅ : Finset Empty), (((0 : ℕ)) : ℝ) * Real.log ((0 : ℕ) : ℝ)) :=
  (grid_bound Unit Empty Empty 1 1 (fun _ => Real.log 2) (fun _ => 0) (fun _ => 2) (fun _ => 0)
    (fun _ _ => 1 / 2) (fun _ x => x.elim) (fun _ _ => ∅) (fun _ => true) (fun _ => 2) (fun _ => 0) ∅
    (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ s => s.elim) (fun _ => 0) 0 1 0 {()}
    (fun _ => Real.log_nonneg (by norm_num)) (fun _ => le_rfl) (fun _ => le_rfl) (fun _ s => s.elim)
    (fun _ => Nat.prime_two)
    (by
      intro l F hF
      rcases F.eq_empty_or_nonempty with rfl | ⟨w, hw⟩
      · simpa using Real.log_natCast_nonneg l
      · rw [← hF w hw, sum_const, nsmul_eq_mul]
        have h1 : (F.card : ℝ) ≤ 1 := by exact_mod_cast (Finset.card_le_univ F)
        have h2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
        push_cast
        nlinarith)
    (by simp) (by simp) (by simp) (by intro w _ ij; norm_num) (by intro x; exact x.elim)
    (by
      intro P hP
      have := prime_sum_bound P hP
      refine le_of_lt (lt_of_eq_of_lt (sum_congr rfl ?_) this)
      intro l _
      rw [zero_add, div_eq_mul_inv, mul_comm])
    (by simp) (by simp)).1
def twoAdicValuationRat : AddValuation ℚ (WithTop ℝ) :=
  AddValuation.of (fun x => if x = 0 then ⊤ else (((padicValRat 2 x : ℤ) : ℝ) : WithTop ℝ)) (by simp) (by simp)
    (by
      intro x y
      by_cases hx : x = 0
      · simp [hx]
      · by_cases hy : y = 0
        · simp [hy]
        · by_cases hxy : x + y = 0
          · simp [hxy]
          · simp only [if_neg hx, if_neg hy, if_neg hxy]
            rw [← WithTop.coe_min, WithTop.coe_le_coe, ← Int.cast_min, Int.cast_le]
            exact padicValRat.min_le_padicValRat_add hxy)
    (by
      intro x y
      by_cases hx : x = 0
      · simp [hx]
      · by_cases hy : y = 0
        · simp [hy]
        · simp only [if_neg hx, if_neg hy, if_neg (mul_ne_zero hx hy)]
          rw [padicValRat.mul hx hy, ← WithTop.coe_add]; push_cast; rfl)
lemma two_adic_valuation_half : twoAdicValuationRat (1 / 2 : ℚ) = ((-1 : ℝ) : WithTop ℝ) := by
  have h : padicValRat 2 (1 / 2 : ℚ) = -1 := by
    rw [one_div, padicValRat.inv]
    have := padicValRat.self (p := 2) (by norm_num)
    rw [show ((2 : ℕ) : ℚ) = 2 by norm_num] at this
    rw [this]
  show (if (1 / 2 : ℚ) = 0 then ⊤ else (((padicValRat 2 (1 / 2 : ℚ) : ℤ) : ℝ) : WithTop ℝ)) = _
  rw [if_neg (by norm_num), h]; norm_num
example : twoAdicValuationRat (1 : ℚ) ≤ twoAdicValuationRat (∑ _x ∈ ({()} : Finset Unit), ∑ _k : Unit, ∑ _l : Unit,
      (1 / 2 : ℚ) * (RingHom.id ℚ) (1 / 2) * (1 / 2)) + ((3 * 1 : ℝ) : WithTop ℝ) ∧
    twoAdicValuationRat (1 : ℚ) = twoAdicValuationRat (∑ _x ∈ ({()} : Finset Unit), ∑ _k : Unit, ∑ _l : Unit,
      (1 / 2 : ℚ) * (RingHom.id ℚ) (1 / 2) * (1 / 2)) + ((3 * 1 : ℝ) : WithTop ℝ) := by
  constructor
  · exact (lemma_c_gauss_sum ℚ twoAdicValuationRat twoAdicValuationRat (RingHom.id ℚ) (fun _ => rfl) Unit Unit {()} (fun _ _ => 1 / 2)
      (fun _ _ => 1 / 2) (fun _ _ _ => 1 / 2) 1 1 one_ne_zero (by simp)
      (by intro x _ k; simp only [two_adic_valuation_half]; simp)
      (by intro x _ k l; simp only [two_adic_valuation_half]; simp)).1
  · simp only [sum_singleton, univ_unique, RingHom.id_apply, AddValuation.map_mul, two_adic_valuation_half,
      AddValuation.map_one]
    rw [← WithTop.coe_add, ← WithTop.coe_add, ← WithTop.coe_add, ← WithTop.coe_zero]
    congr 1; norm_num
example : ∑ x : (ZMod 4)ˣ,
    (((((ZMod.χ₄.ringHomComp (Int.castRingHom ℂ)).toUnitHom) x)⁻¹ : ℂˣ) : ℂ) *
      (AddChar.zmodChar 4 (ζ := Complex.I) Complex.I_pow_four) (x : ZMod 4) =
    (Nat.card (Ideal.span ({2} : Set (ZMod 4))) : ℂ) *
      ((((((ZMod.χ₄.ringHomComp (Int.castRingHom ℂ)).toUnitHom) 1)⁻¹ : ℂˣ) : ℂ) *
        (AddChar.zmodChar 4 (ζ := Complex.I) Complex.I_pow_four) ((1 : (ZMod 4)ˣ) : ZMod 4)) := by
  have hu : ∀ u : (ZMod 4)ˣ, (u : ZMod 4) = 1 ∨ (u : ZMod 4) = 3 := by decide
  refine (gauss_sum_ratio (ZMod 4) (Ideal.span {2}) (AddChar.zmodChar 4 (ζ := Complex.I) Complex.I_pow_four)
    ((ZMod.χ₄.ringHomComp (Int.castRingHom ℂ)).toUnitHom) 1 1 1 ?_ ?_ ?_ ?_ ?_).1
  · intro y hy y' hy'
    rw [Ideal.mem_span_singleton] at hy hy'
    obtain ⟨k, rfl⟩ := hy
    obtain ⟨k', rfl⟩ := hy'
    revert k k'; decide
  · intro z hz
    have h2 := hz 2 (Ideal.mem_span_singleton_self 2)
    rw [AddChar.zmodChar_apply] at h2
    rw [Ideal.mem_span_singleton]
    have h4 : ∀ z : ZMod 4, z = 0 ∨ z = 1 ∨ z = 2 ∨ z = 3 := by decide
    rcases h4 z with rfl | rfl | rfl | rfl
    · exact ⟨0, by decide⟩
    · exfalso
      have : ((1 : ZMod 4) * 2).val = 2 := by decide
      rw [this, Complex.I_sq] at h2
      norm_num at h2
    · exact ⟨1, by decide⟩
    · exfalso
      have : ((3 : ZMod 4) * 2).val = 2 := by decide
      rw [this, Complex.I_sq] at h2
      norm_num at h2
  · intro u _
    rw [MulChar.coe_toUnitHom, AddChar.zmodChar_apply, MulChar.ringHomComp_apply]
    rcases hu u with h | h <;> rw [h]
    · simp
    · have e1 : ((1 : ZMod 4) * (3 - 1)).val = 2 := by decide
      have e2 : ZMod.χ₄ 3 = -1 := by decide
      rw [e1, e2, Complex.I_sq]; simp
  · intro u _; rfl
  · simp
example : ∑ _w ∈ ({()} : Finset Unit), Real.log 2 * ∑ _ij : Fin 1 × Fin 1, (1 / 2 : ℝ) ≤
    ((1 : ℕ) : ℝ) ^ 2 * (2 * (2 + 8 * ((1 : ℕ) : ℝ)) * 0 + 2 * ((1 : ℕ) : ℝ) * 1 + 6 * 0 +
        4 * ((1 : ℕ) : ℝ) * ∑ _s ∈ (∅ : Finset Empty), (((0 : ℕ)) : ℝ) * Real.log ((0 : ℕ) : ℝ)) :=
  grid_squares_bound Unit Empty 1 1 (fun _ => Real.log 2) (fun _ => 0) (fun _ => 2) (fun _ => 0)
    (fun _ _ => 1 / 2) (fun _ _ => 0) (fun _ _ => 0) (fun _ _ _ => 0) (fun _ _ _ _ => 0) (fun _ => true)
    (fun _ => 2) (fun _ => 1) (fun _ => 0) ∅
    (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ s => s.elim) 0 1 0 {()}
    (fun _ => Real.log_nonneg (by norm_num)) (fun _ => le_rfl) (fun _ => le_rfl) (fun _ s => s.elim)
    (fun _ => Nat.prime_two)
    (by
      intro l F hF
      rcases F.eq_empty_or_nonempty with rfl | ⟨w, hw⟩
      · simpa using Real.log_natCast_nonneg l
      · rw [← hF w hw, sum_const, nsmul_eq_mul]
        have h1 : (F.card : ℝ) ≤ 1 := by exact_mod_cast (Finset.card_le_univ F)
        have h2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
        push_cast
        nlinarith)
    (by simp) (by simp) (by simp) (by simp) (by intro w _ ij; norm_num)
    (by simp) (by simp) (by simp) (by simp)
    (by
      intro P hP
      have := prime_budget_bound (fun _ => 0) 0 (by simp) P hP
      linarith)
    (by simp) (by simp)
end tests
end Formalism.ValuationGridEstimates


