-- Prove2me | solution 1 for ArtinPrimitiveRoots.abs_card_box_mul_sub_mod_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-10T00:58:06.213228+00:00
-- url     : https://prove2.me/submissions/deab8045-fc9a-494c-a45c-2eeb328f50b8

import Theorems.Thm_BlockCycleRotation_two_mul_min_div_le_sin
import Mathlib

section
/-! # L102K: the Kloosterman fourth moment ([21] Lemma 3.3, (3.24))

`K_m(h, k) = ∑_{y ∈ (ℤ/m)ˣ} e((h y + k y⁻¹)/m)`. Orthogonality gives
`∑_{h,k} |K_m(h,k)|⁴ = m² T_m`, where `T_m` counts unit quadruples with equal sums and equal
inverse sums, and `T_m ≤ 2 τ₃(m) m²`. -/

namespace ArtinPrimitiveRoots.L102K

open Finset

noncomputable section

/-- The Kloosterman sum `K_m(h,k) = ∑_{y ∈ (ℤ/m)ˣ} e((h y + k y⁻¹)/m)`. -/
def kloosterman (m : ℕ) [NeZero m] (h k : ZMod m) : ℂ :=
  ∑ y : (ZMod m)ˣ, ZMod.stdAddChar (h * (y : ZMod m) + k * ((y⁻¹ : (ZMod m)ˣ) : ZMod m))

/-- `T_m`: the number of unit quadruples `(y₁, y₂, z₁, z₂)` with `y₁ + y₂ = z₁ + z₂` and
`y₁⁻¹ + y₂⁻¹ = z₁⁻¹ + z₂⁻¹`. -/
def kloostermanT (m : ℕ) [NeZero m] : ℕ :=
  #{q : (ZMod m)ˣ × (ZMod m)ˣ × (ZMod m)ˣ × (ZMod m)ˣ |
    (q.1 : ZMod m) + q.2.1 = q.2.2.1 + q.2.2.2 ∧
    ((q.1⁻¹ : (ZMod m)ˣ) : ZMod m) + ((q.2.1⁻¹ : (ZMod m)ˣ) : ZMod m) =
      ((q.2.2.1⁻¹ : (ZMod m)ˣ) : ZMod m) + ((q.2.2.2⁻¹ : (ZMod m)ˣ) : ZMod m)}

/-- `τ₃(m)`, the number of ordered factorizations `m = d₁ d₂ d₃`, counted as the pairs of
divisors `(d₁, d₂)` with `d₁ d₂ ∣ m`. -/
def tau3 (m : ℕ) : ℕ := #{d ∈ m.divisors ×ˢ m.divisors | d.1 * d.2 ∣ m}

lemma conj_kloosterman (m : ℕ) [NeZero m] (h k : ZMod m) :
    (starRingEnd ℂ) (kloosterman m h k) =
      ∑ y : (ZMod m)ˣ, ZMod.stdAddChar (-(h * (y : ZMod m) + k * ((y⁻¹ : (ZMod m)ˣ) : ZMod m))) := by
  rw [kloosterman, map_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [AddChar.map_neg_eq_conj]

/-- Orthogonality in one variable. -/
lemma sum_stdAddChar_mul (m : ℕ) [NeZero m] (a : ZMod m) :
    ∑ h : ZMod m, (ZMod.stdAddChar (h * a) : ℂ) = if a = 0 then (m : ℂ) else 0 := by
  rw [AddChar.sum_mulShift a (ZMod.isPrimitive_stdAddChar m), ZMod.card]
  push_cast; rfl

lemma sum_four {ι : Type*} [Fintype ι] (f g : ι → ℂ) :
    (∑ i, f i) * (∑ i, f i) * ((∑ i, g i) * (∑ i, g i)) =
      ∑ q : ι × ι × ι × ι, f q.1 * f q.2.1 * (g q.2.2.1 * g q.2.2.2) := by
  rw [Finset.sum_mul_sum, Finset.sum_mul_sum, Finset.sum_mul]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  simp only [Fintype.sum_prod_type]

/-- **The fourth moment identity** `∑_{h,k} |K_m(h,k)|⁴ = m² T_m`. -/
theorem sum_norm_kloosterman_pow_four (m : ℕ) [NeZero m] :
    ∑ h : ZMod m, ∑ k : ZMod m, ‖kloosterman m h k‖ ^ 4 = (m : ℝ) ^ 2 * kloostermanT m := by
  classical
  set U := (ZMod m)ˣ
  let A : U × U × U × U → ZMod m := fun q =>
    (q.1 : ZMod m) + q.2.1 - q.2.2.1 - q.2.2.2
  let B : U × U × U × U → ZMod m := fun q =>
    ((q.1⁻¹ : U) : ZMod m) + ((q.2.1⁻¹ : U) : ZMod m) - ((q.2.2.1⁻¹ : U) : ZMod m) -
      ((q.2.2.2⁻¹ : U) : ZMod m)
  have hK : ∀ h k : ZMod m, ((‖kloosterman m h k‖ ^ 4 : ℝ) : ℂ) =
      ∑ q : U × U × U × U, ZMod.stdAddChar (h * A q) * ZMod.stdAddChar (k * B q) := by
    intro h k
    have h2 : ((‖kloosterman m h k‖ ^ 2 : ℝ) : ℂ) =
        kloosterman m h k * (starRingEnd ℂ) (kloosterman m h k) := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    have h4 : ((‖kloosterman m h k‖ ^ 4 : ℝ) : ℂ) =
        (kloosterman m h k * kloosterman m h k) *
          ((starRingEnd ℂ) (kloosterman m h k) * (starRingEnd ℂ) (kloosterman m h k)) := by
      have : ‖kloosterman m h k‖ ^ 4 = (‖kloosterman m h k‖ ^ 2) ^ 2 := by ring
      rw [this, Complex.ofReal_pow, h2]; ring
    rw [h4, conj_kloosterman, kloosterman, sum_four]
    refine Finset.sum_congr rfl fun q _ => ?_
    simp only [← AddChar.map_add_eq_mul, A, B]
    congr 1
    ring
  have hsum : ((∑ h : ZMod m, ∑ k : ZMod m, ‖kloosterman m h k‖ ^ 4 : ℝ) : ℂ) =
      ((m : ℝ) ^ 2 * kloostermanT m : ℝ) := by
    simp_rw [Complex.ofReal_sum, hK]
    have hswap : ∑ h : ZMod m, ∑ k : ZMod m, ∑ q : U × U × U × U,
        ZMod.stdAddChar (h * A q) * ZMod.stdAddChar (k * B q) =
        ∑ q : U × U × U × U, (∑ h : ZMod m, ZMod.stdAddChar (h * A q)) *
          (∑ k : ZMod m, ZMod.stdAddChar (k * B q)) := by
      simp_rw [Finset.sum_mul_sum]
      exact (Finset.sum_congr rfl fun h _ => Finset.sum_comm).trans Finset.sum_comm
    rw [hswap]
    simp_rw [sum_stdAddChar_mul]
    rw [kloostermanT, Finset.card_filter, Nat.cast_sum, Finset.mul_sum]
    push_cast
    refine Finset.sum_congr rfl fun q _ => ?_
    have hA : A q = 0 ↔ (q.1 : ZMod m) + q.2.1 = q.2.2.1 + q.2.2.2 := by
      simp only [A, sub_sub, sub_eq_zero]
    have hB : B q = 0 ↔ ((q.1⁻¹ : U) : ZMod m) + ((q.2.1⁻¹ : U) : ZMod m) =
        ((q.2.2.1⁻¹ : U) : ZMod m) + ((q.2.2.2⁻¹ : U) : ZMod m) := by
      simp only [B, sub_sub, sub_eq_zero]
    by_cases h1 : A q = 0 <;> by_cases h2 : B q = 0 <;>
      simp [h1, h2, hA.symm, hB.symm, sq]
  exact_mod_cast hsum

/-- With `a a' = b b' = c c' = d d' = 1`, `a + b = c + d` and `a' + b' = c' + d'` force
`(a + b)(c − a)(c − b) = 0`. -/
lemma key_relation {R : Type*} [CommRing R] (a b c d a' b' c' d' : R) (ha : a * a' = 1)
    (hb : b * b' = 1) (hc : c * c' = 1) (hd : d * d' = 1) (e1 : a + b = c + d)
    (e2 : a' + b' = c' + d') : (a + b) * (c - a) * (c - b) = 0 := by
  linear_combination (a * b - (a + b) * c) * e1 - a * b * c * d * e2 + b * c * d * ha +
    a * c * d * hb - a * b * d * hc - a * b * c * hd

/-- `T_m` is at most the number of residue triples with `(y₁+y₂)(z₁−y₁)(z₁−y₂) = 0`. -/
lemma kloostermanT_le_card_triples (m : ℕ) [NeZero m] :
    kloostermanT m ≤
      #{t : ZMod m × ZMod m × ZMod m | (t.1 + t.2.1) * (t.2.2 - t.1) * (t.2.2 - t.2.1) = 0} := by
  classical
  rw [kloostermanT]
  refine Finset.card_le_card_of_injOn
    (fun q => ((q.1 : ZMod m), (q.2.1 : ZMod m), (q.2.2.1 : ZMod m))) ?_ ?_
  · intro q hq
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hq ⊢
    exact key_relation _ _ _ _ _ _ _ _ (Units.mul_inv _) (Units.mul_inv _) (Units.mul_inv _)
      (Units.mul_inv _) hq.1 hq.2
  · intro q hq q' hq' heq
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hq hq'
    simp only [Prod.mk.injEq] at heq
    obtain ⟨h1, h2, h3⟩ := heq
    have h4 : (q.2.2.2 : ZMod m) = q'.2.2.2 := by
      have e := hq.1
      have e' := hq'.1
      rw [h1, h2, h3] at e
      linear_combination e' - e
    exact Prod.ext (Units.ext h1) (Prod.ext (Units.ext h2) (Prod.ext (Units.ext h3) (Units.ext h4)))

/-- At most two residues `w` have `2 w = c`. -/
lemma card_two_mul_eq_le (m : ℕ) [NeZero m] (c : ZMod m) : #{w : ZMod m | 2 * w = c} ≤ 2 := by
  classical
  by_cases hne : ∃ w₀ : ZMod m, 2 * w₀ = c
  · obtain ⟨w₀, hw₀⟩ := hne
    calc #{w : ZMod m | 2 * w = c} ≤ #({0, m / 2} : Finset ℕ) := by
          refine Finset.card_le_card_of_injOn (fun w => (w - w₀).val) ?_ ?_
          · intro w hw
            simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hw
            have h0 : ((2 * (w - w₀).val : ℕ) : ZMod m) = 0 := by
              push_cast
              rw [ZMod.natCast_zmod_val]
              linear_combination hw - hw₀
            rw [ZMod.natCast_eq_zero_iff] at h0
            obtain ⟨j, hj⟩ := h0
            have hlt := ZMod.val_lt (w - w₀)
            have hm : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
            have hj2 : j < 2 := by
              by_contra hcon
              push Not at hcon
              have : m * 2 ≤ m * j := Nat.mul_le_mul_left m hcon
              omega
            simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
              Set.mem_singleton_iff]
            interval_cases j
            · left; omega
            · right; omega
          · intro w hw w' hw' heq
            have := ZMod.val_injective m heq
            simpa using this
      _ ≤ 2 := Finset.card_le_two
  · push Not at hne
    have : #{w : ZMod m | 2 * w = c} = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro w _
      exact hne w
    omega

/-- The linear change `(y₁, y₂, z₁) ↦ (y₁ + y₂, z₁ − y₁, z₁ − y₂)` has fibres of size `≤ 2`. -/
lemma card_triples_le (m : ℕ) [NeZero m] :
    #{t : ZMod m × ZMod m × ZMod m | (t.1 + t.2.1) * (t.2.2 - t.1) * (t.2.2 - t.2.1) = 0} ≤
      2 * #{t : ZMod m × ZMod m × ZMod m | t.1 * t.2.1 * t.2.2 = 0} := by
  classical
  refine Finset.card_le_mul_card_image_of_maps_to
    (f := fun t : ZMod m × ZMod m × ZMod m => (t.1 + t.2.1, t.2.2 - t.1, t.2.2 - t.2.1)) ?_ 2 ?_
  · intro t ht
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
    exact ht
  · intro b _
    calc #{a ∈ ({t : ZMod m × ZMod m × ZMod m |
            (t.1 + t.2.1) * (t.2.2 - t.1) * (t.2.2 - t.2.1) = 0} : Finset _) |
            (a.1 + a.2.1, a.2.2 - a.1, a.2.2 - a.2.1) = b}
        ≤ #{w : ZMod m | 2 * w = b.1 - b.2.1 + b.2.2} := by
          refine Finset.card_le_card_of_injOn (fun a => a.1) ?_ ?_
          · intro a ha
            simp only [Finset.coe_filter, Finset.mem_filter, Finset.mem_univ, true_and,
              Set.mem_ofPred_eq] at ha ⊢
            rw [← ha.2]
            ring
          · intro a ha a' ha' heq
            simp only [Finset.coe_filter, Finset.mem_filter, Finset.mem_univ, true_and,
              Set.mem_ofPred_eq] at ha ha'
            have e := ha.2.trans ha'.2.symm
            simp only [Prod.mk.injEq] at e heq
            obtain ⟨e1, e2, _⟩ := e
            refine Prod.ext heq (Prod.ext ?_ ?_)
            · linear_combination e1 - heq
            · linear_combination e2 + heq
      _ ≤ 2 := card_two_mul_eq_le m _

/-- `#{x ∈ ℤ/m : d ∣ x.val} = m/d` for `d ∣ m`. -/
lemma card_dvd_val (m d : ℕ) [NeZero m] (hd0 : 0 < d) (hd : d ∣ m) :
    #{x : ZMod m | d ∣ x.val} = m / d := by
  classical
  have him : (Finset.univ.filter fun x : ZMod m => d ∣ x.val).image ZMod.val =
      (Finset.range (m / d)).image (· * d) := by
    ext v
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_range]
    constructor
    · rintro ⟨x, ⟨j, hj⟩, rfl⟩
      refine ⟨j, ?_, by rw [hj, mul_comm]⟩
      have hlt := ZMod.val_lt x
      rw [hj] at hlt
      rw [Nat.lt_div_iff_mul_lt' hd]
      linarith [mul_comm d j]
    · rintro ⟨j, hj, rfl⟩
      have hlt : j * d < m := by
        rw [Nat.lt_div_iff_mul_lt' hd] at hj; rw [mul_comm]; exact hj
      refine ⟨(j * d : ℕ), ?_, ?_⟩
      · rw [ZMod.val_natCast, Nat.mod_eq_of_lt hlt]; exact Dvd.intro_left j rfl
      · rw [ZMod.val_natCast, Nat.mod_eq_of_lt hlt]
  have h1 := congrArg Finset.card him
  rw [Finset.card_image_of_injective _ (ZMod.val_injective m),
    Finset.card_image_of_injective _ (fun a b h => Nat.eq_of_mul_eq_mul_right hd0 h),
    Finset.card_range] at h1
  exact h1

/-- If `m ∣ abc`, then with `d₁ = (a, m)` and `d₂ = (b, m/d₁)` also `m/(d₁d₂) ∣ c`. -/
lemma dvd_of_dvd_mul_three {m a b c : ℕ} (hm : 0 < m) (h : m ∣ a * b * c) :
    m / (Nat.gcd a m * Nat.gcd b (m / Nat.gcd a m)) ∣ c := by
  set d₁ := Nat.gcd a m with hd₁
  have hd₁0 : 0 < d₁ := Nat.gcd_pos_of_pos_right _ hm
  set n₁ := m / d₁ with hn₁
  have hmn : m = d₁ * n₁ := (Nat.mul_div_cancel' (Nat.gcd_dvd_right a m)).symm
  obtain ⟨a₁, ha₁⟩ : d₁ ∣ a := Nat.gcd_dvd_left a m
  have hcop : Nat.Coprime n₁ a₁ := by
    have := Nat.coprime_div_gcd_div_gcd (m := a) (n := m) hd₁0
    rw [← hd₁, ← hn₁] at this
    have ha' : a / d₁ = a₁ := by rw [ha₁, Nat.mul_div_cancel_left _ hd₁0]
    rw [ha'] at this
    exact this.symm
  have h1 : n₁ ∣ a₁ * (b * c) := by
    have : d₁ * n₁ ∣ d₁ * (a₁ * (b * c)) := by
      rw [← hmn]; rw [ha₁] at h; simpa [mul_assoc] using h
    exact Nat.dvd_of_mul_dvd_mul_left hd₁0 this
  have h2 : n₁ ∣ b * c := hcop.dvd_of_dvd_mul_left h1
  have hn₁0 : 0 < n₁ := by
    rcases Nat.eq_zero_or_pos n₁ with h0 | h0
    · rw [h0, mul_zero] at hmn; omega
    · exact h0
  set d₂ := Nat.gcd b n₁ with hd₂
  have hd₂0 : 0 < d₂ := Nat.gcd_pos_of_pos_right _ hn₁0
  set n₂ := n₁ / d₂ with hn₂
  have hnn : n₁ = d₂ * n₂ := (Nat.mul_div_cancel' (Nat.gcd_dvd_right b n₁)).symm
  obtain ⟨b₁, hb₁⟩ : d₂ ∣ b := Nat.gcd_dvd_left b n₁
  have hcop2 : Nat.Coprime n₂ b₁ := by
    have := Nat.coprime_div_gcd_div_gcd (m := b) (n := n₁) hd₂0
    rw [← hd₂, ← hn₂] at this
    have hb' : b / d₂ = b₁ := by rw [hb₁, Nat.mul_div_cancel_left _ hd₂0]
    rw [hb'] at this
    exact this.symm
  have h3 : n₂ ∣ b₁ * c := by
    have : d₂ * n₂ ∣ d₂ * (b₁ * c) := by
      rw [← hnn, ← mul_assoc, ← hb₁]; exact h2
    exact Nat.dvd_of_mul_dvd_mul_left hd₂0 this
  have h4 : n₂ ∣ c := hcop2.dvd_of_dvd_mul_left h3
  have : m / (d₁ * d₂) = n₂ := by rw [hn₂, hn₁, Nat.div_div_eq_div_mul]
  rw [this]; exact h4

/-- `#{(x, y, z) ∈ (ℤ/m)³ : xyz = 0} ≤ τ₃(m) m²`. -/
lemma card_mul_eq_zero_le (m : ℕ) [NeZero m] :
    #{t : ZMod m × ZMod m × ZMod m | t.1 * t.2.1 * t.2.2 = 0} ≤ tau3 m * m ^ 2 := by
  classical
  have hm : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  set D := (m.divisors ×ˢ m.divisors).filter (fun d => d.1 * d.2 ∣ m) with hD
  let box : ℕ × ℕ → Finset (ZMod m × ZMod m × ZMod m) := fun d =>
    (Finset.univ.filter fun x : ZMod m => d.1 ∣ x.val) ×ˢ
      ((Finset.univ.filter fun y : ZMod m => d.2 ∣ y.val) ×ˢ
        (Finset.univ.filter fun z : ZMod m => m / (d.1 * d.2) ∣ z.val))
  have hsub : (Finset.univ.filter fun t : ZMod m × ZMod m × ZMod m => t.1 * t.2.1 * t.2.2 = 0) ⊆
      D.biUnion box := by
    intro t ht
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
    have hdiv : m ∣ t.1.val * t.2.1.val * t.2.2.val := by
      rw [← ZMod.natCast_eq_zero_iff]
      push_cast
      simp only [ZMod.natCast_zmod_val]
      exact ht
    set d₁ := Nat.gcd t.1.val m
    set d₂ := Nat.gcd t.2.1.val (m / d₁)
    have hd₁m : d₁ ∣ m := Nat.gcd_dvd_right _ _
    have hd₂m' : d₂ ∣ m / d₁ := Nat.gcd_dvd_right _ _
    have hd₁₂ : d₁ * d₂ ∣ m := Nat.mul_dvd_of_dvd_div hd₁m hd₂m'
    rw [Finset.mem_biUnion]
    refine ⟨(d₁, d₂), ?_, ?_⟩
    · rw [hD, Finset.mem_filter, Finset.mem_product, Nat.mem_divisors, Nat.mem_divisors]
      exact ⟨⟨⟨hd₁m, hm.ne'⟩, ⟨hd₂m'.trans (Nat.div_dvd_of_dvd hd₁m), hm.ne'⟩⟩, hd₁₂⟩
    · simp only [box, Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨Nat.gcd_dvd_left _ _, Nat.gcd_dvd_left _ _, dvd_of_dvd_mul_three hm hdiv⟩
  have hbox : ∀ d ∈ D, #(box d) = m ^ 2 := by
    intro d hd
    rw [hD, Finset.mem_filter, Finset.mem_product, Nat.mem_divisors, Nat.mem_divisors] at hd
    obtain ⟨⟨⟨h1, _⟩, ⟨h2, _⟩⟩, h12⟩ := hd
    have hd1 : 0 < d.1 := Nat.pos_of_dvd_of_pos h1 hm
    have hd2 : 0 < d.2 := Nat.pos_of_dvd_of_pos h2 hm
    have h3 : 0 < m / (d.1 * d.2) := Nat.div_pos (Nat.le_of_dvd hm h12) (Nat.mul_pos hd1 hd2)
    simp only [box, Finset.card_product]
    rw [card_dvd_val m _ hd1 h1, card_dvd_val m _ hd2 h2,
      card_dvd_val m _ h3 (Nat.div_dvd_of_dvd h12), Nat.div_div_self h12 hm.ne']
    calc m / d.1 * (m / d.2 * (d.1 * d.2)) = (m / d.1 * d.1) * (m / d.2 * d.2) := by ring
      _ = m ^ 2 := by rw [Nat.div_mul_cancel h1, Nat.div_mul_cancel h2, sq]
  calc #{t : ZMod m × ZMod m × ZMod m | t.1 * t.2.1 * t.2.2 = 0} ≤ #(D.biUnion box) :=
        Finset.card_le_card hsub
    _ ≤ ∑ d ∈ D, #(box d) := Finset.card_biUnion_le
    _ = ∑ d ∈ D, m ^ 2 := Finset.sum_congr rfl hbox
    _ = tau3 m * m ^ 2 := by rw [Finset.sum_const, smul_eq_mul, tau3]

/-- **`T_m ≤ 2 τ₃(m) m²`** ([21] proof of Lemma 3.3). -/
theorem kloostermanT_le (m : ℕ) [NeZero m] : kloostermanT m ≤ 2 * tau3 m * m ^ 2 := by
  calc kloostermanT m ≤ _ := kloostermanT_le_card_triples m
    _ ≤ 2 * _ := card_triples_le m
    _ ≤ 2 * (tau3 m * m ^ 2) := Nat.mul_le_mul_left 2 (card_mul_eq_zero_le m)
    _ = 2 * tau3 m * m ^ 2 := by ring

/-- **The Kloosterman fourth moment**: `∑_{h,k} |K_m(h,k)|⁴ ≤ 2 τ₃(m) m⁴`. -/
theorem sum_norm_kloosterman_pow_four_le (m : ℕ) [NeZero m] :
    ∑ h : ZMod m, ∑ k : ZMod m, ‖kloosterman m h k‖ ^ 4 ≤ 2 * tau3 m * (m : ℝ) ^ 4 := by
  rw [sum_norm_kloosterman_pow_four]
  have := kloostermanT_le m
  have h' : (kloostermanT m : ℝ) ≤ 2 * tau3 m * (m : ℝ) ^ 2 := by exact_mod_cast this
  calc (m : ℝ) ^ 2 * kloostermanT m ≤ (m : ℝ) ^ 2 * (2 * tau3 m * (m : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left h' (by positivity)
    _ = 2 * tau3 m * (m : ℝ) ^ 4 := by ring

/-! ### The pointwise bound -/

/-- `K_m` is constant on the orbits `(h, k) ↦ (h s, k s⁻¹)`. -/
lemma kloosterman_mul_unit (m : ℕ) [NeZero m] (h k : ZMod m) (s : (ZMod m)ˣ) :
    kloosterman m (h * s) (k * ((s⁻¹ : (ZMod m)ˣ) : ZMod m)) = kloosterman m h k := by
  rw [kloosterman, kloosterman]
  refine Fintype.sum_equiv (Equiv.mulLeft s) _ _ fun y => ?_
  simp only [Equiv.coe_mulLeft, Units.val_mul, mul_inv_rev]
  congr 1
  ring

/-- If `h t = k t = 0` in `ℤ/m`, then `m/(h, k, m)` divides `t`. -/
lemma div_gcd_dvd_val {m : ℕ} [NeZero m] {h k t : ZMod m} (hh : h * t = 0) (hk : k * t = 0) :
    m / Nat.gcd (Nat.gcd h.val k.val) m ∣ t.val := by
  have hm : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  have h1 : m ∣ h.val * t.val := by
    rw [← ZMod.natCast_eq_zero_iff]; push_cast; simp only [ZMod.natCast_zmod_val]; exact hh
  have h2 : m ∣ k.val * t.val := by
    rw [← ZMod.natCast_eq_zero_iff]; push_cast; simp only [ZMod.natCast_zmod_val]; exact hk
  have h3 : m ∣ Nat.gcd h.val k.val * t.val := by
    rw [← Nat.gcd_mul_right]; exact Nat.dvd_gcd h1 h2
  have h4 : m ∣ Nat.gcd (Nat.gcd h.val k.val) m * t.val := by
    rw [← Nat.gcd_mul_right]; exact Nat.dvd_gcd h3 (Dvd.intro t.val rfl)
  set g := Nat.gcd (Nat.gcd h.val k.val) m
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_right _ hm
  have h5 : g * (m / g) ∣ g * t.val := by
    rw [Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)]; exact h4
  exact Nat.dvd_of_mul_dvd_mul_left hg0 h5

/-- **The orbit bound**: `|K_m(h,k)|⁴ φ(m/g) ≤ ∑_{h',k'} |K_m(h',k')|⁴`, `g = (h, k, m)`. -/
lemma norm_kloosterman_pow_four_mul_totient_le (m : ℕ) [NeZero m] (h k : ZMod m) :
    ‖kloosterman m h k‖ ^ 4 * (m / Nat.gcd (Nat.gcd h.val k.val) m).totient ≤
      ∑ h' : ZMod m, ∑ k' : ZMod m, ‖kloosterman m h' k'‖ ^ 4 := by
  classical
  have hm : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  set g := Nat.gcd (Nat.gcd h.val k.val) m with hg
  set n := m / g with hn
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_right _ hm
  have hnm : n ∣ m := Nat.div_dvd_of_dvd (Nat.gcd_dvd_right _ _)
  have hn0 : 0 < n := Nat.div_pos (Nat.le_of_dvd hm (Nat.gcd_dvd_right _ _)) hg0
  have : NeZero n := ⟨hn0.ne'⟩
  set lift := Function.surjInv (ZMod.unitsMap_surjective (m := m) hnm) with hlift
  have hlift_spec : ∀ t, ZMod.unitsMap hnm (lift t) = t :=
    Function.surjInv_eq (ZMod.unitsMap_surjective (m := m) hnm)
  let F : (ZMod n)ˣ → ZMod m × ZMod m := fun t =>
    (h * (lift t : ZMod m), k * (((lift t)⁻¹ : (ZMod m)ˣ) : ZMod m))
  have hF : Function.Injective F := by
    intro t t' heq
    simp only [F, Prod.mk.injEq] at heq
    obtain ⟨e1, e2⟩ := heq
    set s := lift t
    set s' := lift t'
    have hh : h * ((s : ZMod m) - s') = 0 := by rw [mul_sub, e1, sub_self]
    have hk : k * ((s : ZMod m) - s') = 0 := by
      have : k * ((s : ZMod m) - s') =
          (k * (((s'⁻¹ : (ZMod m)ˣ) : ZMod m))) * (s * s') -
            (k * (((s⁻¹ : (ZMod m)ˣ) : ZMod m))) * (s * s') := by
        have hs : (s : ZMod m) * ((s⁻¹ : (ZMod m)ˣ) : ZMod m) = 1 := Units.mul_inv s
        have hs' : (s' : ZMod m) * ((s'⁻¹ : (ZMod m)ˣ) : ZMod m) = 1 := Units.mul_inv s'
        linear_combination (k * (s' : ZMod m)) * hs - (k * (s : ZMod m)) * hs'
      rw [this, e2, sub_self]
    have hd := div_gcd_dvd_val hh hk
    rw [← hg, ← hn] at hd
    rw [← hlift_spec t, ← hlift_spec t']
    apply Units.ext
    rw [ZMod.unitsMap_val, ZMod.unitsMap_val]
    rw [← sub_eq_zero, ← ZMod.cast_sub hnm,
      ← ZMod.natCast_zmod_val ((s : ZMod m) - (s' : ZMod m)),
      ZMod.cast_natCast hnm, ZMod.natCast_eq_zero_iff]
    exact hd
  have hconst : ∀ t, ‖kloosterman m (F t).1 (F t).2‖ ^ 4 = ‖kloosterman m h k‖ ^ 4 := by
    intro t
    simp only [F]
    rw [kloosterman_mul_unit]
  calc ‖kloosterman m h k‖ ^ 4 * n.totient
      = ∑ t : (ZMod n)ˣ, ‖kloosterman m (F t).1 (F t).2‖ ^ 4 := by
        simp only [hconst, Finset.sum_const, Finset.card_univ, ZMod.card_units_eq_totient,
          nsmul_eq_mul]
        ring
    _ = ∑ p ∈ Finset.univ.image F, ‖kloosterman m p.1 p.2‖ ^ 4 := by
        rw [Finset.sum_image fun a _ b _ hab => hF hab]
    _ ≤ ∑ p : ZMod m × ZMod m, ‖kloosterman m p.1 p.2‖ ^ 4 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => by positivity
    _ = ∑ h' : ZMod m, ∑ k' : ZMod m, ‖kloosterman m h' k'‖ ^ 4 := Fintype.sum_prod_type _

/-- `n ≤ φ(n) d(n)`. -/
lemma le_totient_mul_card_divisors (n : ℕ) (hn : n ≠ 0) :
    n ≤ n.totient * n.divisors.card := by
  rw [Nat.totient_eq_prod_factorization hn, Nat.card_divisors hn, Finsupp.prod,
    Nat.support_factorization, ← Finset.prod_mul_distrib]
  conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hn, Finsupp.prod, Nat.support_factorization]
  refine Finset.prod_le_prod' fun p hp => ?_
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have he : 1 ≤ n.factorization p :=
    (Nat.Prime.factorization_pos_of_dvd hpp hn (Nat.dvd_of_mem_primeFactors hp))
  obtain ⟨k, hk⟩ : ∃ k, n.factorization p = k + 1 := ⟨n.factorization p - 1, by omega⟩
  rw [hk]
  have hp2 := hpp.two_le
  simp only [Nat.add_sub_cancel, pow_succ]
  rw [mul_assoc]
  refine Nat.mul_le_mul_left _ ?_
  have : p ≤ (p - 1) * 2 := by omega
  calc p ≤ (p - 1) * 2 := this
    _ ≤ (p - 1) * (k + 1 + 1) := Nat.mul_le_mul_left _ (by omega)

lemma tau3_le (m : ℕ) : tau3 m ≤ m.divisors.card ^ 2 := by
  rw [tau3, sq, ← Finset.card_product]
  exact Finset.card_filter_le _ _

/-- **The pointwise Kloosterman bound** ([21] (3.24), explicit form):
`|K_m(h,k)|⁴ ≤ 2 d(m)³ m³ (h, k, m)`. -/
theorem norm_kloosterman_pow_four_le (m : ℕ) [NeZero m] (h k : ZMod m) :
    ‖kloosterman m h k‖ ^ 4 ≤
      2 * (m.divisors.card : ℝ) ^ 3 * (m : ℝ) ^ 3 * Nat.gcd (Nat.gcd h.val k.val) m := by
  have hm : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  set g := Nat.gcd (Nat.gcd h.val k.val) m with hg
  set n := m / g with hn
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_right _ hm
  have hnm : n ∣ m := Nat.div_dvd_of_dvd (Nat.gcd_dvd_right _ _)
  have hn0 : 0 < n := Nat.div_pos (Nat.le_of_dvd hm (Nat.gcd_dvd_right _ _)) hg0
  have hmng : (m : ℝ) = n * g := by
    rw [hn]; exact_mod_cast (Nat.div_mul_cancel (Nat.gcd_dvd_right _ _)).symm
  have h1 := (norm_kloosterman_pow_four_mul_totient_le m h k).trans
    (sum_norm_kloosterman_pow_four_le m)
  rw [← hg, ← hn] at h1
  have h2 : (n : ℝ) ≤ n.totient * n.divisors.card := by
    exact_mod_cast le_totient_mul_card_divisors n hn0.ne'
  have h3 : (n.divisors.card : ℝ) ≤ m.divisors.card := by
    exact_mod_cast Finset.card_le_card (Nat.divisors_subset_of_dvd hm.ne' hnm)
  have h4 : (tau3 m : ℝ) ≤ (m.divisors.card : ℝ) ^ 2 := by exact_mod_cast tau3_le m
  set K := ‖kloosterman m h k‖ ^ 4 with hK
  have hK0 : 0 ≤ K := by positivity
  set D := (m.divisors.card : ℝ)
  have hD0 : 0 ≤ D := by positivity
  -- `K n ≤ K φ(n) d(n) ≤ 2 τ₃ m⁴ D ≤ 2 D³ m⁴`
  have h5 : K * n ≤ 2 * D ^ 3 * (m : ℝ) ^ 4 := by
    calc K * n ≤ K * (n.totient * n.divisors.card) := mul_le_mul_of_nonneg_left h2 hK0
      _ = (K * n.totient) * n.divisors.card := by ring
      _ ≤ (2 * tau3 m * (m : ℝ) ^ 4) * D :=
          mul_le_mul h1 h3 (by positivity) (by positivity)
      _ ≤ (2 * D ^ 2 * (m : ℝ) ^ 4) * D := by gcongr
      _ = 2 * D ^ 3 * (m : ℝ) ^ 4 := by ring
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn0
  rw [hmng] at h5 ⊢
  have : K * n ≤ (2 * D ^ 3 * (n * g) ^ 3 * g) * n := by nlinarith
  exact le_of_mul_le_mul_right this hnpos

end

end ArtinPrimitiveRoots.L102K
end

section
/-! # L102K: completion of a box count in `(ℤ/m)²`

For a finite `Λ ⊆ (ℤ/m)²` and finite sets of integers `I, J`,
`#{(t, s) ∈ I × J : (t, s) mod m ∈ Λ} = m⁻² ∑_{h,k} Î(h) Ĵ(k) Λ̂(h,k)`, with
`Î(h) = ∑_{t ∈ I} e(ht/m)` and `Λ̂(h,k) = ∑_{(x,y) ∈ Λ} e(−(hx + ky)/m)`. For an integer
interval, `|Î(h)| ≤ m/(2 min(h, m − h))` for `h ≠ 0`. This replaces the smoothed-box
discrepancy (3.27) of [21]. -/

namespace ArtinPrimitiveRoots.L102K

open Finset Real

noncomputable section

/-- `Î(h) = ∑_{t ∈ I} e(ht/m)`. -/
def intervalSum (m : ℕ) [NeZero m] (I : Finset ℤ) (h : ZMod m) : ℂ :=
  ∑ t ∈ I, ZMod.stdAddChar (h * (t : ZMod m))

/-- `Λ̂(h,k) = ∑_{(x,y) ∈ Λ} e(−(hx + ky)/m)`. -/
def setFourier {m : ℕ} [NeZero m] (Λ : Finset (ZMod m × ZMod m)) (h k : ZMod m) : ℂ :=
  ∑ p ∈ Λ, ZMod.stdAddChar (-(h * p.1 + k * p.2))

/-- The weight `m / (2 min(h, m − h))` (and `0` at `h = 0`). -/
def wt (m : ℕ) [NeZero m] (h : ZMod m) : ℝ :=
  if h = 0 then 0 else (m : ℝ) / (2 * ((min h.val (m - h.val) : ℕ) : ℝ))

lemma wt_nonneg (m : ℕ) [NeZero m] (h : ZMod m) : 0 ≤ wt m h := by
  unfold wt; split_ifs <;> positivity

/-! ### The geometric sum -/

/-- Jordan's inequality at a root of unity: `2 min(a, m−a)/m ≤ sin(πa/m)` for `0 < a < m`. -/
lemma two_mul_min_div_le_sin {a m : ℕ} (h0 : 0 < a) (ham : a < m) :
    2 * ((min a (m - a) : ℕ) : ℝ) / (m : ℝ) ≤ Real.sin (π * a / m) :=
  by
  first
    | exact BlockCycleRotation.two_mul_min_div_le_sin
    | exact BlockCycleRotation.two_mul_min_div_le_sin ..
    | (apply BlockCycleRotation.two_mul_min_div_le_sin <;> first | assumption | infer_instance)
    | simpa using BlockCycleRotation.two_mul_min_div_le_sin

lemma norm_stdAddChar_sub_one_ge (m : ℕ) [NeZero m] (h : ZMod m) (hh : h ≠ 0) :
    4 * ((min h.val (m - h.val) : ℕ) : ℝ) / m ≤ ‖(ZMod.stdAddChar h : ℂ) - 1‖ := by
  rw [ZMod.stdAddChar_apply, ZMod.toCircle_apply]
  have hrw : 2 * (π : ℂ) * Complex.I * (h.val : ℂ) / (m : ℂ) =
      Complex.I * ((2 * π * h.val / m : ℝ) : ℂ) := by push_cast; ring
  rw [hrw, Complex.norm_exp_I_mul_ofReal_sub_one]
  have hval : 0 < h.val := (ZMod.val_pos).mpr hh
  have hlt := ZMod.val_lt h
  have hs := two_mul_min_div_le_sin hval hlt
  have hhalf : (2 * π * h.val / m : ℝ) / 2 = π * h.val / m := by ring
  rw [hhalf, Real.norm_eq_abs, abs_mul, abs_two]
  have hsin : 0 ≤ Real.sin (π * h.val / m) := le_trans (by positivity) hs
  rw [abs_of_nonneg hsin]
  have : 4 * ((min h.val (m - h.val) : ℕ) : ℝ) / m =
      2 * (2 * ((min h.val (m - h.val) : ℕ) : ℝ) / m) := by ring
  rw [this]
  linarith

lemma sum_Ico_int_eq (A B : ℤ) (f : ℤ → ℂ) :
    ∑ t ∈ Finset.Ico A B, f t = ∑ j ∈ Finset.range (B - A).toNat, f (A + j) := by
  refine Finset.sum_nbij' (fun t => (t - A).toNat) (fun j => A + j) ?_ ?_ ?_ ?_ ?_
  · intro t ht
    simp only [Finset.mem_Ico, Finset.mem_range] at ht ⊢
    omega
  · intro j hj
    simp only [Finset.mem_Ico, Finset.mem_range] at hj ⊢
    omega
  · intro t ht
    simp only [Finset.mem_Ico] at ht
    omega
  · intro j _
    simp
  · intro t ht
    simp only [Finset.mem_Ico] at ht
    congr 1
    omega

/-- **The geometric sum**: `|∑_{A ≤ t < B} e(ht/m)| ≤ m/(2 min(h, m − h))` for `h ≠ 0`. -/
theorem norm_intervalSum_Ico_le (m : ℕ) [NeZero m] (h : ZMod m) (hh : h ≠ 0) (A B : ℤ) :
    ‖intervalSum m (Finset.Ico A B) h‖ ≤ wt m h := by
  rw [wt, if_neg hh, intervalSum]
  set ζ : ℂ := ZMod.stdAddChar h with hζ
  have hζ1 : ‖ζ‖ = 1 := AddChar.norm_apply _ _
  have hζ0 : ζ ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hζ1; exact zero_ne_one hζ1
  have hterm : ∀ t : ℤ, (ZMod.stdAddChar (h * (t : ZMod m)) : ℂ) = ζ ^ t := by
    intro t
    rw [hζ, mul_comm, ← zsmul_eq_mul, AddChar.map_zsmul_eq_zpow]
  simp_rw [hterm]
  rw [sum_Ico_int_eq]
  simp_rw [zpow_add₀ hζ0, zpow_natCast]
  rw [← Finset.mul_sum, norm_mul, norm_zpow, hζ1, one_zpow, one_mul]
  have hne : ζ ≠ 1 := by
    intro h1
    apply hh
    apply ZMod.injective_stdAddChar (N := m)
    rw [AddChar.map_zero_eq_one]
    exact h1
  rw [geom_sum_eq hne, norm_div]
  have hnum : ‖ζ ^ (B - A).toNat - 1‖ ≤ 2 := by
    calc ‖ζ ^ (B - A).toNat - 1‖ ≤ ‖ζ ^ (B - A).toNat‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_pow, hζ1, one_pow, norm_one]; norm_num
  have hden := norm_stdAddChar_sub_one_ge m h hh
  rw [← hζ] at hden
  have hval : 0 < h.val := (ZMod.val_pos).mpr hh
  have hlt := ZMod.val_lt h
  have hmin : (0 : ℝ) < ((min h.val (m - h.val) : ℕ) : ℝ) := by
    have : 0 < min h.val (m - h.val) := lt_min hval (by omega)
    exact_mod_cast this
  have hm : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
  have hdpos : 0 < 4 * ((min h.val (m - h.val) : ℕ) : ℝ) / m := by positivity
  calc ‖ζ ^ (B - A).toNat - 1‖ / ‖ζ - 1‖
      ≤ 2 / (4 * ((min h.val (m - h.val) : ℕ) : ℝ) / m) :=
        div_le_div₀ (by norm_num) hnum hdpos hden
    _ = (m : ℝ) / (2 * ((min h.val (m - h.val) : ℕ) : ℝ)) := by field_simp; ring

/-! ### The weighted sum `∑_{h ≠ 0} wt(h) (h, m)` -/

/-- The harmonic sum over `(0, X]`. -/
lemma harm_le (X : ℕ) : ∑ i ∈ Ioc 0 X, (1 / (i : ℝ)) ≤ 1 + Real.log X := by
  have h := harmonic_le_one_add_log X
  rw [harmonic_eq_sum_Icc] at h
  push_cast at h
  have : Icc 1 X = Ioc 0 X := by ext i; simp; omega
  rw [this] at h
  simpa [one_div] using h

/-- `∑_{0 < j ≤ m} (j, m)/j ≤ d(m)(1 + log m)`. -/
lemma sum_gcd_div_le (m : ℕ) (hm : 0 < m) :
    ∑ j ∈ Ioc 0 m, ((Nat.gcd j m : ℕ) : ℝ) / j ≤ m.divisors.card * (1 + Real.log m) := by
  classical
  have h1 : ∀ j ∈ Ioc 0 m, ((Nat.gcd j m : ℕ) : ℝ) / j ≤
      ∑ d ∈ m.divisors, if d ∣ j then (d : ℝ) / j else 0 := by
    intro j hj
    have hg : Nat.gcd j m ∈ m.divisors :=
      Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right _ _, hm.ne'⟩
    rw [← Finset.add_sum_erase _ _ hg, if_pos (Nat.gcd_dvd_left _ _)]
    have : 0 ≤ ∑ d ∈ m.divisors.erase (Nat.gcd j m), if d ∣ j then (d : ℝ) / j else 0 :=
      Finset.sum_nonneg fun d _ => by split_ifs <;> positivity
    linarith
  have h2 : ∀ d ∈ m.divisors, (∑ j ∈ Ioc 0 m, if d ∣ j then (d : ℝ) / j else 0) =
      ∑ i ∈ Ioc 0 (m / d), (1 / (i : ℝ)) := by
    intro d hd
    have hdm : d ∣ m := Nat.dvd_of_mem_divisors hd
    have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdm hm
    rw [← Finset.sum_filter]
    have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd0.ne'
    refine Finset.sum_nbij' (fun j => j / d) (fun i => d * i) ?_ ?_ ?_ ?_ ?_
    · intro j hj
      simp only [Finset.mem_filter, Finset.mem_Ioc] at hj ⊢
      obtain ⟨⟨hj0, hjm⟩, ⟨i, rfl⟩⟩ := hj
      rw [Nat.mul_div_cancel_left _ hd0]
      refine ⟨Nat.pos_of_mul_pos_left hj0, ?_⟩
      rw [Nat.le_div_iff_mul_le hd0]; linarith [mul_comm d i]
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_Ioc] at hi ⊢
      obtain ⟨hi0, him⟩ := hi
      rw [Nat.le_div_iff_mul_le hd0] at him
      exact ⟨⟨Nat.mul_pos hd0 hi0, by linarith [mul_comm d i]⟩, Dvd.intro i rfl⟩
    · intro j hj
      simp only [Finset.mem_filter, Finset.mem_Ioc] at hj
      exact Nat.mul_div_cancel' hj.2
    · intro i _
      exact Nat.mul_div_cancel_left _ hd0
    · intro j hj
      simp only [Finset.mem_filter, Finset.mem_Ioc] at hj
      obtain ⟨_, ⟨i, rfl⟩⟩ := hj
      rw [Nat.mul_div_cancel_left _ hd0]
      push_cast
      field_simp
  calc ∑ j ∈ Ioc 0 m, ((Nat.gcd j m : ℕ) : ℝ) / j
      ≤ ∑ j ∈ Ioc 0 m, ∑ d ∈ m.divisors, if d ∣ j then (d : ℝ) / j else 0 := sum_le_sum h1
    _ = ∑ d ∈ m.divisors, ∑ j ∈ Ioc 0 m, if d ∣ j then (d : ℝ) / j else 0 := Finset.sum_comm
    _ = ∑ d ∈ m.divisors, ∑ i ∈ Ioc 0 (m / d), (1 / (i : ℝ)) := sum_congr rfl h2
    _ ≤ ∑ d ∈ m.divisors, (1 + Real.log m) := by
        refine sum_le_sum fun d hd => (harm_le _).trans ?_
        have hdm : d ∣ m := Nat.dvd_of_mem_divisors hd
        have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdm hm
        have hq : 0 < m / d := Nat.div_pos (Nat.le_of_dvd hm hdm) hd0
        have : ((m / d : ℕ) : ℝ) ≤ m := by exact_mod_cast Nat.div_le_self m d
        have := Real.log_le_log (by exact_mod_cast hq) this
        linarith
    _ = m.divisors.card * (1 + Real.log m) := by rw [Finset.sum_const, nsmul_eq_mul]

lemma sum_zmod_val (m : ℕ) [NeZero m] (F : ℕ → ℝ) :
    ∑ x : ZMod m, F x.val = ∑ j ∈ range m, F j := by
  refine Finset.sum_bij' (fun x _ => x.val) (fun j _ => (j : ZMod m)) ?_ ?_ ?_ ?_ ?_
  · intro x _; exact Finset.mem_range.mpr (ZMod.val_lt x)
  · intro j _; exact Finset.mem_univ _
  · intro x _; exact ZMod.natCast_zmod_val x
  · intro j hj; rw [ZMod.val_natCast, Nat.mod_eq_of_lt (Finset.mem_range.mp hj)]
  · intro x _; rfl

/-- **The weighted sum**: `∑_h wt(h) (h, m) ≤ m d(m)(1 + log m)`. -/
theorem sum_wt_gcd_le (m : ℕ) [NeZero m] :
    ∑ h : ZMod m, wt m h * Nat.gcd h.val m ≤ m * m.divisors.card * (1 + Real.log m) := by
  classical
  have hm : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  -- `wt(h) ≤ (m/2)(1/h + 1/(−h))`
  let G : ZMod m → ℝ := fun h => if h = 0 then 0 else ((Nat.gcd h.val m : ℕ) : ℝ) / h.val
  have hneg : ∀ h : ZMod m, ((Nat.gcd (-h).val m : ℕ) : ℝ) = Nat.gcd h.val m := by
    intro h
    by_cases hh : h = 0
    · rw [hh, neg_zero]
    · rw [ZMod.neg_val, if_neg hh]
      have hlt := ZMod.val_lt h
      congr 1
      rw [Nat.gcd_comm, Nat.gcd_self_sub_right hlt.le, Nat.gcd_comm]
  have hpt : ∀ h : ZMod m, wt m h * Nat.gcd h.val m ≤ (m / 2) * (G h + G (-h)) := by
    intro h
    by_cases hh : h = 0
    · simp [wt, G, hh]
    · have hnh : -h ≠ 0 := neg_ne_zero.mpr hh
      simp only [wt, G, if_neg hh, if_neg hnh]
      rw [hneg h, ZMod.neg_val, if_neg hh]
      have hval : 0 < h.val := (ZMod.val_pos).mpr hh
      have hlt := ZMod.val_lt h
      have hsub : ((m - h.val : ℕ) : ℝ) = (m : ℝ) - h.val := by rw [Nat.cast_sub hlt.le]
      have ha : (0 : ℝ) < h.val := by exact_mod_cast hval
      have hb : (0 : ℝ) < (m : ℝ) - h.val := by
        have : (h.val : ℝ) < m := by exact_mod_cast hlt
        linarith
      have hg : (0 : ℝ) ≤ ((Nat.gcd h.val m : ℕ) : ℝ) := by positivity
      rw [hsub]
      rcases le_total h.val (m - h.val) with hc | hc
      · rw [min_eq_left hc]
        have : (m : ℝ) / (2 * h.val) * ((Nat.gcd h.val m : ℕ) : ℝ) =
            (m / 2) * (((Nat.gcd h.val m : ℕ) : ℝ) / h.val) := by field_simp
        rw [this]
        have : 0 ≤ ((Nat.gcd h.val m : ℕ) : ℝ) / ((m : ℝ) - h.val) := div_nonneg hg hb.le
        nlinarith
      · rw [min_eq_right hc, hsub]
        have : (m : ℝ) / (2 * ((m : ℝ) - h.val)) * ((Nat.gcd h.val m : ℕ) : ℝ) =
            (m / 2) * (((Nat.gcd h.val m : ℕ) : ℝ) / ((m : ℝ) - h.val)) := by field_simp
        rw [this]
        have : 0 ≤ ((Nat.gcd h.val m : ℕ) : ℝ) / h.val := div_nonneg hg ha.le
        nlinarith
  have hsumG : ∑ h : ZMod m, G h ≤ m.divisors.card * (1 + Real.log m) := by
    have : ∑ h : ZMod m, G h =
        ∑ j ∈ range m, (if j = 0 then 0 else ((Nat.gcd j m : ℕ) : ℝ) / j) := by
      rw [← sum_zmod_val m (fun j => if j = 0 then 0 else ((Nat.gcd j m : ℕ) : ℝ) / j)]
      refine Finset.sum_congr rfl fun h _ => ?_
      simp only [G, ZMod.val_eq_zero]
    rw [this]
    refine le_trans ?_ (sum_gcd_div_le m hm)
    rw [Finset.range_eq_Ico]
    have hsplit : ∑ j ∈ Ico 0 m, (if j = 0 then 0 else ((Nat.gcd j m : ℕ) : ℝ) / j) ≤
        ∑ j ∈ Ioc 0 m, ((Nat.gcd j m : ℕ) : ℝ) / j := by
      rw [← Finset.sum_filter_add_sum_filter_not (Ico 0 m) (fun j => j = 0)]
      have h0 : ∑ j ∈ (Ico 0 m).filter (fun j => j = 0),
          (if j = 0 then 0 else ((Nat.gcd j m : ℕ) : ℝ) / j) = 0 :=
        Finset.sum_eq_zero fun j hj => by rw [if_pos (Finset.mem_filter.mp hj).2]
      rw [h0, zero_add]
      calc ∑ j ∈ (Ico 0 m).filter (fun j => ¬ j = 0),
            (if j = 0 then 0 else ((Nat.gcd j m : ℕ) : ℝ) / j)
          = ∑ j ∈ (Ico 0 m).filter (fun j => ¬ j = 0), ((Nat.gcd j m : ℕ) : ℝ) / j :=
            Finset.sum_congr rfl fun j hj => by rw [if_neg (Finset.mem_filter.mp hj).2]
        _ ≤ ∑ j ∈ Ioc 0 m, ((Nat.gcd j m : ℕ) : ℝ) / j := by
            refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => by positivity
            intro j hj
            simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_Ioc] at hj ⊢
            omega
    exact hsplit
  have hGneg : ∑ h : ZMod m, G (-h) = ∑ h : ZMod m, G h :=
    Fintype.sum_equiv (Equiv.neg (ZMod m)) _ _ fun h => rfl
  calc ∑ h : ZMod m, wt m h * Nat.gcd h.val m ≤ ∑ h : ZMod m, (m / 2) * (G h + G (-h)) :=
        sum_le_sum fun h _ => hpt h
    _ = (m / 2) * (∑ h : ZMod m, G h + ∑ h : ZMod m, G (-h)) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib]
    _ = m * ∑ h : ZMod m, G h := by rw [hGneg]; ring
    _ ≤ m * (m.divisors.card * (1 + Real.log m)) := mul_le_mul_of_nonneg_left hsumG hmR.le
    _ = m * m.divisors.card * (1 + Real.log m) := by ring

/-! ### The completion identity -/

lemma sum_stdAddChar_mul' (m : ℕ) [NeZero m] (a : ZMod m) :
    ∑ h : ZMod m, (ZMod.stdAddChar (h * a) : ℂ) = if a = 0 then (m : ℂ) else 0 := by
  rw [AddChar.sum_mulShift a (ZMod.isPrimitive_stdAddChar m), ZMod.card]
  push_cast; rfl

/-- Fourier inversion for the multiplicity of a residue in `I`. -/
lemma card_fiber_eq (m : ℕ) [NeZero m] (I : Finset ℤ) (x : ZMod m) :
    ((#(I.filter (fun t : ℤ => (t : ZMod m) = x)) : ℕ) : ℂ) =
      (1 / (m : ℂ)) * ∑ h : ZMod m, intervalSum m I h * ZMod.stdAddChar (-(h * x)) := by
  classical
  have hm : (m : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne m
  simp_rw [intervalSum, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [← AddChar.map_add_eq_mul]
  have : ∀ t ∈ I, ∑ h : ZMod m, (ZMod.stdAddChar (h * (t : ZMod m) + -(h * x)) : ℂ) =
      if (t : ZMod m) = x then (m : ℂ) else 0 := by
    intro t _
    have := sum_stdAddChar_mul' m ((t : ZMod m) - x)
    simp only [sub_eq_zero] at this
    rw [← this]
    refine Finset.sum_congr rfl fun h _ => ?_
    congr 1; ring
  rw [Finset.sum_congr rfl this, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  field_simp

/-- The number of `(t, s) ∈ I × J` with `(t, s) mod m ∈ Λ`. -/
def boxCount (m : ℕ) (Λ : Finset (ZMod m × ZMod m)) (I J : Finset ℤ) : ℕ :=
  #((I ×ˢ J).filter (fun p : ℤ × ℤ => ((p.1 : ZMod m), (p.2 : ZMod m)) ∈ Λ))

/-- **The completion identity.** -/
theorem card_box_eq (m : ℕ) [NeZero m] (Λ : Finset (ZMod m × ZMod m)) (I J : Finset ℤ) :
    ((boxCount m Λ I J : ℕ) : ℂ) =
      (1 / (m : ℂ) ^ 2) * ∑ h : ZMod m, ∑ k : ZMod m,
        intervalSum m I h * intervalSum m J k * setFourier Λ h k := by
  classical
  -- the count is `∑_{q ∈ Λ} f_I(q₁) f_J(q₂)`
  have hcount : boxCount m Λ I J =
      ∑ q ∈ Λ, #(I.filter (fun t : ℤ => (t : ZMod m) = q.1)) *
        #(J.filter (fun s : ℤ => (s : ZMod m) = q.2)) := by
    rw [boxCount, Finset.card_eq_sum_card_fiberwise
      (s := (I ×ˢ J).filter (fun p : ℤ × ℤ => ((p.1 : ZMod m), (p.2 : ZMod m)) ∈ Λ))
      (f := fun p : ℤ × ℤ => ((p.1 : ZMod m), (p.2 : ZMod m)))
      (t := Λ) (fun p hp => (Finset.mem_filter.mp hp).2)]
    refine Finset.sum_congr rfl fun q hq => ?_
    rw [← Finset.card_product]
    congr 1
    ext ⟨t, s⟩
    simp only [Finset.mem_filter, Finset.mem_product]
    constructor
    · rintro ⟨⟨⟨ht, hs⟩, _⟩, he⟩
      rw [Prod.ext_iff] at he
      exact ⟨⟨ht, he.1⟩, ⟨hs, he.2⟩⟩
    · rintro ⟨⟨ht, h1⟩, ⟨hs, h2⟩⟩
      have he : ((t : ZMod m), (s : ZMod m)) = q := Prod.ext h1 h2
      exact ⟨⟨⟨ht, hs⟩, he ▸ hq⟩, he⟩
  have hmul : ∀ q : ZMod m × ZMod m,
      (1 / (m : ℂ) * ∑ h : ZMod m, intervalSum m I h * ZMod.stdAddChar (-(h * q.1))) *
        ((1 / (m : ℂ)) * ∑ k : ZMod m, intervalSum m J k * ZMod.stdAddChar (-(k * q.2))) =
      ∑ h : ZMod m, ∑ k : ZMod m, 1 / (m : ℂ) ^ 2 *
        (intervalSum m I h * intervalSum m J k * ZMod.stdAddChar (-(h * q.1 + k * q.2))) := by
    intro q
    rw [show ∀ x y : ℂ, (1 / (m : ℂ) * x) * (1 / (m : ℂ) * y) = 1 / (m : ℂ) ^ 2 * (x * y) from
      fun x y => by ring, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [neg_add, AddChar.map_add_eq_mul]
    ring
  calc ((boxCount m Λ I J : ℕ) : ℂ)
      = ∑ q ∈ Λ, ((#(I.filter (fun t : ℤ => (t : ZMod m) = q.1)) : ℕ) : ℂ) *
          ((#(J.filter (fun s : ℤ => (s : ZMod m) = q.2)) : ℕ) : ℂ) := by
        rw [hcount]; push_cast; rfl
    _ = ∑ q ∈ Λ, (1 / (m : ℂ) * ∑ h : ZMod m, intervalSum m I h * ZMod.stdAddChar (-(h * q.1))) *
        ((1 / (m : ℂ)) * ∑ k : ZMod m, intervalSum m J k * ZMod.stdAddChar (-(k * q.2))) := by
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [card_fiber_eq, card_fiber_eq]
    _ = ∑ q ∈ Λ, ∑ h : ZMod m, ∑ k : ZMod m, 1 / (m : ℂ) ^ 2 *
        (intervalSum m I h * intervalSum m J k * ZMod.stdAddChar (-(h * q.1 + k * q.2))) :=
        Finset.sum_congr rfl fun q _ => hmul q
    _ = ∑ h : ZMod m, ∑ k : ZMod m, ∑ q ∈ Λ, 1 / (m : ℂ) ^ 2 *
        (intervalSum m I h * intervalSum m J k * ZMod.stdAddChar (-(h * q.1 + k * q.2))) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun h _ => Finset.sum_comm
    _ = (1 / (m : ℂ) ^ 2) * ∑ h : ZMod m, ∑ k : ZMod m,
        intervalSum m I h * intervalSum m J k * setFourier Λ h k := by
        simp only [setFourier, Finset.mul_sum]

/-- **The completion bound.** If `|Î(h)|, |Ĵ(h)| ≤ w(h)` for `h ≠ 0` and
`|Λ̂(h,k)| ≤ B a(h) a(k)`, `|Λ̂(0,k)| ≤ B a(k)`, `|Λ̂(h,0)| ≤ B a(h)` off the origin, then the
count differs from `|I||J||Λ|/m²` by at most `B m⁻² ((|I| + |J|) W + W²)`,
`W = ∑_{h ≠ 0} w(h) a(h)`. -/
theorem card_box_sub_le (m : ℕ) [NeZero m] (Λ : Finset (ZMod m × ZMod m)) (I J : Finset ℤ)
    (w a : ZMod m → ℝ) (B : ℝ) (hw0 : ∀ h, 0 ≤ w h)
    (hI : ∀ h, h ≠ 0 → ‖intervalSum m I h‖ ≤ w h) (hJ : ∀ h, h ≠ 0 → ‖intervalSum m J h‖ ≤ w h)
    (h11 : ∀ h k, h ≠ 0 → k ≠ 0 → ‖setFourier Λ h k‖ ≤ B * (a h * a k))
    (h01 : ∀ k, k ≠ 0 → ‖setFourier Λ 0 k‖ ≤ B * a k)
    (h10 : ∀ h, h ≠ 0 → ‖setFourier Λ h 0‖ ≤ B * a h) :
    |((boxCount m Λ I J : ℕ) : ℝ) -
        #I * #J * #Λ / (m : ℝ) ^ 2| ≤
      B / (m : ℝ) ^ 2 * ((#I + #J) * (∑ h ∈ univ.erase 0, w h * a h) +
        (∑ h ∈ univ.erase 0, w h * a h) ^ 2) := by
  classical
  have hm : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
  set W := ∑ h ∈ univ.erase (0 : ZMod m), w h * a h with hW
  set F : ZMod m → ZMod m → ℂ := fun h k => intervalSum m I h * intervalSum m J k * setFourier Λ h k
  have hI0 : intervalSum m I 0 = #I := by simp [intervalSum]
  have hJ0 : intervalSum m J 0 = #J := by simp [intervalSum]
  have hΛ0 : setFourier Λ 0 0 = #Λ := by simp [setFourier]
  have hF00 : F 0 0 = (#I * #J * #Λ : ℂ) := by simp only [F, hI0, hJ0, hΛ0]
  -- split the double sum
  have hsplit : ∑ h : ZMod m, ∑ k : ZMod m, F h k =
      F 0 0 + ∑ k ∈ univ.erase 0, F 0 k + ∑ h ∈ univ.erase 0, F h 0 +
        ∑ h ∈ univ.erase 0, ∑ k ∈ univ.erase 0, F h k := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : ZMod m))]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : ZMod m))]
    have : ∀ h, ∑ k : ZMod m, F h k = F h 0 + ∑ k ∈ univ.erase 0, F h k := fun h =>
      (Finset.add_sum_erase _ _ (Finset.mem_univ (0 : ZMod m))).symm
    simp_rw [this, Finset.sum_add_distrib]
    ring
  have hcount := card_box_eq m Λ I J
  have hdiff : ((boxCount m Λ I J : ℕ) : ℂ) -
      (#I * #J * #Λ : ℂ) / (m : ℂ) ^ 2 =
      (1 / (m : ℂ) ^ 2) * (∑ k ∈ univ.erase 0, F 0 k + ∑ h ∈ univ.erase 0, F h 0 +
        ∑ h ∈ univ.erase 0, ∑ k ∈ univ.erase 0, F h k) := by
    rw [hcount]
    change (1 / (m : ℂ) ^ 2) * ∑ h : ZMod m, ∑ k : ZMod m, F h k - _ = _
    rw [hsplit, hF00]
    ring
  have hb1 : ‖∑ k ∈ univ.erase 0, F 0 k‖ ≤ #I * (B * W) := by
    calc ‖∑ k ∈ univ.erase 0, F 0 k‖ ≤ ∑ k ∈ univ.erase 0, ‖F 0 k‖ := norm_sum_le _ _
      _ ≤ ∑ k ∈ univ.erase 0, #I * (B * (w k * a k)) := by
          refine sum_le_sum fun k hk => ?_
          have hk0 : k ≠ 0 := Finset.ne_of_mem_erase hk
          simp only [F, norm_mul, hI0, Complex.norm_natCast]
          calc (#I : ℝ) * ‖intervalSum m J k‖ * ‖setFourier Λ 0 k‖
              ≤ #I * w k * (B * a k) :=
                mul_le_mul (mul_le_mul_of_nonneg_left (hJ k hk0) (by positivity)) (h01 k hk0)
                  (norm_nonneg _) (by have := hw0 k; positivity)
            _ = #I * (B * (w k * a k)) := by ring
      _ = #I * (B * W) := by rw [← Finset.mul_sum, ← Finset.mul_sum]
  have hb2 : ‖∑ h ∈ univ.erase 0, F h 0‖ ≤ #J * (B * W) := by
    calc ‖∑ h ∈ univ.erase 0, F h 0‖ ≤ ∑ h ∈ univ.erase 0, ‖F h 0‖ := norm_sum_le _ _
      _ ≤ ∑ h ∈ univ.erase 0, #J * (B * (w h * a h)) := by
          refine sum_le_sum fun h hh => ?_
          have hh0 : h ≠ 0 := Finset.ne_of_mem_erase hh
          simp only [F, norm_mul, hJ0, Complex.norm_natCast]
          calc ‖intervalSum m I h‖ * (#J : ℝ) * ‖setFourier Λ h 0‖
              ≤ w h * #J * (B * a h) :=
                mul_le_mul (mul_le_mul_of_nonneg_right (hI h hh0) (by positivity)) (h10 h hh0)
                  (norm_nonneg _) (by have := hw0 h; positivity)
            _ = #J * (B * (w h * a h)) := by ring
      _ = #J * (B * W) := by rw [← Finset.mul_sum, ← Finset.mul_sum]
  have hb3 : ‖∑ h ∈ univ.erase 0, ∑ k ∈ univ.erase 0, F h k‖ ≤ B * W ^ 2 := by
    calc ‖∑ h ∈ univ.erase 0, ∑ k ∈ univ.erase 0, F h k‖
        ≤ ∑ h ∈ univ.erase 0, ∑ k ∈ univ.erase 0, ‖F h k‖ :=
          (norm_sum_le _ _).trans (sum_le_sum fun h _ => norm_sum_le _ _)
      _ ≤ ∑ h ∈ univ.erase 0, ∑ k ∈ univ.erase 0, B * ((w h * a h) * (w k * a k)) := by
          refine sum_le_sum fun h hh => sum_le_sum fun k hk => ?_
          have hh0 : h ≠ 0 := Finset.ne_of_mem_erase hh
          have hk0 : k ≠ 0 := Finset.ne_of_mem_erase hk
          simp only [F, norm_mul]
          calc ‖intervalSum m I h‖ * ‖intervalSum m J k‖ * ‖setFourier Λ h k‖
              ≤ w h * w k * (B * (a h * a k)) :=
                mul_le_mul (mul_le_mul (hI h hh0) (hJ k hk0) (norm_nonneg _) (hw0 h))
                  (h11 h k hh0 hk0) (norm_nonneg _) (by have := hw0 h; have := hw0 k; positivity)
            _ = B * ((w h * a h) * (w k * a k)) := by ring
      _ = B * W ^ 2 := by
          rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun h _ => ?_
          rw [Finset.mul_sum]
  have hnorm : ‖((boxCount m Λ I J : ℕ) : ℂ) -
      (#I * #J * #Λ : ℂ) / (m : ℂ) ^ 2‖ ≤
      B / (m : ℝ) ^ 2 * ((#I + #J) * W + W ^ 2) := by
    rw [hdiff, norm_mul]
    have h1 : ‖(1 / (m : ℂ) ^ 2)‖ = 1 / (m : ℝ) ^ 2 := by
      rw [norm_div, norm_one, norm_pow, Complex.norm_natCast]
    rw [h1]
    calc 1 / (m : ℝ) ^ 2 * ‖∑ k ∈ univ.erase 0, F 0 k + ∑ h ∈ univ.erase 0, F h 0 +
          ∑ h ∈ univ.erase 0, ∑ k ∈ univ.erase 0, F h k‖
        ≤ 1 / (m : ℝ) ^ 2 * (#I * (B * W) + #J * (B * W) + B * W ^ 2) := by
          gcongr
          exact (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
            (add_le_add hb1 hb2)) hb3)
      _ = B / (m : ℝ) ^ 2 * ((#I + #J) * W + W ^ 2) := by ring
  have hcast : ((boxCount m Λ I J : ℕ) : ℂ) -
      (#I * #J * #Λ : ℂ) / (m : ℂ) ^ 2 =
      ((((boxCount m Λ I J : ℕ) : ℝ) -
        #I * #J * #Λ / (m : ℝ) ^ 2 : ℝ) : ℂ) := by push_cast; ring
  rw [hcast, Complex.norm_real, Real.norm_eq_abs] at hnorm
  exact hnorm

end

end ArtinPrimitiveRoots.L102K
end

section
/-! # L102K: Fourier coefficients of the residue hyperbola ([21] (3.28))

Modulo `m₁ = n S₁` (with `S₁ ∣ n`, `S₂` coprime to `m₁`, `a` a unit) the set
`Λ = {(t, s) : S₁ ∣ t, (x₀ + S₂ t)(y₀ + S₂ s) = a}` has Fourier coefficients
`S₁ Λ̂(h,k) = ∑_{j < S₁} e(c_j) K_{m₁}((jn − h)σ, −kσa)`, `σ = S₂⁻¹`, so
`|Λ̂(h,k)|⁴ ≤ 2 d(m₁)³ m₁³ S₁ (k, m₁)` and the same with `(h, m₁)`. -/

namespace ArtinPrimitiveRoots.L102K

open Finset

noncomputable section

/-- The hyperbola `{(t, s) : S₁ ∣ t, (x₀ + S₂ t)(y₀ + S₂ s) = a}` modulo `n S₁`. -/
def hyperSet (n S₁ S₂ : ℕ) [NeZero (n * S₁)] (x₀ y₀ a : ℤ) :
    Finset (ZMod (n * S₁) × ZMod (n * S₁)) :=
  univ.filter fun p => S₁ ∣ p.1.val ∧
    ((x₀ : ZMod (n * S₁)) + S₂ * p.1) * ((y₀ : ZMod (n * S₁)) + S₂ * p.2) = a

lemma natCast_mul_eq_zero_iff (n S₁ : ℕ) [NeZero (n * S₁)] (z : ZMod (n * S₁)) :
    (n : ZMod (n * S₁)) * z = 0 ↔ S₁ ∣ z.val := by
  have hn : 0 < n := Nat.pos_of_ne_zero fun h0 => NeZero.ne (n * S₁) (by rw [h0, zero_mul])
  have : (n : ZMod (n * S₁)) * z = ((n * z.val : ℕ) : ZMod (n * S₁)) := by
    push_cast; rw [ZMod.natCast_zmod_val]
  rw [this, ZMod.natCast_eq_zero_iff]
  exact Nat.mul_dvd_mul_iff_left hn

/-- `∑_{j < S₁} e(jnz/(nS₁)) = S₁ · 1[S₁ ∣ z]`. -/
lemma sum_range_char (n S₁ : ℕ) [NeZero (n * S₁)] (z : ZMod (n * S₁)) :
    ∑ j ∈ range S₁, (ZMod.stdAddChar (((j * n : ℕ) : ZMod (n * S₁)) * z) : ℂ) =
      if S₁ ∣ z.val then (S₁ : ℂ) else 0 := by
  set ζ : ℂ := ZMod.stdAddChar ((n : ZMod (n * S₁)) * z) with hζ
  have hterm : ∀ j : ℕ, (ZMod.stdAddChar (((j * n : ℕ) : ZMod (n * S₁)) * z) : ℂ) = ζ ^ j := by
    intro j
    rw [hζ, ← AddChar.map_nsmul_eq_pow, nsmul_eq_mul]
    push_cast; ring_nf
  simp_rw [hterm]
  split_ifs with hd
  · have h1 : ζ = 1 := by
      rw [hζ, (natCast_mul_eq_zero_iff n S₁ z).mpr hd, AddChar.map_zero_eq_one]
    simp [h1]
  · have h1 : ζ ≠ 1 := by
      intro h1
      apply hd
      rw [← natCast_mul_eq_zero_iff]
      apply ZMod.injective_stdAddChar (N := n * S₁)
      rw [AddChar.map_zero_eq_one]
      exact h1
    have h2 : ζ ^ S₁ = 1 := by
      rw [hζ, ← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, ← mul_assoc, ← Nat.cast_mul,
        mul_comm S₁ n, ZMod.natCast_self, zero_mul, AddChar.map_zero_eq_one]
    rw [geom_sum_eq h1, h2, sub_self, zero_div]

/-- If `G ∣ nS₁` divides `z u + n c` with `u` a unit, then `G ≤ S₁ (z, nS₁)`. -/
lemma le_mul_gcd_of_dvd {n S₁ : ℕ} [NeZero (n * S₁)] {G : ℕ} (hG : G ∣ n * S₁)
    (z u c : ZMod (n * S₁)) (hu : IsUnit u) (hdiv : G ∣ (z * u + (n : ZMod (n * S₁)) * c).val) :
    G ≤ S₁ * Nat.gcd z.val (n * S₁) := by
  have hm : 0 < n * S₁ := Nat.pos_of_ne_zero (NeZero.ne _)
  have hn : 0 < n := Nat.pos_of_mul_pos_right hm
  have hS₁ : 0 < S₁ := Nat.pos_of_mul_pos_left hm
  set G' := Nat.gcd G n with hG'
  have hG'0 : 0 < G' := Nat.gcd_pos_of_pos_right _ hn
  have hG'm : G' ∣ n * S₁ := (Nat.gcd_dvd_right G n).trans (Dvd.intro S₁ rfl)
  let π := ZMod.castHom hG'm (ZMod G')
  have h1 : π (z * u + (n : ZMod (n * S₁)) * c) = 0 := by
    rw [← ZMod.natCast_zmod_val (z * u + (n : ZMod (n * S₁)) * c), map_natCast,
      ZMod.natCast_eq_zero_iff]
    exact (Nat.gcd_dvd_left G n).trans hdiv
  have h2 : π (n : ZMod (n * S₁)) = 0 := by
    rw [map_natCast, ZMod.natCast_eq_zero_iff]; exact Nat.gcd_dvd_right G n
  rw [map_add, map_mul, map_mul, h2, zero_mul, add_zero] at h1
  have h3 : π z = 0 := ((hu.map π).mul_left_eq_zero).mp h1
  have h4 : G' ∣ z.val := by
    have : π z = ((z.val : ℕ) : ZMod G') := by
      conv_lhs => rw [← ZMod.natCast_zmod_val z]
      rw [map_natCast]
    rw [this, ZMod.natCast_eq_zero_iff] at h3
    exact h3
  have h5 : G' ≤ Nat.gcd z.val (n * S₁) :=
    Nat.le_of_dvd (Nat.gcd_pos_of_pos_right _ hm) (Nat.dvd_gcd h4 hG'm)
  have h6 : G ∣ G' * Nat.gcd G S₁ := by
    have := Nat.gcd_mul_right_dvd_mul_gcd G n S₁
    rwa [Nat.gcd_eq_left hG] at this
  have h7 : G ≤ G' * S₁ := (Nat.le_of_dvd (Nat.mul_pos hG'0 (Nat.gcd_pos_of_pos_right _ hS₁)) h6).trans
    (Nat.mul_le_mul_left _ (Nat.le_of_dvd hS₁ (Nat.gcd_dvd_right _ _)))
  calc G ≤ G' * S₁ := h7
    _ ≤ Nat.gcd z.val (n * S₁) * S₁ := Nat.mul_le_mul_right _ h5
    _ = S₁ * Nat.gcd z.val (n * S₁) := mul_comm _ _

/-- **(3.28)**: the Fourier coefficient of the hyperbola as an average of Kloosterman sums. -/
theorem setFourier_hyperSet (n S₁ S₂ : ℕ) [NeZero (n * S₁)] (x₀ y₀ a : ℤ)
    (hS₂ : Nat.Coprime S₂ (n * S₁)) (ha : IsUnit (a : ZMod (n * S₁))) (h k : ZMod (n * S₁)) :
    (S₁ : ℂ) * setFourier (hyperSet n S₁ S₂ x₀ y₀ a) h k =
      ∑ j ∈ range S₁,
        ZMod.stdAddChar (h * (((ZMod.unitOfCoprime S₂ hS₂)⁻¹ : (ZMod (n * S₁))ˣ) : ZMod (n * S₁)) *
            (x₀ : ZMod (n * S₁)) + k * (((ZMod.unitOfCoprime S₂ hS₂)⁻¹ : (ZMod (n * S₁))ˣ) :
              ZMod (n * S₁)) * (y₀ : ZMod (n * S₁)) -
            ((j * n : ℕ) : ZMod (n * S₁)) *
              (((ZMod.unitOfCoprime S₂ hS₂)⁻¹ : (ZMod (n * S₁))ˣ) : ZMod (n * S₁)) *
                (x₀ : ZMod (n * S₁))) *
          kloosterman (n * S₁)
            (((j * n : ℕ) : ZMod (n * S₁)) *
                (((ZMod.unitOfCoprime S₂ hS₂)⁻¹ : (ZMod (n * S₁))ˣ) : ZMod (n * S₁)) -
              h * (((ZMod.unitOfCoprime S₂ hS₂)⁻¹ : (ZMod (n * S₁))ˣ) : ZMod (n * S₁)))
            (-(k * (((ZMod.unitOfCoprime S₂ hS₂)⁻¹ : (ZMod (n * S₁))ˣ) : ZMod (n * S₁)) *
              (a : ZMod (n * S₁)))) := by
  classical
  set σ : (ZMod (n * S₁)) := (((ZMod.unitOfCoprime S₂ hS₂)⁻¹ : (ZMod (n * S₁))ˣ) : (ZMod (n * S₁))) with hσ
  have hσS : (S₂ : (ZMod (n * S₁))) * σ = 1 := by
    rw [hσ, ← ZMod.coe_unitOfCoprime S₂ hS₂, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  set A : (ZMod (n * S₁))ˣ := ha.unit with hA
  have hAa : ((A : (ZMod (n * S₁))ˣ) : (ZMod (n * S₁))) = a := ha.unit_spec
  -- `F u` is the summand at the unit `u`
  let F : (ZMod (n * S₁))ˣ → ℂ := fun u =>
    ZMod.stdAddChar (-(h * (σ * ((u : (ZMod (n * S₁))) - (x₀ : ZMod (n * S₁)))) + k * (σ * ((a : (ZMod (n * S₁))) * ((u⁻¹ : (ZMod (n * S₁))ˣ) : (ZMod (n * S₁))) - (y₀ : ZMod (n * S₁))))))
  -- Step 1: the bijection with units
  have hstep1 : setFourier (hyperSet n S₁ S₂ x₀ y₀ a) h k =
      ∑ u ∈ univ.filter (fun u : (ZMod (n * S₁))ˣ => S₁ ∣ (σ * ((u : (ZMod (n * S₁))) - (x₀ : ZMod (n * S₁)))).val), F u := by
    rw [setFourier]
    symm
    refine Finset.sum_bij (fun u _ => (σ * ((u : (ZMod (n * S₁))) - (x₀ : ZMod (n * S₁))), σ * ((a : (ZMod (n * S₁))) * ((u⁻¹ : (ZMod (n * S₁))ˣ) : (ZMod (n * S₁))) - (y₀ : ZMod (n * S₁)))))
      ?_ ?_ ?_ ?_
    · intro u hu
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
      simp only [hyperSet, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨hu, ?_⟩
      have e1 : (x₀ : (ZMod (n * S₁))) + S₂ * (σ * ((u : (ZMod (n * S₁))) - (x₀ : ZMod (n * S₁)))) = u := by
        rw [← mul_assoc, hσS, one_mul]; ring
      have e2 : (y₀ : (ZMod (n * S₁))) + S₂ * (σ * ((a : (ZMod (n * S₁))) * ((u⁻¹ : (ZMod (n * S₁))ˣ) : (ZMod (n * S₁))) - (y₀ : ZMod (n * S₁)))) =
          (a : (ZMod (n * S₁))) * ((u⁻¹ : (ZMod (n * S₁))ˣ) : (ZMod (n * S₁))) := by
        rw [← mul_assoc, hσS, one_mul]; ring
      rw [e1, e2, mul_left_comm, Units.mul_inv, mul_one]
    · intro u _ u' _ heq
      simp only [Prod.mk.injEq] at heq
      have := heq.1
      have hσu : IsUnit σ := Units.isUnit _
      have h2 : (u : (ZMod (n * S₁))) - x₀ = (u' : (ZMod (n * S₁))) - x₀ := hσu.mul_left_cancel this
      exact Units.ext (by linear_combination h2)
    · intro p hp
      simp only [hyperSet, Finset.mem_filter, Finset.mem_univ, true_and] at hp
      obtain ⟨hdiv, heq⟩ := hp
      have hX : IsUnit ((x₀ : (ZMod (n * S₁))) + S₂ * p.1) := by
        rw [← heq] at ha; exact isUnit_of_mul_isUnit_left ha
      refine ⟨hX.unit, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [IsUnit.unit_spec]
        have : σ * ((x₀ : (ZMod (n * S₁))) + S₂ * p.1 - (x₀ : ZMod (n * S₁))) = p.1 := by
          rw [add_sub_cancel_left, ← mul_assoc, mul_comm σ, hσS, one_mul]
        rw [this]; exact hdiv
      · have e1 : σ * (((hX.unit : (ZMod (n * S₁))ˣ) : (ZMod (n * S₁))) - (x₀ : ZMod (n * S₁))) = p.1 := by
          rw [IsUnit.unit_spec, add_sub_cancel_left, ← mul_assoc, mul_comm σ, hσS, one_mul]
        have e2 : (a : (ZMod (n * S₁))) * (((hX.unit)⁻¹ : (ZMod (n * S₁))ˣ) : (ZMod (n * S₁))) = (y₀ : (ZMod (n * S₁))) + S₂ * p.2 := by
          have hinv : (((hX.unit)⁻¹ : (ZMod (n * S₁))ˣ) : (ZMod (n * S₁))) *
              ((x₀ : (ZMod (n * S₁))) + S₂ * p.1) = 1 := by
            exact hX.val_inv_mul
          rw [← heq]
          linear_combination ((y₀ : (ZMod (n * S₁))) + S₂ * p.2) * hinv
        have e3 : σ * ((a : (ZMod (n * S₁))) * (((hX.unit)⁻¹ : (ZMod (n * S₁))ˣ) : (ZMod (n * S₁))) - (y₀ : ZMod (n * S₁))) = p.2 := by
          rw [e2, add_sub_cancel_left, ← mul_assoc, mul_comm σ, hσS, one_mul]
        rw [e1, e3]
    · intro u _
      rfl
  -- Step 2: insert the character sum detecting `S₁ ∣ ·`
  have hstep2 : (S₁ : ℂ) * ∑ u ∈ univ.filter (fun u : (ZMod (n * S₁))ˣ => S₁ ∣ (σ * ((u : (ZMod (n * S₁))) - (x₀ : ZMod (n * S₁)))).val), F u =
      ∑ j ∈ range S₁, ∑ u : (ZMod (n * S₁))ˣ,
        ZMod.stdAddChar (((j * n : ℕ) : (ZMod (n * S₁))) * (σ * ((u : (ZMod (n * S₁))) - (x₀ : ZMod (n * S₁))))) * F u := by
    rw [Finset.sum_filter, Finset.mul_sum, Finset.sum_comm]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [← Finset.sum_mul, sum_range_char]
    split_ifs <;> simp
  rw [hstep1, hstep2]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [kloosterman, Finset.mul_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  simp only [F]
  rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
  congr 1
  ring

/-- `‖K‖⁴ ≤ X` gives `‖K‖ ≤ X^{1/4}`. -/
lemma le_rpow_quarter_of_pow_four_le {x X : ℝ} (hx : 0 ≤ x) (h : x ^ 4 ≤ X) :
    x ≤ X ^ ((1 : ℝ) / 4) := by
  have hX : 0 ≤ X := le_trans (by positivity) h
  calc x = (x ^ 4) ^ ((1 : ℝ) / 4) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hx]; norm_num
    _ ≤ X ^ ((1 : ℝ) / 4) := Real.rpow_le_rpow (by positivity) h (by norm_num)

/-- **The hyperbola bound**: `|Λ̂(h,k)| ≤ (2 d(m₁)³ m₁³ S₁ g)^{1/4}` for `g = (k, m₁)` and for
`g = (h, m₁)`. -/
theorem norm_setFourier_hyperSet_le (n S₁ S₂ : ℕ) [NeZero (n * S₁)] (x₀ y₀ a : ℤ)
    (hS₂ : Nat.Coprime S₂ (n * S₁)) (ha : IsUnit (a : ZMod (n * S₁))) (h k : ZMod (n * S₁))
    (g : ℕ) (hg : g = Nat.gcd k.val (n * S₁) ∨ g = Nat.gcd h.val (n * S₁)) :
    ‖setFourier (hyperSet n S₁ S₂ x₀ y₀ a) h k‖ ≤
      (2 * ((n * S₁).divisors.card : ℝ) ^ 3 * ((n * S₁ : ℕ) : ℝ) ^ 3 * (S₁ * g)) ^
        ((1 : ℝ) / 4) := by
  have hm : 0 < n * S₁ := Nat.pos_of_ne_zero (NeZero.ne _)
  have hS₁ : 0 < S₁ := Nat.pos_of_mul_pos_left hm
  set σ : (ZMod (n * S₁)) := (((ZMod.unitOfCoprime S₂ hS₂)⁻¹ : (ZMod (n * S₁))ˣ) : (ZMod (n * S₁))) with hσ
  have hσu : IsUnit σ := Units.isUnit _
  set X := 2 * ((n * S₁).divisors.card : ℝ) ^ 3 * ((n * S₁ : ℕ) : ℝ) ^ 3 * (S₁ * g)
  -- each Kloosterman sum is bounded by `X^{1/4}`
  have hK : ∀ j : ℕ, ‖kloosterman (n * S₁) (((j * n : ℕ) : (ZMod (n * S₁))) * σ - h * σ) (-(k * σ * a))‖ ≤
      X ^ ((1 : ℝ) / 4) := by
    intro j
    refine le_rpow_quarter_of_pow_four_le (norm_nonneg _) ?_
    refine (norm_kloosterman_pow_four_le (n * S₁) _ _).trans ?_
    set G := Nat.gcd (Nat.gcd (((j * n : ℕ) : (ZMod (n * S₁))) * σ - h * σ).val (-(k * σ * a)).val) (n * S₁)
    have hGm : G ∣ n * S₁ := Nat.gcd_dvd_right _ _
    have hGle : G ≤ S₁ * g := by
      rcases hg with hg | hg
      · rw [hg]
        refine le_mul_gcd_of_dvd hGm k (-(σ * a)) 0 ?_ ?_
        · exact (hσu.mul ha).neg
        · have : k * -(σ * (a : (ZMod (n * S₁)))) + (n : (ZMod (n * S₁))) * 0 = -(k * σ * a) := by ring
          rw [this]
          exact (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_right _ _)
      · rw [hg]
        refine le_mul_gcd_of_dvd hGm h (-σ) ((j : (ZMod (n * S₁))) * σ) hσu.neg ?_
        have : h * -σ + (n : (ZMod (n * S₁))) * ((j : (ZMod (n * S₁))) * σ) = ((j * n : ℕ) : (ZMod (n * S₁))) * σ - h * σ := by
          push_cast; ring
        rw [this]
        exact (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_left _ _)
    have hGR : (G : ℝ) ≤ S₁ * g := by exact_mod_cast hGle
    have hpos : 0 ≤ 2 * ((n * S₁).divisors.card : ℝ) ^ 3 * ((n * S₁ : ℕ) : ℝ) ^ 3 := by positivity
    calc 2 * ((n * S₁).divisors.card : ℝ) ^ 3 * ((n * S₁ : ℕ) : ℝ) ^ 3 * (G : ℝ)
        ≤ 2 * ((n * S₁).divisors.card : ℝ) ^ 3 * ((n * S₁ : ℕ) : ℝ) ^ 3 * (S₁ * g) :=
          mul_le_mul_of_nonneg_left hGR hpos
      _ = X := rfl
  have hid := setFourier_hyperSet n S₁ S₂ x₀ y₀ a hS₂ ha h k
  have hS₁R : (0 : ℝ) < S₁ := by exact_mod_cast hS₁
  have hnorm : (S₁ : ℝ) * ‖setFourier (hyperSet n S₁ S₂ x₀ y₀ a) h k‖ ≤
      S₁ * X ^ ((1 : ℝ) / 4) := by
    have : ‖(S₁ : ℂ) * setFourier (hyperSet n S₁ S₂ x₀ y₀ a) h k‖ =
        (S₁ : ℝ) * ‖setFourier (hyperSet n S₁ S₂ x₀ y₀ a) h k‖ := by
      rw [norm_mul, Complex.norm_natCast]
    rw [← this, hid]
    calc ‖∑ j ∈ range S₁, _‖ ≤ ∑ j ∈ range S₁, X ^ ((1 : ℝ) / 4) := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
          rw [norm_mul, AddChar.norm_apply, one_mul]
          exact hK j
      _ = S₁ * X ^ ((1 : ℝ) / 4) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  exact le_of_mul_le_mul_left hnorm hS₁R

end

end ArtinPrimitiveRoots.L102K
end

section
/-! # L102K: the number of points on the residue hyperbola ([21] (3.26))

`#Λ = ∑_{l ∣ n, (l, S) = 1} μ(l) n/l`, where `Λ = hyperSet n S₁ S₂ x₀ y₀ a`. -/

namespace ArtinPrimitiveRoots.L102K

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

noncomputable section

/-- `∑_{l ∣ n, l ∣ z} μ(l) = 1[(z, n) = 1]`. -/
lemma sum_moebius_dvd (n : ℕ) (hn : 0 < n) (z : ℤ) :
    ∑ l ∈ n.divisors, (if (l : ℤ) ∣ z then μ l else 0) = if IsCoprime z (n : ℤ) then 1 else 0 := by
  have key : ∑ l ∈ n.divisors, (if (l : ℤ) ∣ z then μ l else 0) =
      ∑ l ∈ (Int.gcd z n).divisors, μ l := by
    rw [← Finset.sum_filter]
    congr 1
    ext l
    simp only [Finset.mem_filter, Nat.mem_divisors]
    have hg : Int.gcd z n ≠ 0 :=
      Nat.pos_iff_ne_zero.mp (Int.gcd_pos_of_ne_zero_right _ (by exact_mod_cast hn.ne'))
    rw [Int.natCast_dvd]
    constructor
    · rintro ⟨⟨hl, _⟩, hz⟩
      refine ⟨?_, hg⟩
      rw [Int.gcd, Int.natAbs_natCast]
      exact Nat.dvd_gcd hz hl
    · rintro ⟨hl, _⟩
      rw [Int.gcd, Int.natAbs_natCast] at hl
      exact ⟨⟨Nat.dvd_trans hl (Nat.gcd_dvd_right _ _), hn.ne'⟩,
        Nat.dvd_trans hl (Nat.gcd_dvd_left _ _)⟩
  rw [key, ← coe_mul_zeta_apply, moebius_mul_coe_zeta, one_apply]
  by_cases h : IsCoprime z (n : ℤ)
  · rw [if_pos h, if_pos (Int.isCoprime_iff_gcd_eq_one.mp h)]
  · rw [if_neg h, if_neg (fun h' => h (Int.isCoprime_iff_gcd_eq_one.mpr h'))]

/-- `#{r < n : r ≡ c (mod l)} = n/l` for `l ∣ n`, `c < l`. -/
lemma card_range_mod_eq (n l c : ℕ) (hl : 0 < l) (hln : l ∣ n) (hc : c < l) :
    #((range n).filter (fun r => r % l = c)) = n / l := by
  obtain ⟨q, rfl⟩ := hln
  rw [Nat.mul_div_cancel_left _ hl]
  calc #((range (l * q)).filter (fun r => r % l = c)) = #(range q) := by
        refine Finset.card_nbij' (fun r => r / l) (fun i => c + l * i) ?_ ?_ ?_ ?_
        · intro r hr
          simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hr ⊢
          rw [Nat.div_lt_iff_lt_mul hl]; linarith [mul_comm l q, hr.1]
        · intro i hi
          simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hi ⊢
          refine ⟨?_, ?_⟩
          · have : i + 1 ≤ q := hi
            nlinarith
          · rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hc]
        · intro r hr
          simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hr
          rw [← hr.2]; exact Nat.mod_add_div r l
        · intro i _
          show (c + l * i) / l = i
          rw [Nat.add_mul_div_left _ _ hl, Nat.div_eq_of_lt hc, zero_add]
    _ = q := Finset.card_range q

/-- For `l ∣ n`: `#{r < n : l ∣ x₀ + S r}` is `n/l` if `(l, S) = 1` and `0` otherwise, provided
`x₀` is coprime to every prime dividing both `n` and `S`. -/
lemma card_range_dvd (n S l : ℕ) (hl : 0 < l) (hln : l ∣ n) (x₀ : ℤ)
    (hx₀ : IsCoprime x₀ (Nat.gcd n S : ℤ)) :
    #((range n).filter (fun r : ℕ => (l : ℤ) ∣ x₀ + S * r)) =
      if Nat.Coprime l S then n / l else 0 := by
  classical
  split_ifs with hcop
  · -- `S` is a unit mod `l`
    have : NeZero l := ⟨hl.ne'⟩
    set Su : (ZMod l)ˣ := ZMod.unitOfCoprime S hcop.symm
    set c : ZMod l := -(x₀ : ZMod l) * ((Su⁻¹ : (ZMod l)ˣ) : ZMod l)
    have hiff : ∀ r : ℕ, (l : ℤ) ∣ x₀ + S * r ↔ r % l = c.val := by
      intro r
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      have hSu : ((Su : (ZMod l)ˣ) : ZMod l) = (S : ZMod l) := ZMod.coe_unitOfCoprime _ _
      constructor
      · intro h
        have : (r : ZMod l) = c := by
          simp only [c]
          rw [← hSu] at h
          have h2 := congrArg (· * ((Su⁻¹ : (ZMod l)ˣ) : ZMod l)) h
          simp only [zero_mul] at h2
          rw [add_mul, mul_assoc, mul_comm (r : ZMod l), ← mul_assoc, Units.mul_inv, one_mul] at h2
          linear_combination h2
        rw [← this, ZMod.val_natCast]
      · intro h
        have : (r : ZMod l) = c := by
          rw [← ZMod.natCast_zmod_val c, ← h, ZMod.natCast_mod]
        rw [this]
        simp only [c]
        rw [← hSu]
        have := Su.mul_inv
        linear_combination (-(x₀ : ZMod l)) * this
    rw [Finset.filter_congr fun r _ => hiff r]
    exact card_range_mod_eq n l c.val hl hln (ZMod.val_lt c)
  · -- a common prime `p ∣ l, S` divides `x₀ + S r` only if it divides `x₀`
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro r _ hdiv
    obtain ⟨p, hp, hpl, hpS⟩ := Nat.Prime.not_coprime_iff_dvd.mp hcop
    have hpg : p ∣ Nat.gcd n S := Nat.dvd_gcd (hpl.trans hln) hpS
    have hpx : (p : ℤ) ∣ x₀ := by
      have h1 : (p : ℤ) ∣ x₀ + S * r := (Int.natCast_dvd_natCast.mpr hpl).trans hdiv
      have h2 : (p : ℤ) ∣ (S : ℤ) * r := (Int.natCast_dvd_natCast.mpr hpS).mul_right _
      have := dvd_sub h1 h2
      simpa using this
    have hpu : IsUnit (p : ℤ) := by
      have hpg' : (p : ℤ) ∣ (Nat.gcd n S : ℤ) := Int.natCast_dvd_natCast.mpr hpg
      exact hx₀.isUnit_of_dvd' hpx hpg'
    rw [Int.isUnit_iff_natAbs_eq, Int.natAbs_natCast] at hpu
    exact hp.one_lt.ne' hpu

/-- `#{r < n : (x₀ + S r, n) = 1} = ∑_{l ∣ n, (l,S) = 1} μ(l) n/l`. -/
lemma card_range_coprime (n S : ℕ) (hn : 0 < n) (x₀ : ℤ) (hx₀ : IsCoprime x₀ (Nat.gcd n S : ℤ)) :
    ((#((range n).filter (fun r : ℕ => IsCoprime (x₀ + S * r) (n : ℤ))) : ℕ) : ℤ) =
      ∑ l ∈ n.divisors.filter (fun l => Nat.Coprime l S), μ l * ((n / l : ℕ) : ℤ) := by
  classical
  rw [Finset.card_filter, Nat.cast_sum]
  have h1 : ∀ r ∈ range n, (((if IsCoprime (x₀ + S * r) (n : ℤ) then 1 else 0 : ℕ)) : ℤ) =
      ∑ l ∈ n.divisors, (if (l : ℤ) ∣ x₀ + S * r then μ l else 0) := by
    intro r _
    rw [sum_moebius_dvd n hn]
    split_ifs <;> simp
  rw [Finset.sum_congr rfl h1, Finset.sum_comm, Finset.sum_filter]
  refine Finset.sum_congr rfl fun l hl => ?_
  have hln : l ∣ n := Nat.dvd_of_mem_divisors hl
  have hl0 : 0 < l := Nat.pos_of_dvd_of_pos hln hn
  rw [← Finset.sum_filter, Finset.sum_const, card_range_dvd n S l hl0 hln x₀ hx₀, nsmul_eq_mul]
  split_ifs <;> simp [mul_comm]

/-- `#Λ` is the number of admissible first coordinates. -/
lemma card_hyperSet_fst (n S₁ S₂ : ℕ) [NeZero (n * S₁)] (x₀ y₀ a : ℤ)
    (hS₂ : Nat.Coprime S₂ (n * S₁)) (ha : IsUnit (a : ZMod (n * S₁))) :
    #(hyperSet n S₁ S₂ x₀ y₀ a) =
      #(univ.filter fun t : ZMod (n * S₁) => S₁ ∣ t.val ∧
        IsUnit ((x₀ : ZMod (n * S₁)) + S₂ * t)) := by
  classical
  set σ : ZMod (n * S₁) := (((ZMod.unitOfCoprime S₂ hS₂)⁻¹ : (ZMod (n * S₁))ˣ) : ZMod (n * S₁))
    with hσ
  have hσS : (S₂ : ZMod (n * S₁)) * σ = 1 := by
    rw [hσ, ← ZMod.coe_unitOfCoprime S₂ hS₂, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  refine Finset.card_bij (fun p _ => p.1) ?_ ?_ ?_
  · intro p hp
    simp only [hyperSet, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    refine ⟨hp.1, ?_⟩
    have := hp.2 ▸ ha
    exact isUnit_of_mul_isUnit_left this
  · intro p hp p' hp' h1
    simp only [hyperSet, Finset.mem_filter, Finset.mem_univ, true_and] at hp hp'
    have hX : IsUnit ((x₀ : ZMod (n * S₁)) + S₂ * p.1) := isUnit_of_mul_isUnit_left (hp.2 ▸ ha)
    have e : ((x₀ : ZMod (n * S₁)) + S₂ * p.1) * ((y₀ : ZMod (n * S₁)) + S₂ * p.2) =
        ((x₀ : ZMod (n * S₁)) + S₂ * p.1) * ((y₀ : ZMod (n * S₁)) + S₂ * p'.2) := by
      rw [hp.2]; rw [h1]; exact hp'.2.symm
    have e2 := hX.mul_left_cancel e
    have e3 : (S₂ : ZMod (n * S₁)) * p.2 = S₂ * p'.2 := by linear_combination e2
    have e4 : p.2 = p'.2 := by
      have := congrArg (σ * ·) e3
      rwa [← mul_assoc, ← mul_assoc, mul_comm σ, hσS, one_mul, one_mul] at this
    exact Prod.ext h1 e4
  · intro t ht
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
    obtain ⟨hdiv, hX⟩ := ht
    refine ⟨(t, σ * ((a : ZMod (n * S₁)) * ((hX.unit⁻¹ : (ZMod (n * S₁))ˣ) : ZMod (n * S₁)) -
      (y₀ : ZMod (n * S₁)))), ?_, rfl⟩
    simp only [hyperSet, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨hdiv, ?_⟩
    have hinv := hX.mul_val_inv
    rw [← mul_assoc, hσS, one_mul]
    linear_combination (a : ZMod (n * S₁)) * hinv

/-- `#Λ ≤ nS₁`. -/
lemma card_hyperSet_le (n S₁ S₂ : ℕ) [NeZero (n * S₁)] (x₀ y₀ a : ℤ)
    (hS₂ : Nat.Coprime S₂ (n * S₁)) (ha : IsUnit (a : ZMod (n * S₁))) :
    #(hyperSet n S₁ S₂ x₀ y₀ a) ≤ n * S₁ := by
  rw [card_hyperSet_fst n S₁ S₂ x₀ y₀ a hS₂ ha]
  exact (Finset.card_filter_le _ _).trans (by rw [Finset.card_univ, ZMod.card])

/-- **(3.26)**: `#Λ = ∑_{l ∣ n, (l, S₁S₂) = 1} μ(l) n/l`. -/
theorem card_hyperSet (n S₁ S₂ : ℕ) [NeZero (n * S₁)] (x₀ y₀ a : ℤ) (hS₁n : S₁ ∣ n)
    (hS₂ : Nat.Coprime S₂ (n * S₁)) (ha : IsUnit (a : ZMod (n * S₁)))
    (hx₀ : IsCoprime x₀ (Nat.gcd n (S₁ * S₂) : ℤ)) :
    ((#(hyperSet n S₁ S₂ x₀ y₀ a) : ℕ) : ℤ) =
      ∑ l ∈ n.divisors.filter (fun l => Nat.Coprime l (S₁ * S₂)), μ l * ((n / l : ℕ) : ℤ) := by
  classical
  have hm : 0 < n * S₁ := Nat.pos_of_ne_zero (NeZero.ne _)
  have hn : 0 < n := Nat.pos_of_mul_pos_right hm
  have hS₁ : 0 < S₁ := Nat.pos_of_mul_pos_left hm
  set σ : ZMod (n * S₁) := (((ZMod.unitOfCoprime S₂ hS₂)⁻¹ : (ZMod (n * S₁))ˣ) : ZMod (n * S₁))
    with hσ
  have hσS : (S₂ : ZMod (n * S₁)) * σ = 1 := by
    rw [hσ, ← ZMod.coe_unitOfCoprime S₂ hS₂, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hA := card_hyperSet_fst n S₁ S₂ x₀ y₀ a hS₂ ha
  -- (b) parametrise `t = S₁ r`
  have hB : #(univ.filter fun t : ZMod (n * S₁) => S₁ ∣ t.val ∧
        IsUnit ((x₀ : ZMod (n * S₁)) + S₂ * t)) =
      #((range n).filter (fun r : ℕ => IsCoprime (x₀ + ((S₁ * S₂ : ℕ) : ℤ) * r) (n : ℤ))) := by
    symm
    refine Finset.card_bij (fun r _ => ((S₁ * r : ℕ) : ZMod (n * S₁))) ?_ ?_ ?_
    · intro r hr
      simp only [Finset.mem_filter, Finset.mem_range] at hr
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have hlt : S₁ * r < n * S₁ := by rw [mul_comm n]; exact Nat.mul_lt_mul_of_pos_left hr.1 hS₁
      refine ⟨by rw [ZMod.val_natCast, Nat.mod_eq_of_lt hlt]; exact Dvd.intro r rfl, ?_⟩
      have : (x₀ : ZMod (n * S₁)) + S₂ * ((S₁ * r : ℕ) : ZMod (n * S₁)) =
          ((x₀ + ((S₁ * S₂ : ℕ) : ℤ) * r : ℤ) : ZMod (n * S₁)) := by push_cast; ring
      rw [this, ZMod.coe_int_isUnit_iff_isCoprime]
      have h2 := hr.2
      have hcop : IsCoprime (x₀ + ((S₁ * S₂ : ℕ) : ℤ) * r) (((n * S₁ : ℕ)) : ℤ) := by
        rw [show ((n * S₁ : ℕ) : ℤ) = (n : ℤ) * (S₁ : ℤ) by push_cast; ring]
        refine IsCoprime.mul_right h2 ?_
        exact h2.of_isCoprime_of_dvd_right (Int.natCast_dvd_natCast.mpr hS₁n)
      exact hcop.symm
    · intro r hr r' hr' h
      simp only [Finset.mem_filter, Finset.mem_range] at hr hr'
      have hlt : S₁ * r < n * S₁ := by rw [mul_comm n]; exact Nat.mul_lt_mul_of_pos_left hr.1 hS₁
      have hlt' : S₁ * r' < n * S₁ := by rw [mul_comm n]; exact Nat.mul_lt_mul_of_pos_left hr'.1 hS₁
      have := congrArg ZMod.val h
      rw [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt hlt'] at this
      exact Nat.eq_of_mul_eq_mul_left hS₁ this
    · intro t ht
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
      obtain ⟨⟨r, hr⟩, hX⟩ := ht
      have hlt := ZMod.val_lt t
      rw [hr] at hlt
      have hrn : r < n := by
        rw [mul_comm n] at hlt; exact Nat.lt_of_mul_lt_mul_left hlt
      refine ⟨r, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_range]
        refine ⟨hrn, ?_⟩
        have : (x₀ : ZMod (n * S₁)) + S₂ * t =
            ((x₀ + ((S₁ * S₂ : ℕ) : ℤ) * r : ℤ) : ZMod (n * S₁)) := by
          rw [← ZMod.natCast_zmod_val t, hr]; push_cast; ring
        rw [this, ZMod.coe_int_isUnit_iff_isCoprime] at hX
        have := hX.symm
        rw [show ((n * S₁ : ℕ) : ℤ) = (n : ℤ) * (S₁ : ℤ) by push_cast; ring] at this
        exact this.of_mul_right_left
      · rw [← hr, ZMod.natCast_zmod_val]
  rw [hA, hB]
  have hx₀' : IsCoprime x₀ (Nat.gcd n (S₁ * S₂) : ℤ) := hx₀
  exact card_range_coprime n (S₁ * S₂) hn x₀ hx₀'

end

end ArtinPrimitiveRoots.L102K
end

section
/-! # L102K: the fibre count ([21] (3.25)–(3.27))

For `n ≥ 1`, squarefree `S`, `a` coprime to `n` with `a ≡ x₀y₀ (S)`, and integer intervals
`[A₁, B₁)`, `[A₂, B₂)`:

`#{(x, y) : x ≡ x₀, y ≡ y₀ (S), nS ∣ xy − a} = (B₁−A₁)(B₂−A₂) M(n)/(nS)² + O(error)`,

`M(n) = ∑_{l ∣ n, (l,S)=1} μ(l) n/l`. The proof splits `S = S₁S₂` with `S₁ = (S, n)`, substitutes
`x = x₀ + S₂t`, `y = y₀ + S₂s`, and applies the completion bound to `hyperSet` modulo `nS₁`. -/

namespace ArtinPrimitiveRoots.L102K

open Finset ArithmeticFunction Real
open scoped ArithmeticFunction.Moebius

noncomputable section

/-! ### The arithmetic of `S = S₁ S₂` -/

lemma split_facts (S n : ℕ) (hS : Squarefree S) (hn : n ≠ 0) :
    Nat.gcd S n * (S / Nat.gcd S n) = S ∧ Nat.Coprime (S / Nat.gcd S n) n ∧
      Nat.Coprime (Nat.gcd S n) (S / Nat.gcd S n) ∧ Nat.gcd S n ∣ n := by
  have h1 : Nat.gcd S n * (S / Nat.gcd S n) = S := Nat.mul_div_cancel' (Nat.gcd_dvd_left S n)
  refine ⟨h1, Nat.coprime_div_gcd_of_squarefree hS hn, ?_, Nat.gcd_dvd_right S n⟩
  have : Squarefree (Nat.gcd S n * (S / Nat.gcd S n)) := by rw [h1]; exact hS
  exact (Nat.squarefree_mul_iff.mp this).1

/-! ### The substituted interval -/

lemma exists_sub_interval (S₂ : ℕ) (hS₂ : 0 < S₂) (x₀ A B : ℤ) (hAB : A ≤ B) :
    ∃ lo hi : ℤ, (∀ t : ℤ, t ∈ Finset.Ico lo hi ↔ x₀ + S₂ * t ∈ Finset.Ico A B) ∧
      |((#(Finset.Ico lo hi) : ℕ) : ℝ) - ((B - A : ℤ) : ℝ) / S₂| ≤ 1 := by
  have hS : (0 : ℝ) < S₂ := by exact_mod_cast hS₂
  refine ⟨⌈((A - x₀ : ℤ) : ℝ) / S₂⌉, ⌈((B - x₀ : ℤ) : ℝ) / S₂⌉, ?_, ?_⟩
  · intro t
    simp only [Finset.mem_Ico]
    rw [Int.ceil_le, Int.lt_ceil, div_le_iff₀ hS, lt_div_iff₀ hS]
    have hc : ((t * (S₂ : ℤ) : ℤ) : ℝ) = (t : ℝ) * S₂ := by push_cast; ring
    rw [← hc, Int.cast_le, Int.cast_lt]
    constructor
    · rintro ⟨h1, h2⟩; constructor <;> linarith [mul_comm (S₂ : ℤ) t]
    · rintro ⟨h1, h2⟩; constructor <;> linarith [mul_comm (S₂ : ℤ) t]
  · set a := ((A - x₀ : ℤ) : ℝ) / S₂
    set b := ((B - x₀ : ℤ) : ℝ) / S₂
    have hab : a ≤ b := by
      apply div_le_div_of_nonneg_right _ hS.le
      exact_mod_cast (by linarith : A - x₀ ≤ B - x₀)
    have hle : ⌈a⌉ ≤ ⌈b⌉ := Int.ceil_mono hab
    rw [Int.card_Ico]
    have hcast : (((⌈b⌉ - ⌈a⌉).toNat : ℕ) : ℝ) = ((⌈b⌉ - ⌈a⌉ : ℤ) : ℝ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg (by linarith)]
    rw [hcast]
    have hba : ((B - A : ℤ) : ℝ) / S₂ = b - a := by
      simp only [a, b]; push_cast; field_simp; ring
    rw [hba]
    push_cast
    have h1 := Int.le_ceil a
    have h2 := Int.ceil_lt_add_one a
    have h3 := Int.le_ceil b
    have h4 := Int.ceil_lt_add_one b
    rw [abs_le]; constructor <;> linarith

/-! ### The substitution is a bijection -/

/-- The membership equivalence behind the substitution `x = x₀ + S₂ t`, `y = y₀ + S₂ s`. -/
lemma mem_hyperSet_iff (n S : ℕ) (hn : 0 < n) (hS0 : 0 < S) (hS : Squarefree S)
    [NeZero (n * Nat.gcd S n)] (x₀ y₀ a : ℤ) (ha : IsCoprime a (n : ℤ))
    (hax : (S : ℤ) ∣ a - x₀ * y₀) (t s : ℤ) :
    ((t : ZMod (n * Nat.gcd S n)), (s : ZMod (n * Nat.gcd S n))) ∈
        hyperSet n (Nat.gcd S n) (S / Nat.gcd S n) x₀ y₀ a ↔
      ((S : ℤ) ∣ (x₀ + (S / Nat.gcd S n : ℕ) * t) - x₀ ∧
        (S : ℤ) ∣ (y₀ + (S / Nat.gcd S n : ℕ) * s) - y₀ ∧
        ((n * S : ℕ) : ℤ) ∣ (x₀ + (S / Nat.gcd S n : ℕ) * t) * (y₀ + (S / Nat.gcd S n : ℕ) * s) - a) := by
  obtain ⟨hS12, hS2n, hS1S2, hS1n⟩ := split_facts S n hS hn.ne'
  set S₁ := Nat.gcd S n with hS₁
  set S₂ := S / Nat.gcd S n with hS₂
  set m₁ := n * S₁ with hm₁
  have hS₁0 : 0 < S₁ := Nat.gcd_pos_of_pos_left _ hS0
  have hS₂0 : 0 < S₂ := by
    rcases Nat.eq_zero_or_pos S₂ with h | h
    · rw [h, mul_zero] at hS12; omega
    · exact h
  have hm₁0 : 0 < m₁ := Nat.mul_pos hn hS₁0
  -- integer forms
  have hSZ : (S : ℤ) = (S₁ : ℤ) * S₂ := by exact_mod_cast hS12.symm
  have hnS : ((n * S : ℕ) : ℤ) = (m₁ : ℤ) * S₂ := by
    simp only [hm₁]; push_cast; rw [hSZ]; ring
  have hS₁m : (S₁ : ℤ) ∣ (m₁ : ℤ) := ⟨n, by simp only [hm₁]; push_cast; ring⟩
  have hcopS₂m : IsCoprime (m₁ : ℤ) (S₂ : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_natCast_natCast]
    exact Nat.Coprime.mul_left hS2n.symm hS1S2
  have hcopS₁S₂ : IsCoprime (S₁ : ℤ) (S₂ : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_natCast_natCast]; exact hS1S2
  -- `x₀` is coprime to `S₁`
  have hcopx : IsCoprime (S₁ : ℤ) x₀ := by
    have haS₁ : IsCoprime a (S₁ : ℤ) :=
      ha.of_isCoprime_of_dvd_right (Int.natCast_dvd_natCast.mpr hS1n)
    have hS₁dvd : (S₁ : ℤ) ∣ a - x₀ * y₀ :=
      (Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_left S n)).trans hax
    obtain ⟨k, hk⟩ := hS₁dvd
    have : IsCoprime (x₀ * y₀) (S₁ : ℤ) := by
      have e : x₀ * y₀ = a + (S₁ : ℤ) * (-k) := by linarith
      rw [e]
      exact haS₁.add_mul_left_left (-k)
    exact this.of_mul_left_left.symm
  -- the pieces
  have hval : S₁ ∣ (t : ZMod m₁).val ↔ (S₁ : ℤ) ∣ t := by
    rw [← Int.natCast_dvd_natCast, ZMod.val_intCast, Int.dvd_iff_emod_eq_zero,
      Int.dvd_iff_emod_eq_zero, Int.emod_emod_of_dvd _ hS₁m]
  have hprod : ((x₀ : ZMod m₁) + S₂ * (t : ZMod m₁)) * ((y₀ : ZMod m₁) + S₂ * (s : ZMod m₁)) =
      (a : ZMod m₁) ↔ (m₁ : ℤ) ∣ (x₀ + S₂ * t) * (y₀ + S₂ * s) - a := by
    have : ((x₀ : ZMod m₁) + S₂ * (t : ZMod m₁)) * ((y₀ : ZMod m₁) + S₂ * (s : ZMod m₁)) =
        (((x₀ + S₂ * t) * (y₀ + S₂ * s) : ℤ) : ZMod m₁) := by push_cast; ring
    rw [this, ZMod.intCast_eq_intCast_iff_dvd_sub, ← dvd_neg, neg_sub]
  have hS₂dvd : (S₂ : ℤ) ∣ (x₀ + S₂ * t) * (y₀ + S₂ * s) - a := by
    have h1 : (S₂ : ℤ) ∣ a - x₀ * y₀ :=
      (Int.natCast_dvd_natCast.mpr (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left S n))).trans hax
    have : (x₀ + S₂ * t) * (y₀ + S₂ * s) - a =
        (S₂ : ℤ) * (t * y₀ + x₀ * s + S₂ * t * s) - (a - x₀ * y₀) := by ring
    rw [this]
    exact dvd_sub (Dvd.intro _ rfl) h1
  have hxdiv : (S : ℤ) ∣ (x₀ + S₂ * t) - x₀ ↔ (S₁ : ℤ) ∣ t := by
    rw [add_sub_cancel_left, hSZ, mul_comm (S₂ : ℤ) t]
    exact mul_dvd_mul_iff_right (by exact_mod_cast hS₂0.ne')
  have hydiv : (S : ℤ) ∣ (y₀ + S₂ * s) - y₀ ↔ (S₁ : ℤ) ∣ s := by
    rw [add_sub_cancel_left, hSZ, mul_comm (S₂ : ℤ) s]
    exact mul_dvd_mul_iff_right (by exact_mod_cast hS₂0.ne')
  have hbig : ((n * S : ℕ) : ℤ) ∣ (x₀ + S₂ * t) * (y₀ + S₂ * s) - a ↔
      (m₁ : ℤ) ∣ (x₀ + S₂ * t) * (y₀ + S₂ * s) - a := by
    rw [hnS]
    constructor
    · intro h; exact (Dvd.intro _ rfl).trans h
    · intro h; exact hcopS₂m.mul_dvd h hS₂dvd
  -- `S₁ ∣ t` and `m₁ ∣ xy − a` force `S₁ ∣ s`
  have hs : (S₁ : ℤ) ∣ t → (m₁ : ℤ) ∣ (x₀ + S₂ * t) * (y₀ + S₂ * s) - a → (S₁ : ℤ) ∣ s := by
    intro ht hm
    have h1 : (S₁ : ℤ) ∣ (x₀ + S₂ * t) * (y₀ + S₂ * s) - a := hS₁m.trans hm
    have h2 : (S₁ : ℤ) ∣ a - x₀ * y₀ :=
      (Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_left S n)).trans hax
    have h3 : (S₁ : ℤ) ∣ (S₂ : ℤ) * t * (y₀ + S₂ * s) := (ht.mul_left _).mul_right _
    have h4 : (S₁ : ℤ) ∣ (x₀ * S₂) * s := by
      have : (x₀ * S₂) * s = ((x₀ + S₂ * t) * (y₀ + S₂ * s) - a) + (a - x₀ * y₀) -
          (S₂ : ℤ) * t * (y₀ + S₂ * s) := by ring
      rw [this]
      exact dvd_sub (dvd_add h1 h2) h3
    exact (hcopx.mul_right hcopS₁S₂).dvd_of_dvd_mul_left h4
  simp only [hyperSet, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hval, hprod, hxdiv, hydiv, hbig]
  constructor
  · rintro ⟨ht, hm⟩; exact ⟨ht, hs ht hm, hm⟩
  · rintro ⟨ht, _, hm⟩; exact ⟨ht, hm⟩

/-- The fibre count equals a box count of `hyperSet`. -/
lemma fiber_eq_boxCount (n S : ℕ) (hn : 0 < n) (hS0 : 0 < S) (hS : Squarefree S)
    [NeZero (n * Nat.gcd S n)] (x₀ y₀ a : ℤ) (ha : IsCoprime a (n : ℤ))
    (hax : (S : ℤ) ∣ a - x₀ * y₀) (A₁ B₁ A₂ B₂ lo₁ hi₁ lo₂ hi₂ : ℤ)
    (hI : ∀ t : ℤ, t ∈ Finset.Ico lo₁ hi₁ ↔
      x₀ + (S / Nat.gcd S n : ℕ) * t ∈ Finset.Ico A₁ B₁)
    (hJ : ∀ s : ℤ, s ∈ Finset.Ico lo₂ hi₂ ↔
      y₀ + (S / Nat.gcd S n : ℕ) * s ∈ Finset.Ico A₂ B₂) :
    #((Finset.Ico A₁ B₁ ×ˢ Finset.Ico A₂ B₂).filter (fun p : ℤ × ℤ =>
        (S : ℤ) ∣ p.1 - x₀ ∧ (S : ℤ) ∣ p.2 - y₀ ∧ ((n * S : ℕ) : ℤ) ∣ p.1 * p.2 - a)) =
      boxCount (n * Nat.gcd S n) (hyperSet n (Nat.gcd S n) (S / Nat.gcd S n) x₀ y₀ a)
        (Finset.Ico lo₁ hi₁) (Finset.Ico lo₂ hi₂) := by
  obtain ⟨hS12, _, _, _⟩ := split_facts S n hS hn.ne'
  set S₂ := S / Nat.gcd S n with hS₂
  have hS₂0 : 0 < S₂ := by
    rcases Nat.eq_zero_or_pos S₂ with h | h
    · rw [h, mul_zero] at hS12; omega
    · exact h
  have hS₂Z : (S₂ : ℤ) ≠ 0 := by exact_mod_cast hS₂0.ne'
  have hS₂dvdS : (S₂ : ℤ) ∣ (S : ℤ) := Int.natCast_dvd_natCast.mpr (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left S n))
  rw [boxCount]
  symm
  refine Finset.card_bij (fun p _ => (x₀ + S₂ * p.1, y₀ + S₂ * p.2)) ?_ ?_ ?_
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_product] at hp ⊢
    obtain ⟨⟨h1, h2⟩, h3⟩ := hp
    exact ⟨⟨(hI p.1).mp h1, (hJ p.2).mp h2⟩,
      (mem_hyperSet_iff n S hn hS0 hS x₀ y₀ a ha hax p.1 p.2).mp h3⟩
  · intro p _ p' _ h
    simp only [Prod.mk.injEq] at h
    have e1 : (S₂ : ℤ) * p.1 = S₂ * p'.1 := by linarith [h.1]
    have e2 : (S₂ : ℤ) * p.2 = S₂ * p'.2 := by linarith [h.2]
    exact Prod.ext (mul_left_cancel₀ hS₂Z e1) (mul_left_cancel₀ hS₂Z e2)
  · intro q hq
    simp only [Finset.mem_filter, Finset.mem_product] at hq
    obtain ⟨⟨hx, hy⟩, hP⟩ := hq
    obtain ⟨t, ht⟩ := hS₂dvdS.trans hP.1
    obtain ⟨s, hs⟩ := hS₂dvdS.trans hP.2.1
    have hxq : q.1 = x₀ + S₂ * t := by linarith
    have hyq : q.2 = y₀ + S₂ * s := by linarith
    refine ⟨(t, s), ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_product]
      refine ⟨⟨(hI t).mpr (hxq ▸ hx), (hJ s).mpr (hyq ▸ hy)⟩, ?_⟩
      refine (mem_hyperSet_iff n S hn hS0 hS x₀ y₀ a ha hax t s).mpr ?_
      rw [← hxq, ← hyq]; exact hP
    · simp only
      rw [← hxq, ← hyq]

end

end ArtinPrimitiveRoots.L102K

namespace ArtinPrimitiveRoots.L102K

open Finset ArithmeticFunction Real
open scoped ArithmeticFunction.Moebius

noncomputable section

/-- The real-number bookkeeping of the fibre count. -/
lemma real_assembly {c P Q K m s₂ X Y B W T R : ℝ} (hm : 1 ≤ m) (hs₂ : 1 ≤ s₂) (hX : 0 ≤ X)
    (hY : 0 ≤ Y) (hK0 : 0 ≤ K) (hKm : K ≤ m) (hP : |P - X / s₂| ≤ 1) (hQ : |Q - Y / s₂| ≤ 1)
    (hQ0 : 0 ≤ Q) (hW0 : 0 ≤ W) (hW : W ≤ m * T) (hB0 : 0 ≤ B) (hBR : B ≤ R)
    (hc : |c - P * Q * K / m ^ 2| ≤ B / m ^ 2 * ((P + Q) * W + W ^ 2)) :
    |c - X * Y * K / (m * s₂) ^ 2| ≤ R * ((X + Y + 2) * T / m + T ^ 2) + (X + Y + 1) / m := by
  have hm0 : 0 < m := by linarith
  have hs0 : 0 < s₂ := by linarith
  have hXs : X / s₂ ≤ X := div_le_self hX hs₂
  have hYs : Y / s₂ ≤ Y := div_le_self hY hs₂
  have hXs0 : 0 ≤ X / s₂ := div_nonneg hX hs0.le
  rw [abs_le] at hP hQ
  -- Step A
  have hA : |P * Q * K / m ^ 2 - X * Y * K / (m * s₂) ^ 2| ≤ (X + Y + 1) / m := by
    have e : P * Q * K / m ^ 2 - X * Y * K / (m * s₂) ^ 2 =
        K / m ^ 2 * ((P - X / s₂) * Q + X / s₂ * (Q - Y / s₂)) := by
      field_simp; ring
    rw [e, abs_mul, abs_of_nonneg (by positivity)]
    have h1 : |(P - X / s₂) * Q + X / s₂ * (Q - Y / s₂)| ≤ X + Y + 1 := by
      have h2 : |(P - X / s₂) * Q| ≤ Q := by
        rw [abs_mul, abs_of_nonneg hQ0]
        have : |P - X / s₂| ≤ 1 := abs_le.mpr ⟨hP.1, hP.2⟩
        exact mul_le_of_le_one_left hQ0 this
      have h3 : |X / s₂ * (Q - Y / s₂)| ≤ X / s₂ := by
        rw [abs_mul, abs_of_nonneg hXs0]
        have : |Q - Y / s₂| ≤ 1 := abs_le.mpr ⟨hQ.1, hQ.2⟩
        exact mul_le_of_le_one_right hXs0 this
      calc |(P - X / s₂) * Q + X / s₂ * (Q - Y / s₂)|
          ≤ |(P - X / s₂) * Q| + |X / s₂ * (Q - Y / s₂)| := abs_add_le _ _
        _ ≤ Q + X / s₂ := add_le_add h2 h3
        _ ≤ X + Y + 1 := by linarith [hQ.2]
    calc K / m ^ 2 * |(P - X / s₂) * Q + X / s₂ * (Q - Y / s₂)| ≤ K / m ^ 2 * (X + Y + 1) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ ≤ m / m ^ 2 * (X + Y + 1) := by
          apply mul_le_mul_of_nonneg_right _ (by linarith)
          exact div_le_div_of_nonneg_right hKm (by positivity)
      _ = (X + Y + 1) / m := by field_simp
  -- Step B
  have hB : B / m ^ 2 * ((P + Q) * W + W ^ 2) ≤ R * ((X + Y + 2) * T / m + T ^ 2) := by
    have hPQ : P + Q ≤ X + Y + 2 := by linarith [hP.2, hQ.2]
    have hT0 : 0 ≤ T := by
      have : 0 ≤ m * T := le_trans hW0 hW
      exact nonneg_of_mul_nonneg_right this hm0
    have h1 : (P + Q) * W + W ^ 2 ≤ (X + Y + 2) * (m * T) + (m * T) ^ 2 := by
      have := mul_le_mul hPQ hW hW0 (by linarith)
      have h2 : W ^ 2 ≤ (m * T) ^ 2 := pow_le_pow_left₀ hW0 hW 2
      linarith
    have h2 : B / m ^ 2 * ((P + Q) * W + W ^ 2) ≤
        B / m ^ 2 * ((X + Y + 2) * (m * T) + (m * T) ^ 2) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have h3 : B / m ^ 2 * ((X + Y + 2) * (m * T) + (m * T) ^ 2) =
        B * ((X + Y + 2) * T / m + T ^ 2) := by field_simp
    rw [h3] at h2
    refine h2.trans (mul_le_mul_of_nonneg_right hBR (by positivity))
  calc |c - X * Y * K / (m * s₂) ^ 2|
      = |(c - P * Q * K / m ^ 2) + (P * Q * K / m ^ 2 - X * Y * K / (m * s₂) ^ 2)| := by ring_nf
    _ ≤ |c - P * Q * K / m ^ 2| + |P * Q * K / m ^ 2 - X * Y * K / (m * s₂) ^ 2| := abs_add_le _ _
    _ ≤ R * ((X + Y + 2) * T / m + T ^ 2) + (X + Y + 1) / m := add_le_add (hc.trans hB) hA

/-- `x₀` is coprime to `S₁ = (S, n)`. -/
lemma isCoprime_x₀ (n S : ℕ) (x₀ y₀ a : ℤ) (ha : IsCoprime a (n : ℤ))
    (hax : (S : ℤ) ∣ a - x₀ * y₀) : IsCoprime x₀ (Nat.gcd S n : ℤ) := by
  have haS₁ : IsCoprime a (Nat.gcd S n : ℤ) :=
    ha.of_isCoprime_of_dvd_right (Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_right S n))
  have hS₁dvd : (Nat.gcd S n : ℤ) ∣ a - x₀ * y₀ :=
    (Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_left S n)).trans hax
  obtain ⟨k, hk⟩ := hS₁dvd
  have : IsCoprime (x₀ * y₀) (Nat.gcd S n : ℤ) := by
    have e : x₀ * y₀ = a + (Nat.gcd S n : ℤ) * (-k) := by linarith
    rw [e]
    exact haS₁.add_mul_left_left (-k)
  exact this.of_mul_left_left

/-- `(2τ³m³S₁g)^{1/4} ≤ 2τS₁m^{3/4}g`. -/
lemma quarter_bound (τ m S₁ g : ℝ) (hτ : 1 ≤ τ) (hm : 0 ≤ m) (hS₁ : 1 ≤ S₁) (hg : 1 ≤ g) :
    (2 * τ ^ 3 * m ^ 3 * (S₁ * g)) ^ ((1 : ℝ) / 4) ≤ 2 * τ * S₁ * m ^ ((3 : ℝ) / 4) * g := by
  have hm34 : (m ^ ((3 : ℝ) / 4)) ^ 4 = m ^ 3 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hm]; norm_num
  have hR0 : 0 ≤ 2 * τ * S₁ * m ^ ((3 : ℝ) / 4) * g := by positivity
  have hle : 2 * τ ^ 3 * m ^ 3 * (S₁ * g) ≤ (2 * τ * S₁ * m ^ ((3 : ℝ) / 4) * g) ^ 4 := by
    have e : (2 * τ * S₁ * m ^ ((3 : ℝ) / 4) * g) ^ 4 = 16 * τ ^ 4 * S₁ ^ 4 * m ^ 3 * g ^ 4 := by
      rw [mul_pow, mul_pow, mul_pow, mul_pow, hm34]; ring
    rw [e]
    have h1 : τ ^ 3 ≤ τ ^ 4 := pow_le_pow_right₀ hτ (by norm_num)
    have h2 : S₁ ≤ S₁ ^ 4 := by
      calc S₁ = S₁ ^ 1 := (pow_one _).symm
        _ ≤ S₁ ^ 4 := pow_le_pow_right₀ hS₁ (by norm_num)
    have h3 : g ≤ g ^ 4 := by
      calc g = g ^ 1 := (pow_one _).symm
        _ ≤ g ^ 4 := pow_le_pow_right₀ hg (by norm_num)
    have hm3 : 0 ≤ m ^ 3 := by positivity
    have h4 : S₁ * g ≤ S₁ ^ 4 * g ^ 4 := mul_le_mul h2 h3 (by linarith) (by positivity)
    have h5 : τ ^ 3 * (S₁ * g) ≤ τ ^ 4 * (S₁ ^ 4 * g ^ 4) :=
      mul_le_mul h1 h4 (by positivity) (by positivity)
    have h6 := mul_le_mul_of_nonneg_left h5 (by positivity : (0 : ℝ) ≤ 2 * m ^ 3)
    have h7 : 0 ≤ 2 * m ^ 3 * (τ ^ 4 * (S₁ ^ 4 * g ^ 4)) := by positivity
    have e1 : 2 * τ ^ 3 * m ^ 3 * (S₁ * g) = 2 * m ^ 3 * (τ ^ 3 * (S₁ * g)) := by ring
    have e2 : 16 * τ ^ 4 * S₁ ^ 4 * m ^ 3 * g ^ 4 = 8 * (2 * m ^ 3 * (τ ^ 4 * (S₁ ^ 4 * g ^ 4))) := by
      ring
    rw [e1, e2]
    linarith
  calc (2 * τ ^ 3 * m ^ 3 * (S₁ * g)) ^ ((1 : ℝ) / 4)
      ≤ ((2 * τ * S₁ * m ^ ((3 : ℝ) / 4) * g) ^ 4) ^ ((1 : ℝ) / 4) :=
        Real.rpow_le_rpow (by positivity) hle (by norm_num)
    _ = 2 * τ * S₁ * m ^ ((3 : ℝ) / 4) * g := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hR0]; norm_num

/-- The final simplification of the fibre-count error. -/
lemma final_bound {τ₁ τN S₁ S m₁ N n Z : ℝ} (hτ₁ : 1 ≤ τ₁) (hτle : τ₁ ≤ τN)
    (hlog : 0 ≤ Real.log m₁) (hS₁ : 1 ≤ S₁) (hSle : S₁ ≤ S) (hm₁N : m₁ ≤ N) (hnm₁ : n ≤ m₁)
    (hn : 0 < n) (hN1' : 1 ≤ N) (hZ : 0 ≤ Z) :
    2 * τ₁ * S₁ * m₁ ^ ((3 : ℝ) / 4) *
        ((Z + 2) * (τ₁ * (1 + Real.log m₁)) / m₁ + (τ₁ * (1 + Real.log m₁)) ^ 2) +
      (Z + 1) / m₁ ≤
      3 * S * N ^ ((3 : ℝ) / 4) * (τN * (1 + Real.log N)) ^ 3 * ((Z + 2) / n + 1) := by
  have hm₁ : 0 < m₁ := lt_of_lt_of_le hn hnm₁
  have hN : 0 < N := lt_of_lt_of_le hm₁ hm₁N
  set T₁ := τ₁ * (1 + Real.log m₁) with hT₁
  set T := τN * (1 + Real.log N) with hT
  have hlogle : Real.log m₁ ≤ Real.log N := Real.log_le_log hm₁ hm₁N
  have hT₁le : T₁ ≤ T := mul_le_mul hτle (by linarith) (by linarith) (by linarith)
  have hT₁1 : 1 ≤ T₁ := by rw [hT₁]; exact one_le_mul_of_one_le_of_one_le hτ₁ (by linarith)
  have hT1 : 1 ≤ T := le_trans hT₁1 hT₁le
  have hSR1 : (1 : ℝ) ≤ S := le_trans hS₁ hSle
  have hm34 : m₁ ^ ((3 : ℝ) / 4) ≤ N ^ ((3 : ℝ) / 4) :=
    Real.rpow_le_rpow hm₁.le hm₁N (by norm_num)
  have hm340 : 0 ≤ m₁ ^ ((3 : ℝ) / 4) := by positivity
  have hfrac : (Z + 2) / m₁ ≤ (Z + 2) / n := div_le_div_of_nonneg_left (by linarith) hn hnm₁
  have hfrac0 : 0 ≤ (Z + 2) / n := by positivity
  have hτT : τ₁ ≤ T := le_trans (le_mul_of_one_le_right (by linarith) (by linarith)) hT₁le
  have hRle : 2 * τ₁ * S₁ * m₁ ^ ((3 : ℝ) / 4) ≤ 2 * T * S * N ^ ((3 : ℝ) / 4) := by
    have h1 : 2 * τ₁ * S₁ ≤ 2 * T * S :=
      mul_le_mul (by linarith) hSle (by linarith) (by linarith)
    exact mul_le_mul h1 hm34 hm340 (by positivity)
  have hbr : (Z + 2) * T₁ / m₁ + T₁ ^ 2 ≤ T ^ 2 * ((Z + 2) / n + 1) := by
    have h1 : (Z + 2) * T₁ / m₁ = T₁ * ((Z + 2) / m₁) := by ring
    rw [h1]
    have h2 : T₁ * ((Z + 2) / m₁) ≤ T ^ 2 * ((Z + 2) / n) := by
      have : T₁ ≤ T ^ 2 := le_trans hT₁le (le_self_pow₀ hT1 (by norm_num))
      exact mul_le_mul this hfrac (by positivity) (by positivity)
    have h3 : T₁ ^ 2 ≤ T ^ 2 := pow_le_pow_left₀ (by linarith) hT₁le 2
    rw [mul_add, mul_one]
    linarith
  have hN1 : 1 ≤ N ^ ((3 : ℝ) / 4) := Real.one_le_rpow hN1' (by norm_num)
  have hlast : (Z + 1) / m₁ ≤ S * N ^ ((3 : ℝ) / 4) * T ^ 3 * ((Z + 2) / n + 1) := by
    have h1 : (Z + 1) / m₁ ≤ (Z + 2) / n :=
      le_trans (div_le_div_of_nonneg_right (by linarith) hm₁.le) hfrac
    have h2 : 1 ≤ S * N ^ ((3 : ℝ) / 4) * T ^ 3 := by
      have : 1 ≤ T ^ 3 := one_le_pow₀ hT1
      have h4 : 1 ≤ S * N ^ ((3 : ℝ) / 4) := one_le_mul_of_one_le_of_one_le hSR1 hN1
      exact one_le_mul_of_one_le_of_one_le h4 this
    have h5 : (Z + 2) / n + 1 ≤ S * N ^ ((3 : ℝ) / 4) * T ^ 3 * ((Z + 2) / n + 1) :=
      le_mul_of_one_le_left (by linarith) h2
    linarith
  calc 2 * τ₁ * S₁ * m₁ ^ ((3 : ℝ) / 4) * ((Z + 2) * T₁ / m₁ + T₁ ^ 2) + (Z + 1) / m₁
      ≤ (2 * T * S * N ^ ((3 : ℝ) / 4)) * (T ^ 2 * ((Z + 2) / n + 1)) +
          S * N ^ ((3 : ℝ) / 4) * T ^ 3 * ((Z + 2) / n + 1) :=
        add_le_add (mul_le_mul hRle hbr (by positivity) (by positivity)) hlast
    _ = 3 * S * N ^ ((3 : ℝ) / 4) * T ^ 3 * ((Z + 2) / n + 1) := by ring

/-- **The fibre count** ([21] (3.25)–(3.27), with completion in place of smoothing). -/
theorem fiber_count (n S : ℕ) (hn : 0 < n) (hS0 : 0 < S) (hS : Squarefree S) (x₀ y₀ a : ℤ)
    (ha : IsCoprime a (n : ℤ)) (hax : (S : ℤ) ∣ a - x₀ * y₀) (A₁ B₁ A₂ B₂ : ℤ)
    (h₁ : A₁ ≤ B₁) (h₂ : A₂ ≤ B₂) :
    |(#((Finset.Ico A₁ B₁ ×ˢ Finset.Ico A₂ B₂).filter (fun p : ℤ × ℤ =>
        (S : ℤ) ∣ p.1 - x₀ ∧ (S : ℤ) ∣ p.2 - y₀ ∧ ((n * S : ℕ) : ℤ) ∣ p.1 * p.2 - a)) : ℝ) -
      ((B₁ - A₁ : ℤ) : ℝ) * ((B₂ - A₂ : ℤ) : ℝ) *
        (((∑ l ∈ n.divisors.filter (fun l => Nat.Coprime l S), μ l * ((n / l : ℕ) : ℤ)) : ℤ) : ℝ) /
          ((n : ℝ) * S) ^ 2| ≤
      3 * S * ((n * S : ℕ) : ℝ) ^ ((3 : ℝ) / 4) *
        (((n * S).divisors.card : ℝ) * (1 + Real.log ((n * S : ℕ) : ℝ))) ^ 3 *
        ((((B₁ - A₁ : ℤ) : ℝ) + ((B₂ - A₂ : ℤ) : ℝ) + 2) / n + 1) := by
  classical
  obtain ⟨hS12, hS2n, hS1S2, hS1n⟩ := split_facts S n hS hn.ne'
  set S₁ := Nat.gcd S n with hS₁def
  set S₂ := S / Nat.gcd S n with hS₂def
  have hS₁0 : 0 < S₁ := Nat.gcd_pos_of_pos_left _ hS0
  have hS₂0 : 0 < S₂ := by
    rcases Nat.eq_zero_or_pos S₂ with h | h
    · rw [h, mul_zero] at hS12; omega
    · exact h
  set m₁ := n * S₁ with hm₁
  have hm₁0 : 0 < m₁ := Nat.mul_pos hn hS₁0
  have : NeZero m₁ := ⟨hm₁0.ne'⟩
  obtain ⟨lo₁, hi₁, hI, hIc⟩ := exists_sub_interval S₂ hS₂0 x₀ A₁ B₁ h₁
  obtain ⟨lo₂, hi₂, hJ, hJc⟩ := exists_sub_interval S₂ hS₂0 y₀ A₂ B₂ h₂
  rw [fiber_eq_boxCount n S hn hS0 hS x₀ y₀ a ha hax A₁ B₁ A₂ B₂ lo₁ hi₁ lo₂ hi₂ hI hJ]
  -- the hyperbola modulo `m₁`
  have hS₂cop : Nat.Coprime S₂ m₁ := Nat.Coprime.mul_right hS2n hS1S2.symm
  have haU : IsUnit (a : ZMod m₁) := by
    rw [ZMod.coe_int_isUnit_iff_isCoprime]
    have h1 : IsCoprime a (S₁ : ℤ) :=
      ha.of_isCoprime_of_dvd_right (Int.natCast_dvd_natCast.mpr hS1n)
    have : IsCoprime a ((n : ℤ) * S₁) := ha.mul_right h1
    rw [hm₁]; push_cast; exact this.symm
  set Lam := hyperSet n S₁ S₂ x₀ y₀ a with hLam
  set τ₁ : ℝ := (m₁.divisors.card : ℝ) with hτ₁
  have hτ₁1 : 1 ≤ τ₁ := by
    rw [hτ₁]; exact_mod_cast Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr hm₁0.ne'⟩
  set R : ℝ := 2 * τ₁ * S₁ * (m₁ : ℝ) ^ ((3 : ℝ) / 4) with hR
  have hR0 : 0 ≤ R := by positivity
  have hgpos : ∀ h : ZMod m₁, (1 : ℝ) ≤ (Nat.gcd h.val m₁ : ℝ) := by
    intro h
    exact_mod_cast Nat.gcd_pos_of_pos_right _ hm₁0
  have hS₁R : (1 : ℝ) ≤ S₁ := by exact_mod_cast hS₁0
  have hFour : ∀ h k : ZMod m₁, ∀ g : ℕ,
      (g = Nat.gcd k.val m₁ ∨ g = Nat.gcd h.val m₁) → 1 ≤ g →
        ‖setFourier Lam h k‖ ≤ R * g := by
    intro h k g hg hg1
    have := norm_setFourier_hyperSet_le n S₁ S₂ x₀ y₀ a hS₂cop haU h k g hg
    refine this.trans ?_
    have hgR : (1 : ℝ) ≤ g := by exact_mod_cast hg1
    exact quarter_bound τ₁ (m₁ : ℝ) S₁ g hτ₁1 (by positivity) hS₁R hgR
  have hcomp := card_box_sub_le m₁ Lam (Finset.Ico lo₁ hi₁) (Finset.Ico lo₂ hi₂) (wt m₁)
    (fun h => (Nat.gcd h.val m₁ : ℝ)) R (wt_nonneg m₁)
    (fun h hh => norm_intervalSum_Ico_le m₁ h hh lo₁ hi₁)
    (fun h hh => norm_intervalSum_Ico_le m₁ h hh lo₂ hi₂)
    (fun h k _ _ => by
      refine (hFour h k (Nat.gcd k.val m₁) (Or.inl rfl) (Nat.gcd_pos_of_pos_right _ hm₁0)).trans ?_
      have := hgpos h
      have hk := hgpos k
      calc R * (Nat.gcd k.val m₁ : ℝ) = R * (1 * (Nat.gcd k.val m₁ : ℝ)) := by ring
        _ ≤ R * ((Nat.gcd h.val m₁ : ℝ) * (Nat.gcd k.val m₁ : ℝ)) := by gcongr)
    (fun k _ => hFour 0 k _ (Or.inl rfl) (Nat.gcd_pos_of_pos_right _ hm₁0))
    (fun h _ => hFour h 0 _ (Or.inr rfl) (Nat.gcd_pos_of_pos_right _ hm₁0))
  -- the weighted sum
  set T₁ : ℝ := τ₁ * (1 + Real.log m₁) with hT₁
  have hlogm₁ : 0 ≤ Real.log m₁ := Real.log_nonneg (by exact_mod_cast hm₁0)
  have hW : ∑ h ∈ univ.erase (0 : ZMod m₁), wt m₁ h * (Nat.gcd h.val m₁ : ℝ) ≤ m₁ * T₁ := by
    refine le_trans ?_ ((sum_wt_gcd_le m₁).trans (le_of_eq (by rw [hT₁]; ring)))
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
      fun h _ _ => mul_nonneg (wt_nonneg m₁ h) (by positivity)
  have hW0 : 0 ≤ ∑ h ∈ univ.erase (0 : ZMod m₁), wt m₁ h * (Nat.gcd h.val m₁ : ℝ) :=
    Finset.sum_nonneg fun h _ => mul_nonneg (wt_nonneg m₁ h) (by positivity)
  -- the count of `Lam`
  have hK : ((#Lam : ℕ) : ℝ) =
      (((∑ l ∈ n.divisors.filter (fun l => Nat.Coprime l S), μ l * ((n / l : ℕ) : ℤ)) : ℤ) : ℝ) := by
    have hx₀ : IsCoprime x₀ (Nat.gcd n (S₁ * S₂) : ℤ) := by
      rw [hS12, Nat.gcd_comm]; exact isCoprime_x₀ n S x₀ y₀ a ha hax
    have := card_hyperSet n S₁ S₂ x₀ y₀ a hS1n hS₂cop haU hx₀
    rw [hS12] at this
    exact_mod_cast this
  have hKm : ((#Lam : ℕ) : ℝ) ≤ m₁ := by exact_mod_cast card_hyperSet_le n S₁ S₂ x₀ y₀ a hS₂cop haU
  have hmS : ((m₁ : ℝ) * S₂) = (n : ℝ) * S := by
    rw [hm₁, ← hS12]; push_cast; ring
  have hX : (0 : ℝ) ≤ ((B₁ - A₁ : ℤ) : ℝ) := by exact_mod_cast (by linarith : (0 : ℤ) ≤ B₁ - A₁)
  have hY : (0 : ℝ) ≤ ((B₂ - A₂ : ℤ) : ℝ) := by exact_mod_cast (by linarith : (0 : ℤ) ≤ B₂ - A₂)
  set Z := ((B₁ - A₁ : ℤ) : ℝ) + ((B₂ - A₂ : ℤ) : ℝ) with hZdef
  have hmain := real_assembly (c := (boxCount m₁ Lam (Finset.Ico lo₁ hi₁) (Finset.Ico lo₂ hi₂) : ℝ))
    (P := (#(Finset.Ico lo₁ hi₁) : ℝ)) (Q := (#(Finset.Ico lo₂ hi₂) : ℝ)) (K := (#Lam : ℝ))
    (m := m₁) (s₂ := S₂) (X := ((B₁ - A₁ : ℤ) : ℝ)) (Y := ((B₂ - A₂ : ℤ) : ℝ)) (B := R)
    (W := ∑ h ∈ univ.erase (0 : ZMod m₁), wt m₁ h * (Nat.gcd h.val m₁ : ℝ)) (T := T₁) (R := R)
    (by exact_mod_cast hm₁0) (by exact_mod_cast hS₂0) hX hY (by positivity) hKm hIc hJc
    (by positivity) hW0 hW hR0 le_rfl hcomp
  rw [hmS, hK] at hmain
  refine hmain.trans ?_
  -- final simplification
  have hm₁nS : m₁ ∣ n * S := by
    rw [hm₁, ← hS12]; exact Dvd.intro S₂ (by ring)
  have hnS0 : 0 < n * S := Nat.mul_pos hn hS0
  have hτle : τ₁ ≤ ((n * S).divisors.card : ℝ) := by
    rw [hτ₁]; exact_mod_cast Finset.card_le_card (Nat.divisors_subset_of_dvd hnS0.ne' hm₁nS)
  have hm₁le : (m₁ : ℝ) ≤ ((n * S : ℕ) : ℝ) := by exact_mod_cast Nat.le_of_dvd hnS0 hm₁nS
  have hnm₁ : (n : ℝ) ≤ m₁ := by exact_mod_cast Nat.le_mul_of_pos_right n hS₁0
  have hSR : (S₁ : ℝ) ≤ S := by exact_mod_cast Nat.le_of_dvd hS0 (Nat.gcd_dvd_left S n)
  exact final_bound hτ₁1 hτle hlogm₁ hS₁R hSR hm₁le hnm₁ (by exact_mod_cast hn)
    (by exact_mod_cast hnS0) (add_nonneg hX hY)

end

end ArtinPrimitiveRoots.L102K
end

section
/-! Check module: `chk_abs_card_box_mul_sub_mod_le`, the published statement `abs_card_box_mul_sub_mod_le` verbatim, proved from the
development. -/

namespace ArtinPrimitiveRoots

open Finset ArithmeticFunction Real
open scoped ArithmeticFunction.Moebius

end ArtinPrimitiveRoots
end

section
open ArtinPrimitiveRoots
open Finset ArithmeticFunction Real
open scoped ArithmeticFunction.Moebius
theorem solution (n S : ℕ) (hn : 0 < n) (hS0 : 0 < S) (hS : Squarefree S)
    (x₀ y₀ a : ℤ) (ha : IsCoprime a (n : ℤ)) (hax : (S : ℤ) ∣ a - x₀ * y₀) (A₁ B₁ A₂ B₂ : ℤ)
    (h₁ : A₁ ≤ B₁) (h₂ : A₂ ≤ B₂) :
    |(#((Finset.Ico A₁ B₁ ×ˢ Finset.Ico A₂ B₂).filter (fun p : ℤ × ℤ =>
        (S : ℤ) ∣ p.1 - x₀ ∧ (S : ℤ) ∣ p.2 - y₀ ∧ ((n * S : ℕ) : ℤ) ∣ p.1 * p.2 - a)) : ℝ) -
      ((B₁ - A₁ : ℤ) : ℝ) * ((B₂ - A₂ : ℤ) : ℝ) *
        (((∑ l ∈ n.divisors.filter (fun l => Nat.Coprime l S), μ l * ((n / l : ℕ) : ℤ)) : ℤ) : ℝ) /
          ((n : ℝ) * S) ^ 2| ≤
      3 * S * ((n * S : ℕ) : ℝ) ^ ((3 : ℝ) / 4) *
        (((n * S).divisors.card : ℝ) * (1 + Real.log ((n * S : ℕ) : ℝ))) ^ 3 *
        ((((B₁ - A₁ : ℤ) : ℝ) + ((B₂ - A₂ : ℤ) : ℝ) + 2) / n + 1) :=
  L102K.fiber_count n S hn hS0 hS x₀ y₀ a ha hax A₁ B₁ A₂ B₂ h₁ h₂
end
