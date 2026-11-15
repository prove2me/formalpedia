-- Prove2me | Definitions.Def_RPLib_S3_KHC
-- name    : RPLib_S3_KHC
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T15:36:36.565506+00:00
-- url     : https://prove2.me/theorems/14ccd54d-0572-4b97-b809-19b215c02f75
-- title:
--   Kronecker-Hurwitz class number relation: splitting by the sign of `S`, and the one-variable sums
-- statement:
--   Splitting by the sign of `S`, and the one-variable sums.
--
--   * `Yn n` : determinant `n`, `R > 0`; `Y_box` : the support of `wN` on `Yn n` lies in the box `4n`;
--   * **`splitY`** : `∑ᶠ_{Yn n} wN = ∑ᶠ_{Xn n} (wN + wN ∘ mS) + ∑ᶠ_{Yn n, S = 0} wN` (`mS` maps `Xn n` onto `S < 0`);
--   * `fs_range`, `fs_red`, `fs_div` : finsum reindexing helpers;
--   * `sum1`, `sum2` : the one-variable sums of the root terms.
--
--   **Formalization note.** Library module of an elementary formalization of the Kronecker-Hurwitz class number relation $\sum_{t^2 \le 4n} H(4n - t^2) = 2\sigma(n) - \sum_{d \mid n} \min(d, n/d)$ (Popa-Zagier's tessellation proof, recast as a telescoping identity over integer matrices of determinant $n$), part of a formalization of the Ramanujan-Petersson conjecture in weight two. It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   A. A. Popa and D. Zagier, A combinatorial refinement of the Kronecker-Hurwitz class number relation, arXiv:1604.02822 (2016); L. Kronecker, Über die Anzahl der verschiedenen Classen quadratischer Formen von negativer Determinante, J. reine angew. Math. 57 (1860), 248-255; A. Hurwitz, Über Relationen zwischen Classenanzahlen binärer quadratischer Formen von negativer Determinante, Math. Ann. 25 (1885), 157-196; H. Cohen, A Course in Computational Algebraic Number Theory, GTM 138, Springer 1993, Section 5.3

import Mathlib
import Definitions.Def_RPLib_S3_KHB

/-!
# S3-KH, part C: splitting by the sign of `S`, and the one-variable sums

* `Yn n` : determinant `n`, `R > 0`; `Y_box` : the support of `wN` on `Yn n` lies in the box `4n`;
* **`splitY`** : `∑ᶠ_{Yn n} wN = ∑ᶠ_{Xn n} (wN + wN ∘ mS) + ∑ᶠ_{Yn n, S = 0} wN` (`mS` maps `Xn n` onto `S < 0`);
* `fs_range`, `fs_red`, `fs_div` : finsum reindexing helpers;
* `sum1`, `sum2` : the one-variable sums of the root terms.
-/

set_option autoImplicit false

namespace RamanujanPetersson.S3.KH

/-- Determinant `n`, positive lower-left entry. -/
def Yn (n : ℤ) : Set (ℤ × ℤ × ℤ × ℤ) := {N | det4 N = n ∧ 0 < N.2.2.1}

lemma Xn_sub (n : ℤ) : Xn n ⊆ Yn n := fun _ h => ⟨h.1, h.2.1⟩

lemma Y_box {n : ℤ} (hn : 0 < n) {N : ℤ × ℤ × ℤ × ℤ} (hN : N ∈ Yn n) (h : wN N ≠ 0) :
    N ∈ box (4 * n) := by
  obtain ⟨P, Q, R, S⟩ := N
  obtain ⟨hd, hR⟩ := hN
  simp only [det4] at hd hR
  obtain ⟨h1, h2, h3⟩ := wt_ne hR h
  simp only at h1 h2 h3
  have hC : 3 * (-Q) * R ≤ 4 * n := by nlinarith [sq_nonneg (P + S), mul_le_mul_of_nonneg_left h2 h1]
  have hCn : -Q ≤ 4 * n := by nlinarith
  have ht : (P + S) ^ 2 ≤ 4 * n := by nlinarith [mul_le_mul_of_nonneg_left h2 h1]
  have ht' : P + S ≤ 4 * n ∧ -(4 * n) ≤ P + S := by constructor <;> nlinarith [sq_nonneg (P + S - 1), sq_nonneg (P + S + 1)]
  simp only [box, Finset.mem_product, Finset.mem_Icc]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> omega

lemma Y_fin {n : ℤ} (hn : 0 < n) {s : Set (ℤ × ℤ × ℤ × ℤ)} (hs : s ⊆ Yn n) :
    (Function.support (s.indicator wN)).Finite := by
  classical
  refine (box (4 * n)).finite_toSet.subset fun N hN => ?_
  rw [Function.mem_support] at hN
  by_cases hX : N ∈ s
  · rw [Set.indicator_of_mem hX] at hN; exact Y_box hn (hs hX) hN
  · rw [Set.indicator_of_notMem hX] at hN; exact absurd rfl hN

/-- `N ↦ N S` as an equivalence. -/
def eS : (ℤ × ℤ × ℤ × ℤ) ≃ (ℤ × ℤ × ℤ × ℤ) where
  toFun := mS
  invFun N := (-N.2.1, N.1, -N.2.2.2, N.2.2.1)
  left_inv N := by rcases N with ⟨a, b, c, d⟩; simp [mS]
  right_inv N := by rcases N with ⟨a, b, c, d⟩; simp [mS]

lemma mem_S {n : ℤ} (N : ℤ × ℤ × ℤ × ℤ) :
    mS N ∈ Yn n ∩ {N | N.2.2.2 < 0} ↔ N ∈ Xn n := by
  rcases N with ⟨P, Q, R, S⟩
  simp only [Xn, Yn, mS, det4, Set.mem_inter_iff, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨by linarith, by linarith, h2⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨⟨by linarith, h3⟩, by linarith⟩

/-- **Split by the sign of `S`.** -/
theorem splitY {n : ℤ} (hn : 0 < n) :
    ∑ᶠ N, (Yn n).indicator wN N =
      ∑ᶠ N, (Xn n).indicator (fun N => wN N + wN (mS N)) N +
        ∑ᶠ N, (Yn n ∩ {N | N.2.2.2 = 0}).indicator wN N := by
  classical
  set g1 := (Yn n ∩ {N : ℤ × ℤ × ℤ × ℤ | N.2.2.2 < 0}).indicator wN with hg1
  have hpt : ∀ N, (Xn n).indicator (fun N => wN N + wN (mS N)) N = (Xn n).indicator wN N + g1 (eS N) := by
    intro N
    have e := mem_S (n := n) N
    simp only [hg1, eS, Equiv.coe_fn_mk]
    by_cases hX : N ∈ Xn n
    · rw [Set.indicator_of_mem hX, Set.indicator_of_mem hX, Set.indicator_of_mem (e.2 hX)]
    · rw [Set.indicator_of_notMem hX, Set.indicator_of_notMem hX,
        Set.indicator_of_notMem (fun h => hX (e.1 h)), add_zero]
  have hsp : ∀ N, (Yn n).indicator wN N =
      (Xn n).indicator wN N + g1 N + (Yn n ∩ {N | N.2.2.2 = 0}).indicator wN N := by
    intro N
    simp only [hg1, Set.indicator_apply, Set.mem_inter_iff, Set.mem_ofPred_eq, Xn, Yn]
    by_cases hY : det4 N = n ∧ 0 < N.2.2.1
    · rcases lt_trichotomy N.2.2.2 0 with h | h | h
      · simp [hY, h, h.ne, not_lt.2 h.le]
      · simp [hY, h]
      · simp [hY, h, h.ne', not_lt.2 h.le]
    · have : ¬ (det4 N = n ∧ 0 < N.2.2.1 ∧ 0 < N.2.2.2) := fun h => hY ⟨h.1, h.2.1⟩
      simp [hY, this]
  have hgf : (Function.support fun N => g1 (eS N)).Finite :=
    (Y_fin hn Set.inter_subset_left).preimage eS.injective.injOn
  rw [finsum_congr hpt, finsum_add_distrib (Y_fin hn (Xn_sub n)) hgf, finsum_comp_equiv eS (f := g1),
    finsum_congr hsp,
    finsum_add_distrib (((Y_fin hn (Xn_sub n)).union (Y_fin hn Set.inter_subset_left)).subset
      (Function.support_add _ _)) (Y_fin hn Set.inter_subset_left),
    finsum_add_distrib (Y_fin hn (Xn_sub n)) (Y_fin hn Set.inter_subset_left)]

/-! ## Reindexing helpers -/

lemma fs_range {α β : Type*} {g : α → β} (hg : Function.Injective g) (f : β → ℚ)
    (h : Function.support f ⊆ Set.range g) : ∑ᶠ a, f (g a) = ∑ᶠ b, f b := by
  rw [← finsum_mem_range hg, ← finsum_mem_univ f]
  exact finsum_mem_inter_support_eq' f _ _ (fun x hx => ⟨fun _ => Set.mem_univ _, fun _ => h hx⟩)

lemma fs_red (F : ℤ × ℤ × ℤ × ℤ → ℚ) (g : ℤ × ℤ → ℤ × ℤ × ℤ × ℤ) (hg : Function.Injective g)
    (hF : Function.support F ⊆ Set.range g) (hfin : (Function.support F).Finite) :
    ∑ᶠ N, F N = ∑ᶠ (d : ℤ) (P : ℤ), F (g (d, P)) := by
  rw [← fs_range hg F hF]
  exact finsum_curry (fun x => F (g x)) (hfin.preimage hg.injOn)

lemma fs_div {n : ℕ} (hn : 0 < n) (G : ℤ → ℚ) :
    ∑ᶠ d : ℤ, (if 0 < d ∧ d ∣ (n : ℤ) then G d else 0) = ∑ d ∈ n.divisors, G d := by
  classical
  rw [finsum_eq_sum_of_support_subset (s := n.divisors.map Nat.castEmbedding) _ ?_, Finset.sum_map]
  · refine Finset.sum_congr rfl fun d hd => ?_
    have h1 := Nat.mem_divisors.1 hd
    have e : (Nat.castEmbedding d : ℤ) = (d : ℤ) := rfl
    rw [e, if_pos ⟨by exact_mod_cast Nat.pos_of_mem_divisors hd, Int.natCast_dvd_natCast.2 h1.1⟩]
  · intro d hd
    rw [Function.mem_support] at hd
    have hc : 0 < d ∧ d ∣ (n : ℤ) := by
      by_contra h; exact hd (if_neg h)
    have e : ((d.toNat : ℕ) : ℤ) = d := Int.toNat_of_nonneg hc.1.le
    simp only [Finset.coe_map, Set.mem_image, Finset.mem_coe, Nat.mem_divisors]
    refine ⟨d.toNat, ⟨Int.natCast_dvd_natCast.1 (e.symm ▸ hc.2), hn.ne'⟩, e⟩

/-! ## One-variable sums -/

lemma icc_sum (a b : ℤ) (h : a < b) :
    ∑ P ∈ Finset.Icc a b, ((1 : ℚ) - (if P = a then 1 / 2 else 0) - (if P = b then 1 / 2 else 0)) =
      b - a := by
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.sum_ite_eq',
    Finset.sum_ite_eq', if_pos (Finset.mem_Icc.2 ⟨le_rfl, h.le⟩), if_pos (Finset.mem_Icc.2 ⟨h.le, le_rfl⟩),
    Int.card_Icc, nsmul_eq_mul, mul_one]
  have e : (((b + 1 - a).toNat : ℕ) : ℚ) = ((((b + 1 - a).toNat : ℕ) : ℤ) : ℚ) := by norm_cast
  rw [e, Int.toNat_of_nonneg (by omega)]
  push_cast; ring

/-- The `R = S` root sum in one variable. -/
lemma sum1 (L : ℤ) : ∑ᶠ P : ℤ, (hs P * hs (L - P) - cor P (L - P) / 12) =
    (if 0 < L then (L : ℚ) else 0) + (if L = 0 then 1 / 6 else 0) := by
  rcases lt_trichotomy L 0 with hL | hL | hL
  · rw [if_neg (by omega), if_neg (by omega), add_zero]
    refine (finsum_congr fun P => ?_).trans finsum_zero
    rcases le_or_gt 0 P with h | h
    · rw [hs_neg (by omega : L - P < 0), cor_r (by omega : L - P ≠ 0)]; ring
    · rw [hs_neg h, cor_l (by omega : P ≠ 0)]; ring
  · subst hL
    rw [if_neg (lt_irrefl 0), if_pos rfl, zero_add, finsum_eq_single _ 0]
    · rw [hs_zero rfl, sub_zero, hs_zero rfl, cor_one rfl rfl]; norm_num
    · intro P hP
      rcases lt_or_gt_of_ne hP with h | h
      · rw [hs_neg h, cor_l hP]; ring
      · rw [hs_neg (by omega : 0 - P < 0), cor_l hP]; ring
  · rw [if_pos hL, if_neg hL.ne', add_zero]
    have hpt : ∀ P ∈ Finset.Icc 0 L, hs P * hs (L - P) - cor P (L - P) / 12 =
        1 - (if P = 0 then 1 / 2 else 0) - (if P = L then 1 / 2 else 0) := by
      intro P hP
      have hP' := Finset.mem_Icc.1 hP
      rcases lt_trichotomy P 0 with h0 | h0 | h0 <;> rcases lt_trichotomy P L with h1 | h1 | h1 <;>
      first
      | omega
      | (simp (disch := omega) only [hs_pos, hs_zero, hs_neg, cor_one, cor_l, cor_r, if_pos, if_neg] <;>
          norm_num)
    rw [finsum_eq_sum_of_support_subset _ (s := Finset.Icc 0 L) ?_]
    · rw [Finset.sum_congr rfl hpt, icc_sum 0 L hL]; push_cast; ring
    · intro P hP
      rw [Function.mem_support] at hP
      rw [Finset.coe_Icc, Set.mem_Icc]
      by_contra hc
      apply hP
      rcases (by omega : P < 0 ∨ L < P) with h | h
      · rw [hs_neg h, cor_l (by omega : P ≠ 0)]; ring
      · rw [hs_neg (by omega : L - P < 0), cor_r (by omega : L - P ≠ 0)]; ring

/-- The `S = 0` root sum in one variable. -/
lemma sum2 (δ C : ℤ) (hδ : 0 < δ) :
    ∑ᶠ P : ℤ, wt δ (0 - P) C = δ * hs (C - δ) - (if C = δ then 1 / 12 else 0) := by
  classical
  rw [finsum_eq_sum_of_support_subset _ (s := Finset.Icc (-δ) 0) ?_]
  · have hpt : ∀ P ∈ Finset.Icc (-δ) 0, wt δ (0 - P) C =
        hs (C - δ) * (1 - (if P = -δ then 1 / 2 else 0) - (if P = 0 then 1 / 2 else 0)) -
          (if P = -δ then (if C = δ then 1 / 12 else 0) else 0) := by
      intro P hP
      have hP' := Finset.mem_Icc.1 hP
      simp only [wt]
      rcases lt_trichotomy P (-δ) with h0 | h0 | h0 <;> rcases lt_trichotomy P 0 with h1 | h1 | h1 <;>
      rcases lt_trichotomy C δ with h2 | h2 | h2 <;>
      first
      | omega
      | (simp (disch := omega) only [hs_pos, hs_zero, hs_neg, cor_one, cor_l, cor_r, if_pos, if_neg] <;>
          norm_num)
    rw [Finset.sum_congr rfl hpt, Finset.sum_sub_distrib, ← Finset.mul_sum, icc_sum (-δ) 0 (by omega),
      Finset.sum_ite_eq', if_pos (Finset.mem_Icc.2 ⟨le_rfl, by omega⟩)]
    push_cast; ring
  · intro P hP
    rw [Function.mem_support] at hP
    rw [Finset.coe_Icc, Set.mem_Icc]
    by_contra hc
    apply hP
    simp only [wt]
    rcases (by omega : 0 < P ∨ P < -δ) with h | h
    · rw [hs_neg (by omega : 0 - P < 0), cor_l (by omega : δ - (0 - P) ≠ 0)]; ring
    · rw [hs_neg (by omega : δ - (0 - P) < 0), cor_l (by omega : δ - (0 - P) ≠ 0)]; ring

end RamanujanPetersson.S3.KH


