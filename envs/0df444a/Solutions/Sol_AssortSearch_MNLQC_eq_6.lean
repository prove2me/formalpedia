-- Prove2me | solution 1 for AssortSearch.MNLQC.eq_6
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-13T01:56:59.181992+00:00
-- url     : https://prove2.me/submissions/f0f3a073-cb31-4844-b341-fd4ec006cf65

import Mathlib
import Definitions.Def_AssortSearch_MNLQC_Model

open AssortSearch.MNLQC RetailVariety.Structure

namespace TwentyAnalysis.MNL

variable {n : ℕ} (m : Fin n → ℝ) (c : ℝ → ℝ) (v : Fin n → ℝ) (v0 : ℝ)
  (S : Finset (Fin n)) (j : Fin n)

lemma total_pos (hv : ∀ i, 0 < v i) (hv0 : 0 < v0) : 0 < prefTotal v v0 S := by
  unfold prefTotal
  have hs : 0 ≤ ∑ i ∈ S, v i := Finset.sum_nonneg fun i _ => (hv i).le
  linarith

lemma pref_lt (hv : ∀ i, 0 < v i) (hv0 : 0 < v0) {i : Fin n} (hi : i ∈ S) :
    v i < prefTotal v v0 S := by
  have hs : v i ≤ ∑ k ∈ S, v k := Finset.single_le_sum (fun k _ => (hv k).le) hi
  unfold prefTotal
  linarith

lemma demand_formula (hj : j ∉ S) (x : ℝ) (i : Fin n) :
    demandAdded v v0 S j x i = (if i = j then x else v i) / (x + prefTotal v v0 S) := by
  have hs : ∑ k ∈ S, Function.update v j x k = ∑ k ∈ S, v k := by
    apply Finset.sum_congr rfl
    intro k hk
    exact Function.update_of_ne (by intro h; apply hj; simpa [h] using hk) _ _
  unfold demandAdded share
  rw [Finset.sum_insert hj, hs]
  simp only [Function.update_self]
  rw [show x + ∑ k ∈ S, v k + v0 = x + prefTotal v v0 S by unfold prefTotal; ring]
  by_cases hi : i = j <;> simp [hi, Function.update_of_ne]

lemma canonical (hj : j ∉ S) (x : ℝ) : hm m c v v0 S j x =
    (m j * (x / (x + prefTotal v v0 S)) - c (x / (x + prefTotal v v0 S))) +
    ∑ i ∈ S, (m i * (v i / (x + prefTotal v v0 S)) - c (v i / (x + prefTotal v v0 S))) -
    ∑ i ∈ S, profitS m c v v0 S i := by
  unfold hm lossL profitAdded
  rw [demand_formula v v0 S j hj x j]
  simp only [ite_true]
  have hs : (∑ i ∈ S, (m i * demandAdded v v0 S j x i - c (demandAdded v v0 S j x i))) =
      ∑ i ∈ S, (m i * (v i / (x + prefTotal v v0 S)) - c (v i / (x + prefTotal v v0 S))) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [demand_formula v v0 S j hj x i, if_neg (by intro h; apply hj; simpa [h] using hi)]
  rw [hs]
  ring

lemma ratio_domain (V : ℝ) (hV : 0 < V) (x : ℝ) (hx : 0 ≤ x) : x / (x + V) ∈ Set.Icc (0 : ℝ) 1 := by
  exact ⟨div_nonneg hx (by linarith), (div_le_one (by linarith)).2 (by linarith)⟩

lemma ratio_strict (V : ℝ) (hV : 0 < V) (x : ℝ) (hx : 0 < x) : x / (x + V) ∈ Set.Ioo (0 : ℝ) 1 := by
  exact ⟨div_pos hx (by linarith), (div_lt_one (by linarith)).2 (by linarith)⟩

lemma old_ratio_domain (V w : ℝ) (hV : 0 < V) (hw : 0 < w) (hwV : w < V)
    (x : ℝ) (hx : 0 ≤ x) : w / (x + V) ∈ Set.Ioo (0 : ℝ) 1 := by
  exact ⟨div_pos hw (by linarith), (div_lt_one (by linarith)).2 (by linarith)⟩

lemma profit_concave_cost (hc : ConcaveOn ℝ (Set.Icc 0 1) c) (margin p q u w : ℝ)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : p + q = 1) (hu : u ∈ Set.Icc (0 : ℝ) 1)
    (hw : w ∈ Set.Icc (0 : ℝ) 1) :
    margin * (p * u + q * w) - c (p * u + q * w) ≤
      p * (margin * u - c u) + q * (margin * w - c w) := by
  have h := hc.2 hu hw hp hq hpq
  simp only [smul_eq_mul] at h
  nlinarith

lemma derivative (hv : ∀ i, 0 < v i) (hv0 : 0 < v0) (hj : j ∉ S)
    (hc_diff : DifferentiableOn ℝ c (Set.Ioo 0 1)) (x : ℝ) (hx : 0 < x) :
    HasDerivAt (hm m c v v0 S j)
      (numerator6 m c v v0 S j x / (x + prefTotal v v0 S) ^ 2) x := by
  let V := prefTotal v v0 S
  have hV : 0 < V := total_pos v v0 S hv hv0
  have hD : x + V ≠ 0 := ne_of_gt (by linarith : 0 < x + V)
  have hnew : HasDerivAt (fun y : ℝ => y / (y + V)) (V / (x + V)^2) x := by
    convert (hasDerivAt_id x).div ((hasDerivAt_id x).add_const V) hD using 1 <;> first | rfl | (simp only [id_eq]; ring)
  have hold (w : ℝ) : HasDerivAt (fun y : ℝ => w / (y + V)) (-w / (x + V)^2) x := by
    convert (hasDerivAt_const x w).div ((hasDerivAt_id x).add_const V) hD using 1 <;> first | rfl | (simp only [id_eq]; ring)
  have hcd (y : ℝ) (hy : y ∈ Set.Ioo (0 : ℝ) 1) : HasDerivAt c (deriv c y) y :=
    ((hc_diff y hy).differentiableAt (isOpen_Ioo.mem_nhds hy)).hasDerivAt
  have hn := (hnew.const_mul (m j)).sub ((hcd _ (ratio_strict V hV x hx)).comp x hnew)
  have ho (i : Fin n) (hi : i ∈ S) :=
    ((hold (v i)).const_mul (m i)).sub ((hcd _
      (old_ratio_domain V (v i) hV (hv i) (pref_lt v v0 S hv hv0 hi) x hx.le)).comp x (hold (v i)))
  have hs := (hn.add (HasDerivAt.fun_sum ho)).sub_const (∑ i ∈ S, profitS m c v v0 S i)
  have heq : (fun y => (m j * (y / (y + V)) - c (y / (y + V))) +
      ∑ i ∈ S, (m i * (v i / (y + V)) - c (v i / (y + V))) -
      ∑ i ∈ S, profitS m c v v0 S i) = hm m c v v0 S j := by
    funext y
    exact (canonical m c v v0 S j hj y).symm
  simp only [Pi.add_apply, Pi.sub_apply, Function.comp_apply] at hs
  rw [heq] at hs
  convert hs using 1 <;> try rfl
  unfold numerator6
  dsimp [V]
  simp only [div_mul_eq_mul_div, ← mul_div_assoc, mul_neg, ← Finset.sum_div,
    Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  ring

lemma numerator_mono (hv : ∀ i, 0 < v i) (hv0 : 0 < v0)
    (hc : ConcaveOn ℝ (Set.Icc 0 1) c)
    (hc_diff : DifferentiableOn ℝ c (Set.Ioo 0 1)) :
    MonotoneOn (numerator6 m c v v0 S j) (Set.Ioi 0) := by
  let V := prefTotal v v0 S
  have hV : 0 < V := total_pos v v0 S hv hv0
  have hanti : AntitoneOn (deriv c) (Set.Ioo 0 1) :=
    (hc.subset Set.Ioo_subset_Icc_self (convex_Ioo 0 1)).antitoneOn_deriv
      (fun y hy => (hc_diff y hy).differentiableAt (isOpen_Ioo.mem_nhds hy))
  intro x hx y hy hxy
  have hDx : 0 < x + V := by change 0 < x at hx; linarith
  have hDy : 0 < y + V := by change 0 < y at hy; linarith
  have hrat : x / (x + V) ≤ y / (y + V) := by
    apply (div_le_div_iff₀ hDx hDy).2
    nlinarith
  have hn := mul_le_mul_of_nonneg_right
    (hanti (ratio_strict V hV x hx) (ratio_strict V hV y hy) hrat) hV.le
  have ho : ∀ i ∈ S, deriv c (v i / (x + V)) * v i ≤ deriv c (v i / (y + V)) * v i := by
    intro i hi
    apply mul_le_mul_of_nonneg_right _ (hv i).le
    apply hanti
      (old_ratio_domain V (v i) hV (hv i) (pref_lt v v0 S hv hv0 hi) y hy.le)
      (old_ratio_domain V (v i) hV (hv i) (pref_lt v v0 S hv hv0 hi) x hx.le)
    exact div_le_div_of_nonneg_left (hv i).le hDx (by linarith)
  have hs := Finset.sum_le_sum ho
  unfold numerator6
  dsimp [V] at hn hs
  linarith

lemma sign_pattern (hv : ∀ i, 0 < v i) (hv0 : 0 < v0) (hj : j ∉ S)
    (hc : ConcaveOn ℝ (Set.Icc 0 1) c)
    (hc_diff : DifferentiableOn ℝ c (Set.Ioo 0 1)) :
    (∀ x : ℝ, 0 < x → deriv (hm m c v v0 S j) x ≤ 0) ∨
      ∃ a : ℝ, 0 ≤ a ∧
        (∀ x : ℝ, 0 < x → x < a → deriv (hm m c v v0 S j) x ≤ 0) ∧
        (∀ x : ℝ, a < x → 0 ≤ deriv (hm m c v v0 S j) x) := by
  have hd (x : ℝ) (hx : 0 < x) := (derivative m c v v0 S j hv hv0 hj hc_diff x hx).deriv
  have hmono := numerator_mono m c v v0 S j hv hv0 hc hc_diff
  by_cases hall : ∀ x : ℝ, 0 < x → numerator6 m c v v0 S j x ≤ 0
  · left
    intro x hx
    rw [hd x hx]
    exact div_nonpos_of_nonpos_of_nonneg (hall x hx) (sq_nonneg _)
  · right
    push_neg at hall
    let A : Set ℝ := {x | 0 < x ∧ 0 < numerator6 m c v v0 S j x}
    have hA : A.Nonempty := by obtain ⟨x, hx, hn⟩ := hall; exact ⟨x, hx, hn⟩
    have hAb : BddBelow A := ⟨0, fun x hx => hx.1.le⟩
    have ha : 0 ≤ sInf A := le_csInf hA (fun x hx => hx.1.le)
    refine ⟨sInf A, ha, ?_, ?_⟩
    · intro x hx hxa
      rw [hd x hx]
      apply div_nonpos_of_nonpos_of_nonneg _ (sq_nonneg _)
      by_contra hn
      have hm : x ∈ A := ⟨hx, lt_of_not_ge hn⟩
      exact (not_le_of_gt hxa) (csInf_le hAb hm)
    · intro x hax
      have hx : 0 < x := ha.trans_lt hax
      rw [hd x hx]
      obtain ⟨y, hy, hyx⟩ := exists_lt_of_csInf_lt hA hax
      exact div_nonneg (hy.2.le.trans (hmono hy.1 hx hyx.le)) (sq_nonneg _)

end TwentyAnalysis.MNL

theorem solution
    {n : ℕ} (m : Fin n → ℝ) (c : ℝ → ℝ) (v : Fin n → ℝ) (v0 : ℝ)
    (S : Finset (Fin n)) (j : Fin n)
    (hv : ∀ i, 0 < v i) (hv0 : 0 < v0)
    (hc_concave : ConcaveOn ℝ (Set.Icc 0 1) c) (hc_mono : MonotoneOn c (Set.Icc 0 1))
    (hj : j ∉ S)
    (hc_diff : DifferentiableOn ℝ c (Set.Ioo 0 1)) (x : ℝ) (hx : 0 < x) :
    HasDerivAt (hm m c v v0 S j)
      (numerator6 m c v v0 S j x / (x + prefTotal v v0 S) ^ 2) x := by
  exact TwentyAnalysis.MNL.derivative m c v v0 S j hv hv0 hj hc_diff x hx
