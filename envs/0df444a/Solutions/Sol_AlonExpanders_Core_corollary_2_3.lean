-- Prove2me | solution 1 for AlonExpanders.Core.corollary_2_3
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T05:56:53.781551+00:00
-- url     : https://prove2.me/submissions/98cc441c-22ee-4c0c-8d2a-bbe3bb6155f5

import Mathlib
import Definitions.Def_AlonExpanders_Core_IsEnlarger
import Definitions.Def_AlonExpanders_Core_IsMagnifier

open Matrix Finset

namespace AlonExpanders.Core

lemma c23_expand {V : Type} [Fintype V] [DecidableEq V] (A : Matrix V V ℝ) (hA : A.IsHermitian)
    (f : V → ℝ) (k : V) :
    ∑ i, (∑ j, hA.eigenvectorBasis i j * f j) * hA.eigenvectorBasis i k = f k := by
  have h := hA.eigenvectorBasis.sum_repr' (WithLp.toLp 2 f)
  have h2 := congrArg (fun x => x k) h
  simp only at h2
  rw [← h2]
  simp [PiLp.inner_apply, mul_comm]

lemma c23_unit {V : Type} [Fintype V] [DecidableEq V] (A : Matrix V V ℝ) (hA : A.IsHermitian)
    (i : V) : ∑ j, hA.eigenvectorBasis i j ^ 2 = 1 := by
  have h := hA.eigenvectorBasis.orthonormal.1 i
  have h2 : ‖hA.eigenvectorBasis i‖ ^ 2 = 1 := by rw [h]; norm_num
  rw [EuclideanSpace.norm_sq_eq] at h2
  simpa using h2

lemma c23_quad {V : Type} [Fintype V] [DecidableEq V] (A : Matrix V V ℝ) (hA : A.IsHermitian)
    (g : V → ℝ) :
    g ⬝ᵥ (A *ᵥ g) = ∑ i, hA.eigenvalues i * (∑ j, hA.eigenvectorBasis i j * g j) ^ 2 ∧
    ∑ k, g k ^ 2 = ∑ i, (∑ j, hA.eigenvectorBasis i j * g j) ^ 2 := by
  set c : V → ℝ := fun i => ∑ j, hA.eigenvectorBasis i j * g j with hc
  have hg : ∀ k, g k = ∑ i, c i * hA.eigenvectorBasis i k := fun k => (c23_expand A hA g k).symm
  have hmul : ∀ k, (A *ᵥ g) k = ∑ i, c i * hA.eigenvalues i * hA.eigenvectorBasis i k := by
    intro k
    have : ∀ i, (A *ᵥ ⇑(hA.eigenvectorBasis i)) k = hA.eigenvalues i * hA.eigenvectorBasis i k :=
      fun i => by rw [hA.mulVec_eigenvectorBasis i]; rfl
    simp only [mulVec, dotProduct] at this ⊢
    simp_rw [hg, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_assoc, ← this i, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  constructor
  · simp only [dotProduct, hmul]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [sq, hc]
    simp only
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  · have : ∀ k, g k ^ 2 = ∑ i, c i * hA.eigenvectorBasis i k * g k := by
      intro k; rw [sq]; nth_rewrite 1 [hg k]
      rw [Finset.sum_mul]
    simp_rw [this]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [sq, hc]; simp only
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring


lemma c23_E {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (g : V → ℝ) : g ⬝ᵥ (G.lapMatrix ℝ *ᵥ g) =
      (∑ u, ∑ v, if G.Adj u v then (g u - g v) ^ 2 else 0) / 2 := by
  rw [← Matrix.toLinearMap₂'_apply', SimpleGraph.lapMatrix_toLinearMap₂']

lemma c23_rayleigh {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hn : 2 ≤ Fintype.card V) (f : V → ℝ) :
    AlonMilman.Diameter.lambda1 G * (∑ v, f v ^ 2 - (∑ v, f v) ^ 2 / Fintype.card V) ≤
      (∑ u, ∑ v, if G.Adj u v then (f u - f v) ^ 2 else 0) / 2 := by
  set hQ := G.isHermitian_lapMatrix ℝ
  set n := Fintype.card V with hn_def
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  set e : Fin n ≃ V := Fintype.equivOfCardEq (Fintype.card_fin _)
  set i0 : V := e ⟨n - 1, by omega⟩
  have hl : AlonMilman.Diameter.lambda1 G = hQ.eigenvalues₀ ⟨n - 2, by omega⟩ := by
    unfold AlonMilman.Diameter.lambda1; rw [dif_pos hn]
  have hlam : ∀ i, i ≠ i0 → AlonMilman.Diameter.lambda1 G ≤ hQ.eigenvalues i := by
    intro i hi
    rw [hl]
    show hQ.eigenvalues₀ ⟨n - 2, by omega⟩ ≤ hQ.eigenvalues₀ (e.symm i)
    apply hQ.eigenvalues₀_antitone
    have h1 : e.symm i ≠ ⟨n - 1, by omega⟩ := by
      intro h; apply hi; show i = e ⟨n - 1, by omega⟩; rw [← h]; simp
    have h2 := (e.symm i).isLt
    have h3 : (e.symm i).val ≠ n - 1 := fun h => h1 (Fin.ext h)
    show (e.symm i).val ≤ n - 2
    omega
  have hnn : 0 ≤ hQ.eigenvalues i0 := (SimpleGraph.posSemidef_lapMatrix ℝ G).eigenvalues_nonneg i0
  have hE0 : ∀ g : V → ℝ, 0 ≤ (∑ u, ∑ v, if G.Adj u v then (g u - g v) ^ 2 else 0) / 2 := by
    intro g
    apply div_nonneg _ (by norm_num)
    apply Finset.sum_nonneg; intro u _; apply Finset.sum_nonneg; intro v _
    split_ifs <;> positivity
  -- key bound
  have K : ∀ g : V → ℝ, AlonMilman.Diameter.lambda1 G *
      (∑ k, g k ^ 2 - (∑ j, hQ.eigenvectorBasis i0 j * g j) ^ 2) ≤
      (∑ u, ∑ v, if G.Adj u v then (g u - g v) ^ 2 else 0) / 2 := by
    intro g
    rw [← c23_E, (c23_quad _ hQ g).1, (c23_quad _ hQ g).2]
    set c : V → ℝ := fun i => ∑ j, hQ.eigenvectorBasis i j * g j
    have : ∀ i, AlonMilman.Diameter.lambda1 G * c i ^ 2 -
        (if i = i0 then AlonMilman.Diameter.lambda1 G * c i ^ 2 else 0) ≤
        hQ.eigenvalues i * c i ^ 2 := by
      intro i
      split_ifs with h
      · subst h; simp only [sub_self]; exact mul_nonneg hnn (sq_nonneg _)
      · simp only [sub_zero]; exact mul_le_mul_of_nonneg_right (hlam i h) (sq_nonneg _)
    have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => this i)
    rw [Finset.sum_sub_distrib, Finset.sum_ite_eq' Finset.univ i0, if_pos (Finset.mem_univ _),
      ← Finset.mul_sum] at hs
    show AlonMilman.Diameter.lambda1 G * (∑ i, c i ^ 2 - c i0 ^ 2) ≤ _
    linarith
  rcases le_or_gt (AlonMilman.Diameter.lambda1 G) 0 with hl0 | hl0
  · have hcs : (∑ v, f v) ^ 2 ≤ n * ∑ v, f v ^ 2 := by
      have := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := f)
      simpa using this
    have : 0 ≤ ∑ v, f v ^ 2 - (∑ v, f v) ^ 2 / n := by
      rw [sub_nonneg, div_le_iff₀ hnR]; linarith
    exact (mul_nonpos_of_nonpos_of_nonneg hl0 this).trans (hE0 f)
  set u : V → ℝ := fun j => hQ.eigenvectorBasis i0 j
  set q : ℝ := ∑ j, u j
  have hq1 : (n : ℝ) ≤ q ^ 2 := by
    have h := K (fun _ => 1)
    simp only [sub_self, sq, mul_zero, ite_self, Finset.sum_const_zero, zero_div, mul_one,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h
    have : (n : ℝ) - q * q ≤ 0 := by
      by_contra hc; push_neg at hc
      have := mul_pos hl0 hc; linarith
    nlinarith
  have hq2 : q ^ 2 ≤ n := by
    have := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := u)
    have hu := c23_unit _ hQ i0
    simp only [Finset.card_univ] at this
    rw [hu] at this; simpa [q] using this
  have hq0 : q ≠ 0 := by
    intro h; rw [h] at hq1; norm_num at hq1; linarith
  set p : ℝ := ∑ j, u j * f j
  set s : ℝ := p / q
  have hg := K (fun k => f k - s)
  have hc0 : ∑ j, hQ.eigenvectorBasis i0 j * (f j - s) = 0 := by
    have : ∑ j, hQ.eigenvectorBasis i0 j * (f j - s) = p - s * q := by
      simp only [mul_sub, Finset.sum_sub_distrib, p, q, u, Finset.mul_sum]
      congr 1; refine Finset.sum_congr rfl fun j _ => by ring
    rw [this]; simp only [s]; field_simp; ring
  rw [hc0] at hg
  simp only [sub_sub_sub_cancel_right] at hg
  have hvar : ∑ v, f v ^ 2 - (∑ v, f v) ^ 2 / n ≤ ∑ k, (f k - s) ^ 2 := by
    have : ∑ k, (f k - s) ^ 2 = ∑ v, f v ^ 2 - 2 * s * ∑ v, f v + n * s ^ 2 := by
      simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul, Finset.mul_sum]
      congr 1; congr 1; refine Finset.sum_congr rfl fun j _ => by ring
    rw [this]
    have : 0 ≤ (n * s - ∑ v, f v) ^ 2 / n := div_nonneg (sq_nonneg _) hnR.le
    have e2 : (n * s - ∑ v, f v) ^ 2 / n = n * s ^ 2 - 2 * s * ∑ v, f v + (∑ v, f v) ^ 2 / n := by
      field_simp; ring
    linarith
  calc AlonMilman.Diameter.lambda1 G * (∑ v, f v ^ 2 - (∑ v, f v) ^ 2 / n)
      ≤ AlonMilman.Diameter.lambda1 G * ∑ k, (f k - s) ^ 2 :=
        mul_le_mul_of_nonneg_left hvar hl0.le
    _ ≤ _ := by simpa using hg


theorem c23_core {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (n d : ℕ) (ε : ℝ) (hε : 0 ≤ ε) (hG : IsEnlarger G n d ε) :
    IsMagnifier G n d (2 * ε / ((d : ℝ) + 2 * ε)) := by
  obtain ⟨hcard, hdeg, hlam⟩ := hG
  refine ⟨hcard, hdeg, ?_⟩
  intro X hX
  rcases hε.eq_or_lt with h0 | hεp
  · rw [← h0]; simp
  rcases lt_or_ge n 2 with hn2 | hn2
  · have : X.card = 0 := by omega
    simp [this]
  set B : Finset V := Finset.univ.filter (fun v => v ∉ X ∧ ∃ x ∈ X, G.Adj x v) with hB
  have hset : AKSSorting.Core.neighbours G X \ (X : Set V) = (B : Set V) := by
    ext v; simp [AKSSorting.Core.neighbours, B]; tauto
  rw [hset, Set.ncard_coe_finset]
  have hdisj : ∀ v, v ∈ B → v ∉ X := fun v hv => by simp [B] at hv; exact hv.1
  set f : V → ℝ := fun v => (if v ∈ X then 1 else 0) + (if v ∈ B then 1 / 2 else 0) with hf
  have hsum : ∑ v, f v = X.card + B.card / 2 := by
    simp only [f, Finset.sum_add_distrib]
    rw [Finset.sum_boole, Finset.sum_ite_mem]
    simp [Finset.filter_mem_eq_inter, div_eq_mul_inv]
  have hsq : ∑ v, f v ^ 2 = X.card + B.card / 4 := by
    have : ∀ v, f v ^ 2 = (if v ∈ X then 1 else 0) + (if v ∈ B then 1 / 4 else 0) := by
      intro v
      by_cases hX : v ∈ X <;> by_cases hBv : v ∈ B <;> simp [f, hX, hBv]
      · exact absurd hX (hdisj v hBv)
      · norm_num
    simp only [this, Finset.sum_add_distrib]
    rw [Finset.sum_boole, Finset.sum_ite_mem]
    simp [Finset.filter_mem_eq_inter, div_eq_mul_inv]
  have hpt : ∀ u v, (if G.Adj u v then (f u - f v) ^ 2 else 0) ≤
      (if G.Adj u v then (if u ∈ B then 1 / 4 else 0) else 0) +
      (if G.Adj u v then (if v ∈ B then 1 / 4 else 0) else 0) := by
    intro u v
    by_cases ha : G.Adj u v
    · simp only [if_pos ha]
      have hvB : u ∈ X → v ∉ X → v ∈ B := fun hu hv => by
        simp [B]; exact ⟨hv, u, hu, ha⟩
      have huB : v ∈ X → u ∉ X → u ∈ B := fun hv hu => by
        simp [B]; exact ⟨hu, v, hv, ha.symm⟩
      have fval : ∀ w, (w ∈ X ∧ w ∉ B ∧ f w = 1) ∨ (w ∉ X ∧ w ∈ B ∧ f w = 1 / 2) ∨
          (w ∉ X ∧ w ∉ B ∧ f w = 0) := by
        intro w
        by_cases hX : w ∈ X
        · have hB : w ∉ B := fun h => hdisj w h hX
          left; exact ⟨hX, hB, by simp [f, hX, hB]⟩
        · by_cases hB : w ∈ B
          · right; left; exact ⟨hX, hB, by simp [f, hX, hB]⟩
          · right; right; exact ⟨hX, hB, by simp [f, hX, hB]⟩
      rcases fval u with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ <;>
      rcases fval v with ⟨k1, k2, k3⟩ | ⟨k1, k2, k3⟩ | ⟨k1, k2, k3⟩ <;>
      simp only [h3, k3, h2, k2, if_true, if_false] <;> try norm_num
      · exact absurd (hvB h1 k1) k2
      · exact absurd (huB k1 h1) h2
    · simp [ha]
  have hS1 : ∑ u, ∑ v, (if G.Adj u v then (if u ∈ B then (1 / 4 : ℝ) else 0) else 0) ≤
      d * B.card / 4 := by
    have : ∀ u, ∑ v, (if G.Adj u v then (if u ∈ B then (1 / 4 : ℝ) else 0) else 0) =
        (if u ∈ B then 1 / 4 else 0) * G.degree u := by
      intro u
      rw [SimpleGraph.degree_eq_sum_if_adj (G := G) (R := ℝ), Finset.mul_sum]
      refine Finset.sum_congr rfl fun v _ => ?_
      split_ifs <;> simp
    simp only [this]
    have h2 : ∀ u, (if u ∈ B then (1 / 4 : ℝ) else 0) * G.degree u ≤
        (if u ∈ B then (d : ℝ) / 4 else 0) := by
      intro u
      have hd : (G.degree u : ℝ) ≤ d := by exact_mod_cast (G.degree_le_maxDegree u).trans hdeg
      split_ifs <;> linarith
    refine (Finset.sum_le_sum fun u _ => h2 u).trans ?_
    rw [Finset.sum_ite_mem]; simp [Finset.filter_mem_eq_inter]; ring_nf; rfl
  have hS2 : ∑ u, ∑ v, (if G.Adj u v then (if v ∈ B then (1 / 4 : ℝ) else 0) else 0) =
      ∑ u, ∑ v, (if G.Adj u v then (if u ∈ B then (1 / 4 : ℝ) else 0) else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
    by_cases h : G.Adj u v
    · simp [h, h.symm]
    · have h' : ¬ G.Adj v u := fun h' => h h'.symm
      simp [h, h']
  have hE : (∑ u, ∑ v, if G.Adj u v then (f u - f v) ^ 2 else 0) / 2 ≤ d * B.card / 4 := by
    have := Finset.sum_le_sum fun u (_ : u ∈ Finset.univ) =>
      Finset.sum_le_sum fun v (_ : v ∈ Finset.univ) => hpt u v
    simp only [Finset.sum_add_distrib] at this
    rw [hS2] at this
    linarith
  have hR := c23_rayleigh G (by omega) f
  rw [hsum, hsq, hcard] at hR
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hXB : X.card + B.card ≤ n := by
    rw [← hcard, ← Finset.card_union_of_disjoint]
    · exact Finset.card_le_univ _
    · rw [Finset.disjoint_left]; intro v hv hvB; exact hdisj v hvB hv
  have hx2 : 2 * ((X.card : ℕ) : ℝ) ≤ n := by exact_mod_cast hX
  have hxb : ((X.card : ℕ) : ℝ) + ((B.card : ℕ) : ℝ) ≤ n := by exact_mod_cast hXB
  set x : ℝ := ((X.card : ℕ) : ℝ)
  set b : ℝ := ((B.card : ℕ) : ℝ)
  have hx0 : 0 ≤ x := Nat.cast_nonneg _
  have hb0 : 0 ≤ b := Nat.cast_nonneg _
  have hvar0 : 0 ≤ x + b / 4 - (x + b / 2) ^ 2 / n := by
    rw [sub_nonneg, div_le_iff₀ hnR]; nlinarith
  have h1 : ε * (x + b / 4 - (x + b / 2) ^ 2 / n) ≤ d * b / 4 :=
    (mul_le_mul_of_nonneg_right hlam hvar0).trans (hR.trans hE)
  have h2 : ε * (4 * x * n + b * n - (2 * x + b) ^ 2) ≤ d * b * n := by
    have e : ε * (x + b / 4 - (x + b / 2) ^ 2 / n) * (4 * n) =
        ε * (4 * x * n + b * n - (2 * x + b) ^ 2) := by field_simp; ring
    have := mul_le_mul_of_nonneg_right h1 (by linarith : (0 : ℝ) ≤ 4 * n)
    rw [e] at this; linarith
  have h3 : (2 * x + b) ^ 2 ≤ n * (2 * x + 3 * b) := by nlinarith
  have h4 : ε * (2 * x - 2 * b) * n ≤ d * b * n := by nlinarith
  have h5 : ε * (2 * x - 2 * b) ≤ d * b := le_of_mul_le_mul_right h4 hnR
  have hd0 : (0 : ℝ) < d + 2 * ε := by positivity
  rw [div_mul_eq_mul_div, div_le_iff₀ hd0]
  nlinarith

end AlonExpanders.Core

open AlonExpanders.Core


theorem solution {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (n d : ℕ) (ε : ℝ) (hε : 0 ≤ ε) (hG : IsEnlarger G n d ε) :
    IsMagnifier G n d (2 * ε / ((d : ℝ) + 2 * ε)) := by
  exact c23_core G n d ε hε hG
