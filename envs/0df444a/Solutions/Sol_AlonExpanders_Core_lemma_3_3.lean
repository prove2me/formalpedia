-- Prove2me | solution 1 for AlonExpanders.Core.lemma_3_3
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T06:02:29.956443+00:00
-- url     : https://prove2.me/submissions/e2651e8f-b240-4720-ac66-aba1982b8955

import Mathlib
import Definitions.Def_AlonMilman_Diameter_lambda1
import Definitions.Def_AlonExpanders_Core_IsIOBipartite
import Definitions.Def_AlonExpanders_Core_IsStrongExpander

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

section comb
variable {I O : Type} [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O]
    (G : SimpleGraph (I ⊕ O)) [DecidableRel G.Adj]

def l31NI (A : Finset I) : Finset O :=
  Finset.univ.filter (fun o => ∃ i ∈ A, G.Adj (Sum.inl i) (Sum.inr o))

def l31NO (B : Finset O) : Finset I :=
  Finset.univ.filter (fun i => ∃ o ∈ B, G.Adj (Sum.inr o) (Sum.inl i))

lemma l31_nbI (hbip : IsIOBipartite G) (A : Finset I) :
    AKSSorting.Core.neighbours G (A.map Function.Embedding.inl) =
      (((l31NI G A).map Function.Embedding.inr : Finset (I ⊕ O)) : Set (I ⊕ O)) := by
  ext v
  rcases v with i | o
  · simp only [AKSSorting.Core.neighbours, Set.mem_setOf_eq, Finset.mem_map,
      Function.Embedding.inl_apply, Finset.coe_map, Set.mem_image, Finset.mem_coe,
      Function.Embedding.inr_apply]
    constructor
    · rintro ⟨x, ⟨j, hj, rfl⟩, h⟩; exact absurd h (hbip.1 j i)
    · rintro ⟨o, _, h⟩; cases h
  · simp only [AKSSorting.Core.neighbours, Set.mem_setOf_eq, Finset.mem_map,
      Function.Embedding.inl_apply, Finset.coe_map, Set.mem_image, Finset.mem_coe,
      Function.Embedding.inr_apply, l31NI, Finset.mem_filter, Finset.mem_univ, true_and,
      Sum.inr.injEq]
    constructor
    · rintro ⟨x, ⟨j, hj, rfl⟩, h⟩; exact ⟨o, ⟨j, hj, h⟩, rfl⟩
    · rintro ⟨o', ⟨j, hj, h⟩, rfl⟩; exact ⟨_, ⟨j, hj, rfl⟩, h⟩

end comb

lemma tb_rayleigh_eps {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hn : 2 ≤ Fintype.card V) (ε : ℝ)
    (hε : ε ≤ AlonMilman.Diameter.lambda1 G) (f : V → ℝ) :
    ε * (∑ v, f v ^ 2 - (∑ v, f v) ^ 2 / Fintype.card V) ≤
      (∑ u, ∑ v, if G.Adj u v then (f u - f v) ^ 2 else 0) / 2 := by
  have hnR : (0 : ℝ) < Fintype.card V := by exact_mod_cast (by omega : 0 < Fintype.card V)
  have hcs : (∑ v, f v) ^ 2 ≤ Fintype.card V * ∑ v, f v ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := f)
    simpa using this
  have : 0 ≤ ∑ v, f v ^ 2 - (∑ v, f v) ^ 2 / Fintype.card V := by
    rw [sub_nonneg, div_le_iff₀ hnR]; linarith
  exact (mul_le_mul_of_nonneg_right hε this).trans (c23_rayleigh G hn f)

/-- expansion of the edge sum for a regular graph -/
lemma tb_edge_sum {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (d : ℕ) (hreg : G.IsRegularOfDegree d) (w : V → ℝ) :
    (∑ u, ∑ v, if G.Adj u v then (w u - w v) ^ 2 else 0) =
      2 * d * ∑ u, w u ^ 2 - 2 * ∑ u, ∑ v, if G.Adj u v then w u * w v else 0 := by
  have hdeg : ∀ u, ∑ v, (if G.Adj u v then w u ^ 2 else 0) = d * w u ^ 2 := by
    intro u
    have h := SimpleGraph.degree_eq_sum_if_adj (G := G) (R := ℝ) u
    rw [hreg u] at h
    rw [h, Finset.sum_mul]
    refine Finset.sum_congr rfl fun v _ => ?_
    split_ifs <;> simp
  have hdeg2 : ∑ u, ∑ v, (if G.Adj u v then w v ^ 2 else 0) =
      ∑ u, ∑ v, (if G.Adj u v then w u ^ 2 else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
    by_cases h : G.Adj u v
    · simp [h, h.symm]
    · have h' : ¬ G.Adj v u := fun h' => h h'.symm
      simp [h, h']
  have : ∀ u v, (if G.Adj u v then (w u - w v) ^ 2 else 0) =
      (if G.Adj u v then w u ^ 2 else 0) + (if G.Adj u v then w v ^ 2 else 0) -
        2 * (if G.Adj u v then w u * w v else 0) := by
    intro u v; split_ifs <;> ring
  simp only [this, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [hdeg2]
  simp only [hdeg, ← Finset.mul_sum]
  ring


section bip
variable {I O : Type} [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O]
    (G : SimpleGraph (I ⊕ O)) [DecidableRel G.Adj]

lemma tb_ite_comm {V : Type} (G : SimpleGraph V) [DecidableRel G.Adj] (a b : V) (x y : ℝ) :
    (if G.Adj a b then x else y) = (if G.Adj b a then x else y) := by
  by_cases h : G.Adj a b
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (fun h' => h h'.symm)]

def tbz (v : I → ℝ) (o : O) : ℝ := ∑ i, if G.Adj (Sum.inl i) (Sum.inr o) then v i else 0

lemma tb_row (d : ℕ) (hbip : IsIOBipartite G) (hreg : G.IsRegularOfDegree d) (i : I) :
    ∑ o, (if G.Adj (Sum.inl i) (Sum.inr o) then (1 : ℝ) else 0) = d := by
  have h := SimpleGraph.degree_eq_sum_if_adj (G := G) (R := ℝ) (Sum.inl i)
  rw [hreg, Fintype.sum_sum_type] at h
  have h0 : ∑ j : I, (if G.Adj (Sum.inl i) (Sum.inl j) then (1 : ℝ) else 0) = 0 :=
    Finset.sum_eq_zero fun j _ => if_neg (hbip.1 i j)
  rw [h0, zero_add] at h; exact h.symm

lemma tb_col (d : ℕ) (hbip : IsIOBipartite G) (hreg : G.IsRegularOfDegree d) (o : O) :
    ∑ i, (if G.Adj (Sum.inl i) (Sum.inr o) then (1 : ℝ) else 0) = d := by
  have h := SimpleGraph.degree_eq_sum_if_adj (G := G) (R := ℝ) (Sum.inr o)
  rw [hreg, Fintype.sum_sum_type] at h
  have h0 : ∑ j : O, (if G.Adj (Sum.inr o) (Sum.inr j) then (1 : ℝ) else 0) = 0 :=
    Finset.sum_eq_zero fun j _ => if_neg (hbip.2 o j)
  rw [h0, add_zero] at h
  rw [h]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact tb_ite_comm G _ _ _ _

lemma tb_sumz (d : ℕ) (hbip : IsIOBipartite G) (hreg : G.IsRegularOfDegree d) (v : I → ℝ) :
    ∑ o, tbz G v o = d * ∑ i, v i := by
  simp only [tbz]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← tb_row G d hbip hreg i, Finset.sum_mul]
  refine Finset.sum_congr rfl fun o _ => ?_
  split_ifs <;> simp

lemma tb_mean0 (n d : ℕ) (hO : Fintype.card O = n) (hI : Fintype.card I = n) (hn : 1 ≤ n)
    (hbip : IsIOBipartite G) (hreg : G.IsRegularOfDegree d) (ε : ℝ)
    (hε : ε ≤ AlonMilman.Diameter.lambda1 G) (v : I → ℝ) (hv : ∑ i, v i = 0) :
    ∑ o, tbz G v o ^ 2 ≤ ((d : ℝ) - ε) ^ 2 * ∑ i, v i ^ 2 := by
  set Z := ∑ o, tbz G v o ^ 2
  set W := ∑ i, v i ^ 2
  set μ : ℝ := (d : ℝ) - ε
  have hcardV : 2 ≤ Fintype.card (I ⊕ O) := by rw [Fintype.card_sum]; omega
  have key : ∀ k : ℝ, 0 < k → 2 * Z * k ≤ μ * (W * k ^ 2 + Z) := by
    intro k hk
    set w : I ⊕ O → ℝ := Sum.elim v (fun o => tbz G v o / k)
    have hR := tb_rayleigh_eps G hcardV ε hε w
    rw [tb_edge_sum G d hreg w] at hR
    have hsw : ∑ u, w u = 0 := by
      rw [Fintype.sum_sum_type]
      simp only [w, Sum.elim_inl, Sum.elim_inr]
      rw [← Finset.sum_div, tb_sumz G d hbip hreg v, hv]; simp
    have hsw2 : ∑ u, w u ^ 2 = W + Z / k ^ 2 := by
      rw [Fintype.sum_sum_type]
      simp only [w, Sum.elim_inl, Sum.elim_inr, div_pow]
      rw [← Finset.sum_div]
    have hcross : ∑ u, ∑ u', (if G.Adj u u' then w u * w u' else 0) = 2 * (Z / k) := by
      rw [Fintype.sum_sum_type]
      simp only [Fintype.sum_sum_type, w, Sum.elim_inl, Sum.elim_inr]
      have h1 : ∀ i j : I, (if G.Adj (Sum.inl i) (Sum.inl j) then v i * v j else 0) = 0 :=
        fun i j => if_neg (hbip.1 i j)
      have h2 : ∀ o p : O, (if G.Adj (Sum.inr o) (Sum.inr p) then
          tbz G v o / k * (tbz G v p / k) else 0) = 0 := fun o p => if_neg (hbip.2 o p)
      simp only [h1, h2, Finset.sum_const_zero, zero_add, add_zero]
      have h3 : ∑ o, ∑ i, (if G.Adj (Sum.inr o) (Sum.inl i) then tbz G v o / k * v i else 0) =
          Z / k := by
        simp only [Z, Finset.sum_div]
        refine Finset.sum_congr rfl fun o _ => ?_
        calc ∑ i, (if G.Adj (Sum.inr o) (Sum.inl i) then tbz G v o / k * v i else 0)
            = tbz G v o / k * ∑ i, (if G.Adj (Sum.inl i) (Sum.inr o) then v i else 0) := by
              rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_
              rw [tb_ite_comm G (Sum.inr o)]; split_ifs <;> ring
          _ = tbz G v o ^ 2 / k := by
              show tbz G v o / k * tbz G v o = _; ring
      have h4 : ∑ i, ∑ o, (if G.Adj (Sum.inl i) (Sum.inr o) then v i * (tbz G v o / k) else 0) =
          ∑ o, ∑ i, (if G.Adj (Sum.inr o) (Sum.inl i) then tbz G v o / k * v i else 0) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun o _ => Finset.sum_congr rfl fun i _ => ?_
        rw [tb_ite_comm G (Sum.inl i)]; split_ifs <;> ring
      rw [h4, h3]; ring
    rw [hsw, hsw2, hcross] at hR
    have h5 : ε * (W + Z / k ^ 2) ≤ (2 * d * (W + Z / k ^ 2) - 2 * (2 * (Z / k))) / 2 := by
      simpa using hR
    have h6 : 2 * (Z / k) ≤ μ * (W + Z / k ^ 2) := by simp only [μ]; linarith
    have e1 : 2 * (Z / k) * k ^ 2 = 2 * Z * k := by field_simp
    have e2 : μ * (W + Z / k ^ 2) * k ^ 2 = μ * (W * k ^ 2 + Z) := by field_simp
    have := mul_le_mul_of_nonneg_right h6 (sq_nonneg k)
    rw [e1, e2] at this; exact this
  have hZ0 : 0 ≤ Z := Finset.sum_nonneg fun o _ => sq_nonneg _
  have hW0 : 0 ≤ W := Finset.sum_nonneg fun o _ => sq_nonneg _
  rcases le_or_gt μ 0 with hμ | hμ
  · have := key 1 one_pos
    have : 0 ≤ μ ^ 2 * W := by positivity
    nlinarith
  · have := key μ hμ
    have h7 : Z * μ ≤ μ ^ 2 * W * μ := by nlinarith
    exact le_of_mul_le_mul_right h7 hμ

lemma tb_gen (n d : ℕ) (hO : Fintype.card O = n) (hI : Fintype.card I = n) (hn : 1 ≤ n)
    (hbip : IsIOBipartite G) (hreg : G.IsRegularOfDegree d) (ε : ℝ)
    (hε : ε ≤ AlonMilman.Diameter.lambda1 G) (v : I → ℝ) :
    ∑ o, tbz G v o ^ 2 ≤ ((d : ℝ) - ε) ^ 2 * (∑ i, v i ^ 2 - (∑ i, v i) ^ 2 / n) +
      (d : ℝ) ^ 2 * (∑ i, v i) ^ 2 / n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  set S := ∑ i, v i
  set a : ℝ := S / n
  set v0 : I → ℝ := fun i => v i - a
  have hv0 : ∑ i, v0 i = 0 := by
    simp only [v0, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, hI, nsmul_eq_mul]
    simp only [a, S]; field_simp; ring
  have h0 := tb_mean0 G n d hO hI hn hbip hreg ε hε v0 hv0
  have hz : ∀ o, tbz G v o = tbz G v0 o + a * d := by
    intro o
    simp only [tbz, v0]
    rw [← tb_col G d hbip hreg o, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs <;> ring
  have hs0 : ∑ o, tbz G v0 o = 0 := by rw [tb_sumz G d hbip hreg, hv0, mul_zero]
  have hsq : ∑ o, tbz G v o ^ 2 = ∑ o, tbz G v0 o ^ 2 + n * (a * d) ^ 2 := by
    simp only [hz, add_sq, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, hO,
      nsmul_eq_mul]
    have : ∑ o, 2 * tbz G v0 o * (a * d) = 0 := by
      rw [← Finset.sum_mul, ← Finset.mul_sum, hs0]; ring
    rw [this]; ring
  have hw : ∑ i, v0 i ^ 2 = ∑ i, v i ^ 2 - S ^ 2 / n := by
    simp only [v0, sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, hI, nsmul_eq_mul, ← Finset.sum_mul, ← Finset.mul_sum]
    simp only [a]; field_simp; ring
  rw [hsq, ← hw]
  have : (n : ℝ) * (a * d) ^ 2 = (d : ℝ) ^ 2 * S ^ 2 / n := by simp only [a]; field_simp
  rw [this]; linarith

lemma tb_core (n d : ℕ) (hI : Fintype.card I = n) (hO : Fintype.card O = n)
    (hbip : IsIOBipartite G) (hreg : G.IsRegularOfDegree d) (ε : ℝ)
    (hε : ε ≤ AlonMilman.Diameter.lambda1 G) (X : Finset I) :
    (d : ℝ) ^ 2 /
        (((X.card : ℝ) / n) * ((d : ℝ) ^ 2 - ((d : ℝ) - ε) ^ 2) +
          ((d : ℝ) - ε) ^ 2) * (X.card : ℝ) ≤
      ((AKSSorting.Core.neighbours G (X.map Function.Embedding.inl)).ncard : ℝ) := by
  rw [l31_nbI G hbip, Set.ncard_coe_finset, Finset.card_map]
  rcases Nat.eq_zero_or_pos X.card with hx | hx
  · simp [hx]
  have hn : 1 ≤ n := by
    have := Finset.card_le_univ X; rw [hI] at this; omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  set v : I → ℝ := fun i => if i ∈ X then 1 else 0
  have hS : ∑ i, v i = X.card := by simp [v, Finset.sum_boole]
  have hW : ∑ i, v i ^ 2 = X.card := by
    have : ∀ i, v i ^ 2 = v i := fun i => by simp only [v]; split_ifs <;> norm_num
    simp only [this, hS]
  have hg := tb_gen G n d hO hI hn hbip hreg ε hε v
  rw [hS, hW] at hg
  set T := l31NI G X
  have hsupp : ∀ o, o ∉ T → tbz G v o = 0 := by
    intro o ho
    simp only [T, l31NI, Finset.mem_filter, Finset.mem_univ, true_and, not_exists,
      not_and] at ho
    simp only [tbz, v]
    refine Finset.sum_eq_zero fun i _ => ?_
    split_ifs with h1 h2 <;> first | rfl | exact absurd h1 (ho i h2)
  have hsumz := tb_sumz G d hbip hreg v
  rw [hS] at hsumz
  have hzT : ∑ o ∈ T, tbz G v o = ∑ o, tbz G v o :=
    Finset.sum_subset (Finset.subset_univ _) (fun o _ ho => hsupp o ho)
  have hz2T : ∑ o ∈ T, tbz G v o ^ 2 ≤ ∑ o, tbz G v o ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun o _ _ => sq_nonneg _)
  have hcs := sq_sum_le_card_mul_sum_sq (s := T) (f := tbz G v)
  rw [hzT, hsumz] at hcs
  set x : ℝ := (X.card : ℝ)
  set t : ℝ := (T.card : ℝ)
  set μ : ℝ := (d : ℝ) - ε
  have hx0 : 0 < x := by simp only [x]; exact_mod_cast hx
  have ht0 : 0 ≤ t := Nat.cast_nonneg _
  have key : (d : ℝ) ^ 2 * x ^ 2 ≤ t * (μ ^ 2 * (x - x ^ 2 / n) + (d : ℝ) ^ 2 * x ^ 2 / n) := by
    have := mul_le_mul_of_nonneg_left (hz2T.trans hg) ht0
    nlinarith
  set D := x / n * ((d : ℝ) ^ 2 - μ ^ 2) + μ ^ 2
  have hxD : x * D = μ ^ 2 * (x - x ^ 2 / n) + (d : ℝ) ^ 2 * x ^ 2 / n := by
    simp only [D]; field_simp; ring
  rcases le_or_gt D 0 with hD | hD
  · have : (d : ℝ) ^ 2 / D ≤ 0 := div_nonpos_of_nonneg_of_nonpos (sq_nonneg _) hD
    nlinarith
  · rw [div_mul_eq_mul_div, div_le_iff₀ hD]
    rw [← hxD] at key
    have : (d : ℝ) ^ 2 * x * x ≤ t * D * x := by nlinarith
    exact le_of_mul_le_mul_right this hx0

lemma ss_core (n d : ℕ) (hd : 1 ≤ d) (hI : Fintype.card I = n) (hO : Fintype.card O = n)
    (hbip : IsIOBipartite G) (hreg : G.IsRegularOfDegree d) (ε : ℝ)
    (hε : ε ≤ AlonMilman.Diameter.lambda1 G) :
    IsStrongExpander G n d ((2 * (d : ℝ) * ε - ε ^ 2) / (d : ℝ) ^ 2) := by
  refine ⟨hI, hO, hbip, G.maxDegree_le_of_forall_degree_le d (fun v => (hreg v).le), ?_⟩
  intro X
  have h := tb_core G n d hI hO hbip hreg ε hε X
  refine le_trans ?_ h
  rcases Nat.eq_zero_or_pos X.card with hx | hx
  · simp [hx]
  have hxn : X.card ≤ n := by have := Finset.card_le_univ X; rwa [hI] at this
  have hn : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  set x : ℝ := (X.card : ℝ)
  have hx0 : 0 < x := by simp only [x]; exact_mod_cast hx
  have hxnR : x ≤ n := by simp only [x]; exact_mod_cast hxn
  set α := x / n
  have hα0 : 0 < α := div_pos hx0 hnR
  have hα1 : α ≤ 1 := (div_le_one hnR).2 hxnR
  set μ : ℝ := (d : ℝ) - ε
  set D := α * ((d : ℝ) ^ 2 - μ ^ 2) + μ ^ 2
  have hD : 0 < D := by
    have : D = α * (d : ℝ) ^ 2 + (1 - α) * μ ^ 2 := by simp only [D]; ring
    rw [this]
    have : 0 < α * (d : ℝ) ^ 2 := by positivity
    have : 0 ≤ (1 - α) * μ ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
    linarith
  have hc : (2 * (d : ℝ) * ε - ε ^ 2) / (d : ℝ) ^ 2 = ((d : ℝ) ^ 2 - μ ^ 2) / (d : ℝ) ^ 2 := by
    simp only [μ]; ring
  rw [hc]
  apply mul_le_mul_of_nonneg_right _ hx0.le
  rw [le_div_iff₀ hD]
  set t := ((d : ℝ) ^ 2 - μ ^ 2) / (d : ℝ) ^ 2 * (1 - α)
  have hDt : D = (d : ℝ) ^ 2 * (1 - t) := by
    simp only [D, t]; field_simp; ring
  rw [show (1 + ((d : ℝ) ^ 2 - μ ^ 2) / (d : ℝ) ^ 2 * (1 - α)) = 1 + t from rfl, hDt]
  nlinarith [sq_nonneg t, sq_nonneg (d : ℝ)]

end bip

end AlonExpanders.Core

open AlonExpanders.Core


theorem solution {I O : Type} [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O]
    (G : SimpleGraph (I ⊕ O)) [DecidableRel G.Adj] (n d : ℕ) (hd : 1 ≤ d)
    (hI : Fintype.card I = n) (hO : Fintype.card O = n)
    (hbip : IsIOBipartite G) (hreg : G.IsRegularOfDegree d) :
    IsStrongExpander G n d
      ((2 * (d : ℝ) * AlonMilman.Diameter.lambda1 G - AlonMilman.Diameter.lambda1 G ^ 2) /
        (d : ℝ) ^ 2) := by
  exact ss_core G n d hd hI hO hbip hreg _ le_rfl
