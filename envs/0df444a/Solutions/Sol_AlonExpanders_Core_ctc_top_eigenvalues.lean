-- Prove2me | solution 1 for AlonExpanders.Core.ctc_top_eigenvalues
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T09:40:20.938137+00:00
-- url     : https://prove2.me/submissions/749cb6e6-2531-4f13-b897-f923156b3991

import Mathlib
import Definitions.Def_AlonMilman_Diameter_lambda1
import Definitions.Def_AlonExpanders_Core_IsIOBipartite
import Definitions.Def_AlonExpanders_Core_biadjMatrix

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open Matrix WithLp in
theorem ctc_spec_kit {V : Type} [Fintype V] [DecidableEq V] (A : Matrix V V ℝ)
    (hA : A.IsHermitian) :
    ∃ u : Fin (Fintype.card V) → V → ℝ,
      (∀ k, A *ᵥ u k = hA.eigenvalues₀ k • u k) ∧
      (∀ k l, u k ⬝ᵥ u l = if k = l then 1 else 0) ∧
      (∀ z, z ⬝ᵥ z = ∑ k, (u k ⬝ᵥ z) ^ 2) ∧
      (∀ z, z ⬝ᵥ (A *ᵥ z) = ∑ k, hA.eigenvalues₀ k * (u k ⬝ᵥ z) ^ 2) := by
  set T := Matrix.toEuclideanLin A with hT_def
  have hT : T.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr hA
  have hfin : Module.finrank ℝ (EuclideanSpace ℝ V) = Fintype.card V := finrank_euclideanSpace
  set b := hT.eigenvectorBasis hfin with hb
  have hev : hA.eigenvalues₀ = hT.eigenvalues hfin := rfl
  have hinb : ∀ x y : EuclideanSpace ℝ V, inner ℝ x y = ofLp x ⬝ᵥ ofLp y := by
    intro x y
    rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct_comm]
  have hTz : ∀ z : V → ℝ, T (toLp 2 z) = toLp 2 (A *ᵥ z) := fun z => rfl
  have hTb : ∀ k, A *ᵥ ofLp (b k) = ofLp (T (b k)) := fun k => rfl
  refine ⟨fun k => ofLp (b k), ?_, ?_, ?_, ?_⟩
  · intro k
    simp only
    rw [hTb, hT.apply_eigenvectorBasis hfin k, hev]
    simp
    rfl
  · intro k l
    have := orthonormal_iff_ite.mp b.orthonormal k l
    rw [hinb] at this
    exact this
  · intro z
    have h := b.sum_inner_mul_inner (toLp 2 z) (toLp 2 z)
    rw [hinb, ofLp_toLp] at h
    rw [← h]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hinb, hinb, ofLp_toLp, dotProduct_comm]
    ring
  · intro z
    have h := b.sum_inner_mul_inner (toLp 2 z) (T (toLp 2 z))
    rw [hinb, hTz, ofLp_toLp, ofLp_toLp] at h
    rw [← h]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← hTz, ← hT (b k), hT.apply_eigenvectorBasis hfin k, hev]
    simp only [RCLike.ofReal_real_eq_id, id, real_inner_smul_left]
    rw [hinb, hinb, ofLp_toLp, dotProduct_comm]
    ring

open Matrix in
theorem ctc_pin_ge {V : Type} [Fintype V] {m : ℕ} (A : Matrix V V ℝ) (ev : Fin m → ℝ)
    (u : Fin m → V → ℝ)
    (hnorm : ∀ z, z ⬝ᵥ z = ∑ k, (u k ⬝ᵥ z) ^ 2)
    (hexp : ∀ z, z ⬝ᵥ (A *ᵥ z) = ∑ k, ev k * (u k ⬝ᵥ z) ^ 2)
    (p : Fin m) (c : ℝ) (hc : ∀ k, k ≠ p → c ≤ ev k) (z : V → ℝ) (hz : u p ⬝ᵥ z = 0) :
    c * (z ⬝ᵥ z) ≤ z ⬝ᵥ (A *ᵥ z) := by
  rw [hnorm, hexp, Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ => ?_
  by_cases hk : k = p
  · subst hk; rw [hz]; simp
  · exact mul_le_mul_of_nonneg_right (hc k hk) (sq_nonneg _)

open Matrix in
theorem ctc_pin_le {V : Type} [Fintype V] {m : ℕ} (A : Matrix V V ℝ) (ev : Fin m → ℝ)
    (u : Fin m → V → ℝ)
    (hnorm : ∀ z, z ⬝ᵥ z = ∑ k, (u k ⬝ᵥ z) ^ 2)
    (hexp : ∀ z, z ⬝ᵥ (A *ᵥ z) = ∑ k, ev k * (u k ⬝ᵥ z) ^ 2)
    (p : Fin m) (c : ℝ) (hc : ∀ k, k ≠ p → ev k ≤ c) (z : V → ℝ) (hz : u p ⬝ᵥ z = 0) :
    z ⬝ᵥ (A *ᵥ z) ≤ c * (z ⬝ᵥ z) := by
  rw [hnorm, hexp, Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ => ?_
  by_cases hk : k = p
  · subst hk; rw [hz]; simp
  · exact mul_le_mul_of_nonneg_right (hc k hk) (sq_nonneg _)

open Matrix in
theorem ctc_top {V : Type} [Fintype V] {m : ℕ} (A : Matrix V V ℝ) (ev : Fin m → ℝ)
    (u : Fin m → V → ℝ)
    (hnorm : ∀ z, z ⬝ᵥ z = ∑ k, (u k ⬝ᵥ z) ^ 2)
    (hexp : ∀ z, z ⬝ᵥ (A *ᵥ z) = ∑ k, ev k * (u k ⬝ᵥ z) ^ 2)
    (c : ℝ) (hc : ∀ k, ev k ≤ c) (z : V → ℝ) :
    z ⬝ᵥ (A *ᵥ z) ≤ c * (z ⬝ᵥ z) := by
  rw [hnorm, hexp, Finset.mul_sum]
  exact Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_right (hc k) (sq_nonneg _)

open Matrix in
theorem ctc_two_vec {V : Type} [Fintype V] (A : Matrix V V ℝ) (y1 y2 v : V → ℝ) (e1 e2 : ℝ)
    (h1 : A *ᵥ y1 = e1 • y1) (h2 : A *ᵥ y2 = e2 • y2) (h12 : y1 ⬝ᵥ y2 = 0)
    (p1 : 0 < y1 ⬝ᵥ y1) (p2 : 0 < y2 ⬝ᵥ y2) :
    ∃ z : V → ℝ, 0 < z ⬝ᵥ z ∧ v ⬝ᵥ z = 0 ∧ min e1 e2 * (z ⬝ᵥ z) ≤ z ⬝ᵥ (A *ᵥ z) ∧
      z ⬝ᵥ (A *ᵥ z) ≤ max e1 e2 * (z ⬝ᵥ z) := by
  have h21 : y2 ⬝ᵥ y1 = 0 := by rw [dotProduct_comm]; exact h12
  by_cases hv : v ⬝ᵥ y1 = 0
  · refine ⟨y1, p1, hv, ?_, ?_⟩
    · rw [h1, dotProduct_smul, smul_eq_mul]
      exact mul_le_mul_of_nonneg_right (min_le_left _ _) p1.le
    · rw [h1, dotProduct_smul, smul_eq_mul]
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) p1.le
  · set a := v ⬝ᵥ y2
    set c := v ⬝ᵥ y1
    have hzz : (a • y1 - c • y2) ⬝ᵥ (a • y1 - c • y2) =
        a ^ 2 * (y1 ⬝ᵥ y1) + c ^ 2 * (y2 ⬝ᵥ y2) := by
      simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul,
        h12, h21]
      ring
    have hzA : (a • y1 - c • y2) ⬝ᵥ (A *ᵥ (a • y1 - c • y2)) =
        a ^ 2 * e1 * (y1 ⬝ᵥ y1) + c ^ 2 * e2 * (y2 ⬝ᵥ y2) := by
      simp only [mulVec_sub, mulVec_smul, h1, h2, sub_dotProduct, dotProduct_sub,
        smul_dotProduct, dotProduct_smul, smul_eq_mul, h12, h21]
      ring
    refine ⟨a • y1 - c • y2, ?_, ?_, ?_, ?_⟩
    · rw [hzz]
      have hc2 : 0 < c ^ 2 := by positivity
      have ha2 : 0 ≤ a ^ 2 := sq_nonneg _
      nlinarith [mul_nonneg ha2 p1.le, mul_pos hc2 p2]
    · simp only [dotProduct_sub, dotProduct_smul, smul_eq_mul, a, c]; ring
    · rw [hzA, hzz]
      have q1 := mul_le_mul_of_nonneg_left (min_le_left e1 e2)
        (mul_nonneg (sq_nonneg a) p1.le)
      have q2 := mul_le_mul_of_nonneg_left (min_le_right e1 e2)
        (mul_nonneg (sq_nonneg c) p2.le)
      nlinarith
    · rw [hzA, hzz]
      have q1 := mul_le_mul_of_nonneg_left (le_max_left e1 e2)
        (mul_nonneg (sq_nonneg a) p1.le)
      have q2 := mul_le_mul_of_nonneg_left (le_max_right e1 e2)
        (mul_nonneg (sq_nonneg c) p2.le)
      nlinarith

open Matrix in
theorem ctc_lap_block {I O : Type} [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O]
    (G : SimpleGraph (I ⊕ O)) [DecidableRel G.Adj] (d : ℕ)
    (hbip : AlonExpanders.Core.IsIOBipartite G) (hreg : G.IsRegularOfDegree d)
    (x : I → ℝ) (y : O → ℝ) :
    G.lapMatrix ℝ *ᵥ Sum.elim x y =
      Sum.elim ((d : ℝ) • x - AlonExpanders.Core.biadjMatrix G *ᵥ y)
        ((d : ℝ) • y - (AlonExpanders.Core.biadjMatrix G)ᵀ *ᵥ x) := by
  have hlap : ∀ (f : I ⊕ O → ℝ) (v : I ⊕ O),
      (G.lapMatrix ℝ *ᵥ f) v = ∑ w, (if G.Adj v w then (f v - f w) else 0) := by
    intro f v
    rw [SimpleGraph.lapMatrix_mulVec_apply]
    have h1 : ∑ w, (if G.Adj v w then (f v - f w) else 0)
        = ∑ w ∈ G.neighborFinset v, (f v - f w) := by
      rw [← Finset.sum_filter]
      congr 1
      ext w; simp
    rw [h1, Finset.sum_sub_distrib, Finset.sum_const, SimpleGraph.card_neighborFinset_eq_degree,
      nsmul_eq_mul]
  have hdeg : ∀ v, (d : ℝ) = ∑ w, if G.Adj v w then (1 : ℝ) else 0 := by
    intro v
    rw [← hreg v]
    exact G.degree_eq_sum_if_adj v
  funext v
  rcases v with i | o
  · rw [hlap, Fintype.sum_sum_type]
    have hd := hdeg (Sum.inl i)
    rw [Fintype.sum_sum_type] at hd
    simp only [hbip.1, if_false, Finset.sum_const_zero, zero_add, Sum.elim_inl,
      Sum.elim_inr] at hd ⊢
    have : ∀ o, (if G.Adj (Sum.inl i) (Sum.inr o) then x i - y o else 0) =
        (if G.Adj (Sum.inl i) (Sum.inr o) then (1 : ℝ) else 0) * x i -
          (if G.Adj (Sum.inl i) (Sum.inr o) then (1 : ℝ) else 0) * y o := by
      intro o; by_cases h : G.Adj (Sum.inl i) (Sum.inr o) <;> simp [h]
    rw [Finset.sum_congr rfl (fun o _ => this o), Finset.sum_sub_distrib, ← Finset.sum_mul, ← hd]
    simp [mulVec, dotProduct, AlonExpanders.Core.biadjMatrix]
  · rw [hlap, Fintype.sum_sum_type]
    have hd := hdeg (Sum.inr o)
    rw [Fintype.sum_sum_type] at hd
    simp only [hbip.2, if_false, Finset.sum_const_zero, add_zero, Sum.elim_inr,
      Sum.elim_inl] at hd ⊢
    have : ∀ i, (if G.Adj (Sum.inr o) (Sum.inl i) then y o - x i else 0) =
        (if G.Adj (Sum.inr o) (Sum.inl i) then (1 : ℝ) else 0) * y o -
          (if G.Adj (Sum.inl i) (Sum.inr o) then (1 : ℝ) else 0) * x i := by
      intro i
      by_cases h : G.Adj (Sum.inl i) (Sum.inr o) <;> simp [h, G.adj_comm (Sum.inr o) (Sum.inl i)]
    rw [Finset.sum_congr rfl (fun i _ => this i), Finset.sum_sub_distrib, ← Finset.sum_mul, ← hd]
    simp [mulVec, dotProduct, AlonExpanders.Core.biadjMatrix, transpose]

open Matrix in
theorem ctc_dot_elim {I O : Type} [Fintype I] [Fintype O] (a a' : I → ℝ) (b b' : O → ℝ) :
    Sum.elim a b ⬝ᵥ Sum.elim a' b' = a ⬝ᵥ a' + b ⬝ᵥ b' := by
  simp [dotProduct, Fintype.sum_sum_type]

open Matrix in
theorem ctc_self_nonneg {V : Type} [Fintype V] (a : V → ℝ) : 0 ≤ a ⬝ᵥ a :=
  Finset.sum_nonneg fun i _ => mul_self_nonneg (a i)

open Matrix in
theorem ctc_adj_dot {I O : Type} [Fintype I] [Fintype O] (C : Matrix I O ℝ) (y : O → ℝ)
    (x : I → ℝ) : (C *ᵥ y) ⬝ᵥ x = y ⬝ᵥ (Cᵀ *ᵥ x) := by
  rw [dotProduct_mulVec, vecMul_transpose]

open Matrix in
theorem ctc_lift {I O : Type} [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O]
    (G : SimpleGraph (I ⊕ O)) [DecidableRel G.Adj] (d : ℕ)
    (hbip : AlonExpanders.Core.IsIOBipartite G) (hreg : G.IsRegularOfDegree d)
    (w : O → ℝ) (μ : ℝ) (hμ : 0 ≤ μ)
    (hw : (AlonExpanders.Core.biadjMatrix G)ᵀ *ᵥ (AlonExpanders.Core.biadjMatrix G *ᵥ w) =
      μ • w) :
    G.lapMatrix ℝ *ᵥ Sum.elim ((√μ)⁻¹ • AlonExpanders.Core.biadjMatrix G *ᵥ w) w =
      ((d : ℝ) - √μ) • Sum.elim ((√μ)⁻¹ • AlonExpanders.Core.biadjMatrix G *ᵥ w) w := by
  set C := AlonExpanders.Core.biadjMatrix G with hC
  rw [ctc_lap_block G d hbip hreg, ← hC]
  have hss : √μ * √μ = μ := Real.mul_self_sqrt hμ
  set s := √μ with hsdef
  by_cases hs : s = 0
  · have hμ0 : μ = 0 := by rw [← hss, hs, mul_zero]
    have hCw : C *ᵥ w = 0 := by
      have h1 : (C *ᵥ w) ⬝ᵥ (C *ᵥ w) = 0 := by
        rw [ctc_adj_dot, hw, hμ0, zero_smul, dotProduct_zero]
      exact dotProduct_self_eq_zero.mp h1
    rw [hs, hCw]
    funext v
    rcases v with i | o
    · simp
    · simp [hw, hμ0]
  · funext v
    rcases v with i | o
    · simp only [Sum.elim_inl, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      field_simp
    · simp only [Sum.elim_inr, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mulVec_smul, hw]
      have e : s⁻¹ * (μ * w o) = s * w o := by
        rw [← hss]; field_simp
      rw [e]; ring

open Matrix in
theorem ctc_restrict {I O : Type} [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O]
    (G : SimpleGraph (I ⊕ O)) [DecidableRel G.Adj] (d : ℕ)
    (hbip : AlonExpanders.Core.IsIOBipartite G) (hreg : G.IsRegularOfDegree d)
    (f : I ⊕ O → ℝ) (ν : ℝ) (hf : G.lapMatrix ℝ *ᵥ f = ν • f) :
    AlonExpanders.Core.biadjMatrix G *ᵥ (fun o => f (Sum.inr o)) =
        ((d : ℝ) - ν) • (fun i => f (Sum.inl i)) ∧
      (AlonExpanders.Core.biadjMatrix G)ᵀ *ᵥ (fun i => f (Sum.inl i)) =
        ((d : ℝ) - ν) • (fun o => f (Sum.inr o)) := by
  have hfe : f = Sum.elim (fun i => f (Sum.inl i)) (fun o => f (Sum.inr o)) := by
    funext v; rcases v with i | o <;> rfl
  rw [hfe, ctc_lap_block G d hbip hreg] at hf
  constructor
  · funext i
    have := congrFun hf (Sum.inl i)
    simp only [Sum.elim_inl, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at this ⊢
    linarith
  · funext o
    have := congrFun hf (Sum.inr o)
    simp only [Sum.elim_inr, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at this ⊢
    linarith

set_option maxHeartbeats 1000000 in
open AlonExpanders.Core Matrix in
theorem solution {I O : Type} [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O]
    (G : SimpleGraph (I ⊕ O)) [DecidableRel G.Adj] (n d : ℕ)
    (hI : Fintype.card I = n) (hO : Fintype.card O = n) (hn : 2 ≤ n)
    (hbip : IsIOBipartite G) (hreg : G.IsRegularOfDegree d) :
    (Matrix.isHermitian_conjTranspose_mul_self (biadjMatrix G)).eigenvalues₀ ⟨0, by omega⟩ =
        (d : ℝ) ^ 2 ∧
      (Matrix.isHermitian_conjTranspose_mul_self (biadjMatrix G)).eigenvalues₀ ⟨1, by omega⟩ =
        ((d : ℝ) - AlonMilman.Diameter.lambda1 G) ^ 2 := by
  set C := biadjMatrix G with hC
  have hMv : ∀ w, (Cᴴ * C) *ᵥ w = Cᵀ *ᵥ (C *ᵥ w) := by
    intro w; rw [conjTranspose_eq_transpose_of_trivial, ← mulVec_mulVec]
  have hMh := Matrix.isHermitian_conjTranspose_mul_self C
  obtain ⟨u, hu_eig, hu_orth, hu_norm, hu_exp⟩ := ctc_spec_kit _ hMh
  have hLh := G.isHermitian_lapMatrix ℝ
  obtain ⟨b, hb_eig, hb_orth, hb_norm, hb_exp⟩ := ctc_spec_kit _ hLh
  set μ := hMh.eigenvalues₀ with hμ_def
  set ν := hLh.eigenvalues₀ with hν_def
  have hμanti := hMh.eigenvalues₀_antitone
  have hνanti := hLh.eigenvalues₀_antitone
  set i0 : Fin (Fintype.card O) := ⟨0, by omega⟩ with hi0
  set i1 : Fin (Fintype.card O) := ⟨1, by omega⟩ with hi1
  have hN : Fintype.card (I ⊕ O) = 2 * n := by rw [Fintype.card_sum, hI, hO]; ring
  set last : Fin (Fintype.card (I ⊕ O)) := ⟨Fintype.card (I ⊕ O) - 1, by omega⟩ with hlast
  set sec : Fin (Fintype.card (I ⊕ O)) := ⟨Fintype.card (I ⊕ O) - 2, by omega⟩ with hsec
  have hlam : AlonMilman.Diameter.lambda1 G = ν sec := by
    unfold AlonMilman.Diameter.lambda1
    rw [dif_pos (by omega)]
  -- index facts
  have hμ0 : ∀ k, μ k ≤ μ i0 := by
    intro k; apply hμanti; rw [Fin.le_iff_val_le_val]; simp [i0]
  have hμ1 : ∀ k, k ≠ i0 → μ k ≤ μ i1 := by
    intro k hk; apply hμanti; rw [Fin.le_iff_val_le_val]
    have : k.val ≠ 0 := fun h => hk (Fin.ext h)
    simp only [i1]; omega
  have hμ10 : μ i1 ≤ μ i0 := hμ0 i1
  have hνsec : ∀ k, k ≠ last → ν sec ≤ ν k := by
    intro k hk; apply hνanti; rw [Fin.le_iff_val_le_val]
    have h1 := k.isLt
    have h2 : k.val ≠ Fintype.card (I ⊕ O) - 1 := fun h => hk (Fin.ext h)
    simp only [sec]; omega
  have hνlast : ν last ≤ ν sec := by
    apply hνanti; rw [Fin.le_iff_val_le_val]; simp only [sec, last]; omega
  have hsl : sec ≠ last := by
    intro h; have := congrArg Fin.val h; simp only [sec, last] at this; omega
  have hi01 : i1 ≠ i0 := by
    intro h; have := congrArg Fin.val h; simp [i0, i1] at this
  -- unit vectors
  have hu1 : ∀ k, u k ⬝ᵥ u k = 1 := fun k => by rw [hu_orth]; simp
  have hb1 : ∀ k, b k ⬝ᵥ b k = 1 := fun k => by rw [hb_orth]; simp
  -- M facts
  have hMeig : ∀ k, Cᵀ *ᵥ (C *ᵥ u k) = μ k • u k := fun k => by rw [← hMv]; exact hu_eig k
  have hμnn : ∀ k, 0 ≤ μ k := by
    intro k
    have h : (C *ᵥ u k) ⬝ᵥ (C *ᵥ u k) = μ k := by
      rw [ctc_adj_dot, hMeig, dotProduct_smul, hu1, smul_eq_mul, mul_one]
    rw [← h]; exact ctc_self_nonneg _
  -- lifts
  set s0 := √(μ i0) with hs0
  set s1 := √(μ i1) with hs1
  set f0 := Sum.elim (s0⁻¹ • C *ᵥ u i0) (u i0) with hf0
  set f1 := Sum.elim (s1⁻¹ • C *ᵥ u i1) (u i1) with hf1
  have hLf0 : G.lapMatrix ℝ *ᵥ f0 = ((d : ℝ) - s0) • f0 :=
    ctc_lift G d hbip hreg (u i0) (μ i0) (hμnn i0) (hMeig i0)
  have hLf1 : G.lapMatrix ℝ *ᵥ f1 = ((d : ℝ) - s1) • f1 :=
    ctc_lift G d hbip hreg (u i1) (μ i1) (hμnn i1) (hMeig i1)
  have hf0pos : 0 < f0 ⬝ᵥ f0 := by
    rw [hf0, ctc_dot_elim, hu1]; linarith [ctc_self_nonneg (s0⁻¹ • C *ᵥ u i0)]
  have hf1pos : 0 < f1 ⬝ᵥ f1 := by
    rw [hf1, ctc_dot_elim, hu1]; linarith [ctc_self_nonneg (s1⁻¹ • C *ᵥ u i1)]
  have hf01 : f0 ⬝ᵥ f1 = 0 := by
    rw [hf0, hf1, ctc_dot_elim, hu_orth, if_neg hi01.symm]
    simp only [smul_dotProduct, dotProduct_smul, smul_eq_mul]
    rw [ctc_adj_dot, hMeig, dotProduct_smul, hu_orth, if_neg hi01.symm]
    simp
  have hs0nn : 0 ≤ s0 := Real.sqrt_nonneg _
  have hs1nn : 0 ≤ s1 := Real.sqrt_nonneg _
  have hs10 : s1 ≤ s0 := Real.sqrt_le_sqrt hμ10
  have hss0 : s0 ^ 2 = μ i0 := Real.sq_sqrt (hμnn i0)
  have hss1 : s1 ^ 2 = μ i1 := Real.sq_sqrt (hμnn i1)
  -- S8: μ i0 = d^2
  have hconst := SimpleGraph.lapMatrix_mulVec_const_eq_zero (R := ℝ) G
  have h1elim : (fun _ : I ⊕ O => (1 : ℝ)) = Sum.elim (fun _ => 1) (fun _ => 1) := by
    funext v; rcases v with i | o <;> rfl
  rw [h1elim, ctc_lap_block G d hbip hreg, ← hC] at hconst
  have hrow : C *ᵥ (fun _ => (1 : ℝ)) = (d : ℝ) • (fun _ => (1 : ℝ)) := by
    funext i
    have := congrFun hconst (Sum.inl i)
    simp only [Sum.elim_inl, Pi.sub_apply, Pi.zero_apply, Pi.smul_apply, smul_eq_mul,
      mul_one] at this ⊢
    linarith
  have hcol : Cᵀ *ᵥ (fun _ => (1 : ℝ)) = (d : ℝ) • (fun _ => (1 : ℝ)) := by
    funext o
    have := congrFun hconst (Sum.inr o)
    simp only [Sum.elim_inr, Pi.sub_apply, Pi.zero_apply, Pi.smul_apply, smul_eq_mul,
      mul_one] at this ⊢
    linarith
  have hone : (fun _ : O => (1 : ℝ)) ⬝ᵥ (fun _ => (1 : ℝ)) = n := by
    simp [dotProduct, hO]
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hge0 : (d : ℝ) ^ 2 ≤ μ i0 := by
    have h := ctc_top (Cᴴ * C) μ u hu_norm hu_exp (μ i0) hμ0 (fun _ => (1 : ℝ))
    rw [hMv, hrow, mulVec_smul, hcol, smul_smul, dotProduct_smul, hone, smul_eq_mul] at h
    rw [sq]; exact le_of_mul_le_mul_right h hnpos
  have hle0 : s0 ≤ d := by
    have h := (SimpleGraph.posSemidef_lapMatrix ℝ G).dotProduct_mulVec_nonneg f0
    rw [star_trivial, hLf0, dotProduct_smul, smul_eq_mul] at h
    by_contra hc
    have hneg : ((d : ℝ) - s0) * (f0 ⬝ᵥ f0) < 0 :=
      mul_neg_of_neg_of_pos (by linarith [not_le.mp hc]) hf0pos
    linarith
  have hmu0 : μ i0 = (d : ℝ) ^ 2 := by
    have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    have : μ i0 ≤ (d : ℝ) ^ 2 := by rw [← hss0]; exact pow_le_pow_left₀ hs0nn hle0 2
    exact le_antisymm this hge0
  refine ⟨hmu0, ?_⟩
  rw [hlam]
  -- S9: ν sec ≤ d - s1
  have hS9 : ν sec ≤ (d : ℝ) - s1 := by
    obtain ⟨z, hz, hzv, -, hzu⟩ :=
      ctc_two_vec (G.lapMatrix ℝ) f0 f1 (b last) ((d : ℝ) - s0) ((d : ℝ) - s1)
        hLf0 hLf1 hf01 hf0pos hf1pos
    have hmax : max ((d : ℝ) - s0) ((d : ℝ) - s1) = (d : ℝ) - s1 := max_eq_right (by linarith)
    rw [hmax] at hzu
    have hlow := ctc_pin_ge (G.lapMatrix ℝ) ν b hb_norm hb_exp last (ν sec) hνsec z hzv
    exact le_of_mul_le_mul_right (hlow.trans hzu) hz
  by_cases hlt : ν sec < d
  · -- S10
    have hS10 : ((d : ℝ) - ν sec) ^ 2 ≤ μ i1 := by
      obtain ⟨hC1, hCt1⟩ := ctc_restrict G d hbip hreg (b last) (ν last) (hb_eig last)
      obtain ⟨hC2, hCt2⟩ := ctc_restrict G d hbip hreg (b sec) (ν sec) (hb_eig sec)
      rw [← hC] at hC1 hCt1 hC2 hCt2
      set x1 : I → ℝ := fun i => (b last) (Sum.inl i)
      set y1 : O → ℝ := fun o => (b last) (Sum.inr o)
      set x2 : I → ℝ := fun i => (b sec) (Sum.inl i)
      set y2 : O → ℝ := fun o => (b sec) (Sum.inr o)
      have hB1 : (b last) = Sum.elim x1 y1 := by funext v; rcases v with i | o <;> rfl
      have hB2 : (b sec) = Sum.elim x2 y2 := by funext v; rcases v with i | o <;> rfl
      set a := (d : ℝ) - ν last
      set c := (d : ℝ) - ν sec
      have hc : 0 < c := by simp only [c]; linarith
      have hca : c ≤ a := by simp only [a, c]; linarith
      have horth : x1 ⬝ᵥ x2 + y1 ⬝ᵥ y2 = 0 := by
        have := hb_orth last sec
        rw [if_neg hsl.symm, hB1, hB2, ctc_dot_elim] at this
        exact this
      have hn1 : x1 ⬝ᵥ x1 + y1 ⬝ᵥ y1 = 1 := by
        have := hb1 last; rw [hB1, ctc_dot_elim] at this; exact this
      have hn2 : x2 ⬝ᵥ x2 + y2 ⬝ᵥ y2 = 1 := by
        have := hb1 sec; rw [hB2, ctc_dot_elim] at this; exact this
      have hx12 : a * (x1 ⬝ᵥ x2) = c * (y1 ⬝ᵥ y2) := by
        have h := ctc_adj_dot C y1 x2
        rw [hC1, hCt2, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul] at h
        exact h
      have hy12 : y1 ⬝ᵥ y2 = 0 := by
        have hx : x1 ⬝ᵥ x2 = -(y1 ⬝ᵥ y2) := by linarith
        rw [hx] at hx12
        have hac : 0 < a + c := by linarith
        have h0 : (a + c) * (y1 ⬝ᵥ y2) = 0 := by linear_combination (-1 : ℝ) * hx12
        rcases mul_eq_zero.mp h0 with h | h
        · exact absurd h hac.ne'
        · exact h
      have hMy1 : (Cᴴ * C) *ᵥ y1 = a ^ 2 • y1 := by
        rw [hMv, hC1, mulVec_smul, hCt1, smul_smul, sq]
      have hMy2 : (Cᴴ * C) *ᵥ y2 = c ^ 2 • y2 := by
        rw [hMv, hC2, mulVec_smul, hCt2, smul_smul, sq]
      have hxy1 : a ^ 2 * (x1 ⬝ᵥ x1) = a ^ 2 * (y1 ⬝ᵥ y1) := by
        have h := ctc_adj_dot C y1 (C *ᵥ y1)
        rw [← hMv, hMy1, hC1, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul,
          dotProduct_smul, smul_eq_mul] at h
        linear_combination h
      have hxy2 : c ^ 2 * (x2 ⬝ᵥ x2) = c ^ 2 * (y2 ⬝ᵥ y2) := by
        have h := ctc_adj_dot C y2 (C *ᵥ y2)
        rw [← hMv, hMy2, hC2, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul,
          dotProduct_smul, smul_eq_mul] at h
        linear_combination h
      have ha2 : 0 < a ^ 2 := by
        have : 0 < a := by linarith
        positivity
      have hc2 : 0 < c ^ 2 := by positivity
      have hp1 : 0 < y1 ⬝ᵥ y1 := by
        have := mul_left_cancel₀ ha2.ne' hxy1; linarith
      have hp2 : 0 < y2 ⬝ᵥ y2 := by
        have := mul_left_cancel₀ hc2.ne' hxy2; linarith
      obtain ⟨z, hz, hzv, hzl, -⟩ :=
        ctc_two_vec (Cᴴ * C) y1 y2 (u i0) (a ^ 2) (c ^ 2) hMy1 hMy2 hy12 hp1 hp2
      have hmin : min (a ^ 2) (c ^ 2) = c ^ 2 :=
        min_eq_right (pow_le_pow_left₀ hc.le hca 2)
      rw [hmin] at hzl
      have hup := ctc_pin_le (Cᴴ * C) μ u hu_norm hu_exp i0 (μ i1) hμ1 z hzv
      exact le_of_mul_le_mul_right (hzl.trans hup) hz
    have hA : μ i1 ≤ ((d : ℝ) - ν sec) ^ 2 := by
      rw [← hss1]; exact pow_le_pow_left₀ hs1nn (by linarith) 2
    show μ i1 = _
    linarith
  · replace hlt := not_lt.mp hlt
    have hs1z : s1 = 0 := by linarith
    have hνd : ν sec = d := by linarith
    show μ i1 = _
    rw [← hss1, hs1z, hνd]; ring
