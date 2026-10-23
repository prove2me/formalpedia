-- Prove2me | solution 1 for AlonMilman1985.prop3_1_lambda1_boxProd_faithful
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T05:05:43.221108+00:00
-- url     : https://prove2.me/submissions/14306e2a-5adc-4054-b51c-ecd1cfcc8b3e

import Mathlib
import Definitions.Def_AlonMilman_Diameter_lambda1

open scoped InnerProductSpace

namespace AM86

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

lemma expand {N : ℕ} (b : OrthonormalBasis (Fin N) ℝ E) (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric)
    (μ : Fin N → ℝ) (hb : ∀ i, T (b i) = μ i • b i) (x : E) :
    ⟪x, T x⟫_ℝ = ∑ i, μ i * ⟪b i, x⟫_ℝ ^ 2 := by
  rw [← b.sum_inner_mul_inner x (T x)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← hT, hb, real_inner_smul_left, real_inner_comm x (b i)]; ring

lemma expand_norm {N : ℕ} (b : OrthonormalBasis (Fin N) ℝ E) (x : E) :
    ‖x‖ ^ 2 = ∑ i, ⟪b i, x⟫_ℝ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, ← b.sum_inner_mul_inner x x]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [real_inner_comm x (b i)]; ring

lemma expand_inner {N : ℕ} (b : OrthonormalBasis (Fin N) ℝ E) (x u : E) :
    ⟪x, u⟫_ℝ = ∑ i, ⟪b i, x⟫_ℝ * ⟪b i, u⟫_ℝ := by
  rw [← b.sum_inner_mul_inner x u]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [real_inner_comm x (b i)]

/-- Variational facts for the second smallest eigenvalue, given a nonzero null vector `u`
and positive semidefiniteness. -/
theorem second {N : ℕ} (hN : 2 ≤ N) (b : OrthonormalBasis (Fin N) ℝ E) (T : E →ₗ[ℝ] E)
    (hT : T.IsSymmetric) (μ : Fin N → ℝ) (hμ : Antitone μ) (hb : ∀ i, T (b i) = μ i • b i)
    (hpsd : ∀ x, 0 ≤ ⟪x, T x⟫_ℝ) (u : E) (hu : u ≠ 0) (hTu : T u = 0) :
    (∀ x, ⟪x, u⟫_ℝ = 0 → μ ⟨N - 2, by omega⟩ * ‖x‖ ^ 2 ≤ ⟪x, T x⟫_ℝ) ∧
    (∃ x, x ≠ 0 ∧ ⟪x, u⟫_ℝ = 0 ∧ ⟪x, T x⟫_ℝ ≤ μ ⟨N - 2, by omega⟩ * ‖x‖ ^ 2) := by
  set k : Fin N := ⟨N - 2, by omega⟩
  set l : Fin N := ⟨N - 1, by omega⟩
  have hkl : k ≠ l := by simp [k, l, Fin.ext_iff]; omega
  have hμnn : ∀ i, 0 ≤ μ i := fun i => by
    have := hpsd (b i)
    rw [hb, real_inner_smul_right, real_inner_self_eq_norm_sq, b.orthonormal.1 i] at this
    simpa using this
  have hge : ∀ i, i ≠ l → μ k ≤ μ i := fun i hi => hμ (by
    simp only [k, l, Fin.le_def, ne_eq, Fin.ext_iff] at hi ⊢; omega)
  have hlk : μ l ≤ μ k := hμ (by simp only [k, l, Fin.le_def]; omega)
  have hd : ∀ i, μ i * ⟪b i, u⟫_ℝ = 0 := fun i => by
    have : ⟪b i, T u⟫_ℝ = 0 := by rw [hTu, inner_zero_right]
    rw [← hT, hb, real_inner_smul_left] at this; exact this
  constructor
  · intro x hx
    rw [expand b T hT μ hb x, expand_norm b x, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    by_cases hi : i = l
    · subst hi
      rcases eq_or_lt_of_le hlk with h | h
      · rw [h]
      · -- the bottom eigenvalue is simple: u ∥ b l and x ⊥ b l
        have hdi : ∀ i, i ≠ l → ⟪b i, u⟫_ℝ = 0 := fun i hi => by
          have h1 := hd i
          have : μ i ≠ 0 := by have := hge i hi; have := hμnn l; linarith
          exact (mul_eq_zero.mp h1).resolve_left this
        have hxu := expand_inner b x u
        rw [Finset.sum_eq_single l (fun i _ hi => by rw [hdi i hi, mul_zero]) (by simp)] at hxu
        have hul : ⟪b l, u⟫_ℝ ≠ 0 := by
          intro h0
          apply hu
          have := expand_norm b u
          rw [Finset.sum_eq_single l (fun i _ hi => by rw [hdi i hi]; ring) (by simp), h0] at this
          simpa using this
        have : ⟪b l, x⟫_ℝ = 0 := by
          rw [hx] at hxu
          exact (mul_eq_zero.mp hxu.symm).resolve_right hul
        rw [this]; simp
    · exact mul_le_mul_of_nonneg_right (hge i hi) (sq_nonneg _)
  · by_cases h0 : ⟪b l, u⟫_ℝ = 0 ∧ ⟪b k, u⟫_ℝ = 0
    · refine ⟨b k, ?_, h0.2, ?_⟩
      · intro h; have := b.orthonormal.1 k; rw [h, norm_zero] at this; exact zero_ne_one this
      · rw [hb, real_inner_smul_right, real_inner_self_eq_norm_sq]
    · set α := ⟪b l, u⟫_ℝ
      set β := ⟪b k, u⟫_ℝ
      set x := α • b k - β • b l
      have hkk : ⟪b k, b k⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, b.orthonormal.1 k]; norm_num
      have hll : ⟪b l, b l⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, b.orthonormal.1 l]; norm_num
      have hkl0 : ⟪b k, b l⟫_ℝ = 0 := b.orthonormal.2 hkl
      have hlk0 : ⟪b l, b k⟫_ℝ = 0 := b.orthonormal.2 hkl.symm
      have hn2 : ‖x‖ ^ 2 = α ^ 2 + β ^ 2 := by
        rw [← real_inner_self_eq_norm_sq]
        simp only [x, inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
          hkk, hll, hkl0, hlk0]; ring
      refine ⟨x, ?_, ?_, ?_⟩
      · intro hx0
        have : ‖x‖ ^ 2 = 0 := by rw [hx0, norm_zero]; ring
        rw [hn2] at this
        apply h0; constructor <;> nlinarith [sq_nonneg α, sq_nonneg β]
      · simp only [x, inner_sub_left, real_inner_smul_left, α, β]; ring
      · have hTx : T x = (α * μ k) • b k - (β * μ l) • b l := by
          simp only [x, map_sub, map_smul, hb, smul_smul]
        rw [hTx, hn2]
        simp only [x, inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
          hkk, hll, hkl0, hlk0]
        nlinarith [mul_le_mul_of_nonneg_left hlk (sq_nonneg β)]

end AM86

namespace AM86

open Matrix

/-- twice the Laplacian quadratic form -/
def Q {V : Type} [Fintype V] (H : SimpleGraph V) [DecidableRel H.Adj] (x : V → ℝ) : ℝ :=
  ∑ i, ∑ j, if H.Adj i j then (x i - x j) ^ 2 else 0

lemma Q_nonneg {V : Type} [Fintype V] (H : SimpleGraph V) [DecidableRel H.Adj] (x : V → ℝ) :
    0 ≤ Q H x := Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => by split_ifs <;> positivity))

lemma inner_lap {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (x : V → ℝ) :
    ⟪(WithLp.toLp 2 x : EuclideanSpace ℝ V), Matrix.toEuclideanLin (H.lapMatrix ℝ) (WithLp.toLp 2 x)⟫_ℝ
      = Q H x / 2 := by
  have h1 : Matrix.toEuclideanLin (H.lapMatrix ℝ) (WithLp.toLp 2 x) = WithLp.toLp 2 (H.lapMatrix ℝ *ᵥ x) := by
    simp [Matrix.toEuclideanLin]
  rw [h1]
  have h2 : ⟪(WithLp.toLp 2 x : EuclideanSpace ℝ V), WithLp.toLp 2 (H.lapMatrix ℝ *ᵥ x)⟫_ℝ =
      x ⬝ᵥ (H.lapMatrix ℝ *ᵥ x) := by simp [PiLp.inner_apply, dotProduct, mul_comm]
  rw [h2, ← Matrix.toLinearMap₂'_apply', SimpleGraph.lapMatrix_toLinearMap₂']; rfl

lemma inner_ones {V : Type} [Fintype V] (x : V → ℝ) :
    ⟪(WithLp.toLp 2 x : EuclideanSpace ℝ V), WithLp.toLp 2 (fun _ => (1 : ℝ))⟫_ℝ = ∑ i, x i := by
  simp [PiLp.inner_apply]

lemma norm_sq_toLp {V : Type} [Fintype V] (x : V → ℝ) :
    ‖(WithLp.toLp 2 x : EuclideanSpace ℝ V)‖ ^ 2 = ∑ i, x i ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]; simp [Real.norm_eq_abs, sq_abs]

/-- variational characterisation of `λ₁` -/
theorem graph_var {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (hV : 2 ≤ Fintype.card V) :
    (∀ x : V → ℝ, ∑ i, x i = 0 → AlonMilman.Diameter.lambda1 H * ∑ i, x i ^ 2 ≤ Q H x / 2) ∧
    (∃ x : V → ℝ, x ≠ 0 ∧ ∑ i, x i = 0 ∧ Q H x / 2 ≤ AlonMilman.Diameter.lambda1 H * ∑ i, x i ^ 2) := by
  have hA := H.isHermitian_lapMatrix ℝ
  have hS := (Matrix.isSymmetric_toEuclideanLin_iff (𝕜 := ℝ)).mpr hA
  have hn : Module.finrank ℝ (EuclideanSpace ℝ V) = Fintype.card V := finrank_euclideanSpace
  have hl : AlonMilman.Diameter.lambda1 H = hS.eigenvalues hn ⟨Fintype.card V - 2, by omega⟩ := by
    unfold AlonMilman.Diameter.lambda1; rw [dif_pos hV]; rfl
  have hb : ∀ i, Matrix.toEuclideanLin (H.lapMatrix ℝ) (hS.eigenvectorBasis hn i) = hS.eigenvalues hn i • hS.eigenvectorBasis hn i := by
    intro i; have := hS.apply_eigenvectorBasis hn i; simpa using this
  have hpsd : ∀ x, 0 ≤ ⟪x, Matrix.toEuclideanLin (H.lapMatrix ℝ) x⟫_ℝ := by
    intro x
    have := inner_lap H x.ofLp
    simp only [WithLp.toLp_ofLp] at this
    rw [this]; exact div_nonneg (Q_nonneg H _) (by norm_num)
  set u : EuclideanSpace ℝ V := WithLp.toLp 2 (fun _ => (1 : ℝ))
  have hu : u ≠ 0 := by
    intro h
    have : ‖u‖ ^ 2 = 0 := by rw [h, norm_zero]; ring
    rw [norm_sq_toLp] at this
    simp at this; omega
  have hTu : Matrix.toEuclideanLin (H.lapMatrix ℝ) u = 0 := by
    have h1 : Matrix.toEuclideanLin (H.lapMatrix ℝ) (WithLp.toLp 2 (fun _ => (1 : ℝ))) =
        WithLp.toLp 2 (H.lapMatrix ℝ *ᵥ (fun _ => (1 : ℝ))) := by simp [Matrix.toEuclideanLin]
    simp only [u]; rw [h1, SimpleGraph.lapMatrix_mulVec_const_eq_zero]; rfl
  obtain ⟨h1, h2⟩ := second hV (hS.eigenvectorBasis hn) (Matrix.toEuclideanLin (H.lapMatrix ℝ)) hS (hS.eigenvalues hn)
    (hS.eigenvalues_antitone hn) hb hpsd u hu hTu
  rw [hl]
  constructor
  · intro x hx
    have := h1 (WithLp.toLp 2 x) (by rw [inner_ones]; exact hx)
    rw [norm_sq_toLp] at this
    have e := inner_lap H x
    exact this.trans_eq e
  · obtain ⟨y, hy0, hyu, hy⟩ := h2
    refine ⟨y.ofLp, ?_, ?_, ?_⟩
    · intro h; apply hy0; rw [← WithLp.toLp_ofLp 2 y, h]; rfl
    · have := inner_ones y.ofLp; simp only [WithLp.toLp_ofLp] at this; rw [← this]; exact hyu
    · have e := inner_lap H y.ofLp
      have n := norm_sq_toLp y.ofLp
      simp only [WithLp.toLp_ofLp] at e n
      rw [← e, ← n]; exact hy

end AM86

namespace AM86

lemma Q_shift {V : Type} [Fintype V] (H : SimpleGraph V) [DecidableRel H.Adj] (x : V → ℝ) (c : ℝ) :
    Q H (fun i => x i - c) = Q H x := by
  unfold Q; congr 1; funext i; congr 1; funext j; split_ifs <;> ring

lemma Q_const {V : Type} [Fintype V] (H : SimpleGraph V) [DecidableRel H.Adj] (c : ℝ) :
    Q H (fun _ => c) = 0 := by
  unfold Q; simp

lemma Q_box {V W : Type} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W] (G : SimpleGraph V) (G' : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel G'.Adj] [DecidableRel (G.boxProd G').Adj] (f : V × W → ℝ) :
    Q (G.boxProd G') f = ∑ w, Q G (fun v => f (v, w)) + ∑ v, Q G' (fun w => f (v, w)) := by
  unfold Q
  have hsplit : ∀ p q : V × W, (if (G.boxProd G').Adj p q then (f p - f q) ^ 2 else 0) =
      (if G.Adj p.1 q.1 ∧ p.2 = q.2 then (f p - f q) ^ 2 else 0) +
      (if G'.Adj p.2 q.2 ∧ p.1 = q.1 then (f p - f q) ^ 2 else 0) := by
    intro p q
    have hiff := SimpleGraph.boxProd_adj (G := G) (H := G') (x := p) (y := q)
    by_cases h1 : G.Adj p.1 q.1 ∧ p.2 = q.2
    · have h2 : ¬ (G'.Adj p.2 q.2 ∧ p.1 = q.1) := fun h => G.ne_of_adj h1.1 h.2
      rw [if_pos (hiff.mpr (Or.inl h1)), if_pos h1, if_neg h2, add_zero]
    · by_cases h2 : G'.Adj p.2 q.2 ∧ p.1 = q.1
      · rw [if_pos (hiff.mpr (Or.inr h2)), if_neg h1, if_pos h2, zero_add]
      · have : ¬ (G.boxProd G').Adj p q := fun h => (hiff.mp h).elim h1 h2
        rw [if_neg this, if_neg h1, if_neg h2, add_zero]
  simp_rw [hsplit, Finset.sum_add_distrib]
  congr 1
  · rw [Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun w _ => Finset.sum_congr rfl (fun v _ => ?_))
    rw [Fintype.sum_prod_type]
    simp only
    rw [Finset.sum_congr rfl (fun v' _ => Finset.sum_eq_single w
      (fun b _ hb => by rw [if_neg (fun h => hb h.2.symm)]) (by simp))]
    refine Finset.sum_congr rfl (fun v' _ => ?_)
    by_cases h : G.Adj v v' <;> simp [h]
  · rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun v _ => Finset.sum_congr rfl (fun w _ => ?_))
    rw [Fintype.sum_prod_type]
    simp only
    rw [Finset.sum_eq_single v (fun b _ hb => Finset.sum_eq_zero (fun w' _ => by
      rw [if_neg (fun h => hb h.2.symm)])) (by simp)]
    refine Finset.sum_congr rfl (fun w' _ => ?_)
    by_cases h : G'.Adj w w' <;> simp [h]

/-- Jensen-type step: `Σ_v Q(m + d_v) ≥ |V| Q(m)` when `Σ_v d_v = 0`. -/
lemma Q_jensen {V W : Type} [Fintype V] [Fintype W] (H : SimpleGraph W) [DecidableRel H.Adj]
    (m : W → ℝ) (d : V → W → ℝ) (hd : ∀ w, ∑ v, d v w = 0) :
    (Fintype.card V : ℝ) * Q H m ≤ ∑ v, Q H (fun w => m w + d v w) := by
  unfold Q
  rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum; intro i _
  rw [Finset.mul_sum, Finset.sum_comm]
  apply Finset.sum_le_sum; intro j _
  split_ifs
  · have e : ∀ v, (m i + d v i - (m j + d v j)) ^ 2 =
        (m i - m j) ^ 2 + 2 * (m i - m j) * (d v i - d v j) + (d v i - d v j) ^ 2 := fun v => by ring
    simp only [e, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, hd i, hd j,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have : 0 ≤ ∑ v, (d v i - d v j) ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    linarith
  · simp

theorem box_lower {V W : Type} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (G' : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel G'.Adj] [DecidableRel (G.boxProd G').Adj]
    (hV : 2 ≤ Fintype.card V) (hW : 2 ≤ Fintype.card W) (f : V × W → ℝ) (hf : ∑ p, f p = 0) :
    min (AlonMilman.Diameter.lambda1 G) (AlonMilman.Diameter.lambda1 G') * ∑ p, f p ^ 2
      ≤ Q (G.boxProd G') f / 2 := by
  set l1 := AlonMilman.Diameter.lambda1 G
  set l2 := AlonMilman.Diameter.lambda1 G'
  have hVpos : (0 : ℝ) < Fintype.card V := by exact_mod_cast (show 0 < Fintype.card V by omega)
  set nV : ℝ := (Fintype.card V : ℝ)
  set m : W → ℝ := fun w => (∑ v, f (v, w)) / nV
  set g : V → W → ℝ := fun v w => f (v, w) - m w
  have hg : ∀ w, ∑ v, g v w = 0 := by
    intro w
    simp only [g, m, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp; ring
  have hm : ∑ w, m w = 0 := by
    simp only [m, ← Finset.sum_div]
    rw [Finset.sum_comm, ← Fintype.sum_prod_type' (fun v w => f (v, w))]
    simp [hf]
  obtain ⟨A1, -⟩ := graph_var G hV
  obtain ⟨B1, -⟩ := graph_var G' hW
  -- column energies
  have hcol : ∀ w, l1 * ∑ v, g v w ^ 2 ≤ Q G (fun v => f (v, w)) / 2 := by
    intro w
    have := A1 (fun v => g v w) (hg w)
    have e : Q G (fun v => g v w) = Q G (fun v => f (v, w)) := Q_shift G _ (m w)
    rw [e] at this; exact this
  -- row energies
  have hrow : nV * Q G' m ≤ ∑ v, Q G' (fun w => f (v, w)) := by
    have := Q_jensen G' m g hg
    convert this using 3 with v
    funext w; simp [g]
  have hmq := B1 m hm
  -- Pythagoras
  have hpy : ∑ p, f p ^ 2 = ∑ w, ∑ v, g v w ^ 2 + nV * ∑ w, m w ^ 2 := by
    rw [Fintype.sum_prod_type, Finset.sum_comm, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun w _ => ?_)
    have e : ∀ v, f (v, w) ^ 2 = g v w ^ 2 + 2 * m w * g v w + m w ^ 2 := by
      intro v; simp only [g]; ring
    simp only [e, Finset.sum_add_distrib, ← Finset.mul_sum, hg w, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul]
    ring
  rw [Q_box, hpy]
  have hX : 0 ≤ ∑ w, ∑ v, g v w ^ 2 := Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have hY : 0 ≤ ∑ w, m w ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have h1 : min l1 l2 * ∑ w, ∑ v, g v w ^ 2 ≤ l1 * ∑ w, ∑ v, g v w ^ 2 :=
    mul_le_mul_of_nonneg_right (min_le_left _ _) hX
  have h2 : min l1 l2 * (nV * ∑ w, m w ^ 2) ≤ l2 * (nV * ∑ w, m w ^ 2) :=
    mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)
  have h3 : l1 * ∑ w, ∑ v, g v w ^ 2 ≤ (∑ w, Q G (fun v => f (v, w))) / 2 := by
    rw [Finset.mul_sum, Finset.sum_div]; exact Finset.sum_le_sum (fun w _ => hcol w)
  have h4 : l2 * (nV * ∑ w, m w ^ 2) ≤ (∑ v, Q G' (fun w => f (v, w))) / 2 := by
    nlinarith
  linarith

end AM86

open Classical in
theorem solution {V W : Type} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W] (G : SimpleGraph V) (G' : SimpleGraph W)
    (hG : G.Connected) (hG' : G'.Connected)
    (hV : 1 < Fintype.card V) (hW : 1 < Fintype.card W) :
    AlonMilman.Diameter.lambda1 (G.boxProd G') =
      min (AlonMilman.Diameter.lambda1 G) (AlonMilman.Diameter.lambda1 G') := by
  have hP : 2 ≤ Fintype.card (V × W) := by
    rw [Fintype.card_prod]; nlinarith
  obtain ⟨P1, ⟨f, hf0, hfs, hfq⟩⟩ := AM86.graph_var (G.boxProd G') hP
  have hpos : ∀ h : V × W → ℝ, h ≠ 0 → 0 < ∑ p, h p ^ 2 := by
    intro h hh
    by_contra hc
    apply hh; funext p
    have h0 : ∑ p, h p ^ 2 = 0 := le_antisymm (not_lt.mp hc) (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)).mp h0 p (Finset.mem_univ _)
    simpa using this
  apply le_antisymm
  · -- upper bound via functions of one coordinate
    apply le_min
    · obtain ⟨-, ⟨x, hx0, hxs, hxq⟩⟩ := AM86.graph_var G hV
      set F : V × W → ℝ := fun p => x p.1
      have hF0 : F ≠ 0 := by
        intro h; apply hx0; funext v
        obtain ⟨w⟩ : Nonempty W := Fintype.card_pos_iff.mp (by omega)
        have := congrFun h (v, w); simpa [F] using this
      have hFs : ∑ p, F p = 0 := by
        have : ∑ p, F p = (Fintype.card W : ℝ) * ∑ v, x v := by simp [F, Fintype.sum_prod_type, Finset.mul_sum]
        rw [this, hxs, mul_zero]
      have hFq : AM86.Q (G.boxProd G') F = (Fintype.card W : ℝ) * AM86.Q G x := by
        rw [AM86.Q_box]; simp [F, AM86.Q_const]
      have hFn : ∑ p, F p ^ 2 = (Fintype.card W : ℝ) * ∑ v, x v ^ 2 := by
        simp [F, Fintype.sum_prod_type, Finset.mul_sum]
      have := P1 F hFs
      rw [hFq, hFn] at this
      have hpF := hpos F hF0
      rw [hFn] at hpF
      have hWpos : (0 : ℝ) < Fintype.card W := by exact_mod_cast (show 0 < Fintype.card W by omega)
      have hxpos : 0 < ∑ v, x v ^ 2 := by
        by_contra h; rw [not_lt] at h; nlinarith
      nlinarith
    · obtain ⟨-, ⟨x, hx0, hxs, hxq⟩⟩ := AM86.graph_var G' hW
      set F : V × W → ℝ := fun p => x p.2
      have hF0 : F ≠ 0 := by
        intro h; apply hx0; funext w
        obtain ⟨v⟩ : Nonempty V := Fintype.card_pos_iff.mp (by omega)
        have := congrFun h (v, w); simpa [F] using this
      have hFs : ∑ p, F p = 0 := by
        simp [F, Fintype.sum_prod_type, hxs]
      have hFq : AM86.Q (G.boxProd G') F = (Fintype.card V : ℝ) * AM86.Q G' x := by
        rw [AM86.Q_box]; simp [F, AM86.Q_const]
      have hFn : ∑ p, F p ^ 2 = (Fintype.card V : ℝ) * ∑ w, x w ^ 2 := by
        simp [F, Fintype.sum_prod_type, Finset.mul_sum]
      have := P1 F hFs
      rw [hFq, hFn] at this
      have hpF := hpos F hF0
      rw [hFn] at hpF
      have hVpos : (0 : ℝ) < Fintype.card V := by exact_mod_cast (show 0 < Fintype.card V by omega)
      have hxpos : 0 < ∑ w, x w ^ 2 := by
        by_contra h; rw [not_lt] at h; nlinarith
      nlinarith
  · have hl := AM86.box_lower G G' hV hW f hfs
    have hp := hpos f hf0
    nlinarith
