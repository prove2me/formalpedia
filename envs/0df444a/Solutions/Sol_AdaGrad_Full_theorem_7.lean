-- Prove2me | solution 1 for AdaGrad.Full.theorem_7
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-08T21:12:23.238977+00:00
-- url     : https://prove2.me/submissions/72c8a273-e9b3-41e3-8e90-bd3b74770c0f

import Mathlib
import Definitions.Def_AdaGrad_Full_Algorithm2
open scoped MatrixOrder InnerProductSpace

set_option autoImplicit false

namespace AdaGrad.Full.T7Aux

open AdaGrad.Full Matrix

variable {d : ℕ}

lemma herm_T {A : Matrix (Fin d) (Fin d) ℝ} (h : A.IsHermitian) : Aᵀ = A := by
  have := h.eq
  rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this

lemma symm_dot {A : Matrix (Fin d) (Fin d) ℝ} (h : Aᵀ = A) (v u : Fin d → ℝ) :
    v ⬝ᵥ (A *ᵥ u) = (A *ᵥ v) ⬝ᵥ u := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, h]

lemma psd_dot {A : Matrix (Fin d) (Fin d) ℝ} (h : A.PosSemidef) (v : Fin d → ℝ) :
    0 ≤ v ⬝ᵥ (A *ᵥ v) := by
  simpa using h.dotProduct_mulVec_nonneg v

lemma trace_mul_nonneg {P Q : Matrix (Fin d) (Fin d) ℝ} (hP : P.PosSemidef)
    (hQ : Q.PosSemidef) : 0 ≤ (P * Q).trace := by
  have h := psd_dot (hP.hadamard hQ) (fun _ => 1)
  have hQs : ∀ i j, Q j i = Q i j := fun i j => by
    have := congrFun (congrFun (herm_T hQ.1) i) j
    simpa [Matrix.transpose_apply] using this
  have e : (P * Q).trace = (fun _ => (1 : ℝ)) ⬝ᵥ ((P ⊙ Q) *ᵥ fun _ => 1) := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, dotProduct, Matrix.mulVec,
      Matrix.hadamard, Matrix.of_apply, one_mul, mul_one, hQs]
  rw [e]; exact h

lemma trace_mul_vecMulVec (A : Matrix (Fin d) (Fin d) ℝ) (v : Fin d → ℝ) :
    (A * vecMulVec v v).trace = v ⬝ᵥ (A *ᵥ v) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.vecMulVec_apply, dotProduct,
    Matrix.mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  ring

lemma psd_c_sub_outer (v : Fin d → ℝ) (c : ℝ) (hc : v ⬝ᵥ v ≤ c) :
    (c • (1 : Matrix (Fin d) (Fin d) ℝ) - vecMulVec v v).PosSemidef := by
  refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · ext i j
    simp [Matrix.conjTranspose_apply, Matrix.vecMulVec_apply, Matrix.one_apply, mul_comm,
      eq_comm]
  · intro x
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ v x
    have hxx : 0 ≤ x ⬝ᵥ x := by
      simp only [dotProduct]; exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
    have e : star x ⬝ᵥ ((c • (1 : Matrix (Fin d) (Fin d) ℝ) - vecMulVec v v) *ᵥ x)
        = c * (x ⬝ᵥ x) - (v ⬝ᵥ x) ^ 2 := by
      simp only [star_trivial, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
        dotProduct_sub, dotProduct_smul, smul_eq_mul]
      have : x ⬝ᵥ (vecMulVec v v *ᵥ x) = (v ⬝ᵥ x) ^ 2 := by
        simp only [dotProduct, Matrix.mulVec, Matrix.vecMulVec_apply, sq, Finset.sum_mul,
          Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
        ring
      rw [this]
    rw [e]
    have h1 : (v ⬝ᵥ x) ^ 2 ≤ (v ⬝ᵥ v) * (x ⬝ᵥ x) := by
      simpa [dotProduct, sq] using hcs
    nlinarith

lemma sqrt_mono {P Q : Matrix (Fin d) (Fin d) ℝ} (hP : P.PosSemidef) (hQ : Q.PosSemidef)
    (h : (Q * Q - P * P).PosSemidef) : (Q - P).PosSemidef := by
  have hE : (Q - P).IsHermitian := hQ.1.sub hP.1
  rw [hE.posSemidef_iff_eigenvalues_nonneg]
  intro i
  by_contra hneg
  push Not at hneg
  set μ := hE.eigenvalues i with hμ
  set v : Fin d → ℝ := ⇑(hE.eigenvectorBasis i) with hvdef
  have hv : (Q - P) *ᵥ v = μ • v := hE.mulVec_eigenvectorBasis i
  have hvn : v ⬝ᵥ v = 1 := by
    have h1 := (hE.eigenvectorBasis).orthonormal.1 i
    have h2 : ⟪hE.eigenvectorBasis i, hE.eigenvectorBasis i⟫_ℝ = 1 := by
      rw [real_inner_self_eq_norm_sq, h1]; norm_num
    rw [EuclideanSpace.inner_eq_star_dotProduct] at h2
    simpa [hvdef] using h2
  have hQv : Q *ᵥ v = P *ᵥ v + μ • v := by
    rw [← hv, Matrix.sub_mulVec]; abel
  have h1 := psd_dot h v
  rw [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, dotProduct_sub,
    symm_dot (herm_T hQ.1), symm_dot (herm_T hP.1), hQv] at h1
  have ha := psd_dot hP v
  have hb := psd_dot hQ v
  rw [hQv] at hb
  set w := P *ᵥ v
  have e1 : (w + μ • v) ⬝ᵥ (w + μ • v) = w ⬝ᵥ w + 2 * μ * (v ⬝ᵥ w) + μ ^ 2 * (v ⬝ᵥ v) := by
    simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul,
      dotProduct_comm w v]
    ring
  have e2 : v ⬝ᵥ (w + μ • v) = v ⬝ᵥ w + μ * (v ⬝ᵥ v) := by
    simp only [dotProduct_add, dotProduct_smul, smul_eq_mul]
  rw [e1] at h1
  rw [e2] at hb
  rw [hvn] at h1 hb
  have hμ0 : μ < 0 := by simpa using hneg
  have h3 : 2 * (v ⬝ᵥ w) + μ ≤ 0 := by
    by_contra hc
    push Not at hc
    nlinarith [mul_neg_of_neg_of_pos hμ0 hc]
  linarith

lemma core {X Y : Matrix (Fin d) (Fin d) ℝ} (hX : X.PosSemidef) (hY : Y.PosSemidef)
    (g : Fin d → ℝ) (hXY : X * X = Y * Y + vecMulVec g g) (hD : (X - Y).PosSemidef)
    (η : ℝ) (z : Fin d → ℝ) :
    η * (g ⬝ᵥ z) - 1 / 2 * (z ⬝ᵥ (X *ᵥ z)) ≤ η ^ 2 * (X.trace - Y.trace) := by
  have hzz : 0 ≤ z ⬝ᵥ z := by
    simp only [dotProduct]; exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have key : ∀ ε > (0 : ℝ),
      η * (g ⬝ᵥ z) - 1 / 2 * (z ⬝ᵥ (X *ᵥ z)) ≤ η ^ 2 * (X.trace - Y.trace) + ε * (z ⬝ᵥ z) := by
    intro ε hε
    set A : Matrix (Fin d) (Fin d) ℝ := ε • (1 : Matrix (Fin d) (Fin d) ℝ) + X with hAdef
    have hApd : A.PosDef := (PosDef.one.smul hε).add_posSemidef hX
    have hdet : IsUnit A.det := (hApd.det_pos).ne'.isUnit
    set B := A⁻¹ with hBdef
    have hAB : A * B = 1 := Matrix.mul_nonsing_inv A hdet
    have hBA : B * A = 1 := Matrix.nonsing_inv_mul A hdet
    have hB : B.PosSemidef := hApd.inv.posSemidef
    set D := X - Y with hDdef
    have hXA : X = A - ε • (1 : Matrix (Fin d) (Fin d) ℝ) := by rw [hAdef]; abel
    have hXB : X * B = 1 - ε • B := by
      rw [hXA, Matrix.sub_mul, hAB, Matrix.smul_mul, Matrix.one_mul]
    have hBX : B * X = 1 - ε • B := by
      rw [hXA, Matrix.mul_sub, hBA, Matrix.mul_smul, Matrix.mul_one]
    have houter : vecMulVec g g = X * D + D * X - D * D := by
      have : vecMulVec g g = X * X - Y * Y := by rw [hXY]; abel
      rw [this, hDdef]; noncomm_ring
    have htr : (B * vecMulVec g g).trace
        = 2 * D.trace - 2 * ε * (B * D).trace - (B * (D * D)).trace := by
      rw [houter, Matrix.mul_sub, Matrix.mul_add, Matrix.trace_sub, Matrix.trace_add,
        ← Matrix.mul_assoc B X D, hBX, ← Matrix.mul_assoc B D X, Matrix.trace_mul_cycle B D X,
        hXB, Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul,
        Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul]
      ring
    have h1 : 0 ≤ (B * D).trace := trace_mul_nonneg hB hD
    have hDD : (D * D).PosSemidef := by
      have := posSemidef_conjTranspose_mul_self D
      rwa [hD.1.eq] at this
    have h2 : 0 ≤ (B * (D * D)).trace := trace_mul_nonneg hB hDD
    have hgB : g ⬝ᵥ (B *ᵥ g) ≤ 2 * (X.trace - Y.trace) := by
      rw [← trace_mul_vecMulVec, htr, ← Matrix.trace_sub]
      nlinarith
    set w := η • (B *ᵥ g) with hw
    have hAw : A *ᵥ w = η • g := by
      rw [hw, Matrix.mulVec_smul, Matrix.mulVec_mulVec, hAB, Matrix.one_mulVec]
    have hAT : Aᵀ = A := herm_T hApd.1
    have hFY := psd_dot hApd.posSemidef (z - w)
    have e1 : (z - w) ⬝ᵥ (A *ᵥ (z - w))
        = z ⬝ᵥ (A *ᵥ z) - 2 * η * (g ⬝ᵥ z) + η ^ 2 * (g ⬝ᵥ (B *ᵥ g)) := by
      rw [Matrix.mulVec_sub, hAw, dotProduct_sub, sub_dotProduct, sub_dotProduct,
        symm_dot hAT w z, hAw]
      simp only [dotProduct_smul, smul_dotProduct, smul_eq_mul, hw, dotProduct_comm z g,
        dotProduct_comm (B *ᵥ g) g]
      ring
    have e2 : z ⬝ᵥ (A *ᵥ z) = ε * (z ⬝ᵥ z) + z ⬝ᵥ (X *ᵥ z) := by
      rw [hAdef, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_add,
        dotProduct_smul, smul_eq_mul]
    rw [e1, e2] at hFY
    have h3 : η ^ 2 * (g ⬝ᵥ (B *ᵥ g)) ≤ η ^ 2 * (2 * (X.trace - Y.trace)) :=
      mul_le_mul_of_nonneg_left hgB (sq_nonneg η)
    nlinarith
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have := key (ε / (z ⬝ᵥ z + 1)) (by positivity)
  have h4 : ε / (z ⬝ᵥ z + 1) * (z ⬝ᵥ z) ≤ ε := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  linarith


/-! ## Euclidean bridges -/

lemma inner_dot (u v : EuclideanSpace ℝ (Fin d)) :
    ⟪u, v⟫_ℝ = WithLp.ofLp u ⬝ᵥ WithLp.ofLp v := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct_comm]

lemma mInner_dot (M : Matrix (Fin d) (Fin d) ℝ) (u v : EuclideanSpace ℝ (Fin d)) :
    mInner M u v = WithLp.ofLp u ⬝ᵥ (M *ᵥ WithLp.ofLp v) := by
  rw [mInner, inner_dot]; rfl

lemma norm_sq_dot (u : EuclideanSpace ℝ (Fin d)) :
    ‖u‖ ^ 2 = WithLp.ofLp u ⬝ᵥ WithLp.ofLp u := by
  rw [← real_inner_self_eq_norm_sq, inner_dot]

lemma mInner_add_mat (M N : Matrix (Fin d) (Fin d) ℝ) (u : EuclideanSpace ℝ (Fin d)) :
    mInner (M + N) u u = mInner M u u + mInner N u u := by
  simp only [mInner_dot, Matrix.add_mulVec, dotProduct_add]

lemma mInner_sub_mat (M N : Matrix (Fin d) (Fin d) ℝ) (u : EuclideanSpace ℝ (Fin d)) :
    mInner (M - N) u u = mInner M u u - mInner N u u := by
  simp only [mInner_dot, Matrix.sub_mulVec, dotProduct_sub]

lemma mInner_smul_one (c : ℝ) (u : EuclideanSpace ℝ (Fin d)) :
    mInner (c • (1 : Matrix (Fin d) (Fin d) ℝ)) u u = c * ‖u‖ ^ 2 := by
  rw [mInner_dot, norm_sq_dot, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul,
    smul_eq_mul]

lemma mInner_zero_mat (u : EuclideanSpace ℝ (Fin d)) :
    mInner (0 : Matrix (Fin d) (Fin d) ℝ) u u = 0 := by
  rw [mInner_dot, Matrix.zero_mulVec, dotProduct_zero]

lemma mInner_neg (M : Matrix (Fin d) (Fin d) ℝ) (u : EuclideanSpace ℝ (Fin d)) :
    mInner M (-u) (-u) = mInner M u u := by
  simp only [mInner_dot, WithLp.ofLp_neg, Matrix.mulVec_neg, neg_dotProduct, dotProduct_neg,
    neg_neg]

lemma mInner_nonneg {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.PosSemidef)
    (u : EuclideanSpace ℝ (Fin d)) : 0 ≤ mInner M u u := by
  rw [mInner_dot]; exact psd_dot hM _

lemma mInner_le_trace {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.PosSemidef)
    (u : EuclideanSpace ℝ (Fin d)) : mInner M u u ≤ ‖u‖ ^ 2 * M.trace := by
  set v := WithLp.ofLp u
  have h := trace_mul_nonneg hM (psd_c_sub_outer v (v ⬝ᵥ v) le_rfl)
  rw [Matrix.mul_sub, Matrix.trace_sub, trace_mul_vecMulVec, Matrix.mul_smul, Matrix.mul_one,
    Matrix.trace_smul, smul_eq_mul] at h
  rw [mInner_dot, norm_sq_dot]
  linarith

lemma mInner_expand {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.PosSemidef)
    (p q : EuclideanSpace ℝ (Fin d)) (s : ℝ) :
    mInner M (p + s • q) (p + s • q)
      = mInner M p p + 2 * s * mInner M q p + s ^ 2 * mInner M q q := by
  simp only [mInner_dot, WithLp.ofLp_add, WithLp.ofLp_smul, Matrix.mulVec_add,
    Matrix.mulVec_smul, add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul,
    smul_eq_mul]
  rw [symm_dot (herm_T hM.1) (WithLp.ofLp p) (WithLp.ofLp q),
    dotProduct_comm (M *ᵥ WithLp.ofLp p) (WithLp.ofLp q)]
  ring

/-! ## The matrices `G`, `S`, `H` -/

lemma outer_psd (v : EuclideanSpace ℝ (Fin d)) : (outer v).PosSemidef := by
  have := Matrix.posSemidef_vecMulVec_self_star (WithLp.ofLp v)
  simpa [outer] using this

lemma G_succ (g : ℕ → EuclideanSpace ℝ (Fin d)) (n : ℕ) :
    G g (n + 1) = G g n + outer (g (n + 1)) := by
  simp only [G]
  rw [Finset.sum_Icc_succ_top (by omega)]

lemma G_psd (g : ℕ → EuclideanSpace ℝ (Fin d)) (n : ℕ) : (G g n).PosSemidef :=
  posSemidef_sum _ fun i _ => outer_psd _

lemma S_psd (g : ℕ → EuclideanSpace ℝ (Fin d)) (n : ℕ) : (S g n).PosSemidef :=
  Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg _)

lemma S_sq (g : ℕ → EuclideanSpace ℝ (Fin d)) (n : ℕ) : S g n * S g n = G g n :=
  CFC.sqrt_mul_sqrt_self _ (Matrix.nonneg_iff_posSemidef.mpr (G_psd g n))

lemma S_zero (g : ℕ → EuclideanSpace ℝ (Fin d)) : S g 0 = 0 := by
  simp [S, G]

lemma D_psd (g : ℕ → EuclideanSpace ℝ (Fin d)) (n : ℕ) :
    (S g (n + 1) - S g n).PosSemidef := by
  refine sqrt_mono (S_psd g n) (S_psd g (n + 1)) ?_
  rw [S_sq, S_sq, G_succ, add_sub_cancel_left]
  exact outer_psd _

lemma H_psd {δ : ℝ} (hδ : 0 ≤ δ) (g : ℕ → EuclideanSpace ℝ (Fin d)) (n : ℕ) :
    (H δ g n).PosSemidef :=
  (PosSemidef.one.smul hδ).add (S_psd g n)

lemma mInner_H (δ : ℝ) (g : ℕ → EuclideanSpace ℝ (Fin d)) (n : ℕ)
    (u : EuclideanSpace ℝ (Fin d)) :
    mInner (H δ g n) u u = δ * ‖u‖ ^ 2 + mInner (S g n) u u := by
  rw [H, mInner_add_mat, mInner_smul_one]

lemma S_le_H {δ : ℝ} (hδ : 0 ≤ δ) (g : ℕ → EuclideanSpace ℝ (Fin d)) (n : ℕ)
    (hg : ‖g (n + 1)‖ ≤ δ) : (H δ g n - S g (n + 1)).PosSemidef := by
  refine sqrt_mono (S_psd g (n + 1)) (H_psd hδ g n) ?_
  have e : H δ g n * H δ g n - S g (n + 1) * S g (n + 1)
      = (δ ^ 2 • (1 : Matrix (Fin d) (Fin d) ℝ) - outer (g (n + 1))) + (2 * δ) • S g n := by
    rw [S_sq g (n + 1), G_succ, ← S_sq g n]
    simp only [H, add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      Matrix.mul_one, smul_smul]
    module
  rw [e]
  refine (psd_c_sub_outer _ _ ?_).add ((S_psd g n).smul (by linarith))
  rw [← norm_sq_dot]
  nlinarith [norm_nonneg (g (n + 1))]

lemma core_euc (g : ℕ → EuclideanSpace ℝ (Fin d)) (n : ℕ) (η : ℝ)
    (z : EuclideanSpace ℝ (Fin d)) :
    η * ⟪g (n + 1), z⟫_ℝ - 1 / 2 * mInner (S g (n + 1)) z z
      ≤ η ^ 2 * ((S g (n + 1)).trace - (S g n).trace) := by
  have h := core (S_psd g (n + 1)) (S_psd g n) (WithLp.ofLp (g (n + 1)))
    (by rw [S_sq, S_sq, G_succ]; rfl) (D_psd g n) η (WithLp.ofLp z)
  rw [inner_dot, mInner_dot]
  exact h

/-! ## Strong convexity at a minimizer -/

lemma strong_min {X : Set (EuclideanSpace ℝ (Fin d))} (hXc : Convex ℝ X)
    (ϕ : EuclideanSpace ℝ (Fin d) → ℝ) (hϕ : ConvexOn ℝ Set.univ ϕ)
    (a c : EuclideanSpace ℝ (Fin d)) (k : ℝ) (hk : 0 ≤ k)
    {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.PosSemidef) (x y : EuclideanSpace ℝ (Fin d))
    (hx : x ∈ X) (hy : y ∈ X)
    (hmin : ∀ z ∈ X, ⟪a, x⟫_ℝ + k * ϕ x + 1 / 2 * mInner M (x - c) (x - c)
      ≤ ⟪a, z⟫_ℝ + k * ϕ z + 1 / 2 * mInner M (z - c) (z - c)) :
    ⟪a, x⟫_ℝ + k * ϕ x + 1 / 2 * mInner M (x - c) (x - c) + 1 / 2 * mInner M (y - x) (y - x)
      ≤ ⟪a, y⟫_ℝ + k * ϕ y + 1 / 2 * mInner M (y - c) (y - c) := by
  set α := mInner M (y - x) (x - c) with hα
  set β := mInner M (y - x) (y - x) with hβ
  have hβ0 : 0 ≤ β := mInner_nonneg hM _
  set K := ⟪a, y - x⟫_ℝ + k * (ϕ y - ϕ x) + α with hK
  have key : ∀ s : ℝ, 0 < s → s ≤ 1 → 0 ≤ K + s * β / 2 := by
    intro s hs0 hs1
    have hz : x + s • (y - x) ∈ X := hXc.add_smul_sub_mem hx hy ⟨hs0.le, hs1⟩
    have hle := hmin _ hz
    have hϕs : ϕ (x + s • (y - x)) ≤ (1 - s) * ϕ x + s * ϕ y := by
      have h := hϕ.2 (Set.mem_univ x) (Set.mem_univ y) (by linarith : (0:ℝ) ≤ 1 - s)
        hs0.le (by ring)
      have e : (1 - s) • x + s • y = x + s • (y - x) := by
        rw [smul_sub, sub_smul, one_smul]; abel
      rw [e] at h
      simpa [smul_eq_mul] using h
    have e1 : x + s • (y - x) - c = (x - c) + s • (y - x) := by abel
    rw [e1, mInner_expand hM, inner_add_right, real_inner_smul_right] at hle
    have h3 : k * ϕ (x + s • (y - x)) ≤ k * ((1 - s) * ϕ x + s * ϕ y) :=
      mul_le_mul_of_nonneg_left hϕs hk
    have hinner : ⟪a, y - x⟫_ℝ = ⟪a, y⟫_ℝ - ⟪a, x⟫_ℝ := inner_sub_right _ _ _
    have h4 : 0 ≤ s * (K + s * β / 2) := by
      rw [hK]; nlinarith
    by_contra hneg
    push Not at hneg
    have : s * (K + s * β / 2) < 0 := mul_neg_of_pos_of_neg hs0 hneg
    linarith
  have hK0 : 0 ≤ K := by
    by_contra hneg
    push Not at hneg
    set s := min 1 (-K / (β + 1)) with hsdef
    have hc1 : 0 < β + 1 := by linarith
    have hs0 : 0 < s := lt_min one_pos (div_pos (by linarith) hc1)
    have hs1 : s ≤ 1 := min_le_left _ _
    have hs2 : s ≤ -K / (β + 1) := min_le_right _ _
    have h5 := key s hs0 hs1
    have h6 : s * (β + 1) ≤ -K := (le_div_iff₀ hc1).mp hs2
    nlinarith
  have e2 : y - c = (x - c) + (1 : ℝ) • (y - x) := by rw [one_smul]; abel
  rw [e2, mInner_expand hM]
  have hinner : ⟪a, y - x⟫_ℝ = ⟪a, y⟫_ℝ - ⟪a, x⟫_ℝ := inner_sub_right _ _ _
  nlinarith

/-! ## Regret shift -/

lemma sum_shift (F : ℕ → ℝ) (T : ℕ) :
    ∑ t ∈ Finset.Icc 1 T, F t + F (T + 1) = F 1 + ∑ t ∈ Finset.Icc 1 T, F (t + 1) := by
  induction T with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega)]
    linarith

lemma regret_shift (f : ℕ → EuclideanSpace ℝ (Fin d) → ℝ) (ϕ : EuclideanSpace ℝ (Fin d) → ℝ)
    (x : ℕ → EuclideanSpace ℝ (Fin d)) (xstar : EuclideanSpace ℝ (Fin d)) (T : ℕ)
    (hϕx : ϕ (x 1) ≤ ϕ (x (T + 1))) :
    AdaGrad.Diag.regret f ϕ x xstar T
      ≤ ∑ t ∈ Finset.Icc 1 T, (f t (x t) - f t xstar + ϕ (x (t + 1)) - ϕ xstar) := by
  have h := sum_shift (fun t => ϕ (x t)) T
  unfold AdaGrad.Diag.regret
  have e1 : ∑ t ∈ Finset.Icc 1 T, (f t (x t) + ϕ (x t) - f t xstar - ϕ xstar)
      = ∑ t ∈ Finset.Icc 1 T, (f t (x t) - f t xstar - ϕ xstar)
        + ∑ t ∈ Finset.Icc 1 T, ϕ (x t) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun t _ => by ring
  have e2 : ∑ t ∈ Finset.Icc 1 T, (f t (x t) - f t xstar + ϕ (x (t + 1)) - ϕ xstar)
      = ∑ t ∈ Finset.Icc 1 T, (f t (x t) - f t xstar - ϕ xstar)
        + ∑ t ∈ Finset.Icc 1 T, ϕ (x (t + 1)) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun t _ => by ring
  rw [e1, e2]
  linarith

end AdaGrad.Full.T7Aux

namespace AdaGrad.Full.T7Aux

open AdaGrad.Full Matrix

lemma part1 {d : ℕ} (η δ : ℝ) (hη : 0 < η) (hδ : 0 ≤ δ)
    (X : Set (EuclideanSpace ℝ (Fin d))) (hXc : Convex ℝ X)
    (h0X : (0 : EuclideanSpace ℝ (Fin d)) ∈ X)
    (f : ℕ → EuclideanSpace ℝ (Fin d) → ℝ)
    (ϕ : EuclideanSpace ℝ (Fin d) → ℝ) (hϕ : ConvexOn ℝ Set.univ ϕ)
    (hϕ0 : ∀ y ∈ X, ϕ 0 ≤ ϕ y) (T : ℕ) (hT : 1 ≤ T)
    (x g : ℕ → EuclideanSpace ℝ (Fin d)) (hrun : IsPrimalDualRun η δ X ϕ f x g T)
    (hg : ∀ t ∈ Finset.Icc 1 T, ‖g t‖ ≤ δ) (xstar : EuclideanSpace ℝ (Fin d))
    (hstar : xstar ∈ X) :
    AdaGrad.Diag.regret f ϕ x xstar T ≤ δ / η * ‖xstar‖ ^ 2
      + 1 / η * ‖xstar‖ ^ 2 * (S g T).trace + η * (S g T).trace := by
  obtain ⟨hx1, hpd⟩ := hrun
  set Φ : ℕ → EuclideanSpace ℝ (Fin d) → ℝ := fun n y =>
    ⟪η • ∑ τ ∈ Finset.Icc 1 n, g τ, y⟫_ℝ + ((n : ℝ) * η) * ϕ y
      + 1 / 2 * mInner (H δ g n) (y - 0) (y - 0) with hΦ
  have hmem : ∀ n ≤ T, x (n + 1) ∈ X := by
    intro n hn
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simpa [hx1] using h0X
    · exact (hpd n (Finset.mem_Icc.mpr ⟨h, hn⟩)).2.1
  have e0 : ∀ y, Φ 0 y = 1 / 2 * mInner (H δ g 0) y y := by
    intro y; simp [hΦ]
  have hmin : ∀ n ≤ T, ∀ z ∈ X, Φ n (x (n + 1)) ≤ Φ n z := by
    intro n hn z hz
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h
      rw [e0, e0, hx1]
      have := mInner_nonneg (H_psd hδ g 0) z
      have h00 : mInner (H δ g 0) 0 0 = 0 := by simp [mInner]
      rw [h00]; linarith
    · have hm := (hpd n (Finset.mem_Icc.mpr ⟨h, hn⟩)).2.2
      have hle := (isMinOn_iff.mp hm) z hz
      have hn0 : (0 : ℝ) < n := by exact_mod_cast h
      have e : ∀ y, Φ n y = (n : ℝ) * (η * ⟪(1 / (n : ℝ)) • ∑ τ ∈ Finset.Icc 1 n, g τ, y⟫_ℝ
          + η * ϕ y + (1 / (n : ℝ)) * psi (H δ g n) y) := by
        intro y
        simp only [hΦ, psi, sub_zero, real_inner_smul_left]
        field_simp
      rw [e, e]
      exact mul_le_mul_of_nonneg_left hle hn0.le
  have hsucc : ∀ n y, Φ (n + 1) y = Φ n y + η * ⟪g (n + 1), y⟫_ℝ + η * ϕ y
      + 1 / 2 * mInner (S g (n + 1) - S g n) y y := by
    intro n y
    simp only [hΦ, sub_zero]
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1), smul_add, inner_add_left,
      real_inner_smul_left, real_inner_smul_left, mInner_H, mInner_H, mInner_sub_mat]
    push_cast
    ring
  have claim : ∀ n ≤ T, ∑ t ∈ Finset.Icc 1 n,
      (η * ⟪g t, x t - xstar⟫_ℝ + η * ϕ (x (t + 1)) - η * ϕ xstar)
      + Φ n xstar - 1 / 2 * mInner (H δ g n) xstar xstar
      ≤ Φ n (x (n + 1)) + η ^ 2 * (S g n).trace := by
    intro n
    induction n with
    | zero =>
      intro _
      rw [e0, e0, hx1, S_zero]
      have h00 : mInner (H δ g 0) 0 0 = 0 := by simp [mInner]
      simp [h00]
    | succ n ih =>
      intro hn
      have ih' := ih (by omega)
      have hst := strong_min hXc ϕ hϕ (η • ∑ τ ∈ Finset.Icc 1 n, g τ) 0 ((n : ℝ) * η)
        (by positivity) (H_psd hδ g n) (x (n + 1)) (x (n + 1 + 1)) (hmem n (by omega))
        (hmem (n + 1) hn) (fun z hz => hmin n (by omega) z hz)
      have hcore := core_euc g n η (x (n + 1) - x (n + 1 + 1))
      have hgn : ‖g (n + 1)‖ ≤ δ := hg (n + 1) (Finset.mem_Icc.mpr ⟨by omega, hn⟩)
      have hHS := mInner_nonneg (S_le_H hδ g n hgn) (x (n + 1 + 1) - x (n + 1))
      rw [mInner_sub_mat] at hHS
      have hneg : x (n + 1) - x (n + 1 + 1) = -(x (n + 1 + 1) - x (n + 1)) := by abel
      rw [hneg, mInner_neg, inner_neg_right] at hcore
      have hD0 := mInner_nonneg (D_psd g n) (x (n + 1 + 1))
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1), hsucc, hsucc]
      have hHs : mInner (H δ g (n + 1)) xstar xstar
          = mInner (H δ g n) xstar xstar + mInner (S g (n + 1) - S g n) xstar xstar := by
        rw [mInner_H, mInner_H, mInner_sub_mat]; ring
      rw [hHs]
      have hi1 : ⟪g (n + 1), x (n + 1) - xstar⟫_ℝ
          = ⟪g (n + 1), x (n + 1)⟫_ℝ - ⟪g (n + 1), xstar⟫_ℝ := inner_sub_right _ _ _
      have hi2 : ⟪g (n + 1), x (n + 1 + 1) - x (n + 1)⟫_ℝ
          = ⟪g (n + 1), x (n + 1 + 1)⟫_ℝ - ⟪g (n + 1), x (n + 1)⟫_ℝ := inner_sub_right _ _ _
      simp only [sub_zero] at hst
      simp only [hΦ, sub_zero] at ih' ⊢
      nlinarith
  have hfin := claim T le_rfl
  have hT' := hmin T le_rfl xstar hstar
  -- regret
  have hshift := regret_shift f ϕ x xstar T (by rw [hx1]; exact hϕ0 _ (hmem T le_rfl))
  have hsum : η * ∑ t ∈ Finset.Icc 1 T, (f t (x t) - f t xstar + ϕ (x (t + 1)) - ϕ xstar)
      ≤ ∑ t ∈ Finset.Icc 1 T,
        (η * ⟪g t, x t - xstar⟫_ℝ + η * ϕ (x (t + 1)) - η * ϕ xstar) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun t ht => ?_
    have hs := (hpd t ht).1 xstar
    have hi : ⟪g t, xstar - x t⟫_ℝ = -⟪g t, x t - xstar⟫_ℝ := by
      rw [← inner_neg_right, neg_sub]
    rw [hi] at hs
    nlinarith
  have hHT := mInner_H δ g T xstar
  have htr := mInner_le_trace (S_psd g T) xstar
  have htr0 : 0 ≤ (S g T).trace := (S_psd g T).trace_nonneg
  have hx2 : 0 ≤ ‖xstar‖ ^ 2 := by positivity
  have hmain : η * AdaGrad.Diag.regret f ϕ x xstar T
      ≤ δ * ‖xstar‖ ^ 2 + ‖xstar‖ ^ 2 * (S g T).trace + η ^ 2 * (S g T).trace := by
    have := mul_le_mul_of_nonneg_left hshift hη.le
    nlinarith
  have eR : δ / η * ‖xstar‖ ^ 2 + 1 / η * ‖xstar‖ ^ 2 * (S g T).trace + η * (S g T).trace
      = (δ * ‖xstar‖ ^ 2 + ‖xstar‖ ^ 2 * (S g T).trace + η ^ 2 * (S g T).trace) / η := by
    field_simp
  rw [eR, le_div_iff₀ hη]
  linarith

lemma part2 {d : ℕ} (η δ : ℝ) (hη : 0 < η) (hδ : 0 ≤ δ)
    (X : Set (EuclideanSpace ℝ (Fin d))) (hXc : Convex ℝ X)
    (_h0X : (0 : EuclideanSpace ℝ (Fin d)) ∈ X)
    (f : ℕ → EuclideanSpace ℝ (Fin d) → ℝ)
    (ϕ : EuclideanSpace ℝ (Fin d) → ℝ) (hϕ : ConvexOn ℝ Set.univ ϕ)
    (hϕ0 : ∀ y ∈ X, ϕ 0 ≤ ϕ y) (T : ℕ) (hT : 1 ≤ T)
    (x g : ℕ → EuclideanSpace ℝ (Fin d)) (hrun : IsMirrorDescentRun η δ X ϕ f x g T)
    (xstar : EuclideanSpace ℝ (Fin d)) (hstar : xstar ∈ X) :
    AdaGrad.Diag.regret f ϕ x xstar T ≤ δ / η * ‖xstar‖ ^ 2
      + 1 / (2 * η) * (Finset.Icc 1 T).sup' (Finset.nonempty_Icc.mpr hT)
          (fun t => ‖xstar - x t‖ ^ 2) * (S g T).trace
      + η * (S g T).trace := by
  obtain ⟨hx1, hmd⟩ := hrun
  set Mx := (Finset.Icc 1 T).sup' (Finset.nonempty_Icc.mpr hT) (fun t => ‖xstar - x t‖ ^ 2)
    with hMx
  have claim : ∀ n ≤ T,
      η * ∑ t ∈ Finset.Icc 1 n, (f t (x t) - f t xstar + ϕ (x (t + 1)) - ϕ xstar)
      + 1 / 2 * mInner (H δ g n) (xstar - x (n + 1)) (xstar - x (n + 1))
      ≤ 1 / 2 * (δ * ‖xstar‖ ^ 2) + (Mx / 2 + η ^ 2) * (S g n).trace := by
    intro n
    induction n with
    | zero =>
      intro _
      rw [hx1, sub_zero, mInner_H, S_zero, mInner_zero_mat]
      simp
    | succ n ih =>
      intro hn
      have ih' := ih (by omega)
      have ht : n + 1 ∈ Finset.Icc 1 T := Finset.mem_Icc.mpr ⟨by omega, hn⟩
      obtain ⟨hsub, hmem, hm⟩ := hmd (n + 1) ht
      have hmin' : ∀ z ∈ X, ⟪η • g (n + 1), x (n + 1 + 1)⟫_ℝ + η * ϕ (x (n + 1 + 1))
          + 1 / 2 * mInner (H δ g (n + 1)) (x (n + 1 + 1) - x (n + 1))
              (x (n + 1 + 1) - x (n + 1))
          ≤ ⟪η • g (n + 1), z⟫_ℝ + η * ϕ z
            + 1 / 2 * mInner (H δ g (n + 1)) (z - x (n + 1)) (z - x (n + 1)) := by
        intro z hz
        have := (isMinOn_iff.mp hm) z hz
        simp only [bregman, real_inner_smul_left] at this ⊢
        linarith
      have hst := strong_min hXc ϕ hϕ (η • g (n + 1)) (x (n + 1)) η hη.le
        (H_psd hδ g (n + 1)) (x (n + 1 + 1)) xstar hmem hstar hmin'
      simp only [real_inner_smul_left] at hst
      have hs := hsub xstar
      have hcore := core_euc g n η (x (n + 1) - x (n + 1 + 1))
      have hneg : x (n + 1) - x (n + 1 + 1) = -(x (n + 1 + 1) - x (n + 1)) := by abel
      rw [hneg, mInner_neg, inner_neg_right] at hcore
      have hHS := mInner_H δ g (n + 1) (x (n + 1 + 1) - x (n + 1))
      have hu0 : 0 ≤ ‖x (n + 1 + 1) - x (n + 1)‖ ^ 2 := by positivity
      have hHs : mInner (H δ g (n + 1)) (xstar - x (n + 1)) (xstar - x (n + 1))
          = mInner (H δ g n) (xstar - x (n + 1)) (xstar - x (n + 1))
            + mInner (S g (n + 1) - S g n) (xstar - x (n + 1)) (xstar - x (n + 1)) := by
        rw [mInner_H, mInner_H, mInner_sub_mat]; ring
      have hDtr := mInner_le_trace (D_psd g n) (xstar - x (n + 1))
      rw [Matrix.trace_sub] at hDtr
      have hD0 : 0 ≤ (S g (n + 1)).trace - (S g n).trace := by
        rw [← Matrix.trace_sub]; exact (D_psd g n).trace_nonneg
      have hMle : ‖xstar - x (n + 1)‖ ^ 2 ≤ Mx :=
        Finset.le_sup' (fun t => ‖xstar - x t‖ ^ 2) ht
      have hDM : ‖xstar - x (n + 1)‖ ^ 2 * ((S g (n + 1)).trace - (S g n).trace)
          ≤ Mx * ((S g (n + 1)).trace - (S g n).trace) :=
        mul_le_mul_of_nonneg_right hMle hD0
      have hi1 : ⟪g (n + 1), xstar - x (n + 1)⟫_ℝ
          = ⟪g (n + 1), xstar⟫_ℝ - ⟪g (n + 1), x (n + 1)⟫_ℝ := inner_sub_right _ _ _
      have hi2 : ⟪g (n + 1), x (n + 1 + 1) - x (n + 1)⟫_ℝ
          = ⟪g (n + 1), x (n + 1 + 1)⟫_ℝ - ⟪g (n + 1), x (n + 1)⟫_ℝ := inner_sub_right _ _ _
      have hf : η * (f (n + 1) (x (n + 1)) - f (n + 1) xstar)
          ≤ η * (⟪g (n + 1), x (n + 1)⟫_ℝ - ⟪g (n + 1), xstar⟫_ℝ) := by
        apply mul_le_mul_of_nonneg_left _ hη.le
        linarith
      have hB0 := mInner_nonneg (H_psd hδ g (n + 1)) (xstar - x (n + 1 + 1))
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1), mul_add]
      nlinarith
  have hfin := claim T le_rfl
  have hB0 := mInner_nonneg (H_psd hδ g T) (xstar - x (T + 1))
  have hmemT : x (T + 1) ∈ X := (hmd T (Finset.mem_Icc.mpr ⟨hT, le_rfl⟩)).2.1
  have hshift := regret_shift f ϕ x xstar T (by rw [hx1]; exact hϕ0 _ hmemT)
  have htr0 : 0 ≤ (S g T).trace := (S_psd g T).trace_nonneg
  have hx2 : 0 ≤ ‖xstar‖ ^ 2 := by positivity
  have hmain : η * AdaGrad.Diag.regret f ϕ x xstar T
      ≤ δ * ‖xstar‖ ^ 2 + Mx / 2 * (S g T).trace + η ^ 2 * (S g T).trace := by
    have := mul_le_mul_of_nonneg_left hshift hη.le
    nlinarith
  have eR : δ / η * ‖xstar‖ ^ 2 + 1 / (2 * η) * Mx * (S g T).trace + η * (S g T).trace
      = (δ * ‖xstar‖ ^ 2 + Mx / 2 * (S g T).trace + η ^ 2 * (S g T).trace) / η := by
    field_simp
  rw [eR, le_div_iff₀ hη]
  linarith

end AdaGrad.Full.T7Aux

open AdaGrad.Full in
theorem solution {d : ℕ} (η δ : ℝ) (hη : 0 < η) (hδ : 0 ≤ δ)
    (X : Set (EuclideanSpace ℝ (Fin d))) (hXc : Convex ℝ X) (hXcl : IsClosed X)
    (h0X : (0 : EuclideanSpace ℝ (Fin d)) ∈ X)
    (f : ℕ → EuclideanSpace ℝ (Fin d) → ℝ) (hf : ∀ t, ConvexOn ℝ Set.univ (f t))
    (ϕ : EuclideanSpace ℝ (Fin d) → ℝ) (hϕ : ConvexOn ℝ Set.univ ϕ)
    (hϕ0 : ∀ y ∈ X, ϕ 0 ≤ ϕ y) (T : ℕ) (hT : 1 ≤ T) :
    (∀ x g : ℕ → EuclideanSpace ℝ (Fin d), IsPrimalDualRun η δ X ϕ f x g T →
      (∀ t ∈ Finset.Icc 1 T, ‖g t‖ ≤ δ) → ∀ xstar ∈ X,
        AdaGrad.Diag.regret f ϕ x xstar T ≤ δ / η * ‖xstar‖ ^ 2 + 1 / η * ‖xstar‖ ^ 2 * (S g T).trace
          + η * (S g T).trace) ∧
    (∀ x g : ℕ → EuclideanSpace ℝ (Fin d), IsMirrorDescentRun η δ X ϕ f x g T →
      ∀ xstar ∈ X,
        AdaGrad.Diag.regret f ϕ x xstar T ≤ δ / η * ‖xstar‖ ^ 2
          + 1 / (2 * η) * (Finset.Icc 1 T).sup' (Finset.nonempty_Icc.mpr hT)
              (fun t => ‖xstar - x t‖ ^ 2) * (S g T).trace
          + η * (S g T).trace) := by
  refine ⟨fun x g hrun hg xstar hstar => ?_, fun x g hrun xstar hstar => ?_⟩
  · exact AdaGrad.Full.T7Aux.part1 η δ hη hδ X hXc h0X f ϕ hϕ hϕ0 T hT x g hrun hg xstar hstar
  · exact AdaGrad.Full.T7Aux.part2 η δ hη hδ X hXc h0X f ϕ hϕ hϕ0 T hT x g hrun xstar hstar
