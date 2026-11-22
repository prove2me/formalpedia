-- Prove2me | Definitions.Def_GirvingAKS_Graph_Regular
-- name    : GirvingAKS_Graph_Regular
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-22T18:30:09.812944+00:00
-- url     : https://prove2.me/theorems/3e0ab2a0-3027-440d-abba-322c84dcf2bb
-- title:
--   AKS sorting networks (Seiferas port) — Regular Graphs and Spectral Theory
-- statement:
--   Part of a port of the Lean development https://github.com/girving/aks (commit `c7fb62e`), which proves the Ajtai–Komlós–Szemerédi theorem: there are sorting networks of depth $O(\log n)$ and size $O(n\log n)$, following Seiferas's simplified separator-based construction (J. Seiferas, *Sorting networks of logarithmic depth, further simplified*, Algorithmica 53 (2009)). This definition bundle is the module `AKS/Graph/Regular.lean`; it contains the definitions of that module together with their supporting lemmas, so that later bundles can import them.
--
--   **Contents.** Lean formalization of `d`-regular graphs via rotation maps, their normalized adjacency matrices, and spectral gap (operator norm).
--
--   HalfEdgeGraph squaring is in `Square.lean`; the complete graph is in `Complete.lean`.
--
--   **Formalization Note** The file was ported from Lean v4.29.0-rc4 to Lean v4.33.1 / Mathlib `0df444a`. The ported text agrees with the upstream file except for small proof repairs needed by the newer toolchain, the removal of the Lean module-system keywords, and the renaming of the upstream structure `Graph` to `HalfEdgeGraph`, which avoids a clash with Mathlib's `Graph`.
-- source:
--   https://github.com/girving/aks/blob/c7fb62ed80a4a610f87f34db0082cadbd7c00c9f/AKS/Graph/Regular.lean (ported); Seiferas, Sorting networks of logarithmic depth, further simplified, Algorithmica 53 (2009) 374–384; Ajtai, Komlós, Szemerédi, Sorting in c log n parallel steps, Combinatorica 3 (1983) 1–19

import Definitions.Def_GirvingAKS_Misc_Fin
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Algebra.Order.Chebyshev

/-! Ported to Lean v4.33.1 / Mathlib 0df444a from `AKS/Graph/Regular.lean` of
https://github.com/girving/aks (commit c7fb62ed80a4a610f87f34db0082cadbd7c00c9f, Apache-2.0). -/

/-
  # Regular Graphs and Spectral Theory

  Lean formalization of `d`-regular graphs via rotation maps,
  their normalized adjacency matrices, and spectral gap (operator norm).

  HalfEdgeGraph squaring is in `Square.lean`; the complete graph is in
  `Complete.lean`.
-/


section


open Matrix BigOperators Finset


/-! **Regular Graphs and Adjacency Matrices** -/

/-- A d-regular graph on n vertices, represented by a rotation map.

    The rotation map Rot(v, i) = (u, j) means: the i-th edge out of
    vertex v leads to vertex u, and this edge is the j-th edge out of u.

    This representation is essential for defining the zig-zag product
    cleanly, because it tracks the "port" structure at each vertex. -/
structure RegularGraph (n d : ℕ) where
  /-- Rot : V × [d] → V × [d], the rotation map. -/
  rot : Fin n × Fin d → Fin n × Fin d
  /-- Rotation is an involution: following an edge back returns you. -/
  rot_involution : ∀ x, rot (rot x) = x

/-- The vertex reached from v along port i. -/
def RegularGraph.neighbor {n d : ℕ} (G : RegularGraph n d)
    (v : Fin n) (i : Fin d) : Fin n :=
  (G.rot (v, i)).1

/-- The port at the far end of edge (v, i). -/
def RegularGraph.reversePort {n d : ℕ} (G : RegularGraph n d)
    (v : Fin n) (i : Fin d) : Fin d :=
  (G.rot (v, i)).2

theorem RegularGraph.neighbor_reversePort {n d : ℕ} (G : RegularGraph n d)
    (v : Fin n) (i : Fin d) :
    G.neighbor (G.neighbor v i) (G.reversePort v i) = v := by
  unfold RegularGraph.neighbor RegularGraph.reversePort
  rw [Prod.mk.eta]
  exact congr_arg Prod.fst (G.rot_involution (v, i))

theorem RegularGraph.reversePort_reversePort {n d : ℕ} (G : RegularGraph n d)
    (v : Fin n) (i : Fin d) :
    G.reversePort (G.neighbor v i) (G.reversePort v i) = i := by
  unfold RegularGraph.neighbor RegularGraph.reversePort
  rw [Prod.mk.eta]
  exact congr_arg Prod.snd (G.rot_involution (v, i))

/-- The normalized adjacency matrix of a d-regular graph.
    M[u, v] = (number of edges from u to v) / d.

    For a d-regular graph, the top eigenvalue is always 1
    (with eigenvector the all-ones vector), and the spectral gap
    is determined by the second-largest eigenvalue. -/
noncomputable def adjMatrix {n d : ℕ} (G : RegularGraph n d) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun u v ↦
    ((Finset.univ.filter (fun i : Fin d ↦ G.neighbor u i = v)).card : ℝ) / d

@[simp]
theorem adjMatrix_apply {n d : ℕ} (G : RegularGraph n d) (u v : Fin n) :
    adjMatrix G u v =
      ((Finset.univ.filter (fun i : Fin d ↦ G.neighbor u i = v)).card : ℝ) / d :=
  rfl

theorem adjMatrix_isSymm {n d : ℕ} (G : RegularGraph n d) : (adjMatrix G).IsSymm := by
  ext u v
  simp only [Matrix.transpose_apply, adjMatrix_apply]
  congr 1
  exact_mod_cast Finset.card_nbij' (G.reversePort v ·) (G.reversePort u ·)
    (fun i hi ↦ by
      simp only [SetLike.mem_coe, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      rw [← hi]; apply G.neighbor_reversePort)
    (fun j hj ↦ by
      simp only [SetLike.mem_coe, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
      rw [← hj]; apply G.neighbor_reversePort)
    (fun i hi ↦ by
      simp only [SetLike.mem_coe, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      rw [← hi]; apply G.reversePort_reversePort)
    (fun j hj ↦ by
      simp only [SetLike.mem_coe, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hj
      rw [← hj]; apply G.reversePort_reversePort)

theorem adjMatrix_isHermitian {n d : ℕ} (G : RegularGraph n d) :
    (adjMatrix G).IsHermitian := by
  show (adjMatrix G)ᴴ = adjMatrix G
  rw [conjTranspose_eq_transpose_of_trivial]
  exact adjMatrix_isSymm G


/-! **Walk Operator (CLM-first)** -/

/-- The walk function on plain vectors: averages f over the d neighbors of
    each vertex.  `(walkFun G f)(v) = (1/d) ∑ᵢ f(G.neighbor v i)`. -/
noncomputable def RegularGraph.walkFun {n d : ℕ} (G : RegularGraph n d)
    (f : Fin n → ℝ) : Fin n → ℝ :=
  fun v ↦ (∑ i : Fin d, f (G.neighbor v i)) / d

/-- The walk operator as a linear map on `EuclideanSpace`. -/
noncomputable def RegularGraph.walkLM {n d : ℕ} (G : RegularGraph n d) :
    EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) where
  toFun f := WithLp.toLp 2 (G.walkFun (WithLp.ofLp f))
  map_add' f g := by
    apply PiLp.ext; intro v
    simp [RegularGraph.walkFun, Finset.sum_add_distrib, add_div]
  map_smul' r f := by
    apply PiLp.ext; intro v
    simp only [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul,
      RingHom.id_apply, RegularGraph.walkFun, ← Finset.mul_sum, mul_div_assoc]

/-- The random walk operator of a d-regular graph, as a continuous linear map
    on `EuclideanSpace`. Maps f to the function averaging f over neighbors:
    `(Wf)(v) = (1/d) ∑ᵢ f(G.neighbor v i)`. -/
noncomputable def RegularGraph.walkCLM {n d : ℕ} (G : RegularGraph n d) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  G.walkLM.toContinuousLinearMap

@[simp]
theorem RegularGraph.walkCLM_apply {n d : ℕ} (G : RegularGraph n d)
    (f : EuclideanSpace ℝ (Fin n)) (v : Fin n) :
    G.walkCLM f v = (∑ i : Fin d, f (G.neighbor v i)) / d :=
  rfl


/-! **Mean Projection (CLM-first)** -/

/-- The mean function on plain vectors: maps f to the constant function
    with value `(1/n) ∑ᵢ f(i)`. -/
noncomputable def meanFun (n : ℕ)
    (f : Fin n → ℝ) : Fin n → ℝ :=
  fun _ ↦ (∑ i, f i) / n

/-- The mean projection as a linear map on `EuclideanSpace`. -/
noncomputable def meanLM (n : ℕ) :
    EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) where
  toFun f := WithLp.toLp 2 (meanFun n (WithLp.ofLp f))
  map_add' f g := by
    apply PiLp.ext; intro v
    simp [meanFun, Finset.sum_add_distrib, add_div]
  map_smul' r f := by
    apply PiLp.ext; intro v
    simp only [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul,
      RingHom.id_apply, meanFun, ← Finset.mul_sum, mul_div_assoc]

/-- The mean projection: maps f to the constant function with value mean(f).
    `(Pf)(v) = (1/n) ∑ᵢ f(i)`. -/
noncomputable def meanCLM (n : ℕ) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  (meanLM n).toContinuousLinearMap

@[simp]
theorem meanCLM_apply (n : ℕ) (f : EuclideanSpace ℝ (Fin n)) (v : Fin n) :
    meanCLM n f v = (∑ i, f i) / n :=
  rfl


theorem meanCLM_idempotent (n : ℕ) :
    meanCLM n * meanCLM n = meanCLM n := by
  ext f : 1; apply PiLp.ext; intro v
  show meanCLM n (meanCLM n f) v = meanCLM n f v
  simp only [meanCLM_apply]
  rw [Finset.sum_div, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    rw [mul_div_cancel₀ _ hne]

theorem meanCLM_isSelfAdjoint (n : ℕ) :
    IsSelfAdjoint (meanCLM n : EuclideanSpace ℝ (Fin n) →L[ℝ] _) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro f g
  change @inner ℝ _ _ (meanCLM n f) g = @inner ℝ _ _ f (meanCLM n g)
  simp only [PiLp.inner_apply, meanCLM_apply]
  simp_rw [show ∀ (a b : ℝ), @inner ℝ ℝ _ a b = a * b from fun a b => by
    show RCLike.re (b * starRingEnd ℝ a) = a * b
    simp only [RCLike.conj_to_real, RCLike.re_to_real]; ring]
  rw [← Finset.mul_sum, ← Finset.sum_mul]
  ring


/-! **Operator Norm Helpers** -/

/-- The rotation map as an equivalence (since it's an involution). -/
def RegularGraph.rotEquiv {n d : ℕ} (G : RegularGraph n d) :
    Fin n × Fin d ≃ Fin n × Fin d where
  toFun := G.rot
  invFun := G.rot
  left_inv := G.rot_involution
  right_inv := G.rot_involution

/-- Double-counting via the rotation bijection: summing g(neighbor(v,i))
    over all vertex-port pairs equals summing g(v) over all pairs. -/
theorem RegularGraph.sum_neighbor_eq {n d : ℕ} (G : RegularGraph n d)
    (g : Fin n → ℝ) :
    ∑ v : Fin n, ∑ i : Fin d, g (G.neighbor v i) =
    ∑ v : Fin n, ∑ _i : Fin d, g v := by
  simp_rw [← Fintype.sum_prod_type']
  exact G.rotEquiv.sum_comp (fun p ↦ g p.1)


/-- The walk operator is a contraction: ‖W‖ ≤ 1. -/
theorem RegularGraph.walkCLM_norm_le_one {n d : ℕ} (G : RegularGraph n d) :
    ‖G.walkCLM‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f; rw [one_mul]
  -- Reduce to squared norms via sqrt
  rw [← Real.sqrt_sq (norm_nonneg (G.walkCLM f)), ← Real.sqrt_sq (norm_nonneg f)]
  apply Real.sqrt_le_sqrt
  simp_rw [EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs, walkCLM_apply]
  -- Goal: ∑ v, ((∑ i, f(nbr v i)) / d)² ≤ ∑ v, (f v)²
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp; exact Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)
  · have hd_pos : (0 : ℝ) < d := Nat.cast_pos.mpr hd
    have hd_ne : (d : ℝ) ≠ 0 := ne_of_gt hd_pos
    -- Jensen: ((∑ x_i) / d)² ≤ (∑ x_i²) / d
    have jensen : ∀ v : Fin n, ((∑ i : Fin d, f (G.neighbor v i)) / ↑d) ^ 2 ≤
        (∑ i : Fin d, f (G.neighbor v i) ^ 2) / ↑d := by
      intro v
      have cs := @sq_sum_le_card_mul_sum_sq (Fin d) ℝ _ _ _ _
        Finset.univ (fun i ↦ f (G.neighbor v i))
      simp only [Finset.card_univ, Fintype.card_fin] at cs
      rw [div_pow, sq (d : ℝ), ← div_div]
      apply div_le_div_of_nonneg_right _ hd_pos.le
      rw [div_le_iff₀ hd_pos, mul_comm]
      exact cs
    -- Sum Jensen, then double-count, then simplify
    calc ∑ v, ((∑ i : Fin d, f (G.neighbor v i)) / ↑d) ^ 2
        ≤ ∑ v, (∑ i : Fin d, f (G.neighbor v i) ^ 2) / ↑d :=
          Finset.sum_le_sum (fun v _ ↦ jensen v)
      _ = (∑ v, ∑ i, f (G.neighbor v i) ^ 2) / ↑d := by
          rw [Finset.sum_div]
      _ = (∑ v, ∑ _i : Fin d, f v ^ 2) / ↑d := by
          rw [G.sum_neighbor_eq (fun v ↦ f v ^ 2)]
      _ = (∑ v, ↑d * (f v ^ 2)) / ↑d := by
          congr 1; apply Finset.sum_congr rfl; intro v _
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ = ∑ v, f v ^ 2 := by
          rw [← Finset.mul_sum, mul_div_cancel_left₀ _ hd_ne]

/-! **Spectral Gap** -/

/-- The spectral gap λ(G): the operator norm of the walk operator
    restricted to the subspace orthogonal to the constant functions.

      λ(G) = ‖W - P‖

    where W is the random walk operator and P is the mean projection.
    We have 0 ≤ λ(G) ≤ 1, with λ(G) close to 0 meaning
    excellent expansion. -/
noncomputable def spectralGap {n d : ℕ} (G : RegularGraph n d) : ℝ :=
  ‖G.walkCLM - meanCLM n‖

/-- Casting the vertex count doesn't change the spectral gap. -/
theorem spectralGap_cast {n₁ n₂ d : ℕ} (h : n₁ = n₂)
    (G : RegularGraph n₁ d) : spectralGap (h ▸ G) = spectralGap G := by
  subst h; rfl

/-- The spectral gap is nonneg. -/
theorem spectralGap_nonneg {n d : ℕ} (G : RegularGraph n d) :
    0 ≤ spectralGap G :=
  norm_nonneg _

/-- The mean projection doesn't increase the norm: ‖Pf‖ ≤ ‖f‖. -/
private theorem meanCLM_apply_norm_le (n : ℕ) (f : EuclideanSpace ℝ (Fin n)) :
    ‖meanCLM n f‖ ≤ ‖f‖ := by
  rw [← Real.sqrt_sq (norm_nonneg _), ← Real.sqrt_sq (norm_nonneg f)]
  apply Real.sqrt_le_sqrt
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  simp_rw [Real.norm_eq_abs, sq_abs, meanCLM_apply]
  -- Goal: ∑ v, ((∑ i, f i) / n)² ≤ ∑ v, (f v)²
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  · have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    have cs := @sq_sum_le_card_mul_sum_sq (Fin n) ℝ _ _ _ _
      Finset.univ (fun i ↦ f i)
    simp only [Finset.card_univ, Fintype.card_fin] at cs
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, div_pow]
    -- Goal: n * (∑ f)² / n² ≤ ∑ f²
    have h_simp : ↑n * ((∑ i : Fin n, f i) ^ 2 / (↑n) ^ 2) =
        (∑ i : Fin n, f i) ^ 2 / ↑n := by
      field_simp
    rw [h_simp, div_le_iff₀ hn_pos]
    linarith [mul_comm (↑n : ℝ) (∑ x : Fin n, f x ^ 2)]

/-- Subtracting the mean doesn't increase the norm: ‖f - Pf‖ ≤ ‖f‖. -/
theorem norm_sub_meanCLM_le (n : ℕ) (f : EuclideanSpace ℝ (Fin n)) :
    ‖f - meanCLM n f‖ ≤ ‖f‖ := by
  rw [← Real.sqrt_sq (norm_nonneg _), ← Real.sqrt_sq (norm_nonneg f)]
  apply Real.sqrt_le_sqrt
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  simp_rw [Real.norm_eq_abs, sq_abs]
  have hfv : ∀ v : Fin n, (f - meanCLM n f) v = f v - (∑ i, f i) / ↑n := by
    intro v; simp [meanCLM_apply]
  simp_rw [hfv]
  -- Goal: ∑ v, (f v - (∑ i, f i) / n)² ≤ ∑ v, (f v)²
  -- ∑(f v - μ)² = ∑ f v² - (∑ f)²/n ≤ ∑ f v²  (by CS: (∑ f)²/n ≥ 0)
  set S := ∑ i : Fin n, f i
  have expand : ∀ v : Fin n, (f v - S / ↑n) ^ 2 =
      f v ^ 2 - 2 * (S / ↑n) * f v + (S / ↑n) ^ 2 := fun v ↦ by ring
  simp_rw [expand, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  -- Need: ∑ f v² - 2(S/n)·S + n·(S/n)² ≤ ∑ f v²
  -- i.e., n·(S/n)² ≤ 2(S/n)·S
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  · have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    have hn_ne := ne_of_gt hn_pos
    -- 2(S/n)·S - n·(S/n)² = S²/n ≥ 0
    have key : 2 * (S / ↑n) * S - ↑n * (S / ↑n) ^ 2 = S ^ 2 / ↑n := by
      field_simp; ring
    linarith [div_nonneg (sq_nonneg S) hn_pos.le]

/-- The walk operator preserves the mean projection: W(Pf) = Pf (when d > 0). -/
theorem walkCLM_comp_meanCLM {n d : ℕ} (G : RegularGraph n d) (hd : 0 < d) :
    ∀ f : EuclideanSpace ℝ (Fin n), G.walkCLM (meanCLM n f) = meanCLM n f := by
  intro f; ext v
  simp only [RegularGraph.walkCLM_apply, meanCLM_apply]
  -- Goal: (∑ i : Fin d, (∑ j, f j) / n) / d = (∑ j, f j) / n
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  exact mul_div_cancel_left₀ _ (by positivity)

theorem spectralGap_le_one {n d : ℕ} (G : RegularGraph n d) :
    spectralGap G ≤ 1 := by
  unfold spectralGap
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f; rw [one_mul]
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · -- d = 0: walkCLM sends everything to 0
    have hW : G.walkCLM f = 0 := by
      ext v; simp [RegularGraph.walkCLM_apply]
    simp only [ContinuousLinearMap.sub_apply, hW, zero_sub, norm_neg]
    exact meanCLM_apply_norm_le n f
  · -- d > 0: factor as W(f - Pf) using WP = P
    have hWP := walkCLM_comp_meanCLM G hd f
    calc ‖(G.walkCLM - meanCLM n) f‖
        = ‖G.walkCLM f - meanCLM n f‖ := by
          simp [ContinuousLinearMap.sub_apply]
      _ = ‖G.walkCLM f - G.walkCLM (meanCLM n f)‖ := by rw [hWP]
      _ = ‖G.walkCLM (f - meanCLM n f)‖ := by rw [map_sub]
      _ ≤ ‖G.walkCLM‖ * ‖f - meanCLM n f‖ := G.walkCLM.le_opNorm _
      _ ≤ 1 * ‖f - meanCLM n f‖ := by
          apply mul_le_mul_of_nonneg_right G.walkCLM_norm_le_one (norm_nonneg _)
      _ = ‖f - meanCLM n f‖ := one_mul _
      _ ≤ ‖f‖ := norm_sub_meanCLM_le n f

/-- For a 0-regular graph on n ≥ 1 vertices, spectralGap = 1.
    Walk is zero, so spectralGap = ‖P‖ = 1 (P maps all-ones to itself). -/
theorem spectralGap_zero_degree {n : ℕ} (G : RegularGraph n 0) (hn : 0 < n) :
    spectralGap G = 1 :=
  le_antisymm (spectralGap_le_one G) <| by
    have hW : G.walkCLM = 0 := by ext f v; simp [RegularGraph.walkCLM_apply]
    rw [show spectralGap G = ‖meanCLM n‖ from by
      unfold spectralGap; rw [hW, zero_sub, norm_neg]]
    set e : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun _ ↦ (1 : ℝ))
    have he_pos : 0 < ‖e‖ := by
      rw [norm_pos_iff]; intro h
      exact one_ne_zero (congr_fun (congrArg WithLp.ofLp h) ⟨0, hn⟩)
    have hPe : meanCLM n e = e := by
      apply PiLp.ext; intro v
      show (∑ _ : Fin n, (1 : ℝ)) / ↑n = 1
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one,
          div_self (Nat.cast_ne_zero.mpr (by omega))]
    have h := (meanCLM n).le_opNorm e; rw [hPe] at h
    exact le_of_mul_le_mul_right (by linarith) he_pos

end


