-- Prove2me | Definitions.Def_GirvingAKS_Halver_Tanner
-- name    : GirvingAKS_Halver_Tanner
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-22T18:32:12.232201+00:00
-- url     : https://prove2.me/theorems/2efead14-9cdf-4be6-b841-048adc11e4fb
-- title:
--   AKS sorting networks (Seiferas port) — Tanner's Vertex Expansion Bound
-- statement:
--   Part of a port of the Lean development https://github.com/girving/aks (commit `c7fb62e`), which proves the Ajtai–Komlós–Szemerédi theorem: there are sorting networks of depth $O(\log n)$ and size $O(n\log n)$, following Seiferas's simplified separator-based construction (J. Seiferas, *Sorting networks of logarithmic depth, further simplified*, Algorithmica 53 (2009)). This definition bundle is the module `AKS/Halver/Tanner.lean`; it contains the definitions of that module together with their supporting lemmas, so that later bundles can import them.
--
--   **Contents.** For a d-regular graph G with spectral gap ≤ β, Tanner's bound gives: |N(T)| ≥ |T|·n / (|T| + β²·(n - |T|))
--
--   This is strictly stronger than the expander mixing lemma for small sets and is the key ingredient for the expander → halver bridge.
--
--   The proof combines Cauchy-Schwarz on the codegree distribution with the spectral gap operator norm bound via orthogonal decomposition.
--
--   **Formalization Note** The file was ported from Lean v4.29.0-rc4 to Lean v4.33.1 / Mathlib `0df444a`. The ported text agrees with the upstream file except for small proof repairs needed by the newer toolchain, the removal of the Lean module-system keywords, and the renaming of the upstream structure `Graph` to `HalfEdgeGraph`, which avoids a clash with Mathlib's `Graph`.
-- source:
--   https://github.com/girving/aks/blob/c7fb62ed80a4a610f87f34db0082cadbd7c00c9f/AKS/Halver/Tanner.lean (ported); Seiferas, Sorting networks of logarithmic depth, further simplified, Algorithmica 53 (2009) 374–384; Ajtai, Komlós, Szemerédi, Sorting in c log n parallel steps, Combinatorica 3 (1983) 1–19

import Definitions.Def_GirvingAKS_Halver_Mixing
import Definitions.Def_GirvingAKS_Graph_Square
import Definitions.Def_GirvingAKS_Graph_Walk

/-! Ported to Lean v4.33.1 / Mathlib 0df444a from `AKS/Halver/Tanner.lean` of
https://github.com/girving/aks (commit c7fb62ed80a4a610f87f34db0082cadbd7c00c9f, Apache-2.0). -/

/-
  # Tanner's Vertex Expansion Bound

  For a d-regular graph G with spectral gap ≤ β, Tanner's bound gives:
  |N(T)| ≥ |T|·n / (|T| + β²·(n - |T|))

  This is strictly stronger than the expander mixing lemma for small sets
  and is the key ingredient for the expander → halver bridge.

  The proof combines Cauchy-Schwarz on the codegree distribution with
  the spectral gap operator norm bound via orthogonal decomposition.
-/


section


open Finset BigOperators


/-! **Neighborhood and Codegree** -/

/-- The neighborhood of a vertex set T: all vertices with at least one
    neighbor in T. -/
def RegularGraph.neighborSet {n d : ℕ} (G : RegularGraph n d)
    (T : Finset (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter (fun v => ∃ p : Fin d, G.neighbor v p ∈ T)

/-- The codegree of a vertex v with respect to T: the number of ports
    leading to T. -/
def RegularGraph.codeg {n d : ℕ} (G : RegularGraph n d)
    (T : Finset (Fin n)) (v : Fin n) : ℕ :=
  (Finset.univ.filter (fun p : Fin d => G.neighbor v p ∈ T)).card

/-- Codegree is zero outside the neighborhood. -/
theorem RegularGraph.codeg_eq_zero_of_not_mem {n d : ℕ} (G : RegularGraph n d)
    (T : Finset (Fin n)) (v : Fin n) (hv : v ∉ G.neighborSet T) :
    G.codeg T v = 0 := by
  simp only [neighborSet, Finset.mem_filter, Finset.mem_univ, true_and,
    not_exists] at hv
  simp only [codeg, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro p _; exact hv p


/-! **Codegree Sum** -/

/-- The sum of codegrees equals d·|T|. -/
theorem RegularGraph.codeg_sum {n d : ℕ} (G : RegularGraph n d)
    (T : Finset (Fin n)) :
    ∑ v, G.codeg T v = d * T.card := by
  -- Lift to ℝ where sum_neighbor_eq is available
  suffices h : (∑ v, (G.codeg T v : ℝ)) = (d : ℝ) * ↑T.card by exact_mod_cast h
  -- Express each codeg as a sum of indicators
  have hc : ∀ v : Fin n, (G.codeg T v : ℝ) =
      ∑ i : Fin d, if G.neighbor v i ∈ T then (1 : ℝ) else 0 := by
    intro v; simp only [codeg, Finset.sum_boole]
  simp_rw [hc]
  -- Apply rotation bijection: ∑ v ∑ i, f(nbr(v,i)) = ∑ v ∑ i, f(v)
  rw [G.sum_neighbor_eq (fun v ↦ if v ∈ T then (1 : ℝ) else 0)]
  -- Simplify: ∑ v, d * [v ∈ T] = d * |T|
  simp_rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← Finset.mul_sum, Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter]


/-! **Walk Operator and Codegree** -/

/-- The walk operator applied to an indicator vector gives codeg/d at each vertex. -/
theorem RegularGraph.walkCLM_indicatorVec {n d : ℕ} (G : RegularGraph n d)
    (T : Finset (Fin n)) (v : Fin n) :
    G.walkCLM (indicatorVec T) v = (G.codeg T v : ℝ) / d := by
  simp only [RegularGraph.walkCLM_apply, indicatorVec_apply, codeg]
  congr 1
  simp only [Finset.sum_boole]

/-- ‖W·1_T‖² = (∑ codeg(v)²) / d². -/
theorem RegularGraph.norm_sq_walkCLM_indicatorVec {n d : ℕ} (G : RegularGraph n d)
    (T : Finset (Fin n)) :
    ‖G.walkCLM (indicatorVec T)‖ ^ 2 =
    (∑ v, (G.codeg T v : ℝ) ^ 2) / (d : ℝ) ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp_rw [Real.norm_eq_abs, sq_abs, G.walkCLM_indicatorVec T]
  simp_rw [div_pow]
  rw [← Finset.sum_div]


/-! **Orthogonal Decomposition for ‖W·1_T‖²** -/

/-- The mean projection applied to an indicator gives constant |T|/n. -/
private theorem meanCLM_indicatorVec_eq {n : ℕ} (T : Finset (Fin n)) (v : Fin n) :
    meanCLM n (indicatorVec T) v = (↑T.card : ℝ) / ↑n := by
  simp only [meanCLM_apply]
  congr 1
  simp_rw [indicatorVec_apply]
  rw [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter]

/-- ‖P(1_T)‖² = |T|²/n. -/
private theorem norm_sq_meanCLM_indicatorVec {n : ℕ} (hn : 0 < n) (T : Finset (Fin n)) :
    ‖meanCLM n (indicatorVec T)‖ ^ 2 = (↑T.card) ^ 2 / ↑n := by
  rw [EuclideanSpace.norm_sq_eq]
  simp_rw [Real.norm_eq_abs, sq_abs, meanCLM_indicatorVec_eq T, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, div_pow]
  have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hn)
  field_simp

/-- The sum ∑ v, indicatorVec T v = ↑T.card (as ℝ). -/
private theorem sum_indicatorVec_eq {n : ℕ} (T : Finset (Fin n)) :
    ∑ v : Fin n, indicatorVec T v = (↑T.card : ℝ) := by
  simp_rw [indicatorVec_apply, Finset.sum_boole, Finset.filter_mem_eq_inter,
    Finset.univ_inter]

/-- Key bound: ‖W·1_T‖² ≤ |T|·(|T| + β²·(n - |T|)) / n.
    Uses orthogonal decomposition W(1_T) = P(1_T) + (W-P)(1_T),
    Pythagorean theorem (since P*(W-P) = 0), and operator norm bound. -/
theorem norm_sq_walk_indicatorVec_le {n d : ℕ} (G : RegularGraph n d)
    (hd : 0 < d) (hn : 0 < n)
    (T : Finset (Fin n)) (β : ℝ) (hβ : spectralGap G ≤ β) :
    ‖G.walkCLM (indicatorVec T)‖ ^ 2 ≤
    ↑T.card * (↑T.card + β ^ 2 * (↑n - ↑T.card)) / ↑n := by
  set f := indicatorVec T
  have hn_r : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_r
  have hd_ne : (d : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hd)
  -- Abbreviations for proved helper results
  have hPf_sq := norm_sq_meanCLM_indicatorVec hn T
  -- Sum of W(f) over all vertices = |T|
  have hsum_Wf : ∑ v, G.walkCLM f v = (↑T.card : ℝ) := by
    simp only [RegularGraph.walkCLM_apply]
    rw [← Finset.sum_div, G.sum_neighbor_eq (fun v ↦ f v)]
    simp_rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [← Finset.mul_sum, mul_div_cancel_left₀ _ hd_ne]
    exact sum_indicatorVec_eq T
  -- Sum of P(f) over all vertices = |T|
  have hsum_Pf : ∑ v, meanCLM n f v = (↑T.card : ℝ) := by
    simp only [meanCLM_apply]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
    exact sum_indicatorVec_eq T
  -- P(W-P) = 0 (from PW=P and P²=P)
  have hPA : meanCLM n * (G.walkCLM - meanCLM n) = (0 : _ →L[ℝ] _) := by
    rw [mul_sub, meanCLM_comp_walkCLM G hd, meanCLM_idempotent, sub_self]
  -- Orthogonality helper: P applied to (W-P)f is zero
  have hPA_f : meanCLM n ((G.walkCLM - meanCLM n) f) = 0 := by
    show (meanCLM n * (G.walkCLM - meanCLM n)) f = 0
    rw [hPA, ContinuousLinearMap.zero_apply]
  -- Orthogonality: ⟨Pf, (W-P)f⟩ = 0 (via P self-adjoint + P(W-P) = 0)
  have hortho : @inner ℝ _ _ (meanCLM n f) ((G.walkCLM - meanCLM n) f) = 0 := by
    have h1 := ContinuousLinearMap.adjoint_inner_left
      (meanCLM n : EuclideanSpace ℝ (Fin n) →L[ℝ] _) f ((G.walkCLM - meanCLM n) f)
    rw [(meanCLM_isSelfAdjoint n).adjoint_eq] at h1
    rw [real_inner_comm, ← h1, hPA_f, inner_zero_left]
  -- Decompose: Wf = Pf + (W-P)f
  have hdecomp : G.walkCLM f = meanCLM n f + (G.walkCLM - meanCLM n) f := by
    simp only [ContinuousLinearMap.sub_apply]; abel
  -- Pythagorean: ‖Wf‖² = ‖Pf‖² + ‖(W-P)f‖²
  have hpyth : ‖G.walkCLM f‖ ^ 2 =
      ‖meanCLM n f‖ ^ 2 + ‖(G.walkCLM - meanCLM n) f‖ ^ 2 := by
    rw [hdecomp, norm_add_sq_real, hortho, mul_zero, add_zero]
  -- (W-P)(Pf) = 0 (from WP=P and P²=P)
  have hAPf : (G.walkCLM - meanCLM n) (meanCLM n f) = 0 := by
    simp only [ContinuousLinearMap.sub_apply]
    rw [walkCLM_comp_meanCLM G hd f]
    have : meanCLM n (meanCLM n f) = meanCLM n f := by
      show (meanCLM n * meanCLM n) f = meanCLM n f; rw [meanCLM_idempotent]
    rw [this, sub_self]
  -- (W-P)(f) = (W-P)(f - Pf) since (W-P)(Pf) = 0
  have hAfact : (G.walkCLM - meanCLM n) f =
      (G.walkCLM - meanCLM n) (f - meanCLM n f) := by
    rw [map_sub, hAPf, sub_zero]
  -- ‖(W-P)f‖ ≤ β · ‖f - Pf‖ (operator norm bound)
  have hAnorm : ‖(G.walkCLM - meanCLM n) f‖ ≤ β * ‖f - meanCLM n f‖ := by
    calc ‖(G.walkCLM - meanCLM n) f‖
        = ‖(G.walkCLM - meanCLM n) (f - meanCLM n f)‖ := by rw [hAfact]
      _ ≤ ‖(G.walkCLM - meanCLM n : _ →L[ℝ] _)‖ * ‖f - meanCLM n f‖ :=
          (G.walkCLM - meanCLM n).le_opNorm (f - meanCLM n f)
      _ ≤ β * ‖f - meanCLM n f‖ := mul_le_mul_of_nonneg_right hβ (norm_nonneg _)
  -- ‖f - Pf‖² = |T| - |T|²/n (Pythagorean decomposition of f)
  have hfPf_sq : ‖f - meanCLM n f‖ ^ 2 = ↑T.card - (↑T.card) ^ 2 / ↑n := by
    -- ⟨Pf, f-Pf⟩ = 0 via P self-adjoint + P(f-Pf) = 0
    have hP_proj : meanCLM n (f - meanCLM n f) = 0 := by
      rw [map_sub]; show meanCLM n f - (meanCLM n * meanCLM n) f = 0
      rw [meanCLM_idempotent, sub_self]
    have hortho2 : @inner ℝ _ _ (meanCLM n f) (f - meanCLM n f) = 0 := by
      have h1 := ContinuousLinearMap.adjoint_inner_left
        (meanCLM n : EuclideanSpace ℝ (Fin n) →L[ℝ] _) f (f - meanCLM n f)
      rw [(meanCLM_isSelfAdjoint n).adjoint_eq] at h1
      rw [real_inner_comm, ← h1, hP_proj, inner_zero_left]
    have hf_decomp : f = meanCLM n f + (f - meanCLM n f) := by abel
    have : ‖f‖ ^ 2 = ‖meanCLM n f‖ ^ 2 + ‖f - meanCLM n f‖ ^ 2 := by
      conv_lhs => rw [hf_decomp]
      rw [norm_add_sq_real, hortho2, mul_zero, add_zero]
    rw [norm_sq_indicatorVec] at this; linarith
  -- ‖(W-P)f‖² ≤ β²·(|T| - |T|²/n)
  have hAf_sq : ‖(G.walkCLM - meanCLM n) f‖ ^ 2 ≤
      β ^ 2 * (↑T.card - (↑T.card) ^ 2 / ↑n) := by
    calc ‖(G.walkCLM - meanCLM n) f‖ ^ 2
        ≤ (β * ‖f - meanCLM n f‖) ^ 2 := by
          apply sq_le_sq'
          · linarith [norm_nonneg ((G.walkCLM - meanCLM n) f),
              mul_nonneg (le_trans (spectralGap_nonneg G) hβ) (norm_nonneg (f - meanCLM n f))]
          · exact hAnorm
      _ = β ^ 2 * ‖f - meanCLM n f‖ ^ 2 := by ring
      _ = β ^ 2 * (↑T.card - (↑T.card) ^ 2 / ↑n) := by rw [hfPf_sq]
  -- Final combination
  calc ‖G.walkCLM f‖ ^ 2
      = ‖meanCLM n f‖ ^ 2 + ‖(G.walkCLM - meanCLM n) f‖ ^ 2 := hpyth
    _ ≤ (↑T.card) ^ 2 / ↑n + β ^ 2 * (↑T.card - (↑T.card) ^ 2 / ↑n) := by
        linarith [hPf_sq, hAf_sq]
    _ = ↑T.card * (↑T.card + β ^ 2 * (↑n - ↑T.card)) / ↑n := by
        field_simp


/-! **Tanner's Bound** -/

/-- Tanner's vertex expansion bound: for any T ⊆ V in a d-regular graph
    with spectral gap ≤ β,
    |N(T)| · (|T| + β²·(n - |T|)) ≥ |T| · n. -/
theorem tanner_bound {n d : ℕ} (G : RegularGraph n d) (hd : 0 < d) (hn : 0 < n)
    (β : ℝ) (hβ : spectralGap G ≤ β) (_hβ_nn : 0 ≤ β)
    (T : Finset (Fin n)) (hT : 0 < T.card) :
    (T.card : ℝ) * ↑n ≤ ↑(G.neighborSet T).card * (↑T.card + β ^ 2 * (↑n - ↑T.card)) := by
  set N := G.neighborSet T
  have hd_r : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hn_r : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hT_r : (0 : ℝ) < ↑T.card := Nat.cast_pos.mpr hT
  -- Step 1: ∑_{v ∈ N(T)} codeg(v) = d * |T| (codeg=0 outside N(T))
  have hsum : ∑ v ∈ N, (G.codeg T v : ℝ) = (d : ℝ) * ↑T.card := by
    rw [Finset.sum_subset (Finset.subset_univ N) (fun v _ hv ↦ by
      simp only [Nat.cast_eq_zero]; exact G.codeg_eq_zero_of_not_mem T v hv)]
    exact_mod_cast G.codeg_sum T
  -- Step 2: Cauchy-Schwarz: (∑_{N} codeg)² ≤ |N| * ∑_{N} codeg²
  have cs := sq_sum_le_card_mul_sum_sq (s := N) (f := fun v ↦ (G.codeg T v : ℝ))
  rw [hsum] at cs
  -- Step 3: ∑_{N} codeg² ≤ ∑_V codeg²
  have hsumsq : ∑ v ∈ N, (G.codeg T v : ℝ) ^ 2 ≤
      ∑ v, (G.codeg T v : ℝ) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ N)
      (fun _ _ _ ↦ sq_nonneg _)
  -- Step 4: ∑_V codeg² = d² * ‖W·1_T‖²
  have hcodeg_sq : ∑ v, (G.codeg T v : ℝ) ^ 2 =
      (d : ℝ) ^ 2 * ‖G.walkCLM (indicatorVec T)‖ ^ 2 := by
    rw [G.norm_sq_walkCLM_indicatorVec T, mul_div_cancel₀]
    exact pow_ne_zero 2 (ne_of_gt hd_r)
  -- Step 5: n * ‖W·1_T‖² ≤ |T|·(|T| + β²(n-|T|)) (norm bound, multiplied by n)
  have hnorm_nd : ↑n * ‖G.walkCLM (indicatorVec T)‖ ^ 2 ≤
      ↑T.card * (↑T.card + β ^ 2 * (↑n - ↑T.card)) := by
    have h := norm_sq_walk_indicatorVec_le G hd hn T β hβ
    have h' := (le_div_iff₀ hn_r).mp h
    linarith
  -- Chain: d²·|T|² ≤ |N|·d²·‖W 1_T‖² (from CS + subset + codeg identity)
  have hchain : (d : ℝ) ^ 2 * (↑T.card) ^ 2 ≤
      ↑N.card * ((d : ℝ) ^ 2 * ‖G.walkCLM (indicatorVec T)‖ ^ 2) := by
    calc (d : ℝ) ^ 2 * (↑T.card) ^ 2
        = ((d : ℝ) * ↑T.card) ^ 2 := by ring
      _ ≤ ↑N.card * ∑ v ∈ N, (G.codeg T v : ℝ) ^ 2 := cs
      _ ≤ ↑N.card * ∑ v, (G.codeg T v : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_left hsumsq (Nat.cast_nonneg _)
      _ = ↑N.card * ((d : ℝ) ^ 2 * ‖G.walkCLM (indicatorVec T)‖ ^ 2) := by
          rw [hcodeg_sq]
  -- Combined bound: d²·|T|²·n ≤ |N|·d²·|T|·(|T| + β²(n-|T|))
  have h_combined : (d : ℝ) ^ 2 * (↑T.card) ^ 2 * ↑n ≤
      ↑N.card * (d : ℝ) ^ 2 * ↑T.card * (↑T.card + β ^ 2 * (↑n - ↑T.card)) := by
    nlinarith [mul_le_mul_of_nonneg_right hchain (le_of_lt hn_r),
      mul_le_mul_of_nonneg_left hnorm_nd
        (mul_nonneg (Nat.cast_nonneg N.card) (le_of_lt (sq_pos_of_pos hd_r))),
      sq_nonneg ‖G.walkCLM (indicatorVec T)‖]
  -- Cancel d²·|T| (both positive): |T|·n ≤ |N|·(...)
  by_contra h; push_neg at h
  linarith [mul_lt_mul_of_pos_left h (mul_pos (sq_pos_of_pos hd_r) hT_r)]


/-! **Volume Tanner Bound for General Graphs** -/

noncomputable section

/-- The neighborhood of a vertex set T in a general graph: vertices with
    at least one half-edge targeting T. -/
def HalfEdgeGraph.neighborSet {n : ℕ} (G : HalfEdgeGraph n) (T : Finset (Fin n)) : Finset (Fin n) :=
  univ.filter (fun v => ∃ e ∈ univ.filter (G.src · = v), G.target e ∈ T)

/-- The codegree of vertex `v` with respect to `T`: the number of half-edges
    from `v` to `T`. -/
def HalfEdgeGraph.codeg {n : ℕ} (G : HalfEdgeGraph n) (T : Finset (Fin n)) (v : Fin n) : ℕ :=
  (univ.filter (fun e => G.src e = v ∧ G.target e ∈ T)).card

/-- Codegree is zero outside the neighborhood. -/
theorem HalfEdgeGraph.codeg_eq_zero_of_not_mem {n : ℕ} (G : HalfEdgeGraph n)
    (T : Finset (Fin n)) (v : Fin n) (hv : v ∉ G.neighborSet T) :
    G.codeg T v = 0 := by
  rw [HalfEdgeGraph.codeg, card_eq_zero, filter_eq_empty_iff]
  intro e _ ⟨h_src, h_tgt⟩
  apply hv
  simp only [HalfEdgeGraph.neighborSet, mem_filter, mem_univ, true_and]
  exact ⟨e, h_src, h_tgt⟩

/-- Sum of codegrees equals the volume of T: `∑ codeg(T, v) = ∑_{w ∈ T} deg(w)`. -/
theorem HalfEdgeGraph.codeg_sum {n : ℕ} (G : HalfEdgeGraph n) (T : Finset (Fin n)) :
    ∑ v, G.codeg T v = ∑ w ∈ T, G.deg w := by
  -- Lift to ℝ where sum_target_eq_sum_src is available
  suffices h : (∑ v, (G.codeg T v : ℝ)) = ∑ w ∈ T, (G.deg w : ℝ) by exact_mod_cast h
  -- Express codeg as indicator sum over half-edges
  have hcv : ∀ v : Fin n, (G.codeg T v : ℝ) =
      ∑ e ∈ univ.filter (G.src · = v), if G.target e ∈ T then (1 : ℝ) else 0 := by
    intro v; simp only [HalfEdgeGraph.codeg, Finset.sum_boole, Nat.cast_inj]
    congr 1; ext e; simp only [mem_filter, mem_univ, true_and, and_comm]
  simp_rw [hcv]
  -- Collapse fiber: ∑_v ∑_{e:src=v} f(e) = ∑_e f(e)
  rw [Finset.sum_fiberwise_of_maps_to (g := G.src) (fun _ _ ↦ mem_univ _)]
  -- ∑_e [target e ∈ T] = ∑_e [src e ∈ T] via rotation bijection
  rw [G.sum_target_eq_sum_src (fun v ↦ if v ∈ T then (1 : ℝ) else 0)]
  -- ∑_e [src e ∈ T] = ∑_{v∈T} deg v
  -- Group by src: ∑_e f(src e) = ∑_v ∑_{e:src=v} f(v)
  rw [← Finset.sum_fiberwise_of_maps_to (g := G.src) (fun _ _ ↦ mem_univ _)]
  -- In each fiber, [src e ∈ T] = [v ∈ T], so inner sum = deg(v) · [v ∈ T]
  conv_lhs => arg 2; ext v; rw [Finset.sum_congr rfl (fun e he ↦ by
    rw [show G.src e = v from (mem_filter.mp he).2])]
  simp_rw [Finset.sum_const, nsmul_eq_mul]
  -- Goal: ∑ v, ↑(deg v) * (if v ∈ T then 1 else 0) = ∑ w ∈ T, ↑(deg w)
  simp_rw [mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  exact Finset.sum_congr (by ext v; simp) (fun _ _ ↦ rfl)

/-- The volume indicator vector: `φ_T(v) = √deg(v) · [v ∈ T]`. -/
def HalfEdgeGraph.volIndicatorVec {n : ℕ} (G : HalfEdgeGraph n) (T : Finset (Fin n)) :
    EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun v ↦ Real.sqrt (G.deg v) * if v ∈ T then 1 else 0)

@[simp]
theorem HalfEdgeGraph.volIndicatorVec_apply {n : ℕ} (G : HalfEdgeGraph n) (T : Finset (Fin n))
    (v : Fin n) :
    G.volIndicatorVec T v = Real.sqrt (G.deg v) * if v ∈ T then 1 else 0 := rfl

/-- `‖φ_T‖² = vol(T)`. -/
theorem HalfEdgeGraph.norm_sq_volIndicatorVec {n : ℕ} (G : HalfEdgeGraph n) (T : Finset (Fin n)) :
    ‖G.volIndicatorVec T‖ ^ 2 = ∑ v ∈ T, (G.deg v : ℝ) := by
  rw [EuclideanSpace.norm_sq_eq]
  simp_rw [Real.norm_eq_abs, sq_abs, volIndicatorVec_apply]
  simp_rw [mul_ite, mul_one, mul_zero, sq, ite_mul, zero_mul, mul_ite, mul_zero,
    Real.mul_self_sqrt (Nat.cast_nonneg _)]
  rw [Finset.sum_ite_mem, Finset.univ_inter]
  exact Finset.sum_congr rfl (fun v hv ↦ if_pos hv)

/-- The normalized walk operator on the volume indicator gives codeg/√deg. -/
theorem HalfEdgeGraph.normalizedWalkCLM_volIndicatorVec {n : ℕ} (G : HalfEdgeGraph n)
    (T : Finset (Fin n)) (v : Fin n) :
    G.normalizedWalkCLM (G.volIndicatorVec T) v =
    (G.codeg T v : ℝ) / Real.sqrt (G.deg v) := by
  simp only [normalizedWalkCLM_apply, volIndicatorVec_apply]
  -- LHS: (1/√d_v) * ∑_{e:src=v} (√d_t · [t∈T]) / √d_t
  -- Cancel √d_t in each summand: = (1/√d_v) * ∑_{e:src=v} [target∈T]
  have simplify : ∀ e ∈ univ.filter (G.src · = v),
      Real.sqrt ↑(G.deg (G.target e)) * (if G.target e ∈ T then 1 else 0) /
        Real.sqrt ↑(G.deg (G.target e)) =
      if G.target e ∈ T then 1 else 0 := by
    intro e _
    rcases Nat.eq_zero_or_pos (G.deg (G.target e)) with h | h
    · exfalso; have := G.deg_src_pos (G.rot e)
      simp only [HalfEdgeGraph.target] at h; omega
    · exact mul_div_cancel_left₀ _ (Real.sqrt_ne_zero'.mpr (Nat.cast_pos.mpr h))
  rw [Finset.sum_congr rfl simplify]
  -- Now: (1/√d_v) * ∑_{e:src=v} [target∈T] = codeg / √d_v
  rw [one_div, ← div_eq_inv_mul]
  congr 1
  simp only [codeg, Finset.sum_boole, Nat.cast_inj]
  congr 1; ext e; simp only [mem_filter, mem_univ, true_and, and_comm]

/-- `‖N·φ_T‖² = ∑_v codeg(T,v)² / deg(v)`. -/
theorem HalfEdgeGraph.norm_sq_walk_volIndicatorVec {n : ℕ} (G : HalfEdgeGraph n)
    (T : Finset (Fin n)) :
    ‖G.normalizedWalkCLM (G.volIndicatorVec T)‖ ^ 2 =
    ∑ v, (G.codeg T v : ℝ) ^ 2 / (G.deg v : ℝ) := by
  rw [EuclideanSpace.norm_sq_eq]
  simp_rw [Real.norm_eq_abs, sq_abs, G.normalizedWalkCLM_volIndicatorVec T, div_pow,
    Real.sq_sqrt (Nat.cast_nonneg _)]

/-- `P · N = P` for general graphs (via self-adjointness). -/
private theorem HalfEdgeGraph.degreeMeanCLM_comp_normalizedWalkCLM {n : ℕ} (G : HalfEdgeGraph n) :
    G.degreeMeanCLM * G.normalizedWalkCLM = G.degreeMeanCLM := by
  -- (PN)* = N*P* = NP = P, so PN = (PN)** = P** = P
  have h_adj : (G.degreeMeanCLM * G.normalizedWalkCLM).adjoint = G.degreeMeanCLM := by
    have : G.normalizedWalkCLM * G.degreeMeanCLM = G.degreeMeanCLM :=
      ContinuousLinearMap.ext G.normalizedWalkCLM_comp_degreeMean
    calc (G.degreeMeanCLM * G.normalizedWalkCLM).adjoint
        = G.normalizedWalkCLM.adjoint * G.degreeMeanCLM.adjoint := by
          show ContinuousLinearMap.adjoint (G.degreeMeanCLM.comp G.normalizedWalkCLM) = _
          exact ContinuousLinearMap.adjoint_comp _ _
      _ = G.normalizedWalkCLM * G.degreeMeanCLM := by
          rw [G.normalizedWalkCLM_isSelfAdjoint.adjoint_eq,
              G.degreeMeanCLM_isSelfAdjoint.adjoint_eq]
      _ = G.degreeMeanCLM := this
  calc G.degreeMeanCLM * G.normalizedWalkCLM
      = (G.degreeMeanCLM * G.normalizedWalkCLM).adjoint.adjoint := by
        rw [ContinuousLinearMap.adjoint_adjoint]
    _ = G.degreeMeanCLM.adjoint := by rw [h_adj]
    _ = G.degreeMeanCLM := G.degreeMeanCLM_isSelfAdjoint.adjoint_eq

/-- Key spectral bound: `halfs · ‖N·φ_T‖² ≤ vol(T) · (vol(T) + β² · (halfs - vol(T)))`.
    Uses the same orthogonal decomposition as the regular version. -/
private theorem norm_sq_walk_volIndicatorVec_le {n : ℕ} (G : HalfEdgeGraph n) (hh : 0 < G.halfs)
    (T : Finset (Fin n)) (β : ℝ) (hβ : G.spectralGap ≤ β) :
    let vol_T := ∑ v ∈ T, (G.deg v : ℝ)
    (G.halfs : ℝ) * ‖G.normalizedWalkCLM (G.volIndicatorVec T)‖ ^ 2 ≤
    vol_T * (vol_T + β ^ 2 * (↑G.halfs - vol_T)) := by
  set φ := G.volIndicatorVec T
  set vol_T := ∑ v ∈ T, (G.deg v : ℝ)
  set N_op := G.normalizedWalkCLM
  set P_op := G.degreeMeanCLM
  have hh_r : (0 : ℝ) < G.halfs := Nat.cast_pos.mpr hh
  have hh_ne : (G.halfs : ℝ) ≠ 0 := ne_of_gt hh_r
  -- P(N-P) = 0
  have hPA : P_op * (N_op - P_op) = (0 : _ →L[ℝ] _) := by
    rw [mul_sub, G.degreeMeanCLM_comp_normalizedWalkCLM, G.degreeMeanCLM_idempotent, sub_self]
  -- Orthogonality: ⟨Pφ, (N-P)φ⟩ = 0
  have hortho : @inner ℝ _ _ (P_op φ) ((N_op - P_op) φ) = 0 := by
    have h1 := ContinuousLinearMap.adjoint_inner_left P_op φ ((N_op - P_op) φ)
    rw [G.degreeMeanCLM_isSelfAdjoint.adjoint_eq] at h1
    rw [real_inner_comm, ← h1]
    show @inner ℝ _ _ ((P_op * (N_op - P_op)) φ) φ = 0
    rw [hPA, ContinuousLinearMap.zero_apply, inner_zero_left]
  -- Decompose: Nφ = Pφ + (N-P)φ
  have hdecomp : N_op φ = P_op φ + (N_op - P_op) φ := by
    simp only [ContinuousLinearMap.sub_apply]; abel
  -- Pythagorean: ‖Nφ‖² = ‖Pφ‖² + ‖(N-P)φ‖²
  have hpyth : ‖N_op φ‖ ^ 2 = ‖P_op φ‖ ^ 2 + ‖(N_op - P_op) φ‖ ^ 2 := by
    rw [hdecomp, norm_add_sq_real, hortho, mul_zero, add_zero]
  -- ‖Pφ‖² = vol(T)² / halfs
  have hPnorm : ‖P_op φ‖ ^ 2 = vol_T ^ 2 / ↑G.halfs := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [show P_op = G.degreeMeanCLM from rfl, show φ = G.volIndicatorVec T from rfl]
    simp_rw [Real.norm_eq_abs, sq_abs, HalfEdgeGraph.degreeMeanCLM_apply, HalfEdgeGraph.volIndicatorVec_apply]
    -- The inner product ∑_w φ(w) · √deg(w) = ∑_w deg(w) · [w∈T] = vol(T)
    have inner_eq : ∑ w, (Real.sqrt ↑(G.deg w) * if w ∈ T then 1 else 0) *
        Real.sqrt ↑(G.deg w) = vol_T := by
      simp_rw [mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
      rw [Finset.sum_ite_mem, univ_inter]
      apply Finset.sum_congr rfl; intro w _
      exact Real.mul_self_sqrt (Nat.cast_nonneg _)
    simp_rw [inner_eq, mul_div_assoc, mul_pow, div_pow,
      Real.sq_sqrt (Nat.cast_nonneg _)]
    rw [← Finset.sum_mul]
    have hsd' : (∑ v : Fin n, (G.deg v : ℝ)) = (G.halfs : ℝ) := by exact_mod_cast G.sum_deg
    rw [hsd']; field_simp
  -- (N-P)(Pφ) = 0
  have hAPf : (N_op - P_op) (P_op φ) = 0 := by
    simp only [ContinuousLinearMap.sub_apply]
    rw [G.normalizedWalkCLM_comp_degreeMean φ]
    show P_op φ - (P_op * P_op) φ = 0
    rw [G.degreeMeanCLM_idempotent, sub_self]
  -- ‖(N-P)φ‖ ≤ β · ‖φ - Pφ‖
  have hAnorm : ‖(N_op - P_op) φ‖ ≤ β * ‖φ - P_op φ‖ := by
    calc ‖(N_op - P_op) φ‖
        = ‖(N_op - P_op) (φ - P_op φ)‖ := by rw [map_sub, hAPf, sub_zero]
      _ ≤ ‖(N_op - P_op : _ →L[ℝ] _)‖ * ‖φ - P_op φ‖ := (N_op - P_op).le_opNorm _
      _ ≤ β * ‖φ - P_op φ‖ := mul_le_mul_of_nonneg_right hβ (norm_nonneg _)
  -- ‖φ‖² = vol(T) and ‖φ - Pφ‖² = vol(T) - vol(T)²/halfs
  have hfnorm : ‖φ‖ ^ 2 = vol_T := G.norm_sq_volIndicatorVec T
  -- P(φ - Pφ) = 0
  have hP_proj : P_op (φ - P_op φ) = 0 := by
    rw [map_sub]; show P_op φ - (P_op * P_op) φ = 0
    rw [G.degreeMeanCLM_idempotent, sub_self]
  -- Orthogonality of Pφ and (φ - Pφ)
  have hortho2 : @inner ℝ _ _ (P_op φ) (φ - P_op φ) = 0 := by
    have h1 := ContinuousLinearMap.adjoint_inner_left P_op φ (φ - P_op φ)
    rw [G.degreeMeanCLM_isSelfAdjoint.adjoint_eq] at h1
    rw [real_inner_comm, ← h1, hP_proj, inner_zero_left]
  have hfPf_sq : ‖φ - P_op φ‖ ^ 2 = vol_T - vol_T ^ 2 / ↑G.halfs := by
    have hf_decomp : φ = P_op φ + (φ - P_op φ) := by abel
    have : ‖φ‖ ^ 2 = ‖P_op φ‖ ^ 2 + ‖φ - P_op φ‖ ^ 2 := by
      conv_lhs => rw [hf_decomp]
      rw [norm_add_sq_real, hortho2, mul_zero, add_zero]
    linarith [hPnorm, hfnorm]
  -- ‖(N-P)φ‖² ≤ β² · (vol(T) - vol(T)²/halfs)
  have hAf_sq : ‖(N_op - P_op) φ‖ ^ 2 ≤ β ^ 2 * (vol_T - vol_T ^ 2 / ↑G.halfs) := by
    calc ‖(N_op - P_op) φ‖ ^ 2
        ≤ (β * ‖φ - P_op φ‖) ^ 2 := by
          apply sq_le_sq'
          · linarith [norm_nonneg ((N_op - P_op) φ),
              mul_nonneg (le_trans G.spectralGap_nonneg hβ) (norm_nonneg (φ - P_op φ))]
          · exact hAnorm
      _ = β ^ 2 * ‖φ - P_op φ‖ ^ 2 := by ring
      _ = β ^ 2 * (vol_T - vol_T ^ 2 / ↑G.halfs) := by rw [hfPf_sq]
  -- Final: halfs · ‖Nφ‖² ≤ vol(T) · (vol(T) + β² · (halfs - vol(T)))
  calc (G.halfs : ℝ) * ‖N_op φ‖ ^ 2
      = ↑G.halfs * (‖P_op φ‖ ^ 2 + ‖(N_op - P_op) φ‖ ^ 2) := by rw [hpyth]
    _ ≤ ↑G.halfs * (vol_T ^ 2 / ↑G.halfs + β ^ 2 * (vol_T - vol_T ^ 2 / ↑G.halfs)) := by
        apply mul_le_mul_of_nonneg_left _ (le_of_lt hh_r)
        linarith [hPnorm, hAf_sq]
    _ = vol_T * (vol_T + β ^ 2 * (↑G.halfs - vol_T)) := by field_simp

/-- **Volume Tanner bound** for general graphs:
    `vol(T) · halfs ≤ vol(N(T)) · (vol(T) + β² · (halfs - vol(T)))`. -/
theorem HalfEdgeGraph.tanner_bound_vol {n : ℕ} (G : HalfEdgeGraph n) (hh : 0 < G.halfs)
    (T : Finset (Fin n)) (hT_vol : 0 < ∑ v ∈ T, (G.deg v : ℝ))
    (β : ℝ) (hβ : G.spectralGap ≤ β) :
    (∑ v ∈ T, (G.deg v : ℝ)) * ↑G.halfs ≤
    (∑ v ∈ G.neighborSet T, (G.deg v : ℝ)) *
      ((∑ v ∈ T, (G.deg v : ℝ)) + β ^ 2 * (↑G.halfs - ∑ v ∈ T, (G.deg v : ℝ))) := by
  set NT := G.neighborSet T
  set vol_T := ∑ v ∈ T, (G.deg v : ℝ)
  set vol_NT := ∑ v ∈ NT, (G.deg v : ℝ)
  have hh_r : (0 : ℝ) < G.halfs := Nat.cast_pos.mpr hh
  -- Step 1: Cauchy-Schwarz on codegrees with volume weights
  -- vol(T)² = (∑_{N(T)} codeg)² ≤ vol(N(T)) · ∑_{N(T)} codeg²/deg
  have hcodeg_sum_NT : ∑ v ∈ NT, (G.codeg T v : ℝ) = vol_T := by
    rw [sum_subset (subset_univ NT) (fun v _ hv ↦ by
      simp only [Nat.cast_eq_zero]; exact G.codeg_eq_zero_of_not_mem T v hv)]
    have := G.codeg_sum T
    simp only [vol_T]; exact_mod_cast this
  -- Weighted CS: (∑ √d · c/√d)² ≤ (∑ d)(∑ c²/d)
  have cs : vol_T ^ 2 ≤ vol_NT *
      ∑ v ∈ NT, (G.codeg T v : ℝ) ^ 2 / (G.deg v : ℝ) := by
    rw [← hcodeg_sum_NT]
    -- Rewrite as (∑ a·b)² ≤ (∑ a²)(∑ b²) with a = √deg, b = codeg/√deg
    have h := sum_mul_sq_le_sq_mul_sq NT
      (fun v ↦ Real.sqrt (G.deg v))
      (fun v ↦ (G.codeg T v : ℝ) / Real.sqrt (G.deg v))
    -- Simplify ∑ a² = vol(N(T)) and ∑ a·b = ∑ codeg
    have ha_sq : ∑ v ∈ NT, Real.sqrt ↑(G.deg v) ^ 2 = vol_NT := by
      simp only [Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) _), vol_NT]
    have hab : ∑ v ∈ NT, Real.sqrt ↑(G.deg v) *
        ((G.codeg T v : ℝ) / Real.sqrt ↑(G.deg v)) =
        ∑ v ∈ NT, (G.codeg T v : ℝ) := by
      apply sum_congr rfl; intro v hv
      rcases Nat.eq_zero_or_pos (G.deg v) with hd | hd
      · -- deg = 0 ⟹ codeg = 0
        have hc : G.codeg T v = 0 := by
          simp only [HalfEdgeGraph.codeg, card_eq_zero, filter_eq_empty_iff]
          intro e _ ⟨hsrc, _⟩; linarith [hsrc ▸ G.deg_src_pos e]
        simp [hd, hc]
      · rw [mul_div_cancel₀ _ (Real.sqrt_ne_zero'.mpr (Nat.cast_pos.mpr hd))]
    have hb_sq : ∑ v ∈ NT, ((G.codeg T v : ℝ) / Real.sqrt ↑(G.deg v)) ^ 2 =
        ∑ v ∈ NT, (G.codeg T v : ℝ) ^ 2 / ↑(G.deg v) := by
      apply sum_congr rfl; intro v _
      rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    rw [hab, ha_sq, hb_sq] at h; exact h
  -- Step 2: ∑_{N(T)} codeg²/deg ≤ ∑_V codeg²/deg
  have hsumsq : ∑ v ∈ NT, (G.codeg T v : ℝ) ^ 2 / ↑(G.deg v) ≤
      ∑ v, (G.codeg T v : ℝ) ^ 2 / ↑(G.deg v) :=
    sum_le_sum_of_subset_of_nonneg (subset_univ NT)
      (fun _ _ _ ↦ div_nonneg (sq_nonneg _) (Nat.cast_nonneg _))
  -- Step 3: ∑_V codeg²/deg = ‖N·φ_T‖²
  have hcodeg_norm : ∑ v, (G.codeg T v : ℝ) ^ 2 / ↑(G.deg v) =
      ‖G.normalizedWalkCLM (G.volIndicatorVec T)‖ ^ 2 :=
    (G.norm_sq_walk_volIndicatorVec T).symm
  -- Step 4: Spectral bound (extract from let-binding)
  have hspec : (G.halfs : ℝ) * ‖G.normalizedWalkCLM (G.volIndicatorVec T)‖ ^ 2 ≤
      vol_T * (vol_T + β ^ 2 * (↑G.halfs - vol_T)) :=
    norm_sq_walk_volIndicatorVec_le G hh T β hβ
  -- Chain: vol(T)² · halfs ≤ vol(NT) · vol(T) · (vol(T) + β²(halfs - vol(T)))
  have h_combined : vol_T ^ 2 * ↑G.halfs ≤
      vol_NT * vol_T * (vol_T + β ^ 2 * (↑G.halfs - vol_T)) := by
    -- From CS: vol_T² ≤ vol_NT * ∑codeg²/deg
    -- From subset+norm: ∑codeg²/deg ≤ ‖N·φ_T‖²
    -- From spectral: halfs * ‖N·φ_T‖² ≤ vol_T * (...)
    have h1 : vol_T ^ 2 ≤ vol_NT * ‖G.normalizedWalkCLM (G.volIndicatorVec T)‖ ^ 2 := by
      calc vol_T ^ 2 ≤ vol_NT * ∑ v ∈ NT, (G.codeg T v : ℝ) ^ 2 / ↑(G.deg v) := cs
        _ ≤ vol_NT * ∑ v, (G.codeg T v : ℝ) ^ 2 / ↑(G.deg v) :=
            mul_le_mul_of_nonneg_left hsumsq (Finset.sum_nonneg (fun v _ ↦ Nat.cast_nonneg _))
        _ = vol_NT * ‖G.normalizedWalkCLM (G.volIndicatorVec T)‖ ^ 2 := by rw [hcodeg_norm]
    nlinarith [sq_nonneg ‖G.normalizedWalkCLM (G.volIndicatorVec T)‖,
      Finset.sum_nonneg (fun v (_ : v ∈ NT) ↦ Nat.cast_nonneg (α := ℝ) (G.deg v))]
  -- Cancel vol(T): vol(T) · halfs ≤ vol(NT) · (...)
  by_contra h; push_neg at h
  linarith [mul_lt_mul_of_pos_left h hT_vol]

/-- **Cardinality Tanner bound** for general graphs with bounded degree ratio:
    `|T| · n ≤ (d_max/d_min)² · |N(T)| · (|T| + β² · (n - |T|))`. -/
theorem HalfEdgeGraph.tanner_bound_card {n : ℕ} (G : HalfEdgeGraph n)
    (d_min d_max : ℕ) (hd_min : 0 < d_min)
    (h_lb : ∀ v, d_min ≤ G.deg v) (h_ub : ∀ v, G.deg v ≤ d_max)
    (hn : 0 < n) (T : Finset (Fin n)) (hT : 0 < T.card)
    (β : ℝ) (hβ : G.spectralGap ≤ β) :
    (T.card : ℝ) * ↑n ≤ (d_max : ℝ) ^ 2 / (d_min : ℝ) ^ 2 *
      ↑(G.neighborSet T).card * (↑T.card + β ^ 2 * (↑n - ↑T.card)) := by
  set NT := G.neighborSet T
  have hd_min_r : (0 : ℝ) < d_min := Nat.cast_pos.mpr hd_min
  have hd_max_pos : 0 < d_max := lt_of_lt_of_le hd_min (h_lb ⟨0, hn⟩ |>.trans (h_ub _))
  have hd_max_r : (0 : ℝ) < d_max := Nat.cast_pos.mpr hd_max_pos
  -- Volume bounds
  have h_vol_lb : (d_min : ℝ) * ↑T.card ≤ ∑ v ∈ T, (G.deg v : ℝ) :=
    calc (d_min : ℝ) * ↑T.card = ∑ _ ∈ T, (d_min : ℝ) := by
          rw [sum_const, nsmul_eq_mul, mul_comm]
      _ ≤ ∑ v ∈ T, (G.deg v : ℝ) :=
          sum_le_sum (fun v _ ↦ by exact_mod_cast h_lb v)
  have h_vol_NT_ub : ∑ v ∈ NT, (G.deg v : ℝ) ≤ (d_max : ℝ) * ↑NT.card :=
    calc ∑ v ∈ NT, (G.deg v : ℝ) ≤ ∑ _ ∈ NT, (d_max : ℝ) :=
          sum_le_sum (fun v _ ↦ by exact_mod_cast h_ub v)
      _ = (d_max : ℝ) * ↑NT.card := by rw [sum_const, nsmul_eq_mul, mul_comm]
  have h_halfs_ub : (G.halfs : ℝ) ≤ (d_max : ℝ) * ↑n := by
    have hsd := G.sum_deg
    calc (G.halfs : ℝ) = ∑ v, (G.deg v : ℝ) := by exact_mod_cast hsd.symm
      _ ≤ ∑ _, (d_max : ℝ) := sum_le_sum (fun v _ ↦ by exact_mod_cast h_ub v)
      _ = (d_max : ℝ) * ↑n := by
          rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_comm]
  have h_halfs_lb : (d_min : ℝ) * ↑n ≤ (G.halfs : ℝ) := by
    have hsd := G.sum_deg
    calc (d_min : ℝ) * ↑n
        = ∑ _, (d_min : ℝ) := by
          rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_comm]
      _ ≤ ∑ v, (G.deg v : ℝ) := sum_le_sum (fun v _ ↦ by exact_mod_cast h_lb v)
      _ = (G.halfs : ℝ) := by exact_mod_cast hsd
  have h_vol_compl : (G.halfs : ℝ) - ∑ v ∈ T, (G.deg v : ℝ) ≤
      (d_max : ℝ) * (↑n - ↑T.card) := by
    -- halfs - vol(T) = ∑_{v∉T} deg v ≤ d_max · (n - |T|)
    have hsd := G.sum_deg
    have hsplit : ∑ v ∈ univ \ T, (G.deg v : ℝ) + ∑ v ∈ T, (G.deg v : ℝ) =
        (G.halfs : ℝ) := by
      rw [Finset.sum_sdiff (subset_univ T)]; exact_mod_cast hsd
    have hthis : (G.halfs : ℝ) - ∑ v ∈ T, (G.deg v : ℝ) = ∑ v ∈ univ \ T, (G.deg v : ℝ) := by
      linarith
    rw [hthis]
    have hcard_eq : (univ \ T).card + T.card = n := by
      have := Finset.card_sdiff_add_card_eq_card (subset_univ T)
      rw [card_univ, Fintype.card_fin] at this; exact this
    have hcard : (↑(univ \ T).card : ℝ) = ↑n - ↑T.card := by
      have : (↑(univ \ T).card : ℝ) + ↑T.card = ↑n := by exact_mod_cast hcard_eq
      linarith
    calc ∑ v ∈ univ \ T, (G.deg v : ℝ) ≤ ∑ _ ∈ univ \ T, (d_max : ℝ) :=
          sum_le_sum (fun v _ ↦ by exact_mod_cast h_ub v)
      _ = (d_max : ℝ) * (↑n - ↑T.card) := by
          rw [sum_const, nsmul_eq_mul, mul_comm, hcard]
  have hh : 0 < G.halfs := by
    have h := h_halfs_lb
    exact_mod_cast calc (0 : ℝ) < (d_min : ℝ) * ↑n := mul_pos hd_min_r (Nat.cast_pos.mpr hn)
      _ ≤ (G.halfs : ℝ) := h
  have hT_vol : 0 < ∑ v ∈ T, (G.deg v : ℝ) := by
    linarith [mul_pos hd_min_r (Nat.cast_pos.mpr hT)]
  -- Apply volume Tanner bound
  have hvol := G.tanner_bound_vol hh T hT_vol β hβ
  -- From volume bound, derive cardinality bound
  -- Clear denominator: |T|·n ≤ (d_max/d_min)²·|NT|·(|T|+β²(n-|T|))
  -- ⟺ d_min²·|T|·n ≤ d_max²·|NT|·(|T|+β²(n-|T|))
  suffices hmul : (d_min : ℝ) ^ 2 * (↑T.card * ↑n) ≤
      (d_max : ℝ) ^ 2 * (↑NT.card * (↑T.card + β ^ 2 * (↑n - ↑T.card))) by
    rw [show (d_max : ℝ) ^ 2 / (d_min : ℝ) ^ 2 * ↑NT.card *
        (↑T.card + β ^ 2 * (↑n - ↑T.card)) =
        (d_max : ℝ) ^ 2 * (↑NT.card * (↑T.card + β ^ 2 * (↑n - ↑T.card))) /
        (d_min : ℝ) ^ 2 from by ring]
    rwa [le_div_iff₀ (sq_pos_of_pos hd_min_r), mul_comm]
  -- vol(T) ≤ d_max · |T|
  have h_vol_T_ub : ∑ v ∈ T, (G.deg v : ℝ) ≤ (d_max : ℝ) * ↑T.card :=
    calc ∑ v ∈ T, (G.deg v : ℝ) ≤ ∑ _ ∈ T, (d_max : ℝ) :=
          sum_le_sum (fun v _ ↦ by exact_mod_cast h_ub v)
      _ = (d_max : ℝ) * ↑T.card := by rw [sum_const, nsmul_eq_mul, mul_comm]
  -- LHS lower bound: d_min²·|T|·n ≤ vol(T)·halfs
  have h_lhs : (d_min : ℝ) ^ 2 * (↑T.card * ↑n) ≤
      (∑ v ∈ T, (G.deg v : ℝ)) * ↑G.halfs := by
    have := mul_le_mul h_vol_lb h_halfs_lb
      (mul_nonneg (le_of_lt hd_min_r) (Nat.cast_nonneg _))
      (Finset.sum_nonneg (fun v _ ↦ Nat.cast_nonneg (α := ℝ) _))
    nlinarith
  -- Inner bound: vol(T) + β²(halfs - vol(T)) ≤ d_max · (|T| + β²(n - |T|))
  have hβ_nn : 0 ≤ β := le_trans G.spectralGap_nonneg hβ
  have h_inner : ∑ v ∈ T, (G.deg v : ℝ) +
      β ^ 2 * (↑G.halfs - ∑ v ∈ T, (G.deg v : ℝ)) ≤
      (d_max : ℝ) * (↑T.card + β ^ 2 * (↑n - ↑T.card)) := by
    nlinarith [h_vol_T_ub, h_vol_compl, sq_nonneg β]
  -- RHS upper bound: vol(NT) · inner ≤ d_max² · |NT| · outer
  have h_vol_le_halfs : ∑ v ∈ T, (G.deg v : ℝ) ≤ ↑G.halfs := by
    have hsd : ∑ v, (G.deg v : ℝ) = ↑G.halfs := by exact_mod_cast G.sum_deg
    linarith [sum_le_sum_of_subset_of_nonneg (subset_univ T)
      (fun i _ _ ↦ Nat.cast_nonneg (α := ℝ) (G.deg i))]
  have h_inner_nn : (0 : ℝ) ≤ ∑ v ∈ T, (G.deg v : ℝ) +
      β ^ 2 * (↑G.halfs - ∑ v ∈ T, (G.deg v : ℝ)) := by
    nlinarith [sq_nonneg β, h_vol_le_halfs]
  have h_rhs : (∑ v ∈ NT, (G.deg v : ℝ)) *
      (∑ v ∈ T, (G.deg v : ℝ) + β ^ 2 * (↑G.halfs - ∑ v ∈ T, (G.deg v : ℝ))) ≤
      (d_max : ℝ) ^ 2 * (↑NT.card * (↑T.card + β ^ 2 * (↑n - ↑T.card))) := by
    have := mul_le_mul h_vol_NT_ub h_inner h_inner_nn (by positivity)
    nlinarith
  linarith [hvol]

end

end


