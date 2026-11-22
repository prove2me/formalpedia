-- Prove2me | Definitions.Def_GirvingAKS_Graph_Square
-- name    : GirvingAKS_Graph_Square
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-22T18:30:49.20332+00:00
-- url     : https://prove2.me/theorems/cce4c8cb-290d-445e-af0c-bb07875e82d5
-- title:
--   AKS sorting networks (Seiferas port) — HalfEdgeGraph Squaring and Spectral Gap Squaring
-- statement:
--   Part of a port of the Lean development https://github.com/girving/aks (commit `c7fb62e`), which proves the Ajtai–Komlós–Szemerédi theorem: there are sorting networks of depth $O(\log n)$ and size $O(n\log n)$, following Seiferas's simplified separator-based construction (J. Seiferas, *Sorting networks of logarithmic depth, further simplified*, Algorithmica 53 (2009)). This definition bundle is the module `AKS/Graph/Square.lean`; it contains the definitions of that module together with their supporting lemmas, so that later bundles can import them.
--
--   **Contents.** The square G² of a `d`-regular graph takes two steps along G's edges, yielding a d²-regular graph. The key result is `spectralGap_square`: λ(G²) = λ(G)², proved via the C*-algebra identity `(W - P)² = W² - P` (from `WP = PW = P`).
--
--   **Formalization Note** The file was ported from Lean v4.29.0-rc4 to Lean v4.33.1 / Mathlib `0df444a`. The ported text agrees with the upstream file except for small proof repairs needed by the newer toolchain, the removal of the Lean module-system keywords, and the renaming of the upstream structure `Graph` to `HalfEdgeGraph`, which avoids a clash with Mathlib's `Graph`.
-- source:
--   https://github.com/girving/aks/blob/c7fb62ed80a4a610f87f34db0082cadbd7c00c9f/AKS/Graph/Square.lean (ported); Seiferas, Sorting networks of logarithmic depth, further simplified, Algorithmica 53 (2009) 374–384; Ajtai, Komlós, Szemerédi, Sorting in c log n parallel steps, Combinatorica 3 (1983) 1–19

import Definitions.Def_GirvingAKS_Graph_Regular

/-! Ported to Lean v4.33.1 / Mathlib 0df444a from `AKS/Graph/Square.lean` of
https://github.com/girving/aks (commit c7fb62ed80a4a610f87f34db0082cadbd7c00c9f, Apache-2.0). -/

/-
  # HalfEdgeGraph Squaring and Spectral Gap Squaring

  The square G² of a `d`-regular graph takes two steps along G's edges,
  yielding a d²-regular graph. The key result is `spectralGap_square`:
  λ(G²) = λ(G)², proved via the C*-algebra identity
  `(W - P)² = W² - P` (from `WP = PW = P`).
-/


section


open Matrix BigOperators Finset


/-! **HalfEdgeGraph Squaring** -/

-- The square G² of a d-regular graph: take two steps.
-- G² is d²-regular. Rot_{G²}(v, (i,j)) follows edge i from v,
-- then edge j from the result.

/-- The rotation map for G²: decode port as (i,j), take step i then step j,
    encode the reverse ports as j'*d + i'. Uses projections (not destructuring)
    so that simp can work with it. -/
def square_rot {n d : ℕ} (G : RegularGraph n d)
    (p : Fin n × Fin (d * d)) : Fin n × Fin (d * d) :=
  have hd : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; exact absurd p.2.isLt (by simp))
  let i : Fin d := ⟨p.2.val / d, (Nat.div_lt_iff_lt_mul hd).mpr p.2.isLt⟩
  let j : Fin d := ⟨p.2.val % d, Nat.mod_lt _ hd⟩
  let step1 := G.rot (p.1, i)
  let step2 := G.rot (step1.1, j)
  (step2.1, ⟨step2.2.val * d + step1.2.val, Fin.pair_lt step2.2 step1.2⟩)

theorem square_rot_involution {n d : ℕ} (G : RegularGraph n d)
    (p : Fin n × Fin (d * d)) : square_rot G (square_rot G p) = p := by
  obtain ⟨v, ij⟩ := p
  simp only [square_rot, fin_encode_fst, fin_encode_snd, Prod.mk.eta, G.rot_involution,
    fin_div_add_mod]

def RegularGraph.square {n d : ℕ} (G : RegularGraph n d) :
    RegularGraph n (d * d) where
  rot := square_rot G
  rot_involution := square_rot_involution G

theorem square_neighbor_unfold {n d : ℕ} (G : RegularGraph n d)
    (u : Fin n) (p : Fin (d * d)) (hd : 0 < d) :
    G.square.neighbor u p =
      G.neighbor (G.neighbor u ⟨p.val / d, (Nat.div_lt_iff_lt_mul hd).mpr p.isLt⟩)
        ⟨p.val % d, Nat.mod_lt _ hd⟩ := by
  simp only [RegularGraph.square, RegularGraph.neighbor, square_rot]

private theorem adjMatrix_square_eq_sq {n d : ℕ} (G : RegularGraph n d) :
    adjMatrix G.square = (adjMatrix G) ^ 2 := by
  ext u v
  simp only [adjMatrix_apply, sq, Matrix.mul_apply, div_mul_div_comm]
  rw [← Finset.sum_div, Nat.cast_mul]
  congr 1
  -- Need: ↑(filter card) = ∑ w, ↑card_uw * ↑card_wv  (as ℝ)
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  · -- Prove the Nat-level identity and cast
    have key : (univ.filter (fun p : Fin (d * d) ↦ G.square.neighbor u p = v)).card =
        ∑ w : Fin n, (univ.filter (fun i : Fin d ↦ G.neighbor u i = w)).card *
          (univ.filter (fun j : Fin d ↦ G.neighbor w j = v)).card := by
      -- Partition by intermediate vertex
      rw [Finset.card_eq_sum_card_fiberwise
        (f := fun p ↦ G.neighbor u ⟨p.val / d, (Nat.div_lt_iff_lt_mul hd).mpr p.isLt⟩)
        (fun _ _ ↦ Finset.mem_coe.mpr (Finset.mem_univ _))]
      congr 1; ext w
      -- Fiber card = card_uw * card_wv
      rw [← Finset.card_product]
      apply Finset.card_nbij'
        -- forward: decode port p as (p/d, p%d)
        (fun p ↦ (⟨p.val / d, (Nat.div_lt_iff_lt_mul hd).mpr p.isLt⟩,
                   ⟨p.val % d, Nat.mod_lt _ hd⟩))
        -- backward: encode (i, j) as i * d + j
        (fun ij ↦ ⟨ij.1.val * d + ij.2.val, Fin.pair_lt ij.1 ij.2⟩)
      -- forward MapsTo
      · intro p hp
        simp only [SetLike.mem_coe, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_product] at hp ⊢
        exact ⟨hp.2, by rw [← hp.2, ← square_neighbor_unfold G u p hd]; exact hp.1⟩
      -- backward MapsTo
      · intro ij hij
        simp only [SetLike.mem_coe, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_product] at hij ⊢
        constructor
        · -- G.square.neighbor u ⟨i*d+j, _⟩ = v
          rw [square_neighbor_unfold G u _ hd, fin_encode_fst, fin_encode_snd]
          rw [hij.1]; exact hij.2
        · -- G.neighbor u ⟨(i*d+j)/d, _⟩ = w
          have := fin_encode_fst ij.1 ij.2
            ((Nat.div_lt_iff_lt_mul hd).mpr (Fin.pair_lt ij.1 ij.2))
          simp only [this]; exact hij.1
      -- LeftInvOn: backward ∘ forward = id
      · intro p hp
        exact fin_div_add_mod p _
      -- RightInvOn: forward ∘ backward = id
      · intro ij hij
        refine Prod.ext ?_ ?_
        · exact fin_encode_fst ij.1 ij.2
            ((Nat.div_lt_iff_lt_mul hd).mpr (Fin.pair_lt ij.1 ij.2))
        · exact fin_encode_snd ij.1 ij.2 (Nat.mod_lt _ hd)
    exact_mod_cast key


/-! **CLM Algebraic Identities for Spectral Gap Squaring** -/

/-- Rotation bijection swaps function arguments in a product sum:
    ∑_{v,i} f(neighbor(v,i))·g(v) = ∑_{v,i} f(v)·g(neighbor(v,i)). -/
theorem RegularGraph.sum_neighbor_swap {n d : ℕ} (G : RegularGraph n d)
    (f g : Fin n → ℝ) :
    ∑ v : Fin n, ∑ i : Fin d, f (G.neighbor v i) * g v =
    ∑ v : Fin n, ∑ i : Fin d, f v * g (G.neighbor v i) := by
  simp_rw [← Fintype.sum_prod_type', RegularGraph.neighbor]
  -- Reindex by rot (a bijection): ∑ p, h(rot p) = ∑ p, h(p)
  have h := G.rotEquiv.sum_comp (fun q ↦ f q.1 * g (G.rot q).1)
  simp only [show ∀ p, (G.rotEquiv p : Fin n × Fin d) = G.rot p from fun _ ↦ rfl,
    G.rot_involution] at h
  exact h

/-- The walk operator is self-adjoint: ⟪Wf, g⟫ = ⟪f, Wg⟫. -/
theorem walkCLM_isSelfAdjoint {n d : ℕ} (G : RegularGraph n d) :
    IsSelfAdjoint G.walkCLM := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro f g
  change @inner ℝ _ _ (G.walkCLM f) g = @inner ℝ _ _ f (G.walkCLM g)
  -- inner on EuclideanSpace: ⟪x, y⟫ = ∑ v, y v * x v (via RCLike.inner_apply)
  simp only [PiLp.inner_apply, RegularGraph.walkCLM_apply]
  simp_rw [show ∀ (a b : ℝ), @inner ℝ ℝ _ a b = b * a from fun a b => by
    show RCLike.re (b * starRingEnd ℝ a) = b * a
    simp only [RCLike.conj_to_real, RCLike.re_to_real]]
  -- Goal: ∑ v, g v * ((∑ i, f(nbr v i))/d) = ∑ v, ((∑ i, g(nbr v i))/d) * f v
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  · simp_rw [mul_div_assoc', div_mul_eq_mul_div, ← Finset.sum_div]
    congr 1
    simp_rw [Finset.mul_sum, Finset.sum_mul]
    exact (G.sum_neighbor_swap (fun v ↦ g v) (fun v ↦ f v)).symm

/-- The mean projection absorbs the walk operator: P ∘ W = P (for d > 0). -/
theorem meanCLM_comp_walkCLM {n d : ℕ} (G : RegularGraph n d) (hd : 0 < d) :
    meanCLM n * G.walkCLM = (meanCLM n : EuclideanSpace ℝ (Fin n) →L[ℝ] _) := by
  ext f v
  simp only [ContinuousLinearMap.mul_apply, meanCLM_apply, RegularGraph.walkCLM_apply]
  -- Goal: (∑ u, (∑ i, f(nbr u i)) / d) / n = (∑ u, f u) / n
  congr 1
  -- Pull /d out of the sum
  rw [← Finset.sum_div]
  -- Now: (∑ u, ∑ i, f(nbr u i)) / d = ∑ u, f u
  rw [G.sum_neighbor_eq (fun v ↦ f v)]
  -- (∑ u, ∑ _i, f u) / d = ∑ u, f u
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← Finset.mul_sum, mul_div_cancel_left₀ _ (by positivity : (d : ℝ) ≠ 0)]

/-- Equivalence between Fin d × Fin d and Fin (d * d) via the
    encode/decode pair (i * d + j) ↔ (i, j). -/
def finPairEquiv {d : ℕ} (hd : 0 < d) : Fin d × Fin d ≃ Fin (d * d) where
  toFun ij := ⟨ij.1.val * d + ij.2.val, Fin.pair_lt ij.1 ij.2⟩
  invFun p := (⟨p.val / d, (Nat.div_lt_iff_lt_mul hd).mpr p.isLt⟩,
               ⟨p.val % d, Nat.mod_lt _ hd⟩)
  left_inv ij := Prod.ext
    (fin_encode_fst ij.1 ij.2 ((Nat.div_lt_iff_lt_mul hd).mpr (Fin.pair_lt ij.1 ij.2)))
    (fin_encode_snd ij.1 ij.2 (Nat.mod_lt _ hd))
  right_inv p := fin_div_add_mod p (Fin.pair_lt
    ⟨p.val / d, (Nat.div_lt_iff_lt_mul hd).mpr p.isLt⟩
    ⟨p.val % d, Nat.mod_lt _ hd⟩)

/-- The walk operator of G² equals the square of G's walk operator:
    W_{G²} = W_G ∘ W_G. -/
private theorem walkCLM_sq {n d : ℕ} (G : RegularGraph n d) :
    G.square.walkCLM = G.walkCLM * G.walkCLM := by
  ext f v
  simp only [ContinuousLinearMap.mul_apply, RegularGraph.walkCLM_apply]
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  · -- Transform RHS: (∑ i, (∑ j, ...)/d) / d → (∑ i, ∑ j, ...) / (d*d)
    rw [← Finset.sum_div, div_div,
      show (↑(d * d) : ℝ) = ↑d * ↑d from by push_cast; ring]
    -- Both sides: (sum) / (d * d). Show numerators equal.
    congr 1
    -- LHS: ∑ p : Fin(d*d), f(sq.nbr v p) = ∑ (i,j) : Fin d × Fin d, f(nbr(nbr v i) j)
    rw [← Fintype.sum_prod_type']
    exact Fintype.sum_equiv (finPairEquiv hd).symm _ _ (fun p ↦ by
      simp only [RegularGraph.square, RegularGraph.neighbor, square_rot, finPairEquiv,
        Equiv.symm]
      rfl)

/-! **Iterated HalfEdgeGraph Squaring** -/

/-- Degree after `p` squarings: `d^(2^p)`. -/
def iterSquareDeg (d p : ℕ) : ℕ :=
  match p with
  | 0 => d
  | p + 1 => iterSquareDeg d p * iterSquareDeg d p

/-- Iterated graph squaring: apply `.square` `p` times. -/
def RegularGraph.iterSquare {n d : ℕ} (G : RegularGraph n d) :
    (p : ℕ) → RegularGraph n (iterSquareDeg d p)
  | 0 => G
  | p + 1 => (G.iterSquare p).square

/-- `iterSquareDeg` is monotone in its first argument. -/
theorem iterSquareDeg_mono {d₁ d₂ : ℕ} (h : d₁ ≤ d₂) (p : ℕ) :
    iterSquareDeg d₁ p ≤ iterSquareDeg d₂ p := by
  induction p with
  | zero => exact h
  | succ p ih => exact Nat.mul_le_mul ih ih

/-- `iterSquareDeg` preserves positivity. -/
theorem iterSquareDeg_pos {d : ℕ} (hd : 0 < d) (p : ℕ) : 0 < iterSquareDeg d p := by
  induction p with
  | zero => exact hd
  | succ p ih => exact Nat.mul_pos ih ih

/-- `iterSquareDeg (2^m) p = 2^(m * 2^p)`. -/
theorem iterSquareDeg_pow2 (m p : ℕ) : iterSquareDeg (2 ^ m) p = 2 ^ (m * 2 ^ p) := by
  induction p with
  | zero => simp [iterSquareDeg]
  | succ p ih =>
    simp only [iterSquareDeg, ih, ← Nat.pow_add]
    congr 1; rw [pow_succ]; ring

theorem spectralGap_square {n d : ℕ} (G : RegularGraph n d) :
    spectralGap G.square = (spectralGap G) ^ 2 := by
  unfold spectralGap
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · -- d = 0: both walkCLMs are 0, spectralGap = ‖meanCLM‖
    have hW : G.walkCLM = 0 := by
      ext f v; simp [RegularGraph.walkCLM_apply]
    have hW2 : G.square.walkCLM = 0 := by
      ext f v; simp [RegularGraph.walkCLM_apply]
    simp only [hW, hW2, zero_sub, norm_neg]
    -- ‖P‖ = ‖P‖² since P is self-adjoint idempotent
    have hidp := meanCLM_idempotent n
    have hsa := meanCLM_isSelfAdjoint n
    rw [← @IsSelfAdjoint.norm_mul_self _ _ ContinuousLinearMap.instStarRingId _ _ hsa, hidp]
  · -- d > 0: algebraic identity (W - P)² = W² - P
    -- Use abbreviations W and P (let, not set, to keep transparent)
    let W := G.walkCLM
    let P : EuclideanSpace ℝ (Fin n) →L[ℝ] _ := meanCLM n
    have hWP : W * P = P := by
      refine ContinuousLinearMap.ext (fun f ↦ ?_)
      exact walkCLM_comp_meanCLM G hd f
    have hPW : P * W = P := meanCLM_comp_walkCLM G hd
    have hPP : P * P = P := meanCLM_idempotent n
    have hsq : (W - P) * (W - P) = W * W - P := by
      have : (W - P) * (W - P) = W * W - W * P - P * W + P * P := by
        simp only [mul_sub, sub_mul]; abel
      rw [this, hWP, hPW, hPP]; abel
    rw [walkCLM_sq G, ← hsq]
    have hsa : IsSelfAdjoint (W - P) := by
      rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric, ContinuousLinearMap.coe_sub]
      exact ((ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
        (walkCLM_isSelfAdjoint G)).sub
        (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (meanCLM_isSelfAdjoint n)))
    rw [← @IsSelfAdjoint.norm_mul_self _ _ ContinuousLinearMap.instStarRingId _ _ hsa]

/-- Spectral gap of iterated squaring: `spectralGap (G.iterSquare p) = (spectralGap G) ^ (2^p)`. -/
theorem spectralGap_iterSquare {n d : ℕ} (G : RegularGraph n d) (p : ℕ) :
    spectralGap (G.iterSquare p) = (spectralGap G) ^ (2 ^ p) := by
  induction p with
  | zero => unfold RegularGraph.iterSquare; simp [pow_zero]; rfl
  | succ p ih =>
    show spectralGap (G.iterSquare p).square = spectralGap G ^ 2 ^ (p + 1)
    rw [spectralGap_square, ih, ← pow_mul, ← pow_succ]

end


