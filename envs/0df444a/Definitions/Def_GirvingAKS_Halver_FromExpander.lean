-- Prove2me | Definitions.Def_GirvingAKS_Halver_FromExpander
-- name    : GirvingAKS_Halver_FromExpander
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-22T18:34:05.079175+00:00
-- url     : https://prove2.me/theorems/8a9a3d08-ecf6-47dd-92e5-45d8532306b6
-- title:
--   AKS sorting networks (Seiferas port) — Expander → ε-Halver Bridge
-- statement:
--   Part of a port of the Lean development https://github.com/girving/aks (commit `c7fb62e`), which proves the Ajtai–Komlós–Szemerédi theorem: there are sorting networks of depth $O(\log n)$ and size $O(n\log n)$, following Seiferas's simplified separator-based construction (J. Seiferas, *Sorting networks of logarithmic depth, further simplified*, Algorithmica 53 (2009)). This definition bundle is the module `AKS/Halver/FromExpander.lean`; it contains the definitions of that module together with their supporting lemmas, so that later bundles can import them.
--
--   **Contents.** Given a d-regular graph G on m vertices with spectral gap ≤ β, constructs a β-halver comparator network of size m·d.
--
--   Key results:
--
--   - `expanderHalver`: the bipartite halver comparator network
--   - `expanderHalver_isEpsilonHalver`: expanders yield ε-halvers (proved via Tanner's bound)
--   - `expanderHalver_size`: the network has exactly m·d comparators
--   - `exists_halver_depth_le`: depth ≤ d (via König's edge coloring)
--
--   **Formalization Note** The file was ported from Lean v4.29.0-rc4 to Lean v4.33.1 / Mathlib `0df444a`. The ported text agrees with the upstream file except for small proof repairs needed by the newer toolchain, the removal of the Lean module-system keywords, and the renaming of the upstream structure `Graph` to `HalfEdgeGraph`, which avoids a clash with Mathlib's `Graph`.
-- source:
--   https://github.com/girving/aks/blob/c7fb62ed80a4a610f87f34db0082cadbd7c00c9f/AKS/Halver/FromExpander.lean (ported); Seiferas, Sorting networks of logarithmic depth, further simplified, Algorithmica 53 (2009) 374–384; Ajtai, Komlós, Szemerédi, Sorting in c log n parallel steps, Combinatorica 3 (1983) 1–19

import Definitions.Def_GirvingAKS_Halver_Defs
import Definitions.Def_GirvingAKS_Halver_Tanner
import Definitions.Def_GirvingAKS_Konig_Coloring
import Definitions.Def_GirvingAKS_Sort_Bipartite
import Definitions.Def_GirvingAKS_Sort_Depth
import Definitions.Def_GirvingAKS_Sort_Monotone
import Definitions.Def_GirvingAKS_Graph_Walk

/-! Ported to Lean v4.33.1 / Mathlib 0df444a from `AKS/Halver/FromExpander.lean` of
https://github.com/girving/aks (commit c7fb62ed80a4a610f87f34db0082cadbd7c00c9f, Apache-2.0). -/

/-
  # Expander → ε-Halver Bridge

  Given a d-regular graph G on m vertices with spectral gap ≤ β,
  constructs a β-halver comparator network of size m·d.

  Key results:
  • `expanderHalver`: the bipartite halver comparator network
  • `expanderHalver_isEpsilonHalver`: expanders yield ε-halvers (proved via Tanner's bound)
  • `expanderHalver_size`: the network has exactly m·d comparators
  • `exists_halver_depth_le`: depth ≤ d (via König's edge coloring)
-/


section


open Finset BigOperators


/-! **Bipartite Comparator Construction** -/

/-- The bipartite comparator list: for each vertex v and port p of G,
    compare wire v (top) with wire m + G.neighbor v p (bottom). -/
def bipartiteComparators {m d : ℕ} (G : RegularGraph m d) :
    List (Comparator (2 * m)) :=
  (List.finRange m).flatMap fun v =>
    (List.finRange d).map fun p =>
      { i := ⟨v.val, by omega⟩
        j := ⟨m + (G.neighbor v p).val, by omega⟩
        h := by simp [Fin.lt_def]; omega }

lemma bipartiteComparators_length {m d : ℕ} (G : RegularGraph m d) :
    (bipartiteComparators G).length = m * d := by
  simp [bipartiteComparators, List.length_flatMap, List.length_map,
    List.length_finRange, List.map_const', List.sum_replicate]

/-- All comparators in the bipartite network are bipartite: top wire < m ≤ bottom wire. -/
lemma bipartiteComparators_bipartite {m d : ℕ} (G : RegularGraph m d)
    (c : Comparator (2 * m)) (hc : c ∈ bipartiteComparators G) :
    c.i.val < m ∧ m ≤ c.j.val := by
  simp only [bipartiteComparators, List.mem_flatMap, List.mem_finRange, List.mem_map,
    true_and] at hc
  obtain ⟨v, p, rfl⟩ := hc
  exact ⟨v.isLt, Nat.le_add_right m _⟩

/-- The halver comparator network from a d-regular expander.
    For each vertex v and port p, compares wire v with wire m + G.neighbor v p. -/
def expanderHalver {m d : ℕ} (G : RegularGraph m d) : ComparatorNetwork (2 * m) :=
  ⟨bipartiteComparators G⟩

/-- The specific comparator for (v, p) is in `bipartiteComparators G`. -/
private lemma mem_bipartiteComparators {m d : ℕ} (G : RegularGraph m d)
    (v : Fin m) (p : Fin d) :
    (⟨⟨v.val, by omega⟩, ⟨m + (G.neighbor v p).val, by omega⟩,
      by simp [Fin.lt_def]; omega⟩ : Comparator (2 * m))
      ∈ bipartiteComparators G := by
  simp only [bipartiteComparators, List.mem_flatMap, List.mem_finRange, List.mem_map, true_and]
  exact ⟨v, p, rfl⟩

/-- After executing bipartite comparators, for each (v, p), output satisfies
    w[v] ≤ w[m + G.neighbor v p]. -/
private theorem exec_bipartite_edge_mono {m d : ℕ} {α : Type*} [LinearOrder α]
    (G : RegularGraph m d)
    (w : Fin (2 * m) → α) (v : Fin m) (p : Fin d) :
    (bipartiteComparators G).foldl (fun acc c ↦ c.apply acc) w
      ⟨v.val, by omega⟩ ≤
    (bipartiteComparators G).foldl (fun acc c ↦ c.apply acc) w
      ⟨m + (G.neighbor v p).val, by omega⟩ := by
  exact foldl_member_order (bipartiteComparators G)
    ⟨⟨v.val, by omega⟩, ⟨m + (G.neighbor v p).val, by omega⟩,
      by simp [Fin.lt_def]; omega⟩
    (mem_bipartiteComparators G v p)
    (bipartiteComparators_bipartite G) w


/-! **Tanner-Based Halver Proof** -/

/-- #{x : Fin n | x.val < k} = k when k ≤ n. -/
private lemma card_fin_filter_lt {n : ℕ} {k : ℕ} (hk : k ≤ n) :
    (univ.filter (fun x : Fin n ↦ x.val < k)).card = k := by
  rcases eq_or_lt_of_le hk with rfl | hlt
  · simp
  · rw [show univ.filter (fun x : Fin n ↦ x.val < k) = Finset.Iio (⟨k, hlt⟩ : Fin n) from by
      ext x; simp [Finset.mem_Iio, Fin.lt_def]]
    simp [Fin.card_Iio]

/-- A comparator network applied to a permutation preserves the count of
    positions with output value < k: exactly k positions have output < k. -/
lemma exec_perm_card_lt {n : ℕ} (net : ComparatorNetwork n)
    (v : Equiv.Perm (Fin n)) (k : ℕ) (hk : k ≤ n) :
    (univ.filter (fun i : Fin n ↦ (net.exec (v : Fin n → Fin n) i).val < k)).card = k := by
  -- g(x) = decide(k ≤ x.val) is monotone (false→true as x increases)
  set g : Fin n → Bool := fun x ↦ decide (k ≤ x.val) with g_def
  have hg : Monotone g := by
    intro a b hab; simp only [g_def]
    by_cases h : k ≤ a.val
    · simp [decide_eq_true_eq.mpr h, decide_eq_true_eq.mpr (le_trans h hab)]
    · simp only [not_le] at h; rw [decide_eq_false (by omega)]; exact Bool.false_le _
  -- g ∘ exec v = exec (g ∘ v), and countOnes is preserved
  have hcomm := net.exec_comp_monotone hg (v : Fin n → Fin n)
  have hpres := network_preserves_countOnes net (g ∘ (v : Fin n → Fin n))
  -- countOnes (g ∘ v) = n - k (v is a bijection, so exactly n-k values have k ≤ val)
  have hcount : countOnes (g ∘ (v : Fin n → Fin n)) = n - k := by
    simp only [countOnes, Function.comp, g_def, decide_eq_true_eq]
    -- Biject {i | k ≤ (v i).val} with {x | k ≤ x.val} via v
    have hbij : (univ.filter (fun i : Fin n ↦ k ≤ (v i).val)).card =
        (univ.filter (fun x : Fin n ↦ k ≤ x.val)).card :=
      Finset.card_nbij' (fun i ↦ v i) (fun x ↦ v.symm x)
        (by intro i hi; simp only [SetLike.mem_coe, Finset.mem_coe, mem_filter, mem_univ, true_and] at hi ⊢; exact hi)
        (by intro x hx; simp only [SetLike.mem_coe, Finset.mem_coe, mem_filter, mem_univ, true_and] at hx ⊢; simp [hx])
        (by intro i _; simp) (by intro x _; simp)
    rw [hbij]
    -- #{k ≤ x.val} = n - #{x.val < k} = n - k
    have hcomp := card_filter_add_card_filter_not (fun x : Fin n ↦ x.val < k) (s := univ)
    rw [card_fin_filter_lt hk] at hcomp
    have hge : (univ.filter (fun x : Fin n ↦ ¬x.val < k)).card = n - k := by
      simp only [Finset.card_univ, Fintype.card_fin] at hcomp; omega
    convert hge using 1; congr 1; ext x; simp only [not_lt]
  -- countOnes (g ∘ exec v) = n - k
  have h_co : countOnes (g ∘ net.exec (↑v)) = n - k := by
    have : g ∘ net.exec (↑v) = net.exec (g ∘ ↑v) := hcomm
    rw [this, hpres, hcount]
  -- #{val < k} = n - countOnes(g ∘ exec v) = n - (n-k) = k
  simp only [countOnes, Function.comp, g_def, decide_eq_true_eq] at h_co
  have hcomp := card_filter_add_card_filter_not
    (fun i : Fin n ↦ k ≤ (net.exec (↑v) i).val) (s := univ)
  rw [h_co, Finset.card_univ, Fintype.card_fin] at hcomp
  have hresult : (univ.filter (fun i : Fin n ↦ ¬k ≤ (net.exec (↑v) i).val)).card = k := by omega
  convert hresult using 1; congr 1; ext i; simp only [not_le]

/-- When d = 0, the spectral gap is at least 1 (for m > 0). -/
private lemma one_le_spectralGap_of_d_eq_zero {m : ℕ} (G : RegularGraph m 0) (hm : 0 < m) :
    1 ≤ spectralGap G := by
  -- d = 0: walkCLM = 0
  have hW : G.walkCLM = 0 := by ext f v; simp [RegularGraph.walkCLM_apply]
  unfold spectralGap; rw [hW, zero_sub, norm_neg]
  -- ‖meanCLM‖ ≥ 1: take the constant-1 vector, which is a fixed point of meanCLM
  set e : EuclideanSpace ℝ (Fin m) := (WithLp.equiv 2 _).symm (fun _ ↦ (1 : ℝ))
  have he_ne : e ≠ 0 := by
    intro h; apply one_ne_zero (α := ℝ)
    calc (1 : ℝ) = e ⟨0, hm⟩ := rfl
      _ = (0 : EuclideanSpace ℝ (Fin m)) ⟨0, hm⟩ := by rw [h]
      _ = 0 := rfl
  have he_pos : 0 < ‖e‖ := norm_pos_iff.mpr he_ne
  have hPe : (meanCLM m : _ →L[ℝ] _) e = e := by
    apply PiLp.ext; intro v; simp only [meanCLM_apply]
    change (∑ _ : Fin m, (1 : ℝ)) / ↑m = 1
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have : (0 : ℝ) < m := Nat.cast_pos.mpr hm
    field_simp
  have h := (meanCLM m : EuclideanSpace ℝ (Fin m) →L[ℝ] _).le_opNorm e
  rw [hPe] at h; exact le_of_mul_le_mul_right (by rwa [one_mul]) he_pos

/-- Contradiction helper: Tanner bound + large set = impossible.
    When `s > β·k` and the Tanner bound `s·m ≤ (k-s)·(s + β²(m-s))` holds,
    we derive False. The key is `(s - βk)² > 0` combined with `k ≤ m`. -/
private lemma tanner_halver_contradiction {s m k : ℕ} {β : ℝ}
    (hm : 0 < m) (hkm : k ≤ m)
    (hs : (s : ℝ) > β * ↑k)
    (hβ_nn : 0 ≤ β) (hsm : s ≤ m)
    (h_tanner : (s : ℝ) * ↑m ≤ (↑k - ↑s) * (↑s + β ^ 2 * (↑m - ↑s))) :
    False := by
  have hsm' : (s : ℝ) ≤ ↑m := by exact_mod_cast hsm
  have hkm' : (k : ℝ) ≤ ↑m := by exact_mod_cast hkm
  have hs_pos : (0 : ℝ) < ↑s := by
    calc (0 : ℝ) ≤ β * ↑k := mul_nonneg hβ_nn (Nat.cast_nonneg _)
      _ < ↑s := hs
  have hm_pos : (0 : ℝ) < ↑m := Nat.cast_pos.mpr hm
  -- s·m > 0
  have hsm_pos : (0 : ℝ) < ↑s * ↑m := mul_pos hs_pos hm_pos
  -- Case split: s ≥ k vs s < k
  by_cases hsk : k ≤ s
  · -- s ≥ k: RHS ≤ 0 < LHS
    have hks : (↑k : ℝ) ≤ ↑s := by exact_mod_cast hsk
    have h1 : (↑k : ℝ) - ↑s ≤ 0 := by linarith
    have h2 : (0 : ℝ) ≤ ↑s + β ^ 2 * (↑m - ↑s) := by nlinarith [sq_nonneg β]
    linarith [mul_nonpos_of_nonpos_of_nonneg h1 h2]
  · -- βk < s < k ≤ m
    push_neg at hsk
    have hsk' : (↑s : ℝ) < ↑k := by exact_mod_cast hsk
    -- From βk < s < k with k > 0: β < 1
    have hβ1 : β < 1 := by
      have : β * ↑k < 1 * ↑k := by linarith
      exact lt_of_mul_lt_mul_right this (Nat.cast_nonneg k)
    -- Factored identity: sm - (k-s)(s+β²(m-s)) = [s-β(k-s)][s+β(k-s)] + (m-k)[s-β²(k-s)]
    have h_factor : (↑s : ℝ) * ↑m - (↑k - ↑s) * (↑s + β ^ 2 * (↑m - ↑s)) =
        (↑s - β * (↑k - ↑s)) * (↑s + β * (↑k - ↑s)) +
        (↑m - ↑k) * (↑s - β ^ 2 * (↑k - ↑s)) := by ring
    have hks_nn : (0 : ℝ) ≤ ↑k - ↑s := by linarith
    have h1 : 0 < (↑s : ℝ) - β * (↑k - ↑s) := by nlinarith
    have h2 : 0 < (↑s : ℝ) + β * (↑k - ↑s) := by positivity
    have h3 : (0 : ℝ) ≤ ↑m - ↑k := by linarith
    have h4 : 0 < (↑s : ℝ) - β ^ 2 * (↑k - ↑s) := by
      nlinarith [mul_nonneg (mul_nonneg hβ_nn (by linarith : (0 : ℝ) ≤ 1 - β)) hks_nn]
    linarith [mul_pos h1 h2, mul_nonneg h3 (le_of_lt h4)]


/-! **Generalized Halver for Any Bipartite Network** -/

/-- General initial halved: any function w on Fin (2m) with permutation-count
    and edge-monotonicity properties satisfies the initial halver bound. -/
private lemma general_epsilon_initial_halved {m d : ℕ} (G : RegularGraph m d)
    (β : ℝ) (hβ : spectralGap G ≤ β) (hβ_nn : 0 ≤ β)
    (w : Fin (2 * m) → Fin (2 * m))
    (h_count : ∀ k : ℕ, k ≤ 2 * m →
      (univ.filter (fun i : Fin (2 * m) ↦ (w i).val < k)).card = k)
    (h_mono : ∀ v : Fin m, ∀ p : Fin d,
      w ⟨v.val, by omega⟩ ≤ w ⟨m + (G.neighbor v p).val, by omega⟩) :
    EpsilonInitialHalved w β := by
  show ∀ k : ℕ, k ≤ Fintype.card (Fin (2 * m)) / 2 →
    ((univ.filter (fun pos : Fin (2 * m) ↦
        Fintype.card (Fin (2 * m)) / 2 ≤ rank pos ∧ rank (w pos) < k)).card : ℝ) ≤ β * k
  simp only [Fintype.card_fin, show 2 * m / 2 = m from Nat.mul_div_cancel_left m (by omega)]
  intro k hk
  simp_rw [rank_fin_val]
  set s := (univ.filter (fun pos : Fin (2 * m) ↦ m ≤ pos.val ∧ (w pos).val < k)).card
  show (s : ℝ) ≤ β * ↑k
  rcases Nat.eq_zero_or_pos k with rfl | hk_pos
  · simp [show s = 0 from by
      simp only [s, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro pos _; simp]
  have hm : 0 < m := by omega
  set T : Finset (Fin m) := univ.filter (fun u : Fin m ↦ (w ⟨m + u.val, by omega⟩).val < k)
  have hs_eq : s = T.card := by
    simp only [s, T]
    apply Finset.card_nbij'
      (fun pos ↦ (⟨pos.val - m, by omega⟩ : Fin m))
      (fun u ↦ (⟨m + u.val, by omega⟩ : Fin (2 * m)))
    · intro pos hpos
      simp only [SetLike.mem_coe, Finset.mem_coe, mem_filter, mem_univ, true_and] at hpos ⊢
      have heq : (⟨m + (pos.val - m), (by omega : m + (pos.val - m) < 2 * m)⟩ : Fin (2 * m)) =
          pos := Fin.ext (by dsimp; omega)
      rw [heq]; exact hpos.2
    · intro u hu
      simp only [SetLike.mem_coe, Finset.mem_coe, mem_filter, mem_univ, true_and] at hu ⊢
      exact ⟨by omega, hu⟩
    · intro pos hpos
      simp only [SetLike.mem_coe, Finset.mem_coe, mem_filter, mem_univ, true_and] at hpos
      exact Fin.ext (by dsimp; omega)
    · intro u _; exact Fin.ext (by dsimp; omega)
  -- Neighborhood containment from edge monotonicity
  have hN_sub : G.neighborSet T ⊆ univ.filter (fun v : Fin m ↦
      (w ⟨v.val, by omega⟩).val < k) := by
    intro v hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    simp only [RegularGraph.neighborSet, Finset.mem_filter, Finset.mem_univ, true_and] at hv
    obtain ⟨p, hp⟩ := hv
    simp only [T, mem_filter, mem_univ, true_and] at hp
    exact lt_of_le_of_lt (Fin.le_def.mp (h_mono v p)) hp
  -- Counting: exactly k positions have output val < k
  have h_total : (univ.filter (fun i : Fin (2 * m) ↦ (w i).val < k)).card = k :=
    h_count k (by omega)
  have h_split := card_filter_fin_double (fun i : Fin (2 * m) ↦ (w i).val < k)
  set top_count := (univ.filter (fun v : Fin m ↦ (w ⟨v.val, by omega⟩).val < k)).card
  have h_total' : top_count + T.card = k := by rw [← h_split]; exact h_total
  have hN_card : (G.neighborSet T).card ≤ k - T.card := by
    have h1 : (G.neighborSet T).card ≤ top_count := Finset.card_le_card hN_sub
    omega
  -- Tanner contradiction
  by_contra h_contra; push_neg at h_contra
  rw [hs_eq] at h_contra
  have hT_pos : 0 < T.card := by
    rcases Nat.eq_zero_or_pos T.card with h0 | h0
    · simp [h0] at h_contra; linarith [mul_nonneg hβ_nn (Nat.cast_nonneg k)]
    · exact h0
  have hsm : T.card ≤ m := Finset.card_filter_le _ _ |>.trans (by simp)
  have hTk : T.card ≤ k := by omega
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · have h1 : 1 ≤ β := le_trans (one_le_spectralGap_of_d_eq_zero G hm) hβ
    have : (T.card : ℝ) ≤ β * ↑k := by
      calc (T.card : ℝ) ≤ ↑k := by exact_mod_cast hTk
        _ = 1 * ↑k := (one_mul _).symm
        _ ≤ β * ↑k := mul_le_mul_of_nonneg_right h1 (Nat.cast_nonneg k)
    linarith
  have h_tanner := tanner_bound G hd hm β hβ hβ_nn T hT_pos
  have h_combined : (T.card : ℝ) * ↑m ≤
      (↑k - ↑T.card) * (↑T.card + β ^ 2 * (↑m - ↑T.card)) := by
    have hsm' : (T.card : ℝ) ≤ ↑m := by exact_mod_cast hsm
    calc (T.card : ℝ) * ↑m
        ≤ ↑(G.neighborSet T).card * (↑T.card + β ^ 2 * (↑m - ↑T.card)) := h_tanner
      _ ≤ (↑k - ↑T.card) * (↑T.card + β ^ 2 * (↑m - ↑T.card)) := by
          apply mul_le_mul_of_nonneg_right _ (by nlinarith [sq_nonneg β])
          exact_mod_cast hN_card
  exact tanner_halver_contradiction hm hk h_contra hβ_nn hsm h_combined

/-- General final halved: dual of initial halved via OrderDual. -/
private lemma general_epsilon_final_halved {m d : ℕ} (G : RegularGraph m d)
    (β : ℝ) (hβ : spectralGap G ≤ β) (hβ_nn : 0 ≤ β)
    (w : Fin (2 * m) → Fin (2 * m))
    (h_count : ∀ k : ℕ, k ≤ 2 * m →
      (univ.filter (fun i : Fin (2 * m) ↦ (w i).val < k)).card = k)
    (h_mono : ∀ v : Fin m, ∀ p : Fin d,
      w ⟨v.val, by omega⟩ ≤ w ⟨m + (G.neighbor v p).val, by omega⟩) :
    EpsilonFinalHalved w β := by
  unfold EpsilonFinalHalved
  show ∀ k : ℕ, k ≤ Fintype.card (Fin (2 * m))ᵒᵈ / 2 →
    ((univ.filter (fun pos : (Fin (2 * m))ᵒᵈ ↦
        Fintype.card (Fin (2 * m))ᵒᵈ / 2 ≤ @rank (Fin (2 * m))ᵒᵈ _ _ pos ∧
        @rank (Fin (2 * m))ᵒᵈ _ _ (w pos) < k)).card : ℝ) ≤ β * k
  simp only [Fintype.card_fin, Fintype.card_orderDual,
    show 2 * m / 2 = m from Nat.mul_div_cancel_left m (by omega)]
  intro k hk
  simp_rw [rank_fin_od, rank_fin_od_fin]
  -- Convert OrderDual filter to Fin filter via congr
  -- (Fin n)ᵒᵈ and Fin n have the same .val, so the filters have equal cards
  suffices h : ∀ s_val : ℕ,
      s_val = (univ.filter (fun pos : Fin (2 * m) ↦
        pos.val < m ∧ 2 * m - k ≤ (w pos).val)).card →
      (s_val : ℝ) ≤ β * ↑k by
    apply h
    apply Finset.card_nbij' (fun x => OrderDual.ofDual x) (fun x => OrderDual.toDual x)
    · intro x hx; simp only [SetLike.mem_coe, Finset.mem_coe, mem_filter, mem_univ, true_and] at hx ⊢
      obtain ⟨h1, h2⟩ := hx
      -- Bridge OrderDual.ofDual identity for omega
      have hxv : (OrderDual.ofDual x).val = x.val := rfl
      have hwv : (OrderDual.ofDual (w x)).val = (w x).val := rfl
      have hx_le : x.val ≤ 2 * m - 1 := by omega
      have hw_le : (w x).val ≤ 2 * m - 1 := by omega
      have hm1 : 1 ≤ 2 * m := by omega
      have hk_le : k ≤ 2 * m := by omega
      constructor
      · zify [hx_le, hm1] at h1; omega
      · show 2 * m - k ≤ (OrderDual.ofDual (w x)).val
        rw [hwv]; zify [hw_le, hm1, hk_le] at h2 ⊢; omega
    · intro x hx; simp only [SetLike.mem_coe, Finset.mem_coe, mem_filter, mem_univ, true_and] at hx ⊢
      obtain ⟨h1, h2⟩ := hx
      have htv : (OrderDual.toDual x).val = x.val := rfl
      have htwv : (w (OrderDual.toDual x)).val = (w x).val := rfl
      have hm1 : 1 ≤ 2 * m := by omega
      have hk_le : k ≤ 2 * m := by omega
      constructor
      · show m ≤ 2 * m - 1 - (OrderDual.toDual x).val
        rw [htv]; zify [show x.val ≤ 2 * m - 1 from by omega, hm1]; omega
      · show 2 * m - 1 - (w (OrderDual.toDual x)).val < k
        rw [htwv]; zify [show (w x).val ≤ 2 * m - 1 from by omega, hm1, hk_le] at h2 ⊢; omega
    · intro x _; rfl
    · intro x _; rfl
  intro s rfl
  set s := (univ.filter (fun pos : Fin (2 * m) ↦
    pos.val < m ∧ 2 * m - k ≤ (w pos).val)).card
  show (s : ℝ) ≤ β * ↑k
  rcases Nat.eq_zero_or_pos k with rfl | hk_pos
  · simp [show s = 0 from by
      simp only [s, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro pos _; simp]
  have hm : 0 < m := by omega
  set T : Finset (Fin m) := univ.filter (fun v : Fin m ↦ 2 * m - k ≤ (w ⟨v.val, by omega⟩).val)
  have hs_eq : s = T.card := by
    show (univ.filter (fun pos : Fin (2 * m) ↦
      pos.val < m ∧ 2 * m - k ≤ (w pos).val)).card = T.card
    rw [← Finset.filter_filter]
    exact card_filter_top_half (fun i : Fin (2 * m) ↦ 2 * m - k ≤ (w i).val)
  -- Neighborhood containment (≥ direction) from edge monotonicity
  have hN_sub : G.neighborSet T ⊆ univ.filter (fun u : Fin m ↦
      2 * m - k ≤ (w ⟨m + u.val, by omega⟩).val) := by
    intro u hu
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    simp only [RegularGraph.neighborSet, Finset.mem_filter, Finset.mem_univ, true_and] at hu
    obtain ⟨p, hp⟩ := hu
    simp only [T, mem_filter, mem_univ, true_and] at hp
    have h1 := hp
    have h2 := Fin.le_def.mp (h_mono (G.neighbor u p) (G.reversePort u p))
    simp only [G.neighbor_reversePort] at h2
    exact le_trans h1 h2
  -- Counting complement
  have h_total_lt : (univ.filter (fun i : Fin (2 * m) ↦ (w i).val < 2 * m - k)).card =
      2 * m - k := h_count (2 * m - k) (by omega)
  have h_total : (univ.filter (fun i : Fin (2 * m) ↦ 2 * m - k ≤ (w i).val)).card = k := by
    have hcomp := card_filter_add_card_filter_not
      (fun i : Fin (2 * m) ↦ (w i).val < 2 * m - k) (s := univ)
    simp only [card_univ, Fintype.card_fin] at hcomp
    have : (univ.filter (fun i : Fin (2 * m) ↦ ¬(w i).val < 2 * m - k)).card = k := by omega
    convert this using 1; congr 1; ext i; simp only [not_lt]
  have h_split := card_filter_fin_double (fun i : Fin (2 * m) ↦ 2 * m - k ≤ (w i).val)
  set bottom_count := (univ.filter (fun u : Fin m ↦
    2 * m - k ≤ (w ⟨m + u.val, by omega⟩).val)).card
  have h_total' : T.card + bottom_count = k := by rw [← h_split]; exact h_total
  have hN_card : (G.neighborSet T).card ≤ k - T.card := by
    have h1 : (G.neighborSet T).card ≤ bottom_count := Finset.card_le_card hN_sub
    omega
  -- Tanner contradiction
  by_contra h_contra; push_neg at h_contra
  rw [hs_eq] at h_contra
  have hT_pos : 0 < T.card := by
    rcases Nat.eq_zero_or_pos T.card with h0 | h0
    · simp [h0] at h_contra; linarith [mul_nonneg hβ_nn (Nat.cast_nonneg k)]
    · exact h0
  have hsm : T.card ≤ m := Finset.card_filter_le _ _ |>.trans (by simp)
  have hTk : T.card ≤ k := by omega
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · have h1 : 1 ≤ β := le_trans (one_le_spectralGap_of_d_eq_zero G hm) hβ
    have : (T.card : ℝ) ≤ β * ↑k := by
      calc (T.card : ℝ) ≤ ↑k := by exact_mod_cast hTk
        _ = 1 * ↑k := (one_mul _).symm
        _ ≤ β * ↑k := mul_le_mul_of_nonneg_right h1 (Nat.cast_nonneg k)
    linarith
  have h_tanner := tanner_bound G hd hm β hβ hβ_nn T hT_pos
  have h_combined : (T.card : ℝ) * ↑m ≤
      (↑k - ↑T.card) * (↑T.card + β ^ 2 * (↑m - ↑T.card)) := by
    have hsm' : (T.card : ℝ) ≤ ↑m := by exact_mod_cast hsm
    calc (T.card : ℝ) * ↑m
        ≤ ↑(G.neighborSet T).card * (↑T.card + β ^ 2 * (↑m - ↑T.card)) := h_tanner
      _ ≤ (↑k - ↑T.card) * (↑T.card + β ^ 2 * (↑m - ↑T.card)) := by
          apply mul_le_mul_of_nonneg_right _ (by nlinarith [sq_nonneg β])
          exact_mod_cast hN_card
  exact tanner_halver_contradiction hm hk h_contra hβ_nn hsm h_combined

/-- Any bipartite comparator network containing all edges of G is a β-halver.
    The proof uses `foldl_member_order` for edge monotonicity (works for any
    ordering of bipartite comparators) and the Tanner bound for the halver
    counting argument. -/
theorem any_bipartite_isEpsilonHalver {m d : ℕ} (G : RegularGraph m d)
    (β : ℝ) (hβ : spectralGap G ≤ β)
    (net : ComparatorNetwork (2 * m))
    (h_bip : ∀ c ∈ net.comparators, c.i.val < m ∧ m ≤ c.j.val)
    (h_edges : ∀ v : Fin m, ∀ p : Fin d,
      (⟨⟨v.val, by omega⟩, ⟨m + (G.neighbor v p).val, by omega⟩,
        by simp [Fin.lt_def]; omega⟩ : Comparator (2 * m)) ∈ net.comparators) :
    IsEpsilonHalver net β := by
  have hβ_nn := le_trans (spectralGap_nonneg G) hβ
  intro v
  have h_mono : ∀ u : Fin m, ∀ p : Fin d,
      net.exec (↑v) ⟨u.val, by omega⟩ ≤
      net.exec (↑v) ⟨m + (G.neighbor u p).val, by omega⟩ :=
    fun u p ↦ foldl_member_order net.comparators _ (h_edges u p) h_bip (↑v)
  have h_count : ∀ k : ℕ, k ≤ 2 * m →
      (univ.filter (fun i : Fin (2 * m) ↦ (net.exec (↑v) i).val < k)).card = k :=
    fun k hk ↦ exec_perm_card_lt net v k hk
  exact ⟨general_epsilon_initial_halved G β hβ hβ_nn _ h_count h_mono,
         general_epsilon_final_halved G β hβ hβ_nn _ h_count h_mono⟩


/-! **Public API** -/

/-- `expanderHalver G` is a β-halver when the spectral gap of G is at most β.
    Proved via Tanner's vertex expansion bound + edge monotonicity + counting. -/
theorem expanderHalver_isEpsilonHalver {m d : ℕ} (G : RegularGraph m d)
    (β : ℝ) (hβ : spectralGap G ≤ β) :
    IsEpsilonHalver (expanderHalver G) β :=
  any_bipartite_isEpsilonHalver G β hβ (expanderHalver G)
    (bipartiteComparators_bipartite G) (mem_bipartiteComparators G)

/-- The halver network has exactly m·d comparators. -/
theorem expanderHalver_size {m d : ℕ} (G : RegularGraph m d) :
    (expanderHalver G).size = m * d := by
  simp only [expanderHalver, ComparatorNetwork.size]
  exact bipartiteComparators_length G


/-! **König Depth Bound** -/

/-- A König matching layer: for each vertex v, the comparator pairing v with
    the bottom vertex determined by the matching's port assignment. -/
def konigLayer {m d : ℕ} (G : RegularGraph m d)
    (portOf : Fin m → Fin d) : List (Comparator (2 * m)) :=
  (List.finRange m).map fun v ↦
    ⟨⟨v.val, by omega⟩, ⟨m + (G.neighbor v (portOf v)).val, by omega⟩,
     by simp [Fin.lt_def]; omega⟩

/-- A matching layer is parallel: no two comparators share a wire. -/
lemma konigLayer_isParallel {m d : ℕ} (G : RegularGraph m d)
    (portOf : Fin m → Fin d)
    (h_inj : Function.Injective (fun v ↦ G.neighbor v (portOf v))) :
    IsParallelLayer (konigLayer G portOf) := by
  simp only [konigLayer, IsParallelLayer, List.pairwise_map]
  apply List.Pairwise.imp _ (List.nodup_finRange m)
  intro v₁ v₂ hne
  unfold Comparator.overlaps; push_neg
  have h_bot_ne : (G.neighbor v₁ (portOf v₁)).val ≠ (G.neighbor v₂ (portOf v₂)).val :=
    fun h ↦ hne (h_inj (Fin.ext h))
  exact ⟨by simp [Fin.ext_iff]; exact Fin.val_ne_of_ne hne,
         by simp [Fin.ext_iff]; omega,
         by simp [Fin.ext_iff]; omega,
         by simp [Fin.ext_iff]; omega⟩

/-- For any d-regular graph G with spectral gap ≤ β, there exists a β-halver
    of size m·d and depth at most d. The depth bound follows from König's edge
    coloring theorem: the bipartite comparator multigraph has max degree d on
    both sides, so it decomposes into d matchings (parallel layers). The halver
    property is preserved under reordering because bipartite comparators maintain
    edge monotonicity in any order (top wires only decrease, bottom wires only
    increase after their comparator fires). -/
theorem exists_halver_depth_le {m d : ℕ} (G : RegularGraph m d)
    (β : ℝ) (hβ : spectralGap G ≤ β) :
    ∃ (net : ComparatorNetwork (2 * m)),
      IsEpsilonHalver net β ∧ net.size ≤ m * d ∧ net.depth ≤ d := by
  -- Case d = 0: use 0-layer parallel decomposition
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · exact ⟨expanderHalver G, expanderHalver_isEpsilonHalver G β hβ,
      le_of_eq (expanderHalver_size G),
      depth_le_of_decomposition _ [] ⟨fun _ h ↦ (nomatch h), by
        simp [expanderHalver, bipartiteComparators]⟩⟩
  -- Case d > 0: use König's edge coloring
  let B := RegBipartite.ofRegularGraph G
  let matchings := B.konigMatchings hd
  -- Build König layers: one per matching
  let layers : List (List (Comparator (2 * m))) :=
    (List.finRange d).map fun k ↦ konigLayer G (fun v ↦ (matchings k).portOf v)
  let net : ComparatorNetwork (2 * m) := ⟨layers.flatten⟩
  refine ⟨net, ?_, ?_, ?_⟩
  · -- Halver property
    apply any_bipartite_isEpsilonHalver G β hβ net
    · -- All comparators are bipartite
      intro c hc
      simp only [net, layers, List.mem_flatten, List.mem_map, List.mem_finRange, true_and] at hc
      obtain ⟨_, ⟨_, rfl⟩, hc'⟩ := hc
      simp only [konigLayer, List.mem_map, List.mem_finRange, true_and] at hc'
      obtain ⟨v, rfl⟩ := hc'
      exact ⟨v.isLt, Nat.le_add_right m _⟩
    · -- All edges are present: for each (v, p), the edge comparator is in the König list
      intro v p
      obtain ⟨k, hk⟩ := (B.konigMatchings_bijective hd v).2 p
      dsimp only at hk; subst hk
      show _ ∈ layers.flatten
      exact List.mem_flatten.mpr
        ⟨_, List.mem_map.mpr ⟨k, List.mem_finRange k, rfl⟩,
         List.mem_map.mpr ⟨v, List.mem_finRange v, rfl⟩⟩
  · -- Size bound
    show layers.flatten.length ≤ m * d
    simp only [layers, List.length_flatten, List.map_map, Function.comp_def,
      konigLayer, List.length_map, List.length_finRange, List.map_const',
      List.sum_replicate, smul_eq_mul]
    exact Nat.mul_comm d m ▸ le_refl _
  · -- Depth bound: d layers of parallel comparators
    have hdecomp : IsParallelDecomposition net layers :=
      ⟨fun layer hl ↦ by
        simp only [layers, List.mem_map, List.mem_finRange, true_and] at hl
        obtain ⟨k, rfl⟩ := hl
        exact konigLayer_isParallel G _ (matchings k).injective, rfl⟩
    calc net.depth ≤ layers.length := depth_le_of_decomposition net layers hdecomp
      _ = d := by simp [layers, List.length_map, List.length_finRange]

/-- The König halver: a computable β-halver network from a d-regular expander.
    For d > 0, decomposes the bipartite comparators into d parallel matching
    layers via König's edge coloring. For d = 0, uses the flat bipartite network.
    This replaces the noncomputable `exists_halver_depth_le.choose`. -/
def konigHalver {m d : ℕ} (G : RegularGraph m d) (hd : 0 < d) :
    ComparatorNetwork (2 * m) :=
  let B := RegBipartite.ofRegularGraph G
  let matchings := B.konigMatchings hd
  ⟨((List.finRange d).map fun k ↦
    konigLayer G (fun v ↦ (matchings k).portOf v)).flatten⟩

theorem konigHalver_isEpsilonHalver {m d : ℕ} (G : RegularGraph m d)
    (hd : 0 < d) (β : ℝ) (hβ : spectralGap G ≤ β) :
    IsEpsilonHalver (konigHalver G hd) β := by
  apply any_bipartite_isEpsilonHalver G β hβ
  · intro c hc
    unfold konigHalver at hc
    simp only [List.mem_flatten, List.mem_map, List.mem_finRange, true_and] at hc
    obtain ⟨_, ⟨_, rfl⟩, hc'⟩ := hc
    simp only [konigLayer, List.mem_map, List.mem_finRange, true_and] at hc'
    obtain ⟨v, rfl⟩ := hc'
    exact ⟨v.isLt, Nat.le_add_right m _⟩
  · intro v p
    let B := RegBipartite.ofRegularGraph G
    obtain ⟨k, hk⟩ := (B.konigMatchings_bijective hd v).2 p
    dsimp only at hk; subst hk
    show _ ∈ (konigHalver G hd).comparators
    unfold konigHalver
    exact List.mem_flatten.mpr
      ⟨_, List.mem_map.mpr ⟨k, List.mem_finRange k, rfl⟩,
       List.mem_map.mpr ⟨v, List.mem_finRange v, rfl⟩⟩

theorem konigHalver_depth_le {m d : ℕ} (G : RegularGraph m d) (hd : 0 < d) :
    (konigHalver G hd).depth ≤ d := by
  let B := RegBipartite.ofRegularGraph G
  let matchings := B.konigMatchings hd
  let layers := (List.finRange d).map fun k ↦
    konigLayer G (fun v ↦ (matchings k).portOf v)
  have hdecomp : IsParallelDecomposition (konigHalver G hd) layers :=
    ⟨fun layer hl ↦ by
      simp only [layers, List.mem_map, List.mem_finRange, true_and] at hl
      obtain ⟨k, rfl⟩ := hl
      exact konigLayer_isParallel G _ (matchings k).injective,
     by unfold konigHalver; rfl⟩
  calc (konigHalver G hd).depth ≤ layers.length :=
        depth_le_of_decomposition _ layers hdecomp
    _ = d := by simp [layers, List.length_map, List.length_finRange]

/-! **HalfEdgeGraph (Irregular) Bipartite Halver** -/

/-- Bipartite comparators from a general (irregular) graph.
    One comparator per half-edge: compare `src(e)` (top half) with
    `m + target(e)` (bottom half). -/
def graphBipartiteComparators {m : ℕ} (G : HalfEdgeGraph m) :
    List (Comparator (2 * m)) :=
  (List.finRange G.halfs).map fun e =>
    { i := ⟨(G.src e).val, by omega⟩
      j := ⟨m + (G.target e).val, by omega⟩
      h := by simp [Fin.lt_def]; omega }

private lemma graphBipartiteComparators_length {m : ℕ} (G : HalfEdgeGraph m) :
    (graphBipartiteComparators G).length = G.halfs := by
  simp [graphBipartiteComparators]

/-- All comparators from a `HalfEdgeGraph` are bipartite: top wire < m ≤ bottom wire. -/
private lemma graphBipartiteComparators_bipartite {m : ℕ} (G : HalfEdgeGraph m)
    (c : Comparator (2 * m)) (hc : c ∈ graphBipartiteComparators G) :
    c.i.val < m ∧ m ≤ c.j.val := by
  simp only [graphBipartiteComparators, List.mem_map, List.mem_finRange, true_and] at hc
  obtain ⟨e, rfl⟩ := hc
  exact ⟨(G.src e).isLt, Nat.le_add_right m _⟩

/-- The specific comparator for half-edge `e` is in `graphBipartiteComparators G`. -/
private lemma mem_graphBipartiteComparators {m : ℕ} (G : HalfEdgeGraph m) (e : Fin G.halfs) :
    (⟨⟨(G.src e).val, by omega⟩, ⟨m + (G.target e).val, by omega⟩,
      by simp [Fin.lt_def]; omega⟩ : Comparator (2 * m))
      ∈ graphBipartiteComparators G := by
  simp only [graphBipartiteComparators, List.mem_map, List.mem_finRange, true_and]
  exact ⟨e, rfl⟩

/-- After executing graph bipartite comparators, for each half-edge `e`,
    `output[src(e)] ≤ output[m + target(e)]`. -/
private theorem exec_graphBipartite_edge_mono {m : ℕ} {α : Type*} [LinearOrder α]
    (G : HalfEdgeGraph m) (w : Fin (2 * m) → α) (e : Fin G.halfs) :
    (graphBipartiteComparators G).foldl (fun acc c ↦ c.apply acc) w
      ⟨(G.src e).val, by omega⟩ ≤
    (graphBipartiteComparators G).foldl (fun acc c ↦ c.apply acc) w
      ⟨m + (G.target e).val, by omega⟩ :=
  foldl_member_order (graphBipartiteComparators G)
    ⟨⟨(G.src e).val, by omega⟩, ⟨m + (G.target e).val, by omega⟩,
      by simp [Fin.lt_def]; omega⟩
    (mem_graphBipartiteComparators G e)
    (graphBipartiteComparators_bipartite G) w

end


