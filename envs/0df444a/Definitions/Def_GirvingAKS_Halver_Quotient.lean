-- Prove2me | Definitions.Def_GirvingAKS_Halver_Quotient
-- name    : GirvingAKS_Halver_Quotient
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-22T18:36:00.736576+00:00
-- url     : https://prove2.me/theorems/1c5f58b0-d4a9-4117-bf5a-59ccc5e29c11
-- title:
--   AKS sorting networks (Seiferas port) — Quotient Halver: Direct Tanner Bound for Non-Integer Quotients
-- statement:
--   Part of a port of the Lean development https://github.com/girving/aks (commit `c7fb62e`), which proves the Ajtai–Komlós–Szemerédi theorem: there are sorting networks of depth $O(\log n)$ and size $O(n\log n)$, following Seiferas's simplified separator-based construction (J. Seiferas, *Sorting networks of logarithmic depth, further simplified*, Algorithmica 53 (2009)). This definition bundle is the module `AKS/Halver/Quotient.lean`; it contains the definitions of that module together with their supporting lemmas, so that later bundles can import them.
--
--   **Contents.** For a `d`-regular graph `G` on `N` vertices with spectral gap `β`, builds an ε-halver on `2 * m` wires for any target `m ≤ N` by projecting through `v ↦ v % m`. Unlike equal-fiber contraction (`contractDivisible`), this works even when `m ∤ N`.
--
--   The proof applies Tanner's bound to the **original** graph `G`, then uses a fiber-projection bridge lemma to translate expansion back to the quotient level. The ε bound degrades by a factor of `q/(q+1)` where `q = ⌊N/m⌋`.
--
--   Key results:
--
--   - `quotientComparators`: bipartite comparator list from mod-`m` projection
--   - `quotientHalver`: the comparator network on `2 * m` wires (computable)
--   - `konigQuotientHalver`: König-decomposed version (computable, depth ≤ Δ)
--   - `quotientHalver_isEpsilonHalver`: halver property
--
--   See `docs/quotient-halver.md` for the full mathematical argument.
--
--   **Formalization Note** The file was ported from Lean v4.29.0-rc4 to Lean v4.33.1 / Mathlib `0df444a`. The ported text agrees with the upstream file except for small proof repairs needed by the newer toolchain, the removal of the Lean module-system keywords, and the renaming of the upstream structure `Graph` to `HalfEdgeGraph`, which avoids a clash with Mathlib's `Graph`.
-- source:
--   https://github.com/girving/aks/blob/c7fb62ed80a4a610f87f34db0082cadbd7c00c9f/AKS/Halver/Quotient.lean (ported); Seiferas, Sorting networks of logarithmic depth, further simplified, Algorithmica 53 (2009) 374–384; Ajtai, Komlós, Szemerédi, Sorting in c log n parallel steps, Combinatorica 3 (1983) 1–19

import Definitions.Def_GirvingAKS_Halver_FromExpander
import Definitions.Def_GirvingAKS_Graph_Contract
import Definitions.Def_GirvingAKS_Konig_ContractedBipartite

/-! Ported to Lean v4.33.1 / Mathlib 0df444a from `AKS/Halver/Quotient.lean` of
https://github.com/girving/aks (commit c7fb62ed80a4a610f87f34db0082cadbd7c00c9f, Apache-2.0). -/

/-
  # Quotient Halver: Direct Tanner Bound for Non-Integer Quotients

  For a `d`-regular graph `G` on `N` vertices with spectral gap `β`, builds
  an ε-halver on `2 * m` wires for any target `m ≤ N` by projecting through
  `v ↦ v % m`. Unlike equal-fiber contraction (`contractDivisible`), this
  works even when `m ∤ N`.

  The proof applies Tanner's bound to the **original** graph `G`, then uses
  a fiber-projection bridge lemma to translate expansion back to the quotient
  level. The ε bound degrades by a factor of `q/(q+1)` where `q = ⌊N/m⌋`.

  Key results:
  - `quotientComparators`: bipartite comparator list from mod-`m` projection
  - `quotientHalver`: the comparator network on `2 * m` wires (computable)
  - `konigQuotientHalver`: König-decomposed version (computable, depth ≤ Δ)
  - `quotientHalver_isEpsilonHalver`: halver property

  See `docs/quotient-halver.md` for the full mathematical argument.
-/


section


open Finset BigOperators


/-! **Quotient Comparator Construction** -/

/-- The quotient comparator list: for each vertex `v : Fin N` and port `p : Fin d`
    of a `d`-regular graph `G`, compare wire `v % m` (top) with wire
    `m + (G.neighbor v p) % m` (bottom). All comparators are bipartite. -/
def quotientComparators {N d : ℕ} (G : RegularGraph N d)
    (m : ℕ) (hm : 0 < m) (_hmN : m ≤ N) :
    List (Comparator (2 * m)) :=
  (List.finRange N).flatMap fun v =>
    (List.finRange d).map fun p =>
      { i := ⟨v.val % m, by have := Nat.mod_lt v.val hm; omega⟩
        j := ⟨m + (G.neighbor v p).val % m, by have := Nat.mod_lt (G.neighbor v p).val hm; omega⟩
        h := by
          apply Fin.mk_lt_mk.mpr
          have := Nat.mod_lt v.val hm; omega }

lemma quotientComparators_length {N d : ℕ} (G : RegularGraph N d)
    (m : ℕ) (hm : 0 < m) (hmN : m ≤ N) :
    (quotientComparators G m hm hmN).length = N * d := by
  simp only [quotientComparators, List.length_flatMap, List.length_map,
    List.length_finRange, List.map_const', List.sum_replicate, smul_eq_mul]

/-- All quotient comparators are bipartite: top wire < m ≤ bottom wire. -/
lemma quotientComparators_bipartite {N d : ℕ} (G : RegularGraph N d)
    (m : ℕ) (hm : 0 < m) (hmN : m ≤ N)
    (c : Comparator (2 * m)) (hc : c ∈ quotientComparators G m hm hmN) :
    c.i.val < m ∧ m ≤ c.j.val := by
  simp only [quotientComparators] at hc
  rw [List.mem_flatMap] at hc
  obtain ⟨v, _, hc'⟩ := hc
  rw [List.mem_map] at hc'
  obtain ⟨p, _, rfl⟩ := hc'
  exact ⟨Nat.mod_lt _ hm, Nat.le_add_right m _⟩

/-- The quotient halver network on `2 * m` wires. -/
def quotientHalver {N d : ℕ} (G : RegularGraph N d)
    (m : ℕ) (hm : 0 < m) (hmN : m ≤ N) : ComparatorNetwork (2 * m) :=
  ⟨quotientComparators G m hm hmN⟩


/-! **Edge Monotonicity** -/

/-- The specific comparator for `(v, p)` is in `quotientComparators`. -/
lemma mem_quotientComparators {N d : ℕ} (G : RegularGraph N d)
    (m : ℕ) (hm : 0 < m) (hmN : m ≤ N)
    (v : Fin N) (p : Fin d) :
    (⟨⟨v.val % m, by have := Nat.mod_lt v.val hm; omega⟩,
      ⟨m + (G.neighbor v p).val % m, by have := Nat.mod_lt (G.neighbor v p).val hm; omega⟩,
      by apply Fin.mk_lt_mk.mpr; have := Nat.mod_lt v.val hm; omega⟩ : Comparator (2 * m))
      ∈ quotientComparators G m hm hmN := by
  simp only [quotientComparators]
  apply List.mem_flatMap.mpr
  exact ⟨v, List.mem_finRange v, List.mem_map.mpr ⟨p, List.mem_finRange p, rfl⟩⟩


/-! **Fiber Lifting and Projection** -/

/-- Lift a set `S ⊆ Fin m` to its fiber union `S* ⊆ Fin N` via mod-`m`. -/
def liftToFiber {N m : ℕ} (_hm : 0 < m) (_hmN : m ≤ N)
    (S : Finset (Fin m)) : Finset (Fin N) :=
  univ.filter (fun v : Fin N ↦ ⟨v.val % m, Nat.mod_lt _ ‹0 < m›⟩ ∈ S)

/-- `liftToFiber` lower bound: `|S| * ⌊N/m⌋ ≤ |S*|`. -/
theorem liftToFiber_card_lb {N m : ℕ} (hm : 0 < m) (hmN : m ≤ N)
    (S : Finset (Fin m)) :
    S.card * (N / m) ≤ (liftToFiber hm hmN S).card := by
  have h_disj : ∀ u₁ ∈ S, ∀ u₂ ∈ S, u₁ ≠ u₂ →
      Disjoint
        (univ.filter (fun v : Fin N ↦ v.val % m = u₁.val))
        (univ.filter (fun v : Fin N ↦ v.val % m = u₂.val)) := by
    intro u₁ _ u₂ _ hne
    simp only [Finset.disjoint_filter]
    intro v _ h1 h2; exact absurd (by rw [h1] at h2; exact Fin.ext h2) hne
  have h_eq : liftToFiber hm hmN S =
      S.biUnion (fun u ↦ univ.filter (fun v : Fin N ↦ v.val % m = u.val)) := by
    ext v; simp only [liftToFiber, mem_filter, mem_univ, true_and, mem_biUnion]
    constructor
    · intro hv; exact ⟨⟨v.val % m, Nat.mod_lt _ hm⟩, hv, rfl⟩
    · intro ⟨u, hu, hvu⟩
      have : (⟨v.val % m, Nat.mod_lt _ hm⟩ : Fin m) = u := Fin.ext hvu
      rw [this]; exact hu
  calc S.card * (N / m)
      = ∑ _u ∈ S, N / m := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ ∑ u ∈ S, (univ.filter (fun v : Fin N ↦ v.val % m = u.val)).card := by
        apply Finset.sum_le_sum; intro u _
        exact mod_fiber_card_lb hm hmN u
    _ ≤ (liftToFiber hm hmN S).card := by
        rw [h_eq]; exact le_of_eq (Finset.card_biUnion h_disj).symm

/-- `liftToFiber` upper bound: `|S*| ≤ |S| * (⌊N/m⌋ + 1)`. -/
theorem liftToFiber_card_ub {N m : ℕ} (hm : 0 < m) (hmN : m ≤ N)
    (S : Finset (Fin m)) :
    (liftToFiber hm hmN S).card ≤ S.card * (N / m + 1) := by
  have h_eq : liftToFiber hm hmN S =
      S.biUnion (fun u ↦ univ.filter (fun v : Fin N ↦ v.val % m = u.val)) := by
    ext v; simp only [liftToFiber, mem_filter, mem_univ, true_and, mem_biUnion]
    constructor
    · intro hv; exact ⟨⟨v.val % m, Nat.mod_lt _ hm⟩, hv, rfl⟩
    · intro ⟨u, hu, hvu⟩
      have : (⟨v.val % m, Nat.mod_lt _ hm⟩ : Fin m) = u := Fin.ext hvu
      rw [this]; exact hu
  rw [h_eq]
  calc (S.biUnion _).card
      ≤ ∑ u ∈ S, (univ.filter (fun v : Fin N ↦ v.val % m = u.val)).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _u ∈ S, (N / m + 1) := by
        apply Finset.sum_le_sum; intro u _
        exact mod_fiber_card_ub hm u
    _ = S.card * (N / m + 1) := by rw [Finset.sum_const, smul_eq_mul]

/-- `liftToFiber` is nonempty when `S` is nonempty. -/
theorem liftToFiber_nonempty {N m : ℕ} (hm : 0 < m) (hmN : m ≤ N)
    (S : Finset (Fin m)) (hS : 0 < S.card) :
    0 < (liftToFiber hm hmN S).card := by
  have hq : 0 < N / m := Nat.div_pos hmN hm
  calc 0 < S.card * (N / m) := Nat.mul_pos hS hq
    _ ≤ (liftToFiber hm hmN S).card := liftToFiber_card_lb hm hmN S

/-- Membership in `liftToFiber`: `v ∈ S*` iff `v % m ∈ S`. -/
@[simp]
theorem mem_liftToFiber {N m : ℕ} (hm : 0 < m) (hmN : m ≤ N)
    (S : Finset (Fin m)) (v : Fin N) :
    v ∈ liftToFiber hm hmN S ↔ ⟨v.val % m, Nat.mod_lt _ hm⟩ ∈ S := by
  simp [liftToFiber]


/-! **Bridge Lemma: Fiber Projection Bounds Neighborhood** -/

/-- Project a set `T ⊆ Fin N` down to `Fin m` via mod-`m`. -/
def projectMod {N m : ℕ} (hm : 0 < m) (T : Finset (Fin N)) : Finset (Fin m) :=
  T.image (fun v ↦ ⟨v.val % m, Nat.mod_lt _ hm⟩)

/-- Bridge lemma: `|T| ≤ |projectMod(T)| * (⌊N/m⌋ + 1)`.
    Each element of `projectMod(T)` has a fiber of size ≤ `⌊N/m⌋ + 1`,
    so the total preimage has at most `|projectMod(T)| * (⌊N/m⌋ + 1)` elements. -/
theorem projectMod_card_mul_ge {N m : ℕ} (hm : 0 < m)
    (T : Finset (Fin N)) :
    T.card ≤ (projectMod hm T).card * (N / m + 1) := by
  have h_sub : T ⊆ (projectMod hm T).biUnion
      (fun u ↦ univ.filter (fun v : Fin N ↦ v.val % m = u.val)) := by
    intro v hv
    simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨⟨v.val % m, Nat.mod_lt _ hm⟩, Finset.mem_image.mpr ⟨v, hv, rfl⟩, rfl⟩
  calc T.card
      ≤ ((projectMod hm T).biUnion _).card := Finset.card_le_card h_sub
    _ ≤ ∑ u ∈ projectMod hm T, (univ.filter (fun v : Fin N ↦ v.val % m = u.val)).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _u ∈ projectMod hm T, (N / m + 1) := by
        apply Finset.sum_le_sum; intro u _
        exact mod_fiber_card_ub hm u
    _ = (projectMod hm T).card * (N / m + 1) := by rw [Finset.sum_const, smul_eq_mul]


/-! **Quotient Tanner Contradiction** -/

/-- For an upward-opening parabola `A·t² + B·t + C` with `A > 0` and `C ≤ 0`,
    if `f(t₀) > 0` and `s > t₀ > 0`, then `f(s) > 0`.

    Proof: `C ≤ 0` means `f(0) ≤ 0`, so the positive root `r < t₀`. Since the
    parabola opens upward, `f(s) > 0` for all `s > r`. -/
private lemma upward_parabola_pos (A B C s t : ℝ) (hA : 0 < A) (hC : C ≤ 0)
    (ht : 0 < t) (hs_gt : s > t)
    (hgt : A * t ^ 2 + B * t + C > 0) :
    A * s ^ 2 + B * s + C > 0 := by
  have hAtB : A * t + B > 0 := by
    have h1 : t * (A * t + B) > 0 := by nlinarith
    rcases mul_pos_iff.mp h1 with ⟨_, h⟩ | ⟨h, _⟩
    · exact h
    · linarith
  have hAstB : A * (s + t) + B > 0 := by nlinarith
  have h_diff : A * s ^ 2 + B * s + C =
      (A * t ^ 2 + B * t + C) + (s - t) * (A * (s + t) + B) := by ring
  linarith [mul_pos (by linarith : s - t > 0) hAstB]

/-- The algebraic contradiction for the quotient halver.

    The combined Tanner + bridge inequality at the quotient level:
      `s·q²·m ≤ (k-s)·(q+1)²·(s + β²·(m-s))`
    is contradicted when `s > ε·k`, provided that
      `(q+1)²·(ε² - β²·(1-ε)²) > (2q+1)·ε`.

    The `(q+1)²` and `q²` factors come from the fiber projection:
    lifting wrong wires to fibers (×q on LHS) and bounding neighborhoods
    through fiber projection (×(q+1) on RHS), each squared because both
    the Tanner bound and bridge contribute a factor. -/
theorem quotient_tanner_contradiction {ε β : ℝ} {s m k : ℕ} {q : ℕ}
    (hm : 0 < m) (hk : k ≤ m) (hβ_nn : 0 ≤ β) (hβ1 : β < 1)
    (hε_nn : 0 ≤ ε) (hsm : s ≤ m) (hsk : s ≤ k)
    (hq_pos : 0 < q)
    (hε_cond : (↑q + 1) ^ 2 * (ε ^ 2 - β ^ 2 * (1 - ε) ^ 2) > (2 * ↑q + 1) * ε)
    (hs : (s : ℝ) > ε * ↑k)
    (h_tanner : (s : ℝ) * ↑q ^ 2 * ↑m ≤
      (↑k - ↑s) * (↑q + 1) ^ 2 * (↑s + β ^ 2 * (↑m - ↑s))) :
    False := by
  -- Handle k = 0 trivially
  rcases Nat.eq_zero_or_pos k with rfl | hk_pos
  · have hs0 : s = 0 := by omega
    simp [hs0] at hs
  have hsm' : (s : ℝ) ≤ ↑m := by exact_mod_cast hsm
  have hsk' : (s : ℝ) ≤ ↑k := by exact_mod_cast hsk
  have hkm' : (k : ℝ) ≤ ↑m := by exact_mod_cast hk
  have hm' : (0 : ℝ) < ↑m := Nat.cast_pos.mpr hm
  have hk' : (0 : ℝ) < ↑k := Nat.cast_pos.mpr hk_pos
  have hq1 : (0 : ℝ) < ↑q + 1 := by positivity
  -- Rewrite h_tanner as quadratic g(s) ≤ 0:
  -- g(t) = t*q²*m - (k-t)*(q+1)²*(t + β²*(m-t))
  --      = A*t² + B*t + C  where A = (q+1)²*(1-β²), C = -(q+1)²*β²*k*m
  have g_eq : ∀ t : ℝ,
      t * ↑q ^ 2 * ↑m - (↑k - t) * (↑q + 1) ^ 2 * (t + β ^ 2 * (↑m - t)) =
      (↑q + 1) ^ 2 * (1 - β ^ 2) * t ^ 2 +
      (↑q ^ 2 * ↑m + (↑q + 1) ^ 2 * ↑m * β ^ 2 -
        (↑q + 1) ^ 2 * (1 - β ^ 2) * ↑k) * t +
      (-(↑q + 1) ^ 2 * β ^ 2 * ↑k * ↑m) := by intro t; ring
  have hA_pos : 0 < (↑q + 1 : ℝ) ^ 2 * (1 - β ^ 2) := by
    apply mul_pos (sq_pos_of_pos hq1); nlinarith [sq_abs β]
  have hC_le : -(↑q + 1 : ℝ) ^ 2 * β ^ 2 * ↑k * ↑m ≤ 0 := by
    have : (0 : ℝ) ≤ (↑q + 1) ^ 2 * β ^ 2 * ↑k * ↑m := by positivity
    linarith
  -- g(s) ≤ 0 from h_tanner
  have h_gs_le : (↑q + 1) ^ 2 * (1 - β ^ 2) * (↑s : ℝ) ^ 2 +
      (↑q ^ 2 * ↑m + (↑q + 1) ^ 2 * ↑m * β ^ 2 -
        (↑q + 1) ^ 2 * (1 - β ^ 2) * ↑k) * ↑s +
      (-(↑q + 1) ^ 2 * β ^ 2 * ↑k * ↑m) ≤ 0 := by
    have := g_eq (↑s); linarith
  -- g(ε*k) > 0: use g(ε*k) ≥ k*m*D where D = hε_cond expression
  have h_diff : ∀ t : ℝ,
      (↑q + 1) ^ 2 * (1 - β ^ 2) * (ε * ↑k) ^ 2 +
      (↑q ^ 2 * ↑m + (↑q + 1) ^ 2 * ↑m * β ^ 2 -
        (↑q + 1) ^ 2 * (1 - β ^ 2) * ↑k) * (ε * ↑k) +
      (-(↑q + 1) ^ 2 * β ^ 2 * ↑k * ↑m) -
      (↑k * ↑m * ((↑q + 1) ^ 2 * (ε ^ 2 - β ^ 2 * (1 - ε) ^ 2) - (2 * ↑q + 1) * ε)) =
      (↑q + 1) ^ 2 * ε * (1 - β ^ 2) * (1 - ε) * ↑k * (↑m - ↑k) := by
    intro; ring
  have hε1 : ε < 1 := by nlinarith
  have h_surplus_nn : (↑q + 1) ^ 2 * ε * (1 - β ^ 2) * (1 - ε) * ↑k * (↑m - ↑k) ≥ 0 :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) hε_nn)
      (by nlinarith [sq_abs β])) (by linarith)) (Nat.cast_nonneg k)) (by linarith)
  have h_gεk : (↑q + 1) ^ 2 * (1 - β ^ 2) * (ε * ↑k) ^ 2 +
      (↑q ^ 2 * ↑m + (↑q + 1) ^ 2 * ↑m * β ^ 2 -
        (↑q + 1) ^ 2 * (1 - β ^ 2) * ↑k) * (ε * ↑k) +
      (-(↑q + 1) ^ 2 * β ^ 2 * ↑k * ↑m) > 0 := by
    have hD : ↑k * ↑m * ((↑q + 1) ^ 2 * (ε ^ 2 - β ^ 2 * (1 - ε) ^ 2) -
        (2 * ↑q + 1) * ε) > 0 :=
      mul_pos (mul_pos hk' hm') (by linarith)
    linarith [h_diff 0, h_surplus_nn]
  -- ε*k > 0
  have hε_pos : 0 < ε := by
    by_contra h; push_neg at h
    have := le_antisymm h hε_nn; subst this
    simp at hε_cond; nlinarith [sq_nonneg β, sq_nonneg (↑q + 1 : ℝ)]
  have hεk_pos : (0 : ℝ) < ε * ↑k := mul_pos hε_pos hk'
  -- Contradiction via upward parabola
  exact absurd (upward_parabola_pos _ _ _ (↑s) (ε * ↑k) hA_pos hC_le hεk_pos hs h_gεk)
    (not_lt.mpr h_gs_le)


/-! **Halver Property** -/

/-- General initial halved for quotient halvers: any output function with
    permutation-count and quotient edge-monotonicity satisfies the initial
    halver bound. The proof lifts the wrong set to fibers, applies Tanner
    to the original graph, uses the bridge lemma, then contradicts via
    `quotient_tanner_contradiction`. -/
private lemma quotient_epsilon_initial_halved {N d m : ℕ} (G : RegularGraph N d)
    (hm : 0 < m) (hmN : m ≤ N) (hd : 0 < d)
    (ε β : ℝ) (hβ : spectralGap G ≤ β) (hβ_nn : 0 ≤ β) (hβ1 : β < 1)
    (hε_nn : 0 ≤ ε)
    (hε_cond : (↑(N / m) + 1) ^ 2 * (ε ^ 2 - β ^ 2 * (1 - ε) ^ 2) >
      (2 * ↑(N / m) + 1) * ε)
    (w : Fin (2 * m) → Fin (2 * m))
    (h_count : ∀ k : ℕ, k ≤ 2 * m →
      (univ.filter (fun i : Fin (2 * m) ↦ (w i).val < k)).card = k)
    (h_mono : ∀ u : Fin N, ∀ p : Fin d,
      w ⟨u.val % m, by have := Nat.mod_lt u.val hm; omega⟩ ≤
      w ⟨m + (G.neighbor u p).val % m,
        by have := Nat.mod_lt (G.neighbor u p).val hm; omega⟩) :
    EpsilonInitialHalved w ε := by
  show ∀ k : ℕ, k ≤ Fintype.card (Fin (2 * m)) / 2 →
    ((univ.filter (fun pos : Fin (2 * m) ↦
        Fintype.card (Fin (2 * m)) / 2 ≤ rank pos ∧ rank (w pos) < k)).card : ℝ) ≤ ε * k
  simp only [Fintype.card_fin, show 2 * m / 2 = m from Nat.mul_div_cancel_left m (by omega)]
  intro k hk
  simp_rw [rank_fin_val]
  set s := (univ.filter (fun pos : Fin (2 * m) ↦ m ≤ pos.val ∧ (w pos).val < k)).card
  show (s : ℝ) ≤ ε * ↑k
  rcases Nat.eq_zero_or_pos k with rfl | hk_pos
  · simp [show s = 0 from by
      simp only [s, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro pos _; simp]
  -- Wrong bottom wires
  set T : Finset (Fin m) := univ.filter (fun u : Fin m ↦ (w ⟨m + u.val, by omega⟩).val < k)
  have hs_eq : s = T.card := by
    simp only [s, T]
    apply Finset.card_nbij'
      (fun pos ↦ (⟨pos.val - m, by omega⟩ : Fin m))
      (fun u ↦ (⟨m + u.val, by omega⟩ : Fin (2 * m)))
    · intro pos hpos
      simp only [SetLike.mem_coe, Finset.mem_coe, mem_filter, mem_univ, true_and] at hpos ⊢
      have heq : (⟨m + (pos.val - m), (by omega : m + (pos.val - m) < 2 * m)⟩ :
          Fin (2 * m)) = pos := Fin.ext (by dsimp; omega)
      rw [heq]; exact hpos.2
    · intro u hu
      simp only [SetLike.mem_coe, Finset.mem_coe, mem_filter, mem_univ, true_and] at hu ⊢
      exact ⟨by omega, hu⟩
    · intro pos hpos
      simp only [SetLike.mem_coe, Finset.mem_coe, mem_filter, mem_univ, true_and] at hpos
      exact Fin.ext (by dsimp; omega)
    · intro u _; exact Fin.ext (by dsimp; omega)
  by_contra h_contra; push_neg at h_contra
  rw [hs_eq] at h_contra
  have hT_pos : 0 < T.card := by
    rcases Nat.eq_zero_or_pos T.card with h0 | h0
    · simp [h0] at h_contra; linarith [mul_nonneg hε_nn (Nat.cast_nonneg k)]
    · exact h0
  have hsm : T.card ≤ m := Finset.card_filter_le _ _ |>.trans (by simp)
  -- Counting: top_count + T.card = k
  have h_split := card_filter_fin_double (fun i : Fin (2 * m) ↦ (w i).val < k)
  have h_total : (univ.filter (fun i : Fin (2 * m) ↦ (w i).val < k)).card = k :=
    h_count k (by omega)
  set top_count := (univ.filter (fun v : Fin m ↦ (w ⟨v.val, by omega⟩).val < k)).card
  have h_total' : top_count + T.card = k := by rw [← h_split]; exact h_total
  have hTk : T.card ≤ k := by omega
  -- q = N / m
  set q := N / m with hq_def
  have hq_pos : 0 < q := Nat.div_pos hmN hm
  -- Lift T to T* ⊆ Fin N
  set T_star := liftToFiber hm hmN T
  have hT_star_pos : 0 < T_star.card := liftToFiber_nonempty hm hmN T hT_pos
  -- Neighborhood containment: projectMod(N_G(T*)) ⊆ {top wires with w < k}
  have hN_sub : projectMod hm (G.neighborSet T_star) ⊆
      univ.filter (fun u : Fin m ↦ (w ⟨u.val, by omega⟩).val < k) := by
    intro u hu
    simp only [projectMod, mem_image, mem_filter, mem_univ, true_and] at hu ⊢
    obtain ⟨v, hv, hvu⟩ := hu
    simp only [RegularGraph.neighborSet, mem_filter, mem_univ, true_and] at hv
    obtain ⟨p, hp⟩ := hv
    rw [mem_liftToFiber] at hp
    simp only [T, mem_filter, mem_univ, true_and] at hp
    have h_mono_vp := h_mono v p
    have hu_eq : u.val = v.val % m := (congr_arg Fin.val hvu).symm
    have : w ⟨u.val, by omega⟩ ≤ w ⟨m + (G.neighbor v p).val % m,
        by have := Nat.mod_lt (G.neighbor v p).val hm; omega⟩ := by
      have : (⟨u.val, by omega⟩ : Fin (2 * m)) = ⟨v.val % m, by
          have := Nat.mod_lt v.val hm; omega⟩ := Fin.ext hu_eq
      rw [this]; exact h_mono_vp
    exact lt_of_le_of_lt (Fin.le_def.mp this) hp
  have hN_card_bridge : ((G.neighborSet T_star).card : ℝ) ≤
      (↑k - ↑T.card) * (↑q + 1) := by
    have h1 : (projectMod hm (G.neighborSet T_star)).card ≤ top_count :=
      Finset.card_le_card hN_sub
    have h2 := projectMod_card_mul_ge hm (G.neighborSet T_star)
    have : (G.neighborSet T_star).card ≤ (k - T.card) * (q + 1) := by
      calc (G.neighborSet T_star).card
          ≤ (projectMod hm (G.neighborSet T_star)).card * (N / m + 1) := h2
        _ ≤ (k - T.card) * (q + 1) := Nat.mul_le_mul (by omega) (by omega)
    exact_mod_cast this
  -- Tanner bound on G at T_star
  have hN_pos : 0 < N := by omega
  have h_tanner := tanner_bound G hd hN_pos β hβ hβ_nn T_star hT_star_pos
  -- Combined inequality: T.card * q² * m ≤ (k - T.card) * (q+1)² * (T.card + β²*(m-T.card))
  have h_combined : (T.card : ℝ) * ↑q ^ 2 * ↑m ≤
      (↑k - ↑T.card) * (↑q + 1) ^ 2 *
        (↑T.card + β ^ 2 * (↑m - ↑T.card)) := by
    have hTsm : (T.card : ℝ) ≤ ↑m := by exact_mod_cast hsm
    have hTsk : (T.card : ℝ) ≤ ↑k := by exact_mod_cast hTk
    have hT_star_lb' : (T.card : ℝ) * ↑q ≤ ↑T_star.card := by
      exact_mod_cast liftToFiber_card_lb hm hmN T
    have hT_star_ub' : (T_star.card : ℝ) ≤ ↑T.card * (↑q + 1) := by
      exact_mod_cast liftToFiber_card_ub hm hmN T
    have hqm_le : ↑q * ↑m ≤ (N : ℝ) := by exact_mod_cast Nat.div_mul_le_self N m
    have hN_lt : (N : ℝ) < (↑q + 1) * ↑m := by
      have : N < (q + 1) * m :=
        calc N < N / m * m + m := Nat.lt_div_mul_add hm
          _ = (N / m + 1) * m := by ring
      exact_mod_cast this
    have hT_star_le_N : (T_star.card : ℝ) ≤ ↑N := by
      exact_mod_cast Finset.card_filter_le _ _ |>.trans (by simp)
    have hX_nn : 0 ≤ ↑T_star.card + β ^ 2 * (↑N - ↑T_star.card) := by
      nlinarith [sq_nonneg β]
    -- Step 1: T.card*q²*m ≤ T_star.card*N
    have step1 : (T.card : ℝ) * ↑q ^ 2 * ↑m ≤ ↑T_star.card * ↑N := by
      have : (T.card : ℝ) * ↑q ^ 2 * ↑m = (↑T.card * ↑q) * (↑q * ↑m) := by ring
      rw [this]; exact mul_le_mul hT_star_lb' hqm_le (by positivity) (by positivity)
    -- Step 2: Tanner bound
    -- Step 3: |N_G|*X ≤ (k-s)*(q+1)*X
    have step3 : ↑(G.neighborSet T_star).card *
        (↑T_star.card + β ^ 2 * (↑N - ↑T_star.card)) ≤
        (↑k - ↑T.card) * (↑q + 1) *
        (↑T_star.card + β ^ 2 * (↑N - ↑T_star.card)) :=
      mul_le_mul_of_nonneg_right hN_card_bridge hX_nn
    -- Step 4: X ≤ (q+1)*(s+β²*(m-s))
    have step4 : ↑T_star.card + β ^ 2 * (↑N - ↑T_star.card) ≤
        (↑q + 1) * (↑T.card + β ^ 2 * (↑m - ↑T.card)) := by
      have h1 : (1 - β ^ 2) * ↑T_star.card ≤ (1 - β ^ 2) * (↑T.card * (↑q + 1)) :=
        mul_le_mul_of_nonneg_left hT_star_ub' (by nlinarith [sq_abs β])
      have h2 : β ^ 2 * ↑N ≤ β ^ 2 * ((↑q + 1) * ↑m) :=
        mul_le_mul_of_nonneg_left (le_of_lt hN_lt) (sq_nonneg β)
      have lhs : ↑T_star.card + β ^ 2 * (↑N - ↑T_star.card) =
          (1 - β ^ 2) * ↑T_star.card + β ^ 2 * ↑N := by ring
      have rhs : (↑q + 1) * (↑T.card + β ^ 2 * (↑m - ↑T.card)) =
          (1 - β ^ 2) * (↑T.card * (↑q + 1)) + β ^ 2 * ((↑q + 1) * ↑m) := by ring
      rw [lhs, rhs]; exact add_le_add h1 h2
    calc (T.card : ℝ) * ↑q ^ 2 * ↑m
        ≤ ↑T_star.card * ↑N := step1
      _ ≤ ↑(G.neighborSet T_star).card *
          (↑T_star.card + β ^ 2 * (↑N - ↑T_star.card)) := h_tanner
      _ ≤ (↑k - ↑T.card) * (↑q + 1) *
          (↑T_star.card + β ^ 2 * (↑N - ↑T_star.card)) := step3
      _ ≤ (↑k - ↑T.card) * (↑q + 1) *
          ((↑q + 1) * (↑T.card + β ^ 2 * (↑m - ↑T.card))) :=
        mul_le_mul_of_nonneg_left step4
          (mul_nonneg (sub_nonneg.mpr (by exact_mod_cast hTk))
            (by positivity))
      _ = (↑k - ↑T.card) * (↑q + 1) ^ 2 *
          (↑T.card + β ^ 2 * (↑m - ↑T.card)) := by ring
  exact quotient_tanner_contradiction hm hk hβ_nn hβ1 hε_nn hsm hTk hq_pos
    hε_cond h_contra h_combined

/-- General final halved for quotient halvers: dual of initial halved via OrderDual. -/
private lemma quotient_epsilon_final_halved {N d m : ℕ} (G : RegularGraph N d)
    (hm : 0 < m) (hmN : m ≤ N) (hd : 0 < d)
    (ε β : ℝ) (hβ : spectralGap G ≤ β) (hβ_nn : 0 ≤ β) (hβ1 : β < 1)
    (hε_nn : 0 ≤ ε)
    (hε_cond : (↑(N / m) + 1) ^ 2 * (ε ^ 2 - β ^ 2 * (1 - ε) ^ 2) >
      (2 * ↑(N / m) + 1) * ε)
    (w : Fin (2 * m) → Fin (2 * m))
    (h_count : ∀ k : ℕ, k ≤ 2 * m →
      (univ.filter (fun i : Fin (2 * m) ↦ (w i).val < k)).card = k)
    (h_mono : ∀ u : Fin N, ∀ p : Fin d,
      w ⟨u.val % m, by have := Nat.mod_lt u.val hm; omega⟩ ≤
      w ⟨m + (G.neighbor u p).val % m,
        by have := Nat.mod_lt (G.neighbor u p).val hm; omega⟩) :
    EpsilonFinalHalved w ε := by
  -- Follow the pattern of general_epsilon_final_halved
  unfold EpsilonFinalHalved
  show ∀ k : ℕ, k ≤ Fintype.card (Fin (2 * m))ᵒᵈ / 2 →
    ((univ.filter (fun pos : (Fin (2 * m))ᵒᵈ ↦
        Fintype.card (Fin (2 * m))ᵒᵈ / 2 ≤ @rank (Fin (2 * m))ᵒᵈ _ _ pos ∧
        @rank (Fin (2 * m))ᵒᵈ _ _ (w pos) < k)).card : ℝ) ≤ ε * k
  simp only [Fintype.card_fin, Fintype.card_orderDual,
    show 2 * m / 2 = m from Nat.mul_div_cancel_left m (by omega)]
  intro k hk
  simp_rw [rank_fin_od, rank_fin_od_fin]
  -- Convert OrderDual filter to Fin filter via suffices (rank_fin_od simplifies
  -- away OrderDual.ofDual, so we bridge by introducing a fresh variable for the card)
  suffices h : ∀ s_val : ℕ,
      s_val = (univ.filter (fun pos : Fin (2 * m) ↦
        pos.val < m ∧ 2 * m - k ≤ (w pos).val)).card →
      (s_val : ℝ) ≤ ε * ↑k by
    apply h
    apply Finset.card_nbij' (fun x => OrderDual.ofDual x) (fun x => OrderDual.toDual x)
    · intro x hx; simp only [SetLike.mem_coe, Finset.mem_coe, mem_filter, mem_univ, true_and] at hx ⊢
      obtain ⟨h1, h2⟩ := hx
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
  show (s : ℝ) ≤ ε * ↑k
  rcases Nat.eq_zero_or_pos k with rfl | hk_pos
  · simp [show s = 0 from by
      simp only [s, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro pos _; simp]
  -- Wrong top wires (positions in [0,m) with large output)
  set T : Finset (Fin m) := univ.filter (fun v : Fin m ↦
    2 * m - k ≤ (w ⟨v.val, by omega⟩).val)
  have hs_eq : s = T.card := by
    show (univ.filter (fun pos : Fin (2 * m) ↦
      pos.val < m ∧ 2 * m - k ≤ (w pos).val)).card = T.card
    rw [← Finset.filter_filter]
    exact card_filter_top_half (fun i : Fin (2 * m) ↦ 2 * m - k ≤ (w i).val)
  by_contra h_contra; push_neg at h_contra
  rw [hs_eq] at h_contra
  have hT_pos : 0 < T.card := by
    rcases Nat.eq_zero_or_pos T.card with h0 | h0
    · simp [h0] at h_contra; linarith [mul_nonneg hε_nn (Nat.cast_nonneg k)]
    · exact h0
  have hsm : T.card ≤ m := Finset.card_filter_le _ _ |>.trans (by simp)
  -- Neighborhood containment (reverse direction) from edge monotonicity
  have hN_sub : G.neighborSet (liftToFiber hm hmN T) ⊆
      univ.filter (fun v : Fin N ↦
        2 * m - k ≤ (w ⟨m + v.val % m, by have := Nat.mod_lt v.val hm; omega⟩).val) := by
    intro v hv
    simp only [RegularGraph.neighborSet, mem_filter, mem_univ, true_and] at hv ⊢
    obtain ⟨p, hp⟩ := hv
    rw [mem_liftToFiber] at hp
    simp only [T, mem_filter, mem_univ, true_and] at hp
    -- G.neighbor v p is in fiber of some u with w(u) ≥ 2m-k
    -- By symmetry: v has neighbor G.neighbor v p. Using reversePort:
    -- w[(G.neighbor v p)%m] ≤ w[m + v%m] by reverse edge monotonicity
    have h_rev := h_mono (G.neighbor v p) (G.reversePort v p)
    simp only [G.neighbor_reversePort] at h_rev
    exact le_trans hp (Fin.le_def.mp h_rev)
  -- project down: projectMod of the neighborhood
  have hN_sub_bot : projectMod hm (G.neighborSet (liftToFiber hm hmN T)) ⊆
      univ.filter (fun u : Fin m ↦ 2 * m - k ≤ (w ⟨m + u.val, by omega⟩).val) := by
    intro u hu
    simp only [projectMod, mem_image] at hu
    obtain ⟨v, hv, hvu⟩ := hu
    simp only [mem_filter, mem_univ, true_and]
    have hu_eq : u.val = v.val % m := by
      simp only [Fin.ext_iff] at hvu; exact hvu.symm
    have : (⟨m + u.val, by omega⟩ : Fin (2 * m)) =
        ⟨m + v.val % m, by have := Nat.mod_lt v.val hm; omega⟩ := Fin.ext (by dsimp; omega)
    rw [this]; exact (mem_filter.mp (hN_sub hv)).2
  -- Counting complement
  have h_total : (univ.filter (fun i : Fin (2 * m) ↦ 2 * m - k ≤ (w i).val)).card = k := by
    have hcomp := card_filter_add_card_filter_not
      (fun i : Fin (2 * m) ↦ (w i).val < 2 * m - k) (s := univ)
    simp only [card_univ, Fintype.card_fin] at hcomp
    have htot := h_count (2 * m - k) (by omega)
    have : (univ.filter (fun i : Fin (2 * m) ↦ ¬(w i).val < 2 * m - k)).card = k := by omega
    convert this using 1; congr 1; ext i; simp only [not_lt]
  have h_split := card_filter_fin_double (fun i : Fin (2 * m) ↦ 2 * m - k ≤ (w i).val)
  set bottom_count := (univ.filter (fun u : Fin m ↦
    2 * m - k ≤ (w ⟨m + u.val, by omega⟩).val)).card
  have h_total' : T.card + bottom_count = k := by rw [← h_split]; exact h_total
  have hTk : T.card ≤ k := by omega
  -- Bridge
  set q := N / m
  have hq_pos : 0 < q := Nat.div_pos hmN hm
  set T_star := liftToFiber hm hmN T
  have hT_star_pos : 0 < T_star.card := liftToFiber_nonempty hm hmN T hT_pos
  have hN_card_bridge : ((G.neighborSet T_star).card : ℝ) ≤
      (↑k - ↑T.card) * (↑q + 1) := by
    have h1 : (projectMod hm (G.neighborSet T_star)).card ≤ bottom_count :=
      Finset.card_le_card hN_sub_bot
    have h2 := projectMod_card_mul_ge hm (G.neighborSet T_star)
    have : (G.neighborSet T_star).card ≤ (k - T.card) * (q + 1) :=
      calc (G.neighborSet T_star).card
          ≤ (projectMod hm (G.neighborSet T_star)).card * (N / m + 1) := h2
        _ ≤ (k - T.card) * (q + 1) := Nat.mul_le_mul (by omega) (by omega)
    exact_mod_cast this
  -- Tanner + combined inequality (same structure as initial case)
  have hN_pos : 0 < N := by omega
  have h_tanner := tanner_bound G hd hN_pos β hβ hβ_nn T_star hT_star_pos
  have h_combined : (T.card : ℝ) * ↑q ^ 2 * ↑m ≤
      (↑k - ↑T.card) * (↑q + 1) ^ 2 *
        (↑T.card + β ^ 2 * (↑m - ↑T.card)) := by
    have hTsm : (T.card : ℝ) ≤ ↑m := by exact_mod_cast hsm
    have hT_star_lb' : (T.card : ℝ) * ↑q ≤ ↑T_star.card := by
      exact_mod_cast liftToFiber_card_lb hm hmN T
    have hT_star_ub' : (T_star.card : ℝ) ≤ ↑T.card * (↑q + 1) := by
      exact_mod_cast liftToFiber_card_ub hm hmN T
    have hqm_le : ↑q * ↑m ≤ (N : ℝ) := by exact_mod_cast Nat.div_mul_le_self N m
    have hN_lt : (N : ℝ) < (↑q + 1) * ↑m := by
      have : N < (q + 1) * m :=
        calc N < N / m * m + m := Nat.lt_div_mul_add hm
          _ = (N / m + 1) * m := by ring
      exact_mod_cast this
    have hT_star_le_N : (T_star.card : ℝ) ≤ ↑N := by
      exact_mod_cast Finset.card_filter_le _ _ |>.trans (by simp)
    have hX_nn : 0 ≤ ↑T_star.card + β ^ 2 * (↑N - ↑T_star.card) := by
      nlinarith [sq_nonneg β]
    have step1 : (T.card : ℝ) * ↑q ^ 2 * ↑m ≤ ↑T_star.card * ↑N := by
      have : (T.card : ℝ) * ↑q ^ 2 * ↑m = (↑T.card * ↑q) * (↑q * ↑m) := by ring
      rw [this]; exact mul_le_mul hT_star_lb' hqm_le (by positivity) (by positivity)
    have step3 : ↑(G.neighborSet T_star).card *
        (↑T_star.card + β ^ 2 * (↑N - ↑T_star.card)) ≤
        (↑k - ↑T.card) * (↑q + 1) *
        (↑T_star.card + β ^ 2 * (↑N - ↑T_star.card)) :=
      mul_le_mul_of_nonneg_right hN_card_bridge hX_nn
    have step4 : ↑T_star.card + β ^ 2 * (↑N - ↑T_star.card) ≤
        (↑q + 1) * (↑T.card + β ^ 2 * (↑m - ↑T.card)) := by
      have h1 : (1 - β ^ 2) * ↑T_star.card ≤ (1 - β ^ 2) * (↑T.card * (↑q + 1)) :=
        mul_le_mul_of_nonneg_left hT_star_ub' (by nlinarith [sq_abs β])
      have h2 : β ^ 2 * ↑N ≤ β ^ 2 * ((↑q + 1) * ↑m) :=
        mul_le_mul_of_nonneg_left (le_of_lt hN_lt) (sq_nonneg β)
      have lhs : ↑T_star.card + β ^ 2 * (↑N - ↑T_star.card) =
          (1 - β ^ 2) * ↑T_star.card + β ^ 2 * ↑N := by ring
      have rhs : (↑q + 1) * (↑T.card + β ^ 2 * (↑m - ↑T.card)) =
          (1 - β ^ 2) * (↑T.card * (↑q + 1)) + β ^ 2 * ((↑q + 1) * ↑m) := by ring
      rw [lhs, rhs]; exact add_le_add h1 h2
    calc (T.card : ℝ) * ↑q ^ 2 * ↑m
        ≤ ↑T_star.card * ↑N := step1
      _ ≤ ↑(G.neighborSet T_star).card *
          (↑T_star.card + β ^ 2 * (↑N - ↑T_star.card)) := h_tanner
      _ ≤ (↑k - ↑T.card) * (↑q + 1) *
          (↑T_star.card + β ^ 2 * (↑N - ↑T_star.card)) := step3
      _ ≤ (↑k - ↑T.card) * (↑q + 1) *
          ((↑q + 1) * (↑T.card + β ^ 2 * (↑m - ↑T.card))) :=
        mul_le_mul_of_nonneg_left step4
          (mul_nonneg (sub_nonneg.mpr (by exact_mod_cast hTk))
            (by positivity))
      _ = (↑k - ↑T.card) * (↑q + 1) ^ 2 *
          (↑T.card + β ^ 2 * (↑m - ↑T.card)) := by ring
  exact quotient_tanner_contradiction hm hk hβ_nn hβ1 hε_nn hsm hTk hq_pos
    hε_cond h_contra h_combined

/-- The quotient halver is an ε-halver. The proof chains edge monotonicity
    (from bipartite comparators) through the quotient Tanner argument. -/
theorem quotientHalver_isEpsilonHalver {N d m : ℕ} (G : RegularGraph N d)
    (hm : 0 < m) (hmN : m ≤ N) (hd : 0 < d)
    (ε β : ℝ) (hβ : spectralGap G ≤ β) (hβ_nn : 0 ≤ β) (hβ1 : β < 1)
    (hε_nn : 0 ≤ ε)
    (hε_cond : (↑(N / m) + 1) ^ 2 * (ε ^ 2 - β ^ 2 * (1 - ε) ^ 2) >
      (2 * ↑(N / m) + 1) * ε) :
    IsEpsilonHalver (quotientHalver G m hm hmN) ε := by
  intro v
  set w := (quotientHalver G m hm hmN).exec (↑v)
  have h_mono : ∀ u : Fin N, ∀ p : Fin d,
      w ⟨u.val % m, by have := Nat.mod_lt u.val hm; omega⟩ ≤
      w ⟨m + (G.neighbor u p).val % m,
        by have := Nat.mod_lt (G.neighbor u p).val hm; omega⟩ :=
    fun u p ↦ foldl_member_order (quotientComparators G m hm hmN)
      _ (mem_quotientComparators G m hm hmN u p)
      (quotientComparators_bipartite G m hm hmN) (↑v)
  have h_count : ∀ k : ℕ, k ≤ 2 * m →
      (univ.filter (fun i : Fin (2 * m) ↦ (w i).val < k)).card = k :=
    fun k hk ↦ exec_perm_card_lt (quotientHalver G m hm hmN) v k hk
  exact ⟨quotient_epsilon_initial_halved G hm hmN hd ε β hβ hβ_nn hβ1 hε_nn
      hε_cond w h_count h_mono,
    quotient_epsilon_final_halved G hm hmN hd ε β hβ hβ_nn hβ1 hε_nn
      hε_cond w h_count h_mono⟩


/-! **Depth Bound (Crude)** -/

/-- Crude depth bound: the quotient halver has at most `N * d` comparators,
    hence depth ≤ `N * d`. -/
theorem quotientHalver_depth_le_crude {N d m : ℕ} (G : RegularGraph N d)
    (hm : 0 < m) (hmN : m ≤ N) :
    (quotientHalver G m hm hmN).depth ≤ N * d := by
  calc (quotientHalver G m hm hmN).depth
      ≤ (quotientHalver G m hm hmN).size := depth_le_size _
    _ = (quotientComparators G m hm hmN).length := rfl
    _ = N * d := quotientComparators_length G m hm hmN


/-! **König Quotient Halver (Depth-Optimal)** -/

/-- A König matching layer for a `RegBipartite`: for each top vertex `v`,
    compare wire `v` with wire `m + B.edges v (portOf v)`. -/
def konigLayerBip {m Δ : ℕ} (B : RegBipartite m Δ)
    (portOf : Fin m → Fin Δ) : List (Comparator (2 * m)) :=
  (List.finRange m).map fun v ↦
    ⟨⟨v.val, by omega⟩, ⟨m + (B.edges v (portOf v)).val, by omega⟩,
     by apply Fin.mk_lt_mk.mpr; omega⟩

/-- A König matching layer is parallel: no two comparators share a wire.
    Uses injectivity of the matching's bottom assignment. -/
lemma konigLayerBip_isParallel {m Δ : ℕ} (B : RegBipartite m Δ)
    (portOf : Fin m → Fin Δ)
    (h_inj : Function.Injective (fun v ↦ B.edges v (portOf v))) :
    IsParallelLayer (konigLayerBip B portOf) := by
  simp only [konigLayerBip, IsParallelLayer, List.pairwise_map]
  apply List.Pairwise.imp _ (List.nodup_finRange m)
  intro v₁ v₂ hne
  unfold Comparator.overlaps; push_neg
  have h_bot_ne : (B.edges v₁ (portOf v₁)).val ≠ (B.edges v₂ (portOf v₂)).val :=
    fun h ↦ hne (h_inj (Fin.ext h))
  exact ⟨by simp [Fin.ext_iff]; exact Fin.val_ne_of_ne hne,
         by simp [Fin.ext_iff]; omega,
         by simp [Fin.ext_iff]; omega,
         by simp [Fin.ext_iff]; omega⟩

/-- König-decomposed quotient halver: uses König edge coloring of the
    contracted mod-`m` bipartite graph for depth ≤ `d * (N / m + 1)`.

    Each vertex `v : Fin m` has a fiber of size ≤ `⌊N/m⌋ + 1`, so the
    contracted bipartite graph has `Δ = d * (⌊N/m⌋ + 1)` ports per vertex.
    We build a computable `RegBipartite` via `contractedBipartite`, then
    decompose into parallel matching layers via König's edge coloring. -/
def konigQuotientHalver {N d : ℕ} (G : RegularGraph N d)
    (m : ℕ) (hm : 0 < m) (hd : 0 < d) :
    ComparatorNetwork (2 * m) :=
  let s : Fin N → Fin m := fun v ↦ ⟨v.val % m, Nat.mod_lt _ hm⟩
  let Δ := d * (N / m + 1)
  have hΔ : 0 < Δ := Nat.mul_pos hd (Nat.succ_pos _)
  have h_ub : ∀ v : Fin m, (fiberSorted s v).length * d ≤ Δ := by
    intro v; rw [fiberSorted_length]
    have : (univ.filter (fun u : Fin N ↦ s u = v)) =
        (univ.filter (fun u : Fin N ↦ u.val % m = v.val)) := by
      ext u; simp [s, Fin.ext_iff]
    rw [this]
    calc (univ.filter (fun u : Fin N ↦ u.val % m = v.val)).card * d
        ≤ (N / m + 1) * d := Nat.mul_le_mul_right d (mod_fiber_card_ub hm v)
      _ = d * (N / m + 1) := Nat.mul_comm _ _
  let B := contractedBipartite G s Δ h_ub
  let matchings := B.konigMatchings hΔ
  ⟨((List.finRange Δ).map fun k ↦
    konigLayerBip B (fun v ↦ (matchings k).portOf v)).flatten⟩

/-- All comparators in the König quotient halver are bipartite. -/
theorem konigQuotientHalver_bipartite {N d : ℕ} (G : RegularGraph N d)
    (m : ℕ) (hm : 0 < m) (hd : 0 < d)
    (c : Comparator (2 * m)) (hc : c ∈ (konigQuotientHalver G m hm hd).comparators) :
    c.i.val < m ∧ m ≤ c.j.val := by
  unfold konigQuotientHalver at hc
  simp only [List.mem_flatten, List.mem_map, List.mem_finRange, true_and] at hc
  obtain ⟨_, ⟨_, rfl⟩, hc'⟩ := hc
  simp only [konigLayerBip, List.mem_map, List.mem_finRange, true_and] at hc'
  obtain ⟨v, rfl⟩ := hc'
  exact ⟨v.isLt, Nat.le_add_right m _⟩

/-- The König quotient halver is an ε-halver.
    The proof uses the same quotient-Tanner argument as `quotientHalver`:
    Tanner's bound on the original graph `G`, the bridge lemma for fiber
    projection, plus the fact that all quotient edges appear as comparators
    (via `contractedBipartite_covers`). Self-loop padding comparators can
    only help. -/
theorem konigQuotientHalver_isEpsilonHalver {N d m : ℕ} (G : RegularGraph N d)
    (hm : 0 < m) (hmN : m ≤ N) (hd : 0 < d)
    (ε β : ℝ) (hβ : spectralGap G ≤ β) (hβ_nn : 0 ≤ β) (hβ1 : β < 1)
    (hε_nn : 0 ≤ ε)
    (hε_cond : (↑(N / m) + 1) ^ 2 * (ε ^ 2 - β ^ 2 * (1 - ε) ^ 2) >
      (2 * ↑(N / m) + 1) * ε) :
    IsEpsilonHalver (konigQuotientHalver G m hm hd) ε := by
  intro v
  set w := (konigQuotientHalver G m hm hd).exec (↑v)
  -- Internal definitions matching konigQuotientHalver
  let s : Fin N → Fin m := fun v ↦ ⟨v.val % m, Nat.mod_lt _ hm⟩
  set Δ := d * (N / m + 1)
  have hΔ : 0 < Δ := Nat.mul_pos hd (Nat.succ_pos _)
  have h_ub : ∀ v : Fin m, (fiberSorted s v).length * d ≤ Δ := by
    intro v; rw [fiberSorted_length]
    have : (univ.filter (fun u : Fin N ↦ s u = v)) =
        (univ.filter (fun u : Fin N ↦ u.val % m = v.val)) := by
      ext u; simp [s, Fin.ext_iff]
    rw [this]
    calc (univ.filter (fun u : Fin N ↦ u.val % m = v.val)).card * d
        ≤ (N / m + 1) * d := Nat.mul_le_mul_right d (mod_fiber_card_ub hm v)
      _ = d * (N / m + 1) := Nat.mul_comm _ _
  let B := contractedBipartite G s Δ h_ub
  let matchings := B.konigMatchings hΔ
  -- Edge monotonicity: for each (u, p), w[u%m] ≤ w[m + (G.neighbor u p)%m]
  have h_mono : ∀ u : Fin N, ∀ p : Fin d,
      w ⟨u.val % m, by have := Nat.mod_lt u.val hm; omega⟩ ≤
      w ⟨m + (G.neighbor u p).val % m,
        by have := Nat.mod_lt (G.neighbor u p).val hm; omega⟩ := by
    intro u p
    set su : Fin m := s u
    -- contractedBipartite_covers gives port q with B.edges (s u) q = s (G.neighbor u p)
    obtain ⟨q, hq⟩ := contractedBipartite_covers G s Δ h_ub u p
    -- konigMatchings_bijective gives matching k with portOf(su) = q
    obtain ⟨k, hk⟩ := (B.konigMatchings_bijective hΔ su).2 q
    dsimp only at hk; subst hk
    -- hq : B.edges su ((matchings k).portOf su) = s (G.neighbor u p)
    have h_edges_eq : (B.edges su ((matchings k).portOf su)).val =
        (G.neighbor u p).val % m := congr_arg Fin.val hq
    -- The comparator at su in layer k is in the network
    have hmem : (⟨⟨su.val, by omega⟩,
        ⟨m + (B.edges su ((matchings k).portOf su)).val, by omega⟩,
        by apply Fin.mk_lt_mk.mpr; omega⟩ : Comparator (2 * m)) ∈
        (konigQuotientHalver G m hm hd).comparators := by
      unfold konigQuotientHalver
      exact List.mem_flatten.mpr
        ⟨_, List.mem_map.mpr ⟨k, List.mem_finRange k, rfl⟩,
         List.mem_map.mpr ⟨su, List.mem_finRange su, rfl⟩⟩
    -- foldl_member_order gives: w[su] ≤ w[m + B.edges...]
    -- Chain with Fin equality from h_edges_eq to get the goal
    exact (foldl_member_order _ _ hmem
      (konigQuotientHalver_bipartite G m hm hd) (↑v)).trans
      (le_of_eq (congrArg w (Fin.ext (congrArg (m + ·) h_edges_eq))))
  -- Count preservation
  have h_count := fun k hk ↦ exec_perm_card_lt (konigQuotientHalver G m hm hd) v k hk
  exact ⟨quotient_epsilon_initial_halved G hm hmN hd ε β hβ hβ_nn hβ1 hε_nn
      hε_cond w h_count h_mono,
    quotient_epsilon_final_halved G hm hmN hd ε β hβ hβ_nn hβ1 hε_nn
      hε_cond w h_count h_mono⟩

/-- Depth bound for the König quotient halver: depth ≤ `d * (N / m + 1)`.
    The contracted mod-`m` graph has max degree ≤ `d * (⌊N/m⌋ + 1)`, so
    König's edge coloring gives that many parallel layers. -/
theorem konigQuotientHalver_depth_le {N d : ℕ} (G : RegularGraph N d)
    (m : ℕ) (hm : 0 < m) (hd : 0 < d) :
    (konigQuotientHalver G m hm hd).depth ≤ d * (N / m + 1) := by
  set Δ := d * (N / m + 1) with hΔ_def
  have hΔ : 0 < Δ := Nat.mul_pos hd (Nat.succ_pos _)
  let s : Fin N → Fin m := fun v ↦ ⟨v.val % m, Nat.mod_lt _ hm⟩
  have h_ub : ∀ v : Fin m, (fiberSorted s v).length * d ≤ Δ := by
    intro v; rw [fiberSorted_length]
    have : (univ.filter (fun u : Fin N ↦ s u = v)) =
        (univ.filter (fun u : Fin N ↦ u.val % m = v.val)) := by
      ext u; simp [s, Fin.ext_iff]
    rw [this]
    calc (univ.filter (fun u : Fin N ↦ u.val % m = v.val)).card * d
        ≤ (N / m + 1) * d := Nat.mul_le_mul_right d (mod_fiber_card_ub hm v)
      _ = d * (N / m + 1) := Nat.mul_comm _ _
  let B := contractedBipartite G s Δ h_ub
  let matchings := B.konigMatchings hΔ
  let layers := (List.finRange Δ).map fun k ↦
    konigLayerBip B (fun v ↦ (matchings k).portOf v)
  have hdecomp : IsParallelDecomposition (konigQuotientHalver G m hm hd) layers :=
    ⟨fun layer hl ↦ by
      simp only [layers, List.mem_map, List.mem_finRange, true_and] at hl
      obtain ⟨k, rfl⟩ := hl
      exact konigLayerBip_isParallel B _ (matchings k).injective,
     by unfold konigQuotientHalver; rfl⟩
  calc (konigQuotientHalver G m hm hd).depth
      ≤ layers.length := depth_le_of_decomposition _ layers hdecomp
    _ = Δ := by simp [layers, List.length_map, List.length_finRange]

end


