-- Prove2me | Definitions.Def_GirvingAKS_Halver_General
-- name    : GirvingAKS_Halver_General
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-22T18:43:40.607237+00:00
-- url     : https://prove2.me/theorems/7f1b1690-458e-4bd2-9700-410f293f7492
-- title:
--   AKS sorting networks (Seiferas port) — General Halver for Arbitrary Sizes
-- statement:
--   Part of a port of the Lean development https://github.com/girving/aks (commit `c7fb62e`), which proves the Ajtai–Komlós–Szemerédi theorem: there are sorting networks of depth $O(\log n)$ and size $O(n\log n)$, following Seiferas's simplified separator-based construction (J. Seiferas, *Sorting networks of logarithmic depth, further simplified*, Algorithmica 53 (2009)). This definition bundle is the module `AKS/Halver/General.lean`; it contains the definitions of that module together with their supporting lemmas, so that later bundles can import them.
--
--   **Contents.** Builds a halver network for any target size `m ≥ 1` via:
--
--   1. Pick `n = max(3, √(Q₀·m) + 1)` so that `mgg n` has `n² ≥ m` vertices
--   2. Apply iterated graph squaring to shrink spectral gap below `ε`
--   3. Use the König quotient halver (`konigQuotientHalver`) to project to `m` wires
--
--   The MGG graph `mgg n` is 8-regular on `n²` vertices with spectral gap ≤ `5√2/8 < 89/100`. The side length `n` is chosen so that `n²/m ≥ Q₀`, which (via `sufficient_epsCond`) ensures the algebraic condition `hε_cond` holds.
--
--   Key results:
--
--   - `mggHalverNet`: halver at `2 * m` wires for any `m ≥ 1`
--   - `mggHalverNet_isEpsilonHalver`: the halver property (proved)
--   - `mggHalverNet_depth_le`: m-independent depth bound (proved)
--   - `halvers`: concrete entry point, fully proved
--
--   **Formalization Note** The file was ported from Lean v4.29.0-rc4 to Lean v4.33.1 / Mathlib `0df444a`. The ported text agrees with the upstream file except for small proof repairs needed by the newer toolchain, the removal of the Lean module-system keywords, and the renaming of the upstream structure `Graph` to `HalfEdgeGraph`, which avoids a clash with Mathlib's `Graph`.
-- source:
--   https://github.com/girving/aks/blob/c7fb62ed80a4a610f87f34db0082cadbd7c00c9f/AKS/Halver/General.lean (ported); Seiferas, Sorting networks of logarithmic depth, further simplified, Algorithmica 53 (2009) 374–384; Ajtai, Komlós, Szemerédi, Sorting in c log n parallel steps, Combinatorica 3 (1983) 1–19

import Definitions.Def_GirvingAKS_Halver_Quotient
import Definitions.Def_GirvingAKS_Halver_Empty
import Definitions.Def_GirvingAKS_MGG_Spectral
import Definitions.Def_GirvingAKS_Graph_Square
import Definitions.Def_GirvingAKS_Misc_Log

/-! Ported to Lean v4.33.1 / Mathlib 0df444a from `AKS/Halver/General.lean` of
https://github.com/girving/aks (commit c7fb62ed80a4a610f87f34db0082cadbd7c00c9f, Apache-2.0). -/

/-
  # General Halver for Arbitrary Sizes

  Builds a halver network for any target size `m ≥ 1` via:
  1. Pick `n = max(3, √(Q₀·m) + 1)` so that `mgg n` has `n² ≥ m` vertices
  2. Apply iterated graph squaring to shrink spectral gap below `ε`
  3. Use the König quotient halver (`konigQuotientHalver`) to project to `m` wires

  The MGG graph `mgg n` is 8-regular on `n²` vertices with spectral gap
  ≤ `5√2/8 < 89/100`. The side length `n` is chosen so that `n²/m ≥ Q₀`,
  which (via `sufficient_epsCond`) ensures the algebraic condition `hε_cond`
  holds.

  Key results:
  - `mggHalverNet`: halver at `2 * m` wires for any `m ≥ 1`
  - `mggHalverNet_isEpsilonHalver`: the halver property (proved)
  - `mggHalverNet_depth_le`: m-independent depth bound (proved)
  - `halvers`: concrete entry point, fully proved
-/


section


/-! **Number of Squarings** -/

/-- Iteratively square a rational number `p` times: `iterSq c p = c^(2^p)`.
    Used to compute `β^(2^p)` for finding the number of squarings needed. -/
def iterSq (c : ℚ) : ℕ → ℚ
  | 0 => c
  | p + 1 => iterSq c p * iterSq c p

lemma iterSq_eq_pow (c : ℚ) (p : ℕ) : iterSq c p = c ^ (2 ^ p) := by
  induction p with
  | zero => simp [iterSq]
  | succ p ih => simp [iterSq, ih, pow_succ]; ring

/-- For any `0 ≤ c < 1` and `ε > 0`, there exists `p` with `c^(2^p) ≤ ε`. -/
lemma iterSq_eventually_le' (c ε : ℚ) (hc0 : 0 ≤ c) (hc1 : c < 1) (hε : 0 < ε) :
    ∃ p, iterSq c p ≤ ε := by
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε hc1
  exact ⟨n, by rw [iterSq_eq_pow]; exact le_of_lt (lt_of_le_of_lt
    (pow_le_pow_of_le_one hc0 hc1.le (le_of_lt Nat.lt_two_pow_self)) hn)⟩


/-! **MGG Spectral Gap Bound (Rational)** -/

/-- Rational upper bound for the MGG spectral gap `5√2/8 ≈ 0.8839`.
    We use `89/100 = 0.89` which satisfies `(5√2/8)² = 50/64 < 7921/10000 = (89/100)²`. -/
def mggBeta : ℚ := 89 / 100

/-- `mggBeta` is nonneg. -/
lemma mggBeta_nn : (0 : ℚ) ≤ mggBeta := by unfold mggBeta; norm_num

/-- `mggBeta` is less than 1. -/
lemma mggBeta_lt_one : mggBeta < 1 := by unfold mggBeta; norm_num

/-- The MGG spectral gap is bounded by `mggBeta`: `spectralGap (mgg n) ≤ 89/100`.
    Proof: `spectralGap (mgg n) ≤ 5√2/8` by `spectralGap_mgg`, and `5√2/8 ≤ 89/100`
    because `(5√2/8)² = 50/64 ≤ 7921/10000 = (89/100)²` (both sides nonneg). -/
theorem mgg_gap_le_mggBeta (n : ℕ) (hn : 3 ≤ n) :
    spectralGap (mgg n) ≤ ↑mggBeta := by
  have h1 := spectralGap_mgg n hn
  have h2 : 5 * Real.sqrt 2 / 8 ≤ (mggBeta : ℝ) := by
    rw [show (mggBeta : ℝ) = 89 / 100 from by unfold mggBeta; push_cast; ring]
    rw [div_le_div_iff₀ (by norm_num : (0:ℝ) < 8) (by norm_num : (0:ℝ) < 100)]
    -- Goal: 5 * √2 * 100 ≤ 89 * 8, i.e., 500 * √2 ≤ 712
    -- Square both sides (both nonneg): 500² * 2 = 500000 ≤ 506944 = 712²
    have h_lhs_nn : 0 ≤ 5 * Real.sqrt 2 * 100 := by positivity
    rw [show 89 * (8 : ℝ) = 712 from by norm_num]
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 from by norm_num),
               sq_nonneg (5 * Real.sqrt 2 * 100 - 712)]
  exact h1.trans h2


/-! **Number of Squarings (MGG)** -/

/-- Number of MGG graph squarings needed for spectral gap `≤ ε`.
    Computes `⌈log₂(⌈log_{1/β}(1/ε)⌉)⌉` where `β = 89/100`.
    Kernel-reducible via `Rat.ceilLog` + `Nat.clog` (no `Nat.find`). -/
def mggNumSquarings (ε : ℚ) (_hε : 0 < ε) : ℕ :=
  Nat.clog 2 (Rat.ceilLog (1 / mggBeta) (1 / ε))

/-- `mggNumSquarings` satisfies its spec. -/
lemma mggNumSquarings_spec (ε : ℚ) (hε : 0 < ε) :
    iterSq mggBeta (mggNumSquarings ε hε) ≤ ε := by
  set c := Rat.ceilLog (1 / mggBeta) (1 / ε)
  set p := Nat.clog 2 c
  -- Step 1: 1/ε ≤ (1/β)^c
  have h_inv_base : (1 : ℚ) < 1 / mggBeta := by unfold mggBeta; norm_num
  have h_inv_x : (0 : ℚ) < 1 / ε := by positivity
  have hle : 1 / ε ≤ (1 / mggBeta) ^ c := Rat.ceilLog_le _ _ h_inv_base h_inv_x
  -- Step 2: c ≤ 2^p
  have hcp : c ≤ 2 ^ p := Nat.le_pow_clog (by omega) c
  -- Step 3: β^(2^p) ≤ β^c (decreasing since 0 ≤ β ≤ 1)
  have h_mono : mggBeta ^ (2 ^ p) ≤ mggBeta ^ c :=
    pow_le_pow_of_le_one mggBeta_nn mggBeta_lt_one.le hcp
  -- Step 4: β^c ≤ ε (from 1/ε ≤ (1/β)^c)
  have hβc_pos : (0 : ℚ) < mggBeta ^ c := pow_pos (by unfold mggBeta; norm_num) c
  have h_beta_c : mggBeta ^ c ≤ ε := by
    rw [div_pow, one_pow] at hle
    rwa [div_le_div_iff₀ hε hβc_pos, one_mul, one_mul] at hle
  -- Combine: iterSq β p = β^(2^p) ≤ β^c ≤ ε
  rw [iterSq_eq_pow]
  exact le_trans h_mono h_beta_c


/-! **Algebraic Condition Infrastructure** -/

/-- The algebraic discriminant `A = ε² - β²(1-ε)²` from the `hε_cond` condition.
    When `A > 0` and `q` is large enough, `(q+1)²A > (2q+1)ε` holds. -/
def epsCondA (ε β : ℚ) : ℚ := ε ^ 2 - β ^ 2 * (1 - ε) ^ 2

/-- `A > 0` when `0 < ε`, `0 ≤ β ≤ ε`, `β < 1`. -/
lemma epsCondA_pos (ε β : ℚ) (hε : 0 < ε) (hβ : 0 ≤ β) (hβε : β ≤ ε) (hβ1 : β < 1) :
    0 < epsCondA ε β := by
  unfold epsCondA
  have key : ε ^ 2 - β ^ 2 * (1 - ε) ^ 2 =
    (ε - β * (1 - ε)) * (ε + β * (1 - ε)) := by ring
  rw [key]; apply mul_pos
  · by_cases h : ε ≤ 1
    · have : (1 - ε) * (ε - β) ≥ 0 := mul_nonneg (by linarith) (by linarith)
      nlinarith [mul_pos hε hε]
    · push_neg at h; have : β * (ε - 1) ≥ 0 := mul_nonneg hβ (by linarith); linarith
  · by_cases h : ε ≤ 1
    · have : β * (1 - ε) ≥ 0 := mul_nonneg hβ (by linarith); linarith
    · push_neg at h; nlinarith

/-- Bridge lemma: if `Q₀ * A > 3ε` then the full `hε_cond` holds for all `q ≥ Q₀`.
    This avoids proving `hε_cond` directly for each `q`; we just need `N/m ≥ Q₀`. -/
theorem sufficient_epsCond (ε A : ℝ) (hε : 0 < ε) (Q₀ : ℕ) (hQ₀ : 1 ≤ Q₀)
    (hQ₀A : (Q₀ : ℝ) * A > 3 * ε)
    (q : ℕ) (hq : Q₀ ≤ q) :
    (↑q + 1) ^ 2 * A > (2 * ↑q + 1) * ε := by
  have hQ₀_pos : (0 : ℝ) < Q₀ := by exact_mod_cast Nat.lt_of_lt_of_le Nat.one_pos hQ₀
  have hA : 0 < A := by
    by_contra h; push_neg at h
    have : (Q₀ : ℝ) * A ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hQ₀_pos.le h; linarith
  have hQ₀_le : (Q₀ : ℝ) ≤ q := by exact_mod_cast hq
  have hq_ge1 : (1 : ℝ) ≤ (q : ℝ) := le_trans (by exact_mod_cast hQ₀) hQ₀_le
  have h1 : (↑q + 1) ^ 2 * A ≥ (↑q : ℝ) ^ 2 * A := by nlinarith [sq_nonneg (q : ℝ)]
  have h2 : (↑q : ℝ) ^ 2 * A ≥ ↑Q₀ * ↑q * A := by
    have h2a : (↑q : ℝ) * ((↑q : ℝ) - ↑Q₀) ≥ 0 := mul_nonneg (by linarith) (by linarith)
    nlinarith
  have h3 : ↑Q₀ * (↑q : ℝ) * A > 3 * ↑q * ε := by
    have hq_pos : (↑q : ℝ) > 0 := by linarith
    nlinarith [mul_pos hq_pos hA]
  have h4 : 3 * (↑q : ℝ) * ε ≥ (2 * ↑q + 1) * ε := by
    have hq_sub : (↑q : ℝ) - 1 ≥ 0 := by linarith
    nlinarith [mul_nonneg hq_sub hε.le]
  linarith


/-! **Q₀ Computation** -/

/-- Existence of Q₀: for any `A > 0`, there exists `Q₀`
    such that `Q₀ * A > 3ε`. -/
lemma mggQ0_exists' (ε A : ℚ) (hA : 0 < A) :
    ∃ Q₀ : ℕ, (Q₀ : ℚ) * A > 3 * ε := by
  obtain ⟨n, hn⟩ := exists_nat_gt (3 * ε / A)
  refine ⟨n, ?_⟩; rwa [gt_iff_lt, ← div_lt_iff₀ hA]

/-- Helper for computing `mggQ0`: the `A` value for given `ε`. -/
def mggCondA (ε : ℚ) (hε : 0 < ε) : ℚ :=
  epsCondA ε (iterSq mggBeta (mggNumSquarings ε hε))

/-- The `A` value is positive. -/
lemma mggCondA_pos (ε : ℚ) (hε : 0 < ε) : 0 < mggCondA ε hε := by
  unfold mggCondA
  have hβ_nn : 0 ≤ iterSq mggBeta (mggNumSquarings ε hε) := by
    rw [iterSq_eq_pow]; exact pow_nonneg mggBeta_nn _
  have hβε := mggNumSquarings_spec ε hε
  have hβ1 : iterSq mggBeta (mggNumSquarings ε hε) < 1 := by
    rw [iterSq_eq_pow]; exact pow_lt_one₀ mggBeta_nn mggBeta_lt_one (by positivity)
  exact epsCondA_pos ε _ hε hβ_nn hβε hβ1

/-- The Q₀ value for the MGG construction: the smallest `Q₀ ≥ 1` such that `Q₀ * A > 3ε`.
    Computed as `⌊3ε/A⌋₊ + 1`, kernel-reducible (no `Nat.find`). -/
def mggQ0 (ε : ℚ) (hε : 0 < ε) : ℕ :=
  ⌊3 * ε / mggCondA ε hε⌋₊ + 1

/-- `mggQ0 ≥ 1`. -/
lemma mggQ0_pos (ε : ℚ) (hε : 0 < ε) : 1 ≤ mggQ0 ε hε := by
  unfold mggQ0; omega

/-- `mggQ0` satisfies the sufficient condition: `Q₀ * A > 3ε`. -/
lemma mggQ0_spec (ε : ℚ) (hε : 0 < ε) :
    (mggQ0 ε hε : ℚ) * mggCondA ε hε > 3 * ε := by
  unfold mggQ0
  have hA_pos := mggCondA_pos ε hε
  have h := Nat.lt_floor_add_one (3 * ε / mggCondA ε hε)
  rw [gt_iff_lt, ← div_lt_iff₀ hA_pos]
  exact_mod_cast h


/-! **Side Length** -/

/-- Side length of the MGG graph for target size `m`:
    `n = max 3 (√(Q₀ * m) + 1)`, ensuring `n ≥ 3` (for `spectralGap_mgg`)
    and `n² ≥ Q₀ * m + 1 > m` (for quotient halver). -/
def mggSideLen (Q0 m : ℕ) : ℕ := max 3 (Nat.sqrt (Q0 * m) + 1)

/-- `mggSideLen ≥ 3`. -/
lemma mggSideLen_ge_three (Q0 m : ℕ) : 3 ≤ mggSideLen Q0 m := le_max_left _ _

/-- `m ≤ n²` where `n = mggSideLen Q0 m`, when `Q0 ≥ 1`. -/
lemma mggSideLen_sq_ge (Q0 m : ℕ) (hQ0 : 1 ≤ Q0) :
    m ≤ mggSideLen Q0 m * mggSideLen Q0 m := by
  unfold mggSideLen
  have h1 : Q0 * m < (Nat.sqrt (Q0 * m) + 1) ^ 2 := Nat.lt_succ_sqrt' (Q0 * m)
  have h2 : m ≤ Q0 * m := Nat.le_mul_of_pos_left m (by omega)
  have h3 : m < (Nat.sqrt (Q0 * m) + 1) ^ 2 := lt_of_le_of_lt h2 h1
  have h4 : m ≤ (Nat.sqrt (Q0 * m) + 1) * (Nat.sqrt (Q0 * m) + 1) := by rw [← sq]; omega
  calc m ≤ (Nat.sqrt (Q0 * m) + 1) * (Nat.sqrt (Q0 * m) + 1) := h4
    _ ≤ max 3 (Nat.sqrt (Q0 * m) + 1) * max 3 (Nat.sqrt (Q0 * m) + 1) :=
      Nat.mul_le_mul (le_max_right _ _) (le_max_right _ _)

/-- `Q0 ≤ n²/m` where `n = mggSideLen Q0 m`, when `m > 0`. -/
lemma mggSideLen_div_ge (Q0 m : ℕ) (hm : 0 < m) :
    Q0 ≤ mggSideLen Q0 m * mggSideLen Q0 m / m := by
  rw [Nat.le_div_iff_mul_le hm]
  unfold mggSideLen
  have h1 : Q0 * m < (Nat.sqrt (Q0 * m) + 1) ^ 2 := Nat.lt_succ_sqrt' (Q0 * m)
  calc Q0 * m
      ≤ (Nat.sqrt (Q0 * m) + 1) * (Nat.sqrt (Q0 * m) + 1) := by rw [← sq]; omega
    _ ≤ max 3 (Nat.sqrt (Q0 * m) + 1) * max 3 (Nat.sqrt (Q0 * m) + 1) :=
      Nat.mul_le_mul (le_max_right _ _) (le_max_right _ _)


/-! **Depth Factor** -/

/-- Depth factor: upper bound on `n²/m + 1` that is independent of `m`.
    We use `7 * Q0 + 10` which covers all cases including `m = 1`.
    For `n = max(3, √(Q0*m) + 1)`, we have `n ≤ √(Q0*m) + 3` (since `max(3,s+1) ≤ s+3`),
    so `n² ≤ (√(Q0*m) + 3)² ≤ Q0*m + 6*Q0*m + 9 = 7*Q0*m + 9`, giving
    `n²/m ≤ 7*Q0 + 9` and `n²/m + 1 ≤ 7*Q0 + 10`. -/
def mggDepthFactor (Q0 : ℕ) : ℕ := 7 * Q0 + 10

/-- `n²/m + 1 ≤ mggDepthFactor Q0` when `m > 0`. -/
lemma mggSideLen_div_le (Q0 m : ℕ) (hm : 0 < m) :
    mggSideLen Q0 m * mggSideLen Q0 m / m + 1 ≤ mggDepthFactor Q0 := by
  unfold mggSideLen mggDepthFactor
  set s := Nat.sqrt (Q0 * m)
  -- max(3, s+1) ≤ s + 3
  have hmax_le : max 3 (s + 1) ≤ s + 3 := by omega
  -- s² ≤ Q0 * m (from Nat.sqrt_le)
  have hs2 : s * s ≤ Q0 * m := Nat.sqrt_le (Q0 * m)
  -- s ≤ Q0 * m (from Nat.sqrt_le_self)
  have hs_le : s ≤ Q0 * m := Nat.sqrt_le_self (Q0 * m)
  -- (s+3)² = s² + 6s + 9 ≤ Q0*m + 6*Q0*m + 9 = 7*Q0*m + 9
  have h_sq : (s + 3) * (s + 3) ≤ 7 * Q0 * m + 9 := by nlinarith
  -- n² ≤ 7*Q0*m + 9
  have hn2_le : max 3 (s + 1) * max 3 (s + 1) ≤ 7 * Q0 * m + 9 :=
    le_trans (Nat.mul_le_mul hmax_le hmax_le) h_sq
  -- n²/m ≤ (7*Q0*m + 9)/m ≤ 7*Q0 + 9
  have hdiv1 : max 3 (s + 1) * max 3 (s + 1) / m ≤ (7 * Q0 * m + 9) / m :=
    Nat.div_le_div_right hn2_le
  have hdiv2 : (7 * Q0 * m + 9) / m ≤ 7 * Q0 + 9 := by
    rw [show 7 * Q0 * m + 9 = 9 + m * (7 * Q0) from by ring]
    rw [Nat.add_mul_div_left 9 (7 * Q0) hm]
    have : 9 / m ≤ 9 := Nat.div_le_self 9 m; omega
  omega


/-! **Halver Construction** -/

/-- Halver network for target size `m ≥ 1`, using the MGG graph.
    Squares `mgg n` `p` times, then applies `konigQuotientHalver`. -/
def mggHalverNet (p Q0 m : ℕ) (hm : 0 < m) :
    ComparatorNetwork (2 * m) :=
  let n := mggSideLen Q0 m
  let G := (mgg n).iterSquare p
  have hd_pos : 0 < iterSquareDeg 8 p := iterSquareDeg_pos (by norm_num) p
  konigQuotientHalver G m hm hd_pos


/-! **Halver Property** -/

/-- The MGG halver is an ε-halver. Chains:
    `spectralGap_mgg` → `mgg_gap_le_mggBeta` → `spectralGap_iterSquare` →
    `sufficient_epsCond` (with Q0, using `mggSideLen_div_ge`) →
    `konigQuotientHalver_isEpsilonHalver`. -/
theorem mggHalverNet_isEpsilonHalver (p Q0 m : ℕ) (hm : 0 < m) (hQ0 : 1 ≤ Q0)
    {ε : ℚ} (hε_pos : 0 < ε)
    (hQ0A : (Q0 : ℚ) * epsCondA ε (iterSq mggBeta p) > 3 * ε) :
    IsEpsilonHalver (mggHalverNet p Q0 m hm) (↑ε) := by
  unfold mggHalverNet
  set n := mggSideLen Q0 m
  have hn3 := mggSideLen_ge_three Q0 m
  have hmN := mggSideLen_sq_ge Q0 m hQ0
  have hd_pos : 0 < iterSquareDeg 8 p := iterSquareDeg_pos (by norm_num) p
  -- Spectral gap bound after squaring
  have hgap_mgg : spectralGap (mgg n) ≤ ↑mggBeta := mgg_gap_le_mggBeta n hn3
  have hgap_sq : spectralGap ((mgg n).iterSquare p) ≤ (↑mggBeta : ℝ) ^ (2^p) := by
    rw [spectralGap_iterSquare]
    exact pow_le_pow_left₀ (spectralGap_nonneg _) hgap_mgg (2^p)
  -- Convert iterSq to pow
  set β := iterSq mggBeta p
  have hβ_eq : (↑β : ℝ) = (↑mggBeta : ℝ) ^ (2^p) := by
    show (↑(iterSq mggBeta p) : ℝ) = _; rw [iterSq_eq_pow]; push_cast; rfl
  have hgap : spectralGap ((mgg n).iterSquare p) ≤ (↑β : ℝ) := by rw [hβ_eq]; exact hgap_sq
  have hβ_nn_q : (0 : ℚ) ≤ β := by
    show 0 ≤ iterSq mggBeta p; rw [iterSq_eq_pow]; exact pow_nonneg mggBeta_nn _
  have hβ_nn : (0 : ℝ) ≤ ↑β := by exact_mod_cast hβ_nn_q
  have hβ1 : (↑β : ℝ) < 1 := by
    exact_mod_cast (show β < 1 from by
      show iterSq mggBeta p < 1; rw [iterSq_eq_pow]
      exact pow_lt_one₀ mggBeta_nn mggBeta_lt_one (by positivity))
  -- Q0 ≤ n²/m
  have hQ0_le := mggSideLen_div_ge Q0 m hm
  -- Cast the ℚ condition to ℝ
  have hε_nn : (0 : ℝ) ≤ ↑ε := by exact_mod_cast hε_pos.le
  have hε_pos_r : (0 : ℝ) < ↑ε := by exact_mod_cast hε_pos
  have hQ0A_r : (Q0 : ℝ) * ((↑ε : ℝ) ^ 2 - (↑β : ℝ) ^ 2 * (1 - ↑ε) ^ 2) > 3 * ↑ε := by
    have h := Rat.cast_lt (K := ℝ).mpr hQ0A
    simp only [Rat.cast_mul, Rat.cast_ofNat, Rat.cast_natCast] at h
    unfold epsCondA at h; push_cast at h; linarith
  -- Apply sufficient_epsCond
  have hε_cond := sufficient_epsCond (↑ε)
    ((↑ε : ℝ) ^ 2 - (↑β : ℝ) ^ 2 * (1 - ↑ε) ^ 2)
    hε_pos_r Q0 hQ0 hQ0A_r
    (n * n / m) (by exact_mod_cast hQ0_le)
  exact konigQuotientHalver_isEpsilonHalver _ hm hmN hd_pos (↑ε) (↑β) hgap hβ_nn hβ1 hε_nn hε_cond

/-! **Depth Bound** -/

/-- Depth bound for the MGG halver: depth ≤ `iterSquareDeg 8 p * mggDepthFactor Q0`.
    The König quotient halver has depth ≤ `d * (N/m + 1)`, and
    `N/m + 1 ≤ mggDepthFactor Q0`. -/
theorem mggHalverNet_depth_le (p Q0 m : ℕ) (hm : 0 < m) :
    (mggHalverNet p Q0 m hm).depth ≤
      iterSquareDeg 8 p * mggDepthFactor Q0 := by
  unfold mggHalverNet
  have hd_pos : 0 < iterSquareDeg 8 p := iterSquareDeg_pos (by norm_num) p
  calc (konigQuotientHalver _ m hm hd_pos).depth
      ≤ iterSquareDeg 8 p * (mggSideLen Q0 m * mggSideLen Q0 m / m + 1) :=
        konigQuotientHalver_depth_le _ m hm hd_pos
    _ ≤ iterSquareDeg 8 p * mggDepthFactor Q0 := by
        apply Nat.mul_le_mul_left
        exact mggSideLen_div_le Q0 m hm


/-! **Concrete Halver Family** -/

/-- m-independent depth bound for halvers at error `ε`.
    Uses MGG base expander (degree 8). -/
def halverDepth (ε : ℚ) (hε : 0 < ε) : ℕ :=
  iterSquareDeg 8 (mggNumSquarings ε hε) * mggDepthFactor (mggQ0 ε hε)

/-- Concrete halver family using the MGG expander (8-regular on `n²` vertices).
    Takes `ε > 0` and computes the number of squarings and Q₀ internally.

    The halver property is fully proved via:
    1. `mggNumSquarings` finds `p` with `(89/100)^(2^p) ≤ ε`
    2. `mggQ0` finds Q₀ so `Q₀ * A > 3ε`
    3. `mggSideLen` picks `n` with `n² ≥ m` and `n²/m ≥ Q₀`
    4. `sufficient_epsCond` bridges to `hε_cond`
    5. `konigQuotientHalver_isEpsilonHalver` gives the halver property -/
def halvers (ε : ℚ) (hε : 0 < ε) : HalverFamily ε where
  depth := halverDepth ε hε
  net m :=
    if hm : 0 < m then
      mggHalverNet (mggNumSquarings ε hε) (mggQ0 ε hε) m hm
    else (⟨[]⟩ : ComparatorNetwork 0).cast (by omega)
  isHalver m := by
    by_cases hm : 0 < m
    · rw [dif_pos hm]
      exact mggHalverNet_isEpsilonHalver _ _ m hm (mggQ0_pos ε hε)
        hε (mggQ0_spec ε hε)
    · rw [dif_neg hm]
      exact (ComparatorNetwork.cast_isEpsilonHalver _ _ _).mpr
        (emptyNet_isEpsilonHalver ↑ε)
  depth_le m := by
    by_cases hm : 0 < m
    · rw [dif_pos hm]
      exact mggHalverNet_depth_le _ _ m hm
    · rw [dif_neg hm]; simp [ComparatorNetwork.cast_depth, emptyNet_depth]

/-! **Helper lemmas for `halverDepth_antitone`** -/

private theorem iterSq_ge_base {c : ℚ} (hc : 1 ≤ c) (p : ℕ) : c ≤ iterSq c p := by
  induction p with
  | zero => simp [iterSq]
  | succ p ih =>
    simp only [iterSq]; exact le_trans ih (le_mul_of_one_le_right (by linarith) (le_trans hc ih))

private theorem iterSq_mul (a b : ℚ) (p : ℕ) : iterSq a p * iterSq b p = iterSq (a * b) p := by
  induction p with
  | zero => simp [iterSq]
  | succ p ih =>
    simp only [iterSq]
    rw [show iterSq a p * iterSq a p * (iterSq b p * iterSq b p) =
      (iterSq a p * iterSq b p) * (iterSq a p * iterSq b p) from by ring, ih]

private theorem iterSquareDeg_cast (d p : ℕ) : (iterSquareDeg d p : ℚ) = iterSq (d : ℚ) p := by
  induction p with
  | zero => simp [iterSquareDeg, iterSq]
  | succ p ih => simp only [iterSquareDeg, iterSq, Nat.cast_mul, ih]

private theorem iterSquareDeg_mono_p {d : ℕ} (hd : 1 ≤ d) {p₁ p₂ : ℕ} (hp : p₁ ≤ p₂) :
    iterSquareDeg d p₁ ≤ iterSquareDeg d p₂ := by
  obtain ⟨k, rfl⟩ := Nat.le.dest hp
  induction k with
  | zero => simp
  | succ k ih =>
    calc iterSquareDeg d p₁ ≤ iterSquareDeg d (p₁ + k) := ih (by omega)
      _ ≤ iterSquareDeg d (p₁ + k) * iterSquareDeg d (p₁ + k) :=
        Nat.le_mul_of_pos_right _ (iterSquareDeg_pos (by omega) _)

/-- `mggNumSquarings` is antitone: larger ε → fewer squarings needed. -/
theorem mggNumSquarings_antitone {ε₁ ε₂ : ℚ} (hε₁ : 0 < ε₁) (hε₂ : 0 < ε₂) (h : ε₁ ≤ ε₂) :
    mggNumSquarings ε₂ hε₂ ≤ mggNumSquarings ε₁ hε₁ := by
  unfold mggNumSquarings
  apply Nat.clog_mono_right 2
  apply Rat.ceilLog_mono_right
  · rw [one_div]; exact one_lt_inv_iff₀.mpr ⟨by unfold mggBeta; norm_num, by unfold mggBeta; norm_num⟩
  · positivity
  · exact div_le_div_of_nonneg_left (by norm_num : (0:ℚ) ≤ 1) hε₁ h

/-- Cross-bound: `ε₂ * A(ε₁,β) ≤ ε₁ * A(ε₂,β)` when `ε₁ ≤ ε₂` and `β < 1`. -/
private theorem epsCondA_cross {ε₁ ε₂ β : ℚ} (hε₁ : 0 < ε₁) (h : ε₁ ≤ ε₂)
    (hβ : 0 ≤ β) (hβ1 : β < 1) :
    ε₂ * epsCondA ε₁ β ≤ ε₁ * epsCondA ε₂ β := by
  unfold epsCondA
  have key : ε₁ * (ε₂ ^ 2 - β ^ 2 * (1 - ε₂) ^ 2) - ε₂ * (ε₁ ^ 2 - β ^ 2 * (1 - ε₁) ^ 2) =
    (ε₂ - ε₁) * (ε₁ * ε₂ * (1 - β ^ 2) + β ^ 2) := by ring
  have h1 : 0 ≤ 1 - β ^ 2 := by nlinarith [sq_nonneg (1 - β)]
  nlinarith [sq_nonneg β, mul_nonneg (mul_nonneg hε₁.le (le_trans hε₁.le h)) h1]

/-- Lower bound: `A ≥ ε · β²` when `β < 1` and `β ≤ ε`. -/
private theorem epsCondA_ge_eps_mul_sq {ε β : ℚ} (hε : 0 < ε) (hβ : 0 ≤ β) (hβ1 : β < 1)
    (hβε : β ≤ ε) : ε * β ^ 2 ≤ epsCondA ε β := by
  unfold epsCondA
  suffices h : β ^ 2 * (1 - ε + ε ^ 2) ≤ ε ^ 2 by linarith
  by_cases hε1 : ε ≤ 1
  · have hβ2 : β ^ 2 ≤ ε ^ 2 := by nlinarith [sq_nonneg (ε - β)]
    calc β ^ 2 * (1 - ε + ε ^ 2) ≤ ε ^ 2 * 1 :=
          mul_le_mul hβ2 (by nlinarith) (by nlinarith [sq_nonneg (1 - ε)]) (by positivity)
      _ = ε ^ 2 := mul_one _
  · push_neg at hε1
    have h1 : β ^ 2 * (1 - ε) ≤ 0 := by nlinarith [sq_nonneg β]
    have h2 : β ^ 2 * ε ^ 2 ≤ ε ^ 2 := by
      nlinarith [sq_nonneg (1 - β), sq_nonneg ε, sq_nonneg (ε * (1 - β))]
    nlinarith

/-- Upper bound on `mggQ0`: `Q₀ · A ≤ 3ε + A`. -/
private theorem mggQ0_mul_le (ε : ℚ) (hε : 0 < ε) :
    (mggQ0 ε hε : ℚ) * mggCondA ε hε ≤ 3 * ε + mggCondA ε hε := by
  unfold mggQ0
  have hA_pos := mggCondA_pos ε hε
  set A := mggCondA ε hε
  -- ⌊3ε/A⌋₊ ≤ 3ε/A, so (⌊3ε/A⌋₊ + 1) * A ≤ 3ε + A
  have hfloor := Nat.floor_le (div_nonneg (by linarith) hA_pos.le : (0:ℚ) ≤ 3 * ε / A)
  -- (↑⌊3ε/A⌋₊ + 1) * A = ↑⌊3ε/A⌋₊ * A + A
  push_cast
  nlinarith [mul_div_cancel₀ (3 * ε) (ne_of_gt hA_pos)]

/-- `21 ≤ 17·(d-1)·β²` where `d = iterSq 8 p`, `β² = iterSq(7921/10000, p)`.
    The key exponential bound ensuring `mggDepthFactor Q₀ ≤ 17·d`. -/
private theorem depth_factor_bound (p : ℕ) :
    (21 : ℚ) ≤ 17 * (iterSq 8 p - 1) * iterSq (7921 / 10000) p := by
  induction p with
  | zero => simp [iterSq]; norm_num
  | succ p ih =>
    simp only [iterSq]
    set d := iterSq (8 : ℚ) p
    set c := iterSq (7921 / 10000 : ℚ) p
    have hd : (8 : ℚ) ≤ d := iterSq_ge_base (by norm_num) p
    have hc_pos : (0 : ℚ) < c := by show 0 < iterSq _ p; rw [iterSq_eq_pow]; positivity
    have hdc : (63368 / 10000 : ℚ) ≤ d * c := by
      have h1 : iterSq (8 * (7921 / 10000) : ℚ) p = d * c := (iterSq_mul 8 (7921/10000) p).symm
      have h2 : (8 * (7921 / 10000) : ℚ) = 63368 / 10000 := by norm_num
      rw [h2] at h1; rw [← h1]; exact iterSq_ge_base (by norm_num) p
    have h_dc1 : (1 : ℚ) ≤ (d + 1) * c := by nlinarith
    have key : 17 * (d * d - 1) * (c * c) = 17 * (d - 1) * c * ((d + 1) * c) := by ring
    nlinarith

/-- `mggDepthFactor (mggQ0 ε hε) ≤ 17 · iterSquareDeg 8 (mggNumSquarings ε hε)`.
    Chains: `Q₀·A ≤ 3ε+A` → `A ≥ ε·β²` → `21 ≤ 17·(d-1)·β²` → divide by `A > 0`. -/
private theorem mggQ0_depth_bound (ε : ℚ) (hε : 0 < ε) :
    mggDepthFactor (mggQ0 ε hε) ≤ 17 * iterSquareDeg 8 (mggNumSquarings ε hε) := by
  set p := mggNumSquarings ε hε
  set A := mggCondA ε hε
  set Q := mggQ0 ε hε
  set d := iterSquareDeg 8 p
  set β := iterSq mggBeta p
  have hA_pos := mggCondA_pos ε hε
  have hβ_nn : 0 ≤ β := by
    show 0 ≤ iterSq mggBeta p; rw [iterSq_eq_pow]; exact pow_nonneg mggBeta_nn _
  have hβ1 : β < 1 := by
    show iterSq mggBeta p < 1; rw [iterSq_eq_pow]
    exact pow_lt_one₀ mggBeta_nn mggBeta_lt_one (by positivity)
  have hβε : β ≤ ε := mggNumSquarings_spec ε hε
  have hA_lb : ε * β ^ 2 ≤ A := epsCondA_ge_eps_mul_sq hε hβ_nn hβ1 hβε
  have hQ_ub := mggQ0_mul_le ε hε
  -- (7Q+10) * A ≤ 21ε + 17A
  have hQA : (7 * Q + 10 : ℚ) * A ≤ 21 * ε + 17 * A := by
    show (7 * (mggQ0 ε hε : ℚ) + 10) * A ≤ _; nlinarith
  -- β² = iterSq(7921/10000, p)
  have hβ2_eq : β * β = iterSq (7921 / 10000 : ℚ) p := by
    show iterSq mggBeta p * iterSq mggBeta p = _
    rw [iterSq_mul]; congr 1; unfold mggBeta; norm_num
  -- (d : ℚ) = iterSq 8 p
  have hd_eq : (d : ℚ) = iterSq 8 p := iterSquareDeg_cast 8 p
  -- 21 ≤ 17*(d-1)*β²
  have h_dfb := depth_factor_bound p
  -- Chain: 21ε ≤ 17*(d-1)*ε*β² ≤ (17d-17)*A
  have hd_pos : (0 : ℚ) < d := by exact_mod_cast iterSquareDeg_pos (by norm_num : 0 < 8) p
  have h_21ε : 21 * ε ≤ (17 * (d : ℚ) - 17) * A := by
    have h1 : (21 : ℚ) ≤ 17 * ((d : ℚ) - 1) * (β * β) := by rw [hβ2_eq, hd_eq]; exact h_dfb
    have h2 : 21 * ε ≤ 17 * ((d : ℚ) - 1) * (ε * β ^ 2) := by nlinarith
    have hfac : (0 : ℚ) ≤ 17 * ((d : ℚ) - 1) := by nlinarith
    calc 21 * ε ≤ 17 * ((d : ℚ) - 1) * (ε * β ^ 2) := h2
      _ ≤ 17 * ((d : ℚ) - 1) * A := by nlinarith
      _ = (17 * (d : ℚ) - 17) * A := by ring
  -- (7Q+10) * A ≤ 17*d*A
  have hQdA : (7 * Q + 10 : ℚ) * A ≤ 17 * (d : ℚ) * A := by nlinarith
  -- Divide by A > 0
  have h_final : (7 * Q + 10 : ℚ) ≤ 17 * (d : ℚ) := le_of_mul_le_mul_right hQdA hA_pos
  show 7 * Q + 10 ≤ 17 * d; exact_mod_cast h_final

/-- Halver depth is antitone in ε: larger error tolerance → fewer squarings → less depth.

    **Case `p₁ = p₂`** (same squarings): same degree `d`, and `Q₂ ≤ Q₁` via `epsCondA_cross`
    (larger ε needs smaller Q₀ for the algebraic condition), so `d·F(Q₂) ≤ d·F(Q₁)`.

    **Case `p₂ < p₁`** (fewer squarings): `F(Q₂) ≤ 17·d₂` (from `depth_factor_bound`),
    so `halverDepth ε₂ ≤ 17·d₂² ≤ 17·d₁ ≤ halverDepth ε₁`. -/
theorem halverDepth_antitone {ε₁ ε₂ : ℚ} (hε₁ : 0 < ε₁) (hε₂ : 0 < ε₂) (h : ε₁ ≤ ε₂) :
    halverDepth ε₂ hε₂ ≤ halverDepth ε₁ hε₁ := by
  unfold halverDepth
  set p₁ := mggNumSquarings ε₁ hε₁
  set p₂ := mggNumSquarings ε₂ hε₂
  set d₁ := iterSquareDeg 8 p₁
  set d₂ := iterSquareDeg 8 p₂
  have hp : p₂ ≤ p₁ := mggNumSquarings_antitone hε₁ hε₂ h
  have hd₁_pos : 0 < d₁ := iterSquareDeg_pos (by omega) p₁
  rcases Nat.eq_or_lt_of_le hp with heq | hlt
  · -- Case p₂ = p₁: same β, show Q₂ ≤ Q₁ via epsCondA_cross
    have hd_eq : d₂ = d₁ := by show iterSquareDeg 8 p₂ = iterSquareDeg 8 p₁; rw [heq]
    set β := iterSq mggBeta p₁
    have hβ_nn : 0 ≤ β := by show 0 ≤ iterSq mggBeta p₁; rw [iterSq_eq_pow]; exact pow_nonneg mggBeta_nn _
    have hβ1 : β < 1 := by show iterSq mggBeta p₁ < 1; rw [iterSq_eq_pow]; exact pow_lt_one₀ mggBeta_nn mggBeta_lt_one (by positivity)
    have hA₁_pos := mggCondA_pos ε₁ hε₁
    have hA₂_pos := mggCondA_pos ε₂ hε₂
    -- mggCondA ε₁ hε₁ = epsCondA ε₁ β since p₁ = p₂ → same β
    have hA₁_eq : mggCondA ε₁ hε₁ = epsCondA ε₁ β := rfl
    have hA₂_eq : mggCondA ε₂ hε₂ = epsCondA ε₂ (iterSq mggBeta p₂) := rfl
    have hβ_eq : iterSq mggBeta p₂ = β := by rw [heq]
    rw [hβ_eq] at hA₂_eq
    -- epsCondA_cross: ε₂ * epsCondA ε₁ β ≤ ε₁ * epsCondA ε₂ β
    have hcross := epsCondA_cross hε₁ h hβ_nn hβ1
    -- 3ε₂/A₂ ≤ 3ε₁/A₁
    have hQ : mggQ0 ε₂ hε₂ ≤ mggQ0 ε₁ hε₁ := by
      unfold mggQ0
      apply Nat.add_le_add_right
      apply Nat.floor_le_floor
      rw [hA₁_eq, hA₂_eq]
      have hA₁ : (0 : ℚ) < epsCondA ε₁ β := by rw [← hA₁_eq]; exact hA₁_pos
      have hA₂ : (0 : ℚ) < epsCondA ε₂ β := by rw [← hA₂_eq]; exact hA₂_pos
      rw [div_le_div_iff₀ hA₂ hA₁]
      linarith
    calc d₂ * mggDepthFactor (mggQ0 ε₂ hε₂)
        ≤ d₁ * mggDepthFactor (mggQ0 ε₂ hε₂) :=
          Nat.mul_le_mul_right _ (by omega)
      _ ≤ d₁ * mggDepthFactor (mggQ0 ε₁ hε₁) := by
          apply Nat.mul_le_mul_left; unfold mggDepthFactor; omega
  · -- Case p₂ < p₁: F(Q₂) ≤ 17·d₂, so d₂·F(Q₂) ≤ 17·d₂² ≤ 17·d₁ ≤ d₁·F(Q₁)
    have hF := mggQ0_depth_bound ε₂ hε₂
    have hd₂_pos : 0 < d₂ := iterSquareDeg_pos (by omega) p₂
    have h_sq : d₂ * d₂ ≤ d₁ := by
      show iterSquareDeg 8 p₂ * iterSquareDeg 8 p₂ ≤ iterSquareDeg 8 p₁
      change iterSquareDeg 8 (p₂ + 1) ≤ iterSquareDeg 8 p₁
      exact iterSquareDeg_mono_p (by omega) hlt
    have hQ₁ := mggQ0_pos ε₁ hε₁
    calc d₂ * mggDepthFactor (mggQ0 ε₂ hε₂)
        ≤ d₂ * (17 * d₂) := Nat.mul_le_mul_left _ hF
      _ = 17 * (d₂ * d₂) := by ring
      _ ≤ 17 * d₁ := Nat.mul_le_mul_left _ h_sq
      _ ≤ d₁ * mggDepthFactor (mggQ0 ε₁ hε₁) := by
          unfold mggDepthFactor; nlinarith

end


