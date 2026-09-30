-- Prove2me | Definitions.Def_CK_GeneralCK_PsiBoundaryLeafReplay
-- name    : CK_GeneralCK_PsiBoundaryLeafReplay
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T12:56:53.875088+00:00
-- url     : https://prove2.me/theorems/74421c87-429f-4d5c-b7b6-57f551ed8c46
-- title:
--   Courtade–Kumar proof module `GeneralCK.PsiBoundaryLeafReplay` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PsiBoundaryLeafReplay` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PsiBoundaryLeafReplay` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PsiBoundaryLeafReplay (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PsiBoundaryLeafReplay.lean)

import Definitions.Def_CK_GeneralCK_PsiScalarOwnerCore
import Mathlib.Analysis.Complex.ExponentialBounds

-- ===== source module GeneralCK.PsiBoundaryLeafReplay =====
section

/-!
# Exact endpoints and complete partition coverage for the seventeen boundary-strip leaves

This file reconstructs, in exact rational arithmetic, the seventeen leaves of the
archived one-dimensional boundary-strip certificate
(`cluster/active_psi_scalar_plan/source/opposite/BOUNDARY_STRIP_RESULT.json`) and
proves in Lean

* that the seventeen closed rational intervals tile the strip `x ∈ [K - A, 1/2]`
  exactly, with `A = 2⁻²⁸` and `K = 2⁻¹³` (`mem_strip_iff`, `leaves_chainFrom`,
  `leaves_rightEnd`);
* that the five leaves inside the first initial interval are exactly the dyadic
  bisections along the archived binary paths `0000, 0001, 001, 01, 1`
  (`root0_leaves`);
* the per-leaf directed comparison of `PROOF.md`: on each leaf `[l,u]` the cost
  lower bound `½(1-u-A)(J A + J u)` strictly exceeds the psi-branch upper
  envelope, which is `η(q/8 + C q)` for the twelve enhanced initial intervals and
  `η(C q)` for the last, with `q = l - A` (`leaf00` … `leaf16`, `all_leaves_gap`).

All transcendental quantities are enclosed by kernel-checked rational witnesses.
`log₂` of a positive rational `b/c` is bounded by exact integer power comparisons
`b^k ≤ 2^p * c^k` (`log2_nat_le`, `log2_div_le_of_pow_le`, `le_log2_div_of_pow_le`);
`η` is bounded above through an explicit rational entropy-inverse witness
(`eta_le_of_H_le`); `C` is bounded below by the elementary rational envelope
`C q ≥ (7/10) q² (1 - 2q)` on `[0,½]` (`Ccap_lower`), and at `q = 2/5 - A` by the
sharper power-checked bound `Ccap_two_fifths`.  Nothing here is evaluated
numerically and no floating-point datum from the archive is used as evidence.

**Scope.** This file does *not* claim the opposite-boundary owner.  The archived
handoff states that the seventeen leaves alone are not an owner proof: the owner
additionally needs the retained opposite corner `a + 1 - b ≤ 2⁻¹³` and the
factor-eight parent criterion, neither of which is proved here.
-/

set_option exponentiation.threshold 100000
set_option maxRecDepth 100000

namespace GeneralCK
namespace BoundaryStrip

/-! ## 1. The archived rational data and its exact partition -/

/-- `A = 2⁻²⁸`, as a rational. -/
def Aq : ℚ := 1/268435456

/-- `K = 2⁻¹³`, as a rational. -/
def Kq : ℚ := 1/8192

/-- The thirteen initial intervals of `BOUNDARY_STRIP.py`: `[K-A, 2K]`, then
`[2^{-k}, 2^{-k+1}]` for `k = 12, 11, …, 3`, then `[1/4, 2/5]` and `[2/5, 1/2]`.
The Boolean records the psi-branch envelope used: `true` for the enhanced bound
(6) `η(q/8 + C q)`, `false` for the plain bound (5) `η(C q)`. -/
def roots : List (ℚ × ℚ × Bool) :=
  [ (32767/268435456, 1/4096, true),
    (1/4096, 1/2048, true),
    (1/2048, 1/1024, true),
    (1/1024, 1/512, true),
    (1/512, 1/256, true),
    (1/256, 1/128, true),
    (1/128, 1/64, true),
    (1/64, 1/32, true),
    (1/32, 1/16, true),
    (1/16, 1/8, true),
    (1/8, 1/4, true),
    (1/4, 2/5, true),
    (2/5, 1/2, false) ]

/-- Exact dyadic bisection along an archived binary path: `false` keeps the left
half, `true` keeps the right half. -/
def bisect : ℚ → ℚ → List Bool → ℚ × ℚ
  | lo, hi, [] => (lo, hi)
  | lo, hi, (false :: t) => bisect lo ((lo + hi)/2) t
  | lo, hi, (true :: t) => bisect ((lo + hi)/2) hi t

/-- The five archived leaf paths inside the first initial interval. -/
def root0Paths : List (List Bool) :=
  [ [false, false, false, false],
    [false, false, false, true],
    [false, false, true],
    [false, true],
    [true] ]

/-- The seventeen leaves of the archived certificate, in increasing order, with
exact rational endpoints and the branch flag inherited from the initial interval. -/
def leaves : List (ℚ × ℚ × Bool) :=
  [ (32767/268435456, 557041/4294967296, true),
    (557041/4294967296, 294905/2147483648, true),
    (294905/2147483648, 163837/1073741824, true),
    (163837/1073741824, 98303/536870912, true),
    (98303/536870912, 1/4096, true),
    (1/4096, 1/2048, true),
    (1/2048, 1/1024, true),
    (1/1024, 1/512, true),
    (1/512, 1/256, true),
    (1/256, 1/128, true),
    (1/128, 1/64, true),
    (1/64, 1/32, true),
    (1/32, 1/16, true),
    (1/16, 1/8, true),
    (1/8, 1/4, true),
    (1/4, 2/5, true),
    (2/5, 1/2, false) ]

theorem roots_length : roots.length = 13 := rfl

theorem leaves_length : leaves.length = 17 := rfl

/-- The strip starts exactly at `K - A = 32767 / 2²⁸`. -/
theorem strip_left : (32767/268435456 : ℚ) = Kq - Aq := by norm_num [Kq, Aq]

/-- The five leaves of the first initial interval are exactly the dyadic
bisections of `[K-A, 2K]` along the archived paths. -/
theorem root0_leaves :
    root0Paths.map (fun p => bisect (32767/268435456) (1/4096) p)
      = [ (32767/268435456, 557041/4294967296),
          (557041/4294967296, 294905/2147483648),
          (294905/2147483648, 163837/1073741824),
          (163837/1073741824, 98303/536870912),
          (98303/536870912, 1/4096) ] := by
  norm_num [root0Paths, bisect]

/-- Every other initial interval contributes a single leaf, its own empty path. -/
theorem trivial_path (lo hi : ℚ) : bisect lo hi [] = (lo, hi) := rfl

/-- Left-anchored adjacency: the first interval starts at `lo` and every
subsequent interval starts exactly where its predecessor ends. -/
def chainFrom : ℚ → List (ℚ × ℚ × Bool) → Prop
  | _, [] => True
  | lo, z :: t => z.1 = lo ∧ chainFrom z.2.1 t

/-- The right endpoint of the last interval of a chain. -/
def rightEnd : ℚ → List (ℚ × ℚ × Bool) → ℚ
  | lo, [] => lo
  | _, z :: t => rightEnd z.2.1 t

@[simp] theorem chainFrom_nil (lo : ℚ) : chainFrom lo [] ↔ True := Iff.rfl

@[simp] theorem chainFrom_cons (lo : ℚ) (z : ℚ × ℚ × Bool) (t : List (ℚ × ℚ × Bool)) :
    chainFrom lo (z :: t) ↔ (z.1 = lo ∧ chainFrom z.2.1 t) := Iff.rfl

@[simp] theorem rightEnd_nil (lo : ℚ) : rightEnd lo [] = lo := rfl

@[simp] theorem rightEnd_cons (lo : ℚ) (z : ℚ × ℚ × Bool) (t : List (ℚ × ℚ × Bool)) :
    rightEnd lo (z :: t) = rightEnd z.2.1 t := rfl

/-- The thirteen initial intervals chain exactly, from `K - A`. -/
theorem roots_chainFrom : chainFrom (Kq - Aq) roots :=
  ⟨by norm_num [Kq, Aq], rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, trivial⟩

theorem roots_rightEnd : rightEnd (Kq - Aq) roots = 1/2 := rfl

/-- **Adjacency.** All seventeen leaves chain exactly: each left endpoint is the
previous right endpoint, as an equality of rationals, and the first left endpoint
is exactly `K - A`. -/
theorem leaves_chainFrom : chainFrom (Kq - Aq) leaves :=
  ⟨by norm_num [Kq, Aq], rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, trivial⟩

/-- **Right end.** The last leaf ends exactly at `1/2`. -/
theorem leaves_rightEnd : rightEnd (Kq - Aq) leaves = 1/2 := rfl

/-- A chain of adjacent closed intervals covers the interval from its anchor to
its right end. -/
theorem exists_leaf_of_chain {x : ℝ} :
    ∀ (L : List (ℚ × ℚ × Bool)) (lo : ℚ), chainFrom lo L →
      (lo : ℝ) ≤ x → x ≤ ((rightEnd lo L : ℚ) : ℝ) →
      L = [] ∨ ∃ z ∈ L, ((z.1 : ℚ) : ℝ) ≤ x ∧ x ≤ ((z.2.1 : ℚ) : ℝ) := by
  intro L
  induction L with
  | nil => intro lo _ _ _; exact Or.inl rfl
  | cons z t ih =>
    intro lo hch hlo hhi
    obtain ⟨hz1, hch'⟩ := hch
    by_cases hcase : x ≤ ((z.2.1 : ℚ) : ℝ)
    · refine Or.inr ⟨z, by simp, ?_, hcase⟩
      rw [hz1]; exact hlo
    · rw [not_le] at hcase
      rw [rightEnd_cons] at hhi
      rcases ih z.2.1 hch' hcase.le hhi with h | ⟨w, hw, hw1, hw2⟩
      · subst h
        rw [rightEnd_nil] at hhi
        exact absurd hhi (not_le.2 hcase)
      · exact Or.inr ⟨w, List.mem_cons_of_mem _ hw, hw1, hw2⟩

/-- Each leaf sits inside the strip. -/
theorem leaf_endpoints_within {z : ℚ × ℚ × Bool} (hz : z ∈ leaves) :
    Kq - Aq ≤ z.1 ∧ z.2.1 ≤ 1/2 := by
  fin_cases hz <;> norm_num [Kq, Aq]

/-- **Exact partition coverage.**  A real number lies in the boundary strip
`[K - A, 1/2]` if and only if it lies in one of the seventeen archived leaves.
Together with `leaves_chainFrom` (adjacent endpoints coincide as rationals) and
`leaves_rightEnd` this is the exact binary-partition statement: the leaves leave
no gap and do not leave the strip. -/
theorem mem_strip_iff (x : ℝ) :
    (((Kq - Aq : ℚ) : ℝ) ≤ x ∧ x ≤ 1/2) ↔
      ∃ z ∈ leaves, ((z.1 : ℚ) : ℝ) ≤ x ∧ x ≤ ((z.2.1 : ℚ) : ℝ) := by
  constructor
  · rintro ⟨h1, h2⟩
    have hre : ((rightEnd (Kq - Aq) leaves : ℚ) : ℝ) = 1/2 := by
      rw [leaves_rightEnd]; norm_num
    rcases exists_leaf_of_chain leaves (Kq - Aq) leaves_chainFrom h1
      (by rw [hre]; exact h2) with h | h
    · exact absurd h (by simp [leaves])
    · exact h
  · rintro ⟨z, hz, h1, h2⟩
    obtain ⟨ha, hb⟩ := leaf_endpoints_within hz
    have ha' : ((Kq - Aq : ℚ) : ℝ) ≤ ((z.1 : ℚ) : ℝ) := by exact_mod_cast ha
    have hb' : ((z.2.1 : ℚ) : ℝ) ≤ ((1/2 : ℚ) : ℝ) := by exact_mod_cast hb
    push_cast at hb'
    exact ⟨le_trans ha' h1, le_trans h2 hb'⟩

/-- The ten middle initial intervals are exactly the dyadic blocks
`[2^{-k}, 2^{-(k-1)}]` for `k = 12, 11, …, 3`, as described in `PROOF.md`. -/
theorem roots_dyadic (k : ℕ) (h3 : 3 ≤ k) (h12 : k ≤ 12) :
    ((1:ℚ)/2^k, (1:ℚ)/2^(k-1), true) ∈ roots := by
  have hk : k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 ∨ k = 12 := by
    omega
  rcases hk with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> norm_num [roots]

/-- `K - A` is a lower bound for every leaf, and it is attained. -/
theorem leaves_left_min : ∀ z ∈ leaves, Kq - Aq ≤ z.1 :=
  fun _ hz => (leaf_endpoints_within hz).1

/-- `1/2` is an upper bound for every leaf, and it is attained. -/
theorem leaves_right_max : ∀ z ∈ leaves, z.2.1 ≤ 1/2 :=
  fun _ hz => (leaf_endpoints_within hz).2

theorem leaves_left_attained : ∃ z ∈ leaves, z.1 = Kq - Aq :=
  ⟨(32767/268435456, 557041/4294967296, true), by simp [leaves], strip_left⟩

theorem leaves_right_attained : ∃ z ∈ leaves, z.2.1 = 1/2 :=
  ⟨(2/5, 1/2, false), by simp [leaves], rfl⟩

/-- The structural preconditions asserted by the archived `gap` routine: on every
leaf the signed imbalance `q = l - A` is strictly positive, and every leaf that
uses the enhanced envelope (6) has `u ≤ 2/5`, which is what licenses it. -/
theorem leaf_branch_valid :
    ∀ z ∈ leaves, Aq < z.1 ∧ (z.2.2 = true → z.2.1 ≤ 2/5) := by
  intro z hz
  fin_cases hz
  · exact ⟨by norm_num [Aq], fun _ => by norm_num⟩
  · exact ⟨by norm_num [Aq], fun _ => by norm_num⟩
  · exact ⟨by norm_num [Aq], fun _ => by norm_num⟩
  · exact ⟨by norm_num [Aq], fun _ => by norm_num⟩
  · exact ⟨by norm_num [Aq], fun _ => by norm_num⟩
  · exact ⟨by norm_num [Aq], fun _ => by norm_num⟩
  · exact ⟨by norm_num [Aq], fun _ => by norm_num⟩
  · exact ⟨by norm_num [Aq], fun _ => by norm_num⟩
  · exact ⟨by norm_num [Aq], fun _ => by norm_num⟩
  · exact ⟨by norm_num [Aq], fun _ => by norm_num⟩
  · exact ⟨by norm_num [Aq], fun _ => by norm_num⟩
  · exact ⟨by norm_num [Aq], fun _ => by norm_num⟩
  · exact ⟨by norm_num [Aq], fun _ => by norm_num⟩
  · exact ⟨by norm_num [Aq], fun _ => by norm_num⟩
  · exact ⟨by norm_num [Aq], fun _ => by norm_num⟩
  · exact ⟨by norm_num [Aq], fun _ => by norm_num⟩
  · exact ⟨by norm_num [Aq], fun h => by simp at h⟩

/-! ## 2. Directed rational enclosures for `log₂` of a positive rational

`log₂ y` is pinned between rationals by *exact integer power comparisons*: no
numerical evaluation of a logarithm occurs anywhere below. -/

theorem log2_nat_le {b : ℕ} (hb : 0 < b) {p k : ℕ} (hk : 0 < k) (hpow : b ^ k ≤ 2 ^ p) :
    Real.log (b : ℝ) / Real.log 2 ≤ (p : ℝ) / (k : ℝ) := by
  have hbR : (0:ℝ) < (b:ℝ) := by exact_mod_cast hb
  have hkR : (0:ℝ) < (k:ℝ) := by exact_mod_cast hk
  have hpowR : (b:ℝ) ^ k ≤ (2:ℝ) ^ p := by exact_mod_cast hpow
  have hlog := Real.log_le_log (by positivity) hpowR
  rw [Real.log_pow, Real.log_pow] at hlog
  rw [div_le_div_iff₀ log_two_pos hkR]
  linarith [hlog]

theorem log2_div_le_of_pow_le {b c : ℕ} (hb : 0 < b) (hc : 0 < c) {p k : ℕ} (hk : 0 < k)
    (hpow : b ^ k ≤ 2 ^ p * c ^ k) :
    Real.log ((b : ℝ) / (c : ℝ)) / Real.log 2 ≤ (p : ℝ) / (k : ℝ) := by
  have hbR : (0:ℝ) < (b:ℝ) := by exact_mod_cast hb
  have hcR : (0:ℝ) < (c:ℝ) := by exact_mod_cast hc
  have hkR : (0:ℝ) < (k:ℝ) := by exact_mod_cast hk
  have hpowR : ((b:ℝ)/(c:ℝ)) ^ k ≤ (2:ℝ) ^ p := by
    rw [div_pow, div_le_iff₀ (by positivity)]
    exact_mod_cast hpow
  have hlog := Real.log_le_log (by positivity) hpowR
  rw [Real.log_pow, Real.log_pow] at hlog
  rw [div_le_div_iff₀ log_two_pos hkR]
  linarith [hlog]

theorem le_log2_div_of_pow_le {b c : ℕ} (hb : 0 < b) (hc : 0 < c) {p k : ℕ} (hk : 0 < k)
    (hpow : 2 ^ p * c ^ k ≤ b ^ k) :
    (p : ℝ) / (k : ℝ) ≤ Real.log ((b : ℝ) / (c : ℝ)) / Real.log 2 := by
  have hbR : (0:ℝ) < (b:ℝ) := by exact_mod_cast hb
  have hcR : (0:ℝ) < (c:ℝ) := by exact_mod_cast hc
  have hkR : (0:ℝ) < (k:ℝ) := by exact_mod_cast hk
  have hpowR : (2:ℝ) ^ p ≤ ((b:ℝ)/(c:ℝ)) ^ k := by
    rw [div_pow, le_div_iff₀ (by positivity)]
    exact_mod_cast hpow
  have hlog := Real.log_le_log (by positivity) hpowR
  rw [Real.log_pow, Real.log_pow] at hlog
  rw [div_le_div_iff₀ hkR log_two_pos]
  linarith [hlog]

/-! ## 3. Elementary rational envelopes for `H` -/

theorem H_eq (v : ℝ) :
    H v = (v * Real.log v⁻¹ + (1 - v) * Real.log (1 - v)⁻¹) / Real.log 2 := rfl

theorem H_ge_first {v : ℝ} (hv0 : 0 < v) (hv1 : v < 1) :
    v * (Real.log v⁻¹ / Real.log 2) ≤ H v := by
  have hnn : 0 ≤ Real.log (1 - v)⁻¹ := by
    rw [Real.log_inv]
    have := Real.log_nonpos (by linarith : (0:ℝ) ≤ 1 - v) (by linarith : (1:ℝ) - v ≤ 1)
    linarith
  have h2 : 0 ≤ (1 - v) * Real.log (1 - v)⁻¹ := mul_nonneg (by linarith) hnn
  have hrw : v * (Real.log v⁻¹ / Real.log 2) = (v * Real.log v⁻¹) / Real.log 2 := by ring
  rw [hrw, H_eq]
  exact (div_le_div_iff_of_pos_right log_two_pos).2 (by linarith)

theorem H_le_of_log_bounds {v c d : ℝ} (hv0 : 0 < v) (hv1 : v < 1)
    (hc : Real.log v⁻¹ / Real.log 2 ≤ c) (hd : Real.log (1 - v)⁻¹ / Real.log 2 ≤ d) :
    H v ≤ v * c + (1 - v) * d := by
  have hlog2 := log_two_pos
  have e1 : Real.log v⁻¹ ≤ c * Real.log 2 := by rw [div_le_iff₀ hlog2] at hc; linarith
  have e2 : Real.log (1 - v)⁻¹ ≤ d * Real.log 2 := by rw [div_le_iff₀ hlog2] at hd; linarith
  rw [H_eq, div_le_iff₀ hlog2]
  nlinarith [mul_le_mul_of_nonneg_left e1 hv0.le,
    mul_le_mul_of_nonneg_left e2 (by linarith : (0:ℝ) ≤ 1 - v)]

/-- The complementary entropy term is bounded by `v / log 2 ≤ 1.4427 v`. -/
theorem H_le_of_log_bound {v c : ℝ} (hv0 : 0 < v) (hv1 : v < 1)
    (hc : Real.log v⁻¹ / Real.log 2 ≤ c) :
    H v ≤ v * c + v * (14427/10000) := by
  have hlog2 := log_two_pos
  have hpos : (0:ℝ) < 1 - v := by linarith
  have hne : (1:ℝ) - v ≠ 0 := ne_of_gt hpos
  have h1 : Real.log (1 - v)⁻¹ ≤ (1 - v)⁻¹ - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  have h2 : (1 - v)⁻¹ - 1 = v / (1 - v) := by field_simp; ring
  have h3 : Real.log (1 - v)⁻¹ ≤ v / (1 - v) := by rw [h2] at h1; exact h1
  have hvq : (0:ℝ) ≤ v / (1 - v) := le_of_lt (div_pos hv0 hpos)
  have hd : Real.log (1 - v)⁻¹ / Real.log 2 ≤ (14427/10000) * (v / (1 - v)) := by
    rw [div_le_iff₀ hlog2]
    nlinarith [Real.log_two_gt_d9, hvq, h3]
  have key := H_le_of_log_bounds hv0 hv1 hc hd
  have hsimp : (1 - v) * ((14427/10000) * (v / (1 - v))) = v * (14427/10000) := by
    field_simp
  rw [hsimp] at key
  exact key

theorem H_quarter_ge : (1/2 : ℝ) ≤ H (1/4) := by
  have h := H_ge_first (v := 1/4) (by norm_num) (by norm_num)
  have e0 : ((1:ℝ)/4)⁻¹ = 2 ^ (2:ℕ) := by norm_num
  have e1 : Real.log ((1:ℝ)/4)⁻¹ = 2 * Real.log 2 := by rw [e0, Real.log_pow]; norm_num
  have e2 : (2 * Real.log 2) / Real.log 2 = 2 := by field_simp
  rw [e1, e2] at h
  linarith

/-! ## 4. Packaged rational bounds for `H` and `J` -/

theorem H_le_of_pow {v : ℝ} (hv0 : 0 < v) (hv1 : v < 1) {b : ℕ} (hb : 0 < b)
    (hvb : v⁻¹ = (b : ℝ)) {p k : ℕ} (hk : 0 < k) (hpow : b ^ k ≤ 2 ^ p)
    {t : ℝ} (ht : v * ((p : ℝ) / (k : ℝ)) + v * (14427/10000) ≤ t) :
    H v ≤ t := by
  refine le_trans (H_le_of_log_bound hv0 hv1 ?_) ht
  rw [hvb]; exact log2_nat_le hb hk hpow

theorem J_le_of_pow {v : ℝ} {b : ℕ} (hb : 0 < b)
    (hvb : (1 - v) / v = (b : ℝ)) {p k : ℕ} (hk : 0 < k) (hpow : b ^ k ≤ 2 ^ p)
    {t : ℝ} (ht : (p : ℝ) / (k : ℝ) ≤ t) :
    J v ≤ t := by
  rw [J, hvb]; exact le_trans (log2_nat_le hb hk hpow) ht

theorem le_J_of_pow {u : ℝ} {b c : ℕ} (hb : 0 < b) (hc : 0 < c)
    (hub : (1 - u) / u = (b : ℝ) / (c : ℝ)) {p k : ℕ} (hk : 0 < k)
    (hpow : 2 ^ p * c ^ k ≤ b ^ k) {t : ℝ} (ht : t ≤ (p : ℝ) / (k : ℝ)) :
    t ≤ J u := by
  rw [J, hub]; exact le_trans ht (le_log2_div_of_pow_le hb hc hk hpow)

/-! ## 5. The boundary-strip comparison functions -/

/-- `A = 2⁻²⁸`, the extreme-mean cap of the archived strip theorem. -/
noncomputable def Ac : ℝ := 1/268435456

/-- `C q = 1 - H((1-q)/2)`, the capacity of a binary symmetric channel with
crossover `(1-q)/2`. -/
noncomputable def Ccap (q : ℝ) : ℝ := 1 - H ((1 - q)/2)

/-- The cost lower bound (4) of `PROOF.md`: `½(1-u-A)(J A + J u)`. -/
noncomputable def stripCost (u : ℝ) : ℝ := (1 - u - Ac)/2 * (J Ac + J u)

/-- The psi-branch upper envelope of `PROOF.md`: `η(q/8 + C q)` in the enhanced
branch (6) and `η(C q)` in the plain branch (5), at `q = l - A`. -/
noncomputable def stripPsi (l : ℝ) (enhanced : Bool) : ℝ :=
  eta (Ccap (l - Ac) + (if enhanced then (l - Ac)/8 else 0))

/-- `J(2⁻²⁸) = log₂(2²⁸ - 1)` is within `10⁻⁸` of `28`. -/
theorem J_Ac_ge : (28 : ℝ) - 1/100000000 ≤ J Ac := by
  have hlog2 := log_two_pos
  have hx : (0:ℝ) < 268435455/268435456 := by norm_num
  have hb := Real.one_sub_inv_le_log_of_pos hx
  have hinv : ((268435455:ℝ)/268435456)⁻¹ = 268435456/268435455 := by norm_num
  rw [hinv] at hb
  have hpow : (268435456:ℝ) = 2 ^ (28:ℕ) := by norm_num
  have hsplit : Real.log ((268435455:ℝ)/268435456) = Real.log 268435455 - 28 * Real.log 2 := by
    rw [Real.log_div (by norm_num) (by norm_num), hpow, Real.log_pow]
    norm_num
  have hJ : J Ac = Real.log 268435455 / Real.log 2 := by
    rw [J]
    congr 1
    norm_num [Ac]
  rw [hJ, le_div_iff₀ hlog2]
  have hb2 : (28:ℝ) * Real.log 2 - 1/268435455 ≤ Real.log 268435455 := by
    rw [hsplit] at hb; linarith [hb]
  nlinarith [Real.log_two_gt_d9, hb2]

theorem Ccap_eq {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Ccap q = ((1 - q) * Real.log (1 - q) + (1 + q) * Real.log (1 + q)) / (2 * Real.log 2) := by
  have hlog2 := log_two_pos
  have hne : Real.log 2 ≠ 0 := ne_of_gt hlog2
  have h1 : (0:ℝ) < 1 - q := by linarith
  have h2 : (0:ℝ) < 1 + q := by linarith
  have e1 : Real.log (((1:ℝ) - q)/2)⁻¹ = Real.log 2 - Real.log (1 - q) := by
    rw [Real.log_inv, Real.log_div (ne_of_gt h1) (by norm_num)]; ring
  have e2 : ((1:ℝ) - (1 - q)/2) = (1 + q)/2 := by ring
  have e3 : Real.log (((1:ℝ) + q)/2)⁻¹ = Real.log 2 - Real.log (1 + q) := by
    rw [Real.log_inv, Real.log_div (ne_of_gt h2) (by norm_num)]; ring
  rw [Ccap, H_eq, e2, e1, e3]
  field_simp
  ring

theorem Ccap_nonneg {q : ℝ} : 0 ≤ Ccap q := by
  have := H_le_one ((1 - q)/2)
  rw [Ccap]; linarith

theorem Ccap_le_one {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1/2) : Ccap q ≤ 1 := by
  have := H_nonneg (by linarith : (0:ℝ) ≤ (1 - q)/2) (by linarith : (1 - q)/2 ≤ 1)
  rw [Ccap]; linarith

theorem Ccap_add_eighth_le_one {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1/2) :
    Ccap q + q/8 ≤ 1 := by
  have hmono : H (1/4) ≤ H ((1 - q)/2) :=
    H_strictMonoOn.monotoneOn ⟨by norm_num, by norm_num⟩
      ⟨by linarith, by linarith⟩ (by linarith)
  have hq4 := H_quarter_ge
  rw [Ccap]; linarith

/-- The kernel-checkable rational lower bound `C q ≥ (7/10) q² (1-2q)` on `[0,½]`,
obtained from `log x ≥ 1 - 1/x` applied to `1-q²`, `1+q` and `(1-q)⁻¹`. -/
theorem Ccap_lower {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1/2) :
    7/10 * q^2 * (1 - 2*q) ≤ Ccap q := by
  have hlog2 := log_two_pos
  have h1 : (0:ℝ) < 1 - q := by linarith
  have h2 : (0:ℝ) < 1 + q := by linarith
  have hs : (0:ℝ) < (1 - q) * (1 + q) := mul_pos h1 h2
  have hsq : (0:ℝ) < 1 - q^2 := by nlinarith
  have hqq : (0:ℝ) ≤ q * (1/2 - q) := mul_nonneg hq0 (by linarith)
  have h1qq : (0:ℝ) ≤ 1 - q - q^2 := by nlinarith
  have hfac : (0:ℝ) ≤ q^2 * (1 - q - q^2) := mul_nonneg (sq_nonneg q) h1qq
  have eF : (1 - q) * Real.log (1 - q) + (1 + q) * Real.log (1 + q)
      = Real.log ((1 - q) * (1 + q)) + q * (Real.log (1 + q) - Real.log (1 - q)) := by
    rw [Real.log_mul (ne_of_gt h1) (ne_of_gt h2)]; ring
  have b1 : 1 - ((1 - q) * (1 + q))⁻¹ ≤ Real.log ((1 - q) * (1 + q)) :=
    Real.one_sub_inv_le_log_of_pos hs
  have b2 : 1 - (1 + q)⁻¹ ≤ Real.log (1 + q) := Real.one_sub_inv_le_log_of_pos h2
  have b3 : q ≤ -Real.log (1 - q) := by
    have h := Real.one_sub_inv_le_log_of_pos (show (0:ℝ) < (1 - q)⁻¹ by positivity)
    rw [inv_inv, Real.log_inv] at h
    linarith
  have hi1 : ((1 - q) * (1 + q))⁻¹ = 1/(1 - q^2) := by
    rw [inv_eq_one_div]; congr 1; ring
  have hi2 : ((1:ℝ) + q)⁻¹ = 1/(1 + q) := inv_eq_one_div _
  have hF : q^2 * (1 - q - q^2) ≤ (1 - q) * Real.log (1 - q) + (1 + q) * Real.log (1 + q) := by
    have hb1' : 1 - 1/(1 - q^2) ≤ Real.log ((1 - q) * (1 + q)) := by rw [← hi1]; exact b1
    have hb2' : 1 - 1/(1 + q) + q ≤ Real.log (1 + q) - Real.log (1 - q) := by
      rw [← hi2]; linarith
    have hmul : q * (1 - 1/(1 + q) + q) ≤ q * (Real.log (1 + q) - Real.log (1 - q)) :=
      mul_le_mul_of_nonneg_left hb2' hq0
    have e : 1 - 1/(1 - q^2) + q * (1 - 1/(1 + q) + q) = q^2 * (1 - q - q^2)/(1 - q^2) := by
      field_simp
      ring
    have key : q^2 * (1 - q - q^2) ≤ 1 - 1/(1 - q^2) + q * (1 - 1/(1 + q) + q) := by
      rw [e, le_div_iff₀ hsq]
      nlinarith [mul_nonneg hfac (sq_nonneg q)]
    rw [eF]
    linarith
  have hCeq := Ccap_eq hq0 (by linarith)
  have hden : (0:ℝ) < 2 * Real.log 2 := by linarith
  have hA : (0:ℝ) ≤ 7/10 * q^2 * (1 - 2*q) :=
    mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg q)) (by linarith)
  have hstep1 : 7/10 * q^2 * (1 - 2*q) * (2 * Real.log 2)
      ≤ 7/10 * q^2 * (1 - 2*q) * (13862943616/10000000000) :=
    mul_le_mul_of_nonneg_left (by linarith [Real.log_two_lt_d9]) hA
  have hbr : (0:ℝ) ≤ 2959394688/100000000000 + (94081210624/100000000000) * q - q^2 := by
    nlinarith
  have hident : q^2 * (1 - q - q^2) - 7/10 * q^2 * (1 - 2*q) * (13862943616/10000000000)
      = q^2 * (2959394688/100000000000 + (94081210624/100000000000) * q - q^2) := by ring
  have hstep2 : 7/10 * q^2 * (1 - 2*q) * (13862943616/10000000000) ≤ q^2 * (1 - q - q^2) := by
    nlinarith [mul_nonneg (sq_nonneg q) hbr]
  rw [hCeq, le_div_iff₀ hden]
  linarith

/-- Power-checked lower bound for `C` at `q = 2/5 - A`, the left endpoint of the
one initial interval that uses the plain envelope (5). -/
theorem Ccap_two_fifths : (29658443/250120000 : ℝ) ≤ Ccap (2/5 - Ac) := by
  have hp : (1 - (2/5 - Ac))/2 = 3/10 + Ac/2 := by ring
  have hmono : H (3/10 + Ac/2) ≤ H (3001/10000) :=
    H_strictMonoOn.monotoneOn ⟨by norm_num [Ac], by norm_num [Ac]⟩
      ⟨by norm_num, by norm_num⟩ (by norm_num [Ac])
  have hHb : H ((3001:ℝ)/10000) ≤ 3001/10000 * (257/148) + (1 - 3001/10000) * (87/169) := by
    refine H_le_of_log_bounds (by norm_num) (by norm_num) ?_ ?_
    · have e : ((3001:ℝ)/10000)⁻¹ = ((10000:ℕ):ℝ)/((3001:ℕ):ℝ) := by norm_num
      rw [e]
      exact le_trans (log2_div_le_of_pow_le (b := 10000) (c := 3001) (p := 257) (k := 148)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
    · have e : ((1:ℝ) - 3001/10000)⁻¹ = ((10000:ℕ):ℝ)/((6999:ℕ):ℝ) := by norm_num
      rw [e]
      exact le_trans (log2_div_le_of_pow_le (b := 10000) (c := 6999) (p := 87) (k := 169)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)) (by norm_num)
  rw [Ccap, hp]
  linarith

/-- `J` is odd about `1/2`. -/
theorem J_one_sub {x : ℝ} (hx0 : 0 < x) (_hx1 : x < 1) : J (1 - x) = - J x := by
  have h1 : (1:ℝ) - (1 - x) = x := by ring
  rw [J, J, ← neg_div, h1]
  congr 1
  rw [← Real.log_inv]
  congr 1
  field_simp

/-- `stripCost u` is exactly the repository's interior edge cost between the
extreme mean `A` and the reflected mean `1 - u`, i.e. the right-hand side of
inequality (3)–(4) of `PROOF.md`. -/
theorem stripCost_eq_interiorCost {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    stripCost u = interiorCost Ac (1 - u) := by
  rw [stripCost, interiorCost, J_one_sub hu0 hu1]
  ring

/-! ## 6. `η` upper bound from a rational entropy-inverse witness -/

/-- If `v ∈ (0,½]` is a rational witness with `H v ≤ h ≤ 1`, then `η h` is bounded
above by the exactly computable quantity `(1-2v) J v`.  This is the only place
where the entropy inverse enters, and it enters through `H` alone. -/
theorem eta_le_of_H_le {h v : ℝ} (hv0 : 0 < v) (hvh : v ≤ 1/2) (hh1 : h ≤ 1)
    (hHv : H v ≤ h) : eta h ≤ (1 - 2*v) * J v := by
  have hv1 : v < 1 := lt_of_le_of_lt hvh (by norm_num)
  have hHpos : 0 < H v := H_pos hv0 hv1
  have hh0 : 0 < h := lt_of_lt_of_le hHpos hHv
  have key := eta_antitoneOn (Set.mem_Ioc.2 ⟨hHpos, H_le_one v⟩)
    (Set.mem_Ioc.2 ⟨hh0, hh1⟩) hHv
  rwa [eta_eq_profile hHpos.le (H_le_one v), entropyInverse_H_lower hv0.le hvh] at key

/-! ## 7. The master per-leaf certificate -/

/-- The directed comparison for a single leaf `[l,u]`, assembled from
kernel-checked rational data: a lower bound `cL` for `C (l-A)`, an entropy-inverse
witness `v`, a rational upper bound `c2` for `J v`, and a rational lower bound
`jU` for `J u`. -/
theorem leaf_gap {l u v cL c2 jU : ℝ} {enh : Bool}
    (hq0 : 0 ≤ l - Ac) (hq : l - Ac ≤ 1/2)
    (hcL : cL ≤ Ccap (l - Ac))
    (hv0 : 0 < v) (hvh : v ≤ 1/2)
    (hHv : H v ≤ cL + (if enh then (l - Ac)/8 else 0))
    (hJv : J v ≤ c2)
    (hu : 0 < 1 - u - Ac)
    (hjU : jU ≤ J u)
    (hfin : (1 - 2*v) * c2 < (1 - u - Ac)/2 * ((28 - 1/100000000) + jU)) :
    stripPsi l enh < stripCost u := by
  have hh1 : Ccap (l - Ac) + (if enh then (l - Ac)/8 else 0) ≤ 1 := by
    cases enh with
    | true => simpa using Ccap_add_eighth_le_one hq0 hq
    | false => simpa using Ccap_le_one hq0 hq
  have hHle : H v ≤ Ccap (l - Ac) + (if enh then (l - Ac)/8 else 0) := by
    refine hHv.trans ?_
    cases enh with
    | true => simpa using by linarith [hcL]
    | false => simpa using by linarith [hcL]
  have heta := eta_le_of_H_le hv0 hvh hh1 hHle
  have hfac : (0:ℝ) ≤ 1 - 2*v := by linarith
  have h2 : (1 - 2*v) * J v ≤ (1 - 2*v) * c2 := mul_le_mul_of_nonneg_left hJv hfac
  have hcost : (1 - u - Ac)/2 * ((28 - 1/100000000) + jU) ≤ stripCost u := by
    rw [stripCost]
    exact mul_le_mul_of_nonneg_left (by linarith [J_Ac_ge]) (by linarith)
  rw [stripPsi]
  linarith

/-! ## 8. The seventeen leaf certificates

Each leaf reproduces the archived comparison `gap(pair, enhanced) > 0` of
`BOUNDARY_STRIP.py` with exact rational witnesses. -/

/-- Leaf 0 of the archived certificate: `x ∈ [32767/268435456, 557041/4294967296]`,
enhanced branch, entropy-inverse witness `1/1433974`. -/
theorem leaf00 :
    stripPsi (32767/268435456) true < stripCost (557041/4294967296) := by
  refine leaf_gap (v := (1433974:ℝ)⁻¹)
    (cL := 7/10 * (32767/268435456 - Ac)^2 * (1 - 2*(32767/268435456 - Ac)))
    (c2 := 634/31) (jU := 2505/194)
    (by norm_num [Ac]) (by norm_num [Ac])
    (Ccap_lower (by norm_num [Ac]) (by norm_num [Ac]))
    (by norm_num) (by norm_num) ?_ ?_ (by norm_num [Ac]) ?_ (by norm_num [Ac])
  · exact H_le_of_pow (b := 1433974) (p := 634) (k := 31) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Ac])
  · exact J_le_of_pow (b := 1433973) (p := 634) (k := 31) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  · exact le_J_of_pow (b := 4294410255) (c := 557041) (p := 2505) (k := 194)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Leaf 1 of the archived certificate: `x ∈ [557041/4294967296, 294905/2147483648]`,
enhanced branch, entropy-inverse witness `1/1343781`. -/
theorem leaf01 :
    stripPsi (557041/4294967296) true < stripCost (294905/2147483648) := by
  refine leaf_gap (v := (1343781:ℝ)⁻¹)
    (cL := 7/10 * (557041/4294967296 - Ac)^2 * (1 - 2*(557041/4294967296 - Ac)))
    (c2 := 1934/95) (jU := 2489/194)
    (by norm_num [Ac]) (by norm_num [Ac])
    (Ccap_lower (by norm_num [Ac]) (by norm_num [Ac]))
    (by norm_num) (by norm_num) ?_ ?_ (by norm_num [Ac]) ?_ (by norm_num [Ac])
  · exact H_le_of_pow (b := 1343781) (p := 1934) (k := 95) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Ac])
  · exact J_le_of_pow (b := 1343780) (p := 1934) (k := 95) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  · exact le_J_of_pow (b := 2147188743) (c := 294905) (p := 2489) (k := 194)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Leaf 2 of the archived certificate: `x ∈ [294905/2147483648, 163837/1073741824]`,
enhanced branch, entropy-inverse witness `1/1263921`. -/
theorem leaf02 :
    stripPsi (294905/2147483648) true < stripCost (163837/1073741824) := by
  refine leaf_gap (v := (1263921:ℝ)⁻¹)
    (cL := 7/10 * (294905/2147483648 - Ac)^2 * (1 - 2*(294905/2147483648 - Ac)))
    (c2 := 2858/141) (jU := 1889/149)
    (by norm_num [Ac]) (by norm_num [Ac])
    (Ccap_lower (by norm_num [Ac]) (by norm_num [Ac]))
    (by norm_num) (by norm_num) ?_ ?_ (by norm_num [Ac]) ?_ (by norm_num [Ac])
  · exact H_le_of_pow (b := 1263921) (p := 2858) (k := 141) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Ac])
  · exact J_le_of_pow (b := 1263920) (p := 2858) (k := 141) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  · exact le_J_of_pow (b := 1073577987) (c := 163837) (p := 1889) (k := 149)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Leaf 3 of the archived certificate: `x ∈ [163837/1073741824, 98303/536870912]`,
enhanced branch, entropy-inverse witness `1/1128886`. -/
theorem leaf03 :
    stripPsi (163837/1073741824) true < stripCost (98303/536870912) := by
  refine leaf_gap (v := (1128886:ℝ)⁻¹)
    (cL := 7/10 * (163837/1073741824 - Ac)^2 * (1 - 2*(163837/1073741824 - Ac)))
    (c2 := 4343/216) (jU := 2185/176)
    (by norm_num [Ac]) (by norm_num [Ac])
    (Ccap_lower (by norm_num [Ac]) (by norm_num [Ac]))
    (by norm_num) (by norm_num) ?_ ?_ (by norm_num [Ac]) ?_ (by norm_num [Ac])
  · exact H_le_of_pow (b := 1128886) (p := 2453) (k := 122) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Ac])
  · exact J_le_of_pow (b := 1128885) (p := 4343) (k := 216) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  · exact le_J_of_pow (b := 536772609) (c := 98303) (p := 2185) (k := 176)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Leaf 4 of the archived certificate: `x ∈ [98303/536870912, 1/4096]`,
enhanced branch, entropy-inverse witness `1/928241`. -/
theorem leaf04 :
    stripPsi (98303/536870912) true < stripCost (1/4096) := by
  refine leaf_gap (v := (928241:ℝ)⁻¹)
    (cL := 7/10 * (98303/536870912 - Ac)^2 * (1 - 2*(98303/536870912 - Ac)))
    (c2 := 1804/91) (jU := 3599/300)
    (by norm_num [Ac]) (by norm_num [Ac])
    (Ccap_lower (by norm_num [Ac]) (by norm_num [Ac]))
    (by norm_num) (by norm_num) ?_ ?_ (by norm_num [Ac]) ?_ (by norm_num [Ac])
  · exact H_le_of_pow (b := 928241) (p := 1804) (k := 91) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Ac])
  · exact J_le_of_pow (b := 928240) (p := 1804) (k := 91) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  · exact le_J_of_pow (b := 4095) (c := 1) (p := 3599) (k := 300)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Leaf 5 of the archived certificate: `x ∈ [1/4096, 1/2048]`,
enhanced branch, entropy-inverse witness `1/681334`. -/
theorem leaf05 :
    stripPsi (1/4096) true < stripCost (1/2048) := by
  refine leaf_gap (v := (681334:ℝ)⁻¹)
    (cL := 7/10 * (1/4096 - Ac)^2 * (1 - 2*(1/4096 - Ac)))
    (c2 := 5639/291) (jU := 3299/300)
    (by norm_num [Ac]) (by norm_num [Ac])
    (Ccap_lower (by norm_num [Ac]) (by norm_num [Ac]))
    (by norm_num) (by norm_num) ?_ ?_ (by norm_num [Ac]) ?_ (by norm_num [Ac])
  · exact H_le_of_pow (b := 681334) (p := 1589) (k := 82) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Ac])
  · exact J_le_of_pow (b := 681333) (p := 5639) (k := 291) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  · exact le_J_of_pow (b := 2047) (c := 1) (p := 3299) (k := 300)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Leaf 6 of the archived certificate: `x ∈ [1/2048, 1/1024]`,
enhanced branch, entropy-inverse witness `1/322575`. -/
theorem leaf06 :
    stripPsi (1/2048) true < stripCost (1/1024) := by
  refine leaf_gap (v := (322575:ℝ)⁻¹)
    (cL := 7/10 * (1/2048 - Ac)^2 * (1 - 2*(1/2048 - Ac)))
    (c2 := 5197/284) (jU := 2999/300)
    (by norm_num [Ac]) (by norm_num [Ac])
    (Ccap_lower (by norm_num [Ac]) (by norm_num [Ac]))
    (by norm_num) (by norm_num) ?_ ?_ (by norm_num [Ac]) ?_ (by norm_num [Ac])
  · exact H_le_of_pow (b := 322575) (p := 2690) (k := 147) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Ac])
  · exact J_le_of_pow (b := 322574) (p := 5197) (k := 284) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  · exact le_J_of_pow (b := 1023) (c := 1) (p := 2999) (k := 300)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Leaf 7 of the archived certificate: `x ∈ [1/1024, 1/512]`,
enhanced branch, entropy-inverse witness `1/152005`. -/
theorem leaf07 :
    stripPsi (1/1024) true < stripCost (1/512) := by
  refine leaf_gap (v := (152005:ℝ)⁻¹)
    (cL := 7/10 * (1/1024 - Ac)^2 * (1 - 2*(1/1024 - Ac)))
    (c2 := 4751/276) (jU := 2699/300)
    (by norm_num [Ac]) (by norm_num [Ac])
    (Ccap_lower (by norm_num [Ac]) (by norm_num [Ac]))
    (by norm_num) (by norm_num) ?_ ?_ (by norm_num [Ac]) ?_ (by norm_num [Ac])
  · exact H_le_of_pow (b := 152005) (p := 2496) (k := 145) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Ac])
  · exact J_le_of_pow (b := 152004) (p := 4751) (k := 276) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  · exact le_J_of_pow (b := 511) (c := 1) (p := 2699) (k := 300)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Leaf 8 of the archived certificate: `x ∈ [1/512, 1/256]`,
enhanced branch, entropy-inverse witness `1/71157`. -/
theorem leaf08 :
    stripPsi (1/512) true < stripCost (1/256) := by
  refine leaf_gap (v := (71157:ℝ)⁻¹)
    (cL := 7/10 * (1/512 - Ac)^2 * (1 - 2*(1/512 - Ac)))
    (c2 := 4481/278) (jU := 1415/177)
    (by norm_num [Ac]) (by norm_num [Ac])
    (Ccap_lower (by norm_num [Ac]) (by norm_num [Ac]))
    (by norm_num) (by norm_num) ?_ ?_ (by norm_num [Ac]) ?_ (by norm_num [Ac])
  · exact H_le_of_pow (b := 71157) (p := 2579) (k := 160) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Ac])
  · exact J_le_of_pow (b := 71156) (p := 4481) (k := 278) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  · exact le_J_of_pow (b := 255) (c := 1) (p := 1415) (k := 177)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Leaf 9 of the archived certificate: `x ∈ [1/256, 1/128]`,
enhanced branch, entropy-inverse witness `1/32978`. -/
theorem leaf09 :
    stripPsi (1/256) true < stripCost (1/128) := by
  refine leaf_gap (v := (32978:ℝ)⁻¹)
    (cL := 7/10 * (1/256 - Ac)^2 * (1 - 2*(1/256 - Ac)))
    (c2 := 1636/109) (jU := 1852/265)
    (by norm_num [Ac]) (by norm_num [Ac])
    (Ccap_lower (by norm_num [Ac]) (by norm_num [Ac]))
    (by norm_num) (by norm_num) ?_ ?_ (by norm_num [Ac]) ?_ (by norm_num [Ac])
  · exact H_le_of_pow (b := 32978) (p := 1621) (k := 108) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Ac])
  · exact J_le_of_pow (b := 32977) (p := 1636) (k := 109) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  · exact le_J_of_pow (b := 127) (c := 1) (p := 1852) (k := 265)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Leaf 10 of the archived certificate: `x ∈ [1/128, 1/64]`,
enhanced branch, entropy-inverse witness `1/15040`. -/
theorem leaf10 :
    stripPsi (1/128) true < stripCost (1/64) := by
  refine leaf_gap (v := (15040:ℝ)⁻¹)
    (cL := 7/10 * (1/128 - Ac)^2 * (1 - 2*(1/128 - Ac)))
    (c2 := 3594/259) (jU := 263/44)
    (by norm_num [Ac]) (by norm_num [Ac])
    (Ccap_lower (by norm_num [Ac]) (by norm_num [Ac]))
    (by norm_num) (by norm_num) ?_ ?_ (by norm_num [Ac]) ?_ (by norm_num [Ac])
  · exact H_le_of_pow (b := 15040) (p := 1124) (k := 81) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Ac])
  · exact J_le_of_pow (b := 15039) (p := 3594) (k := 259) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  · exact le_J_of_pow (b := 63) (c := 1) (p := 263) (k := 44)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Leaf 11 of the archived certificate: `x ∈ [1/64, 1/32]`,
enhanced branch, entropy-inverse witness `1/6678`. -/
theorem leaf11 :
    stripPsi (1/64) true < stripCost (1/32) := by
  refine leaf_gap (v := (6678:ℝ)⁻¹)
    (cL := 7/10 * (1/64 - Ac)^2 * (1 - 2*(1/64 - Ac)))
    (c2 := 2541/200) (jU := 1189/240)
    (by norm_num [Ac]) (by norm_num [Ac])
    (Ccap_lower (by norm_num [Ac]) (by norm_num [Ac]))
    (by norm_num) (by norm_num) ?_ ?_ (by norm_num [Ac]) ?_ (by norm_num [Ac])
  · exact H_le_of_pow (b := 6678) (p := 1207) (k := 95) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Ac])
  · exact J_le_of_pow (b := 6677) (p := 2541) (k := 200) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  · exact le_J_of_pow (b := 31) (c := 1) (p := 1189) (k := 240)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Leaf 12 of the archived certificate: `x ∈ [1/32, 1/16]`,
enhanced branch, entropy-inverse witness `1/2841`. -/
theorem leaf12 :
    stripPsi (1/32) true < stripCost (1/16) := by
  refine leaf_gap (v := (2841:ℝ)⁻¹)
    (cL := 7/10 * (1/32 - Ac)^2 * (1 - 2*(1/32 - Ac)))
    (c2 := 608/53) (jU := 965/247)
    (by norm_num [Ac]) (by norm_num [Ac])
    (Ccap_lower (by norm_num [Ac]) (by norm_num [Ac]))
    (by norm_num) (by norm_num) ?_ ?_ (by norm_num [Ac]) ?_ (by norm_num [Ac])
  · exact H_le_of_pow (b := 2841) (p := 413) (k := 36) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Ac])
  · exact J_le_of_pow (b := 2840) (p := 608) (k := 53) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  · exact le_J_of_pow (b := 15) (c := 1) (p := 965) (k := 247)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Leaf 13 of the archived certificate: `x ∈ [1/16, 1/8]`,
enhanced branch, entropy-inverse witness `1/1136`. -/
theorem leaf13 :
    stripPsi (1/16) true < stripCost (1/8) := by
  refine leaf_gap (v := (1136:ℝ)⁻¹)
    (cL := 7/10 * (1/16 - Ac)^2 * (1 - 2*(1/16 - Ac)))
    (c2 := 1025/101) (jU := 306/109)
    (by norm_num [Ac]) (by norm_num [Ac])
    (Ccap_lower (by norm_num [Ac]) (by norm_num [Ac]))
    (by norm_num) (by norm_num) ?_ ?_ (by norm_num [Ac]) ?_ (by norm_num [Ac])
  · exact H_le_of_pow (b := 1136) (p := 203) (k := 20) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Ac])
  · exact J_le_of_pow (b := 1135) (p := 1025) (k := 101) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  · exact le_J_of_pow (b := 7) (c := 1) (p := 306) (k := 109)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Leaf 14 of the archived certificate: `x ∈ [1/8, 1/4]`,
enhanced branch, entropy-inverse witness `1/428`. -/
theorem leaf14 :
    stripPsi (1/8) true < stripCost (1/4) := by
  refine leaf_gap (v := (428:ℝ)⁻¹)
    (cL := 7/10 * (1/8 - Ac)^2 * (1 - 2*(1/8 - Ac)))
    (c2 := 367/42) (jU := 84/53)
    (by norm_num [Ac]) (by norm_num [Ac])
    (Ccap_lower (by norm_num [Ac]) (by norm_num [Ac]))
    (by norm_num) (by norm_num) ?_ ?_ (by norm_num [Ac]) ?_ (by norm_num [Ac])
  · exact H_le_of_pow (b := 428) (p := 1285) (k := 147) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Ac])
  · exact J_le_of_pow (b := 427) (p := 367) (k := 42) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  · exact le_J_of_pow (b := 3) (c := 1) (p := 84) (k := 53)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Leaf 15 of the archived certificate: `x ∈ [1/4, 2/5]`,
enhanced branch, entropy-inverse witness `1/166`. -/
theorem leaf15 :
    stripPsi (1/4) true < stripCost (2/5) := by
  refine leaf_gap (v := (166:ℝ)⁻¹)
    (cL := 7/10 * (1/4 - Ac)^2 * (1 - 2*(1/4 - Ac)))
    (c2 := 744/101) (jU := 31/53)
    (by norm_num [Ac]) (by norm_num [Ac])
    (Ccap_lower (by norm_num [Ac]) (by norm_num [Ac]))
    (by norm_num) (by norm_num) ?_ ?_ (by norm_num [Ac]) ?_ (by norm_num [Ac])
  · exact H_le_of_pow (b := 166) (p := 1158) (k := 157) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Ac])
  · exact J_le_of_pow (b := 165) (p := 744) (k := 101) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  · exact le_J_of_pow (b := 3) (c := 2) (p := 31) (k := 53)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Leaf 16 of the archived certificate: `x ∈ [2/5, 1/2]`,
plain branch, entropy-inverse witness `1/63`. -/
theorem leaf16 :
    stripPsi (2/5) false < stripCost (1/2) := by
  refine leaf_gap (v := (63:ℝ)⁻¹)
    (cL := 29658443/250120000)
    (c2 := 780/131) (jU := 0/1)
    (by norm_num [Ac]) (by norm_num [Ac])
    Ccap_two_fifths
    (by norm_num) (by norm_num) ?_ ?_ (by norm_num [Ac]) ?_ (by norm_num [Ac])
  · exact H_le_of_pow (b := 63) (p := 795) (k := 133) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num [Ac])
  · exact J_le_of_pow (b := 62) (p := 780) (k := 131) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
  · exact le_J_of_pow (b := 1) (c := 1) (p := 0) (k := 1)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-! ## 9. Assembly -/

/-- **Every one of the seventeen archived leaves satisfies the directed
comparison of `PROOF.md`.**  On each leaf the cost lower bound (4) strictly
exceeds the psi-branch upper envelope, (6) for the enhanced initial intervals and
(5) for the last one.

This is the leaf-replay half of the boundary-strip argument only.  It is *not* an
owner statement: the opposite-boundary owner additionally requires the retained
opposite corner and the factor-eight parent criterion, which are not proved in
this file. -/
theorem all_leaves_gap :
    ∀ z ∈ leaves, stripPsi ((z.1 : ℚ) : ℝ) z.2.2 < stripCost ((z.2.1 : ℚ) : ℝ) := by
  intro z hz
  fin_cases hz
  · show stripPsi (((32767/268435456 : ℚ)) : ℝ) true < stripCost (((557041/4294967296 : ℚ)) : ℝ)
    rw [show (((32767/268435456 : ℚ)) : ℝ) = 32767/268435456 from by push_cast; ring,
        show (((557041/4294967296 : ℚ)) : ℝ) = 557041/4294967296 from by push_cast; ring]
    exact leaf00
  · show stripPsi (((557041/4294967296 : ℚ)) : ℝ) true < stripCost (((294905/2147483648 : ℚ)) : ℝ)
    rw [show (((557041/4294967296 : ℚ)) : ℝ) = 557041/4294967296 from by push_cast; ring,
        show (((294905/2147483648 : ℚ)) : ℝ) = 294905/2147483648 from by push_cast; ring]
    exact leaf01
  · show stripPsi (((294905/2147483648 : ℚ)) : ℝ) true < stripCost (((163837/1073741824 : ℚ)) : ℝ)
    rw [show (((294905/2147483648 : ℚ)) : ℝ) = 294905/2147483648 from by push_cast; ring,
        show (((163837/1073741824 : ℚ)) : ℝ) = 163837/1073741824 from by push_cast; ring]
    exact leaf02
  · show stripPsi (((163837/1073741824 : ℚ)) : ℝ) true < stripCost (((98303/536870912 : ℚ)) : ℝ)
    rw [show (((163837/1073741824 : ℚ)) : ℝ) = 163837/1073741824 from by push_cast; ring,
        show (((98303/536870912 : ℚ)) : ℝ) = 98303/536870912 from by push_cast; ring]
    exact leaf03
  · show stripPsi (((98303/536870912 : ℚ)) : ℝ) true < stripCost (((1/4096 : ℚ)) : ℝ)
    rw [show (((98303/536870912 : ℚ)) : ℝ) = 98303/536870912 from by push_cast; ring,
        show (((1/4096 : ℚ)) : ℝ) = 1/4096 from by push_cast; ring]
    exact leaf04
  · show stripPsi (((1/4096 : ℚ)) : ℝ) true < stripCost (((1/2048 : ℚ)) : ℝ)
    rw [show (((1/4096 : ℚ)) : ℝ) = 1/4096 from by push_cast; ring,
        show (((1/2048 : ℚ)) : ℝ) = 1/2048 from by push_cast; ring]
    exact leaf05
  · show stripPsi (((1/2048 : ℚ)) : ℝ) true < stripCost (((1/1024 : ℚ)) : ℝ)
    rw [show (((1/2048 : ℚ)) : ℝ) = 1/2048 from by push_cast; ring,
        show (((1/1024 : ℚ)) : ℝ) = 1/1024 from by push_cast; ring]
    exact leaf06
  · show stripPsi (((1/1024 : ℚ)) : ℝ) true < stripCost (((1/512 : ℚ)) : ℝ)
    rw [show (((1/1024 : ℚ)) : ℝ) = 1/1024 from by push_cast; ring,
        show (((1/512 : ℚ)) : ℝ) = 1/512 from by push_cast; ring]
    exact leaf07
  · show stripPsi (((1/512 : ℚ)) : ℝ) true < stripCost (((1/256 : ℚ)) : ℝ)
    rw [show (((1/512 : ℚ)) : ℝ) = 1/512 from by push_cast; ring,
        show (((1/256 : ℚ)) : ℝ) = 1/256 from by push_cast; ring]
    exact leaf08
  · show stripPsi (((1/256 : ℚ)) : ℝ) true < stripCost (((1/128 : ℚ)) : ℝ)
    rw [show (((1/256 : ℚ)) : ℝ) = 1/256 from by push_cast; ring,
        show (((1/128 : ℚ)) : ℝ) = 1/128 from by push_cast; ring]
    exact leaf09
  · show stripPsi (((1/128 : ℚ)) : ℝ) true < stripCost (((1/64 : ℚ)) : ℝ)
    rw [show (((1/128 : ℚ)) : ℝ) = 1/128 from by push_cast; ring,
        show (((1/64 : ℚ)) : ℝ) = 1/64 from by push_cast; ring]
    exact leaf10
  · show stripPsi (((1/64 : ℚ)) : ℝ) true < stripCost (((1/32 : ℚ)) : ℝ)
    rw [show (((1/64 : ℚ)) : ℝ) = 1/64 from by push_cast; ring,
        show (((1/32 : ℚ)) : ℝ) = 1/32 from by push_cast; ring]
    exact leaf11
  · show stripPsi (((1/32 : ℚ)) : ℝ) true < stripCost (((1/16 : ℚ)) : ℝ)
    rw [show (((1/32 : ℚ)) : ℝ) = 1/32 from by push_cast; ring,
        show (((1/16 : ℚ)) : ℝ) = 1/16 from by push_cast; ring]
    exact leaf12
  · show stripPsi (((1/16 : ℚ)) : ℝ) true < stripCost (((1/8 : ℚ)) : ℝ)
    rw [show (((1/16 : ℚ)) : ℝ) = 1/16 from by push_cast; ring,
        show (((1/8 : ℚ)) : ℝ) = 1/8 from by push_cast; ring]
    exact leaf13
  · show stripPsi (((1/8 : ℚ)) : ℝ) true < stripCost (((1/4 : ℚ)) : ℝ)
    rw [show (((1/8 : ℚ)) : ℝ) = 1/8 from by push_cast; ring,
        show (((1/4 : ℚ)) : ℝ) = 1/4 from by push_cast; ring]
    exact leaf14
  · show stripPsi (((1/4 : ℚ)) : ℝ) true < stripCost (((2/5 : ℚ)) : ℝ)
    rw [show (((1/4 : ℚ)) : ℝ) = 1/4 from by push_cast; ring,
        show (((2/5 : ℚ)) : ℝ) = 2/5 from by push_cast; ring]
    exact leaf15
  · show stripPsi (((2/5 : ℚ)) : ℝ) false < stripCost (((1/2 : ℚ)) : ℝ)
    rw [show (((2/5 : ℚ)) : ℝ) = 2/5 from by push_cast; ring,
        show (((1/2 : ℚ)) : ℝ) = 1/2 from by push_cast; ring]
    exact leaf16

/-- Restated over the strip: every real point of `[K - A, 1/2]` lies in an
archived leaf on which the directed comparison holds. -/
theorem strip_pointwise_gap {x : ℝ}
    (hx : ((Kq - Aq : ℚ) : ℝ) ≤ x) (hx' : x ≤ 1/2) :
    ∃ z ∈ leaves, ((z.1 : ℚ) : ℝ) ≤ x ∧ x ≤ ((z.2.1 : ℚ) : ℝ) ∧
      stripPsi ((z.1 : ℚ) : ℝ) z.2.2 < stripCost ((z.2.1 : ℚ) : ℝ) := by
  obtain ⟨z, hz, h1, h2⟩ := (mem_strip_iff x).1 ⟨hx, hx'⟩
  exact ⟨z, hz, h1, h2, all_leaves_gap z hz⟩

#print axioms leaves
#print axioms root0_leaves
#print axioms leaves_chainFrom
#print axioms leaves_rightEnd
#print axioms mem_strip_iff
#print axioms Ccap_lower
#print axioms Ccap_two_fifths
#print axioms eta_le_of_H_le
#print axioms J_Ac_ge
#print axioms leaf_gap
#print axioms leaf00
#print axioms leaf01
#print axioms leaf02
#print axioms leaf03
#print axioms leaf04
#print axioms leaf05
#print axioms leaf06
#print axioms leaf07
#print axioms leaf08
#print axioms leaf09
#print axioms leaf10
#print axioms leaf11
#print axioms leaf12
#print axioms leaf13
#print axioms leaf14
#print axioms leaf15
#print axioms leaf16
#print axioms roots_dyadic
#print axioms leaves_left_attained
#print axioms leaves_right_attained
#print axioms leaf_branch_valid
#print axioms stripCost_eq_interiorCost
#print axioms all_leaves_gap
#print axioms strip_pointwise_gap

end BoundaryStrip
end GeneralCK

end


