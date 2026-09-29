-- Prove2me | Definitions.Def_CK_CKLaneC_TM3_Scalar
-- name    : CK_CKLaneC_TM3_Scalar
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T04:11:28.467368+00:00
-- url     : https://prove2.me/theorems/4c8a2fd0-7166-4b0f-826d-8dc1e6176b50
-- title:
--   Courtade–Kumar proof module `CKLaneC.TM3.Scalar` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC.TM3.Scalar` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC.TM3.Scalar` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC.TM3.Scalar (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC/TM3/Scalar.lean)

import Definitions.Def_CK_CKLaneC_TM3_Core

-- ===== source module CKLaneC.TM3.Scalar =====
section

/-!
# Lane C: TM3 elementary functions (scalar log, TM reciprocal, TM log, TM average) and soundness

These are bit-exact mirrors of `tm3c.py`: `log1p_scalar`, `LN2/LN2E`, `log_scalar`, `recip`, `log` and `average`.
`tm3c.py` fixes two units errors in R1's `tm3.py` tails, and its `average` uses the odd count.
-/

namespace CKLaneC.TM3

/-! ## Small real/integer helpers -/

theorem ediv_err (a d : ℤ) (hd : 0 < d) : |((a / d : ℤ) : ℝ) - (a : ℝ) / d| ≤ 1 := by
  have h := (Int.ediv_emod_unique (a := a) (r := a % d) (q := a / d) hd).mp ⟨rfl, rfl⟩
  obtain ⟨h1, h2, h3⟩ := h
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have e : (a : ℝ) = (a % d : ℤ) + d * (a / d : ℤ) := by exact_mod_cast h1.symm
  have hr0 : (0 : ℝ) ≤ ((a % d : ℤ) : ℝ) := by exact_mod_cast h2
  have hr1 : ((a % d : ℤ) : ℝ) < d := by exact_mod_cast h3
  have : ((a / d : ℤ) : ℝ) - (a : ℝ) / d = -(((a % d : ℤ) : ℝ) / d) := by
    rw [e]; field_simp; ring
  rw [this, abs_neg, abs_div, abs_of_nonneg hr0, abs_of_pos hd', div_le_one hd']
  exact hr1.le

theorem abs_log_sub_log_le {a b m : ℝ} (hm : 0 < m) (ha : m ≤ a) (hb : m ≤ b) :
    |Real.log a - Real.log b| ≤ |a - b| / m := by
  have ha0 : 0 < a := lt_of_lt_of_le hm ha
  have hb0 : 0 < b := lt_of_lt_of_le hm hb
  have h1 : Real.log a - Real.log b ≤ |a - b| / m := by
    rw [← Real.log_div ha0.ne' hb0.ne']
    have := Real.log_le_sub_one_of_pos (div_pos ha0 hb0)
    have e : a / b - 1 = (a - b) / b := by field_simp
    calc Real.log (a / b) ≤ (a - b) / b := by linarith
      _ ≤ |a - b| / b := div_le_div_of_nonneg_right (le_abs_self _) hb0.le
      _ ≤ |a - b| / m := div_le_div_of_nonneg_left (abs_nonneg _) hm hb
  have h2 : Real.log b - Real.log a ≤ |a - b| / m := by
    rw [← Real.log_div hb0.ne' ha0.ne']
    have := Real.log_le_sub_one_of_pos (div_pos hb0 ha0)
    have e : b / a - 1 = (b - a) / a := by field_simp
    calc Real.log (b / a) ≤ (b - a) / a := by linarith
      _ ≤ |a - b| / a := by
          apply div_le_div_of_nonneg_right _ ha0.le
          rw [abs_sub_comm]; exact le_abs_self _
      _ ≤ |a - b| / m := div_le_div_of_nonneg_left (abs_nonneg _) hm ha
  exact abs_le.mpr ⟨by linarith, h1⟩

/-- The alternating log1p partial sum `Σ_{i<n} (-1)^i u^(i+1)/(i+1)`. -/
noncomputable def l1pSum (u : ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * u ^ (i + 1) / (i + 1)

theorem abs_log_one_add_sub_l1pSum {u : ℝ} (hu : |u| < 1) (n : ℕ) :
    |Real.log (1 + u) - l1pSum u n| ≤ |u| ^ (n + 1) / (1 - |u|) := by
  have h := Real.abs_log_sub_add_sum_range_le (x := -u) (by rwa [abs_neg]) n
  rw [abs_neg] at h
  have e : ∑ i ∈ Finset.range n, (-u) ^ (i + 1) / ((i : ℝ) + 1) = -l1pSum u n := by
    unfold l1pSum
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [neg_pow, pow_succ]; ring
  rw [e, sub_neg_eq_add] at h
  have e2 : Real.log (1 + u) - l1pSum u n = -l1pSum u n + Real.log (1 + u) := by ring
  rw [e2]; exact h

theorem neg_one_pow_eq_sg (j : ℕ) : (-1 : ℝ) ^ j = if (j + 1) % 2 = 1 then 1 else -1 := by
  rcases Nat.even_or_odd j with h | h
  · rw [h.neg_one_pow]
    have : (j + 1) % 2 = 1 := by obtain ⟨r, hr⟩ := h; omega
    simp [this]
  · rw [h.neg_one_pow]
    have : (j + 1) % 2 = 0 := by obtain ⟨r, hr⟩ := h; omega
    simp [this]

theorem tail_id1 (o a : ℝ) (ho : 0 < o) (hao : a < o) (K : ℕ) :
    o * ((a / o) ^ (K + 2) / (1 - a / o)) = a ^ (K + 2) / (o ^ K * (o - a)) := by
  have ho' : o ≠ 0 := ho.ne'
  have hoa : o - a ≠ 0 := by linarith [sub_pos.mpr hao]
  have h1 : 1 - a / o = (o - a) / o := by field_simp
  rw [h1, div_pow, eq_div_iff (mul_ne_zero (pow_ne_zero _ ho') hoa)]
  field_simp
  ring

theorem tail_id2 (o a c : ℝ) (ho : 0 < o) (hao : a < o) (N : ℕ) :
    c / o * ((a / o) ^ (N + 1) / (1 - a / o)) = c * a ^ (N + 1) / (o ^ N * (o - a)) / o := by
  have ho' : o ≠ 0 := ho.ne'
  have hoa : o - a ≠ 0 := by linarith [sub_pos.mpr hao]
  have h1 : 1 - a / o = (o - a) / o := by field_simp
  rw [h1, div_pow]
  field_simp
  ring

theorem tail_id3 (o a : ℝ) (ho : 0 < o) (hao : a < o) (M : ℕ) :
    (a / o) ^ (M + 2) / (1 - a / o) = a ^ (M + 2) / (o ^ M * (o - a)) / o := by
  have ho' : o ≠ 0 := ho.ne'
  have hoa : o - a ≠ 0 := by linarith [sub_pos.mpr hao]
  have h1 : 1 - a / o = (o - a) / o := by field_simp
  rw [h1, div_pow]
  field_simp
  ring

/-! ## Scalar log1p series (tm3c `log1p_scalar`) -/

noncomputable def l1pStep (one : ℕ) (y : Int) (k : ℕ) (st : Int × Int) : Int × Int :=
  (st.1 * y / (one : Int), if k % 2 = 1 then st.2 + st.1 / (k : Int) else st.2 - st.1 / (k : Int))

noncomputable def l1pLoop (one : ℕ) (y : Int) (K : ℕ) : Int × Int :=
  @Nat.rec (fun _ => Int × Int) (y, 0) (fun j st => l1pStep one y (j + 1) st) K

theorem l1pLoop_zero (one : ℕ) (y : Int) : l1pLoop one y 0 = (y, 0) := rfl
theorem l1pLoop_succ (one : ℕ) (y : Int) (j : ℕ) :
    l1pLoop one y (j + 1) = l1pStep one y (j + 1) (l1pLoop one y j) := rfl

/-- Value and error of `log(1 + y/one)` in units of `1/one`. -/
noncomputable def log1pScalar (one : ℕ) (y : Int) (K : ℕ) : Int × ℕ :=
  ((l1pLoop one y K).2, 2 * K + cdiv (y.natAbs ^ (K + 1)) (one ^ (K - 1) * (one - y.natAbs)) + 1)

theorem l1p_inv (one : ℕ) (hone : 0 < one) (y : Int) (hy : y.natAbs ≤ one) (j : ℕ) :
    |((l1pLoop one y j).1 : ℝ) - one * ((y : ℝ) / one) ^ (j + 1)| ≤ j ∧
    |((l1pLoop one y j).2 : ℝ) - one * l1pSum ((y : ℝ) / one) j| ≤ 2 * j := by
  have hone' : (0 : ℝ) < one := by exact_mod_cast hone
  have hne : (one : ℝ) ≠ 0 := hone'.ne'
  have hyo : |(y : ℝ)| / one ≤ 1 := by
    rw [div_le_one hone', ← Int.cast_abs, ← Nat.cast_natAbs]; exact_mod_cast hy
  induction j with
  | zero =>
    simp only [l1pLoop_zero, l1pSum, Finset.range_zero, Finset.sum_empty]
    constructor
    · have : (one : ℝ) * ((y : ℝ) / one) ^ (0 + 1) = y := by
        simp only [zero_add, pow_one]; field_simp
      rw [this]; simp
    · simp
  | succ j ih =>
    rw [l1pLoop_succ]
    simp only [l1pStep]
    obtain ⟨ht, hs⟩ := ih
    set t := (l1pLoop one y j).1 with htdef
    set s := (l1pLoop one y j).2 with hsdef
    set u := (y : ℝ) / one with hudef
    constructor
    · -- t' = t*y/one
      have hfl := ediv_err (t * y) (one : ℤ) (by exact_mod_cast hone)
      have hcast : (((one : ℤ)) : ℝ) = (one : ℝ) := by norm_cast
      rw [hcast] at hfl
      push_cast at hfl
      have e : (t : ℝ) * y / one - one * u ^ (j + 1 + 1)
          = ((t : ℝ) - one * u ^ (j + 1)) * (y / one) := by
        rw [pow_succ u (j + 1)]; simp only [hudef]; ring
      have e2 : (((t * y / (one : ℤ)) : ℤ) : ℝ) - one * u ^ (j + 1 + 1)
          = ((((t * y / (one : ℤ)) : ℤ) : ℝ) - (t : ℝ) * y / one) + ((t : ℝ) * y / one - one * u ^ (j + 1 + 1)) := by
        ring
      have b2 : |(t : ℝ) * y / one - one * u ^ (j + 1 + 1)| ≤ j := by
        rw [e, abs_mul, abs_div, abs_of_pos hone']
        calc |(t : ℝ) - one * u ^ (j + 1)| * (|(y : ℝ)| / one) ≤ j * 1 :=
              mul_le_mul ht hyo (by positivity) (Nat.cast_nonneg _)
          _ = j := mul_one _
      rw [e2]
      calc _ ≤ |(((t * y / (one : ℤ)) : ℤ) : ℝ) - (t : ℝ) * y / one| + |(t : ℝ) * y / one - one * u ^ (j + 1 + 1)| :=
            abs_add_le _ _
        _ ≤ 1 + j := add_le_add hfl b2
        _ = ((j + 1 : ℕ) : ℝ) := by push_cast; ring
    · -- s' = s ± t/(j+1)
      set d : ℤ := ((j + 1 : ℕ) : ℤ) with hd
      have hdpos : (0 : ℤ) < d := by rw [hd]; exact_mod_cast Nat.succ_pos j
      have hdR : ((d : ℤ) : ℝ) = (j : ℝ) + 1 := by rw [hd]; push_cast; ring
      have hfl := ediv_err t d hdpos
      rw [hdR] at hfl
      set q : ℤ := t / d with hq
      have hk' : (0 : ℝ) < (j : ℝ) + 1 := by positivity
      have hterm : |(q : ℝ) - one * u ^ (j + 1) / ((j : ℝ) + 1)| ≤ 2 := by
        have h2 : |(t : ℝ) / ((j : ℝ) + 1) - one * u ^ (j + 1) / ((j : ℝ) + 1)| ≤ 1 := by
          rw [← sub_div, abs_div, abs_of_pos hk', div_le_one hk']; linarith
        have e3 : (q : ℝ) - one * u ^ (j + 1) / ((j : ℝ) + 1)
            = ((q : ℝ) - (t : ℝ) / ((j : ℝ) + 1)) + ((t : ℝ) / ((j : ℝ) + 1) - one * u ^ (j + 1) / ((j : ℝ) + 1)) := by
          ring
        rw [e3]
        calc _ ≤ |(q : ℝ) - (t : ℝ) / ((j : ℝ) + 1)|
              + |(t : ℝ) / ((j : ℝ) + 1) - one * u ^ (j + 1) / ((j : ℝ) + 1)| := abs_add_le _ _
          _ ≤ 1 + 1 := add_le_add hfl h2
          _ = 2 := by norm_num
      have hsum : l1pSum u (j + 1) = l1pSum u j + (-1 : ℝ) ^ j * u ^ (j + 1) / ((j : ℝ) + 1) := by
        unfold l1pSum; rw [Finset.sum_range_succ]
      rw [hsum, neg_one_pow_eq_sg j]
      split_ifs with hpar
      · have e : (((s + q : ℤ)) : ℝ) - one * (l1pSum u j + 1 * u ^ (j + 1) / ((j : ℝ) + 1))
            = ((s : ℝ) - one * l1pSum u j) + ((q : ℝ) - one * u ^ (j + 1) / ((j : ℝ) + 1)) := by
          push_cast; ring
        rw [e]
        calc _ ≤ |(s : ℝ) - one * l1pSum u j| + |(q : ℝ) - one * u ^ (j + 1) / ((j : ℝ) + 1)| := abs_add_le _ _
          _ ≤ 2 * j + 2 := add_le_add hs hterm
          _ = 2 * ((j + 1 : ℕ) : ℝ) := by push_cast; ring
      · have e : (((s - q : ℤ)) : ℝ) - one * (l1pSum u j + -1 * u ^ (j + 1) / ((j : ℝ) + 1))
            = ((s : ℝ) - one * l1pSum u j) - ((q : ℝ) - one * u ^ (j + 1) / ((j : ℝ) + 1)) := by
          push_cast; ring
        rw [e]
        calc _ ≤ |(s : ℝ) - one * l1pSum u j| + |(q : ℝ) - one * u ^ (j + 1) / ((j : ℝ) + 1)| := abs_sub _ _
          _ ≤ 2 * j + 2 := add_le_add hs hterm
          _ = 2 * ((j + 1 : ℕ) : ℝ) := by push_cast; ring

theorem log1pScalar_sound (one : ℕ) (hone : 0 < one) (y : Int) (K : ℕ) (hK : 1 ≤ K)
    (hy : y.natAbs < one) :
    |((log1pScalar one y K).1 : ℝ) - one * Real.log (1 + y / one)| ≤ (log1pScalar one y K).2 := by
  have hone' : (0 : ℝ) < one := by exact_mod_cast hone
  have hne : (one : ℝ) ≠ 0 := hone'.ne'
  obtain ⟨_, hs⟩ := l1p_inv one hone y hy.le K
  set u := (y : ℝ) / one
  have hau : |u| = (y.natAbs : ℝ) / one := by
    simp only [u]; rw [abs_div, abs_of_pos hone', Nat.cast_natAbs, Int.cast_abs]
  have hu1 : |u| < 1 := by
    rw [hau, div_lt_one hone']; exact_mod_cast hy
  have hser := abs_log_one_add_sub_l1pSum hu1 K
  simp only [log1pScalar]
  -- tail in units
  obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
  have hden : 0 < one ^ (K' + 1 - 1) * (one - y.natAbs) := by
    apply Nat.mul_pos (pow_pos hone _); omega
  have htail := le_cdiv (y.natAbs ^ (K' + 1 + 1)) (one ^ (K' + 1 - 1) * (one - y.natAbs)) hden
  have hsub : ((one - y.natAbs : ℕ) : ℝ) = (one : ℝ) - y.natAbs := by
    rw [Nat.cast_sub hy.le]
  have key : (one : ℝ) * (|u| ^ (K' + 1 + 1) / (1 - |u|))
      = ((y.natAbs ^ (K' + 1 + 1) : ℕ) : ℝ) / ((one ^ (K' + 1 - 1) * (one - y.natAbs) : ℕ) : ℝ) := by
    rw [hau, show K' + 1 - 1 = K' by omega, Nat.cast_mul, hsub, Nat.cast_pow, Nat.cast_pow]
    have : (y.natAbs : ℝ) < one := by exact_mod_cast hy
    exact tail_id1 (one : ℝ) (y.natAbs : ℝ) hone' this K'
  have e : ((l1pLoop one y (K' + 1)).2 : ℝ) - one * Real.log (1 + u)
      = (((l1pLoop one y (K' + 1)).2 : ℝ) - one * l1pSum u (K' + 1))
        - one * (Real.log (1 + u) - l1pSum u (K' + 1)) := by ring
  rw [e]
  calc _ ≤ |((l1pLoop one y (K' + 1)).2 : ℝ) - one * l1pSum u (K' + 1)|
        + |(one : ℝ) * (Real.log (1 + u) - l1pSum u (K' + 1))| := abs_sub _ _
    _ ≤ 2 * ((K' + 1 : ℕ) : ℝ) + (one : ℝ) * (|u| ^ (K' + 1 + 1) / (1 - |u|)) := by
        apply add_le_add
        · exact hs
        · rw [abs_mul, abs_of_pos hone']; exact mul_le_mul_of_nonneg_left hser hone'.le
    _ ≤ 2 * ((K' + 1 : ℕ) : ℝ) + (cdiv (y.natAbs ^ (K' + 1 + 1)) (one ^ (K' + 1 - 1) * (one - y.natAbs)) : ℝ) := by
        rw [key]; gcongr
    _ ≤ _ := by push_cast; linarith

/-! ## `LN2` constant and scalar log (tm3c `LN2`, `log_scalar`) -/

noncomputable def ln2Pair (P : ℕ) : Int × ℕ := log1pScalar (2 ^ P) (-((2 ^ P / 2 : ℕ) : Int)) (P + 8)
noncomputable def LN2 (P : ℕ) : Int := -(ln2Pair P).1
noncomputable def LN2E (P : ℕ) : ℕ := (ln2Pair P).2

theorem LN2_sound (P : ℕ) (hP : 1 ≤ P) : |(LN2 P : ℝ) - 2 ^ P * Real.log 2| ≤ LN2E P := by
  have hone : 0 < 2 ^ P := pow_pos (by norm_num) _
  obtain ⟨P', rfl⟩ : ∃ P', P = P' + 1 := ⟨P - 1, by omega⟩
  have hhalf : (2 ^ (P' + 1) / 2 : ℕ) = 2 ^ P' := by rw [pow_succ]; simp
  have hy : ((-((2 ^ (P' + 1) / 2 : ℕ) : Int)).natAbs) < 2 ^ (P' + 1) := by
    have e0 : (-((2 ^ P' : ℕ) : ℤ)).natAbs = 2 ^ P' := by simp
    rw [hhalf, e0]
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  have h := log1pScalar_sound (2 ^ (P' + 1)) hone (-((2 ^ (P' + 1) / 2 : ℕ) : Int)) (P' + 1 + 8) (by omega) hy
  have e : (1 : ℝ) + ((-((2 ^ (P' + 1) / 2 : ℕ) : Int) : ℤ) : ℝ) / ((2 ^ (P' + 1) : ℕ) : ℝ) = 1 / 2 := by
    rw [hhalf]; push_cast; rw [pow_succ]; field_simp; ring
  rw [e, one_div, Real.log_inv] at h
  unfold LN2 LN2E
  push_cast at h ⊢
  rw [show -((ln2Pair (P' + 1)).1 : ℝ) - 2 ^ (P' + 1) * Real.log 2
      = -(((ln2Pair (P' + 1)).1 : ℝ) - 2 ^ (P' + 1) * -Real.log 2) by ring, abs_neg]
  exact h

/-- Fuelled `floor(log2 n)` (= Python `bit_length - 1` for `n ≥ 1` and enough fuel). -/
noncomputable def log2F (fuel n : ℕ) : ℕ :=
  @Nat.rec (fun _ => ℕ → ℕ) (fun _ => 0) (fun _ ih n => if n < 2 then 0 else ih (n / 2) + 1) fuel n

/-- `(E, y)` of tm3c `log_scalar_y`. -/
noncomputable def logScalarEY (P kint : ℕ) : ℕ × Int :=
  let E0 := log2F (4 * P + 8) kint
  let E := if 2 * 2 ^ (2 * E0) < kint * kint then E0 + 1 else E0
  let num : Int := (kint : Int) - ((2 ^ E : ℕ) : Int)
  (E, if P ≤ E then num / ((2 ^ (E - P) : ℕ) : Int) else num * ((2 ^ (P - E) : ℕ) : Int))

noncomputable def logScalar (P kint : ℕ) : Int × ℕ :=
  ((log1pScalar (2 ^ P) (logScalarEY P kint).2 (4 * P / 5 + 6)).1
      + (((logScalarEY P kint).1 : Int) - P) * LN2 P,
   (log1pScalar (2 ^ P) (logScalarEY P kint).2 (4 * P / 5 + 6)).2 + 3
      + (((logScalarEY P kint).1 : Int) - P).natAbs * LN2E P)

/-- Exact relation between `y` and `u = num / 2^E` (floor when `P ≤ E`). -/
theorem logScalarEY_spec (P kint : ℕ) :
    |((logScalarEY P kint).2 : ℝ) / 2 ^ P - ((kint : ℝ) / 2 ^ (logScalarEY P kint).1 - 1)| ≤ 1 / 2 ^ P := by
  simp only [logScalarEY]
  set E0 := log2F (4 * P + 8) kint
  set E := if 2 * 2 ^ (2 * E0) < kint * kint then E0 + 1 else E0
  have hP0 : (0 : ℝ) < 2 ^ P := by positivity
  have hE0 : (0 : ℝ) < 2 ^ E := by positivity
  have hu : (kint : ℝ) / 2 ^ E - 1 = (((kint : Int) - ((2 ^ E : ℕ) : Int) : ℤ) : ℝ) / 2 ^ E := by
    push_cast; field_simp
  rw [hu]
  split_ifs with hPE
  · -- floor case
    have hd : (0 : ℤ) < ((2 ^ (E - P) : ℕ) : ℤ) := by positivity
    have hfl := ediv_err ((kint : Int) - ((2 ^ E : ℕ) : Int)) ((2 ^ (E - P) : ℕ) : ℤ) hd
    have hsplit : (2 : ℝ) ^ E = 2 ^ (E - P) * 2 ^ P := by
      rw [← pow_add]; congr 1; omega
    set n : ℤ := (kint : Int) - ((2 ^ E : ℕ) : Int)
    have e : ((n / ((2 ^ (E - P) : ℕ) : ℤ) : ℤ) : ℝ) / 2 ^ P - (n : ℝ) / 2 ^ E
        = (((n / ((2 ^ (E - P) : ℕ) : ℤ) : ℤ) : ℝ) - (n : ℝ) / ((2 ^ (E - P) : ℕ) : ℤ)) / 2 ^ P := by
      rw [hsplit]; push_cast; field_simp
    rw [e, abs_div, abs_of_pos hP0]
    exact div_le_div_of_nonneg_right hfl hP0.le
  · -- exact case
    have hsplit : (2 : ℝ) ^ P = 2 ^ (P - E) * 2 ^ E := by
      rw [← pow_add]; congr 1; omega
    have e : ((((kint : Int) - ((2 ^ E : ℕ) : Int)) * ((2 ^ (P - E) : ℕ) : Int) : ℤ) : ℝ) / 2 ^ P
        - (((kint : Int) - ((2 ^ E : ℕ) : Int) : ℤ) : ℝ) / 2 ^ E = 0 := by
      rw [hsplit]; push_cast; field_simp; ring
    rw [e, abs_zero]; positivity

theorem logScalar_sound (P : ℕ) (hP : 3 ≤ P) (kint : ℕ) (hk : 0 < kint)
    (hy : 2 * (logScalarEY P kint).2.natAbs ≤ 2 ^ P) :
    |((logScalar P kint).1 : ℝ) - 2 ^ P * Real.log (kint / 2 ^ P)| ≤ (logScalar P kint).2 := by
  set E := (logScalarEY P kint).1
  set y := (logScalarEY P kint).2
  have hone : 0 < 2 ^ P := pow_pos (by norm_num) _
  have hP0 : (0 : ℝ) < 2 ^ P := by positivity
  have hP8 : (8 : ℝ) ≤ 2 ^ P := by
    have : (2 : ℝ) ^ 3 ≤ 2 ^ P := pow_le_pow_right₀ (by norm_num) hP
    norm_num at this; exact this
  have hyl : y.natAbs < 2 ^ P := by omega
  have hl1 := log1pScalar_sound (2 ^ P) hone y (4 * P / 5 + 6) (by omega) hyl
  have hspec := logScalarEY_spec P kint
  set v : ℝ := (y : ℝ) / 2 ^ P
  set u : ℝ := (kint : ℝ) / 2 ^ E - 1
  have hv : |v| ≤ 1 / 2 := by
    simp only [v]; rw [abs_div, abs_of_pos hP0, div_le_iff₀ hP0, ← Int.cast_abs, ← Nat.cast_natAbs]
    have : (2 : ℝ) * (y.natAbs : ℝ) ≤ 2 ^ P := by exact_mod_cast hy
    linarith
  have hvu : |v - u| ≤ 1 / 2 ^ P := hspec
  have h1v : (1 : ℝ) / 2 ≤ 1 + v := by linarith [(abs_le.mp hv).1]
  have hinv : (1 : ℝ) / 2 ^ P ≤ 1 / 8 := one_div_le_one_div_of_le (by norm_num) hP8
  have h1u : (3 : ℝ) / 8 ≤ 1 + u := by linarith [(abs_le.mp hvu).1, (abs_le.mp hvu).2]
  have hlip := abs_log_sub_log_le (by norm_num : (0 : ℝ) < 3 / 8) h1u (by linarith : (3 : ℝ) / 8 ≤ 1 + v)
  have hlip' : (2 : ℝ) ^ P * |Real.log (1 + u) - Real.log (1 + v)| ≤ 3 := by
    have : |(1 + u) - (1 + v)| ≤ 1 / 2 ^ P := by
      rw [show (1 + u) - (1 + v) = -(v - u) by ring, abs_neg]; exact hvu
    calc (2 : ℝ) ^ P * |Real.log (1 + u) - Real.log (1 + v)| ≤ 2 ^ P * ((1 / 2 ^ P) / (3 / 8)) := by
          gcongr; exact hlip.trans (div_le_div_of_nonneg_right this (by norm_num))
      _ = 8 / 3 := by field_simp
      _ ≤ 3 := by norm_num
  have hln2 := LN2_sound P (by omega)
  -- decomposition of log(kint/2^P)
  have hk0 : (0 : ℝ) < kint := by exact_mod_cast hk
  have hlog : Real.log ((kint : ℝ) / 2 ^ P) = Real.log (1 + u) + ((E : ℝ) - P) * Real.log 2 := by
    simp only [u]
    rw [show (1 : ℝ) + ((kint : ℝ) / 2 ^ E - 1) = (kint : ℝ) / 2 ^ E by ring]
    rw [Real.log_div hk0.ne' (by positivity), Real.log_div hk0.ne' (by positivity),
      Real.log_pow, Real.log_pow]
    ring
  have hcast : (((2 ^ P : ℕ) : ℝ)) = (2 : ℝ) ^ P := by push_cast; rfl
  rw [hcast] at hl1
  simp only [logScalar]
  push_cast
  rw [hlog]
  set k2 : ℝ := (E : ℝ) - P
  have hk2 : |(((E : ℤ) - (P : ℤ) : ℤ) : ℝ)| = ((((E : ℤ) - (P : ℤ)).natAbs : ℕ) : ℝ) := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  have e : ((log1pScalar (2 ^ P) y (4 * P / 5 + 6)).1 : ℝ) + ((E : ℝ) - P) * LN2 P
      - 2 ^ P * (Real.log (1 + u) + ((E : ℝ) - P) * Real.log 2)
      = (((log1pScalar (2 ^ P) y (4 * P / 5 + 6)).1 : ℝ) - 2 ^ P * Real.log (1 + v))
        + 2 ^ P * (Real.log (1 + v) - Real.log (1 + u))
        + ((E : ℝ) - P) * ((LN2 P : ℝ) - 2 ^ P * Real.log 2) := by ring
  rw [e]
  have b3 : |((E : ℝ) - P) * ((LN2 P : ℝ) - 2 ^ P * Real.log 2)|
      ≤ ((((E : ℤ) - (P : ℤ)).natAbs : ℕ) : ℝ) * (LN2E P : ℝ) := by
    rw [abs_mul]
    have : |((E : ℝ) - P)| = ((((E : ℤ) - (P : ℤ)).natAbs : ℕ) : ℝ) := by
      rw [← hk2]; push_cast; rfl
    rw [this]; exact mul_le_mul_of_nonneg_left hln2 (Nat.cast_nonneg _)
  calc _ ≤ |((log1pScalar (2 ^ P) y (4 * P / 5 + 6)).1 : ℝ) - 2 ^ P * Real.log (1 + v)|
        + |(2 : ℝ) ^ P * (Real.log (1 + v) - Real.log (1 + u))|
        + |((E : ℝ) - P) * ((LN2 P : ℝ) - 2 ^ P * Real.log 2)| := abs_add_three _ _ _
    _ ≤ ((log1pScalar (2 ^ P) y (4 * P / 5 + 6)).2 : ℝ) + 3
        + ((((E : ℤ) - (P : ℤ)).natAbs : ℕ) : ℝ) * (LN2E P : ℝ) := by
        gcongr
        · rw [abs_mul, abs_of_pos hP0, abs_sub_comm]; exact hlip'
    _ = _ := by push_cast; ring

end CKLaneC.TM3

end


