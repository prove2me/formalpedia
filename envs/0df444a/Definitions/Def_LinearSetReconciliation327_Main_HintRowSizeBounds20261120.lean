-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_HintRowSizeBounds20261120
-- name    : LinearSetReconciliation327_Main_HintRowSizeBounds20261120
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-22T09:01:14.315869+00:00
-- url     : https://prove2.me/theorems/9566d4fb-6f75-485a-88c8-2e8a44ca4957
-- title:
--   LinearSetReconciliation327 — HintRowSizeBounds (2026-11-20)
-- statement:
--   Internal dependency module `Definitions.LinearSetReconciliation327_Main_HintRowSizeBounds20261120` of the LinearSetReconciliation327 development that formalizes Theorem 5.1 (Performance of HintSketch). It factors the toggle-program / decoder construction into a small node so that every node compiles well inside the platform's compilation limit; it contains only the definitions, structures, lemmas and proofs belonging to this module, and it is sorry-free. This definition is a supporting node, not a statement of independent mathematical interest.
-- source:
--   Tianren Liu, Rui Xu, Tong Yang, Kangyang Zhou, STOC 2027 submission #327 (October 2026), Theorem 5.1 (HintSketch), PDF p.19 (printed p.18)

import Definitions.Def_LinearSetReconciliation327_Main_HintUpdatePrepared20261120
set_option autoImplicit false
namespace LinearSetReconciliation327.Main

theorem hintNmax_le_of_noncheap (P : HintParams) {N X Y : ℕ}
    (hLog : 1 ≤ P.lgn)
    (hD : (N : ℝ) / P.lgn ^ 10 < (HintParams.D N X Y : ℝ))
    (hRows : 0 < P.rows X Y) :
    (P.Nmax N X Y : ℝ) ≤ 3 * P.lgn ^ 13 := by
  let m : ℝ := P.rows X Y
  have hL : 0 < P.lgn := lt_of_lt_of_le (by norm_num) hLog
  have hm : 0 < m := by
    change (0 : ℝ) < (P.rows X Y : ℝ)
    exact_mod_cast hRows
  have hY : (Y : ℝ) ≤ m := by
    change (Y : ℝ) ≤ (P.rows X Y : ℝ)
    exact_mod_cast (show Y ≤ P.rows X Y from le_max_left _ _)
  have hXceil : ((⌈(X : ℝ) / P.lgn ^ 3⌉₊ : ℕ) : ℝ) ≤ m := by
    change ((⌈(X : ℝ) / P.lgn ^ 3⌉₊ : ℕ) : ℝ) ≤ (P.rows X Y : ℝ)
    exact_mod_cast (show ⌈(X : ℝ) / P.lgn ^ 3⌉₊ ≤ P.rows X Y from le_max_right _ _)
  have hX := (div_le_iff₀ (pow_pos hL 3)).mp ((Nat.le_ceil _).trans hXceil)
  have hSum : (HintParams.D N X Y : ℝ) ≤ (X : ℝ) + Y := by
    exact_mod_cast (show HintParams.D N X Y ≤ X + Y from min_le_right _ _)
  have hBound : (N : ℝ) / P.lgn ^ 10 < m * (P.lgn ^ 3 + 1) :=
    hD.trans_le (by nlinarith only [hX, hY, hSum])
  have hMul := (div_lt_iff₀ (pow_pos hL 10)).mp hBound
  have hPowers : (P.lgn ^ 3 + 1) * P.lgn ^ 10 ≤ 2 * P.lgn ^ 13 := by
    have hMono : P.lgn ^ 10 ≤ P.lgn ^ 13 := pow_le_pow_right₀ hLog (by decide)
    nlinarith only [hMono]
  have hNm : (N : ℝ) < 2 * P.lgn ^ 13 * m := by
    calc
      (N : ℝ) < m * (P.lgn ^ 3 + 1) * P.lgn ^ 10 := hMul
      _ = m * ((P.lgn ^ 3 + 1) * P.lgn ^ 10) := by ring
      _ ≤ m * (2 * P.lgn ^ 13) := mul_le_mul_of_nonneg_left hPowers hm.le
      _ = 2 * P.lgn ^ 13 * m := mul_comm _ _
  have hRatio : (N : ℝ) / m < 2 * P.lgn ^ 13 := (div_lt_iff₀ hm).mpr hNm
  have hCeil : (⌈(N : ℝ) / m⌉₊ : ℝ) < (N : ℝ) / m + 1 :=
    Nat.ceil_lt_add_one (div_nonneg (Nat.cast_nonneg _) hm.le)
  have h13 : (1 : ℝ) ≤ P.lgn ^ 13 := one_le_pow₀ hLog
  change (⌈(N : ℝ) / m⌉₊ : ℝ) ≤ 3 * P.lgn ^ 13
  linarith

theorem hintNmax_le_nonleaf (P : HintParams) {N X Y : ℕ}
    (hLog : 1 ≤ P.lgn)
    (hRule : P.rule N X Y = .recursive ∨ P.rule N X Y = .direct) :
    (P.Nmax N X Y : ℝ) ≤ 3 * P.lgn ^ 13 := by
  rcases hRule with h | h
  · have hRec := rule_recursive_spec h
    have hRows : 0 < P.rows X Y := hRec.2.2.symm ▸ one_le_Y_of_recursive hLog hRec.1 hRec.2.2
    exact hintNmax_le_of_noncheap P hLog (lt_of_not_ge hRec.1) hRows
  · have hDirect := rule_direct_spec h
    exact hintNmax_le_of_noncheap P hLog hDirect.1
      (one_le_rows_of_ne hDirect.2.2)

theorem hintBY_le_loglog (P : HintParams) (N X Y : ℕ) (hLog : 1 ≤ P.lgn) :
    (P.BY N X Y : ℝ) ≤ (P.C : ℝ) * (lg P.lgn + 2) + 5 := by
  have hL : 0 < P.lgn := lt_of_lt_of_le (by norm_num) hLog
  have hMon : lg (P.lgn + 2) ≤ lg (4 * P.lgn) :=
    Real.logb_le_logb_of_le (b := 2) (by norm_num) (by linarith) (by linarith)
  have hFour : lg (4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, lg_pow_pos (by norm_num), lg_two]
    norm_num
  rw [lg_mul_pos (by norm_num) hL, hFour, add_comm (2 : ℝ) (lg P.lgn)] at hMon
  exact (BY_le_sharp P N X Y).trans (add_le_add
    (mul_le_mul_of_nonneg_left hMon (Nat.cast_nonneg P.C)) le_rfl)

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.hintNmax_le_nonleaf
#print axioms LinearSetReconciliation327.Main.hintBY_le_loglog


