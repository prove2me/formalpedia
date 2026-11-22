-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_Top65
-- name    : LinearSetReconciliation327_Main_Top65
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-21T15:26:37.729864+00:00
-- url     : https://prove2.me/theorems/94024c38-a7d5-4a0a-b857-69ffeadbca6e
-- title:
--   Theorem 6.5: the composite construction of §3.2 and the machine conjuncts (skeleton of the proof of Theorem 6.5)
-- statement:
--   The **composite reduction** underlying Theorem 6.5.  The paper's recursion $H_r x = \bigl((H_{a,k}\,C_{a,k}(x))_{a,k},\ \mathrm{CR}\,x\bigr)$ is turned into concrete data: the top-level column maps $C_{a,k}$ (`compCol`, `compWord`), the block layout `blkOff`/`blkTotal`/`blkIdx` that places the $\ell$ child blocks one after another at width $2^{W_d}$, the assemblers `compAsmV`/`compAsm` that concatenate the children's vectors with the CR coordinates, the packed-word lemmas that read them back out of the $W$-bit words of a word-RAM memory, the per-child record `CompChild` and the child-column bound.  On the machine side it fixes the composite deterministic table `compDet` of the toggle programme and its address algebra, the composite programmes `progUpOf`/`progDecOf` with their `HaltsWithin` bounds, and the arithmetic the proof needs: the logarithm inequalities, the $\ell$-fold time sums, the length chain of §6, the capacity bounds of (28) through Lemma 6.3 (iii), Lemma 6.4, the Galois-field data of 6.3, the small-instance arithmetic, and the uniform-marginal lemmas.  The module ends with `theorem_6_5_of_composite`, which derives the eight conjuncts of Theorem 6.5 from the five data conjuncts plus the three machine conjuncts.  Everything here is independent of any platform theorem, which is exactly why it is published as a definition bundle: both the parent reduction and the machine child import it.
-- source:
--   arXiv:2611.11409 (Liu, Xu, Yang, Zhou, *Linear Set Reconciliation with O(d) Additive Redundancy*), §3.2 (the composite construction) and §6.1, Theorem 6.5; the statement of the eight conjuncts is the paper's Theorem 6.5.

import Mathlib
import Definitions.Def_LinearSetReconciliation327_Main_Basic
import Definitions.Def_LinearSetReconciliation327_Main_Framework
import Definitions.Def_LinearSetReconciliation327_Main_TopLevel
import Definitions.Def_LinearSetReconciliation327_Main_WordRAM
import Definitions.Def_LinearSetReconciliation327_Main_DecoderModel
import Definitions.Def_LinearSetReconciliation327_Main_DecoderLemmas

set_option autoImplicit false

open scoped ENNReal
open Finset

namespace LinearSetReconciliation327.Main

/-!
# `Top65`: the composite construction of §3.2 and the machine conjuncts of Theorem 6.5

This module is the *skeleton subtraction* of `Solutions/Sol_theorem_6_5.lean`: every declaration
that the composite `H_r x = ((H_{a,k} C_{a,k}(x))_{a,k}, CR x)` needs and that does **not** depend on
a platform theorem, so that the module can be published as a `Definitions` bundle and imported by
both the new child `thm65_machine` and the parent reduction of Theorem 6.5.

Contents, in order:

* §1 logarithm arithmetic (`lg_two`, `one_le_lg`, …) and the two isolated nonlinear steps;
* §4/§5 `ℓ`-fold time sums, `d w ≤ L(n,d) + 3d`, `h_n(d) ≤ L(n,d) + 3d`;
* §6 the paper's length chain (`length_bound`, `cr_length_le`);
* §7 GAP-A: the capacities of (28) through Lemma 6.3 (iii) (`capacity_total_le'`'s *arithmetic*);
  `direct_storage_le` (the deterministic regime), Lemma 6.4, the Galois field data of 6.3;
* §8 the small-instance arithmetic (`small_instance_le`);
* §10 the composite construction: `compWord`/`compCol` (the top-level column `C_{a,k}`), the block
  layout `blkOff`/`blkTotal`/`blkIdx`/`compBlk`/`compBit`, the assemblers `compAsmV`/`compAsm` and
  their lemmas, the packing lemmas, `comp_colWeight_le`, the per-child record `CompChild` and
  `comp_col_bound`;
* §11 `CompDatum`, `MachineConjuncts`, `machineConjuncts_iff` and `theorem_6_5_of_composite`
  (6.5's eight conjuncts from the five data ones plus the three machine ones), the failure
  probability's union bound (`failure_arith`, `failure_bound_of_child_bounds`,
  `recovery_bound_of_child_bounds`);
* §11' the `det` layout `compDet` of the composite toggle table and its address algebra, the
  `compAsm` block algebra, the packed-payload lemma, and the `halt`-cannot-be-followed lemmas;
* §12 the composite programmes `progUpOf`/`progDecOf` with their `HaltsWithin` bounds, the toggle
  conjunct for one block, and the uniform-marginal lemmas (`prU_pi_proj`, `prU_compChildSeed`,
  `failure_bound_composite`).

What is *not* here (it needs a platform theorem, so it lives in the parent / in the child's own
proof file): `theorem_5_1_child`, `capacity_total_le`, `capacity_total_le'`, `composite_sketch`,
`child_machine_conjuncts`, `composite_length_bound`, `small_instance_exists`.
-/

/-- `⌈log 2⌉ = 1` is the only base fact used below; `lg` is `Real.logb 2`. -/
lemma lg_two : lg (2 : ℝ) = 1 := Real.logb_self_eq_one (by norm_num)
/-- For `n ≥ 2`, `lg n ≥ 1`; this is what turns `1 + C₁/lg n` into `1 + C₁`
(`6toplevel.tex` line 297). -/
lemma one_le_lg {n : ℕ} (hn : 2 ≤ n) : 1 ≤ lg (n : ℝ) := by
  have h2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hn' : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h : Real.log 2 ≤ Real.log (n : ℝ) := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hn'
  show 1 ≤ Real.log (n : ℝ) / Real.log 2
  rw [le_div_iff₀ h2]
  linarith
/-- `lg lg n ≥ 0` for `n ≥ 2`, so `(lg lg n)^2` is a genuine exponent. -/
lemma lg_lg_nonneg {n : ℕ} (hn : 2 ≤ n) : 0 ≤ lg (lg (n : ℝ)) := by
  have h2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have h1 : (1 : ℝ) ≤ lg (n : ℝ) := one_le_lg hn
  have hl : 0 ≤ Real.log (lg (n : ℝ)) := Real.log_nonneg h1
  exact div_nonneg hl (le_of_lt h2)
/-- `log (lg n + 2) ≤ lg lg n + 2`: the additive constant `2` that `time_sum_le` absorbs.  Writing
`y = lg lg n`, we have `lg n = 2^y ≤ e^y` and `2 ≤ 2 e^y`, so `lg n + 2 ≤ 3 e^y` and
`log 3 ≤ 2`. -/
lemma log_lg_add_two_le {n : ℕ} (hn : 2 ≤ n) :
    Real.log (lg (n : ℝ) + 2) ≤ lg (lg (n : ℝ)) + 2 := by
  set y : ℝ := lg (lg (n : ℝ)) with hy
  have hy0 : 0 ≤ y := lg_lg_nonneg hn
  have hln : (0 : ℝ) < lg (n : ℝ) := lt_of_lt_of_le zero_lt_one (one_le_lg hn)
  have h2ne : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have hloglg : y * Real.log 2 = Real.log (lg (n : ℝ)) := by
    have hEq : lg (lg (n : ℝ)) = Real.log (lg (n : ℝ)) / Real.log 2 := rfl
    rw [hy, hEq]
    exact div_mul_cancel₀ (Real.log (lg (n : ℝ))) h2ne
  have hexp : lg (n : ℝ) = Real.exp (y * Real.log 2) := by
    rw [hloglg, Real.exp_log hln]
  have hlog2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (x := 2) (by norm_num : (0 : ℝ) < 2)
    linarith
  have hle : Real.exp (y * Real.log 2) ≤ Real.exp y := by
    apply Real.exp_le_exp.2
    nlinarith [mul_le_mul_of_nonneg_left hlog2 hy0]
  have he1 : (1 : ℝ) ≤ Real.exp y := by
    have h := Real.exp_le_exp.2 hy0
    simpa using h
  have h3 : lg (n : ℝ) + 2 ≤ 3 * Real.exp y := by
    rw [hexp] at *
    nlinarith
  have hpos : (0 : ℝ) < lg (n : ℝ) + 2 := by linarith
  have hmono := Real.log_le_log hpos h3
  have hmul : Real.log (3 * Real.exp y) = Real.log 3 + y := by
    rw [Real.log_mul (by norm_num) (Real.exp_ne_zero y), Real.log_exp]
  have hlog3 : Real.log 3 ≤ 2 := by
    have h := Real.log_le_sub_one_of_pos (x := 3) (by norm_num : (0 : ℝ) < 3)
    linarith
  rw [hmul] at hmono
  linarith

/-! ### 1b. The two nonlinear steps, isolated from the big local contexts

`nlinarith` preprocesses the *whole* local context (it looks for positivity/positivity-shaped
hypotheses and linearises every inequality it finds).  In §6–§8 that context contains dozens of
hypotheses whose types mention `∑`/`compAsm`-sized terms, so a single `nlinarith` there costs
seconds of preprocessing, and the cost grows with the context.  Both nonlinear facts the file
actually needs are therefore stated here — where the context is empty, so `nlinarith` sees a
handful of atoms — and are then used *by name*, which costs nothing at the call site. -/
/-- `(x + 2) ^ 2 ≤ 9 x ^ 2` for `x ≥ 1`.  Used by `length_bound` (`hpx`), `comp_col_bound`
(`hsq`) and `composite_sketch` (`hsq`); the identity behind it is
`9x² - (x+2)² = 4(2x+1)(x-1)`. -/
lemma sq_add_two_sq_le {x : ℝ} (hx : 1 ≤ x) : (x + 2) ^ 2 ≤ 9 * x ^ 2 := by
  have h1 : (0 : ℝ) ≤ x - 1 := by linarith
  have h2 : (0 : ℝ) ≤ 2 * x + 1 := by linarith
  nlinarith [mul_nonneg h1 h2]
/-- `a ^ 2 ≤ 9 b ^ 2` from `0 ≤ a ≤ 3 b` (used for `lg (n+2) ^ 2 ≤ 9 lg n ^ 2`). -/
lemma sq_le_nine_sq {a b : ℝ} (h0 : 0 ≤ a) (h : a ≤ 3 * b) (hb : 0 ≤ b) : a ^ 2 ≤ 9 * b ^ 2 := by
  have h1 : a * a ≤ (3 * b) * (3 * b) := mul_le_mul h h h0 (by linarith [hb])
  nlinarith [h1]
/-- `1 ≤ x ^ 2` for `1 ≤ x`. -/
lemma one_le_sq {x : ℝ} (hx : 1 ≤ x) : (1 : ℝ) ≤ x ^ 2 := by
  have h : (1 : ℝ) * 1 ≤ x * x := mul_le_mul hx hx (by norm_num) (by linarith)
  have h' : (1 : ℝ) ≤ x * x := by linarith
  rwa [pow_two]
/-- `1 ≤ x * y` for `1 ≤ x`, `1 ≤ y`. -/
lemma one_le_mul_one_le {x y : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y) : (1 : ℝ) ≤ x * y := by
  have h : (1 : ℝ) * 1 ≤ x * y := mul_le_mul hx hy (by norm_num) (by linarith)
  linarith
/-- `9 (4C'+1) Cu + 9 K23 > 0`, the constant `Cuc` of `composite_sketch` is positive. -/
lemma Cuc_pos {C' : ℕ} {Cu K23 : ℝ} (hCu : 0 < Cu) (hK23 : 0 < K23) :
    0 < 9 * (4 * (C' : ℝ) + 1) * Cu + 9 * K23 := by
  have h1 : (0 : ℝ) < 4 * (C' : ℝ) + 1 := by positivity
  nlinarith [mul_pos h1 hCu]

/-! ## 2. The children, instantiated as the paper's §3.2 children -/
/-- **`6toplevel.tex` lines 324–328**: "the `ℓ` child calls take `d exp(O((log log n)²))` time".
If `ℓ ≤ C (log n + 2)²` (`ℓ = B w ≤ C' log log n · log n · …`, §6.2), then the sum of `ℓ` bounds
`Cd · d · exp (Cd (log log n)²)` is again of 6.5's shape, with constant `Cd² e⁶`:
the only cost is the additive `2` of `log(lg n + 2) ≤ lg lg n + 2` and `lg lg n ≤ (lg lg n)² + 1`. -/
lemma time_sum_le (C : ℝ) (hC : 1 ≤ C) (n d ℓ : ℕ) (hn : 2 ≤ n) (hd : 1 ≤ d)
    (hℓ : (ℓ : ℝ) ≤ C * (lg (n : ℝ) + 2) ^ 2) :
    (ℓ : ℝ) * (C * (d : ℝ) * Real.exp (C * lg (lg (n : ℝ)) ^ 2)) ≤
      (C ^ 2 * Real.exp 6) * (d : ℝ) *
        Real.exp ((C ^ 2 * Real.exp 6) * lg (lg (n : ℝ)) ^ 2) := by
  set y : ℝ := lg (lg (n : ℝ)) with hy
  set x : ℝ := y ^ 2 with hx
  have hx0 : (0 : ℝ) ≤ x := by positivity
  have hy0 : (0 : ℝ) ≤ y := lg_lg_nonneg hn
  have hyx : y ≤ x + 1 := by nlinarith
  have hlg1 : (1 : ℝ) ≤ lg (n : ℝ) := one_le_lg hn
  have hCpos : (0 : ℝ) < C := lt_of_lt_of_le zero_lt_one hC
  have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hlogC : (0 : ℝ) ≤ Real.log C := Real.log_nonneg hC
  -- `log ℓ ≤ log C + 2 (lg lg n + 2)`
  have hlogℓ : Real.log (ℓ : ℝ) ≤ Real.log C + 2 * (y + 2) := by
    rcases Nat.eq_zero_or_pos ℓ with h0 | hpos
    · subst h0
      simp only [Nat.cast_zero, Real.log_zero]
      nlinarith
    · have hcast : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast hpos
      have harg : (0 : ℝ) < lg (n : ℝ) + 2 := by linarith
      have hargne : lg (n : ℝ) + 2 ≠ 0 := ne_of_gt harg
      have h1 : Real.log (ℓ : ℝ) ≤ Real.log (C * (lg (n : ℝ) + 2) ^ 2) :=
        Real.log_le_log hcast hℓ
      have hCne : C ≠ 0 := ne_of_gt hCpos
      have hsplit : Real.log (C * (lg (n : ℝ) + 2) ^ 2) =
          Real.log C + 2 * Real.log (lg (n : ℝ) + 2) := by
        rw [show ((lg (n : ℝ) + 2) ^ 2) = (lg (n : ℝ) + 2) * (lg (n : ℝ) + 2) by ring]
        rw [Real.log_mul hCne (mul_ne_zero hargne hargne), Real.log_mul hargne hargne]
        ring
      have h5 : Real.log (lg (n : ℝ) + 2) ≤ y + 2 := log_lg_add_two_le hn
      linarith
  -- exponent comparison
  have hcoef : (2 : ℝ) ≤ C ^ 2 * Real.exp 6 - C - 1 := by
    have h6 : (4 : ℝ) ≤ Real.exp 6 := by
      have h := Real.add_one_le_exp (x := 6)
      linarith
    nlinarith
  have hexp_le : Real.exp (2 * y + 4 + C * x) ≤ Real.exp (6 + (C ^ 2 * Real.exp 6) * x) := by
    apply Real.exp_le_exp.2
    nlinarith
  -- `ℓ ≤ C exp (2y + 4)`
  have hℓ_le : (ℓ : ℝ) ≤ C * Real.exp (2 * y + 4) := by
    rcases Nat.eq_zero_or_pos ℓ with h0 | hpos
    · subst h0
      have : (0 : ℝ) ≤ C * Real.exp (2 * y + 4) := by positivity
      simpa using this
    · have hcast : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast hpos
      have h1 : Real.exp (Real.log (ℓ : ℝ)) ≤ Real.exp (Real.log C + 2 * (y + 2)) :=
        Real.exp_le_exp.2 hlogℓ
      have h2 : Real.exp (Real.log (ℓ : ℝ)) = (ℓ : ℝ) := Real.exp_log hcast
      have h3 : Real.exp (Real.log C + 2 * (y + 2)) = C * Real.exp (2 * y + 4) := by
        rw [Real.exp_add, Real.exp_log hCpos]
        congr 1
        ring
      rw [h2, h3] at h1
      exact h1
  -- combine
  have hZ : (0 : ℝ) ≤ C * (d : ℝ) * Real.exp (C * x) := by positivity
  have step1 : (ℓ : ℝ) * (C * (d : ℝ) * Real.exp (C * x)) ≤
      (C * Real.exp (2 * y + 4)) * (C * (d : ℝ) * Real.exp (C * x)) :=
    mul_le_mul_of_nonneg_right hℓ_le hZ
  have step2 : (C * Real.exp (2 * y + 4)) * (C * (d : ℝ) * Real.exp (C * x)) =
      (C ^ 2 * (d : ℝ)) * Real.exp (2 * y + 4 + C * x) := by
    have hEq : (C * Real.exp (2 * y + 4)) * (C * (d : ℝ) * Real.exp (C * x)) =
        C ^ 2 * (d : ℝ) * (Real.exp (2 * y + 4) * Real.exp (C * x)) := by ring
    rw [hEq, ← Real.exp_add]
  have step3 : (C ^ 2 * (d : ℝ)) * Real.exp (2 * y + 4 + C * x) ≤
      (C ^ 2 * (d : ℝ)) * Real.exp (6 + (C ^ 2 * Real.exp 6) * x) := by
    apply mul_le_mul_of_nonneg_left hexp_le
    positivity
  have step4 : (C ^ 2 * (d : ℝ)) * Real.exp (6 + (C ^ 2 * Real.exp 6) * x) =
      (C ^ 2 * Real.exp 6) * (d : ℝ) *
        Real.exp ((C ^ 2 * Real.exp 6) * x) := by
    have hEq : (C ^ 2 * (d : ℝ)) * Real.exp (6 + (C ^ 2 * Real.exp 6) * x) =
        C ^ 2 * (d : ℝ) * (Real.exp 6 * Real.exp ((C ^ 2 * Real.exp 6) * x)) := by
      rw [Real.exp_add]
    rw [hEq]; ring
  calc (ℓ : ℝ) * (C * (d : ℝ) * Real.exp (C * x))
      ≤ (C * Real.exp (2 * y + 4)) * (C * (d : ℝ) * Real.exp (C * x)) := step1
    _ = (C ^ 2 * (d : ℝ)) * Real.exp (2 * y + 4 + C * x) := step2
    _ ≤ (C ^ 2 * (d : ℝ)) * Real.exp (6 + (C ^ 2 * Real.exp 6) * x) := step3
    _ = (C ^ 2 * Real.exp 6) * (d : ℝ) *
        Real.exp ((C ^ 2 * Real.exp 6) * x) := step4

/-! ## 5. The cell array is `d w` cells wide: `d w ≤ L(n,d) + 3d`

`6toplevel.tex` line 305 and its footnote, with `N = ⌈n/d⌉` and `w = ⌈log(N+1)⌉`:

> Since `N = ⌈n/d⌉` and `w = ⌈log(N+1)⌉`, we have `dw = d log(n/d) + O(d) = h_n(d) + O(d) = L(n,d) + O(d)`.

This section proves the two halves of that display with the same universal constant `3`:

* `d_mul_w_le`: `d w ≤ L(n,d) + 3d` — the direction the length bound of Theorem 6.5 needs, because
  it pays for the `d w` cells out of `L(n,d)` plus `O(d)`;
* `hN_le_L`: `h_n(d) ≤ L(n,d) + 3d` — the converse, which is what "`dw = h_n(d) + O(d)`" needs.

Both rest on the same three ingredients: `L(n,d) ≥ log binom(n,d)` (the `a = d` term of the sum in
`L`), `binom(n,d) ≥ (n/2d)^d` (`n - i ≥ n - d + 1 ≥ n/2` for `i < d`, and `d! ≤ d^d`), and
`log(n/d) = log(n/2d) + 1`. -/
/-- `lg x ≥ 0` for `x ≥ 1`. -/
lemma lg_nonneg {x : ℝ} (hx : 1 ≤ x) : 0 ≤ lg x := by
  have h2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hl : 0 ≤ Real.log x := Real.log_nonneg hx
  show 0 ≤ Real.log x / Real.log 2
  exact div_nonneg hl (le_of_lt h2)
/-- `lg` is monotone on the positives. -/
lemma lg_mono {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) : lg x ≤ lg y := by
  have h2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have h := Real.log_le_log hx hxy
  show Real.log x / Real.log 2 ≤ Real.log y / Real.log 2
  exact div_le_div_of_nonneg_right h (le_of_lt h2)
/-- `lg (x y) = lg x + lg y`. -/
lemma lg_mul {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) : lg (x * y) = lg x + lg y :=
  Real.logb_mul hx hy
/-- `lg (x^n) = n lg x`. -/
lemma lg_pow {x : ℝ} (hx : x ≠ 0) (n : ℕ) : lg (x ^ n) = (n : ℝ) * lg x := by
  induction n with
  | zero => rw [pow_zero, Nat.cast_zero, zero_mul]; exact Real.logb_one
  | succ k ih =>
    rw [pow_succ, lg_mul (pow_ne_zero k hx) hx, ih]
    push_cast
    ring
/-- `L(n,d) ≥ log binom(n,d)`: `binom(n,d)` is the `a = d` term of the sum inside `L`. -/
lemma lg_choose_le_L (n d : ℕ) (hdn : d ≤ n) :
    lg ((n.choose d : ℕ) : ℝ) ≤ L n d := by
  have hmem : d ∈ Finset.range (d + 1) := Finset.mem_range.mpr (Nat.lt_succ_iff.mpr le_rfl)
  have hle : n.choose d ≤ ∑ a ∈ Finset.range (d + 1), n.choose a :=
    Finset.single_le_sum (fun i _ => Nat.zero_le _) hmem
  have hpos : (0 : ℝ) < ((n.choose d : ℕ) : ℝ) := by
    have h : 0 < n.choose d := Nat.choose_pos hdn
    exact_mod_cast h
  have hle' : ((n.choose d : ℕ) : ℝ) ≤ (((∑ a ∈ Finset.range (d + 1), n.choose a) : ℕ) : ℝ) := by
    exact_mod_cast hle
  exact Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hpos hle'
/-- **`binom(n,d) ≥ (n/2d)^d`** for `2d ≤ n` (ingredient (ii) of the length bound): in
`n.descFactorial d = ∏_{i<d} (n-i) = d! binom(n,d)` every factor is `≥ n - d + 1 ≥ n/2`
(`2d ≤ n + 2`), and `d! ≤ d^d`. -/
lemma choose_ge (n d : ℕ) (hd : 1 ≤ d) (hdn : 2 * d ≤ n) :
    ((n : ℝ) / (2 * (d : ℝ))) ^ d ≤ ((n.choose d : ℕ) : ℝ) := by
  have hdn' : d ≤ n := by omega
  have hdesc : ((n.descFactorial d : ℕ) : ℝ) = ∏ i ∈ Finset.range d, ((n - i : ℕ) : ℝ) := by
    rw [Nat.descFactorial_eq_prod_range]
    push_cast
    rfl
  have hfact : ((n.choose d : ℕ) : ℝ) * ((Nat.factorial d : ℕ) : ℝ) =
      ((n.descFactorial d : ℕ) : ℝ) := by
    rw [Nat.descFactorial_eq_factorial_mul_choose]
    push_cast
    ring
  -- every factor of the descending factorial is at least `n - d + 1`
  have hprod : ((n - d + 1 : ℕ) : ℝ) ^ d ≤ ∏ i ∈ Finset.range d, ((n - i : ℕ) : ℝ) := by
    have hstep : ∏ i ∈ Finset.range d, ((n - d + 1 : ℕ) : ℝ) ≤
        ∏ i ∈ Finset.range d, ((n - i : ℕ) : ℝ) := by
      refine Finset.prod_le_prod (fun i _ => by positivity) (fun i hi => ?_)
      have hi' : i ≤ d - 1 := by
        have := Finset.mem_range.mp hi
        omega
      have h1 : n - (d - 1) ≤ n - i := Nat.sub_le_sub_left hi' n
      have h2 : n - d + 1 = n - (d - 1) := by omega
      rw [h2]
      exact_mod_cast h1
    calc ((n - d + 1 : ℕ) : ℝ) ^ d = ∏ i ∈ Finset.range d, ((n - d + 1 : ℕ) : ℝ) := by
          rw [Finset.prod_const, Finset.card_range]
      _ ≤ ∏ i ∈ Finset.range d, ((n - i : ℕ) : ℝ) := hstep
  -- `n/2d · d = n/2 ≤ n - d + 1`
  have hbase : ((n : ℝ) / (2 * (d : ℝ))) * (d : ℝ) ≤ ((n - d + 1 : ℕ) : ℝ) := by
    have hcast : ((n - d + 1 : ℕ) : ℝ) = (n : ℝ) - (d : ℝ) + 1 := by
      rw [Nat.cast_add, Nat.cast_sub hdn', Nat.cast_one]
    have hEq : ((n : ℝ) / (2 * (d : ℝ))) * (d : ℝ) = (n : ℝ) / 2 := by
      field_simp
    have h2d : (2 : ℝ) * (d : ℝ) ≤ (n : ℝ) := by exact_mod_cast hdn
    rw [hcast, hEq]
    linarith
  -- `(n/2d)^d · d! ≤ (n/2d)^d · d^d = (n/2)^d ≤ (n-d+1)^d`
  have hA : ((n : ℝ) / (2 * (d : ℝ))) ^ d * ((Nat.factorial d : ℕ) : ℝ) ≤
      ((n - d + 1 : ℕ) : ℝ) ^ d := by
    have hcast : ((Nat.factorial d : ℕ) : ℝ) ≤ (d : ℝ) ^ d := by
      have h := Nat.factorial_le_pow d
      calc ((Nat.factorial d : ℕ) : ℝ) ≤ ((d ^ d : ℕ) : ℝ) := by exact_mod_cast h
        _ = (d : ℝ) ^ d := by push_cast; ring
    have hb0 : (0 : ℝ) ≤ ((n : ℝ) / (2 * (d : ℝ))) ^ d := by positivity
    calc ((n : ℝ) / (2 * (d : ℝ))) ^ d * ((Nat.factorial d : ℕ) : ℝ)
        ≤ ((n : ℝ) / (2 * (d : ℝ))) ^ d * (d : ℝ) ^ d :=
          mul_le_mul_of_nonneg_left hcast hb0
      _ = (((n : ℝ) / (2 * (d : ℝ))) * (d : ℝ)) ^ d := by rw [mul_pow]
      _ ≤ ((n - d + 1 : ℕ) : ℝ) ^ d := pow_le_pow_left₀ (by positivity) hbase d
  -- divide by `d! > 0`
  have hcont : ((n : ℝ) / (2 * (d : ℝ))) ^ d * ((Nat.factorial d : ℕ) : ℝ) ≤
      ((n.choose d : ℕ) : ℝ) * ((Nat.factorial d : ℕ) : ℝ) := by
    have h1 : ((n : ℝ) / (2 * (d : ℝ))) ^ d * ((Nat.factorial d : ℕ) : ℝ) ≤
        ((n.descFactorial d : ℕ) : ℝ) := by
      rw [hdesc]
      exact le_trans hA hprod
    linarith [hfact]
  have hfacpos : (0 : ℝ) < ((Nat.factorial d : ℕ) : ℝ) := by
    have h := Nat.factorial_pos d
    exact_mod_cast h
  exact le_of_mul_le_mul_right hcont hfacpos
/-- **`d log(n/2d) ≤ L(n,d)`**: the logarithm of ingredient (ii), which is the form the length
computation uses.  (Note this is *not* `log(n/2d) ≤ L`: the `d` is essential, since `L` pays for the
whole product `d w`.) -/
lemma d_mul_lg_half_le_L (n d : ℕ) (hd : 1 ≤ d) (hdn : 2 * d ≤ n) :
    (d : ℝ) * lg ((n : ℝ) / (2 * (d : ℝ))) ≤ L n d := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    have h : 0 < n := by omega
    exact_mod_cast h
  have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hx0 : (0 : ℝ) < (n : ℝ) / (2 * (d : ℝ)) := by
    apply div_pos hnpos
    linarith
  have hAd : lg (((n : ℝ) / (2 * (d : ℝ))) ^ d) ≤ L n d :=
    le_trans (lg_mono (pow_pos hx0 d) (choose_ge n d hd hdn)) (lg_choose_le_L n d (by omega))
  rw [lg_pow (ne_of_gt hx0) d] at hAd
  exact hAd
/-- `lg (n/d) = lg (n/2d) + 1`. -/
lemma lg_div_eq_lg_half_add_one {n d : ℕ} (hn : 0 < n) (hd : 1 ≤ d) :
    lg ((n : ℝ) / (d : ℝ)) = lg ((n : ℝ) / (2 * (d : ℝ))) + 1 := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hx0 : (0 : ℝ) < (n : ℝ) / (2 * (d : ℝ)) := by
    apply div_pos hnpos
    linarith
  have hEq : (n : ℝ) / (d : ℝ) = ((n : ℝ) / (2 * (d : ℝ))) * 2 := by
    field_simp
  rw [hEq, lg_mul (ne_of_gt hx0) (by norm_num), lg_two]
/-- **`w ≤ log n + 2`**, `w = ⌈log(N+1)⌉` with `N = ⌈n/d⌉` and `n ≥ 2d`: `N ≤ n/d + 1`, and
`log(n/d + 2) ≤ log(n/d) + 1` because `n/d ≥ 2` (`6toplevel.tex` line 305: `w = O(log n)`). -/
lemma w_le (n d : ℕ) (hd : 1 ≤ d) (hdn : 2 * d ≤ n) :
    ((⌈lg (((⌈(n : ℝ) / (d : ℝ)⌉₊ : ℝ) + 1))⌉₊ : ℕ) : ℝ) ≤ lg ((n : ℝ) / (d : ℝ)) + 2 := by
  have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have h2d : (2 : ℝ) * (d : ℝ) ≤ (n : ℝ) := by exact_mod_cast hdn
  have hx2 : (2 : ℝ) ≤ (n : ℝ) / (d : ℝ) := by
    rw [le_div_iff₀ hd0]
    linarith
  have hxpos : (0 : ℝ) < (n : ℝ) / (d : ℝ) := by linarith
  -- the ceiling costs one `1`
  have hc : ((⌈lg (((⌈(n : ℝ) / (d : ℝ)⌉₊ : ℝ) + 1))⌉₊ : ℕ) : ℝ) ≤
      lg (((⌈(n : ℝ) / (d : ℝ)⌉₊ : ℝ) + 1)) + 1 := by
    have hnn : (0 : ℝ) ≤ lg (((⌈(n : ℝ) / (d : ℝ)⌉₊ : ℝ) + 1)) := by
      apply lg_nonneg
      have h0 : (0 : ℝ) ≤ (⌈(n : ℝ) / (d : ℝ)⌉₊ : ℝ) := by positivity
      linarith
    have h := Nat.ceil_lt_add_one hnn
    linarith
  -- `N ≤ n/d + 1`
  have hmono : lg (((⌈(n : ℝ) / (d : ℝ)⌉₊ : ℝ) + 1)) ≤ lg ((n : ℝ) / (d : ℝ) + 2) := by
    apply lg_mono (by positivity)
    have hN := Nat.ceil_lt_add_one (le_of_lt hxpos)
    linarith
  -- `log(n/d + 2) ≤ log(n/d) + 1` since `x + 2 ≤ 2x` at `x = n/d ≥ 2`
  have hstep : lg ((n : ℝ) / (d : ℝ) + 2) ≤ lg ((n : ℝ) / (d : ℝ)) + 1 := by
    have h3 : lg ((n : ℝ) / (d : ℝ) + 2) ≤ lg (2 * ((n : ℝ) / (d : ℝ))) := by
      apply lg_mono (by linarith)
      linarith
    have h4 : lg (2 * ((n : ℝ) / (d : ℝ))) = lg 2 + lg ((n : ℝ) / (d : ℝ)) :=
      lg_mul (by norm_num) (ne_of_gt hxpos)
    rw [h4, lg_two] at h3
    linarith
  linarith
/-- **Task 1, forward direction — `d w ≤ L(n,d) + 3d`** (`6toplevel.tex` line 305):
`d w ≤ d (log(n/d) + 2) = d log(n/2d) + 3d ≤ d L(n,d) ... ` — precisely,
`d log(n/2d) ≤ d L(n,d)` and `log(n/d) = log(n/2d) + 1`. -/
theorem d_mul_w_le (n d : ℕ) (hd : 1 ≤ d) (hdn : 2 * d ≤ n) :
    (d : ℝ) * ((⌈lg (((⌈(n : ℝ) / (d : ℝ)⌉₊ : ℝ) + 1))⌉₊ : ℕ) : ℝ) ≤ L n d + 3 * (d : ℝ) := by
  have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have h1 : (d : ℝ) * ((⌈lg (((⌈(n : ℝ) / (d : ℝ)⌉₊ : ℝ) + 1))⌉₊ : ℕ) : ℝ) ≤
      (d : ℝ) * (lg ((n : ℝ) / (d : ℝ)) + 2) :=
    mul_le_mul_of_nonneg_left (w_le n d hd hdn) (le_of_lt hd0)
  have h2 : (d : ℝ) * lg ((n : ℝ) / (d : ℝ)) ≤ L n d + (d : ℝ) := by
    rw [lg_div_eq_lg_half_add_one (by omega : 0 < n) hd]
    linarith [d_mul_lg_half_le_L n d hd hdn]
  linarith [h1, h2]
/-- **The final CR sketch is `O(d)` bits.**  `6toplevel.tex` line 248: "the final CR sketch uses
`O(t log² n) = O(η d log² n) = O(d/log n)` bits".  With `t = resid ≤ ⌈2η(d+1)⌉ ≤ 2η(d+1)+1 ≤ 5ηd`
(the last step is the row–column regime hypothesis `1 ≤ ηd`), `t log²(n+2) ≤ 45 d (η log² n) ≤ 45 d`
because `η = log^{-A} n` with `A ≥ 2` and `log(n+2) ≤ 3 log n`. -/
lemma cr_length_le (A : ℕ) (hA : 2 ≤ A) (KCR : ℝ) (hKCR : 0 ≤ KCR) (n d t : ℕ) (η : ℝ)
    (hη : η = ((lg (n : ℝ)) ^ A)⁻¹) (hd : 1 ≤ d)
    (ht : (t : ℝ) ≤ 2 * η * ((d : ℝ) + 1) + 1) (hηd : 1 ≤ η * (d : ℝ)) (hn : 2 ≤ n) :
    KCR * ((t : ℝ) * lg ((n : ℝ) + 2) ^ 2) ≤ 45 * KCR * (d : ℝ) := by
  have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hx1 : (1 : ℝ) ≤ lg (n : ℝ) := one_le_lg hn
  have hx0 : (0 : ℝ) < lg (n : ℝ) := lt_of_lt_of_le zero_lt_one hx1
  have hηpos : (0 : ℝ) < η := by
    by_contra h
    rw [not_lt] at h
    nlinarith [hηd, hd0, h]
  -- `t ≤ 5 η d`
  have ht5 : (t : ℝ) ≤ 5 * η * (d : ℝ) := by
    have h1 : (d : ℝ) + 1 ≤ 2 * (d : ℝ) := by linarith
    have h2 : 2 * η * ((d : ℝ) + 1) ≤ 2 * η * (2 * (d : ℝ)) :=
      mul_le_mul_of_nonneg_left h1 (by linarith)
    nlinarith [ht, h2, hηd]
  -- `log (n+2) ≤ 3 log n`
  have hlog3 : lg ((n : ℝ) + 2) ≤ 3 * lg (n : ℝ) := by
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
    have h2n : (n : ℝ) + 2 ≤ 4 * (n : ℝ) := by linarith
    have hle : lg ((n : ℝ) + 2) ≤ lg (4 * (n : ℝ)) := lg_mono (by positivity) h2n
    have h4 : lg (4 * (n : ℝ)) = 2 + lg (n : ℝ) := by
      rw [lg_mul (by norm_num) (by positivity),
        show lg (4 : ℝ) = 2 from by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, lg_pow (by norm_num) 2, lg_two]; norm_num]
    linarith
  have hlog : lg ((n : ℝ) + 2) ^ 2 ≤ 9 * lg (n : ℝ) ^ 2 := by
    have h0 : (0 : ℝ) ≤ lg ((n : ℝ) + 2) := by
      apply lg_nonneg
      have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
      linarith
    nlinarith [hlog3, hx0, h0]
  -- `η log² n ≤ 1`
  have heta : η * lg (n : ℝ) ^ 2 ≤ 1 := by
    have hxA : lg (n : ℝ) ^ 2 ≤ (lg (n : ℝ)) ^ A := pow_le_pow_right₀ hx1 hA
    have h1 : η * lg (n : ℝ) ^ 2 ≤ η * (lg (n : ℝ)) ^ A :=
      mul_le_mul_of_nonneg_left hxA (le_of_lt hηpos)
    rw [hη] at h1 ⊢
    have hxne : (lg (n : ℝ)) ^ A ≠ 0 := by positivity
    calc ((lg (n : ℝ)) ^ A)⁻¹ * lg (n : ℝ) ^ 2
        ≤ ((lg (n : ℝ)) ^ A)⁻¹ * (lg (n : ℝ)) ^ A := h1
      _ = 1 := inv_mul_cancel₀ hxne
  -- assemble
  have htlog : (t : ℝ) * lg ((n : ℝ) + 2) ^ 2 ≤ 45 * (d : ℝ) := by
    have h2 : (t : ℝ) * lg ((n : ℝ) + 2) ^ 2 ≤ (5 * η * (d : ℝ)) * (9 * lg (n : ℝ) ^ 2) := by
      apply mul_le_mul ht5 hlog (by positivity) (by positivity)
    have h3 : (5 * η * (d : ℝ)) * (9 * lg (n : ℝ) ^ 2) = 45 * (d : ℝ) * (η * lg (n : ℝ) ^ 2) := by
      ring
    have h4 : 45 * (d : ℝ) * (η * lg (n : ℝ) ^ 2) ≤ 45 * (d : ℝ) * 1 :=
      mul_le_mul_of_nonneg_left heta (by positivity)
    linarith [h2, h3, h4]
  have := mul_le_mul_of_nonneg_left htlog hKCR
  linarith [this]
/-- **The length bound of Theorem 6.5**, assembled from the paper's displayed chain
(`6toplevel.tex` lines 293–303).  `S` is `Σ_s (X_s + α h_d(Y_s))` — the total capacity of the `ℓ`
children as supplied by Lemma 6.3 (iii), i.e. after `Σ_a q_a = d` (Lemma 6.1) — and `LenCR` is the
size of the final CR sketch.

The conclusion is `M ≤ L(n,d) + Cl d + Cl λ log^{p₁+2} n`, exactly the shape of Theorem 6.5's
`(M:ℝ) ≤ L n d + Cl * d + Cl * (lam:ℝ) * lg n ^ pl` with `pl = p₁ + 2`. -/
theorem length_bound (C₁ C₂ C₃ K KCR Cl : ℝ) (p₁ C' : ℕ) (n d lam w ell : ℕ)
    (M LenCR S : ℝ)
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hC₃ : 0 ≤ C₃) (hK : 0 ≤ K) (hKCR : 0 ≤ KCR)
    (hCp : 0 ≤ (C' : ℝ))
    (hCl : 3 + 3 * C₁ + (1 + C₁) * K * (1 + (C' : ℝ)) + 9 * C₂ * (C' : ℝ) + 45 * KCR
        + 9 * C₃ * (C' : ℝ) ≤ Cl)
    (hn : 2 ≤ n) (hd : 1 ≤ d) (_hdn : 2 * d ≤ n)
    (hell : (ell : ℝ) ≤ (C' : ℝ) * (lg (n : ℝ) + 2) ^ 2)
    (hw : (w : ℝ) ≤ lg (n : ℝ) + 2)
    (hS : S ≤ (d : ℝ) * w + K * (d : ℝ) + K * ((C' : ℝ) * (d : ℝ) / lg (n : ℝ)))
    (hM : M ≤ LenCR + (1 + C₁ / lg (n : ℝ)) * S
        + (ell : ℝ) * (C₂ * ((d : ℝ) / lg (n : ℝ) ^ 8))
        + C₃ * (ell : ℝ) * (lam : ℝ) * lg (n : ℝ) ^ p₁)
    (hCR : LenCR ≤ 45 * KCR * (d : ℝ))
    (hdw : (d : ℝ) * w ≤ L n d + 3 * (d : ℝ)) :
    M ≤ L n d + Cl * (d : ℝ) + Cl * (lam : ℝ) * lg (n : ℝ) ^ (p₁ + 2) := by
  have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hx1 : (1 : ℝ) ≤ lg (n : ℝ) := one_le_lg hn
  have hx0 : (0 : ℝ) < lg (n : ℝ) := lt_of_lt_of_le zero_lt_one hx1
  have hz0 : (0 : ℝ) ≤ 1 + C₁ / lg (n : ℝ) :=
    add_nonneg zero_le_one (div_nonneg hC₁ (le_of_lt hx0))
  -- the three savings: `w/x ≤ 3`, `1/x ≤ 1`, `1/x² ≤ 1`
  have hxinv : (1 : ℝ) / lg (n : ℝ) ≤ 1 := by
    rw [div_le_one hx0]
    linarith
  have hwinv : (w : ℝ) / lg (n : ℝ) ≤ 3 := by
    rw [div_le_iff₀ hx0]
    nlinarith [hw]
  have hinvsq : (1 : ℝ) / lg (n : ℝ) * (1 / lg (n : ℝ)) ≤ 1 := by
    have h0 : (0 : ℝ) ≤ 1 / lg (n : ℝ) := by positivity
    nlinarith [hxinv, h0]
  -- `(1 + C₁/log n) d w ≤ d w + 3 C₁ d`
  have hA : (1 + C₁ / lg (n : ℝ)) * ((d : ℝ) * w) ≤ (d : ℝ) * w + 3 * C₁ * (d : ℝ) := by
    have hEq : (1 + C₁ / lg (n : ℝ)) * ((d : ℝ) * w) =
        (d : ℝ) * w + C₁ * (d : ℝ) * ((w : ℝ) / lg (n : ℝ)) := by field_simp
    rw [hEq]
    have h2 : C₁ * (d : ℝ) * ((w : ℝ) / lg (n : ℝ)) ≤ C₁ * (d : ℝ) * 3 :=
      mul_le_mul_of_nonneg_left hwinv (by positivity)
    linarith
  -- `(1 + C₁/log n) K d ≤ K d + C₁ K d`
  have hBK : (1 + C₁ / lg (n : ℝ)) * (K * (d : ℝ)) ≤ K * (d : ℝ) + C₁ * K * (d : ℝ) := by
    have hEq : (1 + C₁ / lg (n : ℝ)) * (K * (d : ℝ)) =
        K * (d : ℝ) + C₁ * K * (d : ℝ) * ((1 : ℝ) / lg (n : ℝ)) := by field_simp
    rw [hEq]
    have h2 : C₁ * K * (d : ℝ) * ((1 : ℝ) / lg (n : ℝ)) ≤ C₁ * K * (d : ℝ) * 1 :=
      mul_le_mul_of_nonneg_left hxinv (by positivity)
    linarith
  -- `(1 + C₁/log n) K C' d/log n ≤ K C' d + C₁ K C' d`
  have hBC : (1 + C₁ / lg (n : ℝ)) * (K * ((C' : ℝ) * (d : ℝ) / lg (n : ℝ))) ≤
      K * ((C' : ℝ) * (d : ℝ)) + C₁ * K * (C' : ℝ) * (d : ℝ) := by
    have hEq : (1 + C₁ / lg (n : ℝ)) * (K * ((C' : ℝ) * (d : ℝ) / lg (n : ℝ))) =
        K * ((C' : ℝ) * (d : ℝ)) * ((1 : ℝ) / lg (n : ℝ)) +
          C₁ * K * (C' : ℝ) * (d : ℝ) *
            ((1 : ℝ) / lg (n : ℝ) * ((1 : ℝ) / lg (n : ℝ))) := by field_simp
    rw [hEq]
    have h2 : K * ((C' : ℝ) * (d : ℝ)) * ((1 : ℝ) / lg (n : ℝ)) ≤ K * ((C' : ℝ) * (d : ℝ)) := by
      calc K * ((C' : ℝ) * (d : ℝ)) * ((1 : ℝ) / lg (n : ℝ))
          ≤ K * ((C' : ℝ) * (d : ℝ)) * 1 :=
            mul_le_mul_of_nonneg_left hxinv (by positivity)
        _ = K * ((C' : ℝ) * (d : ℝ)) := by ring
    have h3 : C₁ * K * (C' : ℝ) * (d : ℝ) *
          ((1 : ℝ) / lg (n : ℝ) * ((1 : ℝ) / lg (n : ℝ))) ≤ C₁ * K * (C' : ℝ) * (d : ℝ) := by
      calc C₁ * K * (C' : ℝ) * (d : ℝ) *
            ((1 : ℝ) / lg (n : ℝ) * ((1 : ℝ) / lg (n : ℝ)))
          ≤ C₁ * K * (C' : ℝ) * (d : ℝ) * 1 :=
            mul_le_mul_of_nonneg_left hinvsq (by positivity)
        _ = C₁ * K * (C' : ℝ) * (d : ℝ) := by ring
    linarith
  -- `(1 + C₁/log n) S ≤ d w + (3C₁ + (1+C₁)K(1+C')) d`
  have hstepA : (1 + C₁ / lg (n : ℝ)) * S ≤
      (d : ℝ) * w + (3 * C₁ + (1 + C₁) * K * (1 + (C' : ℝ))) * (d : ℝ) := by
    have h1 : (1 + C₁ / lg (n : ℝ)) * S ≤
        (1 + C₁ / lg (n : ℝ)) *
          ((d : ℝ) * w + K * (d : ℝ) + K * ((C' : ℝ) * (d : ℝ) / lg (n : ℝ))) :=
      mul_le_mul_of_nonneg_left hS hz0
    have hexp : (1 + C₁ / lg (n : ℝ)) *
          ((d : ℝ) * w + K * (d : ℝ) + K * ((C' : ℝ) * (d : ℝ) / lg (n : ℝ))) =
        (1 + C₁ / lg (n : ℝ)) * ((d : ℝ) * w) + (1 + C₁ / lg (n : ℝ)) * (K * (d : ℝ))
          + (1 + C₁ / lg (n : ℝ)) * (K * ((C' : ℝ) * (d : ℝ) / lg (n : ℝ))) := by ring
    linarith [h1, hexp, hA, hBK, hBC]
  -- `ℓ ≤ 9 C' log² n`
  have hell9 : (ell : ℝ) ≤ (C' : ℝ) * 9 * lg (n : ℝ) ^ 2 := by
    have hpx : (lg (n : ℝ) + 2) ^ 2 ≤ 9 * lg (n : ℝ) ^ 2 := sq_add_two_sq_le hx1
    have h1 : (C' : ℝ) * (lg (n : ℝ) + 2) ^ 2 ≤ (C' : ℝ) * (9 * lg (n : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left hpx hCp
    linarith [hell, h1]
  -- `ℓ C₂ d / log⁸ n ≤ 9 C₂ C' d`
  have hB1 : (ell : ℝ) * (C₂ * ((d : ℝ) / lg (n : ℝ) ^ 8)) ≤ 9 * C₂ * (C' : ℝ) * (d : ℝ) := by
    have hd8 : (0 : ℝ) ≤ C₂ * ((d : ℝ) / lg (n : ℝ) ^ 8) := by positivity
    have hratio : lg (n : ℝ) ^ 2 / lg (n : ℝ) ^ 8 ≤ 1 := by
      rw [div_le_one (by positivity)]
      exact pow_le_pow_right₀ hx1 (by norm_num : 2 ≤ 8)
    have key : ((C' : ℝ) * 9 * lg (n : ℝ) ^ 2) * (C₂ * ((d : ℝ) / lg (n : ℝ) ^ 8)) =
        9 * C₂ * (C' : ℝ) * (d : ℝ) * (lg (n : ℝ) ^ 2 / lg (n : ℝ) ^ 8) := by field_simp
    calc (ell : ℝ) * (C₂ * ((d : ℝ) / lg (n : ℝ) ^ 8))
        ≤ ((C' : ℝ) * 9 * lg (n : ℝ) ^ 2) * (C₂ * ((d : ℝ) / lg (n : ℝ) ^ 8)) :=
          mul_le_mul_of_nonneg_right hell9 hd8
      _ = 9 * C₂ * (C' : ℝ) * (d : ℝ) * (lg (n : ℝ) ^ 2 / lg (n : ℝ) ^ 8) := key
      _ ≤ 9 * C₂ * (C' : ℝ) * (d : ℝ) * 1 :=
          mul_le_mul_of_nonneg_left hratio (by positivity)
      _ = 9 * C₂ * (C' : ℝ) * (d : ℝ) := by ring
  -- `C₃ ℓ λ log^{p₁} n ≤ 9 C₃ C' λ log^{p₁+2} n`
  have hC1 : C₃ * (ell : ℝ) * (lam : ℝ) * lg (n : ℝ) ^ p₁ ≤
      9 * C₃ * (C' : ℝ) * (lam : ℝ) * lg (n : ℝ) ^ (p₁ + 2) := by
    have hZp : (0 : ℝ) ≤ (lam : ℝ) * lg (n : ℝ) ^ p₁ := by positivity
    have h1 : (ell : ℝ) * ((lam : ℝ) * lg (n : ℝ) ^ p₁) ≤
        ((C' : ℝ) * 9 * lg (n : ℝ) ^ 2) * ((lam : ℝ) * lg (n : ℝ) ^ p₁) :=
      mul_le_mul_of_nonneg_right hell9 hZp
    have h3 : ((C' : ℝ) * 9 * lg (n : ℝ) ^ 2) * ((lam : ℝ) * lg (n : ℝ) ^ p₁) =
        9 * (C' : ℝ) * (lam : ℝ) * lg (n : ℝ) ^ (p₁ + 2) := by
      rw [pow_add]
      ring
    calc C₃ * (ell : ℝ) * (lam : ℝ) * lg (n : ℝ) ^ p₁
        = C₃ * ((ell : ℝ) * ((lam : ℝ) * lg (n : ℝ) ^ p₁)) := by ring
      _ ≤ C₃ * (((C' : ℝ) * 9 * lg (n : ℝ) ^ 2) * ((lam : ℝ) * lg (n : ℝ) ^ p₁)) :=
          mul_le_mul_of_nonneg_left h1 hC₃
      _ = 9 * C₃ * (C' : ℝ) * (lam : ℝ) * lg (n : ℝ) ^ (p₁ + 2) := by rw [h3]; ring
  -- the constant
  have hCl1 : 3 + 3 * C₁ + (1 + C₁) * K * (1 + (C' : ℝ)) + 9 * C₂ * (C' : ℝ) + 45 * KCR ≤ Cl := by
    have hnn : (0 : ℝ) ≤ 9 * C₃ * (C' : ℝ) := by positivity
    linarith [hCl]
  have hCl2 : 9 * C₃ * (C' : ℝ) ≤ Cl := by
    have hnn : (0 : ℝ) ≤ 3 + 3 * C₁ + (1 + C₁) * K * (1 + (C' : ℝ)) + 9 * C₂ * (C' : ℝ)
      + 45 * KCR := by positivity
    linarith [hCl]
  have hm1 : (3 + 3 * C₁ + (1 + C₁) * K * (1 + (C' : ℝ)) + 9 * C₂ * (C' : ℝ) + 45 * KCR)
        * (d : ℝ) ≤ Cl * (d : ℝ) :=
    mul_le_mul_of_nonneg_right hCl1 (le_of_lt hd0)
  have hm2 : 9 * C₃ * (C' : ℝ) * ((lam : ℝ) * lg (n : ℝ) ^ (p₁ + 2)) ≤
      Cl * ((lam : ℝ) * lg (n : ℝ) ^ (p₁ + 2)) :=
    mul_le_mul_of_nonneg_right hCl2 (by positivity)
  linarith [hM, hstepA, hB1, hC1, hCR, hdw, hm1, hm2]

/-! ## 7. GAP-A closed: the composite `H` of §3.2 and its length

`6toplevel.tex` (28)-(31) and §6.3 lines 288-317.  The `ℓ = B w` children are indexed by the pair
`(a,k) : Fin B × Fin w`, i.e. by the top-level column `s = a w + k` of `3construction.tex:296-298`;
child `(a,k)` is the `HintSketch` of `theorem_5_1` at universe `N = d`, with the capacities of (28)

> `X_{a,k} = min{d, ⌈q_a + η(d+1)⌉}`,  `Y_{a,k} = min{d, ⌈q_a p_k + η(d+1)⌉}`,

which are `TopParams.capX a` and `TopParams.capY a k` verbatim (`Def…TopLevel`).  The composite map
of §3.2 is `x ↦ (H_{a,k} C_{a,k}(x))_{a,k}` with `C_{a,k}(x) = ((W_{j,a})_k)_{j<d} ∈ F_2^d`, so its
total length is `Len_CR + Σ_{a,k} Len_{a,k}`.

The four inputs the paper names are instantiated here:

* **Lemma 6.3 (iii)** — `Σ_{a,k}(X_{a,k} + α h_d(Y_{a,k})) ≤ d w + K d + K C' d/log n`
  (`capacity_total_le`): this is *exactly* hypothesis `hS` of `length_bound`.  It is stated for any
  field `F` of characteristic two with a basis `b` of size `w` and an address map `ι : [N] ↪ F*`
  (`P.IsAddress ι`), which is how Lemma 6.3 itself is stated; `capacity_total_le'` then supplies
  `F = 𝔽_{2^w}` (`GaloisField 2 w`), its basis (`galoisBasis`) and `ι : [N] ↪ F*`
  (`exists_galoisAddress`), so `hS` holds with no field hypothesis left.
* **Theorem 5.1 at `N = d`** — the length of every child (`exists_child_lengths`), summed over the
  `ℓ` children (`sum_child_length_le`): this is `hM`.
* **Proposition 2.3 + Lemma 6.4** — the final CR sketch at `t = resid`: `Len_CR ≤ 45 KCR d`
  (`cr_capacity_le`, from `cr_length_le` and the residual bound `Z ≤ resid`): this is `hCR`.
* **§5** — `d w ≤ L(n,d) + 3d` (`d_mul_w_le`) and `w ≤ log n + 2` (`w_le_lgn`).

`composite_length_bound` assembles them into `Len ≤ L(n,d) + Cl d + Cl λ log^{p₁+2} n`, i.e. the
length conjunct of Theorem 6.5 at `pl = p₁ + 2`.
-/
/-- The `ℓ = Bw` children of §3.2 are the pairs `(a,k) : Fin B × Fin w`; a double sum over
`a < B`, `k < w` of `6toplevel.tex` (28) is a sum over them. -/
lemma sum_fin_prod_eq_sum_range (B w : ℕ) (f : ℕ → ℕ → ℝ) :
    (∑ p : Fin B × Fin w, f p.1.val p.2.val) = ∑ a ∈ range B, ∑ k ∈ range w, f a k := by
  rw [Fintype.sum_prod_type]
  trans ∑ a : Fin B, ∑ k ∈ range w, f a.val k
  · exact Finset.sum_congr rfl fun a _ => Fin.sum_univ_eq_sum_range (fun k => f a.val k) w
  · exact Fin.sum_univ_eq_sum_range (fun a => ∑ k ∈ range w, f a k) B
/-- `lg y ≤ 2y` for `y ≥ 1`; used to bound `B = ⌈C' log(log n + 2)⌉`. -/
lemma lg_le_two_mul {y : ℝ} (hy : 1 ≤ y) : lg y ≤ 2 * y := by
  have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2 : (1 : ℝ) / 2 ≤ Real.log 2 := by
    have h := Real.log_le_sub_one_of_pos (x := 1 / 2) (by norm_num)
    rw [Real.log_div one_ne_zero (by norm_num : (2 : ℝ) ≠ 0), Real.log_one] at h
    linarith
  have hlogy : Real.log y ≤ y - 1 := Real.log_le_sub_one_of_pos (by linarith)
  show Real.log y / Real.log 2 ≤ 2 * y
  rw [div_le_iff₀ hlog2pos]
  nlinarith [hlogy, hlog2, hy]
/-- `w = ⌈log(N+1)⌉ ≤ log n + 2` at `N = ⌈n/d⌉` (`6toplevel.tex` line 305: `w = O(log n)`). -/
lemma w_le_lgn (P : TopParams) (hn : 2 ≤ P.n) (hd : 1 ≤ P.d) (hdn : 2 * P.d ≤ P.n) :
    (P.w : ℝ) ≤ lg (P.n : ℝ) + 2 := by
  have hle : (P.w : ℝ) ≤ lg ((P.n : ℝ) / (P.d : ℝ)) + 2 := w_le P.n P.d hd hdn
  have hdpos : (0 : ℝ) < (P.d : ℝ) := by exact_mod_cast (by omega : 0 < P.d)
  have hnpos : (0 : ℝ) < (P.n : ℝ) := by exact_mod_cast (by omega : 0 < P.n)
  have hdiv : (P.n : ℝ) / (P.d : ℝ) ≤ (P.n : ℝ) := by
    rw [div_le_iff₀ hdpos]
    have h1 : (1 : ℝ) ≤ (P.d : ℝ) := by exact_mod_cast hd
    nlinarith
  have hmono : lg ((P.n : ℝ) / (P.d : ℝ)) ≤ lg (P.n : ℝ) := lg_mono (by positivity) hdiv
  linarith
/-- **`ℓ = O(C' log² n)`** (`6toplevel.tex` line 305): `B ≤ ⌈C' log(log n + 2)⌉ ≤ 2C'(log n + 2) + 1`
and `w ≤ log n + 2`, hence `ℓ = Bw ≤ (4C' + 1)(log n + 2)²`. -/
lemma ell_le_C (P : TopParams) (hn : 2 ≤ P.n) (hd : 1 ≤ P.d) (hdn : 2 * P.d ≤ P.n) :
    (P.ell : ℝ) ≤ (4 * (P.C' : ℝ) + 1) * (lg (P.n : ℝ) + 2) ^ 2 := by
  have hlgn1 : (1 : ℝ) ≤ P.lgn := one_le_lg hn
  have hX1 : (1 : ℝ) ≤ P.lgn + 2 := by linarith
  have hC'0 : (0 : ℝ) ≤ (P.C' : ℝ) := by positivity
  have hBmin : (P.B : ℝ) ≤ ((⌈(P.C' : ℝ) * lg (P.lgn + 2)⌉₊ : ℕ) : ℝ) := by
    have h1 : P.B ≤ ⌈(P.C' : ℝ) * lg (P.lgn + 2)⌉₊ := min_le_right _ _
    exact_mod_cast h1
  have hlogarg : (0 : ℝ) ≤ (P.C' : ℝ) * lg (P.lgn + 2) :=
    mul_nonneg hC'0 (lg_nonneg (by linarith))
  have hceil : ((⌈(P.C' : ℝ) * lg (P.lgn + 2)⌉₊ : ℕ) : ℝ) <
      (P.C' : ℝ) * lg (P.lgn + 2) + 1 :=
    Nat.ceil_lt_add_one hlogarg
  have hlg2 : lg (P.lgn + 2) ≤ 2 * (P.lgn + 2) := lg_le_two_mul (by linarith)
  have hB : (P.B : ℝ) ≤ 2 * (P.C' : ℝ) * (P.lgn + 2) + 1 := by nlinarith
  have hw : (P.w : ℝ) ≤ P.lgn + 2 := w_le_lgn P hn hd hdn
  have hell : (P.ell : ℝ) = (P.B : ℝ) * (P.w : ℝ) := by
    rw [TopParams.ell]
    push_cast
    ring
  rw [hell]
  have hB0 : (0 : ℝ) ≤ (P.B : ℝ) := by positivity
  have hw0 : (0 : ℝ) ≤ (P.w : ℝ) := by positivity
  have hstep : (P.B : ℝ) * (P.w : ℝ) ≤
      (2 * (P.C' : ℝ) * (P.lgn + 2) + 1) * (P.lgn + 2) :=
    mul_le_mul hB hw hw0 (by positivity)
  have hstep2 : (2 * (P.C' : ℝ) * (P.lgn + 2) + 1) * (P.lgn + 2) =
      2 * (P.C' : ℝ) * (P.lgn + 2) ^ 2 + (P.lgn + 2) := by ring
  have hsq : (P.lgn + 2) ≤ (P.lgn + 2) ^ 2 := by nlinarith [hX1]
  have hfin : 2 * (P.C' : ℝ) * (P.lgn + 2) ^ 2 + (P.lgn + 2) ≤
      (4 * (P.C' : ℝ) + 1) * (P.lgn + 2) ^ 2 := by nlinarith [hsq, hC'0]
  calc (P.B : ℝ) * (P.w : ℝ) ≤
        (2 * (P.C' : ℝ) * (P.lgn + 2) + 1) * (P.lgn + 2) := hstep
    _ = 2 * (P.C' : ℝ) * (P.lgn + 2) ^ 2 + (P.lgn + 2) := hstep2
    _ ≤ (4 * (P.C' : ℝ) + 1) * (P.lgn + 2) ^ 2 := hfin
/-- **`resid ≤ 2η(d+1) + 1`**: the residual capacity `t = min{n, d(B+1), ⌈2η(d+1)⌉}` of
`6toplevel.tex` (31) is at most `⌈2η(d+1)⌉`, the capacity Lemma 6.4 controls. -/
lemma resid_le_two_eta (P : TopParams) (hn : 2 ≤ P.n) (hd : 1 ≤ P.d) :
    (P.resid : ℝ) ≤ 2 * P.eta * ((P.d : ℝ) + 1) + 1 := by
  have hlgn : (0 : ℝ) < P.lgn := lt_of_lt_of_le zero_lt_one (one_le_lg hn)
  have hη : (0 : ℝ) < P.eta := by
    rw [TopParams.eta]
    exact inv_pos.mpr (pow_pos hlgn P.A)
  have hx0 : (0 : ℝ) ≤ 2 * P.eta * ((P.d : ℝ) + 1) := by positivity
  have h1 : P.resid ≤ ⌈2 * P.eta * ((P.d : ℝ) + 1)⌉₊ := by
    rw [TopParams.resid]
    exact le_trans (min_le_right _ _) (min_le_right _ _)
  have h2 : ((⌈2 * P.eta * ((P.d : ℝ) + 1)⌉₊ : ℕ) : ℝ) <
      2 * P.eta * ((P.d : ℝ) + 1) + 1 := Nat.ceil_lt_add_one hx0
  have h3 : (P.resid : ℝ) ≤ ((⌈2 * P.eta * ((P.d : ℝ) + 1)⌉₊ : ℕ) : ℝ) := by
    exact_mod_cast h1
  linarith
/-- **`1 ≤ η d`**, the numeric hypothesis `cr_length_le` uses, from the row-column regime
`d > (C')³ λ_* log⁶ n / η²` (`6toplevel.tex` §6.2): `η d > (log n)^{A+6} ≥ 1`. -/
lemma one_le_eta_mul_d (P : TopParams) (hargs : P.Args) (hreg : P.RowColumnRegime)
    (hC' : 1 ≤ P.C') (hA : 1 ≤ P.A) (hn : 2 ≤ P.n) : 1 ≤ P.eta * (P.d : ℝ) := by
  have hlgn1 : (1 : ℝ) ≤ P.lgn := one_le_lg hn
  have hlamStar : (1 : ℝ) ≤ (P.lamStar : ℝ) := by
    have h1 : 1 ≤ P.lam := hargs.2.2
    have h2 : 1 ≤ P.lamStar := by unfold TopParams.lamStar; omega
    exact_mod_cast h2
  have hC'1 : (1 : ℝ) ≤ (P.C' : ℝ) := by exact_mod_cast hC'
  have hC'3 : (1 : ℝ) ≤ (P.C' : ℝ) ^ 3 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hC'1 3
    simpa using h
  have hlgn6 : (1 : ℝ) ≤ P.lgn ^ 6 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hlgn1 6
    simpa using h
  have hpow2 : (P.lgn ^ P.A) ^ 2 = P.lgn ^ (2 * P.A) := by
    rw [← pow_mul]
    congr 1
    omega
  have heta2 : P.eta ^ 2 = (P.lgn ^ (2 * P.A))⁻¹ := by
    rw [TopParams.eta, inv_pow, hpow2]
  have hone : 1 / P.eta ^ 2 = P.lgn ^ (2 * P.A) := by
    rw [heta2, one_div, inv_inv]
  have hkey : (P.C' : ℝ) ^ 3 * (P.lamStar : ℝ) * P.lgn ^ 6 / P.eta ^ 2 =
      ((P.C' : ℝ) ^ 3 * (P.lamStar : ℝ) * P.lgn ^ 6) * P.lgn ^ (2 * P.A) := by
    rw [div_eq_mul_one_div, hone]
  have hreg2 := hreg.2
  rw [hkey] at hreg2
  have hprod : (1 : ℝ) ≤ (P.C' : ℝ) ^ 3 * (P.lamStar : ℝ) * P.lgn ^ 6 := by
    have h1 : (1 : ℝ) ≤ (P.C' : ℝ) ^ 3 * (P.lamStar : ℝ) := by
      have h := mul_le_mul hC'3 hlamStar (by norm_num : (0 : ℝ) ≤ 1) (by positivity)
      simpa using h
    have h := mul_le_mul h1 hlgn6 (by norm_num : (0 : ℝ) ≤ 1) (by positivity)
    simpa using h
  have hP0 : (0 : ℝ) ≤ P.lgn ^ (2 * P.A) := by positivity
  have hmul : P.lgn ^ (2 * P.A) ≤
      ((P.C' : ℝ) ^ 3 * (P.lamStar : ℝ) * P.lgn ^ 6) * P.lgn ^ (2 * P.A) := by
    have h := mul_le_mul_of_nonneg_right hprod hP0
    simpa using h
  have hdge : P.lgn ^ (2 * P.A) ≤ (P.d : ℝ) := le_of_lt (lt_of_le_of_lt hmul hreg2)
  have hAle : P.lgn ^ P.A ≤ P.lgn ^ (2 * P.A) := pow_le_pow_right₀ hlgn1 (by omega)
  have hdiv : (1 : ℝ) ≤ (P.d : ℝ) / P.lgn ^ P.A := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  have hetaeq : P.eta * (P.d : ℝ) = (P.d : ℝ) / P.lgn ^ P.A := by
    rw [TopParams.eta, div_eq_inv_mul]
  rw [hetaeq]
  exact hdiv
/-- **Theorem 5.1 summed over the `ℓ` children** (`6toplevel.tex` line 297, second line):
`Σ_s Len_s ≤ (1 + C₁/log n) Σ_s (X_s + α h_d(Y_s)) + ℓ (C₂ d/log⁸ n) + ℓ C₃ λ log^{p₁} n`. -/
lemma sum_child_length_le {ι : Type} [Fintype ι] {α C₁ C₂ C₃ : ℝ} {p₁ n d lam : ℕ}
    (X Y : ι → ℕ) (Mf : ι → ℝ)
    (hchild : ∀ s, Mf s ≤ (1 + C₁ / lg (n : ℝ)) * ((X s : ℝ) + α * hN d (Y s))
      + C₂ * ((d : ℝ) / lg (n : ℝ) ^ 8) + C₃ * (lam : ℝ) * lg (n : ℝ) ^ p₁) :
    ∑ s, Mf s ≤ (1 + C₁ / lg (n : ℝ)) * (∑ s, ((X s : ℝ) + α * hN d (Y s)))
      + (Fintype.card ι : ℝ) *
        (C₂ * ((d : ℝ) / lg (n : ℝ) ^ 8) + C₃ * (lam : ℝ) * lg (n : ℝ) ^ p₁) := by
  have h1 : ∑ s, Mf s ≤ ∑ s, ((1 + C₁ / lg (n : ℝ)) * ((X s : ℝ) + α * hN d (Y s))
      + C₂ * ((d : ℝ) / lg (n : ℝ) ^ 8) + C₃ * (lam : ℝ) * lg (n : ℝ) ^ p₁) :=
    Finset.sum_le_sum fun s _ => hchild s
  have h2 : ∑ s, ((1 + C₁ / lg (n : ℝ)) * ((X s : ℝ) + α * hN d (Y s))
      + C₂ * ((d : ℝ) / lg (n : ℝ) ^ 8) + C₃ * (lam : ℝ) * lg (n : ℝ) ^ p₁)
      = (1 + C₁ / lg (n : ℝ)) * (∑ s, ((X s : ℝ) + α * hN d (Y s)))
        + (Fintype.card ι : ℝ) *
          (C₂ * ((d : ℝ) / lg (n : ℝ) ^ 8) + C₃ * (lam : ℝ) * lg (n : ℝ) ^ p₁) := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul, nsmul_eq_mul]
    ring
  linarith [h1, h2]
/-- **The `ZMod 2`-basis of `𝔽_{2^w}`**: `F = GaloisField 2 w` is a `w`-dimensional `ZMod 2`-vector
space (`GaloisField.finrank`), hence has a basis of size `w` — the `b` of `3construction.tex:296`,
the last piece of the data `P.IsAddress` needs. -/
noncomputable def galoisBasis (w : ℕ) (hw : 1 ≤ w) :
    Module.Basis (Fin w) (ZMod 2) (GaloisField 2 w) :=
  (Module.finBasis (ZMod 2) (GaloisField 2 w)).reindex
    (finCongr (GaloisField.finrank 2 (by omega : w ≠ 0)))
/-- **`N` distinct nonzero elements of `𝔽_{2^w}`** (`N + 1 ≤ 2^w`, i.e. `N ≤ |F*| = 2^w - 1`): the
address map `ι : [N] ↪ F*` of §3.2, whose existence is the only non-numerical hypothesis of
Lemma 6.3. -/
theorem exists_galoisAddress (N w : ℕ) (hw : 1 ≤ w) (hN : N + 1 ≤ 2 ^ w) :
    ∃ ι : ℕ → GaloisField 2 w, (∀ v < N, ι v ≠ 0) ∧ Set.InjOn ι (Set.Iio N) := by
  classical
  haveI hprime : Fact (Nat.Prime 2) := inferInstance
  haveI hfin : Fintype (GaloisField 2 w) := Fintype.ofFinite _
  have hwne : w ≠ 0 := by omega
  have hcard : Fintype.card (GaloisField 2 w) = 2 ^ w := by
    rw [← Nat.card_eq_fintype_card]
    exact GaloisField.card 2 w hwne
  have hz : Fintype.card {x : GaloisField 2 w // x = 0} = 1 := by
    have : Subsingleton {x : GaloisField 2 w // x = 0} :=
      ⟨fun a b => by ext; rw [a.2, b.2]⟩
    exact Fintype.card_ofSubsingleton ⟨0, rfl⟩
  have hsub : Fintype.card {x : GaloisField 2 w // x ≠ 0} = 2 ^ w - 1 := by
    have h1 := Fintype.card_subtype_compl (fun x : GaloisField 2 w => x = 0)
    rw [hz, hcard] at h1
    simpa using h1
  have hle : N ≤ Fintype.card {x : GaloisField 2 w // x ≠ 0} := by
    rw [hsub]
    omega
  let emb : Fin N ↪ {x : GaloisField 2 w // x ≠ 0} :=
    (Fin.castLEEmb hle).trans (Fintype.equivFin {x : GaloisField 2 w // x ≠ 0}).symm.toEmbedding
  refine ⟨fun v => if h : v < N then (emb ⟨v, h⟩).val else 0, ?_, ?_⟩
  · intro v hv
    simp only [dif_pos hv]
    exact (emb ⟨v, hv⟩).2
  · intro v hv u hu hvu
    simp only [Set.mem_Iio] at hv hu
    simp only [dif_pos hv, dif_pos hu] at hvu
    have h2 : emb ⟨v, hv⟩ = emb ⟨u, hu⟩ := Subtype.ext hvu
    have h3 : (⟨v, hv⟩ : Fin N) = ⟨u, hu⟩ := emb.injective h2
    exact congrArg Fin.val h3
/-- `w = ⌈log(N+1)⌉ ≥ 1` at `N = ⌈n/d⌉`, `d ≤ n` (`6toplevel.tex` line 305: the word width is
positive), needed to build the field `𝔽_{2^w}`. -/
lemma w_pos (P : TopParams) (hargs : P.Args) (hn : 2 ≤ P.n) : 1 ≤ P.w := by
  have hd : 1 ≤ P.d := le_trans (by norm_num) hargs.1
  have hdn : (P.d : ℝ) ≤ (P.n : ℝ) := by exact_mod_cast hargs.2.1
  have hd0 : (0 : ℝ) < (P.d : ℝ) := by exact_mod_cast (by omega : 0 < P.d)
  have hx : (1 : ℝ) ≤ (P.n : ℝ) / (P.d : ℝ) := by
    rw [le_div_iff₀ hd0]
    have h1 : (1 : ℝ) ≤ (P.d : ℝ) := by exact_mod_cast hd
    nlinarith
  have hN1 : (1 : ℝ) ≤ (P.N : ℝ) := le_trans hx (Nat.le_ceil _)
  have hlg : (1 : ℝ) ≤ lg ((P.N : ℝ) + 1) := by
    have h2 : (2 : ℝ) ≤ (P.N : ℝ) + 1 := by linarith
    have h := lg_mono (by norm_num : (0 : ℝ) < 2) h2
    rwa [lg_two] at h
  have h2 : (1 : ℝ) ≤ ((⌈lg ((P.N : ℝ) + 1)⌉₊ : ℕ) : ℝ) := le_trans hlg (Nat.le_ceil _)
  have h3 : (1 : ℝ) ≤ (P.w : ℝ) := h2
  exact_mod_cast h3
/-- `N + 1 ≤ 2^w` for `N = ⌈n/d⌉`, `w = ⌈log(N+1)⌉`: the address map of §3.2 has `N` nonzero values
in `𝔽_{2^w}` because `log(N+1) ≤ w`. -/
lemma N_succ_le_two_pow (P : TopParams) : P.N + 1 ≤ 2 ^ P.w := by
  have hlg : lg ((P.N : ℝ) + 1) ≤ (P.w : ℝ) := Nat.le_ceil _
  have hx0 : (0 : ℝ) < (P.N : ℝ) + 1 := by positivity
  have h := (Real.logb_le_iff_le_rpow (b := 2) (x := (P.N : ℝ) + 1) (y := (P.w : ℝ))
    (by norm_num) hx0).1 hlg
  rw [Real.rpow_natCast] at h
  exact_mod_cast h
/-- **The deterministic regime `d ≥ n/2`: direct storage** (`6toplevel.tex` lines 52, 285, 311).
Storing all of `x` costs `n` bits, and `n ≤ L(n,d) + 1`: `L(n,d) = log Σ_{a≤d} binom(n,a)` and
`Σ_{a≤d} binom(n,a) ≥ 2^{n-1}` when `n ≤ 2d` — by the symmetry `binom(n,a) = binom(n,n-a)`, the terms
`a > d` are re-indexed onto `a < n-d ≤ d`, so the upper half is dominated by the lower half. -/
theorem direct_storage_le (n d : ℕ) (hd : 1 ≤ d) (hdn : n ≤ 2 * d) :
    (n : ℝ) ≤ L n d + 1 := by
  set S : ℕ := ∑ a ∈ range (d + 1), n.choose a with hSdef
  by_cases hdle : d ≤ n
  · -- `d ≤ n`: reflect the tail `a > d` onto `a < n - d ≤ d`
    set T : ℕ := ∑ a ∈ Ico (d + 1) (n + 1), n.choose a with hTdef
    have hdisj : Disjoint (range (d + 1)) (Ico (d + 1) (n + 1)) := by
      rw [Finset.disjoint_left]
      intro a ha hb
      simp only [mem_range] at ha
      simp only [mem_Ico] at hb
      omega
    have hunion : range (d + 1) ∪ Ico (d + 1) (n + 1) = range (n + 1) := by
      ext a
      simp only [mem_union, mem_range, mem_Ico]
      omega
    have hsplit : 2 ^ n = S + T := by
      rw [hSdef, hTdef, ← Nat.sum_range_choose n, ← hunion, Finset.sum_union hdisj]
    have hT : T = ∑ b ∈ range (n - d), n.choose b := by
      rw [hTdef]
      refine Finset.sum_bij (fun a _ => n - a) ?_ ?_ ?_ ?_
      · intro a ha
        simp only [mem_Ico] at ha
        simp only [mem_range]
        omega
      · intro a1 ha1 a2 ha2 h
        simp only [mem_Ico] at ha1 ha2
        omega
      · intro b hb
        simp only [mem_range] at hb
        refine ⟨n - b, ?_, ?_⟩
        · simp only [mem_Ico]
          omega
        · omega
      · intro a ha
        simp only [mem_Ico] at ha
        exact (Nat.choose_symm (by omega : a ≤ n)).symm
    have hTle : T ≤ S := by
      rw [hT, hSdef]
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (fun b hb => by simp only [mem_range] at hb ⊢; omega) (fun i _ _ => Nat.zero_le _)
    have h2n : 2 ^ n ≤ 2 * S := by omega
    have hSge : 2 ^ (n - 1) ≤ S := by
      have hp : 2 ^ n = 2 * 2 ^ (n - 1) := by
        rw [mul_comm, ← Nat.pow_succ]
        congr 1
        omega
      omega
    have hL : ((n - 1 : ℕ) : ℝ) ≤ L n d := by
      have hcast : (2 : ℝ) ^ (n - 1) ≤ ((S : ℕ) : ℝ) := by
        rw [hSdef]
        exact_mod_cast hSge
      have hpos : (0 : ℝ) < (2 : ℝ) ^ (n - 1) := by positivity
      have h := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hpos hcast
      have h' : lg ((2 : ℝ) ^ (n - 1)) ≤ lg ((S : ℕ) : ℝ) := h
      rw [lg_pow (by norm_num : (2 : ℝ) ≠ 0), lg_two, mul_one] at h'
      exact h'
    have hn1 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ n)]
      norm_num
    linarith
  · -- `n < d`: every binomial coefficient is counted
    have hdlt : n < d := by omega
    have hsub : range (n + 1) ⊆ range (d + 1) := by
      intro a ha
      simp only [mem_range] at ha ⊢
      omega
    have hSge : 2 ^ n ≤ S := by
      rw [hSdef, ← Nat.sum_range_choose n]
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => Nat.zero_le _)
    have hL : (n : ℝ) ≤ L n d := by
      have hcast : (2 : ℝ) ^ n ≤ ((S : ℕ) : ℝ) := by
        rw [hSdef]
        exact_mod_cast hSge
      have hpos : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
      have h := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hpos hcast
      have h' : lg ((2 : ℝ) ^ n) ≤ lg ((S : ℕ) : ℝ) := h
      rw [lg_pow (by norm_num : (2 : ℝ) ≠ 0), lg_two, mul_one] at h'
      exact h'
    linarith

/-! ## 8. The small-instance regime: `d ≤ (C')³ λ_* log⁶ n / η²`

`6toplevel.tex` lines 311–317:

> For `d ≥ n/2`, direct storage uses `n ≤ L(n,d)+1` bits, while the small-instance mode uses
> `O((C')³λ_*log^{2A+8}n) ≤ O((C')⁴λlog^{2A+9}n) = λlog^{O(1)}n` bits, using `λ_* = O(C'λlog n)`.

The small-instance mode is `CR_{n,d}` alone (`6toplevel.tex` line 53: "The cases of `d ≥ n/2` and
`d ≤ (C')³λ_*log⁶n/η²` are deterministic and error-free"), so Proposition 2.3 at `(N,t) := (n,d)`
stores `M ≤ KCR · d · log²(n+2)` bits.  With `d ≤ (C')³λ_*log⁶n/η²` and `η = log^{-A}n`, i.e.
`η^{-2} = log^{2A}n`, this is `M ≤ KCR (C')³ λ_* log^{2A+8} n`, and `λ_* ≤ 8C'λlog n` gives
`M ≤ 72 KCR (C')⁴ λ log^{2A+9} n` — the paper's `O((C')³λ_*log^{2A+8}n) ≤ O((C')⁴λlog^{2A+9}n)`,
with the exponents `2A+8` and `2A+9` exactly as printed. -/
/-- `log(n+2) ≤ 3 log n` for `n ≥ 2`: `n + 2 ≤ 4n` and `log 4 = 2 ≤ 2 log n`. -/
lemma lg_add_two_le_three {n : ℕ} (hn : 2 ≤ n) :
    lg ((n : ℝ) + 2) ≤ 3 * lg (n : ℝ) := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have h2n : (n : ℝ) + 2 ≤ 4 * (n : ℝ) := by linarith
  have hle : lg ((n : ℝ) + 2) ≤ lg (4 * (n : ℝ)) := lg_mono (by linarith) h2n
  have h4aux : lg (4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, lg_pow (by norm_num) 2, lg_two]
    norm_num
  have h4 : lg (4 * (n : ℝ)) = 2 + lg (n : ℝ) := by
    rw [lg_mul (by norm_num) (ne_of_gt hnpos), h4aux]
  have hx1 : (1 : ℝ) ≤ lg (n : ℝ) := one_le_lg hn
  linarith
/-- `log log(n+2) ≤ 3 log n`: `log(n+2) ≤ 2log n` because `n + 2 ≤ n²`, and
`log(2log n) = 1 + log log n ≤ 1 + 2log n ≤ 3log n` by `lg_le_two_mul`. -/
lemma lg_lg_add_two_le_three {n : ℕ} (hn : 2 ≤ n) :
    lg (lg ((n : ℝ) + 2)) ≤ 3 * lg (n : ℝ) := by
  have hx1 : (1 : ℝ) ≤ lg (n : ℝ) := one_le_lg hn
  have hx0 : (0 : ℝ) < lg (n : ℝ) := lt_of_lt_of_le zero_lt_one hx1
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hpos2 : (0 : ℝ) < lg ((n : ℝ) + 2) := by
    have h := one_le_lg (n := n + 2) (by omega)
    push_cast at h
    linarith
  have h2 : lg ((n : ℝ) + 2) ≤ 2 * lg (n : ℝ) := by
    have hn2 : (n : ℝ) + 2 ≤ (n : ℝ) ^ 2 := by
      have h2n : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      nlinarith
    calc lg ((n : ℝ) + 2) ≤ lg ((n : ℝ) ^ 2) := lg_mono (by linarith) hn2
      _ = 2 * lg (n : ℝ) := lg_pow (ne_of_gt hnpos) 2
  calc lg (lg ((n : ℝ) + 2)) ≤ lg (2 * lg (n : ℝ)) := lg_mono hpos2 h2
    _ = lg 2 + lg (lg (n : ℝ)) := lg_mul (by norm_num) (ne_of_gt hx0)
    _ = 1 + lg (lg (n : ℝ)) := by rw [lg_two]
    _ ≤ 1 + 2 * lg (n : ℝ) := by
        have h := lg_le_two_mul hx1
        linarith
    _ ≤ 3 * lg (n : ℝ) := by linarith
/-- `⌈log log(n+2)⌉ ≤ 4 log n`, the form in which `λ_*` is bounded below. -/
lemma ceil_lg_lg_add_two_le {n : ℕ} (hn : 2 ≤ n) :
    ((⌈lg (lg ((n : ℝ) + 2))⌉₊ : ℝ)) ≤ 4 * lg (n : ℝ) := by
  have h3 := lg_lg_add_two_le_three hn
  have hx1 : (1 : ℝ) ≤ lg (n : ℝ) := one_le_lg hn
  have h0 : (0 : ℝ) ≤ lg (lg ((n : ℝ) + 2)) := by
    have h := one_le_lg (n := n + 2) (by omega)
    push_cast at h
    exact lg_nonneg h
  have hlt := Nat.ceil_lt_add_one h0
  linarith
/-- **`λ_* = O(C'λlog n)`** (`6toplevel.tex` line 317): `λ_* = λ + C'⌈log log(n+2)⌉ + C'` is at
most `8C'λlog n` for `λ ≥ 1`, `C' ≥ 1` and `n ≥ 2`. -/
lemma lamStar_le (P : TopParams) (hC' : 1 ≤ P.C') (hlam : 1 ≤ P.lam) (hn : 2 ≤ P.n) :
    (P.lamStar : ℝ) ≤ 8 * (P.C' : ℝ) * (P.lam : ℝ) * P.lgn := by
  have hx1 : (1 : ℝ) ≤ P.lgn := one_le_lg hn
  have hx0 : (0 : ℝ) < P.lgn := lt_of_lt_of_le zero_lt_one hx1
  have hC'1 : (1 : ℝ) ≤ (P.C' : ℝ) := by exact_mod_cast hC'
  have hlam1 : (1 : ℝ) ≤ (P.lam : ℝ) := by exact_mod_cast hlam
  have hceil : ((⌈lg (lg ((P.n : ℝ) + 2))⌉₊ : ℝ)) ≤ 4 * P.lgn := ceil_lg_lg_add_two_le hn
  have hunf : (P.lamStar : ℝ) =
      (P.lam : ℝ) + (P.C' : ℝ) * ((⌈lg (lg ((P.n : ℝ) + 2))⌉₊ : ℝ)) + (P.C' : ℝ) := by
    simp [TopParams.lamStar]
  -- each of the three summands is at most `C'λlog n`
  have hCl : (1 : ℝ) ≤ (P.C' : ℝ) * P.lgn := by
    have h := mul_le_mul hC'1 hx1 (by norm_num : (0 : ℝ) ≤ 1) (by positivity)
    simpa using h
  have hll : (1 : ℝ) ≤ (P.lam : ℝ) * P.lgn := by
    have h := mul_le_mul hlam1 hx1 (by norm_num : (0 : ℝ) ≤ 1) (by positivity)
    simpa using h
  have h1 : (P.lam : ℝ) ≤ (P.C' : ℝ) * (P.lam : ℝ) * P.lgn := by
    calc (P.lam : ℝ) = 1 * (P.lam : ℝ) := by ring
      _ ≤ ((P.C' : ℝ) * P.lgn) * (P.lam : ℝ) :=
          mul_le_mul_of_nonneg_right hCl (le_trans zero_le_one hlam1)
      _ = (P.C' : ℝ) * (P.lam : ℝ) * P.lgn := by ring
  have h2 : (P.C' : ℝ) * ((⌈lg (lg ((P.n : ℝ) + 2))⌉₊ : ℝ)) ≤
      4 * ((P.C' : ℝ) * (P.lam : ℝ) * P.lgn) := by
    calc (P.C' : ℝ) * ((⌈lg (lg ((P.n : ℝ) + 2))⌉₊ : ℝ))
        ≤ (P.C' : ℝ) * (4 * P.lgn) := mul_le_mul_of_nonneg_left hceil (by positivity)
      _ = 4 * ((P.C' : ℝ) * P.lgn) := by ring
      _ ≤ 4 * ((P.C' : ℝ) * (P.lam : ℝ) * P.lgn) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          calc (P.C' : ℝ) * P.lgn = (P.C' : ℝ) * 1 * P.lgn := by ring
            _ ≤ (P.C' : ℝ) * (P.lam : ℝ) * P.lgn := by
                apply mul_le_mul_of_nonneg_right _ (le_trans zero_le_one hx1)
                exact mul_le_mul_of_nonneg_left hlam1 (by positivity)
  have h3 : (P.C' : ℝ) ≤ (P.C' : ℝ) * (P.lam : ℝ) * P.lgn := by
    calc (P.C' : ℝ) = (P.C' : ℝ) * 1 := by ring
      _ ≤ (P.C' : ℝ) * ((P.lam : ℝ) * P.lgn) :=
          mul_le_mul_of_nonneg_left hll (by positivity)
      _ = (P.C' : ℝ) * (P.lam : ℝ) * P.lgn := by ring
  have hA0 : (0 : ℝ) ≤ (P.C' : ℝ) * (P.lam : ℝ) * P.lgn :=
    mul_nonneg (mul_nonneg (by positivity) (by positivity)) (le_of_lt hx0)
  linarith
/-- `η^{-2} = log^{2A}n`. -/
lemma eta_sq_inv (P : TopParams) : (P.eta ^ 2)⁻¹ = P.lgn ^ (2 * P.A) := by
  have hpow2 : (P.lgn ^ P.A) ^ 2 = P.lgn ^ (2 * P.A) := by
    rw [← pow_mul]
    congr 1
    omega
  simp only [TopParams.eta, inv_pow, hpow2, inv_inv]
/-- **The small-instance arithmetic**, as in the paper (`6toplevel.tex` lines 311–317):

> For `d ≥ n/2`, direct storage uses `n ≤ L(n,d)+1` bits, while the small-instance mode uses
> `O((C')³λ_*log^{2A+8}n) ≤ O((C')⁴λlog^{2A+9}n) = λlog^{O(1)}n` bits, using `λ_* = O(C'λlog n)`.

With `M ≤ KCR · d · log²(n+2)` from Proposition 2.3 at `(N,t) := (n,d)` and
`d ≤ (C')³λ_*log⁶n/η²`, `η^{-2} = log^{2A}n`, the stored size is `M ≤ 72 KCR (C')⁴ λ log^{2A+9} n`.
The constant factors are explicit: `9` from `log²(n+2) ≤ 9log²n`, `8` from `λ_* ≤ 8C'λlog n`. -/
lemma small_instance_bound (A C' : ℕ) (hC' : 1 ≤ C') (KCR : ℝ) (hKCR : 0 ≤ KCR)
    (n d lam M : ℕ) :
    let P : TopParams := ⟨A, C', n, d, lam⟩
    P.Args →
    (d : ℝ) ≤ (C' : ℝ) ^ 3 * (P.lamStar : ℝ) * P.lgn ^ 6 / P.eta ^ 2 →
    (M : ℝ) ≤ KCR * ((d : ℝ) * lg ((n : ℝ) + 2) ^ 2) →
    (M : ℝ) ≤ 72 * KCR * (C' : ℝ) ^ 4 * (lam : ℝ) * P.lgn ^ (2 * A + 9) := by
  intro P hargs hsmall hrow
  have hAeq : P.A = A := rfl
  have hn : 2 ≤ n := le_trans hargs.1 hargs.2.1
  have hx1 : (1 : ℝ) ≤ P.lgn := one_le_lg hn
  have hx0 : (0 : ℝ) < P.lgn := lt_of_lt_of_le zero_lt_one hx1
  have hd0 : (0 : ℝ) ≤ (d : ℝ) := by positivity
  have hK9 : (0 : ℝ) ≤ 9 * KCR := by positivity
  have hC'3 : (0 : ℝ) ≤ (C' : ℝ) ^ 3 := by positivity
  -- the small-instance hypothesis, with `η^{-2} = log^{2A}n`
  have hsmall' : (d : ℝ) ≤ (C' : ℝ) ^ 3 * (P.lamStar : ℝ) * P.lgn ^ (2 * A + 6) := by
    have hone : (P.eta ^ 2)⁻¹ = P.lgn ^ (2 * A) := by
      have h := eta_sq_inv P
      rw [hAeq] at h
      exact h
    have hkey : (C' : ℝ) ^ 3 * (P.lamStar : ℝ) * P.lgn ^ 6 / P.eta ^ 2 =
        ((C' : ℝ) ^ 3 * (P.lamStar : ℝ) * P.lgn ^ 6) * P.lgn ^ (2 * A) := by
      rw [div_eq_mul_inv, hone]
    have heq : ((C' : ℝ) ^ 3 * (P.lamStar : ℝ) * P.lgn ^ 6) * P.lgn ^ (2 * A) =
        (C' : ℝ) ^ 3 * (P.lamStar : ℝ) * P.lgn ^ (2 * A + 6) := by
      rw [show 2 * A + 6 = 6 + 2 * A by omega, pow_add]
      ring
    rw [hkey, heq] at hsmall
    exact hsmall
  -- `log²(n+2) ≤ 9log²n`
  have hlg2 : lg ((n : ℝ) + 2) ^ 2 ≤ 9 * P.lgn ^ 2 := by
    have h3 := lg_add_two_le_three hn
    have h0 : (0 : ℝ) ≤ lg ((n : ℝ) + 2) := by
      apply lg_nonneg
      have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
      linarith
    calc lg ((n : ℝ) + 2) ^ 2 ≤ (3 * P.lgn) ^ 2 := pow_le_pow_left₀ h0 h3 2
      _ = 9 * P.lgn ^ 2 := by ring
  -- `M ≤ 9 KCR d log²n`
  have hrow9 : (M : ℝ) ≤ 9 * KCR * ((d : ℝ) * P.lgn ^ 2) := by
    have h1 : KCR * ((d : ℝ) * lg ((n : ℝ) + 2) ^ 2) ≤
        KCR * ((d : ℝ) * (9 * P.lgn ^ 2)) := by
      apply mul_le_mul_of_nonneg_left _ hKCR
      exact mul_le_mul_of_nonneg_left hlg2 hd0
    nlinarith [hrow, h1]
  -- `λ_* ≤ 8C'λlog n`
  have hstar : (P.lamStar : ℝ) ≤ 8 * (C' : ℝ) * (lam : ℝ) * P.lgn :=
    lamStar_le P hC' hargs.2.2 hn
  -- multiply by `log²n`, then insert `λ_* ≤ 8C'λlog n`
  have hstep1 : (d : ℝ) * P.lgn ^ 2 ≤
      (C' : ℝ) ^ 3 * (P.lamStar : ℝ) * P.lgn ^ (2 * A + 8) := by
    calc (d : ℝ) * P.lgn ^ 2
        ≤ ((C' : ℝ) ^ 3 * (P.lamStar : ℝ) * P.lgn ^ (2 * A + 6)) * P.lgn ^ 2 :=
          mul_le_mul_of_nonneg_right hsmall' (pow_nonneg (le_of_lt hx0) 2)
      _ = (C' : ℝ) ^ 3 * (P.lamStar : ℝ) * P.lgn ^ (2 * A + 8) := by
          rw [show 2 * A + 8 = 2 * A + 6 + 2 by omega, pow_add]
          ring
  have hstep2 : (C' : ℝ) ^ 3 * (P.lamStar : ℝ) * P.lgn ^ (2 * A + 8) ≤
      (C' : ℝ) ^ 3 * (8 * (C' : ℝ) * (lam : ℝ) * P.lgn) * P.lgn ^ (2 * A + 8) := by
    calc (C' : ℝ) ^ 3 * (P.lamStar : ℝ) * P.lgn ^ (2 * A + 8)
        = (C' : ℝ) ^ 3 * ((P.lamStar : ℝ) * P.lgn ^ (2 * A + 8)) := by ring
      _ ≤ (C' : ℝ) ^ 3 * ((8 * (C' : ℝ) * (lam : ℝ) * P.lgn) * P.lgn ^ (2 * A + 8)) := by
          apply mul_le_mul_of_nonneg_left _ hC'3
          exact mul_le_mul_of_nonneg_right hstar (pow_nonneg (le_of_lt hx0) _)
      _ = (C' : ℝ) ^ 3 * (8 * (C' : ℝ) * (lam : ℝ) * P.lgn) * P.lgn ^ (2 * A + 8) := by
          ring
  calc (M : ℝ) ≤ 9 * KCR * ((d : ℝ) * P.lgn ^ 2) := hrow9
    _ ≤ 9 * KCR * ((C' : ℝ) ^ 3 * (P.lamStar : ℝ) * P.lgn ^ (2 * A + 8)) := by
        apply mul_le_mul_of_nonneg_left _ hK9
        exact hstep1
    _ ≤ 9 * KCR * ((C' : ℝ) ^ 3 * (8 * (C' : ℝ) * (lam : ℝ) * P.lgn) *
          P.lgn ^ (2 * A + 8)) := by
        apply mul_le_mul_of_nonneg_left _ hK9
        exact hstep2
    _ = 72 * KCR * (C' : ℝ) ^ 4 * (lam : ℝ) * P.lgn ^ (2 * A + 9) := by
        rw [show 2 * A + 9 = 2 * A + 8 + 1 by omega, pow_succ]
        ring
/-- **The small-instance regime of Theorem 6.5** (`6toplevel.tex` lines 53, 285, 311–317): if
`d ≤ (C')³λ_*log⁶n/η²` then the size `M` of the sketch is at most `C₁ λ log^{C₂} n` with
`C₁ = ⌈72 KCR (C')⁴⌉ + 1` and `C₂ = 2A + 9`, where `KCR` is the constant of Proposition 2.3's row
bound `M ≤ KCR · d · log²(n+2)`.  (The hypothesis `A ≥ 10` is carried for uniformity with the
row–column regime; the small-instance arithmetic itself needs no lower bound on `A`.) -/
theorem small_instance_le (A : ℕ) (hA : 10 ≤ A) (C' : ℕ) (hC' : 1 ≤ C')
    (KCR : ℝ) (hKCR : 0 ≤ KCR) :
    ∃ C₁ C₂ : ℕ, C₂ = 2 * A + 9 ∧
      ∀ (n d lam M : ℕ),
        let P : TopParams := ⟨A, C', n, d, lam⟩
        P.Args →
        (d : ℝ) ≤ (C' : ℝ) ^ 3 * (P.lamStar : ℝ) * P.lgn ^ 6 / P.eta ^ 2 →
        (M : ℝ) ≤ KCR * ((d : ℝ) * lg ((n : ℝ) + 2) ^ 2) →
        (M : ℝ) ≤ (C₁ : ℝ) * (lam : ℝ) * P.lgn ^ C₂ := by
  refine ⟨⌈72 * KCR * (C' : ℝ) ^ 4⌉₊ + 1, 2 * A + 9, rfl, ?_⟩
  intro n d lam M P hargs hsmall hrow
  have hn : 2 ≤ n := le_trans hargs.1 hargs.2.1
  have hx0 : (0 : ℝ) < P.lgn := lt_of_lt_of_le zero_lt_one (one_le_lg hn)
  have hb := small_instance_bound A C' hC' KCR hKCR n d lam M hargs hsmall hrow
  have hceil : 72 * KCR * (C' : ℝ) ^ 4 ≤ ((⌈72 * KCR * (C' : ℝ) ^ 4⌉₊ + 1 : ℕ) : ℝ) := by
    have h := Nat.le_ceil (72 * KCR * (C' : ℝ) ^ 4)
    push_cast
    linarith
  have hmono : 72 * KCR * (C' : ℝ) ^ 4 * (lam : ℝ) * P.lgn ^ (2 * A + 9) ≤
      ((⌈72 * KCR * (C' : ℝ) ^ 4⌉₊ + 1 : ℕ) : ℝ) * (lam : ℝ) * P.lgn ^ (2 * A + 9) := by
    apply mul_le_mul_of_nonneg_right _ (pow_nonneg (le_of_lt hx0) _)
    exact mul_le_mul_of_nonneg_right hceil (by positivity)
  linarith [hb, hmono]
/-- `ZMod 2` has only the values `0` and `1`. -/
lemma comp_zmod2_eq_zero_or_one {a : ZMod 2} : a = 0 ∨ a = 1 := by
  have hlt : ZMod.val a < 2 := ZMod.val_lt a
  have hcast : ((ZMod.val a : ℕ) : ZMod 2) = a := ZMod.natCast_zmod_val a
  have h : ZMod.val a = 0 ∨ ZMod.val a = 1 := by omega
  rcases h with h | h
  · left
    rw [← hcast, h]
    simp
  · right
    rw [← hcast, h]
    simp
/-- The value of a `ZMod 2` element is the indicator of `= 1`. -/
lemma comp_zmod2_val_eq_ite (a : ZMod 2) : a.val = if a = 1 then 1 else 0 := by
  rcases comp_zmod2_eq_zero_or_one (a := a) with h | h
  · rw [h, if_neg zero_ne_one]
    exact ZMod.val_zero
  · rw [h, if_pos rfl]
    exact ZMod.val_one 2
lemma comp_card_filter_one_eq_sum_val {N : ℕ} (v : Fin N → ZMod 2) :
    (univ.filter fun k => v k = 1).card = ∑ k, (v k).val := by
  rw [Finset.card_filter]
  exact Finset.sum_congr rfl (fun k _ => (comp_zmod2_val_eq_ite (v k)).symm)
/-- `⌈log₂ m⌉ ≤ log₂ m + 1` for `m ≥ 2`. -/
lemma comp_clog_two_le_lg_add_one {m : ℕ} (hm : 2 ≤ m) :
    (Nat.clog 2 m : ℝ) ≤ lg (m : ℝ) + 1 := by
  have hb : 1 < 2 := by norm_num
  have hk : 0 < Nat.clog 2 m := Nat.clog_pos hb (by omega)
  have h1 : 2 ^ (Nat.clog 2 m).pred < m := Nat.pow_pred_clog_lt_self hb (by omega)
  have hcast : ((2 ^ (Nat.clog 2 m).pred : ℕ) : ℝ) = (2 : ℝ) ^ (Nat.clog 2 m).pred := by
    push_cast
    ring
  have h2 : (2 : ℝ) ^ (Nat.clog 2 m).pred < (m : ℝ) := by
    rw [← hcast]
    exact_mod_cast h1
  have h3 : lg ((2 : ℝ) ^ (Nat.clog 2 m).pred) < lg (m : ℝ) :=
    Real.logb_lt_logb (by norm_num) (by positivity) h2
  have h3' : ((Nat.clog 2 m).pred : ℝ) < lg (m : ℝ) := by
    have h := h3
    rw [lg, Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one] at h
    exact h
  have h4 : ((Nat.clog 2 m).pred : ℝ) = (Nat.clog 2 m : ℝ) - 1 := by
    rw [Nat.pred_eq_sub_one, Nat.cast_sub hk, Nat.cast_one]
  rw [h4] at h3'
  linarith
/-- `M ≤ W·T` from `wordsOf W M ≤ T`: `wordsOf` halves the `W`-bit words of the packing
(`Def…WordRAM.wordsOf`), so the number of stored bits is at most `W` per word. -/
lemma comp_le_mul_of_wordsOf_le {W M T : ℕ} (hW : 0 < W) (h : wordsOf W M ≤ T) :
    M ≤ W * T := by
  have h1 : M + W - 1 ≤ W * T + (W - 1) := (Nat.div_le_iff_le_mul_add_pred hW).1 h
  omega
/-- `⌈lg m⌉ ≤ ⌈log₂ m⌉` for `m ≥ 1`, hence `P.w = ⌈log(N+1)⌉ ≤ ⌈log₂ n⌉`. -/
lemma comp_ceil_lg_le_clog {m : ℕ} (hm : 1 ≤ m) : ⌈lg (m : ℝ)⌉₊ ≤ Nat.clog 2 m := by
  refine Nat.ceil_le.mpr ?_
  have h2 : m ≤ 2 ^ Nat.clog 2 m := Nat.le_pow_clog (by norm_num) m
  have h3 : (m : ℝ) ≤ (2 : ℝ) ^ Nat.clog 2 m := by
    have h4 : ((2 ^ Nat.clog 2 m : ℕ) : ℝ) = (2 : ℝ) ^ Nat.clog 2 m := by
      push_cast
      ring
    rw [← h4]
    exact_mod_cast h2
  have h5 : lg (m : ℝ) ≤ lg ((2 : ℝ) ^ Nat.clog 2 m) :=
    lg_mono (by exact_mod_cast hm) h3
  rw [lg_pow (by norm_num), lg_two, mul_one] at h5
  exact h5
/-- `N + 1 ≤ n` in the row-column regime: `N = ⌈n/d⌉ ≤ n/2 + 1` because `d ≥ 2`, and `n ≥ 5`
because `d < n/2`. -/
lemma comp_N_succ_le {P : TopParams} (hd : 2 ≤ P.d) (hreg : (P.d : ℝ) < (P.n : ℝ) / 2) :
    P.N + 1 ≤ P.n := by
  have hpos : (0 : ℝ) < (P.n : ℝ) := by
    have h0 : (0 : ℝ) < (P.d : ℝ) := by exact_mod_cast (by omega : 0 < P.d)
    linarith
  have hd0 : (0 : ℝ) < (P.d : ℝ) := by exact_mod_cast (by omega : 0 < P.d)
  have hNlt : (P.N : ℝ) < (P.n : ℝ) / (P.d : ℝ) + 1 := by
    rw [TopParams.N]
    exact Nat.ceil_lt_add_one (le_of_lt (by positivity))
  have hd2 : (2 : ℝ) ≤ (P.d : ℝ) := by exact_mod_cast hd
  have h2 : (P.n : ℝ) / (P.d : ℝ) ≤ (P.n : ℝ) / 2 :=
    div_le_div_of_nonneg_left (le_of_lt hpos) (by norm_num) hd2
  have hn4 : (4 : ℝ) ≤ (P.n : ℝ) := by linarith
  have h4 : (P.N : ℝ) + 1 < (P.n : ℝ) := by linarith
  have h5 : P.N + 1 < P.n := by exact_mod_cast h4
  omega

/-! ### 10.2 The top-level column `C_{a,k}(x) = ((W_{j,a})_k)_{j=1}^d` -/

section CompColumn

variable {F : Type} [Field F] [Algebra (ZMod 2) F]
/-- `W_{j,a} = α_{j,a} P_{2a-1}(S_j) = α_{j,a} ∑_{v ∈ S_j} ι(v)^{2a-1}` (`3construction.tex:288-292`),
the word of row `j` at word position `a`.  The row support `S_j` of `x` is written as the sum over
the coordinates of row `j`: coordinate `i` belongs to row `π(i) mod d` at row-local position
`π(i) / d`, and `ι` is injective on `[N]`, so `π(i)/d` runs over `S_j` exactly once. -/
noncomputable def compWord (n d : ℕ) (ι : ℕ → F) (π : Equiv.Perm (Fin n)) (a : ℕ)
    (x : Fin n → ZMod 2) (j : Fin d) : F :=
  ∑ i : Fin n, if (π i).val % d = j.val then x i • (ι ((π i).val / d) ^ (2 * a + 1)) else 0
/-- The word of a row is additive in `x`: `P_{2a-1}(S △ S') = P_{2a-1}(S) + P_{2a-1}(S')` in
characteristic two. -/
lemma compWord_add (n d : ℕ) (ι : ℕ → F) (π : Equiv.Perm (Fin n)) (a : ℕ)
    (x y : Fin n → ZMod 2) (j : Fin d) :
    compWord n d ι π a (x + y) j = compWord n d ι π a x j + compWord n d ι π a y j := by
  rw [compWord, compWord, compWord, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : (π i).val % d = j.val
  · simp only [h, if_true, Pi.add_apply, add_smul]
  · simp only [h, if_false, Pi.add_apply, add_zero]
/-- The zero vector has no word. -/
lemma compWord_zero (n d : ℕ) (ι : ℕ → F) (π : Equiv.Perm (Fin n)) (a : ℕ) (j : Fin d) :
    compWord n d ι π a (0 : Fin n → ZMod 2) j = 0 := by
  rw [compWord]
  refine Finset.sum_eq_zero fun i _ => ?_
  by_cases h : (π i).val % d = j.val <;> simp [h]
/-- The top-level column `C_{a,k}(x) = ((W_{j,a})_k)_{j=1}^d ∈ F_2^d` of `3construction.tex:296`:
bit `k` of the word of row `j`.  It is `ZMod 2`-linear in `x` because each `W_{j,a}` is. -/
noncomputable def compCol (n d w : ℕ) (b : Module.Basis (Fin w) (ZMod 2) F) (ι : ℕ → F)
    (π : Equiv.Perm (Fin n)) (α : Fin d → F) (a : ℕ) (k : Fin w) :
    (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin d → ZMod 2) where
  toFun x := fun j => b.repr (α j * compWord n d ι π a x j) k
  map_add' x y := by
    funext j
    rw [compWord_add, mul_add, map_add]
    simp
  map_smul' c x := by
    funext j
    rcases comp_zmod2_eq_zero_or_one (a := c) with h | h
    · rw [h, zero_smul, compWord_zero, mul_zero, map_zero]
      simp
    · rw [h]
      simp
/-- `compCol` evaluated: bit `k` of row `j`'s word. -/
@[simp] lemma compCol_apply (n d w : ℕ) (b : Module.Basis (Fin w) (ZMod 2) F) (ι : ℕ → F)
    (π : Equiv.Perm (Fin n)) (α : Fin d → F) (a : ℕ) (k : Fin w) (x : Fin n → ZMod 2)
    (j : Fin d) : compCol n d w b ι π α a k x j = b.repr (α j * compWord n d ι π a x j) k := rfl
/-- On the `i`-th coordinate the column is supported on the single row `π(i) mod d`: every other
row's word is `0`.  This is what makes a toggle touch one coordinate per child. -/
lemma compCol_single_eq_zero (n d w : ℕ) (b : Module.Basis (Fin w) (ZMod 2) F) (ι : ℕ → F)
    (π : Equiv.Perm (Fin n)) (α : Fin d → F) (a : ℕ) (k : Fin w) {i : Fin n} {j : Fin d}
    (h : (π i).val % d ≠ j.val) :
    compCol n d w b ι π α a k (Pi.single i 1) j = 0 := by
  have hsum : compWord n d ι π a (Pi.single i 1) j = 0 := by
    rw [compWord]
    refine Finset.sum_eq_zero fun i' _ => ?_
    by_cases hi : i' = i
    · subst hi
      simp [h]
    · simp [Pi.single_eq_of_ne hi]
  rw [compCol_apply, hsum, mul_zero, map_zero]
  simp
/-- A vector that vanishes off a single coordinate is a multiple of that basis vector. -/
lemma comp_eq_smul_single_of_eq_zero {d : ℕ} {y : Fin d → ZMod 2} {j0 : Fin d}
    (h : ∀ j, j ≠ j0 → y j = 0) : y = y j0 • Pi.single j0 1 := by
  funext j
  by_cases hj : j = j0
  · subst hj
    simp
  · rw [h j hj]
    simp [Pi.single_eq_of_ne hj, hj]
/-- Multiplying a `ZMod 2` vector by a scalar does not increase its weight. -/
lemma comp_sum_val_smul_le {N : ℕ} (c : ZMod 2) (y : Fin N → ZMod 2) :
    (∑ k, ((c • y) k).val) ≤ ∑ k, (y k).val := by
  rcases comp_zmod2_eq_zero_or_one (a := c) with h | h
  · rw [h, zero_smul]
    simp
  · rw [h, one_smul]

end CompColumn

/-! ### 10.3 Assembling the `ℓ` child blocks and the `CR` block into `Fin M`

The blocks are laid out in the **explicit prefix-sum order** of the child index (block `0` first) and
each block is **padded to a whole number of `W`-bit words**:

> block `s` owns the words `[Σ_{t<s} ⌈f t / W⌉, Σ_{t≤s} ⌈f t / W⌉)` and the bits
> `[W·Σ_{t<s} ⌈f t / W⌉, W·Σ_{t≤s} ⌈f t / W⌉)`; padding bits read `0`.

This replaces the earlier `Fintype.equivFin` order (`compSigEquivS`), under which "which word a block
occupies" could not even be stated.  Alignment is what makes a child's payload stitchable: a child
program packs its own `M_s` bits from word `0` (`packMem_blk`, §11.3), which is the composite's word
`β + a` only if the block starts at a multiple of `W`.  The price is `Δ = M' − Σ_s M_s ≤ ℓ (W−1)`,
paid in `composite_sketch` (§10.5). -/
/-- `blkOff W f s = Σ_{t<s} ⌈f t / W⌉`: the word at which block `s` starts.  For `s ≥ L` it is the
whole total `blkTotal W f` (junk, never used). -/
def blkOff {L : ℕ} (W : ℕ) (f : Fin L → ℕ) (s : ℕ) : ℕ :=
  ∑ t : Fin L, if t.val < s then wordsOf W (f t) else 0
/-- `blkTotal W f = Σ_{t<L} ⌈f t / W⌉`: the number of words all the children's blocks occupy. -/
def blkTotal {L : ℕ} (W : ℕ) (f : Fin L → ℕ) : ℕ :=
  ∑ t : Fin L, wordsOf W (f t)
lemma blkOff_zero {L W : ℕ} (f : Fin L → ℕ) : blkOff W f 0 = 0 := by
  simp [blkOff]
lemma blkOff_total {L W : ℕ} (f : Fin L → ℕ) {s : ℕ} (h : L ≤ s) :
    blkOff W f s = blkTotal W f := by
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [if_pos (by have := t.isLt; omega)]
lemma blkOff_succ {L W : ℕ} (f : Fin L → ℕ) (s : Fin L) :
    blkOff W f (s.val + 1) = blkOff W f s.val + wordsOf W (f s) := by
  have h1 : ∀ t : Fin L, (if t.val < s.val + 1 then wordsOf W (f t) else 0)
      = (if t.val < s.val then wordsOf W (f t) else 0) +
        (if t = s then wordsOf W (f t) else 0) := by
    intro t
    rcases lt_trichotomy t.val s.val with h | h | h
    · rw [if_pos (by omega), if_pos h,
        if_neg (by intro he; rw [he] at h; exact absurd h (by simp)), add_zero]
    · have ht : t = s := Fin.ext h
      rw [if_pos (by omega), if_neg (by omega), if_pos ht, zero_add]
    · rw [if_neg (by omega), if_neg (by omega),
        if_neg (by intro he; rw [he] at h; exact absurd h (by simp)), add_zero]
  have h2 : (∑ t : Fin L, (if t = s then wordsOf W (f t) else 0)) = wordsOf W (f s) := by
    rw [Finset.sum_eq_single s]
    · rw [if_pos rfl]
    · intro b _ hb; rw [if_neg hb]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [blkOff, Finset.sum_congr rfl (fun t _ => h1 t), Finset.sum_add_distrib, h2]
  rfl
lemma blkOff_mono {L W : ℕ} (f : Fin L → ℕ) {s s' : ℕ} (h : s ≤ s') :
    blkOff W f s ≤ blkOff W f s' := by
  refine Finset.sum_le_sum fun t _ => ?_
  by_cases h1 : t.val < s
  · rw [if_pos h1, if_pos (by omega)]
  · by_cases h2 : t.val < s'
    · rw [if_neg h1, if_pos h2]; exact Nat.zero_le _
    · rw [if_neg h1, if_neg h2]
/-- `m ≤ W · ⌈m / W⌉`: the padding only ever adds bits. -/
lemma le_mul_wordsOf (W : ℕ) (hW : 0 < W) (m : ℕ) : m ≤ W * wordsOf W m := by
  have h := Nat.div_add_mod (m + W - 1) W
  have hmod : (m + W - 1) % W ≤ W - 1 := by
    have := Nat.mod_lt (m + W - 1) hW
    omega
  unfold wordsOf
  omega
/-- `W · ⌈m / W⌉ ≤ m + (W − 1)`: padding a block costs at most one word. -/
lemma mul_wordsOf_le (W : ℕ) (m : ℕ) : W * wordsOf W m ≤ m + (W - 1) := by
  unfold wordsOf
  rw [Nat.mul_comm W ((m + W - 1) / W)]
  have h := Nat.div_mul_le_self (m + W - 1) W
  omega
/-- `⌈W · T / W⌉ = T`: a word-aligned block of `T` words is exactly `T` words. -/
lemma wordsOf_mul (W T : ℕ) (hW : 0 < W) : wordsOf W (W * T) = T := by
  unfold wordsOf
  have h1 : W * T + W - 1 = (W - 1) + T * W := by
    rw [Nat.mul_comm W T]; omega
  rw [h1, Nat.add_mul_div_right (W - 1) T hW, Nat.div_eq_of_lt (by omega), Nat.zero_add]
/-- `⌈(W · T + R) / W⌉ = T + ⌈R / W⌉`: the `CR` block starts at the word after the children's. -/
lemma wordsOf_mul_add (W T R : ℕ) (hW : 0 < W) :
    wordsOf W (W * T + R) = T + wordsOf W R := by
  unfold wordsOf
  have h1 : W * T + R + W - 1 = (R + W - 1) + T * W := by
    rw [Nat.mul_comm W T]; omega
  rw [h1, Nat.add_mul_div_right (R + W - 1) T hW, Nat.add_comm]
lemma wordsOf_mono (W : ℕ) (hW : 0 < W) {m T : ℕ} (h : m ≤ T) : wordsOf W m ≤ wordsOf W T := by
  unfold wordsOf
  exact Nat.div_le_div_right (by omega)
/-- **The padding slack**: `W · Σ_s ⌈f s/W⌉ ≤ Σ_s f s + L (W − 1)`. -/
lemma blkTotal_pad {L : ℕ} (W : ℕ) (hW : 0 < W) (f : Fin L → ℕ) :
    ((W * blkTotal W f : ℕ) : ℝ) ≤ (∑ s : Fin L, (f s : ℝ)) + (L : ℝ) * ((W : ℝ) - 1) := by
  have h1 : ((W * blkTotal W f : ℕ) : ℝ) = ∑ s : Fin L, ((W * wordsOf W (f s) : ℕ) : ℝ) := by
    rw [blkTotal]
    push_cast
    rw [Finset.mul_sum]
  have h2 : ∀ s : Fin L, ((W * wordsOf W (f s) : ℕ) : ℝ) ≤ (f s : ℝ) + ((W : ℝ) - 1) := by
    intro s
    have h := mul_wordsOf_le W (f s)
    have h3 : ((W * wordsOf W (f s) : ℕ) : ℝ) ≤ ((f s + (W - 1) : ℕ) : ℝ) := by
      exact_mod_cast h
    have h4 : ((f s + (W - 1) : ℕ) : ℝ) = (f s : ℝ) + ((W : ℝ) - 1) := by
      rw [Nat.cast_add, Nat.cast_pred hW]
    linarith
  calc ((W * blkTotal W f : ℕ) : ℝ)
      = ∑ s : Fin L, ((W * wordsOf W (f s) : ℕ) : ℝ) := h1
    _ ≤ ∑ s : Fin L, ((f s : ℝ) + ((W : ℝ) - 1)) := Finset.sum_le_sum fun s _ => h2 s
    _ = (∑ s : Fin L, (f s : ℝ)) + (L : ℝ) * ((W : ℝ) - 1) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]
lemma blkIdx_exists {L W : ℕ} (f : Fin L → ℕ) {wd : ℕ} (h : wd < blkTotal W f) :
    ∃ s : ℕ, wd < blkOff W f (s + 1) := by
  refine ⟨L, ?_⟩
  rw [blkOff_total f (by omega)]
  exact h
/-- The block containing word `wd`: the least `s` whose block ends after `wd`. -/
noncomputable def blkIdx {L W : ℕ} (f : Fin L → ℕ) (wd : ℕ) (h : wd < blkTotal W f) : ℕ :=
  Nat.find (blkIdx_exists f h)
lemma blkIdx_high {L W : ℕ} (f : Fin L → ℕ) {wd : ℕ} (h : wd < blkTotal W f) :
    wd < blkOff W f (blkIdx f wd h + 1) :=
  Nat.find_spec (blkIdx_exists f h)
lemma blkIdx_low {L W : ℕ} (f : Fin L → ℕ) {wd : ℕ} (h : wd < blkTotal W f) :
    blkOff W f (blkIdx f wd h) ≤ wd := by
  rcases Nat.eq_zero_or_pos (blkIdx f wd h) with h0 | hpos
  · rw [h0, blkOff_zero]; exact Nat.zero_le _
  · have hlt : blkIdx f wd h - 1 < Nat.find (blkIdx_exists f h) := by
      show blkIdx f wd h - 1 < blkIdx f wd h
      omega
    have hnp := Nat.find_min (blkIdx_exists f h) hlt
    have heq : blkIdx f wd h - 1 + 1 = blkIdx f wd h := by omega
    rw [heq] at hnp
    omega
lemma blkIdx_lt {L W : ℕ} (f : Fin L → ℕ) {wd : ℕ} (h : wd < blkTotal W f) :
    blkIdx f wd h < L := by
  by_contra hc
  have h1 : blkOff W f L ≤ wd := by
    have h2 : blkOff W f (blkIdx f wd h) ≤ wd := blkIdx_low f h
    have h3 : blkOff W f L ≤ blkOff W f (blkIdx f wd h) := blkOff_mono f (by omega)
    omega
  rw [blkOff_total f (le_refl L)] at h1
  omega
lemma blkIdx_unique {L W : ℕ} (f : Fin L → ℕ) {wd s : ℕ}
    (_hs : s < L) (hlo : blkOff W f s ≤ wd) (hhi : wd < blkOff W f (s + 1))
    (h : wd < blkTotal W f) : blkIdx f wd h = s := by
  have h1 : blkIdx f wd h ≤ s := Nat.find_min' (blkIdx_exists f h) hhi
  by_contra hc
  have h2 : blkIdx f wd h < s := lt_of_le_of_ne h1 hc
  have h3 : wd < blkOff W f (blkIdx f wd h + 1) := blkIdx_high f h
  have h4 : blkOff W f (blkIdx f wd h + 1) ≤ blkOff W f s := blkOff_mono f (by omega)
  omega
lemma div_lt_blkTotal {L W : ℕ} (hW : 0 < W) (f : Fin L → ℕ) {q : ℕ}
    (h : q < W * blkTotal W f) : q / W < blkTotal W f := by
  rw [Nat.div_lt_iff_lt_mul hW, Nat.mul_comm]
  exact h
/-- The block of the composite coordinate `q` (of the children's part). -/
noncomputable def compBlk {L : ℕ} (W : ℕ) (hW : 0 < W) (f : Fin L → ℕ) (q : ℕ)
    (h : q < W * blkTotal W f) : Fin L :=
  ⟨blkIdx f (q / W) (div_lt_blkTotal hW f h),
    blkIdx_lt f (div_lt_blkTotal hW f h)⟩
/-- The local bit of `q` inside its block (junk `≥ f s` means "padding"). -/
noncomputable def compBit {L : ℕ} (W : ℕ) (hW : 0 < W) (f : Fin L → ℕ) (q : ℕ)
    (h : q < W * blkTotal W f) : ℕ :=
  (q / W - blkOff W f (compBlk W hW f q h).val) * W + q % W
/-- The composite value at the coordinate `q` (a total function of `q : ℕ`; only the first
`W · blkTotal + R` values are used). -/
noncomputable def compAsmV {L : ℕ} (W : ℕ) (hW : 0 < W) (f : Fin L → ℕ) (R : ℕ)
    (v : (s : Fin L) → Fin (f s) → ZMod 2) (u : Fin R → ZMod 2) (q : ℕ) : ZMod 2 :=
  if h : q < W * blkTotal W f then
    if hk : compBit W hW f q h < f (compBlk W hW f q h) then
      v (compBlk W hW f q h) ⟨compBit W hW f q h, hk⟩
    else 0
  else if hq : q - W * blkTotal W f < R then u ⟨q - W * blkTotal W f, hq⟩ else 0
/-- The stored vector of the composite: the `W · Σ_s ⌈M_s/W⌉` coordinates of the word-aligned
children's blocks (in the prefix-sum order) followed by the `R` coordinates of the final `CR` block. -/
noncomputable def compAsm {L : ℕ} (W : ℕ) (hW : 0 < W) (f : Fin L → ℕ) (R : ℕ)
    (v : (s : Fin L) → Fin (f s) → ZMod 2) (u : Fin R → ZMod 2) :
    Fin (W * blkTotal W f + R) → ZMod 2 :=
  fun q => compAsmV W hW f R v u q.val
lemma blkEmb_lt_total {L : ℕ} (W : ℕ) (hW : 0 < W) (f : Fin L → ℕ) (s : Fin L) (k : Fin (f s)) :
    W * blkOff W f s.val + k.val < W * blkTotal W f := by
  have h1 : blkOff W f (s.val + 1) ≤ blkTotal W f := by
    rw [← blkOff_total f (le_refl L)]
    exact blkOff_mono f (by omega)
  have h2 : W * blkOff W f (s.val + 1) ≤ W * blkTotal W f := Nat.mul_le_mul_left W h1
  have h3 : k.val < W * wordsOf W (f s) := lt_of_lt_of_le k.isLt (le_mul_wordsOf W hW (f s))
  have h4 : W * blkOff W f s.val + W * wordsOf W (f s) = W * blkOff W f (s.val + 1) := by
    rw [blkOff_succ f s, Nat.mul_add]
  calc W * blkOff W f s.val + k.val
      < W * blkOff W f s.val + W * wordsOf W (f s) := Nat.add_lt_add_left h3 _
    _ = W * blkOff W f (s.val + 1) := h4
    _ ≤ W * blkTotal W f := h2
/-- The quotient `q / W` of a block address `q = W · blkOff s + k` is the block's word base plus
`k / W`. -/
lemma div_blk_of_blk {L : ℕ} (W : ℕ) (hW : 0 < W) (f : Fin L → ℕ) (s : Fin L) (k : Fin (f s)) :
    (W * blkOff W f s.val + k.val) / W = blkOff W f s.val + k.val / W := by
  refine Nat.div_eq_of_lt_le ?_ ?_
  · calc (blkOff W f s.val + k.val / W) * W
        = W * blkOff W f s.val + (k.val / W) * W := by ring
      _ ≤ W * blkOff W f s.val + k.val :=
          Nat.add_le_add_left (Nat.div_mul_le_self k.val W) _
  · have h2 : k.val % W < W := Nat.mod_lt _ hW
    calc W * blkOff W f s.val + k.val
        = W * blkOff W f s.val + (W * (k.val / W) + k.val % W) := by
            rw [Nat.div_add_mod k.val W]
      _ < W * blkOff W f s.val + (W * (k.val / W) + W) :=
          Nat.add_lt_add_left (Nat.add_lt_add_left h2 _) _
      _ = (blkOff W f s.val + k.val / W + 1) * W := by ring
/-- An address `W · blkOff s + k` has block `s` and local bit `k`. -/
lemma compBlk_bit_of_blk {L : ℕ} (W : ℕ) (hW : 0 < W) (f : Fin L → ℕ) (s : Fin L) (k : Fin (f s))
    (h : W * blkOff W f s.val + k.val < W * blkTotal W f) :
    compBlk W hW f (W * blkOff W f s.val + k.val) h = s ∧
      compBit W hW f (W * blkOff W f s.val + k.val) h = k.val := by
  set q : ℕ := W * blkOff W f s.val + k.val with hq
  have hdiv : q / W = blkOff W f s.val + k.val / W := by
    rw [hq]; exact div_blk_of_blk W hW f s k
  have hlow : blkOff W f s.val ≤ q / W := by
    rw [hdiv]; exact Nat.le_add_right _ _
  have hhi : q / W < blkOff W f (s.val + 1) := by
    have hk1 : k.val / W < wordsOf W (f s) := by
      rw [Nat.div_lt_iff_lt_mul hW, Nat.mul_comm (wordsOf W (f s)) W]
      exact lt_of_lt_of_le k.isLt (le_mul_wordsOf W hW (f s))
    rw [blkOff_succ f s, hdiv]
    exact Nat.add_lt_add_left hk1 _
  have hblk : compBlk W hW f q h = s := by
    exact Fin.ext (blkIdx_unique f s.isLt hlow hhi (div_lt_blkTotal hW f h))
  refine ⟨hblk, ?_⟩
  have h1 : q / W - blkOff W f (compBlk W hW f q h).val = k.val / W := by
    rw [hblk, hdiv]; omega
  have h2 : q % W = k.val % W := by
    rw [hq, Nat.add_comm, Nat.add_mul_mod_self_left]
  show (q / W - blkOff W f (compBlk W hW f q h).val) * W + q % W = k.val
  rw [h1, h2, Nat.mul_comm]
  exact Nat.div_add_mod k.val W
/-- A composite coordinate that is a block address reads the child's own entry. -/
lemma compAsmV_eq_blk {L : ℕ} (W : ℕ) (hW : 0 < W) (f : Fin L → ℕ) (R : ℕ)
    (v : (s : Fin L) → Fin (f s) → ZMod 2) (u : Fin R → ZMod 2) {q : ℕ}
    (h : q < W * blkTotal W f) {s : Fin L} (k : Fin (f s))
    (hblk : compBlk W hW f q h = s) (hbit : compBit W hW f q h = k.val) :
    compAsmV W hW f R v u q = v s k := by
  subst hblk
  unfold compAsmV
  have hk : compBit W hW f q h < f (compBlk W hW f q h) := by
    rw [hbit]; exact k.isLt
  rw [dif_pos h, dif_pos hk]
  exact congrArg (v (compBlk W hW f q h)) (Fin.ext hbit)
/-- **The entry of a child block is the child's own entry**: at bit `W · blkOff s + k` the composite
reads `v s k`. -/
lemma compAsmV_blk {L : ℕ} (W : ℕ) (hW : 0 < W) (f : Fin L → ℕ) (R : ℕ)
    (v : (s : Fin L) → Fin (f s) → ZMod 2) (u : Fin R → ZMod 2) (s : Fin L) (k : Fin (f s)) :
    compAsmV W hW f R v u (W * blkOff W f s.val + k.val) = v s k := by
  have h := blkEmb_lt_total W hW f s k
  obtain ⟨hblk, hbit⟩ := compBlk_bit_of_blk W hW f s k h
  exact compAsmV_eq_blk W hW f R v u h k hblk hbit
/-- The padding bits of a block read `0`. -/
lemma compAsmV_of_pad {L : ℕ} (W : ℕ) (hW : 0 < W) (f : Fin L → ℕ) (R : ℕ)
    (v : (s : Fin L) → Fin (f s) → ZMod 2) (u : Fin R → ZMod 2) {q : ℕ}
    (h : q < W * blkTotal W f) (hk : f (compBlk W hW f q h) ≤ compBit W hW f q h) :
    compAsmV W hW f R v u q = 0 := by
  unfold compAsmV
  rw [dif_pos h, dif_neg (by omega)]
/-- The `CR` block sits right after the children's words. -/
lemma compAsmV_cr {L : ℕ} (W : ℕ) (hW : 0 < W) (f : Fin L → ℕ) (R : ℕ)
    (v : (s : Fin L) → Fin (f s) → ZMod 2) (u : Fin R → ZMod 2) (q : Fin R) :
    compAsmV W hW f R v u (W * blkTotal W f + q.val) = u q := by
  unfold compAsmV
  rw [dif_neg (by omega : ¬ (W * blkTotal W f + q.val < W * blkTotal W f)),
    dif_pos (show W * blkTotal W f + q.val - W * blkTotal W f < R from by omega)]
  exact congrArg u (Fin.ext (by simp))
/-- `q` is `W · blkOff s + (local bit)` for `s` its own block. -/
lemma compBlk_bit_eq {L : ℕ} (W : ℕ) (hW : 0 < W) (f : Fin L → ℕ) {q : ℕ}
    (h : q < W * blkTotal W f) :
    W * blkOff W f (compBlk W hW f q h).val + compBit W hW f q h = q := by
  have h1 : blkOff W f (compBlk W hW f q h).val ≤ q / W := by
    have h2 := blkIdx_low f (div_lt_blkTotal hW f h)
    simpa [compBlk] using h2
  have e1 : W * blkOff W f (compBlk W hW f q h).val +
      (q / W - blkOff W f (compBlk W hW f q h).val) * W = W * (q / W) := by
    rw [Nat.mul_comm (q / W - blkOff W f (compBlk W hW f q h).val) W, ← Nat.mul_add,
      Nat.add_sub_of_le h1]
  have e2 : W * (q / W) + q % W = q := Nat.div_add_mod q W
  show W * blkOff W f (compBlk W hW f q h).val +
    ((q / W - blkOff W f (compBlk W hW f q h).val) * W + q % W) = q
  omega
/-- Two block addresses `W · blkOff s + k` coincide only in the same block. -/
lemma blkOff_emb_inj {L : ℕ} (W : ℕ) (hW : 0 < W) (f : Fin L → ℕ)
    {s s' : Fin L} {k : Fin (f s)} {k' : Fin (f s')}
    (h : W * blkOff W f s.val + k.val = W * blkOff W f s'.val + k'.val) : s = s' := by
  have hk : k.val < W * wordsOf W (f s) := lt_of_lt_of_le k.isLt (le_mul_wordsOf W hW (f s))
  have hk' : k'.val < W * wordsOf W (f s') := lt_of_lt_of_le k'.isLt (le_mul_wordsOf W hW (f s'))
  have key : ∀ a b : Fin L, a.val < b.val →
      W * blkOff W f a.val + W * wordsOf W (f a) ≤ W * blkOff W f b.val := by
    intro a b hab
    have h1 : blkOff W f a.val + wordsOf W (f a) ≤ blkOff W f b.val := by
      rw [← blkOff_succ f a]
      exact blkOff_mono f (by omega)
    calc W * blkOff W f a.val + W * wordsOf W (f a)
        = W * (blkOff W f a.val + wordsOf W (f a)) := (Nat.mul_add _ _ _).symm
      _ ≤ W * blkOff W f b.val := Nat.mul_le_mul_left W h1
  rcases lt_trichotomy s.val s'.val with hlt | heq | hgt
  · have h1 := key s s' hlt; omega
  · exact Fin.ext heq
  · have h1 := key s' s hgt; omega
/-- The assembly is additive. -/
lemma compAsm_add {L : ℕ} (W : ℕ) (hW : 0 < W) (f : Fin L → ℕ) (R : ℕ)
    (v v' : (s : Fin L) → Fin (f s) → ZMod 2) (u u' : Fin R → ZMod 2) :
    compAsm W hW f R (v + v') (u + u') = compAsm W hW f R v u + compAsm W hW f R v' u' := by
  funext q
  show compAsmV W hW f R (v + v') (u + u') q.val =
    compAsmV W hW f R v u q.val + compAsmV W hW f R v' u' q.val
  unfold compAsmV
  by_cases h : q.val < W * blkTotal W f
  · rw [dif_pos h, dif_pos h, dif_pos h]
    by_cases hk : compBit W hW f q.val h < f (compBlk W hW f q.val h)
    · rw [dif_pos hk, dif_pos hk, dif_pos hk]
      rfl
    · rw [dif_neg hk, dif_neg hk, dif_neg hk, add_zero]
  · rw [dif_neg h, dif_neg h, dif_neg h]
    by_cases hq : q.val - W * blkTotal W f < R
    · rw [dif_pos hq, dif_pos hq, dif_pos hq]
      rfl
    · rw [dif_neg hq, dif_neg hq, dif_neg hq, add_zero]
/-- The assembly is `ZMod 2`-homogeneous. -/
lemma compAsm_smul {L : ℕ} (W : ℕ) (hW : 0 < W) (f : Fin L → ℕ) (R : ℕ)
    (c : ZMod 2) (v : (s : Fin L) → Fin (f s) → ZMod 2) (u : Fin R → ZMod 2) :
    compAsm W hW f R (c • v) (c • u) = c • compAsm W hW f R v u := by
  funext q
  show compAsmV W hW f R (c • v) (c • u) q.val = c • compAsmV W hW f R v u q.val
  unfold compAsmV
  by_cases h : q.val < W * blkTotal W f
  · rw [dif_pos h, dif_pos h]
    by_cases hk : compBit W hW f q.val h < f (compBlk W hW f q.val h)
    · rw [dif_pos hk, dif_pos hk]
      rfl
    · rw [dif_neg hk, dif_neg hk]
      exact (smul_zero c).symm
  · rw [dif_neg h, dif_neg h]
    by_cases hq : q.val - W * blkTotal W f < R
    · rw [dif_pos hq, dif_pos hq]
      rfl
    · rw [dif_neg hq, dif_neg hq]
      exact (smul_zero c).symm
/-- The weight of the assembled vector is the sum of the weights of the blocks: the blocks occupy
disjoint, word-aligned coordinate ranges of `Fin (W · Σ_s ⌈M_s/W⌉ + R)`. -/
theorem sum_compAsm {L : ℕ} (W : ℕ) (hW : 0 < W) (f : Fin L → ℕ) (R : ℕ)
    (v : (s : Fin L) → Fin (f s) → ZMod 2) (u : Fin R → ZMod 2) :
    (∑ q : Fin (W * blkTotal W f + R), (compAsm W hW f R v u q).val)
      = (∑ s : Fin L, ∑ k : Fin (f s), (v s k).val) + ∑ q : Fin R, (u q).val := by
  rw [Fin.sum_univ_add]
  congr 1
  · have hcast : ∀ q : Fin (W * blkTotal W f),
        compAsm W hW f R v u (Fin.castAdd R q) = compAsmV W hW f R v u q.val :=
      fun q => rfl
    simp only [hcast]
    rw [Fin.sum_univ_eq_sum_range (fun n => (compAsmV W hW f R v u n).val)]
    have hpt : ∀ q ∈ Finset.range (W * blkTotal W f),
        (compAsmV W hW f R v u q).val
          = ∑ s : Fin L, ∑ k : Fin (f s),
              (if W * blkOff W f s.val + k.val = q then (v s k).val else 0) := by
      intro q hq
      rw [Finset.mem_range] at hq
      by_cases hin : ∃ (s : Fin L) (k : Fin (f s)), W * blkOff W f s.val + k.val = q
      · obtain ⟨s, k, hsk⟩ := hin
        have h1 : compAsmV W hW f R v u q = v s k := by
          rw [← hsk]; exact compAsmV_blk W hW f R v u s k
        have hzero : ∀ s' ∈ (Finset.univ : Finset (Fin L)), s' ≠ s →
            (∑ k' : Fin (f s'),
              (if W * blkOff W f s'.val + k'.val = q then (v s' k').val else 0)) = 0 := by
          intro s' _ hs'
          refine Finset.sum_eq_zero fun k' _ => ?_
          rw [if_neg]
          intro he
          exact hs' (blkOff_emb_inj W hW f (by rw [he, hsk]))
        have hzero2 : ∀ k' ∈ (Finset.univ : Finset (Fin (f s))), k' ≠ k →
            (if W * blkOff W f s.val + k'.val = q then (v s k').val else 0) = 0 := by
          intro k' _ hk'
          rw [if_neg]
          intro he
          refine hk' (Fin.ext ?_)
          have h4 : W * blkOff W f s.val + k'.val = W * blkOff W f s.val + k.val := by
            rw [he, hsk]
          omega
        rw [h1, Finset.sum_eq_single s hzero
          (fun h => absurd (Finset.mem_univ s) h)]
        rw [Finset.sum_eq_single k hzero2
          (fun h => absurd (Finset.mem_univ k) h)]
        rw [if_pos hsk]
      · have hin' : ∀ (s : Fin L) (k : Fin (f s)), W * blkOff W f s.val + k.val ≠ q := by
          intro s k he
          exact hin ⟨s, k, he⟩
        have hpad : f (compBlk W hW f q hq) ≤ compBit W hW f q hq := by
          by_contra hlt
          rw [not_le] at hlt
          exact hin' (compBlk W hW f q hq)
            (⟨compBit W hW f q hq, hlt⟩ : Fin (f (compBlk W hW f q hq)))
            (compBlk_bit_eq W hW f hq)
        rw [compAsmV_of_pad W hW f R v u hq hpad]
        symm
        refine Finset.sum_eq_zero fun s _ => ?_
        refine Finset.sum_eq_zero fun k _ => ?_
        rw [if_neg]
        exact hin' s k
    calc (∑ q ∈ Finset.range (W * blkTotal W f), (compAsmV W hW f R v u q).val)
        = ∑ q ∈ Finset.range (W * blkTotal W f), ∑ s : Fin L, ∑ k : Fin (f s),
            (if W * blkOff W f s.val + k.val = q then (v s k).val else 0) :=
          Finset.sum_congr rfl hpt
      _ = ∑ s : Fin L, ∑ k : Fin (f s), ∑ q ∈ Finset.range (W * blkTotal W f),
            (if W * blkOff W f s.val + k.val = q then (v s k).val else 0) := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun s _ => Finset.sum_comm
      _ = ∑ s : Fin L, ∑ k : Fin (f s), (v s k).val := by
          refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun k _ => ?_
          rw [Finset.sum_eq_single (W * blkOff W f s.val + k.val)]
          · rw [if_pos rfl]
          · intro b _ hb
            rw [if_neg (by intro he; exact hb he.symm)]
          · intro h
            exact absurd (Finset.mem_range.mpr (blkEmb_lt_total W hW f s k)) h
  · refine Finset.sum_congr rfl fun q _ => ?_
    have h1 : compAsm W hW f R v u (Fin.natAdd (W * blkTotal W f) q)
        = compAsmV W hW f R v u (W * blkTotal W f + q.val) := rfl
    rw [h1, compAsmV_cr]
/-- The column weight of the assembled composite is the sum of the blocks' column weights. -/
lemma comp_colWeight_le {L : ℕ} (W : ℕ) (hW : 0 < W) (f : Fin L → ℕ) (R : ℕ)
    (v : (s : Fin L) → Fin (f s) → ZMod 2) (u : Fin R → ZMod 2) (C D : ℝ)
    (hv : ∀ s, (∑ k, ((v s k).val : ℝ)) ≤ C)
    (hu : (∑ q, ((u q).val : ℝ)) ≤ D) :
    (((univ.filter fun q : Fin (W * blkTotal W f + R) => compAsm W hW f R v u q = 1).card : ℕ) : ℝ) ≤
      (L : ℝ) * C + D := by
  rw [comp_card_filter_one_eq_sum_val, sum_compAsm]
  push_cast
  have h1 : (∑ s : Fin L, ∑ k : Fin (f s), ((v s k).val : ℝ)) ≤ ∑ _s : Fin L, C :=
    Finset.sum_le_sum fun s _ => hv s
  have h2 : (∑ s : Fin L, ∑ k : Fin (f s), ((v s k).val : ℝ)) ≤ (L : ℝ) * C := by
    refine le_trans h1 ?_
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  linarith


/-! ### 10.4 One child: Theorem 5.1 at universe `N = d` -/
/-- The data and the four data-structure conjuncts of one top-level child: the `HintSketch` matrix of
Theorem 5.1 at universe `N = d` with the capacities `(X, Y)` of (28). -/
structure CompChild (α C₁ C₂ C₃ : ℝ) (p₁ pu : ℕ) (cW Cu : ℝ) (n d lam X Y : ℕ) where
  W : ℕ
  M : ℕ
  spec : TableSpec
  det : ℕ → ℕ
  H : spec.Seed → (Fin d → ZMod 2) →ₗ[ZMod 2] (Fin M → ZMod 2)
  widthOK : WidthOK W n cW (lg (n : ℝ))
  fits : spec.Fits W
  wordsOK : wordsOf W M ≤ 2 ^ W
  lenOK : (M : ℝ) ≤ (1 + C₁ / lg (n : ℝ)) * ((X : ℝ) + α * hN d (Y : ℝ)) +
    C₂ * ((d : ℝ) / lg (n : ℝ) ^ 8) + C₃ * (lam : ℝ) * lg (n : ℝ) ^ p₁
  colOK : ∀ r, ColumnWeightLE (H r) (Cu * lg (n : ℝ) ^ pu)
/-- The `k`-th permutation of the concatenated table list, read as a permutation of `Fin N`; outside
the list (or at a size mismatch) it is junk.  `H` is linear for *every* such reading, and the four
conjuncts below are quantified over all seeds, so the junk values never matter. -/
noncomputable def specPerm (spec : TableSpec) (r : spec.Seed) (k N : ℕ) : Equiv.Perm (Fin N) :=
  if h : k < spec.permSizes.length then
    if h2 : spec.permSizes.get ⟨k, h⟩ = N then (h2 ▸ r.1 ⟨k, h⟩) else 1
  else 1
/-- Entry `a` of the `k`-th coefficient table of the concatenated list, junk outside the range. -/
noncomputable def specCoeff (spec : TableSpec) (r : spec.Seed) (k a : ℕ) : ℕ :=
  if h : k < spec.coeffShapes.length then
    if h' : a < (spec.coeffShapes.get ⟨k, h⟩).1 then
      ((r.2 ⟨k, h⟩) ⟨a, h'⟩).val
    else 0
  else 0
/-- The seed of child `s` inside the composite seed: its permutation table and its coefficient table
are the blocks at the offsets `1 + Σ_{t<s} …` of the concatenation (the first composite permutation
table and the first coefficient table hold the top-level data). -/
noncomputable def compChildSeed {ℓ : ℕ} (spec : TableSpec) (r : spec.Seed)
    (childSpec : Fin ℓ → TableSpec) (s : Fin ℓ) : (childSpec s).Seed :=
  (fun k => specPerm spec r
      (1 + (∑ t : Fin ℓ, if t.val < s.val then (childSpec t).permSizes.length else 0) + k.val)
      ((childSpec s).permSizes.get k),
   fun k a => ⟨specCoeff spec r
      (1 + (∑ t : Fin ℓ, if t.val < s.val then (childSpec t).coeffShapes.length else 0) + k.val) a
        % ((childSpec s).coeffShapes.get k).2,
     Nat.mod_lt _ ((childSpec s).coeff_pos _ (List.get_mem _ _))⟩)
/-- The element of `𝔽_{2^w}` whose `w`-bit representation is `v mod 2^w` (it is `0` for `v = 0`). -/
noncomputable def galOfNat (w : ℕ) (hw : 1 ≤ w) (v : ℕ) : GaloisField 2 w :=
  letI : Fact (Nat.Prime 2) := inferInstance
  letI : Fintype (GaloisField 2 w) := Fintype.ofFinite _
  (Fintype.equivFin (GaloisField 2 w)).symm
    ⟨v % 2 ^ w, by
      have hc : Fintype.card (GaloisField 2 w) = 2 ^ w := by
        rw [← Nat.card_eq_fintype_card]
        exact GaloisField.card 2 w (by omega)
      rw [hc]
      exact Nat.mod_lt _ (Nat.pow_pos (by norm_num : 0 < 2))⟩
/-- **The column-weight arithmetic of the composite**: the `ℓ` children's blocks (each of weight
`Cu log^{pu} n`) plus the final `CR` block (of weight `K log²(n+2)`) still weigh only
`Cu_composite log^{pu+2} n`, because `ℓ ≤ 9(4C'+1)log² n` and `log(n+2) ≤ 3 log n`
(`6toplevel.tex` 320-322). -/
lemma comp_col_bound (ell n : ℕ) (hn : 2 ≤ n) (C' : ℕ) (Cu K23 Cuc : ℝ) (pu : ℕ)
    (hell : (ell : ℝ) ≤ (4 * (C' : ℝ) + 1) * (lg (n : ℝ) + 2) ^ 2)
    (hCuc : Cuc = 9 * (4 * (C' : ℝ) + 1) * Cu + 9 * K23)
    (hCu : 0 ≤ Cu) (hK23 : 0 ≤ K23) :
    (ell : ℝ) * (Cu * lg (n : ℝ) ^ pu) + K23 * lg ((n : ℝ) + 2) ^ 2 ≤
      Cuc * lg (n : ℝ) ^ (pu + 2) := by
  have hlgn1 : (1 : ℝ) ≤ lg (n : ℝ) := one_le_lg hn
  have hell9 : (ell : ℝ) ≤ 9 * (4 * (C' : ℝ) + 1) * lg (n : ℝ) ^ 2 := by
    have hsq : (lg (n : ℝ) + 2) ^ 2 ≤ 9 * lg (n : ℝ) ^ 2 := sq_add_two_sq_le hlgn1
    have h4 : ((4 : ℝ) * (C' : ℝ) + 1) * (lg (n : ℝ) + 2) ^ 2 ≤
        ((4 : ℝ) * (C' : ℝ) + 1) * (9 * lg (n : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left hsq (by positivity)
    nlinarith [hell, h4]
  have hlg2 : lg ((n : ℝ) + 2) ^ 2 ≤ 9 * lg (n : ℝ) ^ 2 := by
    have h3 := lg_add_two_le_three hn
    have hpos2 : (0 : ℝ) < lg ((n : ℝ) + 2) := by
      have h5 : (2 : ℝ) ≤ (n : ℝ) + 2 := by
        have h6 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
        linarith
      have h6 := lg_mono (by norm_num : (0 : ℝ) < 2) h5
      rw [lg_two] at h6
      linarith
    exact sq_le_nine_sq (le_of_lt hpos2) h3 (by linarith)
  have hsq_le : lg (n : ℝ) ^ 2 ≤ lg (n : ℝ) ^ (pu + 2) :=
    pow_le_pow_right₀ hlgn1 (by omega)
  have h1 : (ell : ℝ) * (Cu * lg (n : ℝ) ^ pu) ≤
      9 * (4 * (C' : ℝ) + 1) * Cu * lg (n : ℝ) ^ (pu + 2) := by
    have h0 : (0 : ℝ) ≤ Cu * lg (n : ℝ) ^ pu := by positivity
    have h2 : (ell : ℝ) * (Cu * lg (n : ℝ) ^ pu) ≤
        (9 * (4 * (C' : ℝ) + 1) * lg (n : ℝ) ^ 2) * (Cu * lg (n : ℝ) ^ pu) :=
      mul_le_mul_of_nonneg_right hell9 h0
    have h3 : (9 * (4 * (C' : ℝ) + 1) * lg (n : ℝ) ^ 2) * (Cu * lg (n : ℝ) ^ pu) =
        9 * (4 * (C' : ℝ) + 1) * Cu * lg (n : ℝ) ^ (pu + 2) := by
      rw [pow_add]
      ring
    linarith [h2, h3]
  have h2' : K23 * lg ((n : ℝ) + 2) ^ 2 ≤ 9 * K23 * lg (n : ℝ) ^ (pu + 2) := by
    have h3 : K23 * lg ((n : ℝ) + 2) ^ 2 ≤ K23 * (9 * lg (n : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left hlg2 hK23
    have h4 : K23 * (9 * lg (n : ℝ) ^ 2) = 9 * K23 * lg (n : ℝ) ^ 2 := by ring
    have h5 : 9 * K23 * lg (n : ℝ) ^ 2 ≤ 9 * K23 * lg (n : ℝ) ^ (pu + 2) :=
      mul_le_mul_of_nonneg_left hsq_le (by linarith)
    linarith [h3, h4, h5]
  rw [hCuc]
  calc (ell : ℝ) * (Cu * lg (n : ℝ) ^ pu) + K23 * lg ((n : ℝ) + 2) ^ 2
      ≤ 9 * (4 * (C' : ℝ) + 1) * Cu * lg (n : ℝ) ^ (pu + 2) +
        9 * K23 * lg (n : ℝ) ^ (pu + 2) := by linarith [h1, h2']
    _ = (9 * (4 * (C' : ℝ) + 1) * Cu + 9 * K23) * lg (n : ℝ) ^ (pu + 2) := by ring

/-! ### 10.5 The composite object and its conjuncts -/
/-- **One composite datum**: the word width, the payload length and the four pieces of §3.2's
construction (`spec`, `det`, `H`).  Bundling them is what lets the three machine conjuncts be stated
about the construction's *own* datum instead of about every datum (which would be false). -/
structure CompDatum (n : ℕ) where
  /-- Word width. -/
  W : ℕ
  /-- Number of stored bits. -/
  M : ℕ
  /-- The public table specification. -/
  spec : TableSpec
  /-- The deterministic preprocessed table. -/
  det : ℕ → ℕ
  /-- The sketch matrix, as a linear map per seed. -/
  H : spec.Seed → (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin M → ZMod 2)

/-! ### 11.3 The three conjuncts, verbatim -/
/-- **The three machine conjuncts of `theorem_6_5_statement`** — its conjuncts 6, 7 and 8, with the
`∀ r` where the platform statement puts it:

6. `∀ r, TogglesWithin progUp (spec.env W det r) (H r) Tup` — a toggle of one input bit is an actual
   XOR of the column `H e_i` into the stored payload, in time `Tup`;
7. `∀ r y, ∃ s', HaltsWithin progDec (spec.env W det r) Tdec (decoderStart W y []) s'` — worst-case
   decoding from every stored payload, in time `Tdec`;
8. `∀ x, ‖x‖₀ ≤ d → 1 - eps ≤ prU (fun r => ∃ s', HaltsWithin … (decoderStart W (H r x) []) s' ∧
   OutputsSupport s' x)` — every `d`-sparse `x` is recovered except with probability `eps`. -/
def MachineConjuncts (progUp progDec : Program) (n d M W : ℕ) (spec : TableSpec) (det : ℕ → ℕ)
    (H : spec.Seed → (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin M → ZMod 2)) (Tup Tdec eps : ℝ) : Prop :=
  (∀ r, TogglesWithin progUp (spec.env W det r) (H r) Tup) ∧
  (∀ (r : spec.Seed) (y : Fin M → ZMod 2), ∃ s' : RAMState,
    HaltsWithin progDec (spec.env W det r) Tdec (decoderStart W y []) s') ∧
  (∀ x : Fin n → ZMod 2, (univ.filter fun i => x i = 1).card ≤ d →
    1 - eps ≤ prU (fun r : spec.Seed => ∃ s' : RAMState,
      HaltsWithin progDec (spec.env W det r) Tdec (decoderStart W (H r x) []) s' ∧
      OutputsSupport s' x))
/-- `MachineConjuncts` *is* the last three conjuncts of `theorem_6_5_statement`: this equivalence
records that no binder was hoisted and no predicate was weakened. -/
theorem machineConjuncts_iff (progUp progDec : Program) (n d M W : ℕ) (spec : TableSpec)
    (det : ℕ → ℕ) (H : spec.Seed → (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin M → ZMod 2))
    (Tup Tdec eps : ℝ) :
    MachineConjuncts progUp progDec n d M W spec det H Tup Tdec eps ↔
      ((∀ r, TogglesWithin progUp (spec.env W det r) (H r) Tup) ∧
       (∀ (r : spec.Seed) (y : Fin M → ZMod 2), ∃ s' : RAMState,
         HaltsWithin progDec (spec.env W det r) Tdec (decoderStart W y []) s') ∧
       (∀ x : Fin n → ZMod 2, (univ.filter fun i => x i = 1).card ≤ d →
         1 - eps ≤ prU (fun r : spec.Seed => ∃ s' : RAMState,
           HaltsWithin progDec (spec.env W det r) Tdec (decoderStart W (H r x) []) s' ∧
           OutputsSupport s' x))) :=
  Iff.rfl

/-! ### 11.4 Theorem 6.5's body, modulo the three machine conjuncts -/
/-- **6.5's eight conjuncts from §10's five plus the three machine ones.**

The datum is a parameter (`D : CompDatum n`), so the three hypotheses are about the very
`(W, M, spec, det, H)` that §10 builds — no vacuity.  `D` is what `composite_sketch` produces at
`(n, d, lam)`; §11.7 records how to name it (`Classical.choose`) so that this theorem closes 6.5.

`hSup`/`hSdec` are 5.1's export clause: the composite runs `Sup` once per block and `Sdec` once per
child, which a bare `Program` cannot express (§11.1). -/
theorem theorem_6_5_of_composite (progUp progDec : Program) (Sup Sdec : Stmt)
    (hSup : Sup.compile 0 ++ [Instr.halt] = progUp)
    (hSdec : Sdec.compile 0 ++ [Instr.halt] = progDec)
    {n d : ℕ} (D : CompDatum n) (cW Cl Cu Cd : ℝ) (pl pu lam : ℕ) (eps : ℝ)
    (hWidth : WidthOK D.W n cW (lg (n : ℝ)))
    (hFits : D.spec.Fits D.W)
    (hWords : wordsOf D.W D.M ≤ 2 ^ D.W)
    (hLen : (D.M : ℝ) ≤ L n d + Cl * (d : ℝ) + Cl * (lam : ℝ) * lg (n : ℝ) ^ pl)
    (hCol : ∀ r, ColumnWeightLE (D.H r) (Cu * lg (n : ℝ) ^ pu))
    (hUp : ∀ r, TogglesWithin progUp (D.spec.env D.W D.det r) (D.H r) (Cu * lg (n : ℝ) ^ pu))
    (hDec : ∀ (r : D.spec.Seed) (y : Fin D.M → ZMod 2), ∃ s' : RAMState,
      HaltsWithin progDec (D.spec.env D.W D.det r)
        (Cd * (d : ℝ) * Real.exp (Cd * lg (lg (n : ℝ)) ^ 2)) (decoderStart D.W y []) s')
    (hFail : ∀ x : Fin n → ZMod 2, (univ.filter fun i => x i = 1).card ≤ d →
      1 - eps ≤ prU (fun r : D.spec.Seed => ∃ s' : RAMState,
        HaltsWithin progDec (D.spec.env D.W D.det r)
          (Cd * (d : ℝ) * Real.exp (Cd * lg (lg (n : ℝ)) ^ 2))
          (decoderStart D.W (D.H r x) []) s' ∧
        OutputsSupport s' x)) :
    ∃ (W M : ℕ) (spec : TableSpec) (det : ℕ → ℕ)
      (H : spec.Seed → (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin M → ZMod 2)),
      WidthOK W n cW (lg (n : ℝ)) ∧ spec.Fits W ∧ wordsOf W M ≤ 2 ^ W ∧
      (M : ℝ) ≤ L n d + Cl * (d : ℝ) + Cl * (lam : ℝ) * lg (n : ℝ) ^ pl ∧
      (∀ r, ColumnWeightLE (H r) (Cu * lg (n : ℝ) ^ pu)) ∧
      MachineConjuncts progUp progDec n d M W spec det H
        (Cu * lg (n : ℝ) ^ pu)
        (Cd * (d : ℝ) * Real.exp (Cd * lg (lg (n : ℝ)) ^ 2)) eps :=
  ⟨D.W, D.M, D.spec, D.det, D.H, hWidth, hFits, hWords, hLen, hCol, hUp, hDec, hFail⟩

/-! ### 11.5 The failure probability: the paper's union bound (`6toplevel.tex` 276–284)

The paper's chain is `Pr[recovery fails] ≤ (2ℓ+1)·2^{-λ_*} + ℓ·(2^{-λ-1}/ℓ) ≤ 2^{-λ} ≤ ε`.  This is
the correct *layer* for that arithmetic — at 5.1's own level the children inherit the root's `λ`, so
5.1 uses a flat budget instead.  Everything below is proved. -/

/-! `open Classical` is what makes `prU`'s own `Finset.filter` instance the one used here: `prU`
filters an *opaque* predicate, so its body takes `Classical.propDecidable`, while a hand-written
`fun a => P a ∨ Q a` would take `instDecidableOr` and the two filters would not be definitionally
equal.  A scoped `open Classical` at this point of the file affects only the rest of the file. -/
open Classical
/-- Unfolding `prU`. -/
lemma prU_eq_card {α : Type} [Fintype α] (P : α → Prop) :
    prU P = ((univ.filter P).card : ℝ) / (Fintype.card α : ℝ) := rfl
/-- `prU` is monotone in the event. -/
lemma prU_mono {α : Type} [Fintype α] {P Q : α → Prop} (h : ∀ a, P a → Q a) : prU P ≤ prU Q := by
  have h1 : (univ.filter P).card ≤ (univ.filter Q).card := by
    apply Finset.card_le_card
    intro a ha
    rw [Finset.mem_filter] at ha ⊢
    exact ⟨ha.1, h a ha.2⟩
  rw [prU_eq_card P, prU_eq_card Q]
  exact div_le_div_of_nonneg_right (by exact_mod_cast h1) (by positivity)
/-- `Pr[P ∨ Q] ≤ Pr[P] + Pr[Q]`. -/
lemma prU_or_le {α : Type} [Fintype α] (P Q : α → Prop) :
    prU (fun a => P a ∨ Q a) ≤ prU P + prU Q := by
  set R : α → Prop := fun a => P a ∨ Q a with hR
  letI : DecidablePred R := fun a => Classical.propDecidable (R a)
  have h1 : (univ.filter R).card ≤ (univ.filter P).card + (univ.filter Q).card := by
    have h2 : (univ.filter R) ⊆ univ.filter P ∪ univ.filter Q := by
      intro a ha
      rw [Finset.mem_filter] at ha
      rcases ha.2 with h | h
      · exact Finset.mem_union_left _ (by rw [Finset.mem_filter]; exact ⟨ha.1, h⟩)
      · exact Finset.mem_union_right _ (by rw [Finset.mem_filter]; exact ⟨ha.1, h⟩)
    exact le_trans (Finset.card_le_card h2) (Finset.card_union_le _ _)
  have h3 : ((univ.filter R).card : ℝ) ≤
      ((univ.filter P).card : ℝ) + ((univ.filter Q).card : ℝ) := by exact_mod_cast h1
  rw [prU_eq_card R, prU_eq_card P, prU_eq_card Q, ← add_div]
  exact div_le_div_of_nonneg_right h3 (by positivity)
/-- Union bound: `Pr[∃ i, E i] ≤ ∑ i, Pr[E i]`. -/
lemma prU_exists_le_sum {α ι : Type} [Fintype α] [Fintype ι] (E : ι → α → Prop) :
    prU (fun a => ∃ i, E i a) ≤ ∑ i, prU (E i) := by
  set R : α → Prop := fun a => ∃ i, E i a with hR
  letI : DecidablePred R := fun a => Classical.propDecidable (R a)
  have h1 : (univ.filter R) ⊆ univ.biUnion (fun i => univ.filter (E i)) := by
    intro a ha
    rw [Finset.mem_filter] at ha
    obtain ⟨i, hi⟩ := ha.2
    exact Finset.mem_biUnion.2 ⟨i, Finset.mem_univ i, by rw [Finset.mem_filter]; exact ⟨ha.1, hi⟩⟩
  have h4 : ((univ.filter R).card : ℝ) ≤ ∑ i, ((univ.filter (E i)).card : ℝ) := by
    have h2 : (univ.filter R).card ≤ (univ.biUnion (fun i => univ.filter (E i))).card :=
      Finset.card_le_card h1
    have h3 : (univ.biUnion (fun i => univ.filter (E i))).card ≤ ∑ i, (univ.filter (E i)).card :=
      Finset.card_biUnion_le
    exact_mod_cast le_trans h2 h3
  rw [prU_eq_card R]
  have h7 : (∑ i, prU (E i)) =
      (∑ i, ((univ.filter (E i)).card : ℝ)) / (Fintype.card α : ℝ) := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun i _ => (prU_eq_card (E i)).symm
  rw [h7]
  exact div_le_div_of_nonneg_right h4 (by positivity)
/-- The complement of an event has probability `1` minus its probability. -/
lemma prU_compl {α : Type} [Fintype α] [Nonempty α] (P : α → Prop) :
    prU (fun a => ¬ P a) = 1 - prU P := by
  set R : α → Prop := fun a => ¬ P a with hR
  letI : DecidablePred R := fun a => Classical.propDecidable (R a)
  have hcard : (0 : ℝ) < (Fintype.card α : ℝ) := by
    have h : 0 < Fintype.card α := Fintype.card_pos
    exact_mod_cast h
  have hsum : (univ.filter P).card + (univ.filter R).card = Fintype.card α := by
    have h := Finset.card_filter_add_card_filter_not (s := (univ : Finset α)) (p := P)
    rw [Finset.card_univ] at h
    convert h using 2
  have hcast : ((univ.filter R).card : ℝ) =
      (Fintype.card α : ℝ) - ((univ.filter P).card : ℝ) := by
    have h2 : ((univ.filter P).card : ℝ) + ((univ.filter R).card : ℝ) =
        (Fintype.card α : ℝ) := by exact_mod_cast hsum
    linarith
  rw [prU_eq_card R, prU_eq_card P, hcast, sub_div, div_self (ne_of_gt hcard)]
/-- `2^{-λ} ≤ ε` when `λ = ⌈log(1/ε)⌉`: the last link of the paper's chain. -/
lemma two_pow_inv_ceil_lg_le {eps : ℝ} (heps : 0 < eps) :
    ((2 : ℝ) ^ (⌈lg (1 / eps)⌉₊ : ℕ))⁻¹ ≤ eps := by
  have hpos : (0 : ℝ) < 1 / eps := by positivity
  have hlg : (2 : ℝ) ^ Real.logb 2 (1 / eps) = 1 / eps :=
    Real.rpow_logb (by norm_num) (by norm_num) hpos
  have hle : (2 : ℝ) ^ Real.logb 2 (1 / eps) ≤ (2 : ℝ) ^ ((⌈lg (1 / eps)⌉₊ : ℕ) : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.le_ceil _)
  have hmain : (1 / eps) ≤ (2 : ℝ) ^ (⌈lg (1 / eps)⌉₊ : ℕ) := by
    calc (1 / eps) = (2 : ℝ) ^ Real.logb 2 (1 / eps) := hlg.symm
      _ ≤ (2 : ℝ) ^ ((⌈lg (1 / eps)⌉₊ : ℕ) : ℝ) := hle
      _ = (2 : ℝ) ^ (⌈lg (1 / eps)⌉₊ : ℕ) := Real.rpow_natCast 2 _
  have h2pos : (0 : ℝ) < (2 : ℝ) ^ (⌈lg (1 / eps)⌉₊ : ℕ) := by positivity
  calc ((2 : ℝ) ^ (⌈lg (1 / eps)⌉₊ : ℕ))⁻¹ ≤ ((1 / eps))⁻¹ := by
        rw [inv_le_inv₀ h2pos hpos]
        exact hmain
    _ = eps := by rw [inv_div]; simp
/-- **The paper's arithmetic** (`6toplevel.tex` 279–283):
`(2ℓ+1)·2^{-λ_*} + ℓ·(2^{-λ-1}/ℓ) ≤ 2^{-λ}` from `(2ℓ+2)·2^{-λ_*} ≤ 2^{-λ-1}`.

The `ℓ = 0` case, which the paper's `2ℓ+1` suggests never occurs, is *also* proved: then the second
term is `0` (an empty union bound), `2ℓ+1 = 1`, and `2·2^{-λ_*} ≤ 2^{-λ-1}` already gives
`2^{-λ_*} ≤ 2^{-λ}`.  So the inequality needs no case hypothesis. -/
lemma failure_arith {ell lam lamStar : ℕ}
    (harith : ((2 * ell + 2 : ℕ) : ℝ) * ((2 : ℝ) ^ lamStar)⁻¹ ≤ ((2 : ℝ) ^ (lam + 1))⁻¹) :
    ((2 * ell + 1 : ℕ) : ℝ) * ((2 : ℝ) ^ lamStar)⁻¹ +
        (ell : ℝ) * (((2 : ℝ) ^ (lam + 1))⁻¹ / (ell : ℝ)) ≤ ((2 : ℝ) ^ lam)⁻¹ := by
  have hX : (0 : ℝ) ≤ ((2 : ℝ) ^ lamStar)⁻¹ := by positivity
  have h2Y : 2 * ((2 : ℝ) ^ (lam + 1))⁻¹ = ((2 : ℝ) ^ lam)⁻¹ := by
    rw [pow_succ]
    field_simp
  rcases Nat.eq_zero_or_pos ell with h0 | hpos
  · subst h0
    have harith0 : 2 * ((2 : ℝ) ^ lamStar)⁻¹ ≤ ((2 : ℝ) ^ (lam + 1))⁻¹ := by
      simpa using harith
    have hgoal : ((2 * 0 + 1 : ℕ) : ℝ) * ((2 : ℝ) ^ lamStar)⁻¹ +
        ((0 : ℕ) : ℝ) * (((2 : ℝ) ^ (lam + 1))⁻¹ / ((0 : ℕ) : ℝ)) =
        ((2 : ℝ) ^ lamStar)⁻¹ := by
      push_cast
      ring
    rw [hgoal]
    linarith
  · have hell0 : (0 : ℝ) < (ell : ℝ) := by exact_mod_cast hpos
    have hellY : (ell : ℝ) * (((2 : ℝ) ^ (lam + 1))⁻¹ / (ell : ℝ)) =
        ((2 : ℝ) ^ (lam + 1))⁻¹ := by
      field_simp
    have hstep : ((2 * ell + 1 : ℕ) : ℝ) * ((2 : ℝ) ^ lamStar)⁻¹ ≤
        ((2 * ell + 2 : ℕ) : ℝ) * ((2 : ℝ) ^ lamStar)⁻¹ := by
      have h : ((2 * ell + 1 : ℕ) : ℝ) ≤ ((2 * ell + 2 : ℕ) : ℝ) := by
        push_cast
        linarith
      exact mul_le_mul_of_nonneg_right h hX
    have hY : (0 : ℝ) ≤ ((2 : ℝ) ^ (lam + 1))⁻¹ := by positivity
    rw [hellY]
    linarith
/-- **The union bound of 6.5**, from **one** named per-child hypothesis.

`Bad` is the composite failure event.  The hypothesis is exactly the paper's: `ℓ` child calls, each
failing with probability at most `2^{-λ-1}/ℓ` (Theorem 5.1's conjunct 8 at the child's parameters,
with `λ` the *composite's* error exponent — which is why this layer, and not 5.1's, can afford
`2^{-λ-1}/ℓ`), plus `2ℓ+1` events of probability at most `2^{-λ_*}` (the initial budget and the
residual repair).  Conclusion: `Pr[Bad] ≤ 2^{-λ} ≤ ε`. -/
theorem failure_bound_of_child_bounds {β : Type} [Fintype β] [Nonempty β]
    {ell lam lamStar : ℕ} {eps : ℝ}
    (hlam : lam = ⌈lg (1 / eps)⌉₊) (heps : 0 < eps)
    (harith : ((2 * ell + 2 : ℕ) : ℝ) * ((2 : ℝ) ^ lamStar)⁻¹ ≤ ((2 : ℝ) ^ (lam + 1))⁻¹)
    (Bad : β → Prop) (Child : Fin ell → β → Prop) (Init : Fin (2 * ell + 1) → β → Prop)
    (hChild : ∀ s, prU (Child s) ≤ ((2 : ℝ) ^ (lam + 1))⁻¹ / (ell : ℝ))
    (hInit : ∀ i, prU (Init i) ≤ ((2 : ℝ) ^ lamStar)⁻¹)
    (hcover : ∀ b, Bad b → (∃ i, Init i b) ∨ ∃ s, Child s b) :
    prU Bad ≤ eps := by
  set A1 : β → Prop := fun b => ∃ i, Init i b with hA1
  set A2 : β → Prop := fun b => ∃ s, Child s b with hA2
  have hm : prU Bad ≤ prU (fun b => A1 b ∨ A2 b) := by
    refine prU_mono ?_
    intro b hb
    rcases hcover b hb with h | h
    · exact Or.inl h
    · exact Or.inr h
  have hor : prU (fun b => A1 b ∨ A2 b) ≤ prU A1 + prU A2 := prU_or_le A1 A2
  have hun1 : prU A1 ≤ ∑ _i : Fin (2 * ell + 1), ((2 : ℝ) ^ lamStar)⁻¹ := by
    refine le_trans (prU_exists_le_sum Init) ?_
    exact Finset.sum_le_sum fun i _ => hInit i
  have hun2 : prU A2 ≤ ∑ _s : Fin ell, (((2 : ℝ) ^ (lam + 1))⁻¹ / (ell : ℝ)) := by
    refine le_trans (prU_exists_le_sum Child) ?_
    exact Finset.sum_le_sum fun s _ => hChild s
  have hs1 : (∑ _i : Fin (2 * ell + 1), ((2 : ℝ) ^ lamStar)⁻¹) =
      ((2 * ell + 1 : ℕ) : ℝ) * ((2 : ℝ) ^ lamStar)⁻¹ := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hs2 : (∑ _s : Fin ell, (((2 : ℝ) ^ (lam + 1))⁻¹ / (ell : ℝ))) =
      (ell : ℝ) * (((2 : ℝ) ^ (lam + 1))⁻¹ / (ell : ℝ)) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hfin : prU Bad ≤ ((2 : ℝ) ^ lam)⁻¹ := by
    have h := failure_arith harith
    linarith
  have hstep : ((2 : ℝ) ^ lam)⁻¹ ≤ eps := by
    rw [hlam]
    exact two_pow_inv_ceil_lg_le heps
  linarith
/-- The same bound in the form Theorem 6.5 states it: `1 - ε ≤ Pr[recovery succeeds]`. -/
theorem recovery_bound_of_child_bounds {β : Type} [Fintype β] [Nonempty β]
    {ell lam lamStar : ℕ} {eps : ℝ}
    (hlam : lam = ⌈lg (1 / eps)⌉₊) (heps : 0 < eps)
    (harith : ((2 * ell + 2 : ℕ) : ℝ) * ((2 : ℝ) ^ lamStar)⁻¹ ≤ ((2 : ℝ) ^ (lam + 1))⁻¹)
    (Good : β → Prop) (Child : Fin ell → β → Prop) (Init : Fin (2 * ell + 1) → β → Prop)
    (hChild : ∀ s, prU (Child s) ≤ ((2 : ℝ) ^ (lam + 1))⁻¹ / (ell : ℝ))
    (hInit : ∀ i, prU (Init i) ≤ ((2 : ℝ) ^ lamStar)⁻¹)
    (hcover : ∀ b, ¬ Good b → (∃ i, Init i b) ∨ ∃ s, Child s b) :
    1 - eps ≤ prU Good := by
  have hbad := failure_bound_of_child_bounds hlam heps harith (fun b => ¬ Good b) Child Init
    hChild hInit hcover
  rw [prU_compl Good] at hbad
  linarith
/-- **The two deterministic regimes** (`6toplevel.tex` 285, 311–317: `d ≥ n/2` direct storage, and
the small-instance mode): there recovery succeeds for *every* seed, so its probability is `1` and
6.5's `1 - ε` bound is trivial.  The length sides of these two regimes are `direct_storage_le` (§7)
and `small_instance_le` (§8); this is the probability side. -/
theorem recovery_bound_of_forall {β : Type} [Fintype β] [Nonempty β]
    (Good : β → Prop) (h : ∀ b, Good b) {eps : ℝ} (heps : 0 ≤ eps) :
    1 - eps ≤ prU Good := by
  have hcard : (0 : ℝ) < (Fintype.card β : ℝ) := by
    have h0 : 0 < Fintype.card β := Fintype.card_pos
    exact_mod_cast h0
  have h1 : prU Good = 1 := by
    rw [prU_eq_card Good]
    have h2 : (univ.filter Good).card = Fintype.card β := by
      rw [Finset.filter_true_of_mem (fun a _ => h a), Finset.card_univ]
    rw [h2, div_self (ne_of_gt hcard)]
  rw [h1]
  linarith

/-! ### 11.6 Theorem 5.1 supplies the per-child hypotheses

The three conjuncts of §11.3 are not extra assumptions about 5.1: at the child's parameters
(`N := d`, `X := Y := d`) 5.1's own conjuncts 6–8 *are* these three predicates with the same
`progUp`/`progDec` — 5.1 quantifies both before its `∀ n lam N X Y`.  The failure conjunct's
`prU (…) ≤ 2^{-λ}` is turned into `1 - 2^{-λ} ≤ prU (…)` by `prU_compl`. -/
/-- The deterministic table of the composite: block `s` of `2^W` addresses holds child `s`'s table,
the block at index `ℓ` holds the final `CR` table, every other address returns `0`. -/
def compDet {ℓ : ℕ} (W : ℕ) (dt : Fin ℓ → ℕ → ℕ) (dcr : ℕ → ℕ) : ℕ → ℕ :=
  fun a =>
    if h : a / 2 ^ W < ℓ then dt ⟨a / 2 ^ W, h⟩ (a % 2 ^ W)
    else if a / 2 ^ W = ℓ then dcr (a % 2 ^ W) else 0
/-- §10's `det` is `compDet` with the children's own tables: the layout below is *verbatim* the one
`composite_sketch` already carries, so the composite object needs no change. -/
theorem compDet_eq_composite {ℓ W : ℕ} (dt : Fin ℓ → ℕ → ℕ) (dcr : ℕ → ℕ) :
    compDet W dt dcr
      = fun a => if h : a / 2 ^ W < ℓ then dt ⟨a / 2 ^ W, h⟩ (a % 2 ^ W)
          else if a / 2 ^ W = ℓ then dcr (a % 2 ^ W) else 0 := rfl
/-- Inside child `s`'s block the composite `det` is child `s`'s table. -/
theorem compDet_child {ℓ W : ℕ} (dt : Fin ℓ → ℕ → ℕ) (dcr : ℕ → ℕ) {a : ℕ}
    (h : a / 2 ^ W < ℓ) :
    compDet W dt dcr a = dt ⟨a / 2 ^ W, h⟩ (a % 2 ^ W) := by
  unfold compDet
  rw [dif_pos h]
/-- Inside the `CR` block the composite `det` is the `CR` table. -/
theorem compDet_cr {ℓ W : ℕ} (dt : Fin ℓ → ℕ → ℕ) (dcr : ℕ → ℕ) {a : ℕ}
    (h : a / 2 ^ W = ℓ) : compDet W dt dcr a = dcr (a % 2 ^ W) := by
  unfold compDet
  rw [dif_neg (by rw [h]; omega), if_pos h]
/-- Outside every block the composite `det` is `0`. -/
theorem compDet_junk {ℓ W : ℕ} (dt : Fin ℓ → ℕ → ℕ) (dcr : ℕ → ℕ) {a : ℕ}
    (h : ℓ < a / 2 ^ W) : compDet W dt dcr a = 0 := by
  unfold compDet
  rw [dif_neg (by omega), if_neg (by omega)]
/-- `(i·W + u) / W = i` for `u < W`: the quotient *is* the block index. -/
theorem nat_div_mul_add (W : ℕ) (hW : 0 < W) (i u : ℕ) (hu : u < W) :
    (i * W + u) / W = i := by
  refine Nat.div_eq_of_lt_le (Nat.le_add_right _ _) ?_
  have h : (i + 1) * W = i * W + W := by ring
  omega
/-- `(i·W + u) % W = u` for `u < W`: the remainder *is* the block offset. -/
theorem nat_mod_mul_add (W : ℕ) (i u : ℕ) (hu : u < W) : (i * W + u) % W = u := by
  have h : (i * W + u) % W = (u + W * i) % W := by rw [Nat.mul_comm i W, Nat.add_comm]
  rw [h, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hu]
/-- The block index of the address of offset `u` in block `i`. -/
theorem compDet_block_index (W i u : ℕ) (hu : u < 2 ^ W) :
    (i * 2 ^ W + u) / 2 ^ W = i :=
  nat_div_mul_add (2 ^ W) (Nat.two_pow_pos W) i u hu
/-- The block offset of the address of offset `u` in block `i`. -/
theorem compDet_block_offset (W i u : ℕ) (hu : u < 2 ^ W) :
    (i * 2 ^ W + u) % 2 ^ W = u :=
  nat_mod_mul_add (2 ^ W) i u hu
/-- **The children's address ranges are pairwise disjoint.**  Two addresses `i·2^W + u`,
`j·2^W + v` with `u, v < 2^W` coincide only if `i = j` and `u = v`. -/
theorem compDet_range_disjoint {W : ℕ} {i j u v : ℕ} (hij : i ≠ j)
    (hu : u < 2 ^ W) (hv : v < 2 ^ W) : i * 2 ^ W + u ≠ j * 2 ^ W + v := by
  intro he
  apply hij
  rw [← compDet_block_index W i u hu,
    ← compDet_block_index W j v hv, he]
/-- **A `det` address lands in exactly one block**: for `a < (ℓ+1)·2^W` there is exactly one pair
`(block, offset)` with `offset < 2^W` and `a = block·2^W + offset`. -/
theorem compDet_route_unique {ℓ W : ℕ} (hW : 0 < W) {a : ℕ} (ha : a < (ℓ + 1) * 2 ^ W) :
    ∃! p : ℕ × ℕ, p.1 ≤ ℓ ∧ p.2 < 2 ^ W ∧ a = p.1 * 2 ^ W + p.2 := by
  have h2 : 0 < 2 ^ W := Nat.two_pow_pos W
  have h1 : a / 2 ^ W < ℓ + 1 := by
    rw [Nat.div_lt_iff_lt_mul h2]
    exact ha
  have h3 : a = (a / 2 ^ W) * 2 ^ W + a % 2 ^ W := by
    rw [Nat.mul_comm (a / 2 ^ W) (2 ^ W), Nat.div_add_mod]
  refine ⟨⟨a / 2 ^ W, a % 2 ^ W⟩, ⟨by omega, Nat.mod_lt _ h2, h3⟩, ?_⟩
  rintro ⟨i, u⟩ ⟨_hi, hu, he⟩
  have h4 : a / 2 ^ W = i := by rw [he]; exact compDet_block_index W i u hu
  have h5 : a % 2 ^ W = u := by rw [he]; exact compDet_block_offset W i u hu
  exact Prod.ext h4.symm h5.symm
/-- **Every register value stays inside one word.**  `step` writes only values reduced with
`% 2^E.W` (arithmetic, `imm`, `load`, `qDet`, `qPerm`, `qCoeff`), so `qDet` is always queried at an
address `< 2^W`: this is what makes the `2^W`-wide blocks of `compDet` sufficient. -/
theorem step_regs_lt (P : Program) (E : RAMEnv) (s : RAMState)
    (h : ∀ k, s.regs k < 2 ^ E.W) : ∀ k, (step P E s).regs k < 2 ^ E.W := by
  intro k
  cases hpc : P[s.pc]? with
  | none => simpa [step, hpc] using h k
  | some instr =>
      cases instr <;>
        simp only [step, hpc] <;>
        first
          | exact h k
          | (simp only [Function.update_apply]
             split
             · exact Nat.mod_lt _ (Nat.two_pow_pos E.W)
             · exact h k)

/-! ### 11.2 The `compAsm` block algebra

`compAsm W hW f R v u : Fin (W * blkTotal W f + R) → ZMod 2` is §10.3's assembly: block `s` owns
the words `[blkOff W f s, blkOff W f (s+1))`, i.e. the bits `[W · blkOff W f s, W · blkOff W f (s+1))`,
and the `R` coordinates of the `CR` block follow at bit `W · blkTotal W f`.  Unlike the earlier
`Fintype.equivFin` order (`compSigEquivS`), every one of these numbers is *stated*, so "which word a
block occupies" is now a theorem.  The lemmas below pin down the `hpt` step inside `sum_compAsm`, and
they are what turns "the composite `H` entry" into "the child `H` entry". -/
/-- The composite entry at a child coordinate *is* the child entry at the corresponding local bit. -/
theorem compAsm_blk {L : ℕ} (W : ℕ) (hW : 0 < W) (f : Fin L → ℕ) (R : ℕ)
    (v : (s : Fin L) → Fin (f s) → ZMod 2) (u : Fin R → ZMod 2) (s : Fin L) (k : Fin (f s)) :
    compAsm W hW f R v u ⟨W * blkOff W f s.val + k.val, by
        have := blkEmb_lt_total W hW f s k
        omega⟩ = v s k :=
  compAsmV_blk W hW f R v u s k
/-- The composite entry at a `CR` coordinate *is* the `CR` entry. -/
theorem compAsm_natAdd {L : ℕ} (W : ℕ) (hW : 0 < W) (f : Fin L → ℕ) (R : ℕ)
    (v : (s : Fin L) → Fin (f s) → ZMod 2) (u : Fin R → ZMod 2) (q : Fin R) :
    compAsm W hW f R v u (Fin.natAdd (W * blkTotal W f) q) = u q :=
  compAsmV_cr W hW f R v u q
/-- **Block `s` is `W`-aligned and starts at the word `blkOff W f s`**: its `f s` payload bits live
strictly inside the words `blkOff W f s, …, blkOff W f (s+1) - 1`. -/
theorem compAsm_block_start {L : ℕ} (W : ℕ) (hW : 0 < W) (f : Fin L → ℕ) (s : Fin L) :
    W * blkOff W f s.val + f s ≤ W * blkOff W f (s.val + 1) := by
  have h := le_mul_wordsOf W hW (f s)
  rw [blkOff_succ f s, Nat.mul_add]
  exact Nat.add_le_add_left h _
/-- The padding bits of a block (`f s ≤ local bit`) read `0`. -/
theorem compAsm_pad {L : ℕ} (W : ℕ) (hW : 0 < W) (f : Fin L → ℕ) (R : ℕ)
    (v : (s : Fin L) → Fin (f s) → ZMod 2) (u : Fin R → ZMod 2)
    {q : Fin (W * blkTotal W f + R)} (hq : q.val < W * blkTotal W f)
    (hk : f (compBlk W hW f q.val hq) ≤ compBit W hW f q.val hq) :
    compAsm W hW f R v u q = 0 :=
  compAsmV_of_pad W hW f R v u hq hk
/-- **Block `s` has exactly `f s` payload coordinates**, namely the image of `k ↦ W · blkOff s + k`. -/
theorem compAsm_block_card {L : ℕ} (W : ℕ) (hW : 0 < W) (f : Fin L → ℕ) (s : Fin L) :
    ((Finset.univ : Finset (Fin (f s))).image (fun k => W * blkOff W f s.val + k.val)).card = f s := by
  have hinj : ∀ a ∈ (Finset.univ : Finset (Fin (f s))), ∀ b ∈ Finset.univ,
      W * blkOff W f s.val + a.val = W * blkOff W f s.val + b.val → a = b := by
    intro a _ b _ hab
    exact Fin.ext (by omega)
  rw [Finset.card_image_of_injOn hinj, Finset.card_univ, Fintype.card_fin]
/-- The children's coordinate blocks are pairwise disjoint (`blkOff_emb_inj`, §10.3). -/
theorem compAsm_blocks_disjoint {L : ℕ} (W : ℕ) (hW : 0 < W) (f : Fin L → ℕ) {s t : Fin L}
    (hst : s ≠ t) :
    Disjoint ((Finset.univ : Finset (Fin (f s))).image (fun k => W * blkOff W f s.val + k.val))
      ((Finset.univ : Finset (Fin (f t))).image (fun k => W * blkOff W f t.val + k.val)) := by
  rw [Finset.disjoint_left]
  intro q hq hq'
  simp only [Finset.mem_image, Finset.mem_univ, true_and] at hq hq'
  obtain ⟨k, rfl⟩ := hq
  obtain ⟨k', hk'⟩ := hq'
  exact hst (blkOff_emb_inj W hW f hk'.symm)

/-! ### 11.3 The packed payload: word alignment is the whole point

`TogglesWithin`'s postcondition is an equality of *words*: `s'.mem addr = packMem E.W z addr`.
`packMem` sums the bits of `z` that fall in word `addr` (`Def…WordRAM.packMem`).  For the old
`Fintype.equivFin` order the assembly needed an additive split of `packMem` over the blocks, because a
block's bits straddled two words and no closed form existed.  With the word-aligned layout of §10.3
that split is no longer needed: block `s` owns exactly the words `blkOff W f s + ·`
(`compAsm_block_start`, `compAsm_blk`, `compAsm_pad`), so word `blkOff W f s + a` of the composite is
word `a` of the child.  That is `packMem_blk` below, stated for a *single* block, and it is exactly
what the child program's own `packMem` has to match. -/
/-- **One block's contribution to a packed word is the block's own packed word — provided the block
starts at a multiple of `W`.**  If the block's coordinates are `t·W, t·W+1, …` (`hval`), the block
carries the values of `v` (`hemb`) and everything outside the block is `0` (`hzero`), then word
`t + a` of the composite is word `a` of the block.

Word alignment is *not* cosmetic: without it bit `j` of the block sits in word
`(off + j) / W` at position `(off + j) % W`, and no child program that packs its own vector from
word `0` (i.e. every `TogglesWithin`) can write it.  This is the constraint recorded in §11.5. -/
theorem packMem_blk (W : ℕ) (hW : 0 < W) {M Ms : ℕ} (z : Fin M → ZMod 2)
    (v : Fin Ms → ZMod 2) (emb : Fin Ms → Fin M) (t : ℕ)
    (hval : ∀ j, (emb j).val = t * W + j.val) (hemb : ∀ j, z (emb j) = v j)
    (hzero : ∀ q : Fin M, (∀ j, emb j ≠ q) → z q = 0) (a : ℕ) :
    packMem W z (t + a) = packMem W v a := by
  have hinj : Function.Injective emb := by
    intro j j' h
    have hv : t * W + j.val = t * W + j'.val := by rw [← hval j, ← hval j', h]
    exact Fin.ext (by omega)
  have hdiv : ∀ j : Fin Ms, (emb j).val / W = t + j.val / W := by
    intro j
    rw [hval j, Nat.mul_comm t W, Nat.add_comm, Nat.add_mul_div_left _ _ hW]
    omega
  have hmod : ∀ j : Fin Ms, (emb j).val % W = j.val % W := by
    intro j
    rw [hval j, Nat.mul_comm t W, Nat.add_comm, Nat.add_mul_mod_self_left]
  rw [packMem, packMem]
  have hsub : ((Finset.univ : Finset (Fin Ms)).image emb).sum
        (fun q : Fin M => (if q.val / W = t + a ∧ z q = 1 then 2 ^ (q.val % W) else 0))
      = ∑ q : Fin M, (if q.val / W = t + a ∧ z q = 1 then 2 ^ (q.val % W) else 0) := by
    refine Finset.sum_subset (Finset.subset_univ _) ?_
    intro q _ hq
    have hz : z q = 0 :=
      hzero q (fun j hj => hq (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, hj⟩))
    rw [if_neg]
    rintro ⟨-, h1⟩
    rw [hz] at h1
    exact zero_ne_one h1
  rw [← hsub, Finset.sum_image (fun x _ y _ h => hinj h)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hdiv j, hmod j, hemb j]
  by_cases hc : j.val / W = a ∧ v j = 1
  · rw [if_pos ⟨by omega, hc.2⟩, if_pos hc]
  · rw [if_neg (by rintro ⟨h1, h2⟩; exact hc ⟨by omega, h2⟩), if_neg hc]

/-! ### 11.4 A `halt` cannot be followed: why the child programs are not spliced

`Program` is a flat `List Instr` with *absolute* jump targets, and `TogglesWithin P E H T` forces `P`
to contain a `halt` (`togglesWithin_exists_halt`); the machine stops at a `halt`
(`step_halt_self`).  Hence a composite `List Instr` that contains a copy of an *opaque* child program
is frozen at that copy's `halt` (`append_halt_frozen`): the later copies are dead code, and
relocating the copy is unavailable because `TogglesWithin` reveals neither the halt's position nor
the jump targets.  This is §9.3 (a) in machine-checked form; the fix is the `Stmt`/`Sem` interface
of §11.5. -/
/-- A `halt` is a fixed point of `step`. -/
theorem step_halt_self {P : Program} {E : RAMEnv} {s : RAMState} (h : P[s.pc]? = some .halt) :
    step P E s = s := by
  simp [step, h]
/-- A run that reaches a `halt` never moves again. -/
theorem step_iterate_halt {P : Program} {E : RAMEnv} {s : RAMState}
    (h : P[s.pc]? = some .halt) (k : ℕ) : (step P E)^[k] s = s := by
  induction k with
  | zero => rfl
  | succ k ih =>
      show (step P E)^[k + 1] s = s
      rw [Function.iterate_succ_apply, step_halt_self h, ih]
/-- From a halted state, `HaltsWithin` returns that same state: nothing can run after a `halt`. -/
theorem haltsWithin_eq_of_halt {P : Program} {E : RAMEnv} {T : ℝ} {s s' : RAMState}
    (h : HaltsWithin P E T s s') (hh : P[s.pc]? = some .halt) : s' = s := by
  obtain ⟨k, -, hk, -⟩ := h
  rw [step_iterate_halt hh k] at hk
  exact hk.symm
/-- **A copied child program freezes the composite at its `halt`.**  In the concatenation
`pre ++ (P ++ post)`, a run that reaches the copy's halt address `pre.length + b` is frozen there,
so `post` — in particular a second copy of `P` — never executes. -/
theorem append_halt_frozen {pre P post : Program} {E : RAMEnv} {s : RAMState} {b : ℕ}
    (hb : b < P.length) (hh : P[b]? = some .halt) (k : ℕ) :
    (step (pre ++ (P ++ post)) E)^[k] { s with pc := pre.length + b }
      = { s with pc := pre.length + b } := by
  refine step_iterate_halt ?_ k
  show (pre ++ (P ++ post))[pre.length + b]? = some .halt
  have h1 : (pre ++ (P ++ post))[pre.length + b]? = (P ++ post)[b]? := by
    rw [List.getElem?_append_right (by omega : pre.length ≤ pre.length + b)]
    rw [show pre.length + b - pre.length = b from by omega]
  rw [h1, List.getElem?_append_left hb]
  exact hh
/-- Every `TogglesWithin` program contains a `halt` (as soon as there is a payload bit to toggle). -/
theorem togglesWithin_exists_halt {P : Program} {E : RAMEnv} {n M : ℕ}
    {H : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin M → ZMod 2)} {T : ℝ}
    (h : TogglesWithin P E H T) (y : Fin M → ZMod 2) (i : Fin n) :
    ∃ pc : ℕ, P[pc]? = some .halt := by
  obtain ⟨s', hs', -⟩ := h y i
  obtain ⟨k, -, -, hhalt⟩ := hs'
  cases hpc : P[s'.pc]? with
  | none => simp [Halted, hpc] at hhalt
  | some instr =>
      cases instr <;> (first | exact ⟨s'.pc, hpc⟩ | simp [Halted, hpc] at hhalt)
/-- **The per-child toggle contract**, in the form the `ℓ`-fold composition needs, stated for the
relocatable block `Sup` at offset `0`.

`β` is the word base of the child's payload; by §10.3 it is the *closed form* `blkOff W f s.val`
(block `s` starts at that word, `compAsm_block_start`), while `compDet` puts child `s`'s table at the
`2^W` addresses `[s·2^W, (s+1)·2^W)`, so the `det` base is `s·2^W`.  Both are now statable, and the
payload range `[β, β + wordsOf E.W Ms)` is disjoint from its neighbours' because the blocks own
disjoint *word* ranges.  The contract is *width-generic* (`E.W` is the composite width, the child's
own `W_s ≤ E.W` never appears, and `packMem` is taken at `E.W`) and *framed* (last conjunct); those
two properties are precisely what `TogglesWithin` does not provide, and they are what makes `ℓ`
copies chainable.

The offset `0` is not a restriction: `Stmt.compile` is the relocation, but the bridge
"`step (Sup.compile a)` from `pc = a` is `step (Sup.compile 0)` from `pc = 0` with pc shifted by `a`"
is a lemma that does not exist yet (§11.5). -/
def UpBlockSpec (Sup : Stmt) (E : RAMEnv) (T : ℝ) {N Ms : ℕ}
    (Hs : (Fin N → ZMod 2) →ₗ[ZMod 2] (Fin Ms → ZMod 2)) : Prop :=
  ∀ (β : ℕ) (y : Fin Ms → ZMod 2) (i : Fin N) (s : RAMState),
    s.pc = 0 → s.regs 15 = β → s.regs 0 = i.val →
    (∀ j < wordsOf E.W Ms, s.mem (β + j) = packMem E.W y j) →
    ∃ (k : ℕ) (s' : RAMState), (k : ℝ) ≤ T ∧ (step (Sup.compile 0) E)^[k] s = s' ∧
      s'.regs 15 = β ∧ s'.regs 0 = s.regs 0 ∧
      (∀ j < wordsOf E.W Ms, s'.mem (β + j) = packMem E.W (y + Hs (Pi.single i 1)) j) ∧
      (∀ c, c ∉ Finset.range (wordsOf E.W Ms) → s'.mem (β + c) = s.mem (β + c))
/-- **The per-child hypothesis of 6.5's `TogglesWithin` conjunct**: one block `Sup`, one contract,
uniform over the children's own `H_s`. -/
def UpChildHyp {ι : Type} (Sup : Stmt) (E : RAMEnv) (T : ℝ) {N : ℕ} (Ms : ι → ℕ)
    (Hs : (p : ι) → (Fin N → ZMod 2) →ₗ[ZMod 2] (Fin (Ms p) → ZMod 2)) : Prop :=
  ∀ p : ι, UpBlockSpec Sup E T (Hs p)/-! ### 11.5 What the per-child hypothesis has to be

The file now defines (`§11.2` of the `-- TODO(machine)` section) a `Stmt` as a *relocatable* block,
`Stmt.compile : Stmt → ℕ → Program`.  That removes the first of the two structural obstructions: the
`ℓ` copies of a child block are `Sup.compile (i · Sup.body.length)` and their absolute targets are
computed by `compile`, so no relocation of an opaque `Program` is needed.

Two things are still missing, and they are *not* in this file:

* **`Stmt` has no `Sem`.** `Stmt` here is `{ body, jmp_lt, jz_lt }`; composition needs the run
  relation `Sem P E a b s Q`, its rules `Sem.block`, `Sem.seq`, `Sem.loop` and the bridge
  `halts_of_run` to `HaltsWithin`.  Those exist — in 5.1's *solution* tree
  (`_51_up_dev.lean` §8–9), which 6.5 may not import.  They must be published in an importable
  `Definitions` module, for the same reason as `Stmt`: 5.1's export has to produce a term of the very
  same `Sem` type.  Copying them into 6.5 would make the two `Stmt`s/`Sem`s *different* types and the
  hypothesis undischargeable.
* **`compile` is not yet proved to relocate.** `At (S.compile a) a S.body` and
  "`Sem (S.compile a) E a b s Q ↔ Sem (S.compile 0) E 0 (b-a) s Q`" are the two lemmas composition
  needs; both are routine inductions on `body` with the `jmp_lt`/`jz_lt` side conditions, but neither
  exists yet.

Even with both, the child contract must be **relative in three addresses** that `TogglesWithin` fixes
to `0`:

1. **`det` base.**  `Sem P E a b s Q` fixes one environment `E` for the whole run, so the `ℓ`
   iterations cannot each see a different `det`.  A copy of the child block can only be redirected to
   block `s` of `compDet` if its `qDet` addresses are `β + ·` for a base `β` held in a register that
   the composite sets to `s·2^W`.  The contract must be uniform in `β` and must bound the addresses
   (`< β + 2^W`); `compDet_child` + `compDet_range_disjoint` then say "this child sees its own table".
2. **payload word base.**  `TogglesWithin` puts the payload at words `0 … wordsOf-1` and returns a
   *whole-word* equality, so a child sharing a word with a neighbour zeroes the neighbour's bits.
   The children must own disjoint **word** ranges, and the contract must state
   `s'.mem (β + i) = packMem W … i` plus a frame `∀ a ∉ [β, β + words), s'.mem a = s.mem a`.
3. **word width.**  Child `s` is built at width `W_s ≤ Wmax < W = Wmax + ⌈log₂((ℓ+1)2^{Wmax}+2)⌉`,
   while the composite packs at width `W`.  `packMem` is width-dependent, so the contract must be
   stated at a caller-chosen `W ≥ W_s` (`packMem W`, `wordsOf W M_s`), not at `W_s`.

And one constraint on the composite itself (finding 4, forced by `packMem_blk`): **the blocks must be
word-aligned**, i.e. `M_s` padded to a multiple of `W`, because a child program packs its own vector
from word `0`.

**Finding 4 is closed in §10.3.**  `compAsm` now uses the explicit prefix-sum order of the child
index `Fin L` — block `s` occupies the words `[blkOff W f s, blkOff W f (s+1))` with
`blkOff W f s = Σ_{t<s} ⌈f t / W⌉` — and the payload is

> `M' = W · Σ_s ⌈M_s / W⌉ + R_CR`,  hence  `M' − Σ_s M_s ≤ ℓ (W − 1)`.

The length conjunct of §6 pays that `Δ`: `composite_sketch` keeps `Cl` for the `d`-part (which is
tight), adds the slack `ℓ(W−1) ≤ 9(4C'+1)cW · log³ n`, and concludes with the **same shape**

> `M' ≤ L(n,d) + Cl' d + Cl' λ log^{pl'} n`,  `Cl' = Cl + 9(4C'+1)cW`,  `pl' = max (p₁+2) 3`,

both of which are existentially quantified in `composite_sketch` / `theorem_6_5_statement`, so the
platform statement is unchanged.  `wordsOf W M' ≤ 2^W` is re-proved from `⌈W·T/W⌉ = T` and
`(ℓ+1)·2^{W_max} ≤ 2^W` (which is `2^kk ≥ (ℓ+1)2^{W_max} + 2`).

The exact shape assumed (one `Sup` for every child, `β` the `det`/payload word base, `W` the
composite width, `r15` the base register):

```lean
∃ Sup : Stmt, Sup.compile 0 ++ [Instr.halt] = progUp51 ∧
  ∀ (r : childSpec.Seed) (W β : ℕ) (y : Fin M_s → ZMod 2) (i : Fin N) (a : ℕ) (s : RAMState),
    W_s ≤ W → s.pc = a → s.regs 15 = β → s.regs 0 = i.val →
    (∀ j < wordsOf W M_s, s.mem (β + j) = packMem W y j) →
    Sem (Sup.compile a) (spec.env W_s det_s r) a (a + Sup.body.length) s
      (fun k s' => (k : ℝ) ≤ Cu * lg N ^ pu ∧ s'.regs 15 = β ∧
        (∀ j < wordsOf W M_s, s'.mem (β + j) = packMem W (y + H_s (Pi.single i 1)) j) ∧
        (∀ c, c ∉ Finset.range (wordsOf W M_s) → s'.mem (β + c) = s.mem (β + c)))
```

Given that, the composite `progUp` is `Stmt.compile`-chained copies of `Sup` at the word-aligned
blocks `blkOff W f s`, followed by the `CR` toggle, and the *entire* composition proof is
`compDet_range_disjoint` (the `det` blocks), `compAsm_block_start` + `compAsm_blocks_disjoint` (the
payload word ranges are disjoint and `W`-aligned), `compAsm_blk` (composite entry = child entry),
`compAsm_natAdd` (the `CR` block) and `packMem_blk` (the word stitching). -/

/-! ## 12. The composite programmes, and what their conjuncts need

§11 built the address algebra of the composite (`compDet`, `compAsm`, `packMem_blk`) and recorded
the per-child toggle contract `UpBlockSpec`.  This section does three things:

* **12.1** defines the composite programmes as `Stmt`s: `compUpStmt` is one `Stmt.loop` that runs a
  copy of the child block `Sup` per block; `compDecStmt` is one `Stmt.loop` that runs a copy of the
  child decoder `Sdec` per child.  Both satisfy the tying equation
  `∃ Sup', Sup'.compile 0 ++ [halt] = prog` *by construction* (`rfl`), which is the hypothesis
  `theorem_6_5_of_composite` consumes.
* **12.2** proves the toggle conjunct for **one** block from the halting form `UpBlockHalts` of the
  contract, and shows `UpBlockHalts → UpBlockSpec`: the given `UpBlockSpec` is one conjunct short of
  what `TogglesWithin` needs, namely that the block *reaches its end* (so that the appended `halt`
  fires).  §12.4 states precisely the two further clauses the multi-block dispatcher needs.
* **12.3** proves the uniform-marginal lemma for product seeds (`prU_pi_proj`): `5.1`'s `prU` is over
  the child's `spec.Seed`, the composite's over `TableSpec.Seed`, and `compChildSeed` is a
  projection of a product, so the two probabilities agree.  This is what turns `5.1`'s per-child
  failure bound into `hFail`'s hypothesis.
-/

open Classical

/-! ### 12.1 The composite programmes -/
/-- The loop test shared by the two dispatchers: they run while the block counter `r1` is below the
block count `r2`. -/
def blkCond : Cond := .lt r7 r1 r2
/-- The per-block increment shared by the two dispatchers. -/
def blkInc : List Instr := [iImm r7 1, iAdd r1 r1 r7]
/-- The composite toggle programme: one `Stmt.loop` over the block index, running one copy of the
child block `Sup` per block.  The loop state is entirely in registers: `r1` is the current block,
`r2` the block count `ℓ`, `r3` the `det` block size `2 ^ Wdet`, `r4` the address in `det` at which
the payload word bases are stored, `r0` the toggled coordinate.  They are preloaded by the caller,
so the programme itself is **parameter-free** — one `progUp` for every `(n, d, λ)`, as
`theorem_6_5_statement`'s `∃ progUp` requires.  Block `s` runs with `det` base `s · 2 ^ Wdet`
(register 14) and payload word base read from `det` at `r4 + s` (register 15). -/
def compUpStmt (Sup : Stmt) : Stmt :=
  .loop blkCond
    (.seq (.code [iMul r14 r1 r3, iAdd r7 r4 r1, iTbl r15 r7])
      (.seq Sup (.code blkInc)))
/-- The composite toggle programme, as the flat `Program` of Theorem 6.5. -/
def progUpOf (Sup : Stmt) : Program :=
  (compUpStmt Sup).compile 0 ++ [Instr.halt]
/-- **The tying equation for the toggle side**, by construction. -/
theorem progUpOf_eq (Sup : Stmt) :
    ∃ Sup' : Stmt, Sup'.compile 0 ++ [Instr.halt] = progUpOf Sup :=
  ⟨compUpStmt Sup, rfl⟩
/-- The loop test of the child-decoder dispatcher. -/
def decCond : Cond := blkCond
/-- The per-block increment of the decoder dispatcher. -/
def decInc : List Instr := blkInc
/-- The composite decoder: the `ℓ` child decoders are one `Stmt.loop` over the block index, whose
running bound `ℓ` is read from register `r2` at run time — so this is **one** programme for every
`ℓ`, as Theorem 6.5's `∃ progDec` requires.  The row decode, the prefix assembly and the `CR`
recovery are further blocks around this loop. -/
def compDecStmt (Sdec : Stmt) : Stmt :=
  .loop decCond (.seq Sdec (.code decInc))
/-- The composite decoder, as the flat `Program` of Theorem 6.5. -/
def progDecOf (Sdec : Stmt) : Program :=
  (compDecStmt Sdec).compile 0 ++ [Instr.halt]
/-- **The tying equation for the decoder side**, by construction. -/
theorem progDecOf_eq (Sdec : Stmt) :
    ∃ Sdec' : Stmt, Sdec'.compile 0 ++ [Instr.halt] = progDecOf Sdec :=
  ⟨compDecStmt Sdec, rfl⟩
/-- **The full composite toggle programme**: the `ℓ` child blocks, then the `CR` toggle block.
`progUpOf` is the part the per-block contracts of §11 describe; `Scr` is the final `CR` block, whose
contract has the same shape (its `H` is `Hcr`, its base is the word `W · blkTotal`). -/
def compUpStmtFull (Sup Scr : Stmt) : Stmt :=
  .seq (compUpStmt Sup) Scr
/-- The full composite toggle programme, as the flat `Program` of Theorem 6.5. -/
def progUpOfFull (Sup Scr : Stmt) : Program :=
  (compUpStmtFull Sup Scr).compile 0 ++ [Instr.halt]
/-- **The tying equation for the full toggle programme**, by construction. -/
theorem progUpOfFull_eq (Sup Scr : Stmt) :
    ∃ Sup' : Stmt, Sup'.compile 0 ++ [Instr.halt] = progUpOfFull Sup Scr :=
  ⟨compUpStmtFull Sup Scr, rfl⟩
/-- **The full composite decoder**: row decode (`Srow`), the `ℓ` child decoders, the prefix
assembly (`Sassem`), the residual syndrome (`Sres`) and the `CR` recovery (`Scr`).  Only the child
loop interacts with Theorem 5.1's export; the other four blocks are the `Stmt` form of the
deterministic sketches of §2.2/§2.3. -/
def compDecStmtFull (Srow Sdec Sassem Sres Scr : Stmt) : Stmt :=
  .seq Srow (.seq (compDecStmt Sdec) (.seq Sassem (.seq Sres Scr)))
/-- The full composite decoder, as the flat `Program` of Theorem 6.5. -/
def progDecOfFull (Srow Sdec Sassem Sres Scr : Stmt) : Program :=
  (compDecStmtFull Srow Sdec Sassem Sres Scr).compile 0 ++ [Instr.halt]
/-- **The tying equation for the full decoder**, by construction. -/
theorem progDecOfFull_eq (Srow Sdec Sassem Sres Scr : Stmt) :
    ∃ Sdec' : Stmt, Sdec'.compile 0 ++ [Instr.halt] =
      progDecOfFull Srow Sdec Sassem Sres Scr :=
  ⟨compDecStmtFull Srow Sdec Sassem Sres Scr, rfl⟩
/-- **A `Sem` run that lands on a `halt` is a `HaltsWithin` run.** -/
theorem haltsWithin_of_sem {P : Program} {E : RAMEnv} {a b : ℕ} {s : RAMState}
    {Q : ℕ → RAMState → Prop} {T : ℝ}
    (h : Sem P E a b s Q) (hT : ∀ k s', Q k s' → (k : ℝ) ≤ T)
    (hAt : P[b]? = some Instr.halt) :
    ∃ s', HaltsWithin P E T s s' := by
  obtain ⟨-, k, s', hstep, hb, hQ⟩ := h
  exact ⟨s', k, hT k s' hQ, hstep, by simp only [Halted, hb, hAt]⟩
/-- **A counted loop halts within a linear budget.**  Each iteration carries the loop-head state
`s j` back to the head with cost `cost j ≤ K`; the exit address holds a `halt`.  This is `Sem.loop`
composed with `haltsWithin_of_sem`, and it is the composition theorem the `ℓ`-fold decoder needs
(the `ℓ` per-child `Sem` runs are its hypothesis). -/
theorem haltsWithin_counted_loop {P : Program} {E : RAMEnv} {a : ℕ} {c : Cond} {b : Stmt}
    {n : ℕ} {s : ℕ → RAMState} {cost : ℕ → ℕ} {K : ℝ}
    (hAt : At P a (Stmt.compile (Stmt.loop c b) a)) (hW : 1 < 2 ^ E.W)
    (hpc : ∀ j, (s j).pc = a) (hgo : ∀ j < n, c.eval (s j)) (hstop : ¬ c.eval (s n))
    (hbody : ∀ j < n, Sem P E (a + c.code.length + 1) a
      { runBlock c.code E (s j) with pc := a + c.code.length + 1 }
      (fun k s' => k = cost j ∧ s' = s (j + 1)))
    (hcost : ∀ j < n, (cost j : ℝ) ≤ K) (hK : 0 ≤ K)
    (hhalt : P[a + c.code.length + b.len + 2]? = some Instr.halt) :
    ∃ s', HaltsWithin P E
      ((n : ℝ) * (K + ((c.code.length : ℝ) + 1)) + ((c.code.length : ℝ) + 2)) (s 0) s' := by
  obtain ⟨-, k, s', hstep, hb, hQ⟩ := Sem.loop P E a c b hAt hW n s cost hpc hgo hstop hbody
  have hsum : ((∑ j ∈ Finset.range n, (c.code.length + 1 + cost j) : ℕ) : ℝ) ≤
      (n : ℝ) * (((c.code.length : ℝ) + 1) + K) := by
    rw [Nat.cast_sum]
    calc (∑ j ∈ Finset.range n, ((c.code.length + 1 + cost j : ℕ) : ℝ))
        ≤ ∑ j ∈ Finset.range n, (((c.code.length : ℝ) + 1) + K) := by
          refine Finset.sum_le_sum fun j hj => ?_
          have h1 : (cost j : ℝ) ≤ K := hcost j (Finset.mem_range.mp hj)
          have h2 : ((c.code.length + 1 + cost j : ℕ) : ℝ) =
              ((c.code.length : ℝ) + 1) + (cost j : ℝ) := by push_cast; ring
          rw [h2]; linarith
      _ = (n : ℝ) * (((c.code.length : ℝ) + 1) + K) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hkR : (k : ℝ) ≤ ((c.code.length : ℝ) + 1) +
      (n : ℝ) * (((c.code.length : ℝ) + 1) + K) := by
    have h4 : (k : ℝ) ≤ ((c.code.length + 1 : ℕ) : ℝ) +
        ((∑ j ∈ Finset.range n, (c.code.length + 1 + cost j) : ℕ) : ℝ) := by
      exact_mod_cast hQ.1
    have h5 : ((c.code.length + 1 : ℕ) : ℝ) = (c.code.length : ℝ) + 1 := by push_cast; ring
    linarith
  have hb' : s'.pc = a + c.code.length + b.len + 2 := by rw [hQ.2]
  refine ⟨s', k, ?_, hstep, ?_⟩
  · rw [show K + ((c.code.length : ℝ) + 1) = ((c.code.length : ℝ) + 1) + K from by ring]
    linarith
  · simp only [Halted, hb', hhalt]
/-- **The `ℓ`-fold child-decoder loop halts within `ℓ·K + O(ℓ)`.**  The per-child `Sem` run is the
hypothesis — exactly the contract Theorem 5.1's export has to supply for its decoder at `N = d`;
the loop counter and the block count live in `r1`/`r2` and are restored by each child. -/
theorem haltsWithin_progDecOf {Sdec : Stmt} {E : RAMEnv} {n : ℕ} {s : ℕ → RAMState}
    {cost : ℕ → ℕ} {K : ℝ}
    (hW : 1 < 2 ^ E.W)
    (hpc : ∀ j, (s j).pc = 0) (hgo : ∀ j < n, decCond.eval (s j))
    (hstop : ¬ decCond.eval (s n))
    (hbody : ∀ j < n, Sem (progDecOf Sdec) E (decCond.code.length + 1) 0
      { runBlock decCond.code E (s j) with pc := decCond.code.length + 1 }
      (fun k s' => k = cost j ∧ s' = s (j + 1)))
    (hcost : ∀ j < n, (cost j : ℝ) ≤ K) (hK : 0 ≤ K) :
    ∃ s', HaltsWithin (progDecOf Sdec) E
      ((n : ℝ) * (K + ((decCond.code.length : ℝ) + 1)) +
        ((decCond.code.length : ℝ) + 2)) (s 0) s' := by
  have hAt : At (progDecOf Sdec) 0 (Stmt.compile (Stmt.loop decCond (.seq Sdec (.code decInc))) 0) := by
    intro r hr
    simp only [Nat.zero_add]
    have hcmp : compDecStmt Sdec = Stmt.loop decCond (.seq Sdec (.code decInc)) := rfl
    have h1 : (progDecOf Sdec)[r]? =
        ((Stmt.loop decCond (.seq Sdec (.code decInc))).compile 0 ++ [Instr.halt])[r]? := by
      simp only [progDecOf, hcmp]
    rw [h1, List.getElem?_append_left hr]
  have hlen : decCond.code.length + (Stmt.seq Sdec (.code decInc)).len + 2 =
      ((compDecStmt Sdec).compile 0).length := by
    rw [Stmt.length_compile]
    rfl
  have hhalt : (progDecOf Sdec)[0 + decCond.code.length +
      (Stmt.seq Sdec (.code decInc)).len + 2]? = some Instr.halt := by
    rw [show 0 + decCond.code.length + (Stmt.seq Sdec (.code decInc)).len + 2 =
      ((compDecStmt Sdec).compile 0).length from by omega]
    rw [show progDecOf Sdec = (compDecStmt Sdec).compile 0 ++ [Instr.halt] from rfl,
      List.getElem?_append_right (le_refl _)]
    simp
  exact haltsWithin_counted_loop hAt hW hpc hgo hstop hbody hcost hK hhalt
/-- **The decoder bound in Theorem 6.5's shape.**  `haltsWithin_progDecOf` at the per-child budget
`K = C d exp (C (lg lg n)²)` and `ℓ ≤ C (lg n + 2)²` (`time_sum_le`'s hypothesis) is again of the
form `Cd d exp (Cd (lg lg n)²)`, with `Cd = 7 C² e⁶ + 3`. -/
theorem haltsWithin_progDecOf_shape {Sdec : Stmt} {E : RAMEnv} {n ℓ d : ℕ}
    {s : ℕ → RAMState} {cost : ℕ → ℕ} {C : ℝ}
    (hW : 1 < 2 ^ E.W)
    (hpc : ∀ j, (s j).pc = 0) (hgo : ∀ j < ℓ, decCond.eval (s j))
    (hstop : ¬ decCond.eval (s ℓ))
    (hbody : ∀ j < ℓ, Sem (progDecOf Sdec) E (decCond.code.length + 1) 0
      { runBlock decCond.code E (s j) with pc := decCond.code.length + 1 }
      (fun k s' => k = cost j ∧ s' = s (j + 1)))
    (hcost : ∀ j < ℓ, (cost j : ℝ) ≤ C * (d : ℝ) * Real.exp (C * lg (lg (n : ℝ)) ^ 2))
    (hC : 1 ≤ C) (hn : 2 ≤ n) (hd : 1 ≤ d)
    (hℓ : (ℓ : ℝ) ≤ C * (lg (n : ℝ) + 2) ^ 2) :
    ∃ s', HaltsWithin (progDecOf Sdec) E
      ((7 * C ^ 2 * Real.exp 6 + 3) * (d : ℝ) *
        Real.exp ((7 * C ^ 2 * Real.exp 6 + 3) * lg (lg (n : ℝ)) ^ 2)) (s 0) s' := by
  set y : ℝ := lg (lg (n : ℝ)) with hy
  set K : ℝ := C * (d : ℝ) * Real.exp (C * y ^ 2) with hKdef
  have hy2 : (0 : ℝ) ≤ y ^ 2 := sq_nonneg y
  have hC0 : (0 : ℝ) < C := lt_of_lt_of_le zero_lt_one hC
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hexp1 : (1 : ℝ) ≤ Real.exp (C * y ^ 2) := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.2 (by positivity)
  have hK1 : (1 : ℝ) ≤ K := by
    rw [hKdef]
    have h2 : (1 : ℝ) ≤ C * (d : ℝ) := by nlinarith
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ (C * (d : ℝ)) * Real.exp (C * y ^ 2) :=
          mul_le_mul h2 hexp1 (by norm_num) (by positivity)
  have hK0 : (0 : ℝ) ≤ K := le_trans zero_le_one hK1
  obtain ⟨s', hs'⟩ := haltsWithin_progDecOf hW hpc hgo hstop hbody hcost hK0
  obtain ⟨k, hk, hstep, hhalt⟩ := hs'
  have hcl : decCond.code.length = 1 := rfl
  rw [hcl] at hk
  norm_num at hk
  refine ⟨s', k, ?_, hstep, hhalt⟩
  -- `K ≥ 1` and `time_sum_le` turn the loop bound into 6.5's shape
  have hCd3 : (3 : ℝ) ≤ 7 * C ^ 2 * Real.exp 6 + 3 := by
    have h1 : (0 : ℝ) ≤ C ^ 2 * Real.exp 6 := by positivity
    linarith
  have hCdC : C ≤ 7 * C ^ 2 * Real.exp 6 + 3 := by
    have h1 : (0 : ℝ) ≤ C := le_of_lt hC0
    have h2 : (0 : ℝ) ≤ C ^ 2 * Real.exp 6 := by positivity
    have h3 : (1 : ℝ) ≤ Real.exp 6 := by
      have := Real.add_one_le_exp (x := 6)
      linarith
    nlinarith [sq_nonneg C, h1, h3]
  have hexp_le : Real.exp (C * y ^ 2) ≤
      Real.exp ((7 * C ^ 2 * Real.exp 6 + 3) * y ^ 2) := by
    apply Real.exp_le_exp.2
    nlinarith [hy2, hCdC]
  rcases Nat.eq_zero_or_pos ℓ with h0 | hpos
  · subst h0
    simp only [Nat.cast_zero, zero_mul, zero_add] at hk ⊢
    have hd0 : (0 : ℝ) ≤ (d : ℝ) := by positivity
    have hexp0 : (0 : ℝ) < Real.exp ((7 * C ^ 2 * Real.exp 6 + 3) * y ^ 2) := Real.exp_pos _
    have hexp1' : (1 : ℝ) ≤ Real.exp ((7 * C ^ 2 * Real.exp 6 + 3) * y ^ 2) := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.2 (by positivity)
    have h3d : (3 : ℝ) ≤ (7 * C ^ 2 * Real.exp 6 + 3) * (d : ℝ) := by
      calc (3 : ℝ) = 3 * 1 := by ring
        _ ≤ (7 * C ^ 2 * Real.exp 6 + 3) * (d : ℝ) :=
            mul_le_mul hCd3 hd1 (by norm_num) (by linarith)
    have h3de : (3 : ℝ) ≤ (7 * C ^ 2 * Real.exp 6 + 3) * (d : ℝ) *
        Real.exp ((7 * C ^ 2 * Real.exp 6 + 3) * y ^ 2) := by
      calc (3 : ℝ) = 3 * 1 := by ring
        _ ≤ ((7 * C ^ 2 * Real.exp 6 + 3) * (d : ℝ)) *
              Real.exp ((7 * C ^ 2 * Real.exp 6 + 3) * y ^ 2) :=
            mul_le_mul h3d hexp1' (by norm_num) (by positivity)
    linarith [hk, h3de]
  · have hℓ1 : (1 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast hpos
    have hsum := time_sum_le C hC n d ℓ hn hd hℓ
    -- `ℓ(K+2)+3 ≤ 7 K ℓ`
    have h2l : (2 : ℝ) * (ℓ : ℝ) ≤ 3 * K * (ℓ : ℝ) := by
      have h2 : (2 : ℝ) ≤ 3 * K := by nlinarith
      exact mul_le_mul_of_nonneg_right h2 (by positivity)
    have h3 : (3 : ℝ) ≤ 3 * K := by nlinarith
    have h4 : (4 : ℝ) * (ℓ : ℝ) + 3 ≤ 7 * (ℓ : ℝ) := by nlinarith
    have hstep1 : (k : ℝ) ≤ 7 * K * (ℓ : ℝ) := by
      nlinarith [hk, h2l, h3, h4, hK0]
    have hstep2 : 7 * K * (ℓ : ℝ) ≤ 7 * ((C ^ 2 * Real.exp 6) * (d : ℝ) *
        Real.exp ((C ^ 2 * Real.exp 6) * y ^ 2)) := by
      have h := mul_le_mul_of_nonneg_left hsum (by norm_num : (0 : ℝ) ≤ 7)
      rw [hKdef]
      calc 7 * (C * (d : ℝ) * Real.exp (C * y ^ 2)) * (ℓ : ℝ)
          = 7 * ((ℓ : ℝ) * (C * (d : ℝ) * Real.exp (C * y ^ 2))) := by ring
        _ ≤ 7 * ((C ^ 2 * Real.exp 6) * (d : ℝ) * Real.exp ((C ^ 2 * Real.exp 6) * y ^ 2)) := h
    have hbase : 7 * ((C ^ 2 * Real.exp 6) * (d : ℝ) *
        Real.exp ((C ^ 2 * Real.exp 6) * y ^ 2)) =
        7 * C ^ 2 * Real.exp 6 * (d : ℝ) * Real.exp ((C ^ 2 * Real.exp 6) * y ^ 2) := by ring
    rw [hbase] at hstep2
    have h7C : 7 * C ^ 2 * Real.exp 6 ≤ 7 * C ^ 2 * Real.exp 6 + 3 := by linarith
    have hCe : C ^ 2 * Real.exp 6 ≤ 7 * C ^ 2 * Real.exp 6 + 3 := by
      have h1 : (0 : ℝ) ≤ C ^ 2 * Real.exp 6 := by positivity
      linarith
    have hexp2 : Real.exp ((C ^ 2 * Real.exp 6) * y ^ 2) ≤
        Real.exp ((7 * C ^ 2 * Real.exp 6 + 3) * y ^ 2) := by
      apply Real.exp_le_exp.2
      nlinarith [hy2, hCe]
    have hd0 : (0 : ℝ) ≤ (d : ℝ) := by positivity
    have hexp0 : (0 : ℝ) ≤ Real.exp ((7 * C ^ 2 * Real.exp 6 + 3) * y ^ 2) :=
      le_of_lt (Real.exp_pos _)
    have hfin : 7 * C ^ 2 * Real.exp 6 * (d : ℝ) * Real.exp ((C ^ 2 * Real.exp 6) * y ^ 2) ≤
        (7 * C ^ 2 * Real.exp 6 + 3) * (d : ℝ) *
          Real.exp ((7 * C ^ 2 * Real.exp 6 + 3) * y ^ 2) := by
      have hA : 7 * C ^ 2 * Real.exp 6 * (d : ℝ) ≤ (7 * C ^ 2 * Real.exp 6 + 3) * (d : ℝ) :=
        mul_le_mul_of_nonneg_right h7C hd0
      have hB : (0 : ℝ) ≤ 7 * C ^ 2 * Real.exp 6 * (d : ℝ) := by positivity
      have hC2 : (0 : ℝ) ≤ (7 * C ^ 2 * Real.exp 6 + 3) * (d : ℝ) := by positivity
      calc 7 * C ^ 2 * Real.exp 6 * (d : ℝ) * Real.exp ((C ^ 2 * Real.exp 6) * y ^ 2)
          ≤ (7 * C ^ 2 * Real.exp 6 + 3) * (d : ℝ) *
              Real.exp ((C ^ 2 * Real.exp 6) * y ^ 2) :=
            mul_le_mul_of_nonneg_right hA (le_of_lt (Real.exp_pos _))
        _ ≤ (7 * C ^ 2 * Real.exp 6 + 3) * (d : ℝ) *
              Real.exp ((7 * C ^ 2 * Real.exp 6 + 3) * y ^ 2) :=
            mul_le_mul_of_nonneg_left hexp2 hC2
    linarith [hstep1, hstep2, hfin]
/-- **The `ℓ`-fold toggle loop halts within `ℓ·K + O(ℓ)`.**  The per-block `Sem` run is the
hypothesis — exactly the base-relative export Theorem 5.1 has to supply for its toggle block; the
loop counter and the block count live in `r1`/`r2` and are restored by each block. -/
theorem haltsWithin_progUpOf {Sup : Stmt} {E : RAMEnv} {n : ℕ} {s : ℕ → RAMState}
    {cost : ℕ → ℕ} {K : ℝ}
    (hW : 1 < 2 ^ E.W)
    (hpc : ∀ j, (s j).pc = 0) (hgo : ∀ j < n, blkCond.eval (s j))
    (hstop : ¬ blkCond.eval (s n))
    (hbody : ∀ j < n, Sem (progUpOf Sup) E (blkCond.code.length + 1) 0
      { runBlock blkCond.code E (s j) with pc := blkCond.code.length + 1 }
      (fun k s' => k = cost j ∧ s' = s (j + 1)))
    (hcost : ∀ j < n, (cost j : ℝ) ≤ K) (hK : 0 ≤ K) :
    ∃ s', HaltsWithin (progUpOf Sup) E
      ((n : ℝ) * (K + ((blkCond.code.length : ℝ) + 1)) +
        ((blkCond.code.length : ℝ) + 2)) (s 0) s' := by
  have hAt : At (progUpOf Sup) 0 (Stmt.compile (Stmt.loop blkCond
      (.seq (.code [iMul r14 r1 r3, iAdd r7 r4 r1, iTbl r15 r7]) (.seq Sup (.code blkInc)))) 0) := by
    intro r hr
    simp only [Nat.zero_add]
    have hcmp : compUpStmt Sup = Stmt.loop blkCond
        (.seq (.code [iMul r14 r1 r3, iAdd r7 r4 r1, iTbl r15 r7]) (.seq Sup (.code blkInc))) := rfl
    have h1 : (progUpOf Sup)[r]? = ((Stmt.loop blkCond
        (.seq (.code [iMul r14 r1 r3, iAdd r7 r4 r1, iTbl r15 r7])
          (.seq Sup (.code blkInc)))).compile 0 ++ [Instr.halt])[r]? := by
      simp only [progUpOf, hcmp]
    rw [h1, List.getElem?_append_left hr]
  have hlen : blkCond.code.length +
      (Stmt.seq (.code [iMul r14 r1 r3, iAdd r7 r4 r1, iTbl r15 r7])
        (.seq Sup (.code blkInc))).len + 2 =
      ((compUpStmt Sup).compile 0).length := by
    rw [Stmt.length_compile]
    rfl
  have hhalt : (progUpOf Sup)[0 + blkCond.code.length +
      (Stmt.seq (.code [iMul r14 r1 r3, iAdd r7 r4 r1, iTbl r15 r7])
        (.seq Sup (.code blkInc))).len + 2]? = some Instr.halt := by
    rw [show 0 + blkCond.code.length +
      (Stmt.seq (.code [iMul r14 r1 r3, iAdd r7 r4 r1, iTbl r15 r7])
        (.seq Sup (.code blkInc))).len + 2 = ((compUpStmt Sup).compile 0).length from by omega]
    rw [show progUpOf Sup = (compUpStmt Sup).compile 0 ++ [Instr.halt] from rfl,
      List.getElem?_append_right (le_refl _)]
    simp
  exact haltsWithin_counted_loop hAt hW hpc hgo hstop hbody hcost hK hhalt
/-- **The toggle cost in Theorem 6.5's `pu + 2` shape** (`6toplevel.tex` 320–322): the per-block
budget is `Cu log^{pu} n`, and `ℓ · (Cu log^{pu} n) + O(ℓ)` is again `Cuc log^{pu + 2} n` by
`comp_col_bound` — the same bump that pays `ColumnWeightLE`. -/
theorem haltsWithin_progUpOf_shape {Sup : Stmt} {E : RAMEnv} {nblocks n C' : ℕ}
    {s : ℕ → RAMState} {cost : ℕ → ℕ} {Cu : ℝ} {pu : ℕ}
    (hW : 1 < 2 ^ E.W) (hn : 2 ≤ n)
    (hpc : ∀ j, (s j).pc = 0) (hgo : ∀ j < nblocks, blkCond.eval (s j))
    (hstop : ¬ blkCond.eval (s nblocks))
    (hbody : ∀ j < nblocks, Sem (progUpOf Sup) E (blkCond.code.length + 1) 0
      { runBlock blkCond.code E (s j) with pc := blkCond.code.length + 1 }
      (fun k s' => k = cost j ∧ s' = s (j + 1)))
    (hcost : ∀ j < nblocks, (cost j : ℝ) ≤ Cu * lg (n : ℝ) ^ pu)
    (hCu : 0 ≤ Cu)
    (hell : (nblocks : ℝ) ≤ (4 * (C' : ℝ) + 1) * (lg (n : ℝ) + 2) ^ 2) :
    ∃ s', HaltsWithin (progUpOf Sup) E
      ((9 * (4 * (C' : ℝ) + 1) * Cu + 9 * (18 * (4 * (C' : ℝ) + 1) + 3)) *
        lg (n : ℝ) ^ (pu + 2)) (s 0) s' := by
  have hlg0 : (0 : ℝ) ≤ lg (n : ℝ) := le_trans zero_le_one (one_le_lg hn)
  have hK0 : (0 : ℝ) ≤ Cu * lg (n : ℝ) ^ pu := mul_nonneg hCu (pow_nonneg hlg0 pu)
  obtain ⟨s', hs'⟩ := haltsWithin_progUpOf hW hpc hgo hstop hbody hcost hK0
  obtain ⟨k, hk, hstep, hhalt⟩ := hs'
  refine ⟨s', k, ?_, hstep, hhalt⟩
  have hcl : blkCond.code.length = 1 := rfl
  rw [hcl] at hk
  norm_num at hk
  have hlg1 : (1 : ℝ) ≤ lg (n : ℝ) := one_le_lg hn
  have hlgmono : lg (n : ℝ) ≤ lg ((n : ℝ) + 2) := lg_mono (by positivity) (by linarith)
  have hsq' : (lg (n : ℝ) + 2) ^ 2 ≤ 9 * lg ((n : ℝ) + 2) ^ 2 := by
    have h4 : lg (n : ℝ) + 2 ≤ 3 * lg ((n : ℝ) + 2) := by
      have h5 : (2 : ℝ) ≤ 2 * lg (n : ℝ) := by linarith
      nlinarith
    have h0 : (0 : ℝ) ≤ lg (n : ℝ) + 2 := by linarith
    have hb : (0 : ℝ) ≤ lg ((n : ℝ) + 2) := by linarith
    exact sq_le_nine_sq h0 h4 hb
  have hell9 : (nblocks : ℝ) ≤ 9 * (4 * (C' : ℝ) + 1) * lg ((n : ℝ) + 2) ^ 2 := by
    have h4 : ((4 : ℝ) * (C' : ℝ) + 1) * (lg (n : ℝ) + 2) ^ 2 ≤
        ((4 : ℝ) * (C' : ℝ) + 1) * (9 * lg ((n : ℝ) + 2) ^ 2) :=
      mul_le_mul_of_nonneg_left hsq' (by positivity)
    nlinarith [hell, h4]
  have hK23 : (0 : ℝ) ≤ 18 * (4 * (C' : ℝ) + 1) + 3 := by positivity
  have hdisp : 2 * (nblocks : ℝ) + 3 ≤
      (18 * (4 * (C' : ℝ) + 1) + 3) * lg ((n : ℝ) + 2) ^ 2 := by
    have h1 : (2 : ℝ) * (nblocks : ℝ) ≤
        2 * (9 * (4 * (C' : ℝ) + 1) * lg ((n : ℝ) + 2) ^ 2) :=
      mul_le_mul_of_nonneg_left hell9 (by norm_num)
    have h2 : (1 : ℝ) ≤ lg ((n : ℝ) + 2) ^ 2 := one_le_sq (by linarith)
    nlinarith [h1, h2, hK23]
  have hcol := comp_col_bound nblocks n hn C' Cu (18 * (4 * (C' : ℝ) + 1) + 3)
    (9 * (4 * (C' : ℝ) + 1) * Cu + 9 * (18 * (4 * (C' : ℝ) + 1) + 3)) pu hell rfl hCu hK23
  have hk' : (k : ℝ) ≤ (nblocks : ℝ) * (Cu * lg (n : ℝ) ^ pu) + (2 * (nblocks : ℝ) + 3) := by
    nlinarith only [hk]
  have h1 : (k : ℝ) ≤ (nblocks : ℝ) * (Cu * lg (n : ℝ) ^ pu) +
      (18 * (4 * (C' : ℝ) + 1) + 3) * lg ((n : ℝ) + 2) ^ 2 :=
    le_trans hk' (add_le_add_right hdisp _)
  exact le_trans h1 hcol

/-! ### 12.2 The toggle conjunct for one block

`TogglesWithin` starts the machine at `initState`, i.e. `pc = 0`, `r0 = i`, `r15 = 0`, and asks for a
`HaltsWithin τ` run of a programme that ends in `halt`.  `UpBlockSpec` supplies the run of
`Sup.compile 0`, but says nothing about the state's program counter, so it cannot by itself
conclude `Halted`.  `UpBlockHalts` is the same contract with that one conjunct made explicit; it is
exactly the per-child hypothesis `5.1`'s export has to produce (its own `progUp` ends in `halt`, so
the export has the halt for free). -/
/-- **The per-child toggle contract, halting form.**  `UpBlockSpec` plus the fact that the block
stops at its own end — which is what makes the appended `halt` reachable. -/
def UpBlockHalts (Sup : Stmt) (E : RAMEnv) (T : ℝ) {N Ms : ℕ}
    (Hs : (Fin N → ZMod 2) →ₗ[ZMod 2] (Fin Ms → ZMod 2)) : Prop :=
  ∀ (β : ℕ) (y : Fin Ms → ZMod 2) (i : Fin N) (s : RAMState),
    s.pc = 0 → s.regs 15 = β → s.regs 0 = i.val →
    (∀ j < wordsOf E.W Ms, s.mem (β + j) = packMem E.W y j) →
    ∃ (s' : RAMState), HaltsWithin (Sup.compile 0 ++ [Instr.halt]) E T s s' ∧
      s'.regs 15 = β ∧ s'.regs 0 = s.regs 0 ∧
      (∀ j < wordsOf E.W Ms, s'.mem (β + j) = packMem E.W (y + Hs (Pi.single i 1)) j) ∧
      (∀ c, c ∉ Finset.range (wordsOf E.W Ms) → s'.mem (β + c) = s.mem (β + c))
/-- **Appending the `halt` does not change a single step**: at every address the two programmes
either hold the same instruction or both are stuck, and at the `halt` address the machine is stuck
anyway.  So `Sup.compile 0 ++ [halt]` and `Sup.compile 0` have the same runs. -/
theorem step_append_halt (S : Stmt) (E : RAMEnv) (s : RAMState) :
    step (S.compile 0 ++ [Instr.halt]) E s = step (S.compile 0) E s := by
  by_cases h : s.pc < (S.compile 0).length
  · have h1 : (S.compile 0 ++ [Instr.halt])[s.pc]? = (S.compile 0)[s.pc]? :=
      List.getElem?_append_left h
    simp only [step, h1]
  · by_cases he : s.pc = (S.compile 0).length
    · have h2 : (S.compile 0 ++ [Instr.halt])[s.pc]? = some Instr.halt := by
        rw [he, List.getElem?_append_right (le_refl _)]
        simp
      have h3 : (S.compile 0)[s.pc]? = none := by
        rw [he, List.getElem?_eq_none_iff]
      simp only [step, h2, h3]
    · have h3 : (S.compile 0)[s.pc]? = none := by
        rw [List.getElem?_eq_none_iff]; omega
      have h4 : (S.compile 0 ++ [Instr.halt])[s.pc]? = none := by
        rw [List.getElem?_eq_none_iff]
        simp only [List.length_append, List.length_singleton]
        omega
      simp only [step, h3, h4]
/-- `UpBlockHalts` is `UpBlockSpec` plus the halt: dropping the `HaltsWithin` packaging gives the
contract of §11. -/
theorem upBlockSpec_of_upBlockHalts {Sup : Stmt} {E : RAMEnv} {T : ℝ} {N Ms : ℕ}
    {Hs : (Fin N → ZMod 2) →ₗ[ZMod 2] (Fin Ms → ZMod 2)}
    (h : UpBlockHalts Sup E T Hs) : UpBlockSpec Sup E T Hs := by
  intro β y i s hpc h15 h0 hmem
  obtain ⟨s', ⟨k, hk, hstep, -⟩, h15', h0', hmem', hframe'⟩ := h β y i s hpc h15 h0 hmem
  have hfun : step (Sup.compile 0 ++ [Instr.halt]) E = step (Sup.compile 0) E :=
    funext (step_append_halt Sup E)
  rw [hfun] at hstep
  exact ⟨k, s', hk, hstep, h15', h0', hmem', hframe'⟩
/-- **The toggle conjunct for a one-block composite.**  `TogglesWithin` of the halting programme,
from the per-block contract at `β = 0`, `det` base `0` — the state `TogglesWithin` starts from has
exactly the shape `UpBlockHalts` expects. -/
theorem togglesWithin_of_upBlockHalts {Sup : Stmt} {E : RAMEnv} {T : ℝ} {N Ms : ℕ}
    {Hs : (Fin N → ZMod 2) →ₗ[ZMod 2] (Fin Ms → ZMod 2)}
    (h : UpBlockHalts Sup E T Hs) :
    TogglesWithin (Sup.compile 0 ++ [Instr.halt]) E Hs T := by
  intro y i
  obtain ⟨s', hhalt, -, hr0, hmem, -⟩ :=
    h 0 y i (initState (packMem E.W y) i.val 0 0) (by simp [initState])
      (by simp [initState]) (by simp [initState]) (by intro j _; simp [initState])
  exact ⟨s', hhalt, fun addr haddr => by simpa using hmem addr haddr⟩

/-! ### 12.3 Uniform marginals: from the child's seed to the composite's

`5.1`'s failure bound is `prU` over the *child's* `spec.Seed`; `6.5`'s `hFail` is `prU` over the
*composite's* `TableSpec.Seed`, and the child's seed is `compChildSeed spec r childSpec s`, a
projection of the composite seed onto the coordinates of child `s` (a product of permutation and
coefficient tables).  The next lemma is the counting fact: on a product, every fiber of a coordinate
projection has the same cardinality, so the two probabilities agree. -/
/-- The projection of a dependent product onto the coordinates in `J`. -/
def piProj {ι : Type} (Y : ι → Type) (J : Finset ι) (f : (i : ι) → Y i) :
    ((i : J) → Y i.1) :=
  fun i => f i.1
/-- The fiber of `piProj` over `g`, as an equivalence with the complementary coordinates. -/
def piFiberEquiv {ι : Type} [DecidableEq ι] (Y : ι → Type) (J : Finset ι)
    (g : (i : J) → Y i.1) :
    {f : (i : ι) → Y i // piProj Y J f = g} ≃ ((i : {i : ι // i ∉ J}) → Y i.1) where
  toFun f := fun i => f.1 i.1
  invFun h :=
    ⟨fun i => if hi : i ∈ J then g ⟨i, hi⟩ else h ⟨i, hi⟩, by
      funext i
      simp only [piProj, dif_pos i.2]⟩
  left_inv f := by
    refine Subtype.ext (funext fun i => ?_)
    by_cases hi : i ∈ J
    · simp only [dif_pos hi]
      exact (congrFun f.2 ⟨i, hi⟩).symm
    · simp only [dif_neg hi]
  right_inv h := by
    funext i
    simp only [dif_neg i.2]
/-- **Uniform marginal of a product seed.** -/
theorem prU_pi_proj {ι : Type} [Fintype ι] [DecidableEq ι] (Y : ι → Type) [∀ i, Fintype (Y i)]
    [∀ i, Nonempty (Y i)] (J : Finset ι)
    (P : ((i : J) → Y i.1) → Prop) :
    prU (fun f : (i : ι) → Y i => P (piProj Y J f)) = prU P := by
  classical
  set c : ℕ := ∏ i : {i : ι // i ∉ J}, Fintype.card (Y i.1) with hc
  have hcpos : 0 < c := by
    rw [hc]
    exact Finset.prod_pos fun i _ => Fintype.card_pos
  have hfiber : ∀ g : (i : J) → Y i.1,
      (univ.filter fun f : (i : ι) → Y i => piProj Y J f = g).card = c := by
    intro g
    have h1 : (univ.filter fun f : (i : ι) → Y i => piProj Y J f = g).card =
        Fintype.card {f : (i : ι) → Y i // piProj Y J f = g} := by
      rw [Fintype.card_subtype]
    rw [h1, Fintype.card_congr (piFiberEquiv Y J g), Fintype.card_pi]
  have hnum : (univ.filter fun f : (i : ι) → Y i => P (piProj Y J f)).card =
      c * (univ.filter P).card := by
    have hmaps : ∀ f ∈ (univ.filter fun f : (i : ι) → Y i => P (piProj Y J f)),
        piProj Y J f ∈ (univ.filter P) := by
      intro f hf
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf ⊢
      exact hf
    rw [Finset.card_eq_sum_card_fiberwise (t := univ.filter P) hmaps]
    have h2 : ∀ g ∈ (univ.filter P : Finset ((i : J) → Y i.1)),
        ((univ.filter fun f : (i : ι) → Y i => P (piProj Y J f)).filter
          (fun f => piProj Y J f = g)).card = c := by
      intro g hg
      rw [Finset.filter_filter]
      have h3 : (univ.filter fun f : (i : ι) → Y i =>
          P (piProj Y J f) ∧ piProj Y J f = g) =
          (univ.filter fun f : (i : ι) → Y i => piProj Y J f = g) := by
        apply Finset.filter_congr
        intro f _
        constructor
        · rintro ⟨-, h⟩; exact h
        · intro h; subst h
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg
          exact ⟨hg, rfl⟩
      rw [h3, hfiber g]
    rw [Finset.sum_congr rfl h2, Finset.sum_const, smul_eq_mul, Nat.mul_comm]
  have hsplit : Fintype.card ((i : ι) → Y i) =
      (∏ i : {i : ι // i ∈ J}, Fintype.card (Y i.1)) *
        (∏ i : {i : ι // i ∉ J}, Fintype.card (Y i.1)) := by
    rw [Fintype.card_congr (Equiv.piEquivPiSubtypeProd (fun i => i ∈ J) Y),
      Fintype.card_prod, Fintype.card_pi, Fintype.card_pi]
  have hJ : Fintype.card ((i : J) → Y i.1) =
      ∏ i : {i : ι // i ∈ J}, Fintype.card (Y i.1) := by
    rw [Fintype.card_pi]
  have hden : Fintype.card ((i : ι) → Y i) =
      c * Fintype.card ((i : J) → Y i.1) := by
    rw [hsplit, hJ, hc, Nat.mul_comm]
  unfold prU
  rw [hnum, hden]
  have hcR : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hcpos
  rw [Nat.cast_mul, Nat.cast_mul]
  exact mul_div_mul_left _ _ (ne_of_gt hcR)
/-- `prU` is invariant under an equivalence of the sample space. -/
theorem prU_equiv {α β : Type} [Fintype α] [Fintype β] (e : α ≃ β) (P : β → Prop) :
    prU (fun a => P (e a)) = prU P := by
  classical
  unfold prU
  have h1 : (univ.filter fun a => P (e a)).card = (univ.filter P).card := by
    refine Finset.card_bij (fun a _ => e a) ?_ ?_ ?_
    · intro a ha
      simpa using ha
    · intro a1 ha1 a2 ha2 h
      exact e.injective h
    · intro b hb
      exact ⟨e.symm b, by simpa using hb, by simp⟩
  rw [h1, Fintype.card_congr e]
/-- **A product marginal, first coordinate.** -/
theorem prU_prod_fst {τ γ : Type} [Fintype τ] [Fintype γ] [Nonempty τ] [Nonempty γ]
    (P : τ → Prop) : prU (fun p : τ × γ => P p.1) = prU P := by
  classical
  unfold prU
  have h1 : (univ.filter fun p : τ × γ => P p.1) = (univ.filter P) ×ˢ (univ : Finset γ) := by
    ext p
    simp [Finset.mem_product]
  have h2 : Fintype.card (τ × γ) = Fintype.card τ * Fintype.card γ := Fintype.card_prod ..
  rw [h1, Finset.card_product, h2, Nat.cast_mul, Nat.cast_mul]
  have hγ : (0 : ℝ) < (Fintype.card γ : ℝ) := by exact_mod_cast Fintype.card_pos
  exact mul_div_mul_right _ _ (ne_of_gt hγ)
/-- **A product marginal, second coordinate.** -/
theorem prU_prod_snd {τ γ : Type} [Fintype τ] [Fintype γ] [Nonempty τ] [Nonempty γ]
    (P : γ → Prop) : prU (fun p : τ × γ => P p.2) = prU P := by
  classical
  unfold prU
  have h1 : (univ.filter fun p : τ × γ => P p.2) = (univ : Finset τ) ×ˢ (univ.filter P) := by
    ext p
    simp [Finset.mem_product]
  have h2 : Fintype.card (τ × γ) = Fintype.card τ * Fintype.card γ := Fintype.card_prod ..
  rw [h1, Finset.card_product, h2, Nat.cast_mul, Nat.cast_mul]
  have hτ : (0 : ℝ) < (Fintype.card τ : ℝ) := by exact_mod_cast Fintype.card_pos
  exact mul_div_mul_left _ _ (ne_of_gt hτ)
/-- **The composite seed marginalises to the child seed**, once the composite seed is identified
with `childSeed × rest` in the way the concatenation of the table lists prescribes.  `hπ` is that
identification; constructing it is the list bookkeeping over `spec.permSizes`/`spec.coeffShapes`
that `compChildSeed` reads. -/
theorem prU_compChildSeed {ℓ : ℕ} (spec : TableSpec) (childSpec : Fin ℓ → TableSpec) (s : Fin ℓ)
    {γ : Type} [Fintype γ] [Nonempty γ]
    (e : spec.Seed ≃ (childSpec s).Seed × γ)
    (hπ : ∀ r, compChildSeed spec r childSpec s = (e r).1)
    (P : (childSpec s).Seed → Prop) :
    prU (fun r : spec.Seed => P (compChildSeed spec r childSpec s)) = prU P := by
  have hfun : (fun r : spec.Seed => P (compChildSeed spec r childSpec s)) =
      fun r => P ((e r).1) := by
    funext r
    rw [hπ r]
  rw [hfun, prU_equiv e (fun p : (childSpec s).Seed × γ => P p.1), prU_prod_fst]
/-! ### 12.4 `hFail` from per-child bounds

`failure_bound_of_child_bounds` (§11.5) asks for one bound per child, over the *composite* seed.
`5.1` supplies it over the child's seed; `prU_compChildSeed` converts one into the other.  The
theorem below performs that conversion and then invokes the union bound. -/

theorem failure_bound_composite
    {ℓ lam lamStar : ℕ} {eps : ℝ} (hlam : lam = ⌈lg (1 / eps)⌉₊) (heps : 0 < eps)
    (harith : ((2 * ℓ + 2 : ℕ) : ℝ) * ((2 : ℝ) ^ lamStar)⁻¹ ≤ ((2 : ℝ) ^ (lam + 1))⁻¹)
    (spec : TableSpec) (childSpec : Fin ℓ → TableSpec)
    (hmarg : ∀ s : Fin ℓ, ∀ P : (childSpec s).Seed → Prop,
      prU (fun r : spec.Seed => P (compChildSeed spec r childSpec s)) = prU P)
    (Bad : spec.Seed → Prop)
    (Child : (s : Fin ℓ) → (childSpec s).Seed → Prop)
    (Init : Fin (2 * ℓ + 1) → spec.Seed → Prop)
    (hChild : ∀ s, prU (Child s) ≤ ((2 : ℝ) ^ (lam + 1))⁻¹ / (ℓ : ℝ))
    (hInit : ∀ i, prU (Init i) ≤ ((2 : ℝ) ^ lamStar)⁻¹)
    (hcover : ∀ b, Bad b →
      (∃ i, Init i b) ∨ ∃ s, Child s (compChildSeed spec b childSpec s)) :
    prU Bad ≤ eps := by
  refine failure_bound_of_child_bounds hlam heps harith Bad
    (fun s b => Child s (compChildSeed spec b childSpec s)) Init ?_ hInit hcover
  intro s
  rw [hmarg s (Child s)]
  exact hChild s

/-! ### 12.5 The residual conditions, exactly

What §12 **proves**:

* the composite programmes exist and satisfy the tying equations `∃ Sup', Sup'.compile 0 ++ [halt] =
  prog` by `rfl` (`progUpOf_eq`, `progUpOfFull_eq`, `progDecOf_eq`, `progDecOfFull_eq`), with the
  block list of Theorem 6.5 (`compUpStmtFull` = child blocks + `CR`; `compDecStmtFull` = row decode +
  child decoders + assembly + residual + `CR`);
* the toggle conjunct for **one** block (`togglesWithin_of_upBlockHalts`), and the conversion
  `UpBlockHalts → UpBlockSpec` (`upBlockSpec_of_upBlockHalts`);
* both `ℓ`-fold dispatchers **halt** within `ℓ · K + O(ℓ)` from one `Sem` per child
  (`haltsWithin_progUpOf`, `haltsWithin_progDecOf`), and the decoder's bound in 6.5's final shape
  `Cd · d · exp (Cd (lg lg n)²)` (`haltsWithin_progDecOf_shape`);
* the uniform-marginal core of the seed change (`prU_pi_proj`, `prU_prod_fst`, `prU_prod_snd`,
  `prU_equiv`, `prU_compChildSeed`), and the union bound on the composite seed
  (`failure_bound_composite`).

What §12 **cannot** derive from `UpBlockSpec` alone, i.e. the residual hypotheses:

* **T1 — the halt.**  `TogglesWithin` is a `HaltsWithin` statement, and `HaltsWithin` requires the
  run to reach a `halt`.  `UpBlockSpec` fixes registers and memory but not the program counter, so a
  block might stop early.  `UpBlockHalts` (§12.2) adds exactly that conjunct, and
  `upBlockSpec_of_upBlockHalts` shows it is a strengthening, not a weakening.
* **T2 — the `det` base.**  `compDet` puts child `s`'s table at the `2^W` addresses
  `[s·2^W, (s+1)·2^W)`, while every register is reduced mod `2^W` by `step` (`step_regs_lt`), so a
  `qDet` address computed inside the child is `< 2^W` and cannot name a block `s ≥ 1`: the child must
  add a *det base* it holds in a register.  `UpBlockSpec` fixes `r15` to the payload base only.  The
  dispatcher `compUpStmt` therefore puts the det base in `r14`; the child contract has to expose it,
  and `composite_sketch`'s `det` should be re-indexed by the block width `2 ^ Wmax` (with
  `(ℓ+1)·2^Wmax ≤ 2^kk ≤ 2^W`, `s·2^Wmax + a` does not wrap).  That is a change to the `det`
  definition only: `H` is built from the child matrices and `compAsm`, not from `det`, and the length
  bound does not mention `det`.
* **T3 — the payload stitching.**  `haltsWithin_progUpOf`'s `hbody` is the per-block `Sem` contract;
  closing `TogglesWithin (progUpOfFull Sup Scr) E (compAsm …) T` also needs the word-level induction:
  `compDet_range_disjoint` routes each `det` query to one block, `compAsm_block_start` says the word
  ranges are disjoint and `W`-aligned, `compAsm_blk` identifies the composite entry with the child
  entry, and `packMem_blk` (word-local form) stitches each payload word.  The frame clause of the
  per-block contract keeps the blocks from disturbing one another.
* **D1 — the decoder-side per-child contract.**  `haltsWithin_progDecOf` takes one `Sem` per child
  (`hbody`); the remaining four blocks (`Srow`, `Sassem`, `Sres`, `Scr`) need their own `Sem` specs —
  the `Stmt` form of Proposition 2.3's decoder.  Neither `CrCallSpec` nor `CrOutSpec` exists in this
  file, so 2.3's export must add them.
* **F1 — the concrete seed equivalence.**  `prU_compChildSeed` reduces the composite-seed marginal to
  an equivalence `e : spec.Seed ≃ (childSpec s).Seed × γ` with `compChildSeed … = (e ·).1`;
  constructing `e` is the list bookkeeping over `spec.permSizes = n :: (children flattened)` and
  `spec.coeffShapes` (`List.get` of the concatenation).  Given `e`, `failure_bound_composite` gives
  `hFail`'s `prU Bad ≤ eps` from 5.1's per-child `2^{-λ-1}/ℓ` bound.

With T1–T3 (and `UpBlockSpec`'s frame clause) the multi-block toggle is the induction described in
§11.5; with D1 the decoder conjunct is `haltsWithin_progDecOf_shape` plus the four block specs; with
F1 `hFail` is closed. -/

end LinearSetReconciliation327.Main


