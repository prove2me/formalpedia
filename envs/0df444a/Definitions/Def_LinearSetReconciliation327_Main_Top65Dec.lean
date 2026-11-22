-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_Top65Dec
-- name    : LinearSetReconciliation327_Main_Top65Dec
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-21T10:20:58.696524+00:00
-- url     : https://prove2.me/theorems/6a80a31a-457a-4cf7-bd5a-48a14b3891f0
-- title:
--   The top-level decoder of Theorem 6.5: composite program, stage contracts, time bounds, and conjunct 7
-- statement:
--   **The machine side of Theorem 6.5's decoder.**  This bundle fixes the composite decoder of §9.2 and the vocabulary in which its correctness is stated.
--
--   For six compiled statements $S_{\mathrm{init}},S_{\mathrm{row}},S_{\mathrm{dec}},S_{\mathrm{assem}},S_{\mathrm{res}},S_{\mathrm{cr}}$ it defines the program
--
--   $$
--   \mathrm{progDecOfTop}(S_{\mathrm{init}},\dots,S_{\mathrm{cr}})
--   = \mathrm{compile}\bigl(S_{\mathrm{init}};\ \mathrm{loop}^{d}(S_{\mathrm{row}});\ \mathrm{loop}^{\ell}(S_{\mathrm{dec}});\ S_{\mathrm{assem}};\ S_{\mathrm{res}};\ S_{\mathrm{cr}}\bigr) \mathbin{+\!+} [\mathrm{halt}],
--   $$
--
--   with the address algebra $\mathrm{dRowBase},\mathrm{dColBase},\mathrm{dAsBase},\mathrm{dResBase},\mathrm{dCrBase},\mathrm{dEnd}$ that locates each stage, and the tying equation $\mathrm{progDecOfTop\_eq}$ (by $\mathrm{rfl}$).
--
--   The stage interface is `StageRun P E a b T I Q`: every run of $P$ from a state satisfying $I$ at program counter $a$ reaches program counter $b$ within $T$ steps in a state satisfying $Q$.  `StageRun.trans` composes two stages, and `stageRun_counted_loop` turns a per-iteration body contract into a contract for a counted loop.  The bundle also proves the two time-shape theorems $\mathrm{haltsWithin\_rowLoop\_shape}$ ($d\log^{O(1)}n$) and $\mathrm{haltsWithin\_colLoop\_shape}$ ($(7C^2e^6+3)\,d\exp((7C^2e^6+3)(\lg\lg n)^2)$) from the sub-decoders' own bounds, and $\mathrm{cr\_time\_shape}$ (Proposition 2.3's row bound inside 6.5's budget).
--
--   Finally it defines `TopDecRuns` (one `StageRun` per stage, with trivial postconditions) and proves `haltsWithin_topDec_of_runs` — **conjunct 7** in stage form — and `haltsWithin_topDec_final`, conjunct 7 in 6.5's final shape.  It also names the per-seed worst-case correctness predicate `TopDecCorrects`: every halting run from the sketch of $x$ outputs $\operatorname{supp}x$.  That predicate *is* the correctness half of conjunct 8; the theorem that derives it from the six stage contracts is published separately.
--
--   **Formalization Note** The bundle contains definitions and fully proved lemmas only (no `sorry`, no new axiom).  It deliberately does not import the older `Def_…_Top65` bundle, whose re-exported declarations clash with `Sol_theorem_6_5.lean`; the handful of §1/§4 logarithm facts and the dispatched-loop shape it needs are carried locally under the `d65_` prefix.  The reason it lives in `Definitions` is compilation budget: together with `Sol_theorem_6_5` it elaborates past the platform's per-file limit.
-- source:
--   arXiv:2611.11409 (Tianren Liu, Rui Xu, Tong Yang, Kangyang Zhou, *Linear Set Reconciliation with O(d) Additive Redundancy*), §9.2 (the decoder of Theorem 6.5) and Theorem 6.5, PDF p.31 (printed p.30), lines 324-328 (`6toplevel.tex`); §13.1-13.7 of the verified development `Solutions/Sol_theorem_6_5.lean` and `Solutions/_65_cond_block.lean.txt`.  Proposition 2.3 for the CR stage's time bound.

import Mathlib
import Definitions.Def_LinearSetReconciliation327_Main_Basic
import Definitions.Def_LinearSetReconciliation327_Main_Framework
import Definitions.Def_LinearSetReconciliation327_Main_TopLevel
import Definitions.Def_LinearSetReconciliation327_Main_WordRAM
import Definitions.Def_LinearSetReconciliation327_Main_DecoderModel
import Definitions.Def_LinearSetReconciliation327_Main_DecoderLemmas
/-!
# `Top65Dec`: the top-level decoder of Theorem 6.5 (`6toplevel.tex` 324-328, §9.2)

The decoder of the *universe-`n`* object.  It is not derivable from any export of Theorem 5.1 —
5.1's decoder decodes a universe-`d` object — so it is built here, on the published machine model
(`Stmt`, `Sem`, `At`, `HaltsWithin`) and nothing else.

This module deliberately does **not** import `Definitions.Def_…_Top65`: that bundle re-exports the
declarations `Solutions/Sol_theorem_6_5.lean` re-derives, so importing it from there would clash.
The handful of §1/§4 logarithm lemmas and the dispatched-loop shape it needs are therefore carried
here under the `d65_` prefix, mechanically extracted from `Top65` (their texts are identical).

Contents:

* §13.1 address plumbing (`At.compile_top`, `at_append_left/right`, `at_seq_left/right`);
* §13.2 `StageRun`, the `Sem`-minus-`Halted` stage contract, and the `Halted`-free loop rule;
* §13.3 `topLoop`/`topDecStmt`/`progDecOfTop` and the tying equation `progDecOfTop_eq` (`rfl`);
* §13.4 `haltsWithin_rowLoop_shape` (`d log^{O(1)} n`) and `haltsWithin_colLoop_shape`
  (`(7C²e⁶+3) d exp((7C²e⁶+3)(lg lg n)²)`), proved from the sub-decoders' own time bounds;
* §13.5 `TopDecRuns` (the six stage contracts), `haltsWithin_topDec_of_runs` (**conjunct 7**);
* §13.6 `cr_time_shape` (`proposition_2_3`'s row bound inside 6.5's budget);
* §13.7 `haltsWithin_topDec_final` (conjunct 7 in 6.5's final shape) and `TopDecCorrects`
  (conjunct 8, named — see the note there for the missing platform bridge).
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped ENNReal
open Finset

namespace LinearSetReconciliation327.Main

/-! ### The §1/§4 facts this module needs, carried locally (`d65_` prefix) -/

/-- `⌈log 2⌉ = 1` is the only base fact used below; `lg` is `Real.logb 2`. -/
lemma d65_lg_two : lg (2 : ℝ) = 1 := Real.logb_self_eq_one (by norm_num)

lemma d65_one_le_lg {n : ℕ} (hn : 2 ≤ n) : 1 ≤ lg (n : ℝ) := by
  have h2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hn' : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h : Real.log 2 ≤ Real.log (n : ℝ) := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hn'
  show 1 ≤ Real.log (n : ℝ) / Real.log 2
  rw [le_div_iff₀ h2]
  linarith

/-- `lg lg n ≥ 0` for `n ≥ 2`, so `(lg lg n)^2` is a genuine exponent. -/
lemma d65_lg_lg_nonneg {n : ℕ} (hn : 2 ≤ n) : 0 ≤ lg (lg (n : ℝ)) := by
  have h2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have h1 : (1 : ℝ) ≤ lg (n : ℝ) := d65_one_le_lg hn
  have hl : 0 ≤ Real.log (lg (n : ℝ)) := Real.log_nonneg h1
  exact div_nonneg hl (le_of_lt h2)

lemma d65_log_lg_add_two_le {n : ℕ} (hn : 2 ≤ n) :
    Real.log (lg (n : ℝ) + 2) ≤ lg (lg (n : ℝ)) + 2 := by
  set y : ℝ := lg (lg (n : ℝ)) with hy
  have hy0 : 0 ≤ y := d65_lg_lg_nonneg hn
  have hln : (0 : ℝ) < lg (n : ℝ) := lt_of_lt_of_le zero_lt_one (d65_one_le_lg hn)
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

/-- `lg` is monotone on the positives. -/
lemma d65_lg_mono {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) : lg x ≤ lg y := by
  have h2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have h := Real.log_le_log hx hxy
  show Real.log x / Real.log 2 ≤ Real.log y / Real.log 2
  exact div_le_div_of_nonneg_right h (le_of_lt h2)

/-- `lg (x y) = lg x + lg y`. -/
lemma d65_lg_mul {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) : lg (x * y) = lg x + lg y :=
  Real.logb_mul hx hy

/-- `lg (x^n) = n lg x`. -/
lemma d65_lg_pow {x : ℝ} (hx : x ≠ 0) (n : ℕ) : lg (x ^ n) = (n : ℝ) * lg x := by
  induction n with
  | zero => rw [pow_zero, Nat.cast_zero, zero_mul]; exact Real.logb_one
  | succ k ih =>
    rw [pow_succ, d65_lg_mul (pow_ne_zero k hx) hx, ih]
    push_cast
    ring

/-- `1 ≤ x * y` for `1 ≤ x`, `1 ≤ y`. -/
lemma d65_one_le_mul_one_le {x y : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y) : (1 : ℝ) ≤ x * y := by
  have h : (1 : ℝ) * 1 ≤ x * y := mul_le_mul hx hy (by norm_num) (by linarith)
  linarith

lemma d65_time_sum_le (C : ℝ) (hC : 1 ≤ C) (n d ℓ : ℕ) (hn : 2 ≤ n) (hd : 1 ≤ d)
    (hℓ : (ℓ : ℝ) ≤ C * (lg (n : ℝ) + 2) ^ 2) :
    (ℓ : ℝ) * (C * (d : ℝ) * Real.exp (C * lg (lg (n : ℝ)) ^ 2)) ≤
      (C ^ 2 * Real.exp 6) * (d : ℝ) *
        Real.exp ((C ^ 2 * Real.exp 6) * lg (lg (n : ℝ)) ^ 2) := by
  set y : ℝ := lg (lg (n : ℝ)) with hy
  set x : ℝ := y ^ 2 with hx
  have hx0 : (0 : ℝ) ≤ x := by positivity
  have hy0 : (0 : ℝ) ≤ y := d65_lg_lg_nonneg hn
  have hyx : y ≤ x + 1 := by nlinarith
  have hlg1 : (1 : ℝ) ≤ lg (n : ℝ) := d65_one_le_lg hn
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
      have h5 : Real.log (lg (n : ℝ) + 2) ≤ y + 2 := d65_log_lg_add_two_le hn
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

/-! ### The dispatched-loop shape of §12.1, carried locally

`d65Cond`/`d65Inc` are `blkCond`/`blkInc` of §12.1 — the loop test `r7 < r1 r2` and the counter
increment — under the names this module uses for both of its loops. -/

/-- The loop test: run while the block counter `r1` is below the bound `r2`. -/
def d65Cond : Cond := .lt r7 r1 r2

/-- The per-iteration counter increment. -/
def d65Inc : List Instr := [iImm r7 1, iAdd r1 r1 r7]


/-! ## 13. The top-level decoder of Theorem 6.5 (`6toplevel.tex` 324–328, §9.2)

This section builds the piece of Theorem 6.5 that is 6.5's own machine-side content and that no
export of Theorem 5.1 can supply: the decoder of the **universe-`n`** object.  §9.2's pipeline is

> row decoding (`Stmt.loop` over the `d` rows) → the `ℓ` child decoders (`Stmt.loop` over the
> `ℓ = B w` columns) → prefix assembly → residual syndrome → final `CR` recovery,

and §13 builds exactly that: the `Stmt` (`topDecStmt`), the address algebra that lets each block run
inside the one fixed programme `progDecOfTop` (`At.compile_top`, `at_row_loop`, `at_col_loop`), the
two counted loops in 6.5's own shape (`haltsWithin_rowLoop_shape`, `haltsWithin_colLoop_shape`), the
composition of the six stages into one `HaltsWithin` (`haltsWithin_topDec_of_runs`) and 6.5's
`Cd · d · exp (Cd (lg lg n)²)` closure (`haltsWithin_topDec_shape`).  Those are conjunct 7 of
`theorem_6_5_statement`.

### What each stage consumes, and from where

| stage | `Stmt` | contract's provenance |
|---|---|---|
| `Sinit` | prologue | reads `d`, `ℓ`, `wordsOf W M` out of `det`'s header (§13.7 (P)) |
| `Srow` | body of `Stmt.loop` over `d` rows | `proposition_2_1`'s `progDec` at `(N,t) := (rowLen n d j, B)`, one call per row |
| `Sdec` | body of `Stmt.loop` over `ℓ` columns | `theorem_5_1`'s `progDec` at `N := d`, `X := capX a`, `Y := capY a k` |
| `Sassem` | prefix assembly | register work (`assemble`, `RowScheme.assembled`) |
| `Sres` | residual syndrome | register work |
| `Scr` | `CR` call | `proposition_2_3`'s `progDec` at `(N,t) := (n, resid)` |

The two counted loops are the blocks whose `HaltsWithin` is *proved from the sub-decoders' own time
bounds*; the other four are the named hypotheses `TopDecRuns` records. -/

/-! ### 13.1 Address plumbing: a compiled `Stmt` occupies its own addresses -/

/-- Every compiled programme occupies its own addresses inside itself.  `progDecOfTop` is by
construction `Stmt.compile 0 ++ [halt]`, so this is the append-left projection. -/
theorem At.compile_top (S : Stmt) : At (S.compile 0 ++ [Instr.halt]) 0 (S.compile 0) := by
  intro r hr
  simp only [Nat.zero_add]
  exact List.getElem?_append_left hr

/-- The first summand of an `At` fact for an appended code list. -/
theorem at_append_left {P : Program} {base : ℕ} {l₁ l₂ : List Instr} (h : At P base (l₁ ++ l₂)) :
    At P base l₁ :=
  (At.append.mp h).1

/-- The second summand of an `At` fact for an appended code list, at its compiled address. -/
theorem at_append_right {P : Program} {base : ℕ} {l₁ l₂ : List Instr}
    (h : At P base (l₁ ++ l₂)) : At P (base + l₁.length) l₂ :=
  (At.append.mp h).2

/-- The first half of a `seq`, at the address `Stmt.len` gives it. -/
theorem at_seq_left {P : Program} {base : ℕ} {a b : Stmt}
    (h : At P base (Stmt.compile (Stmt.seq a b) base)) : At P base (Stmt.compile a base) := by
  have h' : At P base (a.compile base ++ b.compile (base + a.len)) := h
  exact (At.append.mp h').1

/-- The second half of a `seq`, at the address `Stmt.len` gives it. -/
theorem at_seq_right {P : Program} {base : ℕ} {a b : Stmt}
    (h : At P base (Stmt.compile (Stmt.seq a b) base)) :
    At P (base + a.len) (Stmt.compile b (base + a.len)) := by
  have h' : At P base (a.compile base ++ b.compile (base + a.len)) := h
  have h2 : At P (base + (a.compile base).length) (b.compile (base + a.len)) :=
    (At.append.mp h').2
  rwa [Stmt.length_compile] at h2

/-! ### 13.2 A `Sem`-free stage contract

`Sem P E a b s Q` asks the run to end at the address `b`, and `HaltsWithin` additionally asks the
machine to be *halted* there.  A stage of a pipeline ends at the entry of the next stage, where no
`halt` sits, so neither notion applies: the right contract is `Sem` minus `Halted`. -/

/-- **One stage of the top-level decoder.**  From every state at the entry address `a` satisfying `I`,
the machine reaches, in at most `T` steps, a state at the exit address `b` satisfying `Q`. -/
def StageRun (P : Program) (E : RAMEnv) (a b : ℕ) (T : ℝ) (I Q : RAMState → Prop) : Prop :=
  ∀ s : RAMState, s.pc = a → I s →
    ∃ (k : ℕ) (s' : RAMState), (k : ℝ) ≤ T ∧ (step P E)^[k] s = s' ∧ s'.pc = b ∧ Q s'

/-- Two stages glue, and the costs add. -/
theorem StageRun.trans {P : Program} {E : RAMEnv} {a b c : ℕ} {T₁ T₂ : ℝ}
    {I J K : RAMState → Prop} (h₁ : StageRun P E a b T₁ I J) (h₂ : StageRun P E b c T₂ J K) :
    StageRun P E a c (T₁ + T₂) I K := by
  intro s hpc hI
  obtain ⟨k₁, s₁, hk₁, hs₁, hb₁, hJ⟩ := h₁ s hpc hI
  obtain ⟨k₂, s₂, hk₂, hs₂, hb₂, hK⟩ := h₂ s₁ hb₁ hJ
  refine ⟨k₁ + k₂, s₂, ?_, ?_, hb₂, hK⟩
  · push_cast
    linarith
  · rw [Nat.add_comm k₁ k₂, Function.iterate_add_apply, hs₁, hs₂]

/-- **The loop rule, `Halted`-free.**  `n` iterations from the loop head, then the failing test.
This is `haltsWithin_counted_loop` with the `halt` requirement removed — a sub-loop of a pipeline
exits into the next block, not into a `halt` — and it is what turns the `d` row decodes and the `ℓ`
child decodes into one `Stmt.loop` each. -/
theorem stageRun_counted_loop {P : Program} {E : RAMEnv} {a : ℕ} {c : Cond} {b : Stmt}
    {n : ℕ} {s : ℕ → RAMState} {cost : ℕ → ℕ} {K : ℝ}
    (hAt : At P a (Stmt.compile (Stmt.loop c b) a)) (hW : 1 < 2 ^ E.W)
    (hpc : ∀ j, (s j).pc = a) (hgo : ∀ j < n, c.eval (s j)) (hstop : ¬ c.eval (s n))
    (hbody : ∀ j < n, Sem P E (a + c.code.length + 1) a
      { runBlock c.code E (s j) with pc := a + c.code.length + 1 }
      (fun k s' => k = cost j ∧ s' = s (j + 1)))
    (hcost : ∀ j < n, (cost j : ℝ) ≤ K) (hK : 0 ≤ K) :
    ∃ (k : ℕ) (s' : RAMState),
      (k : ℝ) ≤ (n : ℝ) * (K + ((c.code.length : ℝ) + 1)) + ((c.code.length : ℝ) + 2) ∧
      (step P E)^[k] (s 0) = s' ∧ s'.pc = a + c.code.length + b.len + 2 := by
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
  refine ⟨k, s', ?_, hstep, ?_⟩
  · rw [show K + ((c.code.length : ℝ) + 1) = ((c.code.length : ℝ) + 1) + K from by ring]
    linarith
  · rw [hQ.2]

/-! ### 13.3 The decoder `Stmt`

The dispatched loop `topLoop S = Stmt.loop d65Cond (S ++ incr)` *is* `compDecStmt S` of §12.1 — one
loop body, one counter `r1`, one bound `r2`, one test `r7 < r1 r2` — reused unchanged for both the
`d` rows and the `ℓ` columns: the two dispatchers differ only in the register preloads, which is what
lets a single parameter-free programme serve every `(n,d,λ)`. -/

/-- The counted dispatcher of §12.1, under the name the top-level decoder uses for both its loops:
one loop body, one counter `r1`, one bound `r2`, one test `r7 < r1 r2`.  It is `compDecStmt` of
§12.1, reused unchanged for the `d` rows and the `ℓ` columns — the two dispatchers differ only in
the register preloads, which is what lets a single parameter-free programme serve every
`(n,d,λ)`. -/
def topLoop (S : Stmt) : Stmt := .loop d65Cond (.seq S (.code d65Inc))

/-- **The top-level decoder of §9.2**, as one `Stmt`: prologue, row decode, the `ℓ` child decoders,
prefix assembly, residual syndrome, `CR` recovery. -/
def topDecStmt (Sinit Srow Sdec Sassem Sres Scr : Stmt) : Stmt :=
  .seq Sinit (.seq (topLoop Srow) (.seq (topLoop Sdec) (.seq Sassem (.seq Sres Scr))))

/-- The top-level decoder as the flat `Program` of Theorem 6.5. -/
def progDecOfTop (Sinit Srow Sdec Sassem Sres Scr : Stmt) : Program :=
  (topDecStmt Sinit Srow Sdec Sassem Sres Scr).compile 0 ++ [Instr.halt]

/-- **The tying equation for the top-level decoder**, by construction: this is the `hSdec`-shaped
hypothesis `theorem_6_5_of_composite` consumes. -/
theorem progDecOfTop_eq (Sinit Srow Sdec Sassem Sres Scr : Stmt) :
    ∃ S' : Stmt, S'.compile 0 ++ [Instr.halt] = progDecOfTop Sinit Srow Sdec Sassem Sres Scr :=
  ⟨topDecStmt Sinit Srow Sdec Sassem Sres Scr, rfl⟩

/-- Address of the row-decoding loop. -/
def dRowBase (Sinit : Stmt) : ℕ := 0 + Sinit.len

/-- Address of the child-decoder loop. -/
def dColBase (Sinit Srow : Stmt) : ℕ := dRowBase Sinit + (topLoop Srow).len

/-- Address of the prefix assembly. -/
def dAsBase (Sinit Srow Sdec : Stmt) : ℕ := dColBase Sinit Srow + (topLoop Sdec).len

/-- Address of the residual syndrome. -/
def dResBase (Sinit Srow Sdec Sassem : Stmt) : ℕ := dAsBase Sinit Srow Sdec + Sassem.len

/-- Address of the `CR` call. -/
def dCrBase (Sinit Srow Sdec Sassem Sres : Stmt) : ℕ := dResBase Sinit Srow Sdec Sassem + Sres.len

/-- Address just past the `CR` call, where `compile` puts the `halt`. -/
def dEnd (Sinit Srow Sdec Sassem Sres Scr : Stmt) : ℕ :=
  dCrBase Sinit Srow Sdec Sassem Sres + Scr.len

/-- The entry precondition of the row loop: counter `0`, bound `d`. -/
def RowIn (d : ℕ) : RAMState → Prop := fun s => s.regs 1 = 0 ∧ s.regs 2 = d

/-- The entry precondition of the child loop: counter `0`, bound `ℓ`. -/
def ColIn (ell : ℕ) : RAMState → Prop := fun s => s.regs 1 = 0 ∧ s.regs 2 = ell

/-- The `At` fact for the decoder suffix that starts at the row loop. -/
theorem at_row_seq (Sinit Srow Sdec Sassem Sres Scr : Stmt) :
    At (progDecOfTop Sinit Srow Sdec Sassem Sres Scr) (dRowBase Sinit)
      (Stmt.compile (Stmt.seq (topLoop Srow)
        (Stmt.seq (topLoop Sdec) (Stmt.seq Sassem (Stmt.seq Sres Scr)))) (dRowBase Sinit)) := by
  have h0 : At (progDecOfTop Sinit Srow Sdec Sassem Sres Scr) 0
      ((topDecStmt Sinit Srow Sdec Sassem Sres Scr).compile 0) := At.compile_top _
  exact at_seq_right (a := Sinit)
    (b := Stmt.seq (topLoop Srow)
      (Stmt.seq (topLoop Sdec) (Stmt.seq Sassem (Stmt.seq Sres Scr)))) h0

/-- The row loop sits where `compile` puts it. -/
theorem at_row_loop (Sinit Srow Sdec Sassem Sres Scr : Stmt) :
    At (progDecOfTop Sinit Srow Sdec Sassem Sres Scr) (dRowBase Sinit)
      (Stmt.compile (topLoop Srow) (dRowBase Sinit)) :=
  at_seq_left (a := topLoop Srow)
    (b := Stmt.seq (topLoop Sdec) (Stmt.seq Sassem (Stmt.seq Sres Scr))) (at_row_seq _ _ _ _ _ _)

/-- The `At` fact for the decoder suffix that starts at the child loop. -/
theorem at_col_seq (Sinit Srow Sdec Sassem Sres Scr : Stmt) :
    At (progDecOfTop Sinit Srow Sdec Sassem Sres Scr) (dColBase Sinit Srow)
      (Stmt.compile (Stmt.seq (topLoop Sdec) (Stmt.seq Sassem (Stmt.seq Sres Scr)))
        (dColBase Sinit Srow)) :=
  at_seq_right (a := topLoop Srow)
    (b := Stmt.seq (topLoop Sdec) (Stmt.seq Sassem (Stmt.seq Sres Scr))) (at_row_seq _ _ _ _ _ _)

/-- The child loop sits where `compile` puts it. -/
theorem at_col_loop (Sinit Srow Sdec Sassem Sres Scr : Stmt) :
    At (progDecOfTop Sinit Srow Sdec Sassem Sres Scr) (dColBase Sinit Srow)
      (Stmt.compile (topLoop Sdec) (dColBase Sinit Srow)) :=
  at_seq_left (a := topLoop Sdec) (b := Stmt.seq Sassem (Stmt.seq Sres Scr))
    (at_col_seq _ _ _ _ _ _)

/-! ### 13.4 The two counted loops, in 6.5's shape

`6toplevel.tex` 324-328: "Row decoding, residual-syndrome formation, and CR recovery together cost
`d log^{O(1)} n` … As the dominant term, the `ℓ` child calls take `d exp(O((log log n)²))` time by
Theorem 5.1."  So the row loop is bounded by a *polylogarithm*, and the child loop by 5.1's own shape;
`loop_cost_shape` is the numeric core of `haltsWithin_progDecOf_shape`, reused at the child loop's own
address inside the top-level programme. -/

/-- `(lg n)^p ≤ Λ exp(Λ (lg lg n)²)`: the absorption that prices every polylogarithmic stage cost
inside 6.5's quasipolylogarithmic budget.  Writing `y = lg lg n`, we have `lg n = 2^y`, hence
`(lg n)^p = exp(p y log 2)`; for `y ≥ 1` this is at most `exp(Λ y²)` because `p log 2 ≤ p ≤ Λ ≤ Λ y`,
and for `y ≤ 1` the left side is at most `2^p ≤ Λ ≤ Λ exp(Λ y²)`.  `Λ` only has to dominate `p` and
`2^p`. -/
lemma pow_lg_le_exp_le {Λ : ℝ} (hΛ1 : 1 ≤ Λ) {p : ℕ} (hp : (p : ℝ) ≤ Λ) (hp2 : (2 : ℝ) ^ p ≤ Λ)
    {n : ℕ} (hn : 2 ≤ n) :
    (lg (n : ℝ)) ^ p ≤ Λ * Real.exp (Λ * lg (lg (n : ℝ)) ^ 2) := by
  set y : ℝ := lg (lg (n : ℝ)) with hy
  have hy0 : 0 ≤ y := d65_lg_lg_nonneg hn
  have hlgn1 : (1 : ℝ) ≤ lg (n : ℝ) := d65_one_le_lg hn
  have hlgnpos : (0 : ℝ) < lg (n : ℝ) := lt_of_lt_of_le zero_lt_one hlgn1
  have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hexp : lg (n : ℝ) = Real.exp (y * Real.log 2) := by
    have hy' : y = Real.logb 2 (lg (n : ℝ)) := hy
    have h : (2 : ℝ) ^ y = lg (n : ℝ) := by
      rw [hy']
      exact Real.rpow_logb (by norm_num) (by norm_num) hlgnpos
    rw [← h, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), mul_comm]
  have hpow : (lg (n : ℝ)) ^ p = Real.exp ((p : ℝ) * (y * Real.log 2)) := by
    rw [hexp, ← Real.exp_nat_mul]
  have hΛ0 : (0 : ℝ) ≤ Λ := le_trans zero_le_one hΛ1
  have hy2 : (0 : ℝ) ≤ y ^ 2 := sq_nonneg y
  have hexpΛ : (1 : ℝ) ≤ Real.exp (Λ * y ^ 2) := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.2 (by positivity)
  have hp0 : (0 : ℝ) ≤ (p : ℝ) := by positivity
  by_cases hy1 : y ≤ 1
  · have h1 : Real.exp ((p : ℝ) * (y * Real.log 2)) ≤ Real.exp ((p : ℝ) * Real.log 2) := by
      apply Real.exp_le_exp.2
      have hle : y * Real.log 2 ≤ 1 * Real.log 2 := mul_le_mul_of_nonneg_right hy1 (le_of_lt hlog2pos)
      nlinarith [hle, hp0]
    have h2 : Real.exp ((p : ℝ) * Real.log 2) = (2 : ℝ) ^ p := by
      have hcast : ((p : ℝ) * Real.log 2) = ((p : ℕ) : ℝ) * Real.log 2 := by push_cast; ring
      rw [hcast, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    calc (lg (n : ℝ)) ^ p = Real.exp ((p : ℝ) * (y * Real.log 2)) := hpow
      _ ≤ Real.exp ((p : ℝ) * Real.log 2) := h1
      _ = (2 : ℝ) ^ p := h2
      _ ≤ Λ := hp2
      _ = Λ * 1 := by ring
      _ ≤ Λ * Real.exp (Λ * y ^ 2) := mul_le_mul_of_nonneg_left hexpΛ hΛ0

  · have hlog2le : Real.log 2 ≤ 1 := by
      have h := Real.log_le_sub_one_of_pos (x := 2) (by norm_num : (0 : ℝ) < 2)
      linarith
    have hy1' : 1 < y := lt_of_not_ge hy1
    have harg : (p : ℝ) * (y * Real.log 2) ≤ Λ * y ^ 2 := by
      have hylog : y * Real.log 2 ≤ y * 1 := mul_le_mul_of_nonneg_left hlog2le hy0
      have h1 : (p : ℝ) * (y * Real.log 2) ≤ (p : ℝ) * y := by
        have h := mul_le_mul_of_nonneg_left hylog hp0
        simpa using h
      have h2 : (p : ℝ) * y ≤ Λ * y := mul_le_mul_of_nonneg_right hp hy0
      have h3 : Λ * y ≤ Λ * y ^ 2 := by
        have hyy : y ≤ y * y := by nlinarith
        calc Λ * y ≤ Λ * (y * y) := mul_le_mul_of_nonneg_left hyy hΛ0
          _ = Λ * y ^ 2 := by ring
      linarith
    calc (lg (n : ℝ)) ^ p = Real.exp ((p : ℝ) * (y * Real.log 2)) := hpow
      _ ≤ Real.exp (Λ * y ^ 2) := Real.exp_le_exp.2 harg
      _ ≤ Λ * Real.exp (Λ * y ^ 2) := by
          calc Real.exp (Λ * y ^ 2) = 1 * Real.exp (Λ * y ^ 2) := by ring
            _ ≤ Λ * Real.exp (Λ * y ^ 2) :=
                mul_le_mul_of_nonneg_right hΛ1 (le_of_lt (Real.exp_pos _))

/-- `(lg n)^p` is at least `1`: what lets the row loop's dispatch overhead be paid by `d`. -/
lemma one_le_pow_lg {n : ℕ} (hn : 2 ≤ n) (p : ℕ) : (1 : ℝ) ≤ lg (n : ℝ) ^ p := by
  have hlg1 : (1 : ℝ) ≤ lg (n : ℝ) := d65_one_le_lg hn
  have hlg0 : (0 : ℝ) ≤ lg (n : ℝ) := le_trans zero_le_one hlg1
  induction p with
  | zero => simp
  | succ k ih =>
      rw [pow_succ]
      exact d65_one_le_mul_one_le ih hlg1

/-- **The numeric core of `haltsWithin_progDecOf_shape`**, as a standalone lemma so that the child
loop can be priced at *its* address inside the top-level programme.  `ℓ` iterations of a body costing
`K = C d exp(C (lg lg n)²)`, plus the dispatch overhead, is 6.5's own shape with `Cd = 7C²e⁶+3`. -/
theorem loop_cost_shape {n ℓ d : ℕ} {C K k : ℝ}
    (hK : K = C * (d : ℝ) * Real.exp (C * lg (lg (n : ℝ)) ^ 2))
    (hk : k ≤ (ℓ : ℝ) * (K + 2) + 3)
    (hC : 1 ≤ C) (hn : 2 ≤ n) (hd : 1 ≤ d)
    (hℓ : (ℓ : ℝ) ≤ C * (lg (n : ℝ) + 2) ^ 2) :
    k ≤ (7 * C ^ 2 * Real.exp 6 + 3) * (d : ℝ) *
        Real.exp ((7 * C ^ 2 * Real.exp 6 + 3) * lg (lg (n : ℝ)) ^ 2) := by
  set y : ℝ := lg (lg (n : ℝ)) with hy
  have hy2 : (0 : ℝ) ≤ y ^ 2 := sq_nonneg y
  have hC0 : (0 : ℝ) < C := lt_of_lt_of_le zero_lt_one hC
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hexp1 : (1 : ℝ) ≤ Real.exp (C * y ^ 2) := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.2 (by positivity)
  have hK1 : (1 : ℝ) ≤ K := by
    rw [hK]
    have h2 : (1 : ℝ) ≤ C * (d : ℝ) := by nlinarith
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ (C * (d : ℝ)) * Real.exp (C * y ^ 2) :=
          mul_le_mul h2 hexp1 (by norm_num) (by positivity)
  have hK0 : (0 : ℝ) ≤ K := le_trans zero_le_one hK1
  have hCd3 : (3 : ℝ) ≤ 7 * C ^ 2 * Real.exp 6 + 3 := by
    have h1 : (0 : ℝ) ≤ C ^ 2 * Real.exp 6 := by positivity
    linarith
  rcases Nat.eq_zero_or_pos ℓ with h0 | hpos
  · subst h0
    simp only [Nat.cast_zero, zero_mul, zero_add] at hk ⊢
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
    have hsum := d65_time_sum_le C hC n d ℓ hn hd hℓ
    have h2l : (2 : ℝ) * (ℓ : ℝ) ≤ 3 * K * (ℓ : ℝ) := by
      have h2 : (2 : ℝ) ≤ 3 * K := by nlinarith
      exact mul_le_mul_of_nonneg_right h2 (by positivity)
    have h3 : (3 : ℝ) ≤ 3 * K := by nlinarith
    have h4 : (4 : ℝ) * (ℓ : ℝ) + 3 ≤ 7 * (ℓ : ℝ) := by nlinarith
    have hstep1 : k ≤ 7 * K * (ℓ : ℝ) := by nlinarith [hk, h2l, h3, h4, hK0]
    have hstep2 : 7 * K * (ℓ : ℝ) ≤ 7 * ((C ^ 2 * Real.exp 6) * (d : ℝ) *
        Real.exp ((C ^ 2 * Real.exp 6) * y ^ 2)) := by
      have h := mul_le_mul_of_nonneg_left hsum (by norm_num : (0 : ℝ) ≤ 7)
      rw [hK]
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
    have hfin : 7 * C ^ 2 * Real.exp 6 * (d : ℝ) * Real.exp ((C ^ 2 * Real.exp 6) * y ^ 2) ≤
        (7 * C ^ 2 * Real.exp 6 + 3) * (d : ℝ) *
          Real.exp ((7 * C ^ 2 * Real.exp 6 + 3) * y ^ 2) := by
      have hA : 7 * C ^ 2 * Real.exp 6 * (d : ℝ) ≤ (7 * C ^ 2 * Real.exp 6 + 3) * (d : ℝ) :=
        mul_le_mul_of_nonneg_right h7C hd0
      have hC2 : (0 : ℝ) ≤ (7 * C ^ 2 * Real.exp 6 + 3) * (d : ℝ) := by positivity
      calc 7 * C ^ 2 * Real.exp 6 * (d : ℝ) * Real.exp ((C ^ 2 * Real.exp 6) * y ^ 2)
          ≤ (7 * C ^ 2 * Real.exp 6 + 3) * (d : ℝ) *
              Real.exp ((C ^ 2 * Real.exp 6) * y ^ 2) :=
            mul_le_mul_of_nonneg_right hA (le_of_lt (Real.exp_pos _))
        _ ≤ (7 * C ^ 2 * Real.exp 6 + 3) * (d : ℝ) *
              Real.exp ((7 * C ^ 2 * Real.exp 6 + 3) * y ^ 2) :=
            mul_le_mul_of_nonneg_left hexp2 hC2
    linarith [hstep1, hstep2, hfin]

/-- **Row decoding halts in `d log^{O(1)} n`** (`6toplevel.tex` 324-326: "the row outputs contain at
most `dB` coordinates").  One `Stmt.loop` of `d` iterations, each one `proposition_2_1` call of cost
`Kr (lg n)^{pr}`; the dispatch overhead is `2` steps per iteration plus `3`. -/
theorem haltsWithin_rowLoop_shape {Sinit Srow Sdec Sassem Sres Scr : Stmt} {E : RAMEnv} {n d : ℕ}
    {s : ℕ → RAMState} {cost : ℕ → ℕ} {Kr : ℝ} {pr : ℕ}
    (hW : 1 < 2 ^ E.W)
    (hpc : ∀ j, (s j).pc = dRowBase Sinit) (hgo : ∀ j < d, d65Cond.eval (s j))
    (hstop : ¬ d65Cond.eval (s d))
    (hbody : ∀ j < d, Sem (progDecOfTop Sinit Srow Sdec Sassem Sres Scr) E
      (dRowBase Sinit + d65Cond.code.length + 1) (dRowBase Sinit)
      { runBlock d65Cond.code E (s j) with pc := dRowBase Sinit + d65Cond.code.length + 1 }
      (fun k s' => k = cost j ∧ s' = s (j + 1)))
    (hcost : ∀ j < d, (cost j : ℝ) ≤ Kr * lg (n : ℝ) ^ pr)
    (hKr : 0 ≤ Kr) (hn : 2 ≤ n) (hd : 1 ≤ d) :
    ∃ (k : ℕ) (s' : RAMState),
      (k : ℝ) ≤ (Kr + 5) * (d : ℝ) * lg (n : ℝ) ^ (pr + 1) ∧
      (step (progDecOfTop Sinit Srow Sdec Sassem Sres Scr) E)^[k] (s 0) = s' ∧
      s'.pc = dColBase Sinit Srow := by
  have hlg1 : (1 : ℝ) ≤ lg (n : ℝ) := d65_one_le_lg hn
  have hlg0 : (0 : ℝ) ≤ lg (n : ℝ) := le_trans zero_le_one hlg1
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hK0 : (0 : ℝ) ≤ Kr * lg (n : ℝ) ^ pr := mul_nonneg hKr (pow_nonneg hlg0 pr)
  obtain ⟨k, s', hk, hstep, hpc'⟩ :=
    stageRun_counted_loop (at_row_loop Sinit Srow Sdec Sassem Sres Scr) hW hpc hgo hstop hbody
      hcost hK0
  have hcl : d65Cond.code.length = 1 := rfl
  have hbl : (Stmt.seq Srow (.code d65Inc)).len = Srow.len + 2 := rfl
  have hll : (topLoop Srow).len = d65Cond.code.length + (Stmt.seq Srow (.code d65Inc)).len + 2 := rfl
  refine ⟨k, s', ?_, hstep, ?_⟩
  · rw [hcl] at hk
    norm_num at hk
    have hp1 : lg (n : ℝ) ^ pr ≤ lg (n : ℝ) ^ (pr + 1) := by
      have h := mul_le_mul_of_nonneg_left hlg1 (pow_nonneg hlg0 pr)
      simpa [pow_succ] using h
    have hone : (1 : ℝ) ≤ lg (n : ℝ) ^ (pr + 1) := one_le_pow_lg hn (pr + 1)
    have hK : Kr * lg (n : ℝ) ^ pr + 2 ≤ (Kr + 2) * lg (n : ℝ) ^ (pr + 1) := by
      have h1 : Kr * lg (n : ℝ) ^ pr ≤ Kr * lg (n : ℝ) ^ (pr + 1) :=
        mul_le_mul_of_nonneg_left hp1 hKr
      have h2 : (2 : ℝ) ≤ 2 * lg (n : ℝ) ^ (pr + 1) := by linarith
      linarith
    have hexp : (d : ℝ) * (Kr * lg (n : ℝ) ^ pr + 2) ≤
        (Kr + 2) * (d : ℝ) * lg (n : ℝ) ^ (pr + 1) := by
      have h := mul_le_mul_of_nonneg_left hK (le_trans zero_le_one hd1)
      calc (d : ℝ) * (Kr * lg (n : ℝ) ^ pr + 2)
          ≤ (d : ℝ) * ((Kr + 2) * lg (n : ℝ) ^ (pr + 1)) := h
        _ = (Kr + 2) * (d : ℝ) * lg (n : ℝ) ^ (pr + 1) := by ring
    have h3 : (3 : ℝ) ≤ 3 * (d : ℝ) * lg (n : ℝ) ^ (pr + 1) := by
      have h1 : (1 : ℝ) ≤ (d : ℝ) * lg (n : ℝ) ^ (pr + 1) := d65_one_le_mul_one_le hd1 hone
      linarith
    have hfin : (d : ℝ) * (Kr * lg (n : ℝ) ^ pr + 2) + 3 ≤
        (Kr + 5) * (d : ℝ) * lg (n : ℝ) ^ (pr + 1) := by
      have h4 : (Kr + 2) * (d : ℝ) * lg (n : ℝ) ^ (pr + 1) + 3 * (d : ℝ) * lg (n : ℝ) ^ (pr + 1) =
          (Kr + 5) * (d : ℝ) * lg (n : ℝ) ^ (pr + 1) := by ring
      linarith [hexp, h3, h4]
    linarith [hk, hfin]
  · rw [hpc', dColBase, hll, hcl, hbl]
    omega

/-- **The `ℓ` child decoders halt in 5.1's own shape** (`6toplevel.tex` 326-328).  One `Stmt.loop` of
`ℓ` iterations, each one `theorem_5_1`'s decoder at `N := d`; the closure into
`Cd d exp(Cd (lg lg n)²)` is `loop_cost_shape`, i.e. `d65_time_sum_le` plus the dispatch overhead. -/
theorem haltsWithin_colLoop_shape {Sinit Srow Sdec Sassem Sres Scr : Stmt} {E : RAMEnv} {n ℓ d : ℕ}
    {s : ℕ → RAMState} {cost : ℕ → ℕ} {C : ℝ}
    (hW : 1 < 2 ^ E.W)
    (hpc : ∀ j, (s j).pc = dColBase Sinit Srow) (hgo : ∀ j < ℓ, d65Cond.eval (s j))
    (hstop : ¬ d65Cond.eval (s ℓ))
    (hbody : ∀ j < ℓ, Sem (progDecOfTop Sinit Srow Sdec Sassem Sres Scr) E
      (dColBase Sinit Srow + d65Cond.code.length + 1) (dColBase Sinit Srow)
      { runBlock d65Cond.code E (s j) with pc := dColBase Sinit Srow + d65Cond.code.length + 1 }
      (fun k s' => k = cost j ∧ s' = s (j + 1)))
    (hcost : ∀ j < ℓ, (cost j : ℝ) ≤ C * (d : ℝ) * Real.exp (C * lg (lg (n : ℝ)) ^ 2))
    (hC : 1 ≤ C) (hn : 2 ≤ n) (hd : 1 ≤ d)
    (hℓ : (ℓ : ℝ) ≤ C * (lg (n : ℝ) + 2) ^ 2) :
    ∃ (k : ℕ) (s' : RAMState),
      (k : ℝ) ≤ (7 * C ^ 2 * Real.exp 6 + 3) * (d : ℝ) *
        Real.exp ((7 * C ^ 2 * Real.exp 6 + 3) * lg (lg (n : ℝ)) ^ 2) ∧
      (step (progDecOfTop Sinit Srow Sdec Sassem Sres Scr) E)^[k] (s 0) = s' ∧
      s'.pc = dAsBase Sinit Srow Sdec := by
  have hK0 : (0 : ℝ) ≤ C * (d : ℝ) * Real.exp (C * lg (lg (n : ℝ)) ^ 2) := by positivity
  obtain ⟨k, s', hk, hstep, hpc'⟩ :=
    stageRun_counted_loop (at_col_loop Sinit Srow Sdec Sassem Sres Scr) hW hpc hgo hstop hbody
      hcost hK0
  have hcl : d65Cond.code.length = 1 := rfl
  have hbl : (Stmt.seq Sdec (.code d65Inc)).len = Sdec.len + 2 := rfl
  have hll : (topLoop Sdec).len = d65Cond.code.length + (Stmt.seq Sdec (.code d65Inc)).len + 2 := rfl
  refine ⟨k, s', ?_, hstep, ?_⟩
  · rw [hcl] at hk
    norm_num at hk
    exact loop_cost_shape rfl hk hC hn hd hℓ
  · rw [hpc', dAsBase, hll, hcl, hbl]
    omega

/-! ### 13.5 The composition of the six stages -/

/-- **The residual hypotheses of Theorem 6.5's decoder (conjunct 7), one field per block of §9.2.**

Each field is a `StageRun` of the *one fixed* programme `progDecOfTop`, at the address `compile` gives
the block, with the pre/post condition linking it to its neighbours.  Provenance:

* `init` — the prologue.  `det` is public preprocessing (not sketch length), and 5.1 and 2.1/2.3 read
  their whole parameter set out of it; the `d`/`ℓ`/word-count header is the same convention
  (§13.7 (P)).
* `row` — **`proposition_2_1`**'s decoder, `d` times: obtained from `haltsWithin_rowLoop_shape` by
  supplying the loop-head family.
* `col` — **`theorem_5_1`**'s decoder at `N := d`, `ℓ` times: obtained from
  `haltsWithin_colLoop_shape` likewise.  This is the field that needs 5.1's decoder exported as a
  `Stmt` with a base-relative `Sem` contract (§12.5 D1 / `Up5Export.down`).
* `as`, `res` — prefix assembly and residual syndrome: register work on the parent's own state.
* `cr` — **`proposition_2_3`**'s decoder at `(N,t) := (n, resid)`.

The `∀ y` binders keep the payload a parameter: `decoderStart W y []` is the only start state the
platform's decoder conjunct has. -/
structure TopDecRuns (Sinit Srow Sdec Sassem Sres Scr : Stmt) (E : RAMEnv) (W M n d ℓ : ℕ)
    (Tini Trow Tdec Tas Tres Tcr : ℝ) : Prop where
  /-- The prologue: read `d`, `ℓ` and `wordsOf W M` from `det`'s header. -/
  init : ∀ y : Fin M → ZMod 2,
    StageRun (progDecOfTop Sinit Srow Sdec Sassem Sres Scr) E 0 (dRowBase Sinit) Tini
      (fun s => s = decoderStart W y []) (RowIn d)
  /-- Row decoding: `d` iterations of `proposition_2_1`. -/
  row : ∀ y : Fin M → ZMod 2,
    StageRun (progDecOfTop Sinit Srow Sdec Sassem Sres Scr) E (dRowBase Sinit) (dColBase Sinit Srow)
      Trow (RowIn d) (ColIn ℓ)
  /-- The `ℓ` child decoders of `theorem_5_1`. -/
  col : ∀ y : Fin M → ZMod 2,
    StageRun (progDecOfTop Sinit Srow Sdec Sassem Sres Scr) E (dColBase Sinit Srow)
      (dAsBase Sinit Srow Sdec) Tdec (ColIn ℓ) (fun _ => True)
  /-- Prefix assembly. -/
  as : ∀ y : Fin M → ZMod 2,
    StageRun (progDecOfTop Sinit Srow Sdec Sassem Sres Scr) E (dAsBase Sinit Srow Sdec)
      (dResBase Sinit Srow Sdec Sassem) Tas (fun _ => True) (fun _ => True)
  /-- Residual syndrome. -/
  res : ∀ y : Fin M → ZMod 2,
    StageRun (progDecOfTop Sinit Srow Sdec Sassem Sres Scr) E (dResBase Sinit Srow Sdec Sassem)
      (dCrBase Sinit Srow Sdec Sassem Sres) Tres (fun _ => True) (fun _ => True)
  /-- The final `CR` recovery of `proposition_2_3`. -/
  cr : ∀ y : Fin M → ZMod 2,
    StageRun (progDecOfTop Sinit Srow Sdec Sassem Sres Scr) E (dCrBase Sinit Srow Sdec Sassem Sres)
      (dEnd Sinit Srow Sdec Sassem Sres Scr) Tcr (fun _ => True) (fun _ => True)

/-- **Conjunct 7 of Theorem 6.5, from the six stage contracts.**  The six `StageRun`s compose into one
run from `decoderStart W y []` to the address `compile` leaves for the trailing `halt`. -/
theorem haltsWithin_topDec_of_runs {Sinit Srow Sdec Sassem Sres Scr : Stmt} {E : RAMEnv}
    {W M n d ℓ : ℕ} {Tini Trow Tdec Tas Tres Tcr : ℝ}
    (h : TopDecRuns Sinit Srow Sdec Sassem Sres Scr E W M n d ℓ Tini Trow Tdec Tas Tres Tcr)
    (y : Fin M → ZMod 2) :
    ∃ s' : RAMState,
      HaltsWithin (progDecOfTop Sinit Srow Sdec Sassem Sres Scr) E
        (Tini + Trow + Tdec + Tas + Tres + Tcr) (decoderStart W y []) s' := by
  have hstep : StageRun (progDecOfTop Sinit Srow Sdec Sassem Sres Scr) E 0
      (dEnd Sinit Srow Sdec Sassem Sres Scr) (Tini + Trow + Tdec + Tas + Tres + Tcr)
      (fun s => s = decoderStart W y []) (fun _ => True) :=
    ((((h.init y).trans (h.row y)).trans (h.col y)).trans (h.as y)).trans (h.res y)
      |>.trans (h.cr y)
  obtain ⟨k, s', hk, hrun, hpc, -⟩ := hstep (decoderStart W y []) rfl rfl
  have hlen : dEnd Sinit Srow Sdec Sassem Sres Scr =
      ((topDecStmt Sinit Srow Sdec Sassem Sres Scr).compile 0).length := by
    rw [Stmt.length_compile]
    simp only [dEnd, dCrBase, dResBase, dAsBase, dColBase, dRowBase, topDecStmt, topLoop, Stmt.len]
    omega
  have hhalt :
      (progDecOfTop Sinit Srow Sdec Sassem Sres Scr)[dEnd Sinit Srow Sdec Sassem Sres Scr]? =
        some Instr.halt := by
    rw [hlen]
    rw [show progDecOfTop Sinit Srow Sdec Sassem Sres Scr =
      (topDecStmt Sinit Srow Sdec Sassem Sres Scr).compile 0 ++ [Instr.halt] from rfl,
      List.getElem?_append_right (le_refl _)]
    simp
  exact ⟨s', k, hk, hrun, by simp only [Halted, hpc, hhalt]⟩

/-! ### 13.6 The `CR` stage in 6.5's shape

`proposition_2_3`'s worst-case time at `(N,t) := (n, resid)` is
`K₂.₃ max 1 (t lg(t+2) lg(n+2))`.  `resid ≤ n` and `resid ≤ d(B+1)` (`TopParams.resid` is a `min`),
`B = O(C' log log n)` and `lg(n+2) ≤ 3 lg n`, so the whole stage is `O(C' d log² n)`, which
`pow_lg_le_exp_le` prices inside `exp(O((lg lg n)²))`. -/

/-- `lg (n + 2) ≤ 3 lg n` for `n ≥ 2`: `n + 2 ≤ 4n` and `lg 4 = 2 ≤ 2 lg n`. -/
lemma lg_nat_add_two_le {n : ℕ} (hn : 2 ≤ n) : lg ((n : ℝ) + 2) ≤ 3 * lg (n : ℝ) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by
    have : 0 < n := by omega
    exact_mod_cast this
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hlg1 : (1 : ℝ) ≤ lg (n : ℝ) := d65_one_le_lg hn
  have hmono : lg ((n : ℝ) + 2) ≤ lg (4 * (n : ℝ)) :=
    d65_lg_mono (by positivity : (0 : ℝ) < (n : ℝ) + 2) (by linarith)
  have hsplit : lg (4 * (n : ℝ)) = lg 4 + lg (n : ℝ) :=
    d65_lg_mul (by norm_num : (4 : ℝ) ≠ 0) (ne_of_gt hn0)
  have h4 : lg (4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) by norm_num, d65_lg_pow (by norm_num : (2 : ℝ) ≠ 0)]
    norm_num [d65_lg_two]
  rw [hsplit, h4] at hmono
  linarith

/-- `y + 3 ≤ 4 exp(y²)` for `y = lg lg n ≥ 0`: `y ≤ exp(y²)` because `1 + y² ≥ y`. -/
lemma lg_lg_add_three_le {n : ℕ} (hn : 2 ≤ n) :
    lg (lg (n : ℝ)) + 3 ≤ 4 * Real.exp (lg (lg (n : ℝ)) ^ 2) := by
  set y : ℝ := lg (lg (n : ℝ)) with hy
  have hy0 : 0 ≤ y := d65_lg_lg_nonneg hn
  have hy2 : (0 : ℝ) ≤ y ^ 2 := sq_nonneg y
  have hexp : y ^ 2 + 1 ≤ Real.exp (y ^ 2) := Real.add_one_le_exp (y ^ 2)
  have hsq : y ≤ y ^ 2 + 1 := by nlinarith
  have hone : (1 : ℝ) ≤ Real.exp (y ^ 2) := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.2 hy2
  linarith

/-- **`proposition_2_3`'s decoder time at `(N,t) := (n, resid)` is inside 6.5's budget.**  With
`t ≤ n`, `t ≤ d(B+1)` and `B + 1 ≤ (C'+1)(lg lg n + 3)`, the row bound `K t lg(t+2) lg(n+2)` is
`O((C'+1) K d exp(11 (lg lg n)²))`. -/
lemma cr_time_shape {n d t B C' : ℕ} {Kcr : ℝ} (hKcr : 0 ≤ Kcr) (hn : 2 ≤ n) (hd : 1 ≤ d)
    (htn : t ≤ n) (htd : t ≤ d * (B + 1))
    (hB : (B : ℝ) + 1 ≤ ((C' : ℝ) + 1) * (lg (lg (n : ℝ)) + 3)) :
    Kcr * max 1 ((t : ℝ) * lg ((t : ℝ) + 2) * lg ((n : ℝ) + 2)) ≤
      1802 * ((C' : ℝ) + 1) * Kcr * (d : ℝ) * Real.exp (11 * lg (lg (n : ℝ)) ^ 2) := by
  set y : ℝ := lg (lg (n : ℝ)) with hy
  have hy0 : 0 ≤ y := d65_lg_lg_nonneg hn
  have hy2 : (0 : ℝ) ≤ y ^ 2 := sq_nonneg y
  have hlg1 : (1 : ℝ) ≤ lg (n : ℝ) := d65_one_le_lg hn
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hC'0 : (0 : ℝ) ≤ (C' : ℝ) := by positivity
  have hC'1 : (0 : ℝ) ≤ (C' : ℝ) + 1 := by linarith
  have hlt0 : (0 : ℝ) ≤ lg ((t : ℝ) + 2) := by
    have h2 : (1 : ℝ) ≤ lg (((t + 2 : ℕ)) : ℝ) := d65_one_le_lg (by omega)
    have hcast : (((t + 2 : ℕ)) : ℝ) = (t : ℝ) + 2 := by push_cast; ring
    rw [hcast] at h2
    linarith
  have hln0 : (0 : ℝ) ≤ lg ((n : ℝ) + 2) := by
    have h2 : (1 : ℝ) ≤ lg (((n + 2 : ℕ)) : ℝ) := d65_one_le_lg (by omega)
    have hcast : (((n + 2 : ℕ)) : ℝ) = (n : ℝ) + 2 := by push_cast; ring
    rw [hcast] at h2
    linarith
  -- `lg n ≤ 5 exp(5 y²)`
  have hpow : lg (n : ℝ) ≤ 5 * Real.exp (5 * y ^ 2) := by
    have h := pow_lg_le_exp_le (Λ := 5) (by norm_num) (p := 1) (by norm_num) (by norm_num) hn
    simpa using h
  have he5 : (1 : ℝ) ≤ Real.exp (5 * y ^ 2) := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.2 (by positivity)
  -- `lg (n+2) ≤ 15 exp(5 y²)` and `lg (t+2) ≤ 15 exp(5 y²)`
  have hlg2 : lg ((n : ℝ) + 2) ≤ 15 * Real.exp (5 * y ^ 2) := by
    have h := lg_nat_add_two_le hn
    linarith
  have hlg3 : lg ((t : ℝ) + 2) ≤ 15 * Real.exp (5 * y ^ 2) := by
    have htn' : (t : ℝ) ≤ (n : ℝ) := by exact_mod_cast htn
    have ht2 : (t : ℝ) + 2 ≤ (n : ℝ) + 2 := by linarith
    have hpos : (0 : ℝ) < (t : ℝ) + 2 := by positivity
    have h := d65_lg_mono hpos ht2
    linarith
  -- `t ≤ 4 (C'+1) d exp(y²)`
  have hyt : (t : ℝ) ≤ 4 * (((C' : ℝ) + 1) * (d : ℝ)) * Real.exp (y ^ 2) := by
    have ht1 : (t : ℝ) ≤ (d : ℝ) * ((B : ℝ) + 1) := by
      have h : (t : ℝ) ≤ ((d * (B + 1) : ℕ) : ℝ) := by exact_mod_cast htd
      push_cast at h
      linarith
    have hB' : (d : ℝ) * ((B : ℝ) + 1) ≤ (d : ℝ) * (((C' : ℝ) + 1) * (y + 3)) :=
      mul_le_mul_of_nonneg_left hB (by linarith)
    have hy3 : y + 3 ≤ 4 * Real.exp (y ^ 2) := lg_lg_add_three_le hn
    have hstep : (d : ℝ) * (((C' : ℝ) + 1) * (y + 3)) ≤
        (d : ℝ) * (((C' : ℝ) + 1) * (4 * Real.exp (y ^ 2))) := by
      apply mul_le_mul_of_nonneg_left _ (by linarith)
      exact mul_le_mul_of_nonneg_left hy3 hC'1
    calc (t : ℝ) ≤ (d : ℝ) * ((B : ℝ) + 1) := ht1
      _ ≤ (d : ℝ) * (((C' : ℝ) + 1) * (y + 3)) := hB'
      _ ≤ (d : ℝ) * (((C' : ℝ) + 1) * (4 * Real.exp (y ^ 2))) := hstep
      _ = 4 * (((C' : ℝ) + 1) * (d : ℝ)) * Real.exp (y ^ 2) := by ring
  have he1 : (1 : ℝ) ≤ Real.exp (y ^ 2) := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.2 hy2
  -- the product bound
  have hX1 : (t : ℝ) * lg ((t : ℝ) + 2) ≤
      60 * (((C' : ℝ) + 1) * (d : ℝ)) * Real.exp (6 * y ^ 2) := by
    have hmul : (t : ℝ) * lg ((t : ℝ) + 2) ≤
        (4 * (((C' : ℝ) + 1) * (d : ℝ)) * Real.exp (y ^ 2)) * (15 * Real.exp (5 * y ^ 2)) :=
      mul_le_mul hyt hlg3 hlt0 (by positivity)
    have heq : (4 * (((C' : ℝ) + 1) * (d : ℝ)) * Real.exp (y ^ 2)) * (15 * Real.exp (5 * y ^ 2)) =
        60 * (((C' : ℝ) + 1) * (d : ℝ)) * Real.exp (6 * y ^ 2) := by
      have h : Real.exp (y ^ 2) * Real.exp (5 * y ^ 2) = Real.exp (6 * y ^ 2) := by
        rw [← Real.exp_add]
        congr 1
        ring
      calc (4 * (((C' : ℝ) + 1) * (d : ℝ)) * Real.exp (y ^ 2)) * (15 * Real.exp (5 * y ^ 2))
          = 60 * (((C' : ℝ) + 1) * (d : ℝ)) * (Real.exp (y ^ 2) * Real.exp (5 * y ^ 2)) := by ring
        _ = 60 * (((C' : ℝ) + 1) * (d : ℝ)) * Real.exp (6 * y ^ 2) := by rw [h]
    linarith [heq]
  have hX : (t : ℝ) * lg ((t : ℝ) + 2) * lg ((n : ℝ) + 2) ≤
      900 * (((C' : ℝ) + 1) * (d : ℝ)) * Real.exp (11 * y ^ 2) := by
    have hmul : (t : ℝ) * lg ((t : ℝ) + 2) * lg ((n : ℝ) + 2) ≤
        (60 * (((C' : ℝ) + 1) * (d : ℝ)) * Real.exp (6 * y ^ 2)) * (15 * Real.exp (5 * y ^ 2)) :=
      mul_le_mul hX1 hlg2 (by positivity) (by positivity)
    have heq : (60 * (((C' : ℝ) + 1) * (d : ℝ)) * Real.exp (6 * y ^ 2)) *
        (15 * Real.exp (5 * y ^ 2)) = 900 * (((C' : ℝ) + 1) * (d : ℝ)) * Real.exp (11 * y ^ 2) := by
      have h : Real.exp (6 * y ^ 2) * Real.exp (5 * y ^ 2) = Real.exp (11 * y ^ 2) := by
        rw [← Real.exp_add]
        congr 1
        ring
      calc (60 * (((C' : ℝ) + 1) * (d : ℝ)) * Real.exp (6 * y ^ 2)) *
            (15 * Real.exp (5 * y ^ 2))
          = 900 * (((C' : ℝ) + 1) * (d : ℝ)) * (Real.exp (6 * y ^ 2) * Real.exp (5 * y ^ 2)) := by
            ring
        _ = 900 * (((C' : ℝ) + 1) * (d : ℝ)) * Real.exp (11 * y ^ 2) := by rw [h]
    linarith [heq]
  -- `max 1 X ≤ 1 + X`
  have hmax : max 1 ((t : ℝ) * lg ((t : ℝ) + 2) * lg ((n : ℝ) + 2)) ≤
      1 + (t : ℝ) * lg ((t : ℝ) + 2) * lg ((n : ℝ) + 2) := by
    have h0 : (0 : ℝ) ≤ (t : ℝ) * lg ((t : ℝ) + 2) * lg ((n : ℝ) + 2) :=
      mul_nonneg (mul_nonneg (by positivity) hlt0) hln0
    apply max_le
    · linarith
    · linarith
  have he11 : (1 : ℝ) ≤ Real.exp (11 * y ^ 2) := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.2 (by positivity)
  have hexp11 : (0 : ℝ) < Real.exp (11 * y ^ 2) := Real.exp_pos _
  have hb1 : Kcr ≤ (901 * ((C' : ℝ) + 1) * Kcr) * (d : ℝ) * Real.exp (11 * y ^ 2) := by
    have h901 : (1 : ℝ) ≤ 901 * ((C' : ℝ) + 1) * (d : ℝ) * Real.exp (11 * y ^ 2) := by
      have h4 : (1 : ℝ) ≤ (901 * ((C' : ℝ) + 1)) * (d : ℝ) := by nlinarith
      calc (1 : ℝ) = 1 * 1 := by ring
        _ ≤ ((901 * ((C' : ℝ) + 1)) * (d : ℝ)) * Real.exp (11 * y ^ 2) :=
            mul_le_mul h4 he11 (by norm_num) (by linarith)
    calc Kcr = Kcr * 1 := by ring
      _ ≤ Kcr * (901 * ((C' : ℝ) + 1) * (d : ℝ) * Real.exp (11 * y ^ 2)) :=
          mul_le_mul_of_nonneg_left h901 hKcr
      _ = (901 * ((C' : ℝ) + 1) * Kcr) * (d : ℝ) * Real.exp (11 * y ^ 2) := by ring
  have hb2 : Kcr * ((t : ℝ) * lg ((t : ℝ) + 2) * lg ((n : ℝ) + 2)) ≤
      (901 * ((C' : ℝ) + 1) * Kcr) * (d : ℝ) * Real.exp (11 * y ^ 2) := by
    have hc : 900 * (((C' : ℝ) + 1) * (d : ℝ)) ≤ 901 * ((C' : ℝ) + 1) * (d : ℝ) := by
      nlinarith [hC'1, hd1]
    have hmono : 900 * (((C' : ℝ) + 1) * (d : ℝ)) * Real.exp (11 * y ^ 2) ≤
        901 * ((C' : ℝ) + 1) * (d : ℝ) * Real.exp (11 * y ^ 2) :=
      mul_le_mul_of_nonneg_right hc (le_of_lt hexp11)
    calc Kcr * ((t : ℝ) * lg ((t : ℝ) + 2) * lg ((n : ℝ) + 2))
        ≤ Kcr * (900 * (((C' : ℝ) + 1) * (d : ℝ)) * Real.exp (11 * y ^ 2)) :=
          mul_le_mul_of_nonneg_left hX hKcr
      _ ≤ Kcr * (901 * ((C' : ℝ) + 1) * (d : ℝ) * Real.exp (11 * y ^ 2)) :=
          mul_le_mul_of_nonneg_left hmono hKcr
      _ = (901 * ((C' : ℝ) + 1) * Kcr) * (d : ℝ) * Real.exp (11 * y ^ 2) := by ring
  have hmain : Kcr * max 1 ((t : ℝ) * lg ((t : ℝ) + 2) * lg ((n : ℝ) + 2)) ≤
      Kcr + Kcr * ((t : ℝ) * lg ((t : ℝ) + 2) * lg ((n : ℝ) + 2)) := by
    have h := mul_le_mul_of_nonneg_left hmax hKcr
    calc Kcr * max 1 ((t : ℝ) * lg ((t : ℝ) + 2) * lg ((n : ℝ) + 2))
        ≤ Kcr * (1 + (t : ℝ) * lg ((t : ℝ) + 2) * lg ((n : ℝ) + 2)) := h
      _ = Kcr + Kcr * ((t : ℝ) * lg ((t : ℝ) + 2) * lg ((n : ℝ) + 2)) := by ring
  have h2x : (901 * ((C' : ℝ) + 1) * Kcr) * (d : ℝ) * Real.exp (11 * y ^ 2) +
      (901 * ((C' : ℝ) + 1) * Kcr) * (d : ℝ) * Real.exp (11 * y ^ 2) =
      2 * ((901 * ((C' : ℝ) + 1) * Kcr) * (d : ℝ) * Real.exp (11 * y ^ 2)) := by ring
  have hfin : Kcr + Kcr * ((t : ℝ) * lg ((t : ℝ) + 2) * lg ((n : ℝ) + 2)) ≤
      1802 * ((C' : ℝ) + 1) * Kcr * (d : ℝ) * Real.exp (11 * y ^ 2) := by
    have hsplit : 1802 * ((C' : ℝ) + 1) * Kcr * (d : ℝ) * Real.exp (11 * y ^ 2) =
        (901 * ((C' : ℝ) + 1) * Kcr) * (d : ℝ) * Real.exp (11 * y ^ 2) +
        (901 * ((C' : ℝ) + 1) * Kcr) * (d : ℝ) * Real.exp (11 * y ^ 2) := by ring
    rw [hsplit]
    linarith [hb1, hb2]
  have hfin2 : Kcr + Kcr * ((t : ℝ) * lg ((t : ℝ) + 2) * lg ((n : ℝ) + 2)) ≤
      1802 * ((C' : ℝ) + 1) * Kcr * (d : ℝ) * Real.exp (11 * y ^ 2) := hfin
  calc Kcr * max 1 ((t : ℝ) * lg ((t : ℝ) + 2) * lg ((n : ℝ) + 2))
      ≤ Kcr + Kcr * ((t : ℝ) * lg ((t : ℝ) + 2) * lg ((n : ℝ) + 2)) := hmain
    _ ≤ 1802 * ((C' : ℝ) + 1) * Kcr * (d : ℝ) * Real.exp (11 * y ^ 2) := hfin2

/-! ### 13.7 The correctness half (conjunct 8), stated exactly

When all sub-decodes succeed, the output is `supp x`.  At the **abstract** level this is a statement
about `Node.decode` (`Definitions.Def_…_Framework`):

```lean
Node.decode CR T r (Node.sketch CR T r x) J = some x
```

and at the **machine** level it is `OutputsSupport s' x` for the state the top-level decoder halts in.
The assembly this section builds consumes exactly one bridge between the two:

* the row loop produces, for each row `j`, the recovered prefix `z_j ∈ ZMod 2 ^ ℓ` that
  `proposition_2_1` certifies (§13.4);
* the column loop consumes the hints `(P_s, J_s)` of Algorithm 2 and returns, per column, the child's
  support; `theorem_5_1`'s `OutputsSupport`/`prU` conjuncts are its contract;
* `Sassem` assembles `x̂` and `Sres` forms `a + CR x̂`; `proposition_2_3`'s `OutputsSupport` returns
  `e`, and the machine's output list is `x̂ + e`.

`TopDecCorrects` is that end-to-end statement, named and quantified over the very programs and stages
`TopDecRuns` fixes.  It is **not** proved here, and §13.8 records exactly what is missing. -/

/-- **The correctness half of Theorem 6.5's decoder (conjunct 8), named.**

For every `d`-sparse `x` and every seed whose six stages all succeed (`TopDecRuns` is uniform in the
seed, so "succeed" is: the run exists *and* the decoded lists are the right ones), the halted state's
`outList` is the support of `x`.  This is 6.5's `OutputsSupport s' x` conjunct made explicit as one
predicate over `(x, y, s')`. -/
def TopDecCorrects (Sinit Srow Sdec Sassem Sres Scr : Stmt) (E : RAMEnv) {n M : ℕ}
    (D : (Fin n → ZMod 2) → Fin M → ZMod 2) (Tdec : ℝ) : Prop :=
  ∀ (x : Fin n → ZMod 2) (s' : RAMState),
    (∃ k : ℕ, (k : ℝ) ≤ Tdec ∧
      (step (progDecOfTop Sinit Srow Sdec Sassem Sres Scr) E)^[k]
        (decoderStart E.W (D x) []) = s' ∧
      Halted (progDecOfTop Sinit Srow Sdec Sassem Sres Scr) s') →
    OutputsSupport s' x

/-- **Conjunct 7, assembled.**  `haltsWithin_topDec_shape` specialised to the `Λtot` that dominates
every exponent the six stages produce: `7C²e⁶+3` (the child loop), `pi`, `pr+1`, `pas`, `pres` (the
four polylogarithmic stages) and `11` (the `CR` stage). -/
theorem haltsWithin_topDec_final {Sinit Srow Sdec Sassem Sres Scr : Stmt} {E : RAMEnv}
    {W M n d ℓ t B : ℕ} {C Ci Cr Cas Cres Kcr Λtot : ℝ} {pi pr pas pres : ℕ} {C' : ℕ}
    {Tini Trow Tdec Tas Tres Tcr : ℝ}
    (h : TopDecRuns Sinit Srow Sdec Sassem Sres Scr E W M n d ℓ Tini Trow Tdec Tas Tres Tcr)
    (hini : Tini ≤ Ci * lg (n : ℝ) ^ pi)
    (hrow : Trow ≤ (Cr + 5) * (d : ℝ) * lg (n : ℝ) ^ (pr + 1))
    (hcol : Tdec ≤ (7 * C ^ 2 * Real.exp 6 + 3) * (d : ℝ) *
      Real.exp ((7 * C ^ 2 * Real.exp 6 + 3) * lg (lg (n : ℝ)) ^ 2))
    (has : Tas ≤ Cas * lg (n : ℝ) ^ pas) (hres : Tres ≤ Cres * lg (n : ℝ) ^ pres)
    (hcr : Tcr ≤ Kcr * max 1 ((t : ℝ) * lg ((t : ℝ) + 2) * lg ((n : ℝ) + 2)))
    (hCi : 0 ≤ Ci) (hCr : 0 ≤ Cr) (hCas : 0 ≤ Cas) (hCres : 0 ≤ Cres) (hKcr : 0 ≤ Kcr)
    (hC : 1 ≤ C) (hn : 2 ≤ n) (hd : 1 ≤ d) (htn : t ≤ n) (htd : t ≤ d * (B + 1))
    (hB : (B : ℝ) + 1 ≤ ((C' : ℝ) + 1) * (lg (lg (n : ℝ)) + 3))
    (hΛ1 : 1 ≤ Λtot) (hΛC : 7 * C ^ 2 * Real.exp 6 + 3 ≤ Λtot)
    (hΛpi : (2 : ℝ) ^ pi + (pi : ℝ) + 2 ≤ Λtot)
    (hΛpr : (2 : ℝ) ^ (pr + 1) + ((pr : ℝ) + 1) + 2 ≤ Λtot)
    (hΛpas : (2 : ℝ) ^ pas + (pas : ℝ) + 2 ≤ Λtot)
    (hΛpres : (2 : ℝ) ^ pres + (pres : ℝ) + 2 ≤ Λtot)
    (hΛ11 : 11 ≤ Λtot)
    (Cd : ℝ)
    (hCd : Cd = max Λtot (Ci * Λtot + (Cr + 5) * Λtot + (7 * C ^ 2 * Real.exp 6 + 3) +
      Cas * Λtot + Cres * Λtot + 1802 * ((C' : ℝ) + 1) * Kcr) + 1)
    (y : Fin M → ZMod 2) :
    ∃ s' : RAMState,
      HaltsWithin (progDecOfTop Sinit Srow Sdec Sassem Sres Scr) E
        (Cd * (d : ℝ) * Real.exp (Cd * lg (lg (n : ℝ)) ^ 2)) (decoderStart W y []) s' := by
  set y₂ : ℝ := lg (lg (n : ℝ)) with hy₂
  set Λ : ℝ := 7 * C ^ 2 * Real.exp 6 + 3 with hΛ
  set M : ℝ := Ci * Λtot + (Cr + 5) * Λtot + Λ + Cas * Λtot + Cres * Λtot +
    1802 * ((C' : ℝ) + 1) * Kcr with hM
  rw [hM] at hCd
  have hy2 : (0 : ℝ) ≤ y₂ ^ 2 := sq_nonneg y₂
  have hΛtot0 : (0 : ℝ) ≤ Λtot := le_trans zero_le_one hΛ1
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hd0 : (0 : ℝ) ≤ (d : ℝ) := by positivity
  have hexpΛ : (0 : ℝ) < Real.exp (Λtot * y₂ ^ 2) := Real.exp_pos _
  have hexpΛ0 : (0 : ℝ) ≤ Real.exp (Λtot * y₂ ^ 2) := le_of_lt hexpΛ
  have hpi : (pi : ℝ) ≤ Λtot := by
    have h0 : (0 : ℝ) ≤ (2 : ℝ) ^ pi := by positivity
    linarith
  have hpi2 : (2 : ℝ) ^ pi ≤ Λtot := by
    have h0 : (0 : ℝ) ≤ (pi : ℝ) := by positivity
    linarith
  have hpr : ((pr + 1 : ℕ) : ℝ) ≤ Λtot := by
    push_cast
    have h0 : (0 : ℝ) ≤ (2 : ℝ) ^ (pr + 1) := by positivity
    linarith
  have hpr2 : (2 : ℝ) ^ (pr + 1) ≤ Λtot := by
    linarith [hΛpr]
  have hpas : (pas : ℝ) ≤ Λtot := by
    have h0 : (0 : ℝ) ≤ (2 : ℝ) ^ pas := by positivity
    linarith
  have hpas2 : (2 : ℝ) ^ pas ≤ Λtot := by
    have h0 : (0 : ℝ) ≤ (pas : ℝ) := by positivity
    linarith
  have hpres : (pres : ℝ) ≤ Λtot := by
    have h0 : (0 : ℝ) ≤ (2 : ℝ) ^ pres := by positivity
    linarith
  have hpres2 : (2 : ℝ) ^ pres ≤ Λtot := by
    have h0 : (0 : ℝ) ≤ (pres : ℝ) := by positivity
    linarith
  -- the six stage bounds, all in `Λtot`-exponent shape
  have hΛ0 : (0 : ℝ) ≤ Λ := by rw [hΛ]; positivity
  have e1 : Tini ≤ Ci * Λtot * (d : ℝ) * Real.exp (Λtot * y₂ ^ 2) := by
    have hp := pow_lg_le_exp_le hΛ1 hpi hpi2 hn
    have h1 : Tini ≤ Ci * (Λtot * Real.exp (Λtot * y₂ ^ 2)) :=
      le_trans hini (mul_le_mul_of_nonneg_left hp hCi)
    have h0 : (0 : ℝ) ≤ Ci * Λtot * Real.exp (Λtot * y₂ ^ 2) :=
      mul_nonneg (mul_nonneg hCi hΛtot0) (le_of_lt hexpΛ)
    have h := mul_le_mul_of_nonneg_left hd1 h0
    calc Tini ≤ Ci * (Λtot * Real.exp (Λtot * y₂ ^ 2)) := h1
      _ = Ci * Λtot * Real.exp (Λtot * y₂ ^ 2) := by ring
      _ = (Ci * Λtot * Real.exp (Λtot * y₂ ^ 2)) * 1 := by ring
      _ ≤ (Ci * Λtot * Real.exp (Λtot * y₂ ^ 2)) * (d : ℝ) := h
      _ = Ci * Λtot * (d : ℝ) * Real.exp (Λtot * y₂ ^ 2) := by ring
  have e2 : Trow ≤ (Cr + 5) * (d : ℝ) * Λtot * Real.exp (Λtot * y₂ ^ 2) := by
    have hp := pow_lg_le_exp_le hΛ1 hpr hpr2 hn
    have h1 : (Cr + 5) * (d : ℝ) * lg (n : ℝ) ^ (pr + 1) ≤
        (Cr + 5) * (d : ℝ) * (Λtot * Real.exp (Λtot * y₂ ^ 2)) :=
      mul_le_mul_of_nonneg_left hp
        (mul_nonneg (by linarith : (0 : ℝ) ≤ Cr + 5) hd0)
    calc Trow ≤ (Cr + 5) * (d : ℝ) * lg (n : ℝ) ^ (pr + 1) := hrow
      _ ≤ (Cr + 5) * (d : ℝ) * (Λtot * Real.exp (Λtot * y₂ ^ 2)) := h1
      _ = (Cr + 5) * (d : ℝ) * Λtot * Real.exp (Λtot * y₂ ^ 2) := by ring
  have e3 : Tdec ≤ Λ * (d : ℝ) * Real.exp (Λtot * y₂ ^ 2) := by
    have hexp : Real.exp (Λ * y₂ ^ 2) ≤ Real.exp (Λtot * y₂ ^ 2) := by
      apply Real.exp_le_exp.2
      nlinarith [hy2, hΛC]
    have h1 : Λ * (d : ℝ) * Real.exp (Λ * y₂ ^ 2) ≤ Λ * (d : ℝ) * Real.exp (Λtot * y₂ ^ 2) :=
      mul_le_mul_of_nonneg_left hexp (mul_nonneg hΛ0 hd0)
    calc Tdec ≤ Λ * (d : ℝ) * Real.exp (Λ * y₂ ^ 2) := hcol
      _ ≤ Λ * (d : ℝ) * Real.exp (Λtot * y₂ ^ 2) := h1
  have e4 : Tas ≤ Cas * Λtot * (d : ℝ) * Real.exp (Λtot * y₂ ^ 2) := by
    have hp := pow_lg_le_exp_le hΛ1 hpas hpas2 hn
    have h1 : Tas ≤ Cas * (Λtot * Real.exp (Λtot * y₂ ^ 2)) :=
      le_trans has (mul_le_mul_of_nonneg_left hp hCas)
    have h0 : (0 : ℝ) ≤ Cas * Λtot * Real.exp (Λtot * y₂ ^ 2) :=
      mul_nonneg (mul_nonneg hCas hΛtot0) (le_of_lt hexpΛ)
    have h3 := mul_le_mul_of_nonneg_left hd1 h0
    calc Tas ≤ Cas * (Λtot * Real.exp (Λtot * y₂ ^ 2)) := h1
      _ = Cas * Λtot * Real.exp (Λtot * y₂ ^ 2) := by ring
      _ = (Cas * Λtot * Real.exp (Λtot * y₂ ^ 2)) * 1 := by ring
      _ ≤ (Cas * Λtot * Real.exp (Λtot * y₂ ^ 2)) * (d : ℝ) := h3
      _ = Cas * Λtot * (d : ℝ) * Real.exp (Λtot * y₂ ^ 2) := by ring
  have e5 : Tres ≤ Cres * Λtot * (d : ℝ) * Real.exp (Λtot * y₂ ^ 2) := by
    have hp := pow_lg_le_exp_le hΛ1 hpres hpres2 hn
    have h1 : Tres ≤ Cres * (Λtot * Real.exp (Λtot * y₂ ^ 2)) :=
      le_trans hres (mul_le_mul_of_nonneg_left hp hCres)
    have h0 : (0 : ℝ) ≤ Cres * Λtot * Real.exp (Λtot * y₂ ^ 2) :=
      mul_nonneg (mul_nonneg hCres hΛtot0) (le_of_lt hexpΛ)
    have h3 := mul_le_mul_of_nonneg_left hd1 h0
    calc Tres ≤ Cres * (Λtot * Real.exp (Λtot * y₂ ^ 2)) := h1
      _ = Cres * Λtot * Real.exp (Λtot * y₂ ^ 2) := by ring
      _ = (Cres * Λtot * Real.exp (Λtot * y₂ ^ 2)) * 1 := by ring
      _ ≤ (Cres * Λtot * Real.exp (Λtot * y₂ ^ 2)) * (d : ℝ) := h3
      _ = Cres * Λtot * (d : ℝ) * Real.exp (Λtot * y₂ ^ 2) := by ring
  have e6 : Tcr ≤ (1802 * ((C' : ℝ) + 1) * Kcr) * (d : ℝ) * Real.exp (Λtot * y₂ ^ 2) := by
    have hc : Tcr ≤ (1802 * ((C' : ℝ) + 1) * Kcr) * (d : ℝ) * Real.exp (11 * y₂ ^ 2) :=
      le_trans hcr (by simpa only [hy₂] using cr_time_shape hKcr hn hd htn htd hB)
    have hexp : Real.exp (11 * y₂ ^ 2) ≤ Real.exp (Λtot * y₂ ^ 2) := by
      apply Real.exp_le_exp.2
      nlinarith [hy2, hΛ11]
    have hK0 : (0 : ℝ) ≤ (1802 * ((C' : ℝ) + 1) * Kcr) * (d : ℝ) := by
      have h2' : (0 : ℝ) ≤ 1802 * ((C' : ℝ) + 1) := by positivity
      exact mul_nonneg (mul_nonneg h2' hKcr) hd0
    have h1 : (1802 * ((C' : ℝ) + 1) * Kcr) * (d : ℝ) * Real.exp (11 * y₂ ^ 2) ≤
        (1802 * ((C' : ℝ) + 1) * Kcr) * (d : ℝ) * Real.exp (Λtot * y₂ ^ 2) :=
      mul_le_mul_of_nonneg_left hexp hK0
    calc Tcr ≤ (1802 * ((C' : ℝ) + 1) * Kcr) * (d : ℝ) * Real.exp (11 * y₂ ^ 2) := hc
      _ ≤ (1802 * ((C' : ℝ) + 1) * Kcr) * (d : ℝ) * Real.exp (Λtot * y₂ ^ 2) := h1
  -- the sum
  have hsum : Tini + Trow + Tdec + Tas + Tres + Tcr ≤
      M * (d : ℝ) * Real.exp (Λtot * y₂ ^ 2) := by
    have hcomb : Ci * Λtot * (d : ℝ) * Real.exp (Λtot * y₂ ^ 2) +
        (Cr + 5) * (d : ℝ) * Λtot * Real.exp (Λtot * y₂ ^ 2) +
        Λ * (d : ℝ) * Real.exp (Λtot * y₂ ^ 2) +
        Cas * Λtot * (d : ℝ) * Real.exp (Λtot * y₂ ^ 2) +
        Cres * Λtot * (d : ℝ) * Real.exp (Λtot * y₂ ^ 2) +
        (1802 * ((C' : ℝ) + 1) * Kcr) * (d : ℝ) * Real.exp (Λtot * y₂ ^ 2) =
        M * (d : ℝ) * Real.exp (Λtot * y₂ ^ 2) := by
      rw [hM]
      ring
    linarith [e1, e2, e3, e4, e5, e6, hcomb]
  -- `M ≤ Cd`, `Λtot ≤ Cd`
  have hMCd : M ≤ Cd := by
    rw [hCd]
    have := le_max_right Λtot M
    linarith
  have hΛCd : Λtot ≤ Cd := by
    rw [hCd]
    have := le_max_left Λtot M
    linarith
  have hCd0 : (0 : ℝ) < Cd := by
    have h1 : (0 : ℝ) < max Λtot M + 1 := by
      have := le_max_left Λtot M
      linarith
    rwa [hCd]
  have hECd : Real.exp (Λtot * y₂ ^ 2) ≤ Real.exp (Cd * y₂ ^ 2) := by
    apply Real.exp_le_exp.2
    nlinarith [hy2, hΛCd]
  have hfinal : M * (d : ℝ) * Real.exp (Λtot * y₂ ^ 2) ≤
      Cd * (d : ℝ) * Real.exp (Cd * y₂ ^ 2) := by
    have h1 : M * (d : ℝ) ≤ Cd * (d : ℝ) := mul_le_mul_of_nonneg_right hMCd hd0
    calc M * (d : ℝ) * Real.exp (Λtot * y₂ ^ 2)
        ≤ Cd * (d : ℝ) * Real.exp (Λtot * y₂ ^ 2) :=
          mul_le_mul_of_nonneg_right h1 (le_of_lt hexpΛ)
      _ ≤ Cd * (d : ℝ) * Real.exp (Cd * y₂ ^ 2) :=
          mul_le_mul_of_nonneg_left hECd (mul_nonneg (le_of_lt hCd0) hd0)
  have htotal : Tini + Trow + Tdec + Tas + Tres + Tcr ≤ Cd * (d : ℝ) * Real.exp (Cd * y₂ ^ 2) :=
    le_trans hsum hfinal
  have htotal' : Tini + Trow + Tdec + Tas + Tres + Tcr ≤
      Cd * (d : ℝ) * Real.exp (Cd * lg (lg (n : ℝ)) ^ 2) := by
    rw [← hy₂]
    exact htotal
  obtain ⟨s', hs'⟩ := haltsWithin_topDec_of_runs h y
  obtain ⟨k, hk, hstep, hhalt⟩ := hs'
  exact ⟨s', k, le_trans hk htotal', hstep, hhalt⟩


end LinearSetReconciliation327.Main


