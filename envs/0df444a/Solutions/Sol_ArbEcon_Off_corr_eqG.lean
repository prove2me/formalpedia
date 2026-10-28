-- Prove2me | solution 1 for ArbEcon.Off.corr_eqG
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:46:08.600194+00:00
-- url     : https://prove2.me/submissions/1e55e746-4a90-4c86-a020-35614fd3cb13

import Definitions.Def_ArdaRH65K_Probes_ArbEconomics_Sound
import Definitions.Def_ArdaRH65K_Turing121_EMZeta
import Definitions.Def_ArdaRH65K_Turing121_EMZetaComplex
import Definitions.Def_ArdaRH65K_Turing121_EMZetaHigh
import Definitions.Def_ArdaRH65K_Turing121_EMZetaHighCheck
import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineCheck
import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineCore
import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineEval
import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineSound
import Definitions.Def_ArdaRH65K_Turing121_EMZetaTail
import Definitions.Def_ArdaRH65K_Turing121_Probes_ArbEconomics_Zeta
import Definitions.Def_ArdaRS_Arithmetic
import Definitions.Def_ArdaRS_Config64
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Tactic.IntervalCases
namespace ArbEcon
end ArbEcon
namespace ArbEcon.OrderK
end ArbEcon.OrderK
namespace ZetaReflection
end ZetaReflection
namespace ZetaReflection.EMHigh
end ZetaReflection.EMHigh
/-  EMZetaHigh.lean -- the GENERAL-ORDER Euler-Maclaurin representation of ζ with an explicit,
    PROVED remainder bound (lane emhigh, memo ANDURIL_ARB_DISCHARGE_2026-09-23 section 3 / step 2
    node `AND_em_zeta_orderK`).

    The island's order-3 chain (`EMZetaTail.em_zeta_strip3`) stops at the saw-3 remainder.  This
    file raises the order to ANY `m ≥ 1` by induction, so the finite part carries every Bernoulli
    correction `B_2, B_4, …, B_{2K}` and the remainder decays like `N^{-(Re s + 2K - 1)}`:

      M1.  `poch`, `emC`            -- rising factorial `s(s+1)…(s+k-1)` and the k-th x-derivative
                                       coefficient `(-1)^k (s)_k` of `x^{-s}`.
      M2.  `em_tail_step`           -- ONE saw-order-raising step on the tail `[N, ∞)`, any k ≥ 1
                                       (generalises `EMZetaTail.em_tail2_step` / `em_tail3_step`).
      M3.  `emTail_unroll`          -- the induction: the saw-1 tail equals the explicit Bernoulli
                                       sum plus `(-1)^(m-1) emTail m / m!`.
      M4.  `em_zeta_order`          -- the general-order identity for `riemannZeta` on `Re s > 0`.
      M5.  `emTail_norm_le`         -- remainder bound from any sup bound of the order-m saw.
      M6.  `abs_sawBernoulli_even_le` -- `|B̃_{2K}(x)| ≤ |B_{2K}|` for every K ≥ 1 (Mathlib's
                                       Fourier cosine series of the Bernoulli polynomials).
      M6'. `abs_sawBernoulli_odd_le`  -- `|B̃_{2K+1}(x)| ≤ 2(2K+1)!/(2π)^{2K+1} (1 + (π²/6−1)/2^{2K−1})`
                                       (Fourier sine series + `ζ(p) ≤ 1 + (π²/6−1)/2^{p−2}`).
      M7.  `em_zeta_orderK_enclosure` -- THE THEOREM (general K), even-saw remainder:
             ‖ζ(s) − emFinite K s N‖ ≤ |B_{2K}|/(2K)! · ‖(s)_{2K}‖ · N^{-(σ+2K-1)}/(σ+2K-1),
           and `em_zeta_orderK_enclosure_odd`, the same finite part with the saw-(2K+1) remainder
             ‖ζ(s) − emFinite K s N‖ ≤ 2(1+(π²/6−1)/2^{2K−1})/(2π)^{2K+1} · ‖(s)_{2K+1}‖ · N^{-(σ+2K)}/(σ+2K)
           (smaller by about `|s+2K|/(2πN)`), with the evaluator-facing Dirichlet form
           `emFinite = Σ_{n<N} n^{-s} + N^{-s}·emCorr`; `em_line_remainder_le` / `_odd_le` are the
           critical-line forms with a rational majorant `Q` of the Pochhammer norm and `r ≤ √N`.
      M8.  exact Bernoulli numbers `B_2 … B_12` (the K ≤ 6 constants).

    conjecture1_proved = False.  A classical analysis lemma (Euler-Maclaurin), not a proof of RH.
-/



open MeasureTheory intervalIntegral Set Filter Topology Complex
open scoped Real Nat

namespace ZetaReflection

namespace EMHigh

/-! ## M1. Rising factorial and the derivative coefficients of `x^{-s}`. -/



















/-! ## M2. The general saw-order-raising step on the tail `[N, ∞)`. -/









/-! ## M3. The induction: unrolling the saw-1 tail to any order. -/





/-! ## M4. The general-order identity for `riemannZeta`. -/





/-! ## M5. The remainder bound from a sup bound of the order-m saw. -/



/-! ## M6. The sup bound `|B̃_{2K}(x)| ≤ |B_{2K}|` (general K ≥ 1). -/





/-! ## M6'. The odd sup bound `|B̃_{2K+1}(x)| ≤ 2 (2K+1)! ζ(2K+1) / (2π)^{2K+1}` (general K ≥ 1),
    with the elementary majorant `ζ(p) ≤ 1 + (π²/6 − 1)/2^(p−2)`. -/







/-! ## M7. THE THEOREM: general-K enclosure, evaluator (Dirichlet) form. -/













/-! ## M7'. The critical line: rational remainder and real/imaginary parts of the correction. -/











/-! ## M7''. Real and imaginary parts of the correction factor on a vertical line. -/













/-! ## M8. The exact Bernoulli numbers `B_2 … B_12` (the constants of K ≤ 6). -/

theorem bernoulli'_five : bernoulli' 5 = 0 := bernoulli'_eq_zero_of_odd (by decide) (by norm_num)
theorem bernoulli'_seven : bernoulli' 7 = 0 := bernoulli'_eq_zero_of_odd (by decide) (by norm_num)
theorem bernoulli'_nine : bernoulli' 9 = 0 := bernoulli'_eq_zero_of_odd (by decide) (by norm_num)
theorem bernoulli'_eleven : bernoulli' 11 = 0 := bernoulli'_eq_zero_of_odd (by decide) (by norm_num)

theorem bernoulli'_six : bernoulli' 6 = 1 / 42 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, Nat.choose, bernoulli'_five]

theorem bernoulli'_eight : bernoulli' 8 = -1 / 30 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, Nat.choose, bernoulli'_five, bernoulli'_six, bernoulli'_seven]

theorem bernoulli'_ten : bernoulli' 10 = 5 / 66 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, Nat.choose, bernoulli'_five, bernoulli'_six, bernoulli'_seven,
    bernoulli'_eight, bernoulli'_nine]

theorem bernoulli'_twelve : bernoulli' 12 = -691 / 2730 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, Nat.choose, bernoulli'_five, bernoulli'_six, bernoulli'_seven,
    bernoulli'_eight, bernoulli'_nine, bernoulli'_ten, bernoulli'_eleven]

theorem bernoulli_four' : bernoulli 4 = -1 / 30 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by decide), bernoulli'_four]
theorem bernoulli_six' : bernoulli 6 = 1 / 42 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by decide), bernoulli'_six]
theorem bernoulli_eight' : bernoulli 8 = -1 / 30 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by decide), bernoulli'_eight]
theorem bernoulli_ten' : bernoulli 10 = 5 / 66 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by decide), bernoulli'_ten]
theorem bernoulli_twelve' : bernoulli 12 = -691 / 2730 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by decide), bernoulli'_twelve]

/-- The odd Bernoulli numbers `B_3, …, B_13` vanish. -/
theorem bernoulli_odd_vanish :
    bernoulli 3 = 0 ∧ bernoulli 5 = 0 ∧ bernoulli 7 = 0 ∧ bernoulli 9 = 0 ∧ bernoulli 11 = 0 ∧
      bernoulli 13 = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> exact bernoulli_eq_zero_of_odd (by decide) (by norm_num)

end EMHigh

end ZetaReflection


/-  EMZetaHighCheck.lean -- a KERNEL-ONLY assembly for the order-(2K+1) Euler-Maclaurin enclosure
    of ζ(1/2 + i t) (lane emhigh, production format).

    `EMZetaHighEval.zetaK_re_bounds` turns the evaluator invariants into Re/Im ζ bounds, but an
    instance then discharges its rational side conditions (the correction factor `B_K(t, N)`, the
    remainder constant, the final inequalities) with `norm_num` on 60-digit rationals: about 3 s of
    tactic interpretation and 1.3 MB of proof term per evaluation.  At the h280000 scale (445,947
    sign evaluations) that is about 400 core-hours of elaboration and 0.6 TB of oleans.

    This file replaces all of it by ONE Boolean checker `checkK`, run by `decide +kernel`, over plain
    `Nat`/`Int` arithmetic, and ONE soundness theorem `checkK_sound`, proved once:
      * `valid64`                  -- the P = 64 evaluator configuration `EMZetaHighCfg64.cfg64`
                                      (lnbig = sqbig = 256) as a function of the height `t = tn / 2^tq`,
                                      validated ONCE for all heights (no per-instance `norm_num`).
      * `betaN`, `Lbeta`, `betaN_spec` -- `B_{i+2}/(i+2)! = betaN i / Lβ`, `Lβ = 2730·12!`, `i ≤ 10`.
      * `gpoch`, `pochRI_eq_gpoch`  -- the Gaussian-integer rising factorial `(2u)^k (1/2 + i tn/u)_k`.
      * `corrData`, `corr_eq`       -- the exact correction factor `emCorr K (1/2 + i t) N` as
                                      `(BreN + i BimN) / BD` with integers computed in the kernel.
      * `pnK`, `pochNormSq_eq_pnK`  -- the remainder numerator `Π_{j<k} ((2j+1)² u² + 4 tn²)`.
      * `remEven`, `remOdd` (+ `_sound`) -- the remainder as `EN/ED` in integers, even-saw
                                      (`em_line_remainder_le`) or odd-saw (`em_line_remainder_odd_le`,
                                      π replaced by `3.141592 < π < 3.141593`, about 7 percent fewer terms).
      * `checkCore`, `checkCore_sound` -- the four final inequalities for ANY remainder `EN/ED`.
      * `checkK`, `checkK_sound`    -- the checker (`odd` flag) and its soundness: `checkK … = true`
                                      gives `reLo/D ≤ Re ζ(1/2+it) ≤ reHi/D` and the same for Im.

    conjecture1_proved = False.  Finite interval arithmetic; nothing here is about RH.
-/



open Complex ZetaReflection ZetaReflection.EMHigh
open scoped Nat Real

namespace ArbEcon

namespace OrderK

/-! ## A. The P = 64 configuration (`EMZetaHighCfg64.cfg64`), validated once for every height. -/



/-! ## B. Bernoulli data over one common denominator. -/





theorem betaN_spec (i : ℕ) (hi : i ≤ 10) :
    (bernoulli (i + 2) : ℝ) / ((i + 2)! : ℝ) = (betaN i : ℝ) / (Lbeta : ℝ) := by
  obtain ⟨h3, h5, h7, h9, h11, _⟩ := bernoulli_odd_vanish
  interval_cases i <;>
    simp [betaN, Lbeta, Nat.factorial, bernoulli_two, bernoulli_four', bernoulli_six',
      bernoulli_eight', bernoulli_ten', bernoulli_twelve', h3, h5, h7, h9, h11] <;> norm_num

/-! ## C. The correction factor in exact integer arithmetic. -/















/-! ## D. The remainder numerator. -/





/-! ## E. The remainder certificates (even and odd saw forms). -/









/-! ## F. The checker and its soundness. -/











end OrderK

end ArbEcon


/-  EMZetaOfflineCheck.lean -- lane offline: the KERNEL-ONLY assembly of an order-(2K+1)
    Euler-Maclaurin enclosure of ζ(σ + i t) at a rational `σ = (a - b)/q` (any sign, `σ > -2K`) and a
    dyadic `t = tn / 2^tq > 0`.

      * `gpochG`, `pochRI_eq_gpochG`  -- the Gaussian-integer rising factorial
                                         `(q u)^k (σ + i t)_k` (`u = 2^tq`);
      * `corrDataG`, `corr_eqG`       -- the exact correction factor `emCorr K (σ + i t) N` as
                                         `(BreN + i BimN) / BD` in integers;
      * `pnG`, `pochNormSq_eq_pnG`    -- the remainder numerator `Π_{j<k} ((sN + j q)² u² + tn² q²)`;
      * `rpow_neg_le_of_pow`          -- `N^(-σ) ≤ Rn/Rd` from `Rd^q N^b ≤ Rn^q N^a`;
      * `remOddG`, `remOddG_sound`    -- the odd-saw remainder of `EMOff.em_zeta_orderK_enclosure_odd_ext`
                                         (valid off the line, `σ > -2K`) as `EN/ED`;
      * `zeta_ballG`                  -- the evaluator balls after `N-1` and `N` terms plus any remainder
                                         bound give balls for `Re ζ(s)`, `Im ζ(s)`;
      * `checkG`, `checkG_sound`      -- ONE Boolean checker (run by `decide +kernel`) and its
                                         soundness: `lo/D ≤ Re ζ(σ + i t) ≤ hi/D`, same for `Im`.

    conjecture1_proved = False.  Finite interval arithmetic at one point; nothing about RH.
-/




open Complex ZetaReflection ZetaReflection.EMHigh
open scoped Nat Real

namespace ArbEcon

namespace Off

open ArbEcon.OrderK (betaN Lbeta betaN_spec )

/-! ## A. The Gaussian-integer rising factorial at `σ = sN/q`, `t = tn/u`. -/



theorem gpochG_succ (sN : ℤ) (q u tn k : ℕ) :
    gpochG sN q u tn (k + 1) =
      ((gpochG sN q u tn k).1 * ((sN + k * q) * u) - (gpochG sN q u tn k).2 * (tn * q),
       (gpochG sN q u tn k).1 * (tn * q) + (gpochG sN q u tn k).2 * ((sN + k * q) * u)) := by
  show (match gpochG sN q u tn k with
    | (x, y) => (x * ((sN + k * q) * u) - y * (tn * q), x * (tn * q) + y * ((sN + k * q) * u))) = _
  rcases gpochG sN q u tn k with ⟨x, y⟩
  rfl

theorem pochRI_eq_gpochG (sN : ℤ) (q u tn : ℕ) (hq : 0 < q) (hu : 0 < u) (σ t : ℝ)
    (hσ : σ = (sN : ℝ) / q) (ht : t = (tn : ℝ) / u) (k : ℕ) :
    (pochRI σ t k).1 = ((gpochG sN q u tn k).1 : ℝ) / ((q : ℝ) * u) ^ k ∧
    (pochRI σ t k).2 = ((gpochG sN q u tn k).2 : ℝ) / ((q : ℝ) * u) ^ k := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have huR : (0 : ℝ) < u := by exact_mod_cast hu
  induction k with
  | zero => simp [pochRI, gpochG]
  | succ k ih =>
    obtain ⟨h1, h2⟩ := ih
    rw [gpochG_succ]
    simp only [pochRI]
    rw [h1, h2, hσ, ht]
    push_cast
    have hne : ((q : ℝ) * u) ^ k ≠ 0 := by positivity
    constructor <;> field_simp <;> ring



theorem gsumG_eq (sN : ℤ) (q u tn : ℕ) (W : ℤ) (M j : ℕ) :
    ((gsumG sN q u tn W M j).1 : ℝ)
        = ∑ i ∈ Finset.range j, (betaN i : ℝ) * ((gpochG sN q u tn (i + 1)).1 : ℝ) * (W : ℝ) ^ (M - 1 - i) ∧
    ((gsumG sN q u tn W M j).2 : ℝ)
        = ∑ i ∈ Finset.range j, (betaN i : ℝ) * ((gpochG sN q u tn (i + 1)).2 : ℝ) * (W : ℝ) ^ (M - 1 - i) := by
  induction j with
  | zero => simp [gsumG]
  | succ j ih =>
    obtain ⟨h1, h2⟩ := ih
    simp only [gsumG, Finset.sum_range_succ]
    push_cast
    rw [h1, h2]
    exact ⟨rfl, rfl⟩





/-! ## B. The remainder numerator and `N^(-σ)`. -/







/-! ## C. The odd-saw remainder certificate, off the line. -/





/-! ## D. The ball: evaluator invariants + remainder + correction factor. -/







/-! ## E. The kernel checker and its soundness. -/











end Off

end ArbEcon


/-  EMZetaOfflineCheck.lean -- lane offline: the KERNEL-ONLY assembly of an order-(2K+1)
    Euler-Maclaurin enclosure of ζ(σ + i t) at a rational `σ = (a - b)/q` (any sign, `σ > -2K`) and a
    dyadic `t = tn / 2^tq > 0`.

      * `gpochG`, `pochRI_eq_gpochG`  -- the Gaussian-integer rising factorial
                                         `(q u)^k (σ + i t)_k` (`u = 2^tq`);
      * `corrDataG`, `corr_eqG`       -- the exact correction factor `emCorr K (σ + i t) N` as
                                         `(BreN + i BimN) / BD` in integers;
      * `pnG`, `pochNormSq_eq_pnG`    -- the remainder numerator `Π_{j<k} ((sN + j q)² u² + tn² q²)`;
      * `rpow_neg_le_of_pow`          -- `N^(-σ) ≤ Rn/Rd` from `Rd^q N^b ≤ Rn^q N^a`;
      * `remOddG`, `remOddG_sound`    -- the odd-saw remainder of `EMOff.em_zeta_orderK_enclosure_odd_ext`
                                         (valid off the line, `σ > -2K`) as `EN/ED`;
      * `zeta_ballG`                  -- the evaluator balls after `N-1` and `N` terms plus any remainder
                                         bound give balls for `Re ζ(s)`, `Im ζ(s)`;
      * `checkG`, `checkG_sound`      -- ONE Boolean checker (run by `decide +kernel`) and its
                                         soundness: `lo/D ≤ Re ζ(σ + i t) ≤ hi/D`, same for `Im`.

    conjecture1_proved = False.  Finite interval arithmetic at one point; nothing about RH.
-/




open Complex ZetaReflection ZetaReflection.EMHigh
open scoped Nat Real

section
namespace ArbEcon
end ArbEcon
open ArbEcon

section
namespace ArbEcon.Off
end ArbEcon.Off
open ArbEcon.Off

open ArbEcon.OrderK (betaN Lbeta betaN_spec )

/-! ## A. The Gaussian-integer rising factorial at `σ = sN/q`, `t = tn/u`. -/













theorem solution (K : ℕ) (sN : ℤ) (q u tn N : ℕ) (hK1 : 1 ≤ K) (hK6 : K ≤ 6) (hq : 0 < q)
    (hu : 0 < u) (htn : 0 < tn) (hN : 1 ≤ N) (σ t : ℝ) (hσ : σ = (sN : ℝ) / q)
    (ht : t = (tn : ℝ) / u) :
    emCorrRe K σ t N = ((corrDataG K sN q u tn N).1 : ℝ) / ((corrDataG K sN q u tn N).2.2 : ℝ) ∧
    emCorrIm K σ t N = ((corrDataG K sN q u tn N).2.1 : ℝ) / ((corrDataG K sN q u tn N).2.2 : ℝ) := by
  set M := 2 * K - 1 with hM
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have huR : (0 : ℝ) < u := by exact_mod_cast hu
  have htnR : (0 : ℝ) < tn := by exact_mod_cast htn
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hWR : (0 : ℝ) < (q : ℝ) * u * N := by positivity
  have hq2 : (0 : ℝ) < ((sN : ℝ) - q) ^ 2 * (u : ℝ) ^ 2 + (tn : ℝ) ^ 2 * (q : ℝ) ^ 2 := by positivity
  have hL : (0 : ℝ) < (Lbeta : ℝ) := by norm_num [Lbeta]
  obtain ⟨hS1, hS2⟩ := gsumG_eq sN q u tn ((q : ℤ) * u * N) M M
  have key : ∀ (sel : ℕ → ℤ) (p : ℕ → ℝ),
      (∀ i, i < M → p (i + 1) = (sel (i + 1) : ℝ) / ((q : ℝ) * u) ^ (i + 1)) →
      (∑ i ∈ Finset.range M,
          (bernoulli (i + 2) : ℝ) / ((i + 2)! : ℝ) / (N : ℝ) ^ (i + 1) * p (i + 1))
        = (∑ i ∈ Finset.range M, (betaN i : ℝ) * (sel (i + 1) : ℝ)
            * ((((q : ℤ) * u * N : ℤ)) : ℝ) ^ (M - 1 - i))
            / ((Lbeta : ℝ) * ((((q : ℤ) * u * N : ℤ)) : ℝ) ^ M) := by
    intro sel p hp
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i hi
    have hiM : i < M := Finset.mem_range.mp hi
    have hi10 : i ≤ 10 := by omega
    rw [betaN_spec i hi10, hp i hiM]
    push_cast
    have hpow : ((q : ℝ) * u * N) ^ M = ((q : ℝ) * u * N) ^ (M - 1 - i) * ((q : ℝ) * u * N) ^ (i + 1) := by
      rw [← pow_add]; congr 1; omega
    rw [hpow]
    have h1 : ((q : ℝ) * u * N) ^ (M - 1 - i) ≠ 0 := by positivity
    have h2 : ((q : ℝ) * u) ^ (i + 1) ≠ 0 := by positivity
    have h3 : (N : ℝ) ^ (i + 1) ≠ 0 := by positivity
    rw [mul_pow ((q : ℝ) * u) (N : ℝ)]
    field_simp
    ring
  have hpR := fun i (_ : i < M) => (pochRI_eq_gpochG sN q u tn hq hu σ t hσ ht (i + 1)).1
  have hpI := fun i (_ : i < M) => (pochRI_eq_gpochG sN q u tn hq hu σ t hσ ht (i + 1)).2
  have kR := key (fun k => (gpochG sN q u tn k).1) (fun k => (pochRI σ t k).1) hpR
  have kI := key (fun k => (gpochG sN q u tn k).2) (fun k => (pochRI σ t k).2) hpI
  constructor
  · simp only [emCorrRe]
    rw [← hM, kR]
    simp only [corrDataG]
    rw [← hM]
    push_cast at hS1 ⊢
    rw [← hS1]
    subst hσ ht
    field_simp
  · simp only [emCorrIm]
    rw [← hM, kI]
    simp only [corrDataG]
    rw [← hM]
    push_cast at hS2 ⊢
    rw [← hS2]
    subst hσ ht
    field_simp
