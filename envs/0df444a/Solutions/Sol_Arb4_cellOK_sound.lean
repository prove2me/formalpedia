-- Prove2me | solution 1 for Arb4.cellOK_sound
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T08:24:51.719339+00:00
-- url     : https://prove2.me/submissions/ac831a14-aee7-4479-9da4-b39ea4ec05c3

import Definitions.Def_ArdaRH65K_Probes_ArbEconomics_Sound
import Definitions.Def_ArdaRH65K_ThetaValue
import Definitions.Def_ArdaRH65K_Turing121_Arb4_Edge
import Definitions.Def_ArdaRH65K_Turing121_Arb4_Q
import Definitions.Def_ArdaRH65K_Turing121_Arb4_Side
import Definitions.Def_ArdaRH65K_Turing121_Arb4_Slab
import Definitions.Def_ArdaRH65K_Turing121_ArctanTaylor
import Definitions.Def_ArdaRH65K_Turing121_ArgHoriz
import Definitions.Def_ArdaRH65K_Turing121_DiffractionCore
import Definitions.Def_ArdaRH65K_Turing121_DlvpTheta
import Definitions.Def_ArdaRH65K_Turing121_DlvpZetaRateEffective
import Definitions.Def_ArdaRH65K_Turing121_EMZeta
import Definitions.Def_ArdaRH65K_Turing121_EMZetaComplex
import Definitions.Def_ArdaRH65K_Turing121_EMZetaHigh
import Definitions.Def_ArdaRH65K_Turing121_EMZetaHighCheck
import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineCheck
import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineCore
import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineEval
import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineSlab
import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineSlabCheck
import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineSlabClear
import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineSound
import Definitions.Def_ArdaRH65K_Turing121_EMZetaTail
import Definitions.Def_ArdaRH65K_Turing121_EdgeClearGlue
import Definitions.Def_ArdaRH65K_Turing121_H1000Octant
import Definitions.Def_ArdaRH65K_Turing121_Probes_ArbEconomics_Zeta
import Definitions.Def_ArdaRH65K_Turing121_RHInBoxAnalytic
import Definitions.Def_ArdaRH65K_Turing121_StripRepr
import Definitions.Def_ArdaRH65K_Turing121_StripReprR1
import Definitions.Def_ArdaRH65K_Turing121_TuringBand
import Definitions.Def_ArdaRH65K_XiLineZeros
import Definitions.Def_ArdaRS_Arithmetic
import Definitions.Def_ArdaRS_Config64
import Mathlib
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Tactic.IntervalCases
import Theorems.Thm_Arb4_Q_val_div
import Theorems.Thm_Arb4_val_emcBQ
import Theorems.Thm_ArbEcon_Off_CK_le
import Theorems.Thm_ArbEcon_Off_dist_le_of_box
import Theorems.Thm_ArbEcon_Off_initO_sound
import Theorems.Thm_ArbEcon_Off_stepO_sound
import Theorems.Thm_ArbEcon_OrderK_valid64
import Theorems.Thm_H1000Oct_cell_zeta_ne_zero_R
namespace Arb4.Q
end Arb4.Q
namespace ArbEcon
end ArbEcon
namespace ArbEcon.Off
end ArbEcon.Off
namespace ZetaReflection
end ZetaReflection
namespace ZetaReflection.EMHigh
end ZetaReflection.EMHigh
/-  Arb4_Q.lean -- lane Arb4 (h1000 compaction): exact rational arithmetic for Boolean kernel
    checkers.

    A certificate side condition such as the error budget of an octant piece is a polynomial
    inequality between explicit rationals.  Closing it by `norm_num` stores the whole normalisation
    trace in the olean (about 300 KB per budget at height 1000).  Here the same inequality is
    computed by `decide +kernel` over plain `Int`/`Nat` arithmetic (GMP-accelerated literals) and
    transported to `ℝ` by ONE soundness theorem per operation, proved once:

      * `Q`             -- an UNNORMALISED rational `n / (dm + 1)` (`n : ℤ`, `dm : ℕ`): the
                           denominator is positive by construction, so no positivity bookkeeping;
                           `val` is its real value, `frac n d` the rational `n / d` (`d ≥ 1`);
      * `add sub mul neg qabs npow div sumQ` -- the operations, `val_*` their homomorphism laws;
      * `le lt`         -- the Boolean comparisons, `le_sound`, `lt_sound`.

    Trust: every theorem is proved from its stated hypotheses; axioms [propext, Classical.choice,
    Quot.sound] (Arb4_AxiomGuard).  No `sorry`.  conjecture1_proved = False.
-/


namespace Arb4



namespace Q





























/-! ## The value homomorphism -/

theorem den_pos (a : Q) : (0 : ℝ) < (a.dm : ℝ) + 1 := by positivity

theorem den_ne (a : Q) : (a.dm : ℝ) + 1 ≠ 0 := ne_of_gt (den_pos a)

theorem val_frac (n : ℤ) {d : ℕ} (hd : 1 ≤ d) : (frac n d).val = (n : ℝ) / (d : ℝ) := by
  simp only [val, frac]
  rw [Nat.cast_sub hd]
  push_cast
  ring_nf

@[simp] theorem val_ofNat (m : ℕ) : (ofNat m).val = (m : ℝ) := by
  simp [val, ofNat]



theorem cast_den_mul (a b : Q) :
    (((a.dm * b.dm + a.dm + b.dm : ℕ) : ℝ) + 1) = ((a.dm : ℝ) + 1) * ((b.dm : ℝ) + 1) := by
  push_cast; ring

theorem val_add (a b : Q) : (add a b).val = a.val + b.val := by
  have h1 := den_ne a
  have h2 := den_ne b
  simp only [val, add]
  rw [cast_den_mul]
  push_cast
  field_simp

theorem val_sub (a b : Q) : (sub a b).val = a.val - b.val := by
  have h1 := den_ne a
  have h2 := den_ne b
  simp only [val, sub]
  rw [cast_den_mul]
  push_cast
  field_simp

theorem val_mul (a b : Q) : (mul a b).val = a.val * b.val := by
  simp only [val, mul]
  rw [cast_den_mul]
  push_cast
  rw [mul_div_mul_comm]



theorem val_qabs (a : Q) : (qabs a).val = |a.val| := by
  simp only [val, qabs]
  rw [abs_div, abs_of_pos (den_pos a), Int.natCast_natAbs, Int.cast_abs]

theorem val_npow (a : Q) : ∀ k, (npow a k).val = a.val ^ k
  | 0 => by simp [npow, val]
  | k + 1 => by rw [npow, val_mul, val_npow a k, pow_succ]



theorem val_sumQ (f : ℕ → Q) : ∀ k, (sumQ f k).val = ∑ i ∈ Finset.range k, (f i).val
  | 0 => by simp [sumQ, val]
  | k + 1 => by rw [sumQ, val_add, val_sumQ f k, Finset.sum_range_succ]

/-! ## The comparisons -/

theorem le_sound {a b : Q} (h : le a b = true) : a.val ≤ b.val := by
  have hz : a.n * ((b.dm : ℤ) + 1) ≤ b.n * ((a.dm : ℤ) + 1) := of_decide_eq_true h
  have hr : (a.n : ℝ) * ((b.dm : ℝ) + 1) ≤ (b.n : ℝ) * ((a.dm : ℝ) + 1) := by exact_mod_cast hz
  simp only [val]
  rw [div_le_div_iff₀ (den_pos a) (den_pos b)]
  exact hr



/-- `0 < n` makes the value positive. -/
theorem val_pos {a : Q} (hn : 0 < a.n) : 0 < a.val := by
  have hn' : (0 : ℝ) < a.n := by exact_mod_cast hn
  exact div_pos hn' (den_pos a)

/-- `0 ≤ n` makes the value nonnegative. -/
theorem val_nonneg {a : Q} (hn : 0 ≤ a.n) : 0 ≤ a.val := by
  have hn' : (0 : ℝ) ≤ a.n := by exact_mod_cast hn
  exact div_nonneg hn' (den_pos a).le



/-! ## Literal conversions (small proof terms for the generated certificates) -/











end Q

end Arb4


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


/-  EMZetaOfflineSound.lean -- soundness of the off-line Nat-only evaluator (EMZetaOfflineEval).

    Every function of `EMZetaOfflineEval` produces a TRUE enclosure:
      * `imul_sound`     : the product `x · v` of a nonnegative bracket and a term ball;
      * `ampl_sound`     : the validated Newton root brackets `2^P m^(-σ)`, `σ = (a - b)/q`
                           (for ANY Newton output: the two kernel comparisons decide the bracket);
      * `termTB_sound`   : the term ball of `m^(-s) = m^(-σ)(cos θ - i sin θ)`, `θ = t log m`;
      * `addChain_sound` : accumulator `k` receives `(log m)^k m^(-s)`;
      * `stepO_sound`, `runO_sound`, `chunkO_sound` : the loop invariant `InvO` (log bracket and
                           the `p + 1` complex balls of `Σ_{m ≤ n} (log m)^k m^(-s)`).
    The log increment and the cos/sin kernels are `ArbEcon.logInc`/`ArbEcon.trig`, whose soundness
    (`ArbEcon.logInc_bound`, `ArbEcon.trig_sound`) is reused unchanged.

    conjecture1_proved = False.  Finite interval arithmetic; nothing here is about RH.
-/



open Real Finset

namespace ArbEcon

namespace Off



/-! ## A. Specifications. -/















/-! ## B. The bracket-times-ball product. -/



/-! ## C. Term balls, accumulation, the log chain. -/







/-! ## D. The validated amplitude bracket. -/





/-! ## E. The term `m^(-s)`. -/





/-! ## F. The partial sums. -/







/-! ## G. One step, the run, the chunks. -/



theorem runO_sound (c : Cfg) (o : OCfg) (σ t : ℝ) (K : ℕ) (hv : Valid c t K) (ho : OValid c o σ) :
    ∀ (L n : ℕ) (s : StO), InvO c σ t n s → InvO c σ t (n + L) (runO c o L s) := by
  intro L
  induction L with
  | zero => intro n s h; exact h
  | succ L ih =>
    intro n s h
    have := ih (n + 1) (stepO c o s) (stepO_sound c o σ t K hv ho n s h)
    rw [show n + (L + 1) = n + 1 + L by ring]
    exact this













end Off

end ArbEcon


/-  EMZetaOfflineSlab.lean -- lane offline: zero-free cells OFF the critical line by a Taylor model
    of the Euler-Maclaurin finite part (the analysis behind a `SlabClear` certificate).

    For a center `c = σc + i tc` (`σc ≥ 0`) and a point `s = c + h`, `‖h‖ ≤ r`:

      T1.  `exp_taylor_le`        -- `‖e^w - Σ_{k≤p} w^k/k!‖ ≤ ‖w‖^(p+1) (p+2)/((p+1)!(p+1))`, `‖w‖ ≤ 1`;
      T2.  `natCpow_neg_add`      -- `n^(-(c+h)) = n^(-c) e^(-h log n)`;
      T3.  `norm_poch_sub_le`     -- `‖(c+h)_k - (c)_k‖ ≤ (U+r)^k - U^k` when every `‖c + j‖ ≤ U`;
      T4.  `emCorr_sub_le`        -- the correction factor moves by at most
                                     `δ = N r / a² + Σ_{i<2K-1} |B_{i+2}|/(i+2)! ((U+r)^(i+1) - U^(i+1)) / N^(i+1)`
                                     (`a ≤ Im c`, `a ≤ Im s`);
      T5.  `emFinite_taylor_le`   -- THE TAYLOR MODEL:
                                     `‖emFinite K (c+h) N - Σ_{k≤p} h^k (-1)^k/k! · W_k‖ ≤ Err`, where
                                     `W_k = Σ_{n<N} (log n)^k n^(-c) + (log N)^k N^(-c) emCorr(c)` and
                                     `Err = C_p (r L)^(p+1) ((N-1) + ‖emCorr(c)‖) + 3 δ`, `L ≥ log N`;
      T6.  `em_remainder_region`  -- the order-(2K+1) remainder uniformly on `1/2 ≤ Re s ≤ 1`,
                                     `0 ≤ Im s ≤ B`;
      T7.  `zeta_ne_zero_of_cell` -- a zero at `s` would force `‖Σ_k h^k …‖ ≤ Err + E`; so
                                     `‖W_0‖ > Σ_{k=1}^p ‖W_k‖ r^k / k! + Err + E` rules it out.

    conjecture1_proved = False.  A finite, local nonvanishing argument; nothing about RH.
-/



open Complex ZetaReflection ZetaReflection.EMHigh
open scoped Nat Real

namespace ArbEcon

namespace Off

/-! ## T1. The complex exponential Taylor remainder. -/







/-! ## T2. Shifting the exponent. -/





/-! ## T3. The Pochhammer symbol moves slowly. -/



/-! ## T4. The correction factor moves slowly. -/





/-! ## T5. The Taylor model of the finite part. -/









/-! ## T6. The order-(2K+1) remainder uniformly on a region. -/



theorem CK_nonneg (K : ℕ) : 0 ≤ CK K := by
  unfold CK
  have : (0 : ℝ) ≤ π ^ 2 / 6 - 1 := by nlinarith [Real.pi_gt_three]
  positivity







/-! ## T7. A zero-free cell. -/





end Off

end ArbEcon


/-  H1000Octant.lean -- lane h1000-integrate: the kernel-checked OCTANT PIECE, the evaluator side of
    brick K6c (`ArgHoriz`) for the horizontal edges `[2, -1] + i T` of the RvM rectangles.

    `ArgHoriz.hAH_of_octCert_boxes` reduces `argChangeHoriz ζ T 2 (-1) ∈ [L, H]` to an octant
    certificate: breakpoints `2 = p 0 > p 1 > … > p m = -1`, one octant label `k j` per piece, and
    the no-crossing facts `0 < octX (k j) ζ(x + i T)` for every `x` of piece `j`, plus two point
    enclosures at `x = 2` and `x = -1`.  This file proves the no-crossing fact of ONE piece from ONE
    run of the off-line evaluator (`EMZetaOfflineEval`, `p + 1` accumulators) at the piece center
    `c = σc + i tc` and ONE Boolean check run by `decide +kernel`:

      A1. `emCorr_sub_le_norm`, `norm_emCorr_le_norm` -- the correction-factor bounds of
          `EMZetaOfflineSlab` with `a ≤ ‖c - 1‖` in place of `a ≤ Im c` (so they hold near `s = 1`
          at small heights);
      A2. `emFinite_taylor_le_G` -- the Taylor model of the EM finite part for ANY real part of the
          center: `‖n^(-c)‖ ≤ G` for `n ≤ N` (`G = 1` for `σc ≥ 0`, `N^(-σc)` for `σc < 0`);
      B.  `pochNormSq_mono_abs`, `em_remainder_horiz` -- the order-(2K+1) remainder uniformly on a
          horizontal segment `xlo ≤ x ≤ xhi` (negative `x` allowed, `x > -2K`);
          `natCpow_norm_le_of_pow` -- the `G` certificate `Gd^q N^b ≤ Gn^q N^a`;
      C.  `octLo`, `octUp`, `sumOct`, `checkOct`, `checkOct_sound` -- the kernel check
          `Σ_{k=1}^p |octX (W_k)| r^k/k! + (|α| + |β|) F < octX (W_0)` on the evaluator balls;
      D.  `piece_octX_pos` -- THE PIECE: for every real `x` with `|x - σc| ≤ r`,
          `0 < ArgHoriz.octX kk (ζ(x + i tc))`.  Along a horizontal piece `h = x - σc` is REAL, so
          the octant projection of the Taylor polynomial is a real polynomial in `h` and only the
          projections `octX (W_k)` enter;
      E.  `abs_sub_le_of_mem_uIcc`, `budget_mono` -- small helpers for the generated certificates.

    Trust: every theorem is proved from its stated hypotheses; axioms [propext, Classical.choice,
    Quot.sound] (AxiomGuardAllZerosKernel_h1000).  No `sorry`.
    conjecture1_proved = False.  Finite interval arithmetic along finitely many segments; nothing
    here bears on the Riemann Hypothesis.
-/



open Complex ZetaReflection ZetaReflection.EMHigh
open scoped Nat Real

namespace H1000Oct

open ArbEcon ArbEcon.Off

/-! ## A1. The correction factor, with `a ≤ ‖c - 1‖`. -/





/-! ## A2. The Taylor model for any real part of the center. -/



/-! ## B. The remainder along a horizontal segment, and the `G` certificate. -/









/-! ## C. The kernel check of a piece. -/

































/-! ## D. The piece. -/





/-! ## E. Helpers for the generated certificates. -/

/-- A point of `[a, b]` (either order) is within `r` of `σ` when both ends are. -/
theorem abs_sub_le_of_mem_uIcc {x a b σ r : ℝ} (hx : x ∈ Set.uIcc a b) (ha : |a - σ| ≤ r)
    (hb : |b - σ| ≤ r) : |x - σ| ≤ r := by
  rw [abs_le] at ha hb ⊢
  rcases Set.mem_uIcc.mp hx with h | h <;> constructor <;> linarith [h.1, h.2]





/-! ## F. Closed forms for the generated budgets (K ≤ 6), and the slab-cell wrapper. -/

theorem abs_bern_div (i : ℕ) (hi : i ≤ 10) :
    |(bernoulli (i + 2) : ℝ)| / ((i + 2)! : ℝ)
      = |(ArbEcon.OrderK.betaN i : ℝ)| / (ArbEcon.OrderK.Lbeta : ℝ) := by
  have hF : (0 : ℝ) < ((i + 2)! : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hL : (0 : ℝ) < (ArbEcon.OrderK.Lbeta : ℝ) := by norm_num [ArbEcon.OrderK.Lbeta]
  rw [← abs_of_pos hF, ← abs_div, ArbEcon.OrderK.betaN_spec i hi, abs_div, abs_of_pos hL]



/-- `corrVar` with the Bernoulli numbers replaced by `betaN / Lbeta` (`K ≤ 6`). -/
theorem corrVar_betaN (K N : ℕ) (hK : K ≤ 6) (r a U : ℝ) :
    corrVar K N r a U = (N : ℝ) * r / a ^ 2
      + ∑ i ∈ Finset.range (2 * K - 1), |(ArbEcon.OrderK.betaN i : ℝ)| / (ArbEcon.OrderK.Lbeta : ℝ)
          * (((U + r) ^ (i + 1) - U ^ (i + 1)) / (N : ℝ) ^ (i + 1)) := by
  unfold corrVar
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i ≤ 10 := by have := Finset.mem_range.mp hi; omega
  rw [← abs_bern_div i hi']
  ring

/-- A rational upper bound of the odd-saw remainder constant at `K = 6`. -/
theorem CK_six_le : CK 6 ≤ 84107 / 1000000000000000 := by
  refine le_trans (CK_le 6) ?_
  norm_num



/-! ## G. Generated-certificate adapters. -/









end H1000Oct


/-  Arb4_Side.lean -- lane Arb4 (h1000 compaction): Boolean kernel checkers, with soundness proved
    once, for the per-piece side conditions of an octant certificate (brick K6c, `H1000Octant`).

    The generated edge modules `H1000Edge_*` of lane h1000-integrate close, per octant piece, an error
    budget, a horizontal remainder bound, a `G` certificate and six scalar conditions by `norm_num`
    (about 400 KB of olean per piece).  Here all of them are ONE Boolean `pieceOK`, run by
    `decide +kernel` on exact rationals (`Arb4_Q`), together with the off-line evaluator run itself
    (the states after `N - 1` and `N` terms are recomputed in the kernel, not stored):

      * `CpQ betaQ emcBQ corrVarQ budgetQ` (+ `val_*`) -- the error budget of
                           `H1000Oct.piece_octX_pos` as a rational, EQUAL to the real one;
      * `pochQ`, `val_pochQ` -- `pochNormSq` as a rational;
      * `PieceD`         -- the certificate data of one piece (center `(a - b)/q`, radius `rn/rd`,
                           octant `kk`, budget `FN/FD`, and the rationals of the side conditions);
      * `gOK remOK geomOK budgetOK` and their soundness -- the `G` bound, the order-13 remainder on the
                           piece, the scalar geometry, the budget;
      * `pieceOK`, `pieceOK_sound` -- THE PIECE: `pieceOK tn tq N L P = true` gives
                           `0 < octX kk (ζ(x + i t))` for every `x` with `|x - σ| ≤ r`, `t = tn / 2^tq`.

    Trust: every theorem is proved from its stated hypotheses; axioms [propext, Classical.choice,
    Quot.sound] (Arb4_AxiomGuard).  No `sorry`.  conjecture1_proved = False.  Finite interval
    arithmetic along finitely many segments; nothing here bears on the Riemann Hypothesis.
-/



open Complex ZetaReflection ZetaReflection.EMHigh
open scoped Nat Real

namespace Arb4

open Q

/-! ## A. The error budget as a rational -/



theorem val_CpQ (p : ℕ) : (CpQ p).val = ArbEcon.Off.Cp p := by
  have hd : 1 ≤ (p + 1)! * (p + 1) := Nat.mul_pos (Nat.factorial_pos _) (Nat.succ_pos _)
  rw [CpQ, val_frac _ hd]
  unfold ArbEcon.Off.Cp
  push_cast
  ring



theorem val_betaQ (i : ℕ) :
    (betaQ i).val = |(ArbEcon.OrderK.betaN i : ℝ)| / (ArbEcon.OrderK.Lbeta : ℝ) := by
  have hL : 1 ≤ ArbEcon.OrderK.Lbeta := by unfold ArbEcon.OrderK.Lbeta; norm_num
  rw [betaQ, val_frac _ hL, Int.natCast_natAbs, Int.cast_abs]







theorem npow_two_n_pos {a : Q} (ha : 0 < a.n) : 0 < (npow a 2).n := by
  show 0 < 1 * a.n * a.n
  rw [one_mul]
  exact mul_pos ha ha

theorem val_corrVarQ (K N : ℕ) (hK : K ≤ 6) (hN : 0 < N) (r a U : Q) (ha : 0 < a.n) :
    (corrVarQ K N r a U).val = ArbEcon.Off.corrVar K N r.val a.val U.val := by
  rw [H1000Oct.corrVar_betaN K N hK]
  unfold corrVarQ
  rw [val_add, val_div _ (npow_two_n_pos ha), val_mul, val_ofNat, val_npow, val_sumQ]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  have hNp : (0 : ℤ) < ((N ^ (i + 1) : ℕ) : ℤ) := by exact_mod_cast pow_pos hN _
  rw [val_mul, val_betaQ, val_div _ hNp, val_sub, val_npow, val_npow, val_add, val_ofNat]
  push_cast
  ring





/-! ## B. `pochNormSq` as a rational -/



theorem val_pochQ (σ t : Q) : ∀ k, (pochQ σ t k).val = pochNormSq σ.val t.val k
  | 0 => by simp [pochQ, pochNormSq]
  | k + 1 => by
    rw [pochQ, val_mul, val_pochQ σ t k, val_add, val_npow, val_npow, val_add, val_ofNat,
      pochNormSq]

/-! ## C. The certificate data of one octant piece -/



theorem val_tQ (tn tq : ℕ) : (tQ tn tq).val = (tn : ℝ) / 2 ^ tq := by
  rw [tQ, val_frac _ (Nat.one_le_two_pow)]
  push_cast
  ring



namespace PieceD

























end PieceD

/-! ## D. The side conditions as Booleans -/













/-! ## E. THE PIECE -/





end Arb4


/-  Arb4_Slab.lean -- lane Arb4 (h1000 compaction): ONE Boolean kernel checker per zero-free
    edge-clearance slab `EdgeClearGlue.SlabClear a b` (brick K1's numerical input).

    The generated slab modules `H1000Slab_*` of lane h1000-integrate cover `[1/2, 1] × [a, b]` by
    cells (one off-line evaluator run and one `ArbEcon.Off.checkCell` each), assembled by
    `H1000Oct.cell_zeta_ne_zero_R`, and close the slab budget, the Pochhammer bound and about
    fifteen scalar conditions per cell by `norm_num`.  Here the WHOLE slab is one Boolean `slabOK`:

      * `slabBudgetQ`, `slabBudget_le` -- the slab error budget as a rational (with
                           `C_6 ≤ 84107 · 10^-15`, `H1000Oct.CK_six_le`);
      * `CellD`, `SlabD` -- the certificate data: the slab `[lo, hi]`, its shared budget, the
                           breakpoints `1/2 = xs 0 < … < xs m = 1` and one cell per column
                           `[xs j, xs (j+1)] × [lo, hi]` (center, radius, half-widths);
      * `cellOK`, `cellOK_sound` -- one cell (evaluator run recomputed, `checkCell`, geometry);
      * `slabOK`, `slabOK_sound` -- THE SLAB: `slabOK S = true` gives `SlabClear lo hi`.

    Trust: every theorem is proved from its stated hypotheses; axioms [propext, Classical.choice,
    Quot.sound] (Arb4_AxiomGuard).  No `sorry`.  conjecture1_proved = False.  A finite zero-free
    slab; nothing here bears on the Riemann Hypothesis.
-/


open Complex ZetaReflection ZetaReflection.EMHigh
open scoped Nat Real

namespace Arb4

open Q

/-! ## A. The slab budget -/



theorem slabBudget_le (N : ℕ) (hN : 1 ≤ N) (R L a U : Q) (Qr r0 : ℕ) (hr0 : 0 < r0) (ha : 0 < a.n) :
    ArbEcon.Off.Cp 5 * (R.val * L.val) ^ (5 + 1) * (((N : ℝ) - 1) + ArbEcon.Off.emcB 6 N a.val U.val)
        + 3 * ArbEcon.Off.corrVar 6 N R.val a.val U.val
        + ArbEcon.Off.CK 6 * (Qr : ℝ) / ((N : ℝ) ^ (2 * 6) * r0) / (((2 * 6 : ℕ) : ℝ) + 1 / 2)
      ≤ (slabBudgetQ N R L a U Qr r0).val := by
  have hNr : (0 : ℤ) < ((N ^ 12 * r0 : ℕ) : ℤ) := by
    exact_mod_cast Nat.mul_pos (pow_pos (by omega) _) hr0
  unfold slabBudgetQ
  rw [val_add, val_add, val_mul, val_mul, val_CpQ, val_npow, val_mul, val_add, val_sub, val_ofNat,
    val_ofNat, val_emcBQ 6 N (by norm_num) (by omega) a U ha, val_mul, val_ofNat,
    val_corrVarQ 6 N (by norm_num) (by omega) R a U ha, val_div _ (by norm_num [frac]),
    val_div _ hNr, val_mul, val_frac _ (by norm_num), val_frac _ (by norm_num), val_ofNat, val_ofNat]
  have hC := H1000Oct.CK_six_le
  have hC0 := ArbEcon.Off.CK_nonneg 6
  have hNpos : (0 : ℝ) < (N : ℝ) ^ (2 * 6) * r0 := by
    have : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have : (0 : ℝ) < r0 := by exact_mod_cast hr0
    positivity
  have hm : ArbEcon.Off.CK 6 * (Qr : ℝ) / ((N : ℝ) ^ (2 * 6) * r0) / (((2 * 6 : ℕ) : ℝ) + 1 / 2)
      ≤ (84107 / 1000000000000000 : ℝ) * (Qr : ℝ) / ((N : ℝ) ^ (2 * 6) * r0) / (((2 * 6 : ℕ) : ℝ) + 1 / 2) := by
    gcongr
  push_cast at hm ⊢
  norm_num at hm ⊢
  linarith

/-! ## B. The certificate data -/





namespace CellD







theorem val_σQ (C : CellD) (hq : 1 ≤ C.q) : C.σQ.val = C.σ := by
  rw [σQ, val_frac _ hq, σ]; push_cast; ring

end CellD

/-! ## C. One cell -/





theorem runs_inv_cell (S : SlabD) (C : CellD) (hN : 2 ≤ S.N) (hq : 1 ≤ C.q) :
    ArbEcon.Off.InvO (ArbEcon.OrderK.cfg64 C.tn S.tq) C.σ ((C.tn : ℝ) / 2 ^ S.tq) (S.N - 1)
        (ArbEcon.Off.runO (ArbEcon.OrderK.cfg64 C.tn S.tq) C.oc (S.N - 2)
          (ArbEcon.Off.StO.init (ArbEcon.OrderK.cfg64 C.tn S.tq) 5)) ∧
      ArbEcon.Off.InvO (ArbEcon.OrderK.cfg64 C.tn S.tq) C.σ ((C.tn : ℝ) / 2 ^ S.tq) S.N
        (ArbEcon.Off.runO (ArbEcon.OrderK.cfg64 C.tn S.tq) C.oc 1
          (ArbEcon.Off.runO (ArbEcon.OrderK.cfg64 C.tn S.tq) C.oc (S.N - 2)
            (ArbEcon.Off.StO.init (ArbEcon.OrderK.cfg64 C.tn S.tq) 5))) := by
  set c := ArbEcon.OrderK.cfg64 C.tn S.tq with hc
  set t : ℝ := (C.tn : ℝ) / 2 ^ S.tq with ht
  have hv : ArbEcon.Valid c t 9 := ArbEcon.OrderK.valid64 C.tn S.tq t rfl
  have ho : ArbEcon.Off.OValid c C.oc C.σ := ⟨rfl, hq, rfl⟩
  have i0 := ArbEcon.Off.initO_sound c C.σ t 5 hv.one_eq
  have i1 := ArbEcon.Off.runO_sound c C.oc C.σ t 9 hv ho (S.N - 2) 1 _ i0
  rw [show 1 + (S.N - 2) = S.N - 1 by omega] at i1
  have i2 := ArbEcon.Off.runO_sound c C.oc C.σ t 9 hv ho 1 (S.N - 1) _ i1
  rw [show S.N - 1 + 1 = S.N by omega] at i2
  exact ⟨i1, i2⟩



/-! ## D. THE SLAB -/







end Arb4


/-  Arb4_Slab.lean -- lane Arb4 (h1000 compaction): ONE Boolean kernel checker per zero-free
    edge-clearance slab `EdgeClearGlue.SlabClear a b` (brick K1's numerical input).

    The generated slab modules `H1000Slab_*` of lane h1000-integrate cover `[1/2, 1] × [a, b]` by
    cells (one off-line evaluator run and one `ArbEcon.Off.checkCell` each), assembled by
    `H1000Oct.cell_zeta_ne_zero_R`, and close the slab budget, the Pochhammer bound and about
    fifteen scalar conditions per cell by `norm_num`.  Here the WHOLE slab is one Boolean `slabOK`:

      * `slabBudgetQ`, `slabBudget_le` -- the slab error budget as a rational (with
                           `C_6 ≤ 84107 · 10^-15`, `H1000Oct.CK_six_le`);
      * `CellD`, `SlabD` -- the certificate data: the slab `[lo, hi]`, its shared budget, the
                           breakpoints `1/2 = xs 0 < … < xs m = 1` and one cell per column
                           `[xs j, xs (j+1)] × [lo, hi]` (center, radius, half-widths);
      * `cellOK`, `cellOK_sound` -- one cell (evaluator run recomputed, `checkCell`, geometry);
      * `slabOK`, `slabOK_sound` -- THE SLAB: `slabOK S = true` gives `SlabClear lo hi`.

    Trust: every theorem is proved from its stated hypotheses; axioms [propext, Classical.choice,
    Quot.sound] (Arb4_AxiomGuard).  No `sorry`.  conjecture1_proved = False.  A finite zero-free
    slab; nothing here bears on the Riemann Hypothesis.
-/


open Complex ZetaReflection ZetaReflection.EMHigh
open scoped Nat Real

section
namespace Arb4
end Arb4
open Arb4

open Q

/-! ## A. The slab budget -/





/-! ## B. The certificate data -/





section
namespace Arb4.CellD
end Arb4.CellD
open Arb4.CellD









end

/-! ## C. One cell -/








set_option maxHeartbeats 1000000

theorem solution (S : SlabD) (hS : slabHeadOK S = true) (j : ℕ) (h : cellOK S j = true) :
    ∀ x y : ℝ, x ∈ Set.uIcc (S.xs j).val (S.xs (j + 1)).val →
      S.lo.val ≤ y → y ≤ S.hi.val → 1 / 2 ≤ x → x ≤ 1 →
      riemannZeta ((x : ℂ) + (y : ℂ) * I) ≠ 0 := by
  intro x y hx hy0 hy1 hxh hx1
  simp only [slabHeadOK, Bool.and_eq_true, Nat.ble_eq, decide_eq_true_eq] at hS
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hm, hFD⟩, _⟩, _⟩, hRL⟩, hlo⟩, hU0⟩, hQ⟩, hr0⟩, hr0N⟩, hN1⟩, hbud⟩ := hS
  simp only [cellOK, Bool.and_eq_true, Nat.ble_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hN2, hq⟩, hrd⟩, hba⟩, hchk⟩, hrR⟩, hL⟩, hta⟩, hU⟩, hw0⟩, hw1⟩, hh0⟩, hh1⟩,
    hwr⟩ := h
  set C := S.cell j with hC
  set tc : ℝ := (C.tn : ℝ) / 2 ^ S.tq with htc
  obtain ⟨i1, i2⟩ := runs_inv_cell S C hN2 hq
  -- values
  have hrR' := le_sound hrR
  rw [val_frac _ hrd] at hrR'
  push_cast at hrR'
  have hL' := le_sound hL
  rw [val_ofNat, val_mul, val_ofNat] at hL'
  have hta' := le_sound hta
  rw [val_tQ] at hta'
  have hU' := le_sound hU
  rw [val_add, val_npow, val_add, C.val_σQ hq, val_ofNat, val_npow, val_tQ, val_npow] at hU'
  have hRL' := le_sound hRL
  rw [val_mul, val_ofNat, Nat.cast_one] at hRL'
  have hQ' := le_sound hQ
  rw [val_pochQ, val_ofNat, val_ofNat, Nat.cast_one] at hQ'
  have hbud' := le_trans (slabBudget_le S.N hN1 S.R S.L S.lo S.U S.Qr S.r0 hr0 hlo) (le_sound hbud)
  rw [val_frac _ hFD] at hbud'
  push_cast at hbud'
  have hσ0 : 0 ≤ C.σ := by
    unfold CellD.σ
    have : (C.b : ℝ) ≤ C.a := by exact_mod_cast hba
    have : (0 : ℝ) < C.q := by exact_mod_cast hq
    apply div_nonneg <;> linarith
  have hP64 : (ArbEcon.OrderK.cfg64 C.tn S.tq).P = 64 := rfl
  have e64 : ((2 ^ 64 : ℕ) : ℝ) = (2 : ℝ) ^ (64 : ℕ) := by push_cast; ring
  have hL'' : ((ArbEcon.Off.runO (ArbEcon.OrderK.cfg64 C.tn S.tq) C.oc 1
      (ArbEcon.Off.runO (ArbEcon.OrderK.cfg64 C.tn S.tq) C.oc (S.N - 2)
        (ArbEcon.Off.StO.init (ArbEcon.OrderK.cfg64 C.tn S.tq) 5))).lhi : ℝ)
      ≤ S.L.val * 2 ^ (ArbEcon.OrderK.cfg64 C.tn S.tq).P := by
    rw [hP64, ← e64]; exact hL'
  have e11 : (2 * ((6 : ℕ) : ℝ) - 1 : ℝ) = ((11 : ℕ) : ℝ) := by norm_num
  have hU'' : (C.σ + (2 * ((6 : ℕ) : ℝ) - 1 : ℝ)) ^ 2 + tc ^ 2 ≤ S.U.val ^ 2 := by
    rw [e11]; exact hU'
  have hQ'' : pochNormSq 1 S.hi.val (2 * 6 + 1) ≤ (S.Qr : ℝ) ^ 2 := by
    rw [sq]; push_cast at hQ' ⊢; exact hQ'
  have hcell := H1000Oct.cell_zeta_ne_zero_R (ArbEcon.OrderK.cfg64 C.tn S.tq) C.oc C.σ tc rfl rfl 6
    S.N 5 (by norm_num) hN2 _ _ i1 i2 C.rn C.rd S.FN S.FD hchk S.R.val S.L.val S.lo.val S.U.val
    S.hi.val (S.Qr : ℝ) S.r0 hrR' hL'' hRL' (val_pos hlo) hta' hσ0 (val_nonneg hU0) hU''
    (Nat.cast_nonneg _) hQ'' hr0 (by rw [sq]; exact hr0N) hbud'
  -- the rectangle is inside the disc
  have hw0' := le_sound hw0
  have hw1' := le_sound hw1
  have hh0' := le_sound hh0
  have hh1' := le_sound hh1
  have hwr' := le_sound hwr
  rw [val_qabs, val_sub, C.val_σQ hq] at hw0' hw1'
  rw [val_qabs, val_sub, val_tQ] at hh0' hh1'
  rw [val_add, val_npow, val_npow, val_npow, val_frac _ hrd] at hwr'
  have hxw : |x - C.σ| ≤ C.w.val := H1000Oct.abs_sub_le_of_mem_uIcc hx hw0' hw1'
  have hyh : |y - tc| ≤ C.hh.val :=
    H1000Oct.abs_sub_le_of_mem_uIcc (Set.mem_uIcc.mpr (Or.inl ⟨hy0, hy1⟩)) hh0' hh1'
  have hr0' : (0 : ℝ) ≤ (C.rn : ℝ) / C.rd := by positivity
  have hdisc := ArbEcon.Off.dist_le_of_box x y C.σ tc C.w.val C.hh.val ((C.rn : ℝ) / C.rd) hxw hyh hr0'
    (by push_cast at hwr' ⊢; exact hwr')
  have hre : ((x : ℂ) + (y : ℂ) * I).re = x := by simp
  have him : ((x : ℂ) + (y : ℂ) * I).im = y := by simp
  exact hcell _ hdisc (by rw [him]; exact hy0) (by rw [him]; exact hy1) (by rw [hre]; exact hxh)
    (by rw [hre]; exact hx1)
