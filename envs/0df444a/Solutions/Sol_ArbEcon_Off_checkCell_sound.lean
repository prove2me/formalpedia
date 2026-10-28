-- Prove2me | solution 1 for ArbEcon.Off.checkCell_sound
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T08:01:01.847144+00:00
-- url     : https://prove2.me/submissions/db567a38-b295-4de7-b23e-e35cee09d866

import Definitions.Def_ArdaRH65K_Probes_ArbEconomics_Sound
import Definitions.Def_ArdaRH65K_Turing121_EMZeta
import Definitions.Def_ArdaRH65K_Turing121_EMZetaComplex
import Definitions.Def_ArdaRH65K_Turing121_EMZetaHigh
import Definitions.Def_ArdaRH65K_Turing121_EMZetaHighCheck
import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineCheck
import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineCore
import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineEval
import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineSlab
import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineSlabCheck
import Definitions.Def_ArdaRH65K_Turing121_EMZetaOfflineSound
import Definitions.Def_ArdaRH65K_Turing121_EMZetaTail
import Definitions.Def_ArdaRH65K_Turing121_Probes_ArbEconomics_Zeta
import Definitions.Def_ArdaRS_Arithmetic
import Definitions.Def_ArdaRS_Config64
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
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
import Theorems.Thm_ArbEcon_Off_corr_eqG
import Theorems.Thm_ArbEcon_Off_wball_sound
import Theorems.Thm_ZetaReflection_EMHigh_emCorr_re_im
namespace ZetaReflection
end ZetaReflection
namespace ZetaReflection.EMHigh
end ZetaReflection.EMHigh
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

theorem psumK_succ (σ t : ℝ) (k n : ℕ) :
    psumK σ t k (n + 1) = psumK σ t k n
      + ((Real.log ((n + 1 : ℕ) : ℝ) : ℝ) : ℂ) ^ k * (((n + 1 : ℕ) : ℕ) : ℂ) ^ (-sOfG σ t) := by
  simp only [psumK]
  rw [Finset.sum_Ico_succ_top (by omega : 1 ≤ n + 1)]





/-! ## G. One step, the run, the chunks. -/

















end Off

end ArbEcon


/-  EMZetaOfflineSlabCheck.lean -- lane offline: the KERNEL checker of a zero-free cell.

    The off-line evaluator run at a center `c = σc + i tc` with `p + 1` accumulators gives, after
    `N - 1` and `N` terms, balls of `S_k = Σ_{n<N} (log n)^k n^(-c)` and of `S_k + (log N)^k N^(-c)`.
    With the exact correction factor `emCorr K c N = (BreN + i BimN)/BD` (`corrDataG`) they give balls
    of the Taylor weights `W_k = S_k + (log N)^k N^(-c) emCorr K c N` of `EMZetaOfflineSlab`.

      * `wData`, `wball_sound`  -- the ball of `W_k`, scaled by `2^P BD`;
      * `sumM`, `sumM_sound`    -- `Σ_{k≥1} ‖W_k‖ rn^k rd^(p-k) (p!/k!)` from above;
      * `checkCell`, `checkCell_sound` -- ONE Boolean check (run by `decide +kernel`) proving
                                   `Σ_{k=1}^p ‖W_k‖ r^k/k! + FN/FD < ‖W_0‖`, `r = rn/rd`, the
                                   hypothesis `hmain` of `zeta_ne_zero_of_cell`.

    conjecture1_proved = False.  Finite interval arithmetic; nothing about RH.
-/


open Complex ZetaReflection ZetaReflection.EMHigh
open scoped Nat Real

namespace ArbEcon

namespace Off

/-! ## A. The Taylor weights from the evaluator's partial sums. -/

theorem Wk_eq_psumK (K N : ℕ) (hN : 1 ≤ N) (σ t : ℝ) (k : ℕ) :
    Wk K N (sOfG σ t) k = psumK σ t k (N - 1)
      + (psumK σ t k N - psumK σ t k (N - 1)) * emCorr K (sOfG σ t) N := by
  have hNm : N - 1 + 1 = N := by omega
  have hsucc := psumK_succ σ t k (N - 1)
  rw [hNm] at hsucc
  rw [hsucc]
  simp only [Wk, psumK]
  rw [hNm]
  push_cast
  ring

/-! ## B. The ball of a weight. -/







theorem wUpper_sound (P : ℕ) (W : ℂ) (BD : ℝ) (hBD : 0 < BD) (d : ℤ × ℤ × ℤ × ℤ)
    (hre : |W.re * 2 ^ P * BD - (d.1 : ℝ)| ≤ (d.2.2.1 : ℝ))
    (him : |W.im * 2 ^ P * BD - (d.2.1 : ℝ)| ≤ (d.2.2.2 : ℝ)) :
    ‖W‖ * 2 ^ P * BD ≤ (wUpper d : ℝ) := by
  have hP : (0 : ℝ) < 2 ^ P := by positivity
  have hk : (0 : ℝ) < 2 ^ P * BD := by positivity
  have hn := Complex.norm_le_abs_re_add_abs_im W
  have e1 : |W.re| * (2 ^ P * BD) = |W.re * 2 ^ P * BD| := by
    rw [abs_mul, abs_mul, abs_of_pos hP, abs_of_pos hBD]; ring
  have e2 : |W.im| * (2 ^ P * BD) = |W.im * 2 ^ P * BD| := by
    rw [abs_mul, abs_mul, abs_of_pos hP, abs_of_pos hBD]; ring
  have a1 : |W.re * 2 ^ P * BD| ≤ |(d.1 : ℝ)| + d.2.2.1 := by
    have := abs_sub_abs_le_abs_sub (W.re * 2 ^ P * BD) (d.1 : ℝ); linarith
  have a2 : |W.im * 2 ^ P * BD| ≤ |(d.2.1 : ℝ)| + d.2.2.2 := by
    have := abs_sub_abs_le_abs_sub (W.im * 2 ^ P * BD) (d.2.1 : ℝ); linarith
  have hw : (wUpper d : ℝ) = |(d.1 : ℝ)| + d.2.2.1 + |(d.2.1 : ℝ)| + d.2.2.2 := by
    simp only [wUpper]; push_cast; rfl
  rw [hw]
  calc ‖W‖ * 2 ^ P * BD = ‖W‖ * (2 ^ P * BD) := by ring
    _ ≤ (|W.re| + |W.im|) * (2 ^ P * BD) := mul_le_mul_of_nonneg_right hn hk.le
    _ = |W.re * 2 ^ P * BD| + |W.im * 2 ^ P * BD| := by rw [add_mul, e1, e2]
    _ ≤ _ := by linarith

/-! ## C. The weighted sum over `k ≥ 1`. -/



theorem sumM_sound (P : ℕ) (f1 f2 : ℕ → ℂ) (B : ℂ) (BreN BimN BD : ℤ) (hBD : (0 : ℝ) < BD)
    (hBre : B.re = (BreN : ℝ) / BD) (hBim : B.im = (BimN : ℝ) / BD) (rn rd p : ℕ) :
    ∀ (m k : ℕ) (xs1 xs2 : List Acc), xs1.length = m → xs2.length = m →
      AccsOK P f1 k xs1 → AccsOK P f2 k xs2 →
      ∑ j ∈ Finset.Ico k (k + m), ‖f1 j + (f2 j - f1 j) * B‖ * 2 ^ P * BD
          * ((rn : ℝ) ^ j * (rd : ℝ) ^ (p - j) * ((p ! / j ! : ℕ) : ℝ))
        ≤ (sumM BreN BimN BD rn rd p k xs1 xs2 : ℝ) := by
  intro m
  induction m with
  | zero =>
    intro k xs1 xs2 hl1 hl2 _ _
    rw [List.length_eq_zero_iff] at hl1 hl2
    subst hl1; subst hl2
    simp [sumM]
  | succ m ih =>
    intro k xs1 xs2 hl1 hl2 hA1 hA2
    match xs1, xs2, hl1, hl2, hA1, hA2 with
    | x1 :: ys1, x2 :: ys2, hl1, hl2, hA1, hA2 =>
      obtain ⟨hx1, hy1⟩ := hA1
      obtain ⟨hx2, hy2⟩ := hA2
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hl1 hl2
      have hrec := ih (k + 1) ys1 ys2 hl1 hl2 hy1 hy2
      have hb := wball_sound P (f1 k) (f2 k) x1 x2 hx1 hx2 BreN BimN BD hBD B hBre hBim
      have hu := wUpper_sound P (f1 k + (f2 k - f1 k) * B) BD hBD _ hb.1 hb.2
      have hfac : (0 : ℝ) ≤ (rn : ℝ) ^ k * (rd : ℝ) ^ (p - k) * ((p ! / k ! : ℕ) : ℝ) := by positivity
      rw [show k + (m + 1) = (k + 1) + m by ring, Finset.sum_eq_sum_Ico_succ_bot (by omega)]
      have hs : (sumM BreN BimN BD rn rd p k (x1 :: ys1) (x2 :: ys2) : ℝ)
          = (wUpper (wData BreN BimN BD x1 x2) : ℝ) * ((rn : ℝ) ^ k * (rd : ℝ) ^ (p - k)
              * ((p ! / k ! : ℕ) : ℝ)) + (sumM BreN BimN BD rn rd p (k + 1) ys1 ys2 : ℝ) := by
        simp only [sumM, Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_natCast]; ring
      rw [hs]
      have := mul_le_mul_of_nonneg_right hu hfac
      linarith

/-! ## D. The cell checker. -/









end Off

end ArbEcon


/-  EMZetaOfflineSlabCheck.lean -- lane offline: the KERNEL checker of a zero-free cell.

    The off-line evaluator run at a center `c = σc + i tc` with `p + 1` accumulators gives, after
    `N - 1` and `N` terms, balls of `S_k = Σ_{n<N} (log n)^k n^(-c)` and of `S_k + (log N)^k N^(-c)`.
    With the exact correction factor `emCorr K c N = (BreN + i BimN)/BD` (`corrDataG`) they give balls
    of the Taylor weights `W_k = S_k + (log N)^k N^(-c) emCorr K c N` of `EMZetaOfflineSlab`.

      * `wData`, `wball_sound`  -- the ball of `W_k`, scaled by `2^P BD`;
      * `sumM`, `sumM_sound`    -- `Σ_{k≥1} ‖W_k‖ rn^k rd^(p-k) (p!/k!)` from above;
      * `checkCell`, `checkCell_sound` -- ONE Boolean check (run by `decide +kernel`) proving
                                   `Σ_{k=1}^p ‖W_k‖ r^k/k! + FN/FD < ‖W_0‖`, `r = rn/rd`, the
                                   hypothesis `hmain` of `zeta_ne_zero_of_cell`.

    conjecture1_proved = False.  Finite interval arithmetic; nothing about RH.
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

/-! ## A. The Taylor weights from the evaluator's partial sums. -/



/-! ## B. The ball of a weight. -/









/-! ## C. The weighted sum over `k ≥ 1`. -/





/-! ## D. The cell checker. -/








set_option maxHeartbeats 2000000
theorem solution (c : Cfg) (o : OCfg) (σ t : ℝ) (hσ : σ = ((o.a : ℝ) - o.b) / o.q)
    (ht : t = (c.tn : ℝ) / 2 ^ c.tq) (K N p : ℕ) (xs1 xs2 : List Acc) (rn rd FN FD : ℕ)
    (h1 : AccsOK c.P (fun k => psumK σ t k (N - 1)) 0 xs1)
    (h2 : AccsOK c.P (fun k => psumK σ t k N) 0 xs2)
    (hc : checkCell c o K N p xs1 xs2 rn rd FN FD = true) :
    ∑ k ∈ Finset.Ico 1 (p + 1), ‖Wk K N (sOfG σ t) k‖ * ((rn : ℝ) / rd) ^ k / (k ! : ℝ)
      + (FN : ℝ) / FD < ‖Wk K N (sOfG σ t) 0‖ := by
  match xs1, xs2, h1, h2, hc with
  | x1 :: ys1, x2 :: ys2, h1, h2, hc =>
    simp only [checkCell, Bool.and_eq_true, Nat.ble_eq, decide_eq_true_eq] at hc
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hK1, hK6⟩, hN2⟩, hrd⟩, hFD⟩, hq1⟩, htn1⟩, hl1⟩, hl2⟩, hRHS0⟩, hmainZ⟩ := hc
    have hl1' : ys1.length = p := Nat.eq_of_beq_eq_true hl1
    have hl2' : ys2.length = p := Nat.eq_of_beq_eq_true hl2
    obtain ⟨hx1, hy1⟩ := h1
    obtain ⟨hx2, hy2⟩ := h2
    -- the correction factor
    set u : ℕ := 2 ^ c.tq with hudef
    have hu : 0 < u := Nat.two_pow_pos _
    have huR : (0 : ℝ) < u := by exact_mod_cast hu
    have ht' : t = (c.tn : ℝ) / u := by rw [ht, hudef]; push_cast; ring
    have hσ' : σ = (((o.a : ℤ) - o.b : ℤ) : ℝ) / o.q := by rw [hσ]; push_cast; ring
    obtain ⟨hcre, hcim⟩ := corr_eqG K ((o.a : ℤ) - o.b) o.q u c.tn N hK1 hK6 (by omega) hu
      (by omega) (by omega) σ t hσ' ht'
    set cd := corrDataG K ((o.a : ℤ) - o.b) o.q u c.tn N with hcd
    have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hqR : (0 : ℝ) < o.q := by exact_mod_cast (show 0 < o.q by omega)
    have htnR : (0 : ℝ) < c.tn := by exact_mod_cast (show 0 < c.tn by omega)
    have hBDpos : (0 : ℝ) < (cd.2.2 : ℝ) := by
      have e : (cd.2.2 : ℝ) = 2 * (((((o.a : ℤ) - o.b : ℤ) : ℝ) - o.q) ^ 2 * (u : ℝ) ^ 2
          + (c.tn : ℝ) ^ 2 * (o.q : ℝ) ^ 2) * ((ArbEcon.OrderK.Lbeta : ℝ) * ((o.q : ℝ) * u * N) ^ (2 * K - 1)) := by
        simp only [hcd, corrDataG]; push_cast; ring
      rw [e]
      have hL : (0 : ℝ) < (ArbEcon.OrderK.Lbeta : ℝ) := by norm_num [ArbEcon.OrderK.Lbeta]
      positivity
    set B := emCorr K (sOfG σ t) N with hB
    have hBre : B.re = (cd.1 : ℝ) / cd.2.2 := by rw [← hcre]; exact (emCorr_re_im K σ t N).1
    have hBim : B.im = (cd.2.1 : ℝ) / cd.2.2 := by rw [← hcim]; exact (emCorr_re_im K σ t N).2
    -- the weights
    have hW : ∀ k, Wk K N (sOfG σ t) k = psumK σ t k (N - 1) + (psumK σ t k N - psumK σ t k (N - 1)) * B :=
      fun k => Wk_eq_psumK K N (by omega) σ t k
    simp only [hW]
    set S : ℝ := 2 ^ c.P * cd.2.2 with hS
    have hP : (0 : ℝ) < 2 ^ c.P := by positivity
    have hSpos : 0 < S := by positivity
    -- the k = 0 ball
    have hb0 := wball_sound c.P (psumK σ t 0 (N - 1)) (psumK σ t 0 N) x1 x2 hx1 hx2 cd.1 cd.2.1 cd.2.2
      hBDpos B hBre hBim
    set d0 := wData cd.1 cd.2.1 cd.2.2 x1 x2 with hd0
    set W0 := psumK σ t 0 (N - 1) + (psumK σ t 0 N - psumK σ t 0 (N - 1)) * B with hW0
    set Csq : ℝ := (d0.1 : ℝ) ^ 2 + (d0.2.1 : ℝ) ^ 2 with hCsq
    set R0 : ℝ := (d0.2.2.1 : ℝ) + d0.2.2.2 with hR0
    -- ‖W0‖ S ≥ ‖center‖ - R0
    have hcenter : Real.sqrt Csq - R0 ≤ ‖W0‖ * S := by
      set Z : ℂ := W0 * (S : ℂ) with hZ
      set C : ℂ := (d0.1 : ℂ) + (d0.2.1 : ℂ) * Complex.I with hC
      have hZre : Z.re = W0.re * 2 ^ c.P * cd.2.2 := by
        rw [hZ, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, hS]; ring
      have hZim : Z.im = W0.im * 2 ^ c.P * cd.2.2 := by
        rw [hZ, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, hS]; ring
      have hCre : C.re = d0.1 := by simp [hC]
      have hCim : C.im = d0.2.1 := by simp [hC]
      have hnC : ‖C‖ = Real.sqrt Csq := by
        rw [Complex.norm_eq_sqrt_sq_add_sq, hCre, hCim]
      have hdiff : ‖Z - C‖ ≤ R0 := by
        refine le_trans (Complex.norm_le_abs_re_add_abs_im _) ?_
        rw [Complex.sub_re, Complex.sub_im, hZre, hZim, hCre, hCim]
        exact add_le_add hb0.1 hb0.2
      have hnZ : ‖Z‖ = ‖W0‖ * S := by
        rw [hZ, norm_mul, Complex.norm_real, Real.norm_of_nonneg hSpos.le]
      have htri : ‖C‖ ≤ ‖Z‖ + ‖Z - C‖ := by
        have := norm_sub_norm_le C Z
        rw [norm_sub_rev] at this
        linarith
      rw [← hnC, ← hnZ]
      linarith
    -- the k ≥ 1 sum
    have hsum := sumM_sound c.P (fun k => psumK σ t k (N - 1)) (fun k => psumK σ t k N) B cd.1 cd.2.1
      cd.2.2 hBDpos hBre hBim rn rd p p 1 ys1 ys2 hl1' hl2' hy1 hy2
    rw [show 1 + p = p + 1 by ring] at hsum
    set Msum : ℝ := (sumM cd.1 cd.2.1 cd.2.2 rn rd p 1 ys1 ys2 : ℝ) with hMsum
    -- the integer inequalities, cast
    set T : ℝ := (rd : ℝ) ^ p * ((p ! : ℕ) : ℝ) * FD with hT
    have hrdR : (0 : ℝ) < rd := by exact_mod_cast (show 0 < rd by omega)
    have hFDR : (0 : ℝ) < FD := by exact_mod_cast (show 0 < FD by omega)
    have hpf : (0 : ℝ) < ((p ! : ℕ) : ℝ) := by exact_mod_cast Nat.factorial_pos p
    have hTpos : 0 < T := by positivity
    set RHS : ℝ := R0 * T + Msum * FD + (FN : ℝ) * S * (rd : ℝ) ^ p * ((p ! : ℕ) : ℝ) with hRHSdef
    have hRHScast : ((cellRHS c o K N p x1 x2 ys1 ys2 rn rd FN FD : ℤ) : ℝ) = RHS := by
      simp only [cellRHS, hRHSdef, hR0, hMsum, hS, hT, hd0, hcd, hudef]
      push_cast; ring
    have hLHScast : ((cellLHS c o K N p x1 x2 rd FD : ℤ) : ℝ) = Csq * T ^ 2 := by
      simp only [cellLHS, hCsq, hT, hd0, hcd, hudef]
      push_cast; ring
    have hRHS0R : 0 ≤ RHS := by
      rw [← hRHScast]; exact_mod_cast hRHS0
    have hmainR : RHS * RHS < Csq * T ^ 2 := by
      rw [← hRHScast, ← hLHScast]; exact_mod_cast hmainZ
    have hCsq0 : 0 ≤ Csq := by positivity
    have hsq : RHS < Real.sqrt Csq * T := by
      have hsq2 : RHS ^ 2 < Csq * T ^ 2 := by rw [sq]; exact hmainR
      have h1 : RHS < Real.sqrt (Csq * T ^ 2) := (Real.lt_sqrt hRHS0R).mpr hsq2
      rwa [Real.sqrt_mul hCsq0, Real.sqrt_sq hTpos.le] at h1
    -- assemble:  ‖W0‖ S T > FD Σ_k … + FN S rd^p p!
    have h2' := mul_le_mul_of_nonneg_right hcenter hTpos.le
    have h1' := mul_le_mul_of_nonneg_right hsum hFDR.le
    have hkey : (∑ j ∈ Finset.Ico 1 (p + 1), ‖psumK σ t j (N - 1) + (psumK σ t j N - psumK σ t j (N - 1)) * B‖
          * 2 ^ c.P * cd.2.2 * ((rn : ℝ) ^ j * (rd : ℝ) ^ (p - j) * ((p ! / j ! : ℕ) : ℝ))) * FD
        + (FN : ℝ) * S * (rd : ℝ) ^ p * ((p ! : ℕ) : ℝ) < ‖W0‖ * S * T := by
      have e1 : (Real.sqrt Csq - R0) * T = Real.sqrt Csq * T - R0 * T := by ring
      rw [e1] at h2'
      linarith
    -- divide by S T = S rd^p p! FD
    have hterm : ∀ j ∈ Finset.Ico 1 (p + 1),
        ‖psumK σ t j (N - 1) + (psumK σ t j N - psumK σ t j (N - 1)) * B‖ * 2 ^ c.P * cd.2.2
          * ((rn : ℝ) ^ j * (rd : ℝ) ^ (p - j) * ((p ! / j ! : ℕ) : ℝ)) * FD
        = (‖psumK σ t j (N - 1) + (psumK σ t j N - psumK σ t j (N - 1)) * B‖ * ((rn : ℝ) / rd) ^ j
            / (j ! : ℝ)) * (S * T) := by
      intro j hj
      have hjp : j ≤ p := by have := Finset.mem_Ico.mp hj; omega
      have hdvd : j ! ∣ p ! := Nat.factorial_dvd_factorial hjp
      have hjf : (0 : ℝ) < (j ! : ℝ) := by exact_mod_cast Nat.factorial_pos j
      have hcast : ((p ! / j ! : ℕ) : ℝ) = ((p ! : ℕ) : ℝ) / (j ! : ℝ) := Nat.cast_div hdvd (ne_of_gt hjf)
      have hpow : (rd : ℝ) ^ p = (rd : ℝ) ^ (p - j) * (rd : ℝ) ^ j := by
        rw [← pow_add]; congr 1; omega
      rw [hcast, hT, hS, hpow, div_pow]
      field_simp
    rw [Finset.sum_mul] at hkey
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul] at hkey
    have hST : 0 < S * T := by positivity
    have e3 : (FN : ℝ) * S * (rd : ℝ) ^ p * ((p ! : ℕ) : ℝ) = (FN : ℝ) / FD * (S * T) := by
      rw [hT]; field_simp
    rw [e3, ← add_mul, show ‖W0‖ * S * T = ‖W0‖ * (S * T) by ring] at hkey
    exact lt_of_mul_lt_mul_right hkey hST.le
