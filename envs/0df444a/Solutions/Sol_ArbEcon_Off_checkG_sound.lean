-- Prove2me | solution 1 for ArbEcon.Off.checkG_sound
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T08:17:37.039931+00:00
-- url     : https://prove2.me/submissions/16258681-ad53-44b2-8207-76db29c653b2

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
import Theorems.Thm_ArbEcon_Off_checkCoreG_sound
import Theorems.Thm_ArbEcon_Off_remOddG_sound
namespace ArbEcon
end ArbEcon
namespace ArbEcon.OrderK
end ArbEcon.OrderK
namespace ZetaReflection
end ZetaReflection
namespace ZetaReflection.EMHigh
end ZetaReflection.EMHigh

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

open ArbEcon.OrderK (betaN Lbeta  )

/-! ## A. The Gaussian-integer rising factorial at `σ = sN/q`, `t = tn/u`. -/















/-! ## B. The remainder numerator and `N^(-σ)`. -/







/-! ## C. The odd-saw remainder certificate, off the line. -/





/-! ## D. The ball: evaluator invariants + remainder + correction factor. -/







/-! ## E. The kernel checker and its soundness. -/








theorem solution (c : Cfg) (o : OCfg) (σ t : ℝ) (hσ : σ = ((o.a : ℝ) - o.b) / o.q)
    (ht : t = (c.tn : ℝ) / 2 ^ c.tq) (K N : ℕ) (x1 x2 : Acc)
    (h1 : AccOK c.P (psumK σ t 0 (N - 1)) x1) (h2 : AccOK c.P (psumK σ t 0 N) x2) (D : ℕ)
    (reLo reHi imLo imHi : ℤ) (Qp Rn Rd : ℕ)
    (hc : checkG c o K N x1 x2 D reLo reHi imLo imHi Qp Rn Rd = true) :
    ((reLo : ℝ) / D ≤ (riemannZeta (sOfG σ t)).re ∧ (riemannZeta (sOfG σ t)).re ≤ (reHi : ℝ) / D) ∧
    ((imLo : ℝ) / D ≤ (riemannZeta (sOfG σ t)).im ∧ (riemannZeta (sOfG σ t)).im ≤ (imHi : ℝ) / D) := by
  simp only [checkG, Bool.and_eq_true] at hc
  obtain ⟨hR, hcore⟩ := hc
  have hcore' := hcore
  simp only [checkCoreG, Bool.and_eq_true, Nat.ble_eq, decide_eq_true_eq] at hcore'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, hN2⟩, _⟩, _⟩, hq1⟩, htn1⟩, _⟩, _⟩, _⟩, _⟩ := hcore'
  have hu : 0 < 2 ^ c.tq := Nat.two_pow_pos _
  have ht' : t = (c.tn : ℝ) / ((2 ^ c.tq : ℕ) : ℝ) := by rw [ht]; push_cast; ring
  have hE := remOddG_sound K N (by omega) o.a o.b o.q (2 ^ c.tq) c.tn (by omega) hu (by omega) σ t hσ
    ht' Qp Rn Rd hR
  exact checkCoreG_sound c.P c.tq c.tn K o.a o.b o.q N σ t hσ ht x1 x2 h1 h2 D reLo reHi imLo imHi
    _ _ hE hcore
