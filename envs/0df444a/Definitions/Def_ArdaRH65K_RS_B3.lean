-- Prove2me | Definitions.Def_ArdaRH65K_RS_B3
-- name    : ArdaRH65K_RS_B3
-- status  : Definition
-- author  : @Johan Mercedes
-- created : 2026-10-28T05:33:35.615764+00:00
-- url     : https://prove2.me/theorems/94660931-95c7-4786-8c41-014f5b08cd4e
-- title:
--   Riemann–Siegel parameters and saddle remainder
-- statement:
--   For real $t$, this bundle defines $a(t)=\sqrt{t/(2\pi)}$,
--   $N(t)=\lfloor a(t)\rfloor_{\mathbb N}$, $p(t)=a(t)-N(t)$, the main theta
--   approximation, and the correction
--
--   $$\Psi(p)=\frac{\cos(2\pi(p^2-p-1/16))}{\cos(2\pi p)}.$$
--
--   It also defines the contour remainder, the saddle factor
--   $\Phi_a(w)=e^{2\pi iaw-\pi iw^2}(1+w/a)^{-1/2-2\pi ia^2}$, and its error
--   integral. Real and complex division are total in the formal definitions; later
--   theorems state the nonvanishing hypotheses needed for their analytic use.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zeta_reflection/lean/RS_B3.lean

import Definitions.Def_ArdaRH65K_RS_B2
import Definitions.Def_ArdaRH65K_RS_C0
import Definitions.Def_ArdaRH65K_RS_Entire
import Definitions.Def_ArdaRH65K_RS_Fold
import Definitions.Def_ArdaRH65K_RS_Kernel
import Definitions.Def_ArdaRH65K_RS_Mellin
import Definitions.Def_ArdaRH65K_RS_Strip
import Mathlib
/-  RS_B3.lean -- lane RS, brick B3 (the explicit Riemann-Siegel remainder), part 2: the exact
    saddle-point reduction.  Mathlib-only (imports `RS_C0`).

    ## Vocabulary (height t > 0)

        a = rsAlpha t = sqrt(t / 2 pi),  N = rsNn t = floor a,  p = rsFrac t = a - N,
        rsThetaMain t = (t/2) log t - (t/2) log(2 pi) - t/2 - pi/8   (verbatim the corpus thetaMain),
        rsPsi p = cos(2 pi (p^2 - p - 1/16)) / cos(2 pi p)            (Gabcke's C0 = Riemann's Psi),
        rsRem t = -lineUp (N + 1/2) (x |-> rsG x x^(-(1/2 + i t)))    (the exact RS remainder, B2).

    By B2 (`completed_re_eq_rs_cos`), on the critical line
        Re completedRiemannZeta(1/2+it) = 2M ( sum_{n<=N} n^(-1/2) cos(phi - t log n) + Re(e^{i phi} rsRem t) ).

    ## What this file proves (no `sorry`, no `native_decide`, no new axioms)

      * `rsRem_factor` : moving the remainder line to the saddle point a and factoring out the
        stationary phase,
            rsRem t = (-1)^(N+1) e^{i pi a^2} a^(-s) (rsJ p + rsE1 a p),
        where rsJ is the tau = 2 Mordell integral (RS_C0) and rsE1 the error integral of the amplitude
        rsPhi a w - 1,  rsPhi a w = e^{2 pi i a w - pi i w^2} (1 + w/a)^(-s).
      * `rs_phase` : e^{i phi} e^{i pi a^2} a^(-s) = a^(-1/2) e^{i (phi - rsThetaMain t - pi/8)}.
      * `rs_remainder_exact` : the EXACT identity
            2 Re(e^{i phi} rsRem t) - (-1)^(N+1) a^(-1/2) Psi(p)
              = (-1)^(N+1) a^(-1/2) [ 2 Re(e^{-i pi/8}(e^{i delta} - 1) rsJ p)
                                      + 2 Re(e^{i (delta - pi/8)} rsE1 a p) ],   delta = phi - thetaMain t,
        so the C0-corrected remainder is controlled by |delta| |rsJ p| and |rsE1 a p| alone.

    conjecture1_proved = False.
-/


open Complex MeasureTheory Filter Topology Set
open scoped Real ComplexConjugate

noncomputable section

namespace RSInt

/-! ## 0. Vocabulary -/

/-- `a = sqrt(t / 2 pi)`, the saddle point of the Riemann-Siegel integral. -/
def rsAlpha (t : ℝ) : ℝ := Real.sqrt (t / (2 * π))

/-- `N = floor(sqrt(t / 2 pi))`, the length of the Riemann-Siegel main sum. -/
def rsNn (t : ℝ) : ℕ := ⌊rsAlpha t⌋₊

/-- `p = sqrt(t / 2 pi) - N ∈ [0, 1)`. -/
def rsFrac (t : ℝ) : ℝ := rsAlpha t - rsNn t

/-- The Stirling main term of the Riemann-Siegel theta (verbatim `ZeroFreeBridge.thetaMain`). -/
def rsThetaMain (t : ℝ) : ℝ :=
  t / 2 * Real.log t - t / 2 * Real.log (2 * Real.pi) - t / 2 - Real.pi / 8

/-- Riemann's Psi (Gabcke's C0): `cos(2 pi (p^2 - p - 1/16)) / cos(2 pi p)`. -/
def rsPsi (p : ℝ) : ℝ := Real.cos (2 * π * (p ^ 2 - p - 1 / 16)) / Real.cos (2 * π * p)

/-- The exact Riemann-Siegel remainder integral at height `t` (B2, line through `N + 1/2`). -/
def rsRem (t : ℝ) : ℂ :=
  -lineUp ((rsNn t : ℝ) + 1 / 2) (fun x => rsG x * x ^ (-((1 / 2 : ℂ) + t * I)))

/-- The saddle-point amplitude `e^{2 pi i a w - pi i w^2} (1 + w/a)^(-(1/2 + 2 pi a^2 i))`. -/
def rsPhi (a : ℝ) (w : ℂ) : ℂ :=
  cexp (2 * ↑π * I * a * w - ↑π * I * w ^ 2) * (1 + w / a) ^ (-((1 / 2 : ℂ) + 2 * ↑π * a ^ 2 * I))

/-- The error integral of the saddle-point expansion. -/
def rsE1 (a p : ℝ) : ℂ :=
  lineUp 0 (fun w => cexp (2 * ↑π * I * w ^ 2) / rsD (p + w) * (rsPhi a w - 1))















/-! ## 1. Shifting the denominator by an integer -/



/-! ## 2. The factorization at the saddle point -/











/-! ## 3. The phase -/



/-! ## 4. The exact C0-corrected remainder -/



end RSInt


def ArdaRH65K_RS_B3 : Nat := 0


