-- Prove2me | Definitions.Def_ArdaRH65K_RS_B3Sharp
-- name    : ArdaRH65K_RS_B3Sharp
-- status  : Definition
-- author  : @Johan Mercedes
-- created : 2026-10-28T05:34:54.559755+00:00
-- url     : https://prove2.me/theorems/36656d2d-db4d-4419-bdd5-68c44886aabd
-- title:
--   Gaussian moments and refined saddle-error coefficients
-- statement:
--   For real $b$ and nonnegative integer $j$, this bundle defines the Gaussian moment
--   $M_b(j)=\int_{\mathbb R}|v|^j e^{-bv^2}\,dv$ and the leading error
--   $E_1(a,w)=-2\pi iw^3/(3a)-w/(2a)$. It also defines coefficient functions by
--
--   $$\begin{aligned}
--   \sum_j c_{\rm main}(j)r^j&=\frac{41}{40}-\frac{10\pi}{3}r^2+\frac{40\pi^2}{9}r^4,\\
--   \sum_j c_{\rm two}(j)r^j&=r+4\pi r^3,\\
--   \sum_j c_S(a_0,j)r^j&=r\left[\frac{\sqrt2}{2}\left(1+\frac{8\pi r^2}{3}\right)
--   +\frac{r+4\pi r^3}{a_0}\right]^2.
--   \end{aligned}$$
--
--   The coefficient functions vanish outside their stated finite degrees; division
--   uses the total formal convention. These quantities express the explicit
--   Gaussian-moment error budget.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zeta_reflection/lean/RS_B3Sharp.lean

import Definitions.Def_ArdaRH65K_RS_B2
import Definitions.Def_ArdaRH65K_RS_B3
import Definitions.Def_ArdaRH65K_RS_C0
import Definitions.Def_ArdaRH65K_RS_Entire
import Definitions.Def_ArdaRH65K_RS_Fold
import Definitions.Def_ArdaRH65K_RS_Kernel
import Definitions.Def_ArdaRH65K_RS_Mellin
import Definitions.Def_ArdaRH65K_RS_Strip
import Mathlib
/-  RS_B3Sharp.lean -- lane RS, brick B3 SHARPENED (RSC0 Phase 2): the same C0-corrected
    Riemann-Siegel remainder as `RS_B3Bound` / `RSSeam_B3Bound`, with smaller kernel-checked constants.
    New theorems only; imports `RSSeam_B3Bound` (hence `RS_B3Bound`) read-only and edits nothing.

    ## The headlines (no `sorry`, no `native_decide`, no new axioms)

      `RSInt.rs_remainder_C0_alpha'` : for t >= 4250 (a = sqrt(t/2pi) >= 26), 0 < p = rsFrac t,
      cos(2 pi p) ≠ 0, and every phase phi with |phi - rsThetaMain t| <= 1/t,
          |2 Re(e^{i phi} rsRem t) - (-1)^(N+1) a^(-1/2) Psi(p)| <= (3/20) a^(-3/2);
      `RSInt.rs_remainder_C0'` : the same in t, <= (3/5) t^(-3/4).
      `RSSeam.rs_remainder_C0_alpha_seam'` : for t >= 509, <= (21/100) a^(-3/2);
      `RSSeam.rs_remainder_C0_seam'` : the same in t, <= (21/25) t^(-3/4).
      The old statements (2/5 and 2 at t >= 10000; 13/20 and 13/5 at t >= 509) are re-derived from
      the new ones as `*_of_sharp` corollaries at the end of the file.

    ## What is sharper than `RS_B3Bound` (same architecture, elementary steps)

      * the saddle exponent E is split as E = E1 + E2 with E1 = -2 pi i w^3/(3a) - w/(2a) EXACT and
        |E2| <= pi |w|^4/a^2 + |w|^2/(2a^2) (Mathlib's log-Taylor remainders of orders 4 and 2), and
        |e^E - 1| <= |E| + |E|^2 e^{|E|} (`norm_rsPhi_sub_one_le'`);
      * on the steepest-descent line |E1| = (sqrt2/2)|v| |1 - 8 pi v^2/3| / a EXACTLY (`rsEone_line`):
        the linear and cubic terms have OPPOSITE signs, and |1 - x| <= 41/40 - (5/4)x + (5/8)x^2;
        the main term then integrates against the FULL Gaussian e^{-4 pi v^2} to (49/120)/(2 pi a);
      * only the second-order remainder pays for e^{|E|}, with e^{-(4 pi - 37/10) v^2};
      * absolute Gaussian moments int |v|^j e^{-b v^2} = b^{-(j+1)/2} Gamma((j+1)/2) (`gaussMom_eq`);
      * one near-zone lemma (|v| <= a/3) for every a >= a0 >= 9, the far zone reused verbatim from
        `RSSeam.norm_E1_integrand_far`;
      * |rsJ p| <= 4/5 by completing the square on the midline (was 4) (`norm_rsJ_le'`).
      Budget: |rsE1| <= (7/100)/a (a >= 26) and (9/100)/a (a >= 9); phase 4/(5 pi a^2) <= (1/100)/a
      resp. (3/100)/a; 2 (7/100) + 1/100 = 3/20 and 2 (9/100) + 3/100 = 21/100; (2 pi)^(3/4) <= 4.

    The numeric lemmas bound a|rsE1| by 0.0689 (a >= 26) and 0.0821 (a >= 9).  Untrusted design
    numerics (closed forms 0.0688 and 0.0770): ~/rh-team/rsc0/out/phase2/lean_numerics.py.

    Not yet `lean_lib`s (lakefile.toml untouched): compile with `lake env lean`; a landing PR adds
    append-only `[[lean_lib]]` entries for RS_B3Sharp and RS_BridgeSharp (and RS_AxiomGuardSharp).

    conjecture1_proved = False.  An explicit finite-height remainder inequality; nothing here bears on
    the Riemann Hypothesis.
-/


open Complex MeasureTheory Filter Topology Set
open scoped Real ComplexConjugate

noncomputable section

namespace RSInt

/-! ## 1. Absolute Gaussian moments -/

/-- `gaussMom b j = ∫ |v|^j e^{-b v^2} dv`. -/
def gaussMom (b : ℝ) (j : ℕ) : ℝ := ∫ v : ℝ, |v| ^ j * Real.exp (-b * v ^ 2)



































/-! ## 2. The saddle exponent split into its exact linear-plus-cubic part and a remainder -/

/-- The linear-plus-cubic part of the saddle exponent, `E1(a, w) = -2 pi i w^3/(3a) - w/(2a)`. -/
def rsEone (a : ℝ) (w : ℂ) : ℂ := -(2 * ↑π * I * w ^ 3 / (3 * a)) - w / (2 * a)









/-! ## 3. The near-zone majorant (|v| <= a/3, every a >= a0 >= 9) -/





/-- Coefficients of `41/40 - (10 pi/3) r^2 + (40 pi^2/9) r^4`, the majorant of `|1 - 8 pi r^2/3|`. -/
def cMain (j : ℕ) : ℝ :=
  if j = 0 then 41 / 40 else if j = 2 then -(10 * π / 3) else if j = 4 then 40 * π ^ 2 / 9 else 0

/-- Coefficients of `r + 4 pi r^3` (the remainder `E2` on the line, divided by `|v| a^{-2}`). -/
def cEtwo (j : ℕ) : ℝ := if j = 1 then 1 else if j = 3 then 4 * π else 0

/-- Coefficients of `r P0(r)^2`, `P0(r) = (sqrt2/2)(1 + (8 pi/3) r^2) + (r + 4 pi r^3)/a0`. -/
def cS (a0 : ℝ) (j : ℕ) : ℝ :=
  if j = 1 then 1 / 2 else if j = 2 then Real.sqrt 2 / a0 else if j = 3 then 8 * π / 3 + 1 / a0 ^ 2
  else if j = 4 then Real.sqrt 2 / a0 * (20 * π / 3)
  else if j = 5 then 32 * π ^ 2 / 9 + 8 * π / a0 ^ 2
  else if j = 6 then Real.sqrt 2 / a0 * (32 * π ^ 2 / 3)
  else if j = 7 then 16 * π ^ 2 / a0 ^ 2 else 0



























/-! ## 4. The error integral, sharpened -/











/-! ## 5. Numerics -/





























/-! ## 6. The tau = 2 Mordell integral: `|rsJ p| <= 4/5` (completing the square on the midline) -/





/-! ## 7. The sharpened C0 remainder bound, `a >= 26` (t >= 4250) -/







/-! ## 8. The old headlines re-derived from the sharpened ones -/





end RSInt

namespace RSSeam

open RSInt

/-! ## 9. The seam, sharpened: t >= 509 (a >= 9) -/









end RSSeam


def ArdaRH65K_RS_B3Sharp : Nat := 0


