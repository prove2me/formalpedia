-- Prove2me | Definitions.Def_FixedPriceTrade_refCurve
-- name    : FixedPriceTrade_refCurve
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:42:19.48858+00:00
-- url     : https://prove2.me/theorems/e46f891a-d83c-418e-9611-142b2b55e6de
-- title:
--   Reference curves $P_x$, contact data, $Q_x$, $\Phi_d$, $B_d$ and the gap integrands
-- statement:
--   Fix $d>0$. For a curvature parameter $C$ put
--   $$
--   \chi(C,y)=\frac{\sqrt{D_C(y)}}{y}\,e^{-\mathcal I_C(y)/2}\qquad(Cy<1,\ D_C(r)>0\text{ for }0\le r\le y),
--   $$
--   and let $Y_d(C)$ solve $\chi(C,Y_d(C))=d$; at the limiting endpoint $Y_d(0)=1/(1+d)$. The terminal value is $\chi_{\mathrm{end}}(C)=Ce^{-\mathcal I_C(1/C)/2}$ and $\bar C(d)>1/4$ solves $\chi_{\mathrm{end}}(\bar C(d))=d$. The contact data are
--   $$
--   x(C)=\frac{1-D_C(Y_d)}{D_C(Y_d)},\quad a_e=\frac{CY_d^2}{D_C(Y_d)},\quad a_a=\frac C{d^2},\quad P_e=\frac{Y_d}{D_C(Y_d)},
--   $$
--   $$
--   Z_d(C)=\int_0^{Y_d}\frac{r^2}{D_C(r)^2}dr,\qquad U_d(C)=\int_0^{Y_d}\frac{Y_d-r}{D_C(r)^2}dr,\qquad B_d(C)=2C-1+C(1-C)Y_d .
--   $$
--   The **reference curve** is $P_x(a)=x+a$ on $[0,a_e]$, the middle arc $\big(a(r),P_x(a(r))\big)=\big(\tfrac C{d^2}e^{-\mathcal I_C(r)},\ \tfrac{e^{-\mathcal I_C(r)/2}}{d\sqrt{D_C(r)}}\big)$, $0\le r\le Y_d(C)$, on $[a_e,a_a]$, and $1/d$ for $a\ge a_a$; at $C=0$, $P\equiv1/d$. The multiplier is
--   $$
--   Q_x(a)=\begin{cases}(1+x)/(x+a)^2,&0<a<a_e,\\0,&a_e<a<a_a,\\d^2,&a>a_a.\end{cases}
--   $$
--   The endpoint envelope is $\Phi_d(x(C))=\mathcal F_d[P_{x(C)}]$. For a control $h$ with reciprocal state $p$, $v=\log(p/P_x)$, and the integrands of (G1) and (G2) are
--   $$
--   a(v')^2+\frac{e^{-2v}-1+2v}{P_x^2}-2Q_xv,\qquad \frac{(Y_d(u)+U_d(u))\,|B_d(u)|}{(1-uY_d(u))^2}.
--   $$
--   These are the comparison curves of §§6–7, one for every endpoint.
--
--   **Formalization Note** $Y_d(C)$ is a guarded choice (junk value $0$ where no solution exists; Lemma 6.1 gives uniqueness on $(0,\bar C(d))$), and $\bar C(d)$ is the infimum of the solutions of $\chi_{\mathrm{end}}=d$ on $(1/4,\infty)$. The curve is indexed by $C$, with endpoint $x(C)$. The middle arc is written through the inverse of the strictly decreasing $a(r)$, as $\sup\{r\in[0,Y_d]: a\le a(r)\}$. $Q_x$ at the break points is immaterial.
-- source:
--   Lin, Shi, Dong, Li, Yu, Zhang, The Exact Welfare Guarantee of Fixed-Price Bilateral Trade, arXiv:2609.35888 (held PDF sha256 26832346…), §6, (19)–(24), p.14; proof of Lemma 6.1, pp.15–16; §7, (29), p.16

import Mathlib
import Definitions.Def_FixedPriceTrade_SCurve
import Definitions.Def_FixedPriceTrade_energy

set_option autoImplicit false

namespace FixedPriceTrade

open MeasureTheory Set Real

/-- `χ(C, y) = √D_C(y) / y · e^{−I_C(y)/2}` ((19), p.14). -/
noncomputable def chi (C y : ℝ) : ℝ := sqrt (Dq C y) / y * exp (-(ICrun C y) / 2)

/-- The side conditions of (19), p.14, together with `y > 0`: `C y < 1` and `D_C(r) > 0` for
`0 ≤ r ≤ y`. -/
def ChiDomain (C y : ℝ) : Prop := 0 < y ∧ C * y < 1 ∧ ∀ r ∈ Icc (0 : ℝ) y, 0 < Dq C r

/-- The terminal value `χ_end(C) = C e^{−I_C(1/C)/2}` (proof of Lemma 6.1, p.15), for
`C > 1/4`. -/
noncomputable def chiEnd (C : ℝ) : ℝ := C * exp (-(ICrun C (1 / C)) / 2)

/-- `C̄(d)`: the value `C > 1/4` with `χ_end(C) = d` (proof of Lemma 6.1, p.15), written as the
infimum of such values.

**Formalization Note.** The proof shows `χ_end` strictly increasing from `0` to `∞` on
`(1/4, ∞)`, so the set is a singleton; Lemma 6.1 (milestone) states this. -/
noncomputable def Cbar (d : ℝ) : ℝ := sInf {C | 1 / 4 < C ∧ chiEnd C = d}

open Classical in
/-- The contact parameter `Y_d(C)`, the solution `y` of `χ(C, y) = d` under the side conditions of
(19) (p.14); at the limiting endpoint `C = 0`, `Y_d(0) = 1/(1 + d)` (p.16).

**Formalization Note.** A guarded choice: when a solution exists it is chosen (Lemma 6.1 shows it
is unique for `0 < C < C̄(d)`), and the junk value `0` is used otherwise; no statement uses
`Y_d(C)` outside `[0, C̄(d))`. -/
noncomputable def Yd (d C : ℝ) : ℝ :=
  if C = 0 then 1 / (1 + d)
  else if hy : ∃ y, ChiDomain C y ∧ chi C y = d then hy.choose else 0

/-- The reciprocal-state endpoint `x(C) = (1 − D_C(Y_d))/D_C(Y_d)` ((20), p.14). At `C = 0` it is
`1/d`. -/
noncomputable def endpointX (d C : ℝ) : ℝ := (1 - Dq C (Yd d C)) / Dq C (Yd d C)

/-- Contact point with the line, `a_e = C Y_d² / D_C(Y_d)` ((20), p.14). -/
noncomputable def aE (d C : ℝ) : ℝ := C * Yd d C ^ 2 / Dq C (Yd d C)

/-- Contact point with the cap, `a_a = C/d²` ((20), p.14). -/
noncomputable def aA (d C : ℝ) : ℝ := C / d ^ 2

/-- `P_e = Y_d / D_C(Y_d)` ((20), p.14). -/
noncomputable def pE (d C : ℝ) : ℝ := Yd d C / Dq C (Yd d C)

/-- `Z_d(C) = ∫_0^{Y_d} r² / D_C(r)² dr` ((21), p.14). -/
noncomputable def Zd (d C : ℝ) : ℝ := ∫ r in (0 : ℝ)..(Yd d C), r ^ 2 / Dq C r ^ 2

/-- `U_d(C) = ∫_0^{Y_d} (Y_d − r) / D_C(r)² dr` ((21), p.14). -/
noncomputable def Ud (d C : ℝ) : ℝ := ∫ r in (0 : ℝ)..(Yd d C), (Yd d C - r) / Dq C r ^ 2

/-- `B_d(C) = 2C − 1 + C(1 − C) Y_d` ((29), p.16). -/
noncomputable def Bd (d C : ℝ) : ℝ := 2 * C - 1 + C * (1 - C) * Yd d C

/-- The tail-time coordinate of the middle arc, `a(r) = (C/d²) e^{−I_C(r)}` ((22), p.14). -/
noncomputable def arcA (d C r : ℝ) : ℝ := C / d ^ 2 * exp (-(ICrun C r))

/-- The state on the middle arc, `P_x(a(r)) = e^{−I_C(r)/2} / (d √D_C(r))` ((22), p.14). -/
noncomputable def arcP (d C r : ℝ) : ℝ := exp (-(ICrun C r) / 2) / (d * sqrt (Dq C r))

/-- The arc parameter at tail time `a`: the `r ∈ [0, Y_d]` with `a(r) = a`, written as
`sup {r ∈ [0, Y_d] | a ≤ a(r)}` (`a(r)` is strictly decreasing from `a_a` to `a_e`). -/
noncomputable def arcR (d C a : ℝ) : ℝ := sSup {r | r ∈ Icc (0 : ℝ) (Yd d C) ∧ a ≤ arcA d C r}

/-- **The reference curve** — Lin, Shi, Dong, Li, Yu, Zhang, *The Exact Welfare Guarantee of
Fixed-Price Bilateral Trade*, arXiv:2609.35888 (held PDF sha256 26832346…), Lemma 6.1, (22),
p.14: `P_x(a) = x + a` on `0 ≤ a ≤ a_e`, the parametric middle arc
`(a(r), e^{−I_C(r)/2}/(d √D_C(r)))`, `0 ≤ r ≤ Y_d(C)`, on `a_e ≤ a ≤ a_a`, and `1/d` for
`a ≥ a_a`; at the limiting endpoint `C = 0`, `P_{1/d} ≡ 1/d` (p.16).

**Formalization Note.** The curve is indexed by the curvature parameter `C`, with endpoint
`x = x(C)`; Lemma 6.1 makes `C ↦ x(C)` a bijection, so this is the paper's `P_x`. The middle arc
is written through the inverse `arcR` of the strictly decreasing `a(r)`; Lemma 6.1 (milestone)
states the parametric identity. For `a < 0` the first branch is used (never evaluated). -/
noncomputable def refCurve (d C a : ℝ) : ℝ :=
  if C = 0 then 1 / d
  else if a ≤ aE d C then endpointX d C + a
  else if a ≤ aA d C then arcP d C (arcR d C a)
  else 1 / d

/-- The multiplier `Q_x` in its almost-everywhere form (24), p.14:
`(1 + x)/(x + a)²` on `(0, a_e)`, `0` on `(a_e, a_a)`, `d²` on `(a_a, ∞)`; at `C = 0`
(`P ≡ 1/d`, `a_e = a_a = 0`) it is `d²`.

**Formalization Note.** Values at the break points are immaterial (a null set). -/
noncomputable def refQ (d C a : ℝ) : ℝ :=
  if C = 0 then d ^ 2
  else if a < aE d C then (1 + endpointX d C) / (endpointX d C + a) ^ 2
  else if a < aA d C then 0
  else d ^ 2

/-- The endpoint envelope `Φ_d(x(C)) = F_d[P_{x(C)}]` ((29), p.16). -/
noncomputable def Phi (d C : ℝ) : ℝ := energy d (refCurve d C)

/-- The logarithmic difference `v(a) = log(p(a)/P_x(a))` ((29), p.16) of the reciprocal state of
the control `h` against the reference curve with parameter `C`. -/
noncomputable def logGap (d : ℝ) (h : ℝ → ℝ) (C a : ℝ) : ℝ :=
  log (recipP d h a / refCurve d C a)

/-- The integrand of (G1), p.16: `a(v′)² + (e^{−2v} − 1 + 2v)/P_x² − 2 Q_x v`. -/
noncomputable def gapIntegrand (d : ℝ) (h : ℝ → ℝ) (C a : ℝ) : ℝ :=
  a * deriv (logGap d h C) a ^ 2 +
    (exp (-2 * logGap d h C a) - 1 + 2 * logGap d h C a) / refCurve d C a ^ 2 -
    2 * refQ d C a * logGap d h C a

/-- The integrand of (G2), p.16: `(Y_d(u) + U_d(u)) |B_d(u)| / (1 − u Y_d(u))²`. -/
noncomputable def envelopeIntegrand (d u : ℝ) : ℝ :=
  (Yd d u + Ud d u) * |Bd d u| / (1 - u * Yd d u) ^ 2

end FixedPriceTrade


