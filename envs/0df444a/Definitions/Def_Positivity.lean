-- Prove2me | Definitions.Def_Positivity
-- name    : Positivity
-- status  : Definition
-- author  : @Somehow
-- created : 2026-10-09T05:25:39.795056+00:00
-- url     : https://prove2.me/theorems/1a876692-16dc-438b-afd3-276cc2732f2b
-- title:
--   Positivity of every certificate weight, and the polynomials $P(u,v)$, $Q(u,v)$
-- statement:
--   This module records that every weight occurring in the all-$N$ Nesterov certificate is strictly positive: the momentum weights $h_j$ (13.1), the capital sequence $H_j$ (strictly increasing from $H_0 = 1$, by (5.1)), the sequence $D_j$ on its valid range, the interpolation weights $a_j$ and $b_j$ (Lemma 13.1), the initial-square coefficients $\alpha_j$ (§14), the terminal coefficient $\beta_T$ ((15.1)-(15.3)) and the interior coefficients $\beta_j$ ((16.1)-(16.4)). The two coefficient sequences introduced explicitly here are the polynomials obtained from the substitution (16.1) $j = u+1$, $N = u+v+3$ with $u, v \ge 0$, under which $\beta_j$ (6.3) becomes the ratio $\beta_j = P(u,v)/Q(u,v)$ with
--
--   $$Q(u,v) = 128\,(u+4)^2 (u+v+4)(u+v+5)\bigl(u^2 + 4uv + 2v^2 + 15u + 26v + 42\bigr).$$
--
--   Here $P(u,v)$ is the degree-$8$ polynomial in $u,v$ of (16.2)-(16.3) whose every coefficient is strictly positive, and $Q(u,v)$ is the factored denominator of (16.4) whose every factor is strictly positive for $u,v \ge 0$; the factor $u^2 + 4uv + 2v^2 + 15u + 26v + 42$ is $8\,D_{j+2}$ under the substitution. The running index $j$ and the horizon $N$ stay universally quantified throughout, so none of the positivity claims is a finite enumeration: each is proved symbolically.
-- source:
--   《有理动量 Nesterov 紧界与半径归一化五算法共同最坏情形 — 可审计完整证明稿》 (manuscript, 2026-10-08), §13-§16, eq. (13.1), (15.1)-(15.3), (16.2)-(16.4); Lean: FullFormalization.Positivity lines 1-156

-- Generated from F:/20261008/FullFormalization\FullFormalization\Positivity.lean by skeleton subtraction (Phase 3-4):
-- every unselected declaration deleted, project imports rewritten.
/-
  FullFormalization.Positivity

  Source sections 13-16: positivity of every weight in the certificate.

    * `h_pos`      — (13.1)
    * `H_pos`      — `H` is strictly increasing from `H_0 = 1`, by (5.1)
    * `D_pos`      — `D_j > 0` on the valid range
    * `a_pos`      — Lemma 13.1, first half
    * `b_pos`      — Lemma 13.1, second half; uses the identity
                     `b_j = H_j (j+3)/(4 D_j D_{j+1}) + h_j/D_j` derived from
                     (5.1) and (5.5), so positivity is immediate from `H, h, D > 0`
    * `alpha_pos`  — section 14
    * `betaT_eq`, `betaT_pos` — (15.1), (15.2), (15.3)
    * `beta_eq_P`, `beta_pos` — (16.2)-(16.4), via the source's substitution
                     `j = u + 1`, `N = u + v + 3`, `u, v >= 0`, and the explicit
                     polynomials `Pbeta (16.2)`, `Qbeta (16.3)` with all-positive
                     coefficients (`Pbeta_pos`, `Qbeta_pos`)

  None of these is a finite enumeration: the running index and `N` stay
  universally quantified throughout, and every statement is proved
  symbolically.
-/

import Mathlib
import Definitions.Def_Certificate
import Definitions.Def_Coefficients

open scoped Gradient RealInnerProductSpace

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

namespace FullFormalization

/-! ### (13.1) `h_j > 0` -/





/-! ### `H_j > 0` -/





/-! ### `a_j > 0` and `b_j > 0`  (Lemma 13.1) -/









/-! ### Section 14: `alpha_j > 0` -/



/-! ### Section 15: `β_T > 0`  —  (15.1), (15.2), (15.3)

`β_T = ½ (a_{N-1} - (m_{N-1} + b_N)²)` by (6.5).  Evaluating the three pieces in
closed form — `a_{N-1} = N(N+7)/(N²+9N+6)`, `m_{N-1} = (N-1)/(N+2)`,
`b_N = 1 - a_{N-1}` — gives the rational function (15.1); the source then
substitutes `N = u + 2` to put the numerator in the all-positive form (15.2). -/







/-! ### Section 16: `β_j > 0`  —  (16.1)-(16.4)

Source (16.1) substitutes `j = u + 1`, `N = u + v + 3` with `u, v >= 0`, under
which `β_j` (6.3) becomes the ratio `P(u,v)/Q(u,v)` of the two polynomials
below; both have all coefficients of one sign, so `β_j > 0` is immediate.

The two coefficient lists are those of `scripts/gen_beta_data.py`, which
regenerates them exactly from the definitions of `a`, `b`, `h`, `H`, `D`, `m`,
`d` in `Coefficients.lean` (source (4.1)-(4.13)).  The source prints the
denominator factor `u² + 4uv + 2v² + 15u + 26v + 42`, which is `8 * D_{j+2}`
under the substitution; the factor `128 (u+4)² (u+v+4)(u+v+5)` likewise collects
the denominators `8 (N+1)(N+2)` of `H`, `2 (N+1)(N+2)` of `h` and `k + 3 = u+4`
of `m`.  Both `P` and `Q` are the sign-flipped (positive) versions: the raw
SymPy output carries an overall sign on each. -/

/-- The numerator `P(u,v)` of (16.2)-(16.3): the source's polynomial after the
substitution (16.1).  Every coefficient is strictly positive. -/
noncomputable def Pbeta (u v : ℕ) : ℝ :=
      15 * (u : ℝ) ^ 8
    + 140 * (u : ℝ) ^ 7 * (v : ℝ)
    + 656 * (u : ℝ) ^ 7
    + 446 * (u : ℝ) ^ 6 * (v : ℝ) ^ 2
    + 5034 * (u : ℝ) ^ 6 * (v : ℝ)
    + 11956 * (u : ℝ) ^ 6
    + 624 * (u : ℝ) ^ 5 * (v : ℝ) ^ 3
    + 12806 * (u : ℝ) ^ 5 * (v : ℝ) ^ 2
    + 74002 * (u : ℝ) ^ 5 * (v : ℝ)
    + 119706 * (u : ℝ) ^ 5
    + 532 * (u : ℝ) ^ 4 * (v : ℝ) ^ 4
    + 14312 * (u : ℝ) ^ 4 * (v : ℝ) ^ 3
    + 145610 * (u : ℝ) ^ 4 * (v : ℝ) ^ 2
    + 574266 * (u : ℝ) ^ 4 * (v : ℝ)
    + 718229 * (u : ℝ) ^ 4
    + 240 * (u : ℝ) ^ 3 * (v : ℝ) ^ 5
    + 8648 * (u : ℝ) ^ 3 * (v : ℝ) ^ 4
    + 120432 * (u : ℝ) ^ 3 * (v : ℝ) ^ 3
    + 829466 * (u : ℝ) ^ 3 * (v : ℝ) ^ 2
    + 2531306 * (u : ℝ) ^ 3 * (v : ℝ)
    + 2632246 * (u : ℝ) ^ 3
    + 40 * (u : ℝ) ^ 2 * (v : ℝ) ^ 6
    + 2312 * (u : ℝ) ^ 2 * (v : ℝ) ^ 5
    + 46324 * (u : ℝ) ^ 2 * (v : ℝ) ^ 4
    + 459472 * (u : ℝ) ^ 2 * (v : ℝ) ^ 3
    + 2471968 * (u : ℝ) ^ 2 * (v : ℝ) ^ 2
    + 6304676 * (u : ℝ) ^ 2 * (v : ℝ)
    + 5724072 * (u : ℝ) ^ 2
    + 152 * (u : ℝ) * (v : ℝ) ^ 6
    + 5992 * (u : ℝ) * (v : ℝ) ^ 5
    + 93936 * (u : ℝ) * (v : ℝ) ^ 4
    + 777736 * (u : ℝ) * (v : ℝ) ^ 3
    + 3599400 * (u : ℝ) * (v : ℝ) ^ 2
    + 8139072 * (u : ℝ) * (v : ℝ)
    + 6702624 * (u : ℝ)
    + 112 * (v : ℝ) ^ 6
    + 3920 * (v : ℝ) ^ 5
    + 56880 * (v : ℝ) ^ 4
    + 445744 * (v : ℝ) ^ 3
    + 1942304 * (v : ℝ) ^ 2
    + 4125504 * (v : ℝ)
    + 3194496

/-- The denominator `Q(u,v)` of (16.2)-(16.3), in factored form.  Every factor
is strictly positive on `u, v >= 0`. -/
noncomputable def Qbeta (u v : ℕ) : ℝ :=
  128 * ((u : ℝ) + 4) ^ 2 * ((u : ℝ) + (v : ℝ) + 4) * ((u : ℝ) + (v : ℝ) + 5)
    * ((u : ℝ) ^ 2 + 4 * (u : ℝ) * (v : ℝ) + 2 * (v : ℝ) ^ 2
        + 15 * (u : ℝ) + 26 * (v : ℝ) + 42)









end FullFormalization


