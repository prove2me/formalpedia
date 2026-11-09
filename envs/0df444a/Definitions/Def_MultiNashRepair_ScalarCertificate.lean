-- Prove2me | Definitions.Def_MultiNashRepair_ScalarCertificate
-- name    : MultiNashRepair_ScalarCertificate
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:26:40.522091+00:00
-- url     : https://prove2.me/theorems/353dcfc6-f416-4bba-83d5-fc54a6bf3473
-- title:
--   The scalar certificate: $K_f$, $S_f$, $C_f$, $U(f)$, $H_c$ and the constants $s_\star, f_\star, \sigma_\star$
-- statement:
--   For reals $f,H,s$ define
--   $$K_f(H)=\frac{(1+H)\,[f+(2f-1)H]}{f(f+H)},\qquad S_f(H)=\frac{(1+H)^2}{f+H},\qquad C_f(H)=\frac{(1-f)(1+H)}{f+H},$$
--   the scalar value $U(f)=\min_{0\le H\le f}K_f(H)$, and
--   $$H_c(s)=\frac{(1+s)(1-2s^2)}{1-s},\qquad Q_c(s)=2s^3-2s^2-2s+1 .$$
--   $s_\star$ is the unique zero of $Q_c$ on $[0,1/2]$ (where $Q_c$ is strictly decreasing from $1$ to $-1/4$), $f_\star=1-s_\star$, and
--   $$\sigma_\star\approx1.5867$$ is the unique root in $(1,2)$ of $p(\sigma)=\sigma^3-19\sigma^2+27\sigma+1$.
--
--   $K_f$ is the repair coefficient of the limiting potential argument, and $\sigma_\star=\max_{0<f<1}U(f)$ is the approximation constant of the main theorem (Theorem 5.8).
--
--   **Formalization Note** $U(f)$ is written as an infimum over $[0,f]$ (a minimum for $f>0$ by continuity). $s_\star$ is the supremum of $\{s\in[0,1/2]: Q_c(s)\ge0\}$ and $\sigma_\star$ the supremum of $\{s\in[1,2]: p(s)\ge0\}$; by the monotonicity facts above these are the stated roots. Division is total in Lean ($x/0=0$).
-- source:
--   J. Tang, S. Ding, C. Fang, Breaking the One-Player Extension Barrier: History-Aware Repair for Multiplayer Approximate Nash Equilibria, arXiv:2611.06076 (preprint; held version, sha256 34b911ed…5c14), (4.8), p.13; (5.36)–(5.38), p.34; p.35 (Q_c, s⋆, f⋆, σ⋆); Theorem 1.1, p.3 (σ⋆); Lemma 5.9, p.36 (U)

import Mathlib

noncomputable section

namespace MultiNashRepair

/-- The repair coefficient `K_f(H) = (1 + H)[f + (2f − 1)H] / (f(f + H))`
(Tang, Ding, Fang, arXiv:2611.06076, (4.8), p.13, and (5.37), p.34). Real division is total. -/
def Kf (f H : ℝ) : ℝ :=
  (1 + H) * (f + (2 * f - 1) * H) / (f * (f + H))

/-- The limiting descent threshold `S_f(H) = (1 + H)^2/(f + H)` ((5.36), p.34). -/
def Sf (f H : ℝ) : ℝ :=
  (1 + H) ^ 2 / (f + H)

/-- The limiting overlap bound `C_f(H) = (1 − f)(1 + H)/(f + H)` ((5.36), p.34). -/
def Cf (f H : ℝ) : ℝ :=
  (1 - f) * (1 + H) / (f + H)

/-- The scalar value `U(f) = min_{0 ≤ H ≤ f} K_f(H)` (Lemma 5.9, p.36; (5.1), p.15).

**Formalization Note.** Written as the infimum of `K_f` over `[0, f]`; for `0 < f` the function is
continuous on this compact interval, so the infimum is the minimum (Lemma 5.9 states the
attainment). -/
def U (f : ℝ) : ℝ :=
  sInf (Kf f '' Set.Icc 0 f)

/-- `H_c(s) = (1 + s)(1 − 2s^2)/(1 − s)` on `0 ≤ s ≤ 1/2` ((5.38), p.34). -/
def Hc (s : ℝ) : ℝ :=
  (1 + s) * (1 - 2 * s ^ 2) / (1 - s)

/-- The cubic `Q_c(s) = 2s^3 − 2s^2 − 2s + 1` with `H_c'(s) = 2Q_c(s)/(1 − s)^2` (p.35). -/
def Qc (s : ℝ) : ℝ :=
  2 * s ^ 3 - 2 * s ^ 2 - 2 * s + 1

/-- `s⋆`, the unique zero of `Q_c` on `[0, 1/2]` (p.35).

**Formalization Note.** `Q_c` is strictly decreasing on `[0, 1/2]` with `Q_c(0) = 1 > 0` and
`Q_c(1/2) = −1/4 < 0` (p.35), so `{s ∈ [0, 1/2] | Q_c(s) ≥ 0} = [0, s⋆]` and its supremum is
`s⋆`. -/
def sStar : ℝ :=
  sSup {s : ℝ | 0 ≤ s ∧ s ≤ 1 / 2 ∧ 0 ≤ Qc s}

/-- The optimal activation fraction `f⋆ = 1 − s⋆` (p.35). -/
def fStar : ℝ :=
  1 - sStar

/-- The cubic `p(σ) = σ^3 − 19σ^2 + 27σ + 1` of Theorem 1.1, p.3. -/
def sigmaPoly (s : ℝ) : ℝ :=
  s ^ 3 - 19 * s ^ 2 + 27 * s + 1

/-- The approximation constant `σ⋆ ≈ 1.5867`, the unique root in `(1, 2)` of
`σ^3 − 19σ^2 + 27σ + 1` (Theorem 1.1, p.3).

**Formalization Note.** Written as `sup {s ∈ [1, 2] | p(s) ≥ 0}`. Since `p(1) = 10 > 0`,
`p(2) = −13 < 0` and `p` is strictly decreasing on `[1, 2]` (proof of Theorem 5.8, p.35), this set
is `[1, σ⋆]` and the supremum is the root. Theorem 5.8 (milestone) proves the root property and
`σ⋆ = H_c(s⋆) = 9 − 16 f⋆ + 6 f⋆^2`, the paper's second definition (p.35). -/
def sigmaStar : ℝ :=
  sSup {s : ℝ | 1 ≤ s ∧ s ≤ 2 ∧ 0 ≤ sigmaPoly s}

end MultiNashRepair


