-- Prove2me | Definitions.Def_Cohen2019_Robust_Phi
-- name    : Cohen2019_Robust_Phi
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T09:06:41.27385+00:00
-- url     : https://prove2.me/theorems/a1f7ef25-2f84-48a4-a4c8-9c3a282b6f4f
-- title:
--   §3.1 — the standard Gaussian CDF $\Phi$ and its inverse $\Phi^{-1}$ (real on $(0,1)$, extended-real on $[0,1]$)
-- statement:
--   Let $Z \sim \mathcal N(0,1)$ be a standard Gaussian random variable. Its cumulative distribution function is
--   $$
--   \Phi(t) = \mathbb P(Z \le t), \qquad t \in \mathbb R .
--   $$
--   $\Phi$ is continuous and strictly increasing from $0$ to $1$, so for $0 < p < 1$ its inverse is
--   $$
--   \Phi^{-1}(p) = \inf\{t \in \mathbb R : p \le \Phi(t)\},
--   $$
--   the unique real $t$ with $\Phi(t) = p$. At the endpoints the inverse is extended by its limits:
--   $$
--   \Phi^{-1}(p) = -\infty \ \text{ for } p \le 0, \qquad \Phi^{-1}(p) = +\infty \ \text{ for } p \ge 1 .
--   $$
--
--   These are the functions in the certified radius $R = \frac{\sigma}{2}\big(\Phi^{-1}(\underline{p_A}) - \Phi^{-1}(\overline{p_B})\big)$ of Cohen, Rosenfeld and Kolter, where "$\Phi^{-1}$ is the inverse of the standard Gaussian CDF". The endpoint values make the radius infinite when $\underline{p_A} = 1$ or $\overline{p_B} = 0$, as the paper observes.
--
--   **Formalization Note** Three declarations: `Phi` is Mathlib's `cdf (gaussianReal 0 1)`; `PhiInvReal` is the real infimum above, used only for $0 < p < 1$ (outside that range it is a junk value $0$); `PhiInv` takes values in `EReal` and is $\bot$ for $p \le 0$, $\top$ for $p \ge 1$, and `PhiInvReal p` in between.
-- source:
--   Cohen, Rosenfeld, Kolter, Certified Adversarial Robustness via Randomized Smoothing, arXiv:1902.02918v2, §3.1, Theorem 1 and eq. (3), p. 4; eqs. (13)–(15), p. 14 (PDF pages)

import Mathlib

namespace Cohen2019.Robust

open MeasureTheory ProbabilityTheory

/-- The standard Gaussian CDF `Φ(t) = ℙ(Z ≤ t)`, `Z ∼ 𝒩(0, 1)`.
Cohen, Rosenfeld, Kolter, *Certified Adversarial Robustness via Randomized Smoothing*,
arXiv:1902.02918v2, §3.1, p. 4 ("Φ⁻¹ is the inverse of the standard Gaussian CDF"); used in
(13)–(15), p. 14, and Appendix A.0.1, pp. 15–16 (PDF pages).

**Formalization Note.** `Φ` is Mathlib's `cdf` of `gaussianReal 0 1`. -/
noncomputable def Phi (t : ℝ) : ℝ := cdf (gaussianReal 0 1) t

/-- The real inverse of `Φ` on `(0, 1)`: `Φ⁻¹(p) = inf {t ∈ ℝ : p ≤ Φ(t)}`.
Cohen–Rosenfeld–Kolter, arXiv:1902.02918v2, §3.1, p. 4; Appendix A, pp. 14–16.

**Formalization Note.** For `0 < p < 1` the set is nonempty and bounded below, `Φ` is continuous
and strictly increasing, and `PhiInvReal p` is the unique `t` with `Φ(t) = p`. Outside `(0, 1)`
the value is a Lean junk value (`sInf ∅ = 0` for `p > 1`, `sInf` of a set unbounded below `= 0`
for `p ≤ 0`, and `0` for `p = 1` as well, since `{t | 1 ≤ Φ t} = ∅`); every statement using
`PhiInvReal` assumes `0 < p < 1`. The endpoint values `Φ⁻¹(0) = −∞`, `Φ⁻¹(1) = +∞` are
carried by `PhiInv`. -/
noncomputable def PhiInvReal (p : ℝ) : ℝ := sInf {t : ℝ | p ≤ Phi t}

/-- The extended-real inverse of `Φ` on `[0, 1]`: `Φ⁻¹(p) = −∞` for `p ≤ 0`, `+∞` for `p ≥ 1`,
and `PhiInvReal p` for `0 < p < 1`. Cohen–Rosenfeld–Kolter, arXiv:1902.02918v2, §3.1, p. 4,
eq. (3) and its restatement (7), p. 13 (PDF pages).

**Formalization Note.** The paper evaluates `Φ⁻¹` at the endpoints `p̲A = 1` or `p̄B = 0`, where the
certified radius is `+∞` (p. 4, "R goes to ∞ as p̲A → 1 and p̄B → 0"). Taking values in `EReal`
makes these endpoints the limits `±∞` instead of a junk real `0`. -/
noncomputable def PhiInv (p : ℝ) : EReal :=
  if p ≤ 0 then ⊥ else if 1 ≤ p then ⊤ else ((PhiInvReal p : ℝ) : EReal)

end Cohen2019.Robust


