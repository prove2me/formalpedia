-- Prove2me | Definitions.Def_MassartDKW_Binom_Setting
-- name    : MassartDKW_Binom_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T12:40:53.298991+00:00
-- url     : https://prove2.me/theorems/06248cbe-55e7-4046-9519-a4671627f61b
-- title:
--   Lemma 1, p. 1272 — the functions h(p, ε) and φ(t)
-- statement:
--   This file fixes the two functions of Lemma 1 of Massart (1990), on which Theorem 2 and Comment 3 are built.
--
--   Let $p$ be a success probability and write $q = 1 - p$. For $0 < \varepsilon \le q = 1 - p < 1$ the paper sets
--
--   $$
--   h(p,\varepsilon) = (p+\varepsilon)\log\frac{p+\varepsilon}{p} + (q-\varepsilon)\log\frac{q-\varepsilon}{q},
--   $$
--
--   and, for $t \ge 0$,
--
--   $$
--   \varphi(t) = t - \frac{t^2}{2\,(1 + 2t/3)} - \log(1+t).
--   $$
--
--   The quantity $h(p,\varepsilon)$ is the Cramér transform of the Bernoulli law with parameter $p$ evaluated at $p + \varepsilon$; equivalently it is the relative entropy $d(p+\varepsilon \,\|\, p)$ between the Bernoulli laws with parameters $p+\varepsilon$ and $p$. The function $\varphi$ measures how much Lemma 1(ii) improves on the Bernstein-type quadratic lower bound for $h$.
--
--   **Formalization Note.** Both functions are defined on all of $\mathbb R$ (resp. $\mathbb R^2$), with $q$ written out as $1 - p$; Lean's conventions $\log 0 = 0$ and $x/0 = 0$ apply outside the paper's range. At $\varepsilon = q$ the second term of $h$ is $0\cdot\log 0 = 0$, the usual value. Every statement using $h$ assumes $p > 0$, so that $\log((p+\varepsilon)/p)$ is genuine. The platform's Bernoulli relative entropy (`bernoulliRelativeEntropy`) is not reused: the paper defines $h$ as a function of $(p,\varepsilon)$ and states Lemma 1 for that function.
-- source:
--   Massart, The tight constant in the Dvoretzky–Kiefer–Wolfowitz inequality, Ann. Probab. 18 (1990), p. 1272, Lemma 1 (definitions of h and φ)

import Mathlib

namespace MassartDKW.Binom

/-- Massart (1990), Lemma 1, p. 1272: `φ(t) = t − t²/(2(1 + 2t/3)) − log(1 + t)`, for `t ≥ 0`. -/
noncomputable def phi (t : ℝ) : ℝ :=
  t - t ^ 2 / (2 * (1 + 2 * t / 3)) - Real.log (1 + t)

/-- Massart (1990), Lemma 1, p. 1272: with `q = 1 − p`,
`h(p, ε) = (p + ε) log((p + ε)/p) + (q − ε) log((q − ε)/q)`.
It is meaningful for `0 < ε ≤ q = 1 − p < 1`; at `ε = q` the second term is `0 · log 0 = 0`. -/
noncomputable def h (p ε : ℝ) : ℝ :=
  (p + ε) * Real.log ((p + ε) / p) + (1 - p - ε) * Real.log ((1 - p - ε) / (1 - p))

end MassartDKW.Binom


