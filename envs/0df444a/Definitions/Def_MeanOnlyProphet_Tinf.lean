-- Prove2me | Definitions.Def_MeanOnlyProphet_Tinf
-- name    : MeanOnlyProphet_Tinf
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:21:56.664493+00:00
-- url     : https://prove2.me/theorems/532a6e87-593e-4a11-bdc5-4c833f6affdf
-- title:
--   Survival $S$, area $A$, $k(t)$ and $T_\infty(t)$ for an acceptance rate $q$
-- statement:
--   For a nonnegative acceptance rate $q$ on $[0,1]$, possibly taking the value $+\infty$, define
--   1. the **survival function** $S(t)=\exp\!\left(-\int_0^t q(s)\,ds\right)$;
--   2. the **area** $A(t)=\int_t^1 S(s)\,ds$;
--   3. $k(t)=S(t)-q(t)\,A(t)-A(0)\,e^{-q(t)}$;
--   4. $T_\infty(t)=1-S(t)+q(t)\,A(t)$.
--
--   These use the conventions $e^{-\infty}=0$ and $q(t)\cdot A(t)=0$ whenever $q(t)=+\infty$. In the $n\to\infty$ analysis $S(t)$ is the probability that the rule has not stopped by time $t$, and $T_\infty(t)$ is the limiting probability that the accepted value exceeds $\theta(t)$.
--
--   **Formalization Note** Rates are functions $\mathbb R\to[0,\infty]$; $\int_0^t q$ is a lower Lebesgue integral over $(0,t]$. The helpers `eNeg` ($e^{-a}$ with $e^{-\infty}=0$), `qTimesA` (the product with the convention) and `toRate` (a real rate viewed as an extended one) live in this definition.
-- source:
--   Feng, Jin, Wu, Xiang, Mean-only Prophet Inequalities, arXiv:2610.24711 (held version, sha256 c68bfec4…74e93a), §3.1, pp.6–7 (PDF pp.7–8); App. A.2, p.30 (PDF p.31); Lemma A.4, p.30

import Mathlib

open MeasureTheory

namespace MeanOnlyProphet

/-- **`e^{−a}` with the convention `e^{−∞} = 0`.** Feng, Jin, Wu, Xiang, *Mean-only Prophet
Inequalities*, arXiv:2610.24711 (held version, sha256 c68bfec4…), Lemma A.4, p.30 (PDF p.31): "Use the
conventions e^{−∞} = 0". For finite `a ∈ ℝ≥0∞` it is `Real.exp (-a)`. -/
noncomputable def eNeg (a : ENNReal) : ℝ :=
  if a = ⊤ then 0 else Real.exp (-a.toReal)

/-- A real rate `q` viewed as an extended rate `t ↦ max(q t, 0) ∈ ℝ≥0∞` (`ENNReal.ofReal`). Used to
state results about real, nonnegative rates with the extended-rate functionals. -/
noncomputable def toRate (q : ℝ → ℝ) : ℝ → ENNReal :=
  fun t => ENNReal.ofReal (q t)

/-- **Survival function `S(t) = exp(−∫_0^t q(s) ds)`.** Feng, Jin, Wu, Xiang, *Mean-only Prophet
Inequalities*, arXiv:2610.24711 (held version), §3.1, p.6 (PDF p.7) and App. A.2, p.30 (PDF p.31).

**Formalization Note.** The rate `q : ℝ → ℝ≥0∞` may take the value `+∞`; the integral is the lower
Lebesgue integral over `(0, t]` and `S(t) = 0` when it is infinite (`e^{−∞} = 0`). -/
noncomputable def survS (q : ℝ → ENNReal) (t : ℝ) : ℝ :=
  eNeg (∫⁻ s in Set.Ioc 0 t, q s)

/-- **Area `A(t) = ∫_t^1 S(s) ds`.** Feng, Jin, Wu, Xiang, arXiv:2610.24711 (held version), §3.1, p.6
(PDF p.7). -/
noncomputable def areaA (q : ℝ → ENNReal) (t : ℝ) : ℝ :=
  ∫ s in t..1, survS q s

/-- **The product `q(t) · A(t)` with the convention `q(t) · A(t) = 0` when `q(t) = +∞`.** Feng, Jin,
Wu, Xiang, arXiv:2610.24711 (held version), Lemma A.4, p.30 (PDF p.31). -/
noncomputable def qTimesA (q : ℝ → ENNReal) (t : ℝ) : ℝ :=
  if q t = ⊤ then 0 else (q t).toReal * areaA q t

/-- **`k(t) = S(t) − q(t) · A(t) − A(0) · e^{−q(t)}`.** Feng, Jin, Wu, Xiang, *Mean-only Prophet
Inequalities*, arXiv:2610.24711 (held version, sha256 c68bfec4…), §3.1, p.7 (PDF p.8). -/
noncomputable def kfun (q : ℝ → ENNReal) (t : ℝ) : ℝ :=
  survS q t - qTimesA q t - areaA q 0 * eNeg (q t)

/-- **`T∞(t) = 1 − S(t) + q(t) · A(t)`.** Feng, Jin, Wu, Xiang, *Mean-only Prophet Inequalities*,
arXiv:2610.24711 (held version, sha256 c68bfec4…), App. A.2, p.30 (PDF p.31): "Define T∞(t) = 1 − S(t) +
q(t) · A(t)."

**Formalization Note.** Rates are `ℝ≥0∞`-valued with `e^{−∞} = 0` (`eNeg`) and `q · A = 0` at
`q = +∞` (`qTimesA`), the conventions of Lemma A.4. -/
noncomputable def Tinf (q : ℝ → ENNReal) (t : ℝ) : ℝ :=
  1 - survS q t + qTimesA q t

end MeanOnlyProphet


