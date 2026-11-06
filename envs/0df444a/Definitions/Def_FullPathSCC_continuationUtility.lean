-- Prove2me | Definitions.Def_FullPathSCC_continuationUtility
-- name    : FullPathSCC_continuationUtility
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:21:34.701821+00:00
-- url     : https://prove2.me/theorems/37140477-9342-4af6-b58a-1c6396e2a8bc
-- title:
--   (6) — the full-path certainty equivalent $\mathcal E^{FP}_t$ and the full-path accumulated preference $V_t$
-- statement:
--   The objects of §2.3 in their abstract setting. On a probability space with a filtration $(\mathcal F_t)$, write $E_t$ for the conditional expectation given $\mathcal F_t$ (the events up to and including time $t$). For $k>0$ and $0<\beta<1$,
--
--   $$
--   \mathcal E^{FP}_t(X)=-\frac1{k\beta^t}\ln E_t\bigl[e^{-k\beta^tX}\bigr],
--   $$
--
--   and for per-stage utilities $u(c_s)$, $s\le N$, the full-path accumulated preference is
--
--   $$
--   V_t=-\frac1{k\beta^t}\ln E_t\Bigl[e^{-k\beta^t\sum_{s=t}^N\beta^{s-t}u(c_s)}\Bigr]=\mathcal E^{FP}_t\Bigl(\sum_{s=t}^N\beta^{s-t}u(c_s)\Bigr).
--   $$
-- source:
--   Zhao, Basu, Lontzek & Schmedders, The Social Cost of Carbon When We Wish for Full-Path Robustness, Management Science 69(12) (2023), doi:10.1287/mnsc.2023.4736, §2.3, p.7589 (the definition of $\mathcal E^{FP}_t$ and (6)); §2, p.7587 (the operators $E_t$)

import Mathlib

namespace FullPathSCC

open MeasureTheory

variable {Ω : Type*} {m0 : MeasurableSpace Ω}

/-- The full-path certainty equivalent of §2.3 (Management Science 69(12) (2023), p.7589):
`ℰ^FP_t(·) = −(1/(kβ^t)) ln(E_t[e^{−kβ^t(·)}])`, where `E_t` is the conditional expectation given
the events up to and including time `t` (§2.1, p.7587), modeled by the filtration `ℱ`.

**Formalization Note** The value is a random variable, defined up to `P`-null sets, as every
conditional expectation is. -/
noncomputable def fullPathCE (P : Measure Ω) (ℱ : Filtration ℕ m0) (k β : ℝ) (t : ℕ)
    (X : Ω → ℝ) : Ω → ℝ :=
  fun ω => -(1 / (k * β ^ t)) *
    Real.log ((P[fun ω' => Real.exp (-(k * β ^ t) * X ω') | ℱ t]) ω)

/-- The full-path accumulated preference of (6) (Management Science 69(12) (2023), p.7589):
`V_t = −(1/(kβ^t)) ln E_t[e^{−kβ^t Σ_{s=t}^N β^{s−t} u(c_s)}]`, that is, `ℰ^FP_t` of the discounted
sum of the per-stage utilities from time `t` on.

**Formalization Note** `u s` is the random variable `u(c_s)`, the per-stage utility of the
consumption stream `{c_t}^N_{t=0}` at time `s`. -/
noncomputable def continuationUtility (P : Measure Ω) (ℱ : Filtration ℕ m0) (k β : ℝ) (N : ℕ)
    (u : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fullPathCE P ℱ k β t (fun ω => ∑ s ∈ Finset.Icc t N, β ^ (s - t) * u s ω)

end FullPathSCC


