-- Prove2me | Definitions.Def_TentNoise_errP
-- name    : TentNoise_errP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-12T06:41:30.294725+00:00
-- url     : https://prove2.me/theorems/5c91cedb-017a-442f-a670-443698ab60ad
-- title:
--   One-step prediction error $\varepsilon_P=\|f-g\|_{L^2(\mu)}$
-- statement:
--   For a fitted map $g:[0,1]\to[0,1]$, the **one-step prediction error** at stationarity is
--
--   $$
--   \varepsilon_P^2:=\mathbb E_{X\sim\mu}\,|f(X)-g(X)|^2,\qquad \varepsilon_P:=\sqrt{\varepsilon_P^2}=\|f-g\|_{L^2(\mu)},
--   $$
--
--   where $f$ is the tent map and $\mu=\mathrm{Unif}[0,1]$. It is the only quantity about $g$ that the upper bound uses.
--
--   **Formalization Note** The expectation is a Bochner integral. For $g$ measurable with $g([0,1])\subseteq[0,1]$ (the hypotheses of every theorem that uses it) the integrand is bounded by $1$ on $[0,1]$, hence integrable, so no default value occurs.
-- source:
--   Huan, Risteski, Wei, Mitigating error propagation in chaotic dynamics via inference-time noising: a view from backward sampling, STOC 2027 submission (manuscript sha256 67925b3e946da20fbfc5ba5a928c6f5743bf4b2ee96e526e8e738f0494f558e6), §2.4, p.5 (PDF p.5); Theorem 3.1, p.6 (‖f − g‖₂ = ε_P)

import Mathlib
import Definitions.Def_TeschlODE_Shared_tentMap
import Definitions.Def_TentNoise_unifI

open MeasureTheory TeschlODE.Shared

namespace TentNoise

/-- The one-step (next-state) prediction error `ε_P` of a fitted map `g`:
`ε_P² := E_{X∼µ} |f(X) − g(X)|²` and `ε_P := √(ε_P²) = ‖f − g‖_{L²(µ)}`
(Huan, Risteski, Wei, *Mitigating error propagation in chaotic dynamics via inference-time noising: a view from backward sampling*, STOC 2027 submission (manuscript sha256 67925b3e…), §2.4, p.5; Theorem 3.1 writes `‖f − g‖₂ = ε_P`).

**Formalization Note** `f` is the published `tentMap 2`; `µ = unifI`. The integral is a Bochner
integral; for `g` measurable with `g([0,1]) ⊆ [0,1]` (the hypotheses of every theorem using it) the
integrand is bounded by `1` on `[0,1]`, hence integrable, so no default value is used. -/
noncomputable def errP (g : ℝ → ℝ) : ℝ :=
  Real.sqrt (∫ x, (tentMap 2 x - g x) ^ 2 ∂unifI)

end TentNoise


