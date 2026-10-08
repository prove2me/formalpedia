-- Prove2me | Definitions.Def_BalkemaDeHaan_DiscreteDomain_PiPC
-- name    : BalkemaDeHaan_DiscreteDomain_PiPC
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:05:25.503984+00:00
-- url     : https://prove2.me/theorems/52e184c1-40c5-401f-a197-1ad452aeaf35
-- title:
--   Π_{p,c} — the two-parameter family of discrete residual-life limit laws (p > 0, c ≥ 0)
-- statement:
--   For $p > 0$ and $c \ge 0$ the discrete limit law $\Pi_{p,c}$ is the distribution function which vanishes for $x < 0$ and, for $x \ge 0$, equals
--   $$\Pi_{p,c}(x) = 1 - \exp\Big(-p\Big[1 + \frac{\log(1+cx)}{cp}\Big]\Big) \quad (c > 0), \qquad \Pi_{p,0}(x) = 1 - \exp\Big(-p\Big[1 + \frac{x}{p}\Big]\Big),$$
--   where $[a]$ is the integer part of $a$. For $c > 0$ this is $\Gamma_{\gamma,\alpha}(cx)$ with $\gamma = p$ and $\alpha = (pc)^{-1}$, where $\Gamma_{\gamma,\alpha}(x) = 1 - \exp(-\gamma[1 + \alpha\log(1+x)])$; for $c = 0$ it is $\Pi_p(x/p)$ with $\Pi_\gamma(x) = 1 - \exp(-\gamma[1+x])$, the limit of the $c > 0$ formula as $c \to 0$.
--
--   $\Pi_{p,c}$ is a step function: it has an atom of mass $1 - e^{-p}$ at $0$, its tail $1 - \Pi_{p,c}$ takes the values $e^{-p}, e^{-2p}, \dots$, and its jumps sit at $(e^{kpc}-1)/c$, $k = 0, 1, 2, \dots$ (at $kp$ when $c = 0$), so successive gaps grow by the factor $e^{pc}$. Together with the continuous laws these are all limit types of normed residual life times.
--
--   **Formalization Note** The integer part is `Int.floor`. The cases $c = 0$ and $c > 0$ are separated explicitly: in Lean $\log(1 + 0\cdot x)/(0\cdot p)$ would be the junk value $0$, which would silently give a different law. The definition is meant for $p > 0$, $c \ge 0$ only, and every statement using it assumes this.
-- source:
--   Balkema, de Haan, Residual Life Time at Great Age, Ann. Probab. 2 (1974), p. 793 (PDF 2), definition of Π_{p,c} and Π_{p,0}

import Mathlib

namespace BalkemaDeHaan.DiscreteDomain

/-- The discrete residual-life limit law `Π_{p,c}` of the introduction (p. 793, PDF 2), for
`p > 0` and `c ≥ 0`; `[·]` is the integer part (`Int.floor`).
* For `c > 0`: `Π_{p,c}(x) = Γ_{p,(pc)⁻¹}(cx) = 1 - exp(-p [1 + log(1 + cx)/(cp)])` for `x ≥ 0`.
* For `c = 0`: `Π_{p,0}(x) = Π_p(x/p) = 1 - exp(-p [1 + x/p])` for `x ≥ 0`.
* Every case is `0` for `x < 0` ("All limit distributions vanish for `x < 0`").
The case split keeps `c = 0` from being the junk value of `log(1 + 0·x)/(0·p) = 0`.
The definition is meant only for `p > 0`, `c ≥ 0`; every statement carries those hypotheses. -/
noncomputable def piPC (p c : ℝ) (x : ℝ) : ℝ :=
  if x < 0 then 0
  else if c = 0 then 1 - Real.exp (-p * ((⌊1 + x / p⌋ : ℤ) : ℝ))
  else 1 - Real.exp (-p * ((⌊1 + Real.log (1 + c * x) / (c * p)⌋ : ℤ) : ℝ))

end BalkemaDeHaan.DiscreteDomain


