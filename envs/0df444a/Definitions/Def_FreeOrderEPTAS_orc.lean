-- Prove2me | Definitions.Def_FreeOrderEPTAS_orc
-- name    : FreeOrderEPTAS_orc
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:24:17.576345+00:00
-- url     : https://prove2.me/theorems/16e7a3fa-d040-41ba-bde5-adb050e1aa61
-- title:
--   The oracle $\mathbb E[\max\{X_i,v\}]$
-- statement:
--   The oracle of Theorem 3.1 returns, for a variable $X_i$ and a number $v$, the value
--   $$\mathbb E[\max\{X_i,v\}].$$
--   It is the only information about the laws that the algorithm of the mission uses.
--
--   **Formalization Note** The programs of the mission receive this function as a value of type `Fin n → ℝ → ℝ`, never the laws, and call it through a counted operation, always with $v\ge0$. The integrand is integrable for every $v$, because $X_i$ has a finite mean.
-- source:
--   Segev & Singla, Efficient Approximation Schemes for Stochastic Probing and Selection-Stopping Problems, arXiv:2007.13121v3, Theorem 3.1, p.17

import Mathlib
import Definitions.Def_FreeOrderEPTAS_Instance

open MeasureTheory

namespace FreeOrderEPTAS

/-- The oracle of Theorem 3.1 (arXiv:2007.13121v3, p.17): `E[max{X_i, v}]`.

**Formalization Note.** The programs of this mission receive this function, as a value of type
`Fin n → ℝ → ℝ`, and never the laws, and call it through the counted `callOrc`, with `v ≥ 0`. The
integrand is integrable for every `v`, since `|max x v| ≤ |x| + |v|` and `μ i` has a finite mean. -/
noncomputable def orc {n : ℕ} (I : Instance n) (i : Fin n) (v : ℝ) : ℝ :=
  ∫ x, max x v ∂(I.μ i)

end FreeOrderEPTAS


