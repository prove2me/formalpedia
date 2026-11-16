-- Prove2me | Definitions.Def_ProdMixedTomo_Supplement_gHalf
-- name    : ProdMixedTomo_Supplement_gHalf
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T22:30:24.96465+00:00
-- url     : https://prove2.me/theorems/87eec5d9-96eb-4bf7-9941-1428a24cdd17
-- title:
--   The error rate $t\sqrt{\log(1/t)}$
-- statement:
--   Under the paper's convention for upper bounds ($\log(1/t)$ means $\max\{1,\log(1/t)\}$, and $t\log^a(1/t)=0$ at $t=0$), the error rate $t\sqrt{\log(1/t)}$ is the function
--   $$
--   g_{1/2}(t)=\begin{cases} t\,\sqrt{\max\{1,\log(1/t)\}}, & t>0,\\ 0, & t\le 0.\end{cases}
--   $$
--   It satisfies $g_{1/2}(t)\ge t$ for $t>0$.
--
--   It is the error rate of the pure-state tomography result (Theorem 3.6, $O(\mathrm{opt}\sqrt{\log(1/\mathrm{opt})})$) and of robust $\ell_2$ mean estimation (Theorem A.1, $\epsilon\sqrt{\log 1/\epsilon}$).
--
--   **Formalization Note** $\log$ is the natural logarithm (the base mission's `logPlus`); its base is absorbed by the universal constants.
-- source:
--   Arulandu, Diakonikolas, Kane, Li, Agnostic Product Mixed State Tomography via Robust Statistics, arXiv:2510.08472 (manuscript of Nov. 3, 2026, sha256 6c87a7ba…), §2 Notation, p.13 (PDF p.15); Theorem 3.6, p.19 (PDF p.21); Theorem A.1, p.51 (PDF p.53)

import Mathlib
import Definitions.Def_ProdMixedTomo_Rates

namespace ProdMixedTomo.Supplement

/-- The error rate `t·√(log(1/t))` of Theorems 3.6 and A.1 under the paper's convention.

Arulandu, Diakonikolas, Kane, Li, *Agnostic Product Mixed State Tomography via Robust Statistics*,
arXiv:2510.08472 (manuscript of Nov. 3, 2026, sha256 6c87a7ba…), §2 Notation, p.13 (PDF p.15): "In upper bounds, we may implicitly take log(1/t) to mean
max{1, log(1/t)} and t log^a(1/t) = 0 at t = 0"; Theorem 3.6, p.19 (PDF p.21)
("O(opt √log(1/opt))"); Theorem A.1, p.51 (PDF p.53) ("ϵ√log 1/ϵ").

**Formalization Note.** `gHalf t = t·√(max{1, log(1/t)})` for `t > 0` (base `logPlus`, natural
log) and `0` for `t ≤ 0`; hence `gHalf t ≥ t` for `t > 0`. -/
noncomputable def gHalf (t : ℝ) : ℝ := if t ≤ 0 then 0 else t * Real.sqrt (logPlus (1 / t))

end ProdMixedTomo.Supplement


