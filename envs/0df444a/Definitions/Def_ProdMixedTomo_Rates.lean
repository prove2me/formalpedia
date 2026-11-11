-- Prove2me | Definitions.Def_ProdMixedTomo_Rates
-- name    : ProdMixedTomo_Rates
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:13:45.086819+00:00
-- url     : https://prove2.me/theorems/8e15d1bc-f06c-43e3-aecf-d0d73d6730fd
-- title:
--   Logarithm convention, $g(t)=t\log(1/t)$ and the sample bound $\tilde O(X)$
-- statement:
--   The paper's notation (p.13) fixes how logarithms are read in upper bounds: $\log(1/t)$ means $\max\{1,\log(1/t)\}$, and $t\log^a(1/t)=0$ at $t=0$. Accordingly we write
--   $$
--   L(t)=\max\{1,\log t\},\qquad g(t)=\begin{cases} t\,L(1/t), & t>0,\\ 0, & t\le 0,\end{cases}
--   $$
--   so that "$\mathrm{opt}\cdot\log 1/\mathrm{opt}$" is $g(\mathrm{opt})$ and "$\epsilon\log 1/\epsilon$" is $g(\epsilon)$. Note $g(t)\ge t$ for $t>0$. The soft-O sample bound with constant $C$ is
--   $$
--   \tilde O_C(X)=C\cdot X\cdot\bigl(\log(2+X)\bigr)^{C},
--   $$
--   a polylogarithmic factor in the printed argument $X$ itself.
--
--   These conventions are shared by every quantitative statement of the mission.
--
--   **Formalization Note** `log` is the natural logarithm; its base is absorbed in the universal constants. The power $(\log(2+X))^C$ is a real power of a number $\ge\log 2>0$.
-- source:
--   Arulandu, Diakonikolas, Kane, Li, Agnostic Product Mixed State Tomography via Robust Statistics, arXiv:2510.08472 (manuscript of Nov. 3, 2026, sha256 6c87a7ba…), §2 Notation, p.13 (PDF p.15)

import Mathlib

namespace ProdMixedTomo

/-!
# Logarithm convention, the error function `g` and the `Õ` sample bound

Arulandu, Diakonikolas, Kane, Li, *Agnostic Product Mixed State Tomography via Robust Statistics*,
arXiv:2510.08472 (manuscript of Nov. 3, 2026, sha256 6c87a7ba…), §2 Notation, p.13 (PDF p.15):
"In upper bounds, we may implicitly take log(1/t) to mean max{1, log(1/t)} and t log^a(1/t) = 0 at
t = 0".

**Formalization Note.** `log` is the natural logarithm `Real.log`; the base is absorbed by the
universal constants. `Õ(X)` is read as `C·X·(log(2 + X))^C` with a universal `C` (polylog of the
printed argument itself).
-/

/-- The paper's `log t` in upper bounds: `max 1 (log t)` (p.13). Written `L(t)`. -/
noncomputable def logPlus (t : ℝ) : ℝ := max 1 (Real.log t)

/-- The error function `g(t) = t · log(1/t)` under the paper's convention (p.13):
`g(t) = t · max{1, log(1/t)}` for `t > 0` and `g(t) = 0` for `t ≤ 0`. -/
noncomputable def gErr (t : ℝ) : ℝ := if t ≤ 0 then 0 else t * logPlus (1 / t)

/-- The sample bound `Õ(X)` with constant `C`: `C · X · (log(2 + X))^C` (real power). -/
noncomputable def otilde (C X : ℝ) : ℝ := C * X * Real.log (2 + X) ^ C

end ProdMixedTomo


