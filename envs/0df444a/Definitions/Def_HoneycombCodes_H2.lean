-- Prove2me | Definitions.Def_HoneycombCodes_H2
-- name    : HoneycombCodes_H2
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:26:36.086205+00:00
-- url     : https://prove2.me/theorems/b5ef7cf7-38f7-41ef-b6fc-14029e7babb0
-- title:
--   Binary entropy $H_2$, the map $J(q)=(1-\sqrt{1-q})/2$ and $g=H_2\circ J$
-- statement:
--   All logarithms are base $2$. The **binary entropy** is
--
--   $$
--   H_2(t) = -t\log_2 t-(1-t)\log_2(1-t),\qquad 0\log 0 = 0 .
--   $$
--
--   For $0\le q\le 1$ put
--
--   $$
--   J(q)=\frac{1-\sqrt{1-q}}{2},\qquad g(q)=H_2\bigl(J(q)\bigr).
--   $$
--
--   The map $J$ inverts $a\mapsto 4a(1-a)$ on $[0,1/2]$, so $g(4a(1-a)) = H_2(a)$ there. The function $g$ enters the second MRRW exponent (2), the MQC and 2MQC exponents of Appendix D and the constant-weight bridge.
--
--   **Formalization Note** $H_2$ uses `Real.logb 2`, for which $\log_2 0 = 0$, so $0\log 0=0$ holds. The formulas are total on $\mathbb R$; outside $[0,1]$ their values are not used by the mission. This mirrors the published `MetricCodes.binaryEntropy`, whose module is not available in this workspace.
-- source:
--   W. Gay, F. Granha Jeronimo, L. Liu, The Honeycomb Framework for Code Bounds, arXiv:2608.20287v2 (sha256 f4b07e318538a352116042dc4da0d4e9d47cfd979cf302c7fce3324584a3cd51), §1, p.1 (PDF 3), below eq. (2); App. D.1, p.59 (PDF 61)

import Mathlib

set_option autoImplicit false

namespace HoneycombCodes

/-- The **binary entropy** `H₂(t) = −t log₂ t − (1 − t) log₂(1 − t)` (with `0 log 0 = 0`),
Gay, Granha Jeronimo, Liu, *The Honeycomb Framework for Code Bounds*, arXiv:2608.20287v2
(sha256 f4b07e31…cd51), §1, p.1 (PDF 3).

**Formalization Note.** Logarithms are `Real.logb 2`; since `Real.logb 2 0 = 0` the convention
`0 log 0 = 0` holds. The formula is defined on all of `ℝ`; every use in this mission evaluates it
on `[0, 1]`. This mirrors the published `MetricCodes.binaryEntropy` (OpenAI), whose module is not
available in this workspace. -/
noncomputable def H2 (t : ℝ) : ℝ :=
  -(t * Real.logb 2 t) - (1 - t) * Real.logb 2 (1 - t)

/-- The map `J(q) = (1 − √(1 − q))/2` for `0 ≤ q ≤ 1`, arXiv:2608.20287v2, §1 eq. (2), p.1, and
App. D.1, p.59 (PDF 61). It satisfies `4 J(q)(1 − J(q)) = q` on `[0, 1]`.

**Formalization Note.** `Real.sqrt` of a negative number is `0`, so `Jmap q = 1/2` for `q > 1`;
the mission only evaluates `Jmap` on `[0, 1]`. -/
noncomputable def Jmap (q : ℝ) : ℝ :=
  (1 - Real.sqrt (1 - q)) / 2

/-- The function `g(q) = H₂(J(q)) = H₂((1 − √(1 − q))/2)`, `0 ≤ q ≤ 1`, arXiv:2608.20287v2, §1,
p.1 (PDF 3), just below eq. (2), and App. D.1, p.59 (PDF 61). -/
noncomputable def g (q : ℝ) : ℝ :=
  H2 (Jmap q)

end HoneycombCodes


