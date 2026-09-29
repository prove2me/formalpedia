-- Prove2me | Definitions.Def_PhiDivRobust_Counterpart_conj
-- name    : PhiDivRobust_Counterpart_conj
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T18:47:16.089731+00:00
-- url     : https://prove2.me/theorems/51f7d31e-ef72-421b-b82a-4d9d8f2a221b
-- title:
--   Conjugate φ*(s) = sup_{t ≥ 0} {st − φ(t)}, Eq. (4)
-- statement:
--   The **conjugate** of a φ-divergence function $\phi$ is the function $\phi^*:\mathbb R\to\mathbb R\cup\{+\infty\}$,
--
--   $$\phi^*(s) = \sup_{t\ge 0}\,\{\, s t - \phi(t)\,\}.$$
--
--   The supremum runs over $t\ge0$ only. For example, the Kullback–Leibler function has $\phi^*(s)=e^s-1$, and the modified $\chi^2$-distance $\phi(t)=(t-1)^2$ has $\phi^*(s)=s+s^2/4$ for $s\ge-2$ and $\phi^*(s)=-1$ for $s<-2$. The conjugate is the ingredient of the robust counterpart (13).
--
--   **Formalization Note** The supremum is taken in `EReal`; for a φ-divergence function it is never $-\infty$, since $t=1$ contributes the value $s$.
-- source:
--   Ben-Tal, den Hertog, De Waegenaere, Melenberg, Rennen, Robust Solutions of Optimization Problems Affected by Uncertain Probabilities, Management Sci. 59(2), 2013, p. 344, Eq. (4)

import Mathlib
open Matrix

namespace PhiDivRobust.Counterpart

/-- The conjugate of a φ-divergence function (Ben-Tal et al. 2013, p. 344, Eq. (4)):
`φ*(s) = sup_{t ≥ 0} {s t − φ(t)}`, valued in `EReal`. The supremum runs over `t ≥ 0` only. -/
noncomputable def conj (φ : ℝ → EReal) (s : ℝ) : EReal :=
  ⨆ t ∈ Set.Ici (0 : ℝ), ((s * t : ℝ) : EReal) - φ t

end PhiDivRobust.Counterpart


