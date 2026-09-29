-- Prove2me | Definitions.Def_PhiDivRobust_Counterpart_scaledConj
-- name    : PhiDivRobust_Counterpart_scaledConj
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T18:47:37.057985+00:00
-- url     : https://prove2.me/theorems/80cfd6cc-6839-4f7e-a039-5969c52529e7
-- title:
--   Conjugate of the scaled function, (λφ)*(s) = sup_{t ≥ 0} {st − λφ(t)}
-- statement:
--   For $\lambda\in\mathbb R$ and a φ-divergence function $\phi$, the conjugate of the scaled function $\lambda\phi$ is
--
--   $$(\lambda\phi)^*(s) = \sup_{t\ge0}\,\{\, s t - \lambda\phi(t)\,\}\in\mathbb R\cup\{+\infty\}.$$
--
--   It is the conjugate (4) applied to $\lambda\phi$, and it appears in the separated form (15) of the dual objective function in the proof of Theorem 1. For $\lambda = 0$ it is $\sup_{t\ge0} st$, which is $0$ for $s\le0$ and $+\infty$ for $s>0$.
--
--   **Formalization Note** Computed in `EReal` with $\lambda\phi(t)$ read as the `EReal` product, so $0\cdot(+\infty)=0$; this is what makes $(0\phi)^*(s)=\sup_{t\ge0}st$, as in the paper.
-- source:
--   Ben-Tal, den Hertog, De Waegenaere, Melenberg, Rennen, Robust Solutions of Optimization Problems Affected by Uncertain Probabilities, Management Sci. 59(2), 2013, p. 347, proof of Theorem 1, Eq. (15) and the closing paragraph

import Mathlib
open Matrix

namespace PhiDivRobust.Counterpart

/-- The conjugate of the scaled function `λφ` (Ben-Tal et al. 2013, p. 347, proof of Theorem 1):
`(λφ)*(s) = sup_{t ≥ 0} {s t − λ φ(t)}`, valued in `EReal`. With `EReal`'s `0 * ⊤ = 0`,
`(0φ)*(s) = sup_{t ≥ 0} s t`. -/
noncomputable def scaledConj (φ : ℝ → EReal) (lam s : ℝ) : EReal :=
  ⨆ t ∈ Set.Ici (0 : ℝ), ((s * t : ℝ) : EReal) - (lam : EReal) * φ t

end PhiDivRobust.Counterpart


