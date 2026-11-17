-- Prove2me | Definitions.Def_LinSSWorst_Supplement_Qexp
-- name    : LinSSWorst_Supplement_Qexp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T12:45:51.548967+00:00
-- url     : https://prove2.me/theorems/90a880e1-0384-4363-8964-51902b9d7099
-- title:
--   The exponent $Q(\delta)$ of the quadratic midslice scheme
-- statement:
--   For $0<\delta<1/2$,
--   $$Q(\delta)=\begin{cases}\dfrac13+\dfrac{1+2\delta}{3}\,H_2\!\left(\dfrac{1-2\delta}{1+2\delta}\right), & 0<\delta\le\frac16,\\[2mm] \dfrac23+\dfrac{2\delta}{3}, & \frac16\le\delta<\frac12,\end{cases}$$
--   where $H_2(p)=-p\log_2p-(1-p)\log_2(1-p)$ is the binary entropy. Both branches equal $7/9$ at $\delta=1/6$.
--
--   $Q(\delta)$ is the share-size exponent of Theorem 6.2.
--
--   **Formalization Note** $H_2$ is the published base-two binary entropy `WildeQIT.binaryEntropy`. At $\delta=1/6$ the first branch is used (the branches agree there).
-- source:
--   Nir, Resolving the Worst-Case Complexity of Linear Secret Sharing, preprint (STOC 2027 submission, version of 2026-11-02, sha256 5521cfdb…), Theorem 6.2, p.19

import Mathlib
import Definitions.Def_WildeQIT_binaryEntropy

namespace LinSSWorst.Supplement

/-- The exponent **`Q(δ)`** of Theorem 6.2 (p.19), from O. Nir, *Resolving the Worst-Case Complexity of
Linear Secret Sharing*, preprint (STOC 2027 submission, version of 2026-11-02, sha256 5521cfdb…):
`Q(δ) = 1/3 + ((1 + 2δ)/3) · H₂((1 − 2δ)/(1 + 2δ))` for `0 < δ ≤ 1/6`, and `Q(δ) = 2/3 + 2δ/3` for
`1/6 ≤ δ < 1/2`.

**Formalization Note.** `H₂` is the base-two binary entropy, the published `WildeQIT.binaryEntropy`
(`H₂(p) = −p log₂ p − (1 − p) log₂ (1 − p)`). The two printed branches overlap at `δ = 1/6`, where both
equal `7/9`; the definition uses the first branch for `δ ≤ 1/6` and the second for `δ > 1/6`. Values for
`δ ∉ (0, 1/2)` are not used. -/
noncomputable def Qexp (δ : ℝ) : ℝ :=
  if δ ≤ 1 / 6 then 1 / 3 + (1 + 2 * δ) / 3 * WildeQIT.binaryEntropy ((1 - 2 * δ) / (1 + 2 * δ))
  else 2 / 3 + 2 * δ / 3

end LinSSWorst.Supplement


