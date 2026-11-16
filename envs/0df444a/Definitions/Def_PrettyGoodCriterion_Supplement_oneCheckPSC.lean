-- Prove2me | Definitions.Def_PrettyGoodCriterion_Supplement_oneCheckPSC
-- name    : PrettyGoodCriterion_Supplement_oneCheckPSC
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T20:31:43.795202+00:00
-- url     : https://prove2.me/theorems/f08a7fd5-363b-4908-b60d-5ef33aa0f6c9
-- title:
--   The weight-three error function $e_3^{\mathrm{LDPC}}(p)$ and the one-check PSC curve $U_3^{\mathrm{PSC}}(\delta)$
-- statement:
--   The **weight-three error function** is
--   $$
--   e_3^{\mathrm{LDPC}}(p):=\frac{1+4p(1-p)-(1-2p)\sqrt{1+12p(1-p)}}{4}.\qquad(57)
--   $$
--   It is the error of the equal-prior Helstrom measurement that decodes one bit of a pure-state-channel output from the three outputs indexed by one weight-three parity check (Lemma 29). The **one-check PSC curve** is
--   $$
--   U_3^{\mathrm{PSC}}(\delta):=\inf_{\substack{0<p<\frac12\\ e_3^{\mathrm{LDPC}}(p)<\delta}} h\!\left(\frac12-\sqrt{p(1-p)}\right),\qquad(58)
--   $$
--   with $h$ the base-2 binary entropy. The paper also gives a closed form for it; that closed form is a claim, and the definition here is the infimum. Theorem 4 shows $R_3(\delta)\le U_3^{\mathrm{PSC}}(\delta)$ and compares $U_3^{\mathrm{PSC}}$ with the first MRRW bound and the Shangguan–Yang curve.
--
--   **Formalization Note** The infimum is the real `sInf` of the image of $\{p:0<p<\tfrac12,\ e_3^{\mathrm{LDPC}}(p)<\delta\}$, kept with its strict inequalities as printed. For $\delta>0$ this set is nonempty ($e_3^{\mathrm{LDPC}}(p)\to0$ as $p\to0^+$), and the objective is positive on it, so `sInf` is the true infimum. $h$ is the published `HoneycombCodes.H2`, the same base-2 binary entropy as in the first MRRW bound `HoneycombCodes.M1`.
-- source:
--   Alrabiah, Guruswami, Binary code rate bounds via classical–quantum channels, arXiv:2608.09347 (held version, sha256 e6d5ac13…), equation (57), p.48 (PDF 50); equation (58), p.50 (PDF 52); Theorem 4, p.5 (PDF 7)

import Mathlib
import Definitions.Def_HoneycombCodes_H2

set_option autoImplicit false

namespace PrettyGoodCriterion.Supplement

/-- The **weight-three error function**
`e_3^LDPC(p) := (1 + 4p(1 − p) − (1 − 2p)√(1 + 12p(1 − p))) / 4`,
Alrabiah–Guruswami, *Binary code rate bounds via classical–quantum channels*, arXiv:2608.09347
(held version), equation (57), p.48 (PDF 50). -/
noncomputable def ldpcError3 (p : ℝ) : ℝ :=
  (1 + 4 * p * (1 - p) - (1 - 2 * p) * Real.sqrt (1 + 12 * p * (1 - p))) / 4

/-- The **one-check PSC curve**
`U_3^PSC(δ) := inf_{0 < p < 1/2, e_3^LDPC(p) < δ} h(1/2 − √(p(1 − p)))`,
Alrabiah–Guruswami, arXiv:2608.09347 (held version), equation (58), p.50 (PDF 52); used in Theorem 4,
p.5 (PDF 7). `h` is the base-2 binary entropy (p.14).

**Formalization Note.** Defined by the infimum on the left of (58), as the real `sInf` of the image of
the feasible set `{p | 0 < p < 1/2, e_3^LDPC(p) < δ}` (strict constraints, as printed); the closed form
on the right of (58) is a claim of the paper, not the definition. For `δ > 0` the set is nonempty
(`e_3^LDPC(p) → 0` as `p → 0⁺`) and the objective is positive on it, so `sInf` is the true infimum.
`h` is the published `HoneycombCodes.H2` (`−t log₂ t − (1 − t) log₂(1 − t)`), the same
binary entropy as in the first MRRW bound `HoneycombCodes.M1`. -/
noncomputable def oneCheckPSC (δ : ℝ) : ℝ :=
  sInf ((fun p : ℝ => HoneycombCodes.H2 (1 / 2 - Real.sqrt (p * (1 - p))))
    '' {p : ℝ | 0 < p ∧ p < 1 / 2 ∧ ldpcError3 p < δ})

end PrettyGoodCriterion.Supplement


