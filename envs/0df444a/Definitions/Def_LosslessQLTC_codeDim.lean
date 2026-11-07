-- Prove2me | Definitions.Def_LosslessQLTC_codeDim
-- name    : LosslessQLTC_codeDim
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:11:32.883327+00:00
-- url     : https://prove2.me/theorems/9b192309-1b74-44bf-bb6a-6bbcd9115774
-- title:
--   The dimension of the CSS code $C(\ker\delta_1^t,\ker\delta_2)$
-- statement:
--   The CSS code of a square complex has qubits on $V_2$, with $C_Z=\ker\delta_2$, $C_X=\ker\delta_1^t$, and parity-check matrices $H_Z=\delta_2$, $H_X=\delta_1^t$. Its dimension is
--
--   $$\dim_{\mathbb F_2}\big(C_Z/C_X^\perp\big)=\dim_{\mathbb F_2}\big(\ker\delta_2/\operatorname{im}\delta_1\big),$$
--
--   and its rate is this dimension divided by $|V_2|$.
--
--   **Formalization Note.** This is the true dimension of the quotient, not the lower bound $n-m_X-m_Z$.
-- source:
--   Cohen, Leigh, Reiner, Ta-Shma, Tzalik, Good Quantum Locally Testable Codes from Lossless Cubical Complexes, arXiv:2610.00525 (held version, sha256 d61f0ed9…), Definition 5.2, p.40; §5.2, p.41

import Mathlib
import Definitions.Def_LosslessQLTC_Level

namespace LosslessQLTC

variable {k : ℕ}

/-- The dimension of the CSS code `C(ker δ_1^t, ker δ_2)` with qubits on `V_2` (arXiv:2610.00525,
held version, sha256 d61f0ed9…, Definition 5.2, p.40, and §5.2, p.41): the dimension over `F₂` of
`C_Z / C_X^⊥ = ker δ_2 / im δ_1`. The rate of the code is this number over `|V_2|`.

**Formalization Note.** This is the true dimension of the quotient, not the lower bound
`n − m_X − m_Z`. -/
noncomputable def codeDim (X : SquareComplex k) : ℕ :=
  Module.finrank (ZMod 2)
    (LinearMap.ker (delta X 2) ⧸
      (LinearMap.range (delta X 1)).comap (LinearMap.ker (delta X 2)).subtype)

end LosslessQLTC


