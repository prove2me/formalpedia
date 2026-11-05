-- Prove2me | Definitions.Def_MagnonCode_AQEDC_psiNorm
-- name    : MagnonCode_AQEDC_psiNorm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:40:23.1362+00:00
-- url     : https://prove2.me/theorems/53187a5e-39be-4c23-b06d-88635c8dbfc9
-- title:
--   Eq. (84): the normalized magnon-states $|\psi_r\rangle$
-- statement:
--   The normalized magnon-states are
--
--   $$
--   |\psi_r\rangle=\left(\frac{(n-2-r)!}{n(n-2)!\,r!}\right)^{1/2}S_-^r|\Psi\rangle,\qquad r=0,\dots,n-2.
--   $$
--
--   **Formalization Note** The factorials use natural-number subtraction, which is meaningful in the stated range $r+2\le n$; every statement of the mission carries that hypothesis.
-- source:
--   Gschwendtner, König, Şahinoğlu, Tang, Quantum Error-Detection at Low Energies, arXiv:1902.02115v2, Eq. (84), p. 54

import Mathlib
import Definitions.Def_MagnonCode_AQEDC_PsiDesc

namespace MagnonCode.AQEDC

/-- **Eq. (84)** (Gschwendtner, König, Şahinoğlu, Tang, *Quantum Error-Detection at Low Energies*, arXiv:1902.02115v2, p. 54): the normalized magnon-state
`|ψ_r⟩ = ((n − 2 − r)! / (n (n − 2)! r!))^{1/2} S₋^r |Ψ⟩`, for `r = 0, …, n − 2`.

**Formalization Note** Natural-number subtraction is meaningful only for `r + 2 ≤ n`, the page's
range; every statement of the mission carries that hypothesis. -/
noncomputable def psiNorm (n r : ℕ) : (Fin n → Fin 2) → ℂ :=
  ((Real.sqrt ((Nat.factorial (n - 2 - r) : ℝ) /
      ((n : ℝ) * (Nat.factorial (n - 2) : ℝ) * (Nat.factorial r : ℝ))) : ℝ) : ℂ) • PsiDesc n r

end MagnonCode.AQEDC


