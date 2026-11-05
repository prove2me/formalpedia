-- Prove2me | Definitions.Def_SpedalieriQHT_qhb
-- name    : SpedalieriQHT_qhb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:48:40.355381+00:00
-- url     : https://prove2.me/theorems/21b59584-8ed0-4049-a297-e24d576364b4
-- title:
--   Quantum Hoeffding bound $H(r)=\sup_{0\le s<1}P(r,s)$
-- statement:
--   For bounded operators $\rho_0,\rho_1$ and a real number $r$, the **quantum Hoeffding bound** (QHB) is
--   $$
--   H(r)=\sup_{0\le s<1}P(r,s)=\sup_{0\le s<1}\frac{-r s-\ln C_s}{1-s},\qquad C_s=\operatorname{Tr}(\rho_0^s\rho_1^{1-s}).
--   $$
--
--   For states $\rho_0,\rho_1$ it is the optimal error exponent of false negatives in asymmetric quantum hypothesis testing when the error exponent of false positives is required to be at least $r$ (Eqs. (13)–(14) of the paper, from Audenaert et al.).
--
--   **Formalization Note** The supremum is taken in the extended reals over $s\in[0,1)$, so it is a genuine supremum and may be $+\infty$.
-- source:
--   Spedalieri–Braunstein, Asymmetric quantum hypothesis testing with Gaussian states, arXiv:1407.0884v3, Sec. II B, Eq. (15), p.3

import Mathlib
import Definitions.Def_SpedalieriQHT_hoeffdingP

namespace SpedalieriQHT

/-- The quantum Hoeffding bound `H(r) = sup_{0 ≤ s < 1} P(r, s)`.

Spedalieri–Braunstein, arXiv:1407.0884v3, Sec. II B, Eq. (15), p.3:
"H(r) := sup_{0≤s<1} P(r, s)".

**Formalization Note.** The supremum is taken in the complete lattice `EReal` over
`s ∈ [0, 1)` (`Set.Ico 0 1`), so it is a genuine supremum and may be `+∞`. -/
noncomputable def qhb {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (ρ0 ρ1 : H →L[ℂ] H) (r : ℝ) : EReal :=
  ⨆ s ∈ Set.Ico (0 : ℝ) 1, hoeffdingP ρ0 ρ1 r s

end SpedalieriQHT


