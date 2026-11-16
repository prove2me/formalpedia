-- Prove2me | Definitions.Def_FourierRankQLB_Supplement_epsN
-- name    : FourierRankQLB_Supplement_epsN
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T23:16:35.168101+00:00
-- url     : https://prove2.me/theorems/f2d399c5-6960-4a94-8c3d-fa9a648f9fc5
-- title:
--   The accuracy $\varepsilon_n = n\,c_\star\,\bar g_n^{3/2}$ (Eq. (86))
-- statement:
--   For an ambient dimension $n$, with $d_n = 2\lfloor n/2\rfloor$ and $\bar g_n = g_{d_n} = (1-\cos(\alpha/d_n))/2$, $\alpha = \pi/100$ (Eqs. (25), (37)), the accuracy of the exactly feasible family of Theorem 7.7 is
--
--   $$
--   \varepsilon_n = n\, c_\star\, \bar g_n^{3/2}, \qquad c_\star = 10^{-8}.
--   $$
--
--   It is the unscaled error $\varepsilon_{0,d} = c_\star g_d^{3/2}$ of Eq. (74) multiplied by the scale $s = n$; since $\bar g_n = \Theta(n^{-2})$, $\varepsilon_n = \Theta(n^{-2})$.
--
--   **Formalization Note** The power $3/2$ is the real power of the nonnegative number $\bar g_n$.
-- source:
--   Augustino et al., Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank, arXiv:2609.09035, Eq. (86), p.42 (with Eqs. (37), p.25 and (74), p.37)

import Mathlib
import Definitions.Def_FourierRankQLB_Supplement_cStar
import Definitions.Def_FourierRankQLB_gd
import Definitions.Def_FourierRankQLB_dn

namespace FourierRankQLB

namespace Supplement

/-- The accuracy `ε_n = n c⋆ ḡ_n^{3/2}` of Eq. (86), with `ḡ_n = g_{d_n}` (Eq. (37)).

Augustino et al., *Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank*, arXiv:2609.09035, Eq. (86), p. 42 (and Eq. (37), p. 25).

**Formalization Note.** `ḡ_n^{3/2}` is the real power `Real.rpow`; `ḡ_n > 0` for `n ≥ 2`. -/
noncomputable def epsN (n : ℕ) : ℝ := n * cStar * gd (dn n) ^ ((3 : ℝ) / 2)

end Supplement

end FourierRankQLB


