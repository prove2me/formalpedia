-- Prove2me | Definitions.Def_HeilmanMax3Cut_Supplement_alphaBOV
-- name    : HeilmanMax3Cut_Supplement_alphaBOV
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:01:43.890471+00:00
-- url     : https://prove2.me/theorems/87bec8a5-3913-48b4-8519-e8e4fa7ef670
-- title:
--   The Briët–Oliveira–Vallentin constant $\alpha_{\mathrm{BOV},k}$, Eq. (6)
-- statement:
--   For $k\ge1$,
--
--   $$\alpha_{\mathrm{BOV},k}=\inf_{-1<\rho<0}\frac{1-F^*(k,\rho)}{1-\rho}.$$
--
--   For $k=3$ this is $\alpha_{\mathrm{BOV}}=\alpha_{\mathrm{BOV},3}=0.9563372685\ldots$, the approximation ratio of the Briët–Oliveira–Vallentin algorithm for product-state Quantum MAX-CUT; for general $k$ it is the ratio of rank-$k$ Gaussian rounding for rank-$k$ MAX-CUT.
--
--   **Formalization Note** The infimum is the real infimum of the image of the open interval $(-1,0)$; the set is nonempty and bounded below by $0$.
-- source:
--   Heilman, Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT, arXiv:2608.00333 (held version, sha256 2b4f1d11…), Eq. (6), p.10; p.5

import Mathlib
import Definitions.Def_HeilmanMax3Cut_Supplement_Fstar

namespace HeilmanMax3Cut.Supplement

/-- **The Briët–Oliveira–Vallentin constant `α_BOV,k`.** Heilman, *Sharp Hardness for MAX-3-CUT and Quantum MAX-CUT*, arXiv:2608.00333 (held version,
sha256 2b4f1d11…), Eq. (6), p.10:
`α_BOV,k := inf_{−1<ρ<0} (1 − F*(k, ρ))/(1 − ρ)`. For `k = 3` it is the constant
`α_BOV = α_BOV,3 = 0.9563372685…` of p.5 ("when `k = 3`, we have … `α_BOV,3 = 0.9563372685…`", p.10).

**Formalization Note.** The infimum is the real `sInf` of the image of the open interval `(−1, 0)`.
The set is nonempty, and bounded below by `0` because `|F*(k, ρ)| ≤ 1` there (`F*` is the noise
stability of a unit-vector-valued function), so `sInf` is the true infimum. The second equality of
(6) (attainment at `ρ_BOV,k`) is a claim of the paper, not part of the definition. -/
noncomputable def alphaBOV (k : ℕ) : ℝ :=
  sInf ((fun ρ : ℝ => (1 - Fstar k ρ) / (1 - ρ)) '' Set.Ioo (-1 : ℝ) 0)

end HeilmanMax3Cut.Supplement


