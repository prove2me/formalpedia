-- Prove2me | Definitions.Def_GrothendieckLB_Supplement_cqCorr
-- name    : GrothendieckLB_Supplement_cqCorr
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T14:40:00.609453+00:00
-- url     : https://prove2.me/theorems/cdd33c03-4fcc-4fc0-9055-58c2df7df257
-- title:
--   Correlation function $H$ of the cubic–quintic scheme
-- statement:
--   Let $(W,X)$ and $(W',X')$ be standard Gaussian vectors in $\mathbb R^2$ such that the two coordinate pairs are independent, $\operatorname{corr}(W,W')=\rho(t)$ and $\operatorname{corr}(X,X')=t$. The correlation function of the cubic–quintic limiting scheme $S=(f,g,\rho_1,\rho_2)$, $\rho_1=\rho$, $\rho_2(t)=t$, is
--   $$
--   H(t)=\frac\pi2\,\mathbb E\bigl[f(W,X)\,g(W',X')\bigr],\qquad -1<t<1 .
--   $$
--
--   **Formalization Note** Defined for all real parameters $(\eta,s_3,s_5)$; the paper's scheme takes the values (10).
-- source:
--   Saha et al., New Lower and Upper Bounds for the Grothendieck Constant, arXiv:2608.11158 (held version, sha256 e7eb5d65…), Definition 4.1, (13), p.24

import Mathlib
import Definitions.Def_GrothendieckLB_Supplement_multiCorr
import Definitions.Def_GrothendieckLB_Supplement_cqRhoPoly
import Definitions.Def_GrothendieckLB_Supplement_cqF
import Definitions.Def_GrothendieckLB_Supplement_cqG

namespace GrothendieckLB

namespace Supplement

/-- The correlation function `H` of the cubic–quintic limiting scheme
`S = (f, g, ρ₁, ρ₂)`, `ρ₁ = ρ`, `ρ₂(t) = t` (Saha et al., *New Lower and Upper Bounds for the Grothendieck Constant*, arXiv:2608.11158 (held version, sha256 e7eb5d65…), Definition 4.1 and (13), p.24):
`H(t) = (π/2) E[f(W, X) g(W′, X′)]`, where `(W, X)` and `(W′, X′)` are standard Gaussian vectors,
the two coordinate pairs are independent, `corr(W, W′) = ρ(t)` and `corr(X, X′) = t`.

**Formalization Note** The two coordinates of `ℝ²` are `z 0 = w` and `z 1 = x`; the
correlation vector is `(ρ(t), t)`. This is `multiCorr` of the pair `(f, g)` of (12), i.e. the
formula of `LimitingScheme.corr` for this scheme. The parameters are free reals; the paper's
are (10). -/
noncomputable def cqCorr (η s₃ s₅ : ℝ) (t : ℝ) : ℝ :=
  multiCorr (fun z : Fin 2 → ℝ => cqF η s₃ s₅ (z 0) (z 1))
    (fun z : Fin 2 → ℝ => cqG η s₃ s₅ (z 0) (z 1)) ![(cqRhoPoly s₃ s₅).eval t, t]

end Supplement

end GrothendieckLB


