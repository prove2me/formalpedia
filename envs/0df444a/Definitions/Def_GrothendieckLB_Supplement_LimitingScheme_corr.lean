-- Prove2me | Definitions.Def_GrothendieckLB_Supplement_LimitingScheme_corr
-- name    : GrothendieckLB_Supplement_LimitingScheme_corr
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T14:37:46.503725+00:00
-- url     : https://prove2.me/theorems/22bd66ad-e0ad-45a3-858f-343304f9faba
-- title:
--   Correlation function $H_{f,g,\rho}$ of a limiting scheme
-- statement:
--   The arcsine-normalized correlation function of a limiting Krivine scheme $S=(f,g,\rho)$ is
--   $$
--   H_{f,g,\rho}(t)=\frac\pi2\,\mathbb E[f(X)\,g(Y)],\qquad -1<t<1,
--   $$
--   where $X,Y\in\mathbb R^k$ are jointly Gaussian with $\mathbb E[X_iX_j]=\mathbb E[Y_iY_j]=\delta_{ij}$ and $\mathbb E[X_iY_j]=\delta_{ij}\rho_i(t)$.
--
--   **Formalization Note** Defined on all of $\mathbb R$; only $t\in(-1,1)$ and the germ at $0$ are used.
-- source:
--   Saha et al., New Lower and Upper Bounds for the Grothendieck Constant, arXiv:2608.11158 (held version, sha256 e7eb5d65…), Definition 3.6, p.18

import Mathlib
import Definitions.Def_GrothendieckLB_Supplement_LimitingScheme
import Definitions.Def_GrothendieckLB_Supplement_multiCorr

namespace GrothendieckLB

namespace Supplement

/-- The arcsine-normalized correlation function of a limiting Krivine scheme
(Saha et al., *New Lower and Upper Bounds for the Grothendieck Constant*, arXiv:2608.11158 (held version, sha256 e7eb5d65…), Definition 3.6, p.18): `H_{f,g,ρ}(t) = (π/2) E[f(X) g(Y)]` for `t ∈ (−1, 1)`, where
`X, Y ∈ ℝ^k` are jointly Gaussian with `E[X_i X_j] = E[Y_i Y_j] = δ_ij` and
`E[X_i Y_j] = δ_ij ρ_i(t)`.

**Formalization Note** Defined on all of `ℝ`; only `t ∈ (−1, 1)` is meaningful and every
statement restricts to it or to the germ at `0`. -/
noncomputable def LimitingScheme.corr {k : ℕ} (S : LimitingScheme k) (t : ℝ) : ℝ :=
  multiCorr S.f S.g (fun i => S.ρ i t)

end Supplement

end GrothendieckLB


