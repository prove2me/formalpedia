-- Prove2me | Definitions.Def_QMAvsQCIP_tInc
-- name    : QMAvsQCIP_tInc
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T02:46:14.893776+00:00
-- url     : https://prove2.me/theorems/64556559-c1bd-47d4-a1c4-ff09aa0f88c1
-- title:
--   Recovery threshold $t_{\mathrm{inc}}(\lambda,s)$
-- statement:
--   The recovery threshold of Eq. (7):
--   $$
--   t_{\mathrm{inc}}(\lambda,s)=\Big\lceil\frac{s+8\lambda^2}{\gamma(\lambda)}\Big\rceil .
--   $$
--
--   **Formalization Note** At $\lambda=0$, where $\gamma=0$, Lean's division gives $0$; the threshold is only used for large $\lambda$. A proved sanity check gives $t_{\mathrm{inc}}\ge1$ and $2^s\delta^{t_{\mathrm{inc}}(\lambda,s)}\le\varepsilon_{\mathrm{inc}}(\lambda)$ for $\lambda\ge1$.
-- source:
--   Cakan, Separating QMA from QCIP with a Classical Oracle, arXiv:2610.03648 (held version, sha256 687668af…34ec), Section 4.2, Eq. (7), p.19

import Definitions.Def_QMAvsQCIP_gammaL

set_option autoImplicit false

namespace QMAvsQCIP

/-- The recovery threshold `t_inc(λ, s) = ⌈(s + 8λ²)/γ(λ)⌉` (Eq. (7)).

Cakan, *Separating QMA from QCIP with a Classical Oracle*, arXiv:2610.03648 (held version,
sha256 687668af…34ec), Section 4.2, p.19 (PDF p.22): "t_inc(λ, s) = ⌈(s + 8λ²)/γ(λ)⌉".

**Formalization Note.** At `λ = 0` (where `γ = 0`) Lean's division gives `0`; the definition is
used only for large `λ`. -/
noncomputable def tInc (lam s : ℕ) : ℕ := ⌈((s + 8 * lam ^ 2 : ℕ) : ℝ) / (gammaL lam : ℝ)⌉₊

end QMAvsQCIP


