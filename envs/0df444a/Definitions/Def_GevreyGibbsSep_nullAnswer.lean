-- Prove2me | Definitions.Def_GevreyGibbsSep_nullAnswer
-- name    : GevreyGibbsSep_nullAnswer
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:38:42.914377+00:00
-- url     : https://prove2.me/theorems/9210dce6-72c9-403b-a10a-8ed11ee33ba3
-- title:
--   Flat answer $\phi_{\mathrm{null}}=(\log\kappa,0,0,\dots)$
-- statement:
--   The **flat answer** is
--   $$\phi_{\mathrm{null}}=(\log\kappa,0,0,\dots),$$
--   what every derivative oracle returns at a point where the density is constantly $\kappa$ on a neighbourhood. Feeding it in place of every oracle answer defines the **null run** $X^{\mathrm{null}}_n=Q_n(\omega,\phi_{\mathrm{null}},\dots,\phi_{\mathrm{null}})$ and the null outputs $\widehat X^{\mathrm{null}}_n=\Psi_n(\omega,\phi_{\mathrm{null}},\dots,\phi_{\mathrm{null}})$ of (B5), a single instance-independent random process.
-- source:
--   Olivucci, Sobchuk, Hoque, Hnybida, Kim, Shayeghi, Ronagh, Provable Quantum–Classical Separation for Continuous Gibbs Sampling, arXiv:2608.24527 (held version, sha256 d4fd40eb…), Eq. (26), p.11; Eqs. (B3), (B5), p.35

import Mathlib
import Definitions.Def_GevreyGibbsSep_Answer
import Definitions.Def_GevreyGibbsSep_oracle

open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace GevreyGibbsSep

/-- The flat answer `ϕ_null = (log κ, 0, 0, …)` of Eq. (26), p.11 (and (B3), p.35) of
arXiv:2608.24527 (sha256 d4fd40eb…). Feeding it in place of every oracle answer gives the null run
`X^null_n = Q_n(ω, ϕ_null, …, ϕ_null)`, `X̂^null_n = Ψ_n(ω, ϕ_null, …, ϕ_null)` of (B5), p.35. -/
noncomputable def nullAnswer (d : ℕ) (κ : ℝ) : Answer d :=
  fun j _ => if j = 0 then Real.log κ else 0

end GevreyGibbsSep


