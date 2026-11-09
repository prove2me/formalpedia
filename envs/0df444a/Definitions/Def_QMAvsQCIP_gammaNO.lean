-- Prove2me | Definitions.Def_QMAvsQCIP_gammaNO
-- name    : QMAvsQCIP_gammaNO
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T02:48:54.291412+00:00
-- url     : https://prove2.me/theorems/596bb64d-b7c8-4fe1-813e-af5b7246681f
-- title:
--   Soundness error $\gamma_{\mathrm{NO}}(\lambda)$
-- statement:
--   The soundness error of the QMA$^{\mathrm{bb}}$ verifier:
--   $$
--   \gamma_{\mathrm{NO}}(\lambda)=\Big(\delta+\sqrt{a(\lambda)/2^\lambda}\Big)^{1/2},\qquad\delta=2^{-\lceil\lambda/12\rceil},\ a(\lambda)=2q\lceil\log_2|\Sigma|\rceil .
--   $$
-- source:
--   Cakan, Separating QMA from QCIP with a Classical Oracle, arXiv:2610.03648 (held version, sha256 687668af…34ec), Lemma 5, p.26; Definition 10, p.68

import Definitions.Def_QMAvsQCIP_delta
import Definitions.Def_QMAvsQCIP_witLen

set_option autoImplicit false

namespace QMAvsQCIP

/-- The soundness error `γ_NO(λ) = (δ + √(a(λ)/2^λ))^{1/2}` of the QMA^bb verifier, with
`δ = 2^{−⌈λ/12⌉}` and `a(λ) = 2q⌈log₂ |Σ|⌉`.

Cakan, *Separating QMA from QCIP with a Classical Oracle*, arXiv:2610.03648 (held version,
sha256 687668af…34ec), Lemma 5, p.26 (PDF p.29): "Set γ_NO = (δ + √(a(λ)/2^λ))^{1/2} = 2^{−Ω(λ)},
δ = 2^{−⌈λ/12⌉}"; Definition 10, p.68 (PDF p.71): "γ_NO(λ) = (δ + √(a(λ)/2^λ))^{1/2}". -/
noncomputable def gammaNO (lam q : ℕ) : ℝ :=
  Real.sqrt (delta lam + Real.sqrt ((witLen lam q : ℝ) / (2 : ℝ) ^ lam))

end QMAvsQCIP


