-- Prove2me | Definitions.Def_HDXConc_logMGF
-- name    : HDXConc_logMGF
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:59:24.373493+00:00
-- url     : https://prove2.me/theorems/4e2ae7c0-f10f-4ce0-8c7c-6dbd72071b3f
-- title:
--   The centered log-moment generating function $\psi$
-- statement:
--   For a top density $\pi_d$ and $F(\sigma)=\sum_{v\in\sigma}f(v)$,
--
--   $$\psi(t)=\log\mathbb E_{\pi_d}\exp\big(t(F-\mathbb E_{\pi_d}F)\big)=\log\sum_{\sigma\in X(d)}\pi_d(\sigma)\exp\big(t(F(\sigma)-\mathbb E_{\pi_d}F)\big).$$
--
--   This is the logarithm of a positive finite sum of exponentials, so it is a smooth function of $t\in\mathbb R$.
-- source:
--   Das, Hopkins, Ray, Tung, Concentration on HDX: Simplified and Optimized, STOC 2027 submission (manuscript sha256 ea5bee5f…), Proof of Theorem 1.1, p.15

import Mathlib
import Definitions.Def_HDXConc_tilt
import Definitions.Def_HDXConc_topVar

namespace HDXConc

/-!
# The centered log-moment generating function `ψ`

Das, Hopkins, Ray, Tung, *Concentration on HDX: Simplified and Optimized*, STOC 2027 submission
(manuscript sha256 ea5bee5f…), proof of Theorem 1.1, p.15.
-/

variable {V : Type*}

/-- `ψ(t) = log E_{π_d} exp(t (F - E_{π_d} F))` (p.15), with `F = topSum f`. For a positive density on a
nonempty top level, this is the logarithm of a positive finite sum of exponentials. -/
noncomputable def logMGF (X : Finset (Finset V)) (d : ℕ) (π : Finset V → ℝ) (f : V → ℝ) (t : ℝ) : ℝ :=
  Real.log (∑ σ ∈ SteurerHDX.faces X d, π σ * Real.exp (t * (topSum f σ - topMean X d π (topSum f))))

end HDXConc


