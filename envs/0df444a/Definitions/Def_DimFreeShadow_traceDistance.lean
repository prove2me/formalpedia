-- Prove2me | Definitions.Def_DimFreeShadow_traceDistance
-- name    : DimFreeShadow_traceDistance
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:01:51.928353+00:00
-- url     : https://prove2.me/theorems/b963034a-72df-49b5-ba7a-d149711d0b96
-- title:
--   Trace distance $d_{\mathrm{tr}}(\rho,\sigma)=\frac12\|\rho-\sigma\|_1$
-- statement:
--   The **trace distance** between two operators on the same space is
--
--   $$
--   d_{\mathrm{tr}}(\rho,\sigma)=\tfrac12\|\rho-\sigma\|_1 ,
--   $$
--
--   where $\|\cdot\|_1$ is the trace norm. It is the metric of the net argument of §5.3 and of the Fuchs–van de Graaf step in Lemma 4.3.
--
--   **Formalization Note** The trace norm is the published `WildeQIT.traceNorm`. The published `WildeQIT.traceDist` has no factor $\frac12$, so the normalized distance is defined here.
-- source:
--   Jeronimo, Huang, Liu, Dimension-Free Polylogarithmic Quantum Shadow Tomography, arXiv:2608.06345 (sha256 a1a42249…), §5.3, p.23

import Mathlib
import Definitions.Def_WildeQIT_traceNorm

namespace DimFreeShadow

/-- **Trace distance** `d_tr(ρ, σ) = ½‖ρ − σ‖₁` (arXiv:2608.06345, sha256 a1a42249…, §5.3, p.23:
"We use the trace distance dtr(ρ, σ) = 1/2∥ρ − σ∥1").

**Formalization Note** `‖·‖₁` is the published trace norm `WildeQIT.traceNorm`
(`‖A‖₁ = Tr √(A†A)`). The published `WildeQIT.traceDist` has no factor `½`, so this paper's
normalized distance is defined here. -/
noncomputable def traceDistance {n : Type} [Fintype n] [DecidableEq n]
    (ρ σ : Matrix n n ℂ) : ℝ :=
  (1 / 2) * WildeQIT.traceNorm (ρ - σ)

end DimFreeShadow


