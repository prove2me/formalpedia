-- Prove2me | Definitions.Def_MetricMinTest_corrK
-- name    : MetricMinTest_corrK
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:04:58.100194+00:00
-- url     : https://prove2.me/theorems/e51af54b-55fe-4e75-afc7-7d1cc4c03d77
-- title:
--   Level correlations $K_s$, display (4.1)
-- statement:
--   For two centers $x,x'$ at level $\mathrm{lev}(x,x')=s$,
--   $$K_s=\sum_{y\in V}g_{\mathrm{lev}(x,y)}g_{\mathrm{lev}(x',y)}=kg_m^2+\sum_{t=s}^{m-1}b^t(g_t^2-g_{t+1}^2)+2g_s\sum_{t=0}^{s-1}b^t(g_t-g_{t+1}),$$
--   with $k=b^m$; empty sums vanish, so $K_0=\kappa$.
--
--   **Formalization Note** Defined by the closed form (the second expression of (4.1)).
-- source:
--   Chen–Fang, Minimum-Mean Testing under Metric Constraints: Shared Information, Certificates, and Adaptivity, STOC 2027 submission (manuscript sha256 dcece1939edb1fcf752ab6152794f04d8762928ada557c99626997db01ad32bb), Eq. (4.1), p.9

import Mathlib

namespace MetricMinTest

/-- **Level-`s` correlation `K_s`**, display (4.1). Chen–Fang, *Minimum-Mean Testing under Metric
Constraints*, STOC 2027 submission (manuscript sha256 dcece193…ad32bb), (4.1), p.9: for two
centers `x, x'` with `lev(x, x') = s`,
`K_s = ∑_{y ∈ V} g_{lev(x,y)} g_{lev(x',y)}
     = k g_m² + ∑_{t=s}^{m−1} b^t (g_t² − g_{t+1}²) + 2 g_s ∑_{t=0}^{s−1} b^t (g_t − g_{t+1})`.

**Formalization Note.** Defined by the closed form, the second line of (4.1), with `k = b^m`;
empty sums vanish. -/
noncomputable def corrK (b m : ℕ) (g : ℕ → ℝ) (s : ℕ) : ℝ :=
  (b : ℝ) ^ m * g m ^ 2 + ∑ t ∈ Finset.Ico s m, (b : ℝ) ^ t * (g t ^ 2 - g (t + 1) ^ 2) +
    2 * g s * ∑ t ∈ Finset.range s, (b : ℝ) ^ t * (g t - g (t + 1))

end MetricMinTest


