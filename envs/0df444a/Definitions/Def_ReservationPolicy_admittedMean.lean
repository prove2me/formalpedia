-- Prove2me | Definitions.Def_ReservationPolicy_admittedMean
-- name    : ReservationPolicy_admittedMean
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T20:22:09.320404+00:00
-- url     : https://prove2.me/theorems/e466ae05-bcdf-4895-8beb-9d35e914ffc7
-- title:
--   Expected ability of admitted students $E[m+\varepsilon\mid m+\varepsilon>d]$
-- statement:
--   The reward of an admitted student equals the expected ability of the admitted students of her group. For a group of mean ability $m$ at cutoff $d$ this is the conditional expectation
--   $$
--   E\bigl[m+\varepsilon\mid m+\varepsilon>d\bigr]=\frac{1}{\rho(m,d)}\int_{\{m+\varepsilon>d\}}(m+\varepsilon)\,\mathrm d\Pr .
--   $$
--   This is the source of the market reward $r_i$ of the paper; its closed form (10) is the theorem `eq_10`.
--
--   **Formalization Note** The value is a set integral divided by the admission probability. The equilibrium predicates require that probability to be positive, so the division never degenerates there.
-- source:
--   Bao, Ni & Singh, Educational Inequality and Reservation Policy in Developing Markets, SSRN 3772113 (May 30, 2023), p.10

import Mathlib
import Definitions.Def_ReservationPolicy_admitProb

open MeasureTheory

namespace ReservationPolicy

/-- The expected ability of the admitted students of a group with mean ability `m` at cutoff `d`,
`E[m + ε | m + ε > d]`. Bao, Ni & Singh, SSRN 3772113 (May 30, 2023), p.10 (PDF 10).

**Formalization Note** The set integral over the admission event divided by `admitProb m d`. The
integrand is bounded on the event and the noise measure is finite, so the integral is genuine.
The division is guarded by the equilibrium predicates, which require `admitProb` to be positive
(`investEfforts`, `plainEfforts`). -/
noncomputable def admittedMean (m d : ℝ) : ℝ :=
  (∫ ε in {ε | d < m + ε}, (m + ε) ∂noise) / admitProb m d

end ReservationPolicy


