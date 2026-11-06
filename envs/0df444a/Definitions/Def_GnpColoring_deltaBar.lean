-- Prove2me | Definitions.Def_GnpColoring_deltaBar
-- name    : GnpColoring_deltaBar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:30:25.976717+00:00
-- url     : https://prove2.me/theorems/1a05553e-0e86-4174-9ee3-d4a018237b27
-- title:
--   The degree threshold $\bar\Delta=d+d^{1/2+\eta}$
-- statement:
--   For real parameters $d$ and $\eta$, the degree threshold is
--
--   $$\bar\Delta = d + d^{1/2+\eta}.$$
--
--   Vertices of degree at most $\bar\Delta$ are *low-degree*; the others are *hubs*. In $G(n,d/n)$ the typical degree is about $d$, so $\bar\Delta$ exceeds it by $d^{1/2+\eta}$, a little more than a standard deviation.
--
--   **Formalization Note** $d^{1/2+\eta}$ is the real power.
-- source:
--   Schiller, Sampling Colorings on G(n, d/n) via Glauber Dynamics, STOC 2027 submission (manuscript sha256 da44ff7b…), Section 3.1, p.15

import Mathlib

open scoped Classical
open Finset

namespace GnpColoring

/-- **The degree threshold** `Δ̄ := d + d^(1/2+η)`.

Schiller, *Sampling Colorings on G(n, d/n) via Glauber Dynamics*, STOC 2027 submission manuscript (sha256 da44ff7b…), Section 3.1, p.15: "we fix constants 0 < η < 1/2, A > 0, and C > 0, and define
Δ̄ := d + d^(1/2+η), and α := C log d > 1."

**Formalization Note** `d^(1/2+η)` is the real power `Real.rpow`. -/
noncomputable def deltaBar (d η : ℝ) : ℝ := d + d ^ ((1 : ℝ) / 2 + η)

end GnpColoring


