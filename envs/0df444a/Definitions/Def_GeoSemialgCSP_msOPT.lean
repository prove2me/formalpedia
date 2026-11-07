-- Prove2me | Definitions.Def_GeoSemialgCSP_msOPT
-- name    : GeoSemialgCSP_msOPT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:49:16.634506+00:00
-- url     : https://prove2.me/theorems/aca4b835-0f0c-4586-a8aa-65825a025f2e
-- title:
--   Optimum $\mathrm{OPT}(\tilde I_f)$ of the multiscale instance
-- statement:
--   For a payoff $f:[q]^k\to\mathbb R$ and height $h$, $\mathrm{OPT}(\tilde I_f)$ is the maximum of $\mathrm{val}(\phi,\tilde I_f)$ over all labellings $\phi$ of the $k^h$ leaves by $[q]$.
--
--   **Formalization Note** A finite supremum; it is $0$ when $q=0$ (no labelling exists).
-- source:
--   Arvanitakis, Chatziafratis, Makarychev, Hardness of Approximation for Semialgebraic CSPs, manuscript (STOC 2027 submission, held version sha256 ee702c42…), §4.1, p.10 (PDF p.11)

import Mathlib
import Definitions.Def_GeoSemialgCSP_msVal

namespace GeoSemialgCSP

/-- **Optimum `OPT(Ĩ_f)`.** Arvanitakis, Chatziafratis, Makarychev, *Hardness of Approximation for Semialgebraic CSPs*,
manuscript (STOC 2027 submission, held version sha256 ee702c42…), §4.1, printed p.10 (PDF p.11): the maximum of
`val(ϕ, Ĩ_f)` over labellings `ϕ : [m] → [q]` of the leaves of `T_m`.

**Formalization Note.** A finite supremum (a maximum for `q ≥ 1`; `0` for `q = 0`). -/
noncomputable def msOPT {k q : ℕ} (h : ℕ) (f : (Fin k → Fin q) → ℝ) : ℝ :=
  ⨆ ϕ : (Fin h → Fin k) → Fin q, msVal f ϕ

end GeoSemialgCSP


