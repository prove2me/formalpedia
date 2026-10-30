-- Prove2me | Definitions.Def_CoffmanMitrani_Data_loadBound
-- name    : CoffmanMitrani_Data_loadBound
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:19:21.132897+00:00
-- url     : https://prove2.me/theorems/e8a12618-e5b8-436a-beba-47b548478e7d
-- title:
--   Right-hand side of inequality (4)
-- statement:
--   For a set $g$ of classes,
--   $$f(g) = \frac{\sum_{i\in g} \rho_i/\mu_i}{1 - \sum_{i\in g}\rho_i}.$$
--   This is the right-hand side of inequality (4); for $g$ the set of all classes it equals $V/(1-\rho)$, the right-hand side of the conservation law. The denominator is positive because $\rho < 1$ and all $\rho_i > 0$, and $f(\emptyset) = 0$, in agreement with the convention on p. 818 that empty sums in (4) are zero.
-- source:
--   Coffman and Mitrani, A Characterization of Waiting Time Performance Realizable by Single-Server Queues, Operations Research 28 (1980), doi:10.1287/opre.28.3.810, §3, p. 817, eq. (4); p. 818

import Mathlib
import Definitions.Def_CoffmanMitrani_Data_rho

namespace CoffmanMitrani

/-- **The right-hand side of inequality (4).**
Coffman and Mitrani, *A Characterization of Waiting Time Performance Realizable by Single-Server
Queues*, Operations Research 28 (1980), doi:10.1287/opre.28.3.810, §3, p. 817, eq. (4): "Σ_{i∈g} ρi Wi ≥ (Σ_{i∈g} ρi/μi)/(1 − Σ_{i∈g} ρi)".

For a set `g` of classes, `D.loadBound g = (Σ_{i∈g} ρi/μi) / (1 − Σ_{i∈g} ρi)`.

**Formalization Note.** `1 − Σ_{i∈g} ρi > 0` for every `g` because all `ρi > 0` and `Σ ρi < 1`, so
there is no division by zero. For `g = ∅` the value is `0`, matching p. 818: "If g12 is empty, we
shall define all sums involved in (4) as zero". -/
noncomputable def Data.loadBound (D : Data) (g : Finset (Fin D.M)) : ℝ :=
  (∑ i ∈ g, D.rho i / D.mu i) / (1 - ∑ i ∈ g, D.rho i)

end CoffmanMitrani


