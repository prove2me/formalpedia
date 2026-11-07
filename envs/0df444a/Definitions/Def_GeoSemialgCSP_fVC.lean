-- Prove2me | Definitions.Def_GeoSemialgCSP_fVC
-- name    : GeoSemialgCSP_fVC
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:49:17.194091+00:00
-- url     : https://prove2.me/theorems/b29a84fc-499e-4a7f-be6c-9d4da74d42f9
-- title:
--   Fiber VC-dimension
-- statement:
--   The **fiber VC-dimension** $\mathrm{fVC}(\Delta)$ of a relation $\Delta\subseteq[q]^k$ is the maximum over the $k$ positions $j$ of the VC-dimension of the family of fibers of $\Delta$ in position $j$.
--
--   For example, $\Delta=[q]^k$ has fiber VC-dimension $0$.
-- source:
--   Arvanitakis, Chatziafratis, Makarychev, Hardness of Approximation for Semialgebraic CSPs, manuscript (STOC 2027 submission, held version sha256 ee702c42…), §3, p.8 (PDF p.9)

import Mathlib
import Definitions.Def_GeoSemialgCSP_fiber
import Definitions.Def_GeoSemialgCSP_vcSets

namespace GeoSemialgCSP

/-- **Fiber VC-dimension.** Arvanitakis, Chatziafratis, Makarychev, *Hardness of Approximation for Semialgebraic CSPs*,
manuscript (STOC 2027 submission, held version sha256 ee702c42…), §3, printed p.8 (PDF p.9): `fVC(Δ)` is the maximum over
the `k` positions of the VC-dimension of the fiber family in that position. -/
noncomputable def fVC {k q : ℕ} (Δ : Set (Fin k → Fin q)) : ℕ∞ :=
  ⨆ j : Fin k, vcSets (Set.range (fiber Δ j))

end GeoSemialgCSP


