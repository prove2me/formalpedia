-- Prove2me | Definitions.Def_EthierKurtz_twoTypeMode
-- name    : EthierKurtz_twoTypeMode
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T07:15:53.20198+00:00
-- url     : https://prove2.me/theorems/74b84d6d-d300-4977-875e-7d132ee31e38
-- title:
--   Scaled eigenvector population mode
-- statement:
--   The eigenvector-weighted two-type population observed on the accelerated time scale and divided by the positive population-scaling index.
-- source:
--   Stewart N. Ethier and Thomas G. Kurtz, Markov Processes: Characterization and Convergence, Wiley, 1986 (held reprint 1986/2005). Chapter 9, Section 2, equations (2.4)–(2.5), printed p. 393 (PDF p. 402).

import Mathlib

set_option autoImplicit true

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped NNReal ENNReal Topology BigOperators ContDiff

namespace EthierKurtz

/-- Eigenvector-weighted population at accelerated time, (2.4) and (2.5).
The positive index in the source is n+1 here. -/
noncomputable def twoTypeMode {Ω : Type*} (v : Fin 2 → ℝ) (n : ℕ)
    (Z : ℝ≥0 → Ω → ℕ × ℕ) (t : ℝ≥0) (w : Ω) : ℝ :=
  (v 0 * (Z ((n + 1 : ℕ) * t) w).1 +
    v 1 * (Z ((n + 1 : ℕ) * t) w).2) / (n + 1 : ℕ)

end EthierKurtz


