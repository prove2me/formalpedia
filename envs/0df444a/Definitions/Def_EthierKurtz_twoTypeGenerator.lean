-- Prove2me | Definitions.Def_EthierKurtz_twoTypeGenerator
-- name    : EthierKurtz_twoTypeGenerator
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T07:14:47.12452+00:00
-- url     : https://prove2.me/theorems/857b209a-5cd0-41ee-9a9c-3b046225ac9e
-- title:
--   Two-type replacement generator
-- statement:
--   The continuous-time two-type branching generator: each type dies at its own rate and is replaced according to its type-specific offspring law.
-- source:
--   Stewart N. Ethier and Thomas G. Kurtz, Markov Processes: Characterization and Convergence, Wiley, 1986 (held reprint 1986/2005). Chapter 9, Section 2, equation (2.1), printed p. 392 (PDF p. 401).

import Mathlib

set_option autoImplicit true

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped NNReal ENNReal Topology BigOperators ContDiff

namespace EthierKurtz

/-- The two-type replacement generator (2.1). Natural subtraction is harmless
at an empty population coordinate because its rate is zero. -/
noncomputable def twoTypeGenerator (rate : Fin 2 → ℝ)
    (ρ : Fin 2 → Measure (ℕ × ℕ)) (f : ℕ × ℕ → ℝ) (z : ℕ × ℕ) : ℝ :=
  rate 0 * z.1 * (∫ k, f (z.1 - 1 + k.1, z.2 + k.2) - f z ∂ρ 0) +
  rate 1 * z.2 * (∫ k, f (z.1 + k.1, z.2 - 1 + k.2) - f z ∂ρ 1)

end EthierKurtz


