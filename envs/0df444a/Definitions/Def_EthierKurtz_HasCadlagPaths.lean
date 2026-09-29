-- Prove2me | Definitions.Def_EthierKurtz_HasCadlagPaths
-- name    : EthierKurtz_HasCadlagPaths
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T05:55:19.208366+00:00
-- url     : https://prove2.me/theorems/34f7f644-3264-4862-9e8b-dd653aaddbc3
-- title:
--   Càdlàg path condition
-- statement:
--   Every sample path is right-continuous and has a finite left limit at each positive time.
-- source:
--   Stewart N. Ethier and Thomas G. Kurtz, Markov Processes: Characterization and Convergence, Wiley, 1986. Chapter 3, Section 5, printed p. 116 (PDF p. 125).

import Mathlib

set_option autoImplicit true

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped ENNReal NNReal Topology BigOperators

namespace EthierKurtz

/-- Unbundled version of the Chapter 6 `CadlagPath` path condition. -/
def HasCadlagPaths {Ω E : Type*} [TopologicalSpace E]
    (X : ℝ≥0 → Ω → E) : Prop :=
  ∀ ω, (∀ t, ContinuousWithinAt (fun s => X s ω) (Set.Ici t) t) ∧
    ∀ t : ℝ≥0, 0 < t → ∃ a : E,
      Tendsto (fun s => X s ω) (𝓝[<] t) (𝓝 a)

end EthierKurtz


