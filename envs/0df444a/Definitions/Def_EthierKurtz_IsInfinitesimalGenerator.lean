-- Prove2me | Definitions.Def_EthierKurtz_IsInfinitesimalGenerator
-- name    : EthierKurtz_IsInfinitesimalGenerator
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T05:41:37.919151+00:00
-- url     : https://prove2.me/theorems/a9e7b810-c19c-4db2-b1a2-58949382082e
-- title:
--   Full infinitesimal generator
-- statement:
--   The derivative graph of the semigroup at zero equals the full graph of the given linear operator on its domain.
-- source:
--   Ethier and Kurtz, Markov Processes: Characterization and Convergence, Wiley, 1986, Chapter 1, pp. 6, 8.

import Mathlib

open Filter
open scoped Topology

namespace EthierKurtz

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Chapter 1, p. 8, (1.10). Equality of the derivative graph and the graph
of the potentially unbounded operator `A : D →ₗ[ℝ] E`. The biconditional
requires the full generator domain, not merely an operator restriction. -/
def IsInfinitesimalGenerator (D : Submodule ℝ E) (A : D →ₗ[ℝ] E)
    (T : ℝ → E →L[ℝ] E) : Prop :=
  ∀ x y : E,
    Tendsto (fun t : ℝ => t⁻¹ • (T t x - x)) (𝓝[>] (0 : ℝ)) (𝓝 y) ↔
      ∃ hx : x ∈ D, A ⟨x, hx⟩ = y

end EthierKurtz


