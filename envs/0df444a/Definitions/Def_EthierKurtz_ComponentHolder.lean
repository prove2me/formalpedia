-- Prove2me | Definitions.Def_EthierKurtz_ComponentHolder
-- name    : EthierKurtz_ComponentHolder
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T06:08:52.361041+00:00
-- url     : https://prove2.me/theorems/4d3e71c0-472d-4561-9e26-5c3455b61a98
-- title:
--   Componentwise local Hölder oscillation
-- statement:
--   A continuous scalar function whose oscillation on each connected component of every sufficiently small region-ball intersection is bounded by a uniform Hölder power.
-- source:
--   Stewart N. Ethier and Thomas G. Kurtz, Markov Processes: Characterization and Convergence, Wiley, 1986. Chapter 8, Section 1, equation (1.13), printed p. 368 (PDF p. 377).

import Mathlib

open Filter
open scoped Topology BoundedContinuousFunction

namespace EthierKurtz

/-- Finite oscillation seminorm (1.13), expressed by pairwise differences
inside each component, never across separate components. -/
def ComponentHolder {d : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin d)))
    (μ : ℝ) (f : EuclideanSpace ℝ (Fin d) → ℝ) : Prop :=
  ContinuousOn f Ω ∧ ∃ ρ₀ M : ℝ, 0 < ρ₀ ∧ 0 ≤ M ∧
    ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∀ x z : EuclideanSpace ℝ (Fin d),
      z ∈ Ω ∩ Metric.ball x ρ →
      ∀ y ∈ connectedComponentIn (Ω ∩ Metric.ball x ρ) z,
      ∀ w ∈ connectedComponentIn (Ω ∩ Metric.ball x ρ) z,
        |f y - f w| ≤ M * ρ ^ μ

end EthierKurtz


