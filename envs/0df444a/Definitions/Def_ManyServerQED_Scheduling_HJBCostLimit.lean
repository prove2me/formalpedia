-- Prove2me | Definitions.Def_ManyServerQED_Scheduling_HJBCostLimit
-- name    : ManyServerQED_Scheduling_HJBCostLimit
-- status  : Definition
-- author  : @Jie Luo
-- created : 2026-11-26T01:14:25.002082+00:00
-- url     : https://prove2.me/theorems/dd644f07-cacd-4508-9a5b-f59c48512e24
-- title:
--   Discounted HJB data for a queueing subsequential limit
-- statement:
--   A Brownian-driven limit state with jointly measurable, locally bounded drift, polynomial moment bounds, and continuous increasing accumulated cost and Hamiltonian gap. The gap identity writes the accumulated gap as the cost plus the discounted drift pairing with the gradient minus the Hamiltonian term.
-- source:
--   Atar, Mandelbaum and Reiman, Scheduling a multi class queue with many exponential servers, proof of Theorem 4. https://arxiv.org/abs/math/0407058

import Definitions.Def_ManyServerQED_Scheduling_Diffusion

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace ManyServerQED.Scheduling

/-- Data for applying a discounted HJB identity to a queueing limit.
The accumulated running cost and gap are continuous nonnegative increasing processes.
The gap law is expressed using the drift of the limiting state and the Hamiltonian. -/
structure HJBCostLimit {k : ℕ} (D : DiffusionData k)
    (L : (Fin k → ℝ) → (Fin k → ℝ) → ℝ) (γ : ℝ)
    (f : (Fin k → ℝ) → ℝ) (x : Fin k → ℝ) where
  Ω : Type
  [mΩ : MeasurableSpace Ω]
  P : Measure Ω
  isProb : IsProbabilityMeasure P
  F : Filtration ℝ≥0 mΩ
  W : ℝ≥0 → Ω → Fin k → ℝ
  W_bm : IsStdFBrownian P F W
  X : ℝ≥0 → Ω → Fin k → ℝ
  X_cont : ∀ ω, Continuous (fun t => X t ω)
  X_adapted : ∀ t, Measurable[F t] (X t)
  X_zero : ∀ᵐ ω ∂P, X 0 ω = x
  X_moment : ∀ p : ℕ, ∃ c : ℝ, 0 ≤ c ∧ ∃ j : ℕ, ∀ t : ℝ≥0,
    Integrable (fun ω => l1norm (X t ω)^p) P ∧
    (∫ ω, l1norm (X t ω)^p ∂P) ≤ c*(1+(t:ℝ)^j)
  b : ℝ≥0 → Ω → Fin k → ℝ
  b_meas : Measurable (fun z : Ω × ℝ≥0 => b z.2 z.1)
  b_bound : ∀ ω (T : ℝ≥0), ∃ a : ℝ, ∀ t ∈ Set.Icc 0 T, ‖b t ω‖ ≤ a
  state_eq : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, X t ω = x + (fun i => D.r i * W t ω i) +
    ∫ s in (0 : ℝ)..(t : ℝ), b s.toNNReal ω
  cost : ℝ≥0 → Ω → ℝ
  gap : ℝ≥0 → Ω → ℝ
  cost_cont : ∀ ω, Continuous (fun t => cost t ω)
  gap_cont : ∀ ω, Continuous (fun t => gap t ω)
  cost_integrable : ∀ t, Integrable (cost t) P
  gap_meas : ∀ t, Measurable (gap t)
  cost_increases : ∀ᵐ ω ∂P, Monotone (fun t => cost t ω)
  gap_increases : ∀ᵐ ω ∂P, Monotone (fun t => gap t ω)
  cost_zero : ∀ᵐ ω ∂P, cost 0 ω = 0
  gap_eq : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, gap t ω = cost t ω +
    ∫ s in (0 : ℝ)..(t : ℝ), Real.exp (-γ*s) *
      ((∑ i, b s.toNNReal ω i * grad f (X s.toNNReal ω) i) -
        hamiltonian D L (X s.toNNReal ω) (grad f (X s.toNNReal ω)))

attribute [instance] HJBCostLimit.mΩ

end ManyServerQED.Scheduling


