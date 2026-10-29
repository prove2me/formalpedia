-- Prove2me | Definitions.Def_EntropyMFG_Enhanced_Equilibrium
-- name    : EntropyMFG_Enhanced_Equilibrium
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T02:24:29.101036+00:00
-- url     : https://prove2.me/theorems/6ace7b77-17ef-45a6-a28e-7a2b25f2ec5d
-- title:
--   Definition 1: Nash equilibrium and population consistency
-- statement:
--   An equilibrium consists of population state and action flows, a measurable density-valued feedback, its controlled state, and a finite attained payoff. The policy obtained by evaluating the feedback at that state satisfies every admissibility clause for the original game. Its payoff is at least the payoff of every admissible deviation. At every time the population state law is the controlled state's law, and the population action density agrees with the feedback at every real state and action. The initial population law is $\nu$. The actual extended-real supremum equals the attained payoff. No uniqueness of equilibrium is asserted.
-- source:
--   Guo, Xu, Zariphopoulou, Entropy Regularization for Mean Field Games with Learning, arXiv:2010.00145v2, https://arxiv.org/abs/2010.00145v2, Definition 1, p. 6, with §2 p. 5 admissibility and §3.2 pp. 9–10

import Definitions.Def_EntropyMFG_Enhanced_Game

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
noncomputable section

namespace EntropyMFG.Enhanced

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- Definition 1: admissibility, best response against every admissible deviation,
and state/action consistency. The game value is attained. -/
def IsEquilibrium (p : Parameters) (P : Measure Ω) (F : Filtration ℝ mΩ)
    (W : ℝ → Ω → ℝ) (t : ℝ) (ξ : Ω → ℝ) (ν : Measure ℝ)
    (μ : ℝ → Measure ℝ) (α f : ℝ → ℝ → ℝ → ℝ)
    (X : ℝ → Ω → ℝ) (v : ℝ) : Prop :=
  Population t p.T ν μ α ∧ Feedback t p.T f ∧
  Admissible p P F W t ξ μ α (fun s ω => f s (X s ω)) X v ∧
  (∀ π Y w, Admissible p P F W t ξ μ α π Y w → w ≤ v) ∧
  (∀ s ∈ Icc t p.T, ∀ x u, α s x u = f s x u) ∧
  (∀ s ∈ Icc t p.T, μ s = Measure.map (X s) P) ∧
  gameValue p P F W t ξ μ α = (v : EReal)

end EntropyMFG.Enhanced


