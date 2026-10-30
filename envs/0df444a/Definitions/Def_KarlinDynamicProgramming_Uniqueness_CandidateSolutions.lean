-- Prove2me | Definitions.Def_KarlinDynamicProgramming_Uniqueness_CandidateSolutions
-- name    : KarlinDynamicProgramming_Uniqueness_CandidateSolutions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T14:54:43.304725+00:00
-- url     : https://prove2.me/theorems/2b49795c-b74d-43a7-89bd-3aac818cdf2b
-- title:
--   Attained Bellman solutions and vanishing signed terminal envelopes
-- statement:
--   BellmanSolution requires the value M at every state to be a greatest element of the range of L plus P times the next-state value: every action is bounded above and some action attains equality. The terminal value after N decisions is the signed value at the reached state times the product weight. VanishingTerminalEnvelope requires real least upper bounds of these terminal ranges at every horizon, tending to zero for each initial state. This extends the source terminal maximum to a possibly nonattained finite supremum. Admissible is exactly the conjunction of these two predicates. twoStepValue is the expanded two-decision objective. No optimality, sign, continuity or boundedness of M is built into these definitions.
-- source:
--   Karlin, The Structure of Dynamic Programing Models, Naval Research Logistics Quarterly 2(4) (1955), 285–294, doi:10.1002/nav.3800020408; Equation (2) and Uniqueness, PDF 6–7 / printed 290–291

import Definitions.Def_KarlinDynamicProgramming_Uniqueness_Returns
open Filter

namespace KarlinDynamicProgramming.Uniqueness

variable {Ω D : Type*} [TopologicalSpace Ω] [TopologicalSpace D]

/-- The objective for one decision, with continuation value M. -/
def bellmanAction (m : Model Ω D) (M : Ω → ℝ) (ω : Ω) (a : D) : ℝ :=
  m.L ω a + m.P a * M (m.T a ω)

/-- Equation (2) has an attained decision maximum at every state. -/
def BellmanSolution (m : Model Ω D) (M : Ω → ℝ) : Prop :=
  ∀ ω, IsGreatest (Set.range (bellmanAction m M ω)) (M ω)

/-- The signed terminal expression after N decisions. -/
def terminalValue (m : Model Ω D) (M : Ω → ℝ) (ω : Ω)
    (s : Strategy D) (N : ℕ) : ℝ :=
  weight m s N * M (trajectory m ω s N)

/-- Finite least upper bounds of signed terminal values tend to zero, at each ω.
No absolute values or uniformity over initial states are imposed. -/
def VanishingTerminalEnvelope (m : Model Ω D) (M : Ω → ℝ) : Prop :=
  ∀ ω, ∃ r : ℕ → ℝ,
    (∀ N, IsLUB (Set.range (fun s : Strategy D => terminalValue m M ω s N)) (r N)) ∧
    Tendsto r atTop (nhds 0)

/-- Exactly the candidate class for the selected conditional uniqueness claim. -/
def Admissible (m : Model Ω D) (M : Ω → ℝ) : Prop :=
  BellmanSolution m M ∧ VanishingTerminalEnvelope m M

/-- Expanded objective from the first unnumbered display on printed page 291. -/
def twoStepValue (m : Model Ω D) (M : Ω → ℝ) (ω : Ω) (a b : D) : ℝ :=
  m.L ω a + m.P a * m.L (m.T a ω) b +
    m.P a * m.P b * M (m.T b (m.T a ω))

end KarlinDynamicProgramming.Uniqueness


