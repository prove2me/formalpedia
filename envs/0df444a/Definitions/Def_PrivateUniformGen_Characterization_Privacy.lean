-- Prove2me | Definitions.Def_PrivateUniformGen_Characterization_Privacy
-- name    : PrivateUniformGen_Characterization_Privacy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T08:55:08.952245+00:00
-- url     : https://prove2.me/theorems/ab0926f0-e764-44d7-a0f4-eaf4e80cc80e
-- title:
--   Replacement neighbors and approximate differential privacy
-- statement:
--   A randomized mechanism on ordered datasets of length $n$ assigns a probability law to every dataset. Two datasets are neighbors when exactly one coordinate changes. The relation “near” additionally admits equal datasets. For real parameters $\varepsilon,\delta$, approximate differential privacy requires, on every measurable output event $O$ and every ordered pair of neighbors,
--
--   $$\Pr[A(S)\in O]\le e^{\varepsilon}\Pr[A(S')\in O]+\delta.$$
--
--   This definition is independent of the language model and permits arbitrary measurable output spaces. Probability laws are bundled, and no realizability, distinctness or computability restriction is imposed on inputs or mechanisms. No sign condition is built in: each result states its own ranges for $\varepsilon,\delta$, as the source does (a negative $\delta$ is infeasible anyway, by the event $O=\emptyset$, whenever neighbors exist).
-- source:
--   Di Wang, Peng Ye, STOC 2027 submission #178 (October 2026), Definition 3.4 and surrounding paragraph, p. 9. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/178.pdf

import Mathlib

open MeasureTheory

namespace PrivateUniformGen.Characterization

/-- Definition 3.4, p. 9: ordered replacement neighbors. -/
def Neighbors {X : Type*} {n : ℕ} (S S' : Fin n → X) : Prop :=
  ∃ i, S i ≠ S' i ∧ ∀ j, j ≠ i → S j = S' j

/-- Inputs differing in at most one position, including equal inputs. -/
def Near {X : Type*} {n : ℕ} (S S' : Fin n → X) : Prop :=
  S = S' ∨ Neighbors S S'

/-- A randomized algorithm, without a computability requirement. -/
abbrev Mechanism (X Y : Type*) [MeasurableSpace Y] (n : ℕ) :=
  (Fin n → X) → ProbabilityMeasure Y

/-- Definition 3.4, p. 9: approximate DP on every input, exactly as stated
    (no sign condition on ε, δ; the source states its parameter ranges per result). -/
def IsDP {X Y : Type*} [MeasurableSpace Y] {n : ℕ}
    (A : Mechanism X Y n) (ε δ : ℝ) : Prop :=
  ∀ S S', Neighbors S S' → ∀ O : Set Y, MeasurableSet O →
    (A S : Measure Y).real O ≤ Real.exp ε * (A S' : Measure Y).real O + δ

end PrivateUniformGen.Characterization


