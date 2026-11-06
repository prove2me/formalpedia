-- Prove2me | Definitions.Def_YuStrategic_Optimality_StrategicSets
-- name    : YuStrategic_Optimality_StrategicSets
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:24:48.716864+00:00
-- url     : https://prove2.me/theorems/317b0f9e-3cfb-4638-b663-e3feae82b7a5
-- title:
--   Sets of strategic measures $\mathcal S_\star,\mathcal S'_\star$ and their initial-state versions $\tilde{\mathcal S}_\star,\tilde{\mathcal S}'_\star$
-- statement:
--   The set of all strategic measures is
--   $$\mathcal S=\{p\in\mathcal P(\Omega)\mid p=\rho_{p_0}[\pi],\ \pi\in\Pi,\ p_0\in\mathcal P(\mathbb X)\},$$
--   and $\mathcal S'\subseteq\mathcal S$ is the subset induced by nonrandomized policies. With $\Pi_m$ (resp. $\Pi_s$) in place of $\Pi$ one obtains $\mathcal S_m$ (resp. $\mathcal S_s$) and their nonrandomized subsets $\mathcal S'_m$, $\mathcal S'_s$. For $\mathcal S_\star\in\{\mathcal S,\mathcal S_m,\mathcal S_s\}$ define
--   $$\tilde{\mathcal S}_\star=\{(x,p)\in\mathbb X\times\mathcal P(\Omega)\mid p\in\mathcal S_\star,\ p_0(p)=\delta_x\},\qquad \tilde{\mathcal S}'_\star=\{(x,p)\mid p\in\mathcal S'_\star,\ p_0(p)=\delta_x\},$$
--   where $p_0(p)$ is the marginal distribution of $x_0$ under $p$. The $x$-section $\tilde{\mathcal S}_\star(x)=\{p\in\mathcal S_\star\mid p_0(p)=\delta_x\}$ is the feasible set of strategic measures from the initial state $x$.
--
--   These sets are the feasible regions of the partial minimization problems in Theorem 3.3.
-- source:
--   Yu, arXiv:2206.06492v3, §3, p. 7 (definitions of S, S′, S_m, S′_m, S_s, S′_s, S̃⋆, S̃′⋆)

import Mathlib
import Definitions.Def_YuStrategic_Optimality_StrategicMeasure

namespace YuStrategic.Optimality

open MeasureTheory ProbabilityTheory

variable {X A : Type} [TopologicalSpace X] [MeasurableSpace X]
  [TopologicalSpace A] [MeasurableSpace A]

/-- The set `S⋆ ⊆ P(Ω)` of strategic measures (Yu, arXiv:2206.06492v3, §3, p. 7):
`S = {p ∈ P(Ω) | p = ρ_{p₀}[π], π ∈ Π, p₀ ∈ P(X)}` for `κ = all`, and `S_m` (resp. `S_s`), the
strategic measures induced by Markov (resp. stationary) policies, for `κ = markov`
(resp. `stationary`). -/
def stratSet (M : Model X A) (κ : PolicyClass) : Set (ProbabilityMeasure (Path X A)) :=
  {P | ∃ (π : Policy M) (p₀ : ProbabilityMeasure X), κ.mem π ∧ IsStrategicMeasure M π p₀ P}

/-- The subset `S′⋆ ⊆ S⋆` of strategic measures induced by the nonrandomized policies of the
class (§3, p. 7): `S′`, `S′_m`, `S′_s`. -/
def stratSet' (M : Model X A) (κ : PolicyClass) : Set (ProbabilityMeasure (Path X A)) :=
  {P | ∃ (π : Policy M) (p₀ : ProbabilityMeasure X),
    κ.mem π ∧ π.IsNonrandomized ∧ IsStrategicMeasure M π p₀ P}

/-- `S̃⋆ := {(x, p) ∈ X × P(Ω) | p ∈ S⋆, p₀(p) = δₓ}` (§3, p. 7), where `p₀(p)` is the marginal
distribution of `x₀` under `p`. Its `x`-section is `S̃⋆(x) = {p ∈ S⋆ | p₀(p) = δₓ}`. -/
def stratSetTilde (M : Model X A) (κ : PolicyClass) :
    Set (X × ProbabilityMeasure (Path X A)) :=
  {z | z.2 ∈ stratSet M κ ∧ (z.2 : Measure (Path X A)).map (stateAt 0) = Measure.dirac z.1}

/-- `S̃′⋆ := {(x, p) ∈ X × P(Ω) | p ∈ S′⋆, p₀(p) = δₓ}` (§3, p. 7). -/
def stratSetTilde' (M : Model X A) (κ : PolicyClass) :
    Set (X × ProbabilityMeasure (Path X A)) :=
  {z | z.2 ∈ stratSet' M κ ∧ (z.2 : Measure (Path X A)).map (stateAt 0) = Measure.dirac z.1}

end YuStrategic.Optimality


