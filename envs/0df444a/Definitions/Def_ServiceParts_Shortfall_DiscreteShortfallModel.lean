-- Prove2me | Definitions.Def_ServiceParts_Shortfall_DiscreteShortfallModel
-- name    : ServiceParts_Shortfall_DiscreteShortfallModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-30T23:18:08.992866+00:00
-- url     : https://prove2.me/theorems/3cd17df4-d28f-45fb-875e-14b05a38bf9b
-- title:
--   Discrete-demand shortfall chain and its transition probabilities p_ij (Section 8.1.2)
-- statement:
--   The discrete-demand case of Section 8.1.2. The capacity $c$ is a nonnegative integer and the demands $D_1, D_2, \dots$ are nonnegative integer valued, independent and identically distributed with generic demand $D$, with finite mean $E[D] < c$.
--
--   The shortfall chain on $\{0, 1, 2, \dots\}$ is $V_0 = 0$ and
--   $$V_n = \left[V_{n-1} + D_n - c\right]^+, \qquad n \ge 1,$$
--   and the transition probabilities of p. 185 are
--   $$p_{ij} = \begin{cases} P\{D \le c - i\}, & j = 0 \text{ and } i \le c,\\ P\{D = c + (j - i)\}, & j > 0,\ i \le c + j,\\ 0, & \text{otherwise.}\end{cases}$$
--
--   These are the objects of the Markov-chain computation of the shortfall distribution (Section 8.1.2).
--
--   **Formalization Note** The positive part is computed in the integers and converted back to a natural number. The subtractions $c - i$ and $c + j - i$ appear only under the guards $i \le c$ and $i \le c + j$, where they are exact.
-- source:
--   Muckstadt, Analysis and Algorithms for Service Parts Supply Chains, Springer 2005, DOI 10.1007/b138879, pp. 184-185, Section 8.1.1 (E[D] < c) and Section 8.1.2 (V_0 = 0, transition probabilities p_ij)

import Mathlib

open MeasureTheory ProbabilityTheory

namespace ServiceParts.Shortfall

/-- The discrete-demand shortfall model of Muckstadt (2005), Section 8.1.2, p. 185: the system of
Section 8.1 with integer capacity `c` and nonnegative integer demands `D_1, D_2, …` (the demand of
period `n` is `demand n` for `n ≥ 1`; `demand 0` is an unused independent copy), independent and
identically distributed, with finite mean `E[D] < c` (standing assumption, p. 184). -/
structure DiscreteShortfallModel (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] where
  /-- the per-period production capacity `c` -/
  capacity : ℕ
  /-- `demand n` is the demand `D_n` of period `n` (for `n ≥ 1`) -/
  demand : ℕ → Ω → ℕ
  demand_measurable : ∀ n, Measurable (demand n)
  /-- the demands of different periods are mutually independent -/
  demand_indep : iIndepFun demand P
  /-- the demands of all periods have the same law as `D_1` -/
  demand_identDistrib : ∀ n, IdentDistrib (demand n) (demand 1) P P
  /-- the expected per-period demand is finite -/
  demand_integrable : Integrable (fun ω => (demand 1 ω : ℝ)) P
  /-- standing assumption of Section 8.1.1: `E[D] < c` -/
  mean_lt_capacity : ∫ ω, (demand 1 ω : ℝ) ∂P < capacity

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- The shortfall chain `V_n` on `ℕ`: `V_0 = 0` and `V_n = [V_{n−1} + D_n − c]^+` (Eq. (8.1)); the
positive part is taken in `ℤ` and converted back to `ℕ`. -/
noncomputable def DiscreteShortfallModel.shortfall (M : DiscreteShortfallModel Ω P) :
    ℕ → Ω → ℕ
  | 0 => fun _ => 0
  | n + 1 => fun ω =>
      ((M.shortfall n ω : ℤ) + (M.demand (n + 1) ω : ℤ) - (M.capacity : ℤ)).toNat

/-- The transition probabilities of Section 8.1.2, p. 185:
`p_{ij} = P{D ≤ c − i}` if `j = 0` and `i ≤ c`; `p_{ij} = P{D = c + (j − i)}` if `j > 0` and
`i ≤ c + j`; `p_{ij} = 0` otherwise. `D` has the common law of the demands (that of `D_1`). The
natural-number subtractions only occur under the guards `i ≤ c`, `i ≤ c + j`, where they are
exact. -/
noncomputable def DiscreteShortfallModel.transProb (M : DiscreteShortfallModel Ω P)
    (i j : ℕ) : ℝ :=
  if j = 0 then
    (if i ≤ M.capacity then (P {ω | M.demand 1 ω ≤ M.capacity - i}).toReal else 0)
  else
    (if i ≤ M.capacity + j then (P {ω | M.demand 1 ω = M.capacity + j - i}).toReal else 0)

end ServiceParts.Shortfall


