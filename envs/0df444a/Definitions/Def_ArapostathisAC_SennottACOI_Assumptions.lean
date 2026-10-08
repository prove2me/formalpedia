-- Prove2me | Definitions.Def_ArapostathisAC_SennottACOI_Assumptions
-- name    : ArapostathisAC_SennottACOI_Assumptions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T15:24:22.966232+00:00
-- url     : https://prove2.me/theorems/9f3b1577-e64c-4d46-bd52-49c22c451e17
-- title:
--   Sennott's Assumptions 5.14–5.16 on the discounted value functions
-- statement:
--   Let $J^*_\beta(i)$ be the optimal $\beta$-discounted cost from state $i$ in the countable-state controlled Markov process of §5 and $h_\beta(i)=J^*_\beta(i)-J^*_\beta(0)$ the differential discounted value function. Sennott's conditions (Arapostathis et al. 1993, p. 307) are:
--
--   1. **Assumption 5.14.** For every $i\in S$ and every $\beta\in(0,1)$, $J^*_\beta(i)<\infty$.
--   2. **Assumption 5.15.** There is a nonnegative integer $L$ such that $h_\beta(i)\ge -L$ for every $i\in S$ and every $\beta\in(0,1)$.
--   3. **Assumption 5.16.** There is a function $M:S\to\mathbb R_+$ such that $h_\beta(i)\le M(i)$ for all $i\in S$ and all $\beta\in(0,1)$, and for every $i\in S$ there is an admissible action $a(i)\in U(i)$ with
--   $$\sum_{j}P(j\mid i,a(i))\,M(j)<\infty.$$
--
--   Together they say that the differential discounted values are bounded below uniformly and bounded above pointwise by a function that is integrable in one step under some action. They replace the uniform boundedness of $h_\beta$ used in the vanishing discount argument for bounded costs.
--
--   **Formalization Note** The paper writes Assumption 5.15 without quantifiers on $i$ and $\beta$; they are universal, as in Assumption 5.16. The function $M$ is named `Mf` in Lean (`M` is the process). "$M:S\to\mathbb R_+$" is a finite nonnegative real function, and for a nonnegative series "$\sum_j\cdots<\infty$" is summability. `hRel` is a genuine difference only under Assumption 5.14, which every theorem of this mission assumes together with 5.15 and 5.16.
-- source:
--   Arapostathis, Borkar, Fernández-Gaucherand, Ghosh, Marcus, Discrete-time controlled Markov processes with average cost criterion: a survey, SIAM J. Control Optim. 31(2) (1993), p. 307, Assumptions 5.14, 5.15, 5.16

import Mathlib
import Definitions.Def_ArapostathisAC_SennottACOI_CMP

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace ArapostathisAC.SennottACOI

variable {A : Type*} [MetricSpace A] [MeasurableSpace A] [BorelSpace A]

/-- Assumption 5.14 (p. 307): for every state `i` and every discount factor `β ∈ (0, 1)`,
the discounted value `J*_β(i)` is finite. -/
def Assumption5_14 (M : ArapostathisAC.VanishingDiscount.CMP A) : Prop :=
  ∀ β ∈ Set.Ioo (0 : ℝ) 1, ∀ i, ArapostathisAC.VanishingDiscount.discValue M β i ≠ ⊤

/-- Assumption 5.15 (p. 307): there is a nonnegative integer `L` with
`h_β(i) = J*_β(i) − J*_β(0) ≥ −L` for every state `i` and every `β ∈ (0, 1)`.
(`hRel` is the paper's `h_β` only under Assumption 5.14, which every statement using this
assumption also imposes.) -/
def Assumption5_15 (M : ArapostathisAC.VanishingDiscount.CMP A) : Prop :=
  ∃ L : ℕ, ∀ β ∈ Set.Ioo (0 : ℝ) 1, ∀ i, -(L : ℝ) ≤ ArapostathisAC.VanishingDiscount.hRel M β i

/-- Assumption 5.16 (p. 307): there is a function `Mf : S → ℝ₊` with `h_β(i) ≤ Mf(i)` for all
states `i` and all `β ∈ (0, 1)`, and for every state `i` some admissible action `a(i) ∈ U(i)`
with `Σ_j P(j | i, a(i)) Mf(j) < ∞`. -/
def Assumption5_16 (M : ArapostathisAC.VanishingDiscount.CMP A) : Prop :=
  ∃ Mf : ℕ → ℝ, (∀ i, 0 ≤ Mf i) ∧
    (∀ β ∈ Set.Ioo (0 : ℝ) 1, ∀ i, ArapostathisAC.VanishingDiscount.hRel M β i ≤ Mf i) ∧
    ∀ i, ∃ a ∈ M.U i, Summable (fun j => ArapostathisAC.VanishingDiscount.prob M i a j * Mf j)

end ArapostathisAC.SennottACOI


