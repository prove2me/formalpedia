-- Prove2me | Definitions.Def_BauerleRiederMDP_LPDuality_bellmanOpReal
-- name    : BauerleRiederMDP_LPDuality_bellmanOpReal
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:29:14.068987+00:00
-- url     : https://prove2.me/theorems/2429629a-e293-45d0-ae70-0c89f0dcd5c7
-- title:
--   Maximal reward operator $\mathcal T$ on real-valued functions
-- statement:
--   For a stationary Markov Decision Model $(E,A,D,Q,r,\beta)$ and a measurable function $v:E\to\mathbb R$, the **maximal reward operator** is
--   $$
--   \mathcal Tv(x):=\sup_{a\in D(x)}\Big(r(x,a)+\beta\int v(x')\,Q(dx'\mid x,a)\Big),\qquad x\in E,
--   $$
--   where $D(x)=\{a\in A:(x,a)\in D\}$ is the set of admissible actions in state $x$.
--
--   The grid operator $\mathcal T_G$ of the state space discretization agrees with $\mathcal T$ on the grid and interpolates its values elsewhere.
--
--   **Formalization Note** The supremum is a real supremum indexed by the elements of $D(x)$, so inadmissible actions never contribute (a supremum written as `⨆ a ∈ D(x)` over the reals would add the value $0$ of an empty supremum for every inadmissible action). $D(x)$ is nonempty because $D$ contains the graph of a measurable map. For $|v|\le c\,b$ with a bounding function $b$ the values are bounded above and this is the book's supremum; on unbounded inputs a real supremum returns a default value, and the mission only applies $\mathcal T$ to $b$-bounded functions.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), §7.1, p.199 (PDF 210), the operator T v(x) := sup_{a∈D(x)} {r(x,a) + β ∫ v(x′)Q(dx′|x,a)}; §7.3, Lemma 7.3.3, p.206

import Mathlib
import Definitions.Def_MDPFinance_LPDuality_Model

open MeasureTheory ProbabilityTheory MDPFinance.LPDuality

namespace BauerleRiederMDP.LPDuality

/-- The maximal reward operator on real-valued functions (Bäuerle & Rieder, *Markov Decision
Processes with Applications to Finance* (2011), §7.1, p.199, PDF 210, and Lemma 7.3.3, p.206):
`T v(x) := sup_{a ∈ D(x)} ( r(x, a) + β ∫ v(x') Q(dx'|x, a) )`.

**Formalization Note** The supremum is a real `⨆` indexed by the subtype `D(x)`, not by a
membership proof, so actions outside `D(x)` never contribute (a real `⨆ a ∈ D(x), …` would add the
value `0` of an empty supremum for every `a ∉ D(x)`). `D(x)` is nonempty because `D` contains the
graph of a measurable map. For `v` with `|v| ≤ c·b` for a bounding function `b` the set of values is
bounded above, so this is the book's supremum; on other inputs the real `⨆` may return a junk value,
and this mission only applies `T` to functions bounded by a multiple of a bounding function. -/
noncomputable def bellmanOpReal {E A : Type*} [MeasurableSpace E] [MeasurableSpace A]
    (M : MarkovDecisionModel E A) (v : E → ℝ) (x : E) : ℝ :=
  ⨆ a : M.Dx x, M.r (x, (a : A)) + M.β * ∫ x', v x' ∂(M.Q (x, (a : A)))

end BauerleRiederMDP.LPDuality


