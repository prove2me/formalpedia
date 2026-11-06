-- Prove2me | Definitions.Def_MemQueryFeas_SucceedsAdaptive
-- name    : MemQueryFeas_SucceedsAdaptive
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:35:44.742234+00:00
-- url     : https://prove2.me/theorems/e3175170-a048-4f6e-9e62-e026ddf08496
-- title:
--   Success with probability $2/3$ within $T$ queries
-- statement:
--   A randomized $M$-bit algorithm **solves feasibility problems of accuracy $\varepsilon$ with probability $2/3$ within $T$ queries** if for every feasibility instance $Q$ of accuracy $\varepsilon$ and every valid, measurable adaptive separation oracle for $Q$,
--   $$
--   \Pr\big(\exists t<T:\ x_t\in Q\big)\ \ge\ \tfrac23,
--   $$
--   the probability being over i.i.d. draws $\omega_0,\omega_1,\dots\sim\mu$.
--
--   **Formalization Note** The draws are the infinite product `Measure.infinitePi`; only the first $T$ matter. The probability is the measure of the event.
-- source:
--   Yu–Blanchard, Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems, preprint (Nov. 3, 2026), Theorem 1, p.2 (PDF p.3)

import Mathlib
import Definitions.Def_MemQueryFeas_RandMemAlg_run
import Definitions.Def_MemQueryFeas_IsFeasInstance
import Definitions.Def_MemQueryFeas_IsValidAdaptive
import Definitions.Def_MemQueryFeas_IsMeasurableAdaptive

open MeasureTheory
open scoped ENNReal

namespace MemQueryFeas

/-- **Solving feasibility problems with probability `2/3` within `T` queries.** Yu–Blanchard, *Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems*, preprint (Nov. 3, 2026), Theorem 1,
p.2 (PDF p.3): "any algorithm that solves feasibility problems up to accuracy `ϵ` with probability
`2/3` … Here, the considered feasibility oracles may be adaptive in the learner's queries."

`SucceedsAdaptive alg ε T`: for every feasibility instance `Q` of accuracy `ε` and every valid,
measurable adaptive separation oracle `O` for `Q`, with probability at least `2/3` over the i.i.d.
per-round randomness, one of the first `T` queries `x_0, …, x_{T-1}` lies in `Q`.

**Formalization Note.** The per-round draws are i.i.d. with law `alg.μ` (`Measure.infinitePi`); only
the first `T` draws matter. The probability of the event is the measure of the set, i.e. its outer
measure if it were not measurable. The oracle is deterministic given the history; randomized
oracles are mixtures of these. Only measurable oracles are required, which makes the hypothesis
weaker. -/
def SucceedsAdaptive {d M : ℕ} (alg : RandMemAlg d M) (ε : ℝ) (T : ℕ) : Prop :=
  ∀ (Q : Set (Vec d)) (O : List (Vec d) → Vec d → Option (Vec d)),
    IsFeasInstance ε Q → IsValidAdaptive Q O → IsMeasurableAdaptive O →
      (2 / 3 : ℝ≥0∞) ≤ Measure.infinitePi (fun _ : ℕ => alg.μ)
        {ω | ∃ t < T, alg.query (alg.run O ω t).1 (ω t) ∈ Q}

end MemQueryFeas


