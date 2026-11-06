-- Prove2me | Definitions.Def_BorelRobustMDP_markovValue
-- name    : BorelRobustMDP_markovValue
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:15:48.712577+00:00
-- url     : https://prove2.me/theorems/13c93f88-560c-4d55-890a-5ff0363827fb
-- title:
--   The Markov values $J_{n\pi\gamma}$, $J_{n\pi}$ and $J_n$
-- statement:
--   For Markov policies $\pi\in\Pi^M$, $\gamma\in\Gamma^M$, the value (2.5) is a function $J_{n\pi\gamma}(x)$ of the state, with $J_{N\pi\gamma}=c_N$. Further
--
--   $$J_{n\pi}(x)=\sup_{\gamma\in\Gamma^M}J_{n\pi\gamma}(x),\qquad J_n(x)=\inf_{\pi\in\Pi^M}\sup_{\gamma\in\Gamma^M}J_{n\pi\gamma}(x).$$
--
--   **Formalization Note.** $J_{n\pi\gamma}(x)$ is the integral of the total cost against the law of motion started from $x$ at calendar time $n$, not the recursion of p.10.
-- source:
--   Bäuerle & Glauner, arXiv:2007.13103v1, p.10

import Mathlib
import Definitions.Def_MDPFinance_Bellman_History
import Definitions.Def_BorelRobustMDP_MarkovPolicy
import Definitions.Def_BorelRobustMDP_MarkovNature
import Definitions.Def_BorelRobustMDP_pathLaw

open MeasureTheory
open MDPFinance.Bellman (Hist histState)

namespace BorelRobustMDP

universe u v

variable {E A : Type u} {Z : Type v} [MeasurableSpace E] [MeasurableSpace A] [MeasurableSpace Z]
  {N : ℕ}

/-- The law of the process under Markov policies `(d, γ)` started in state `x` at calendar time `n`,
for `j` transitions. -/
noncomputable def markovLaw (R : RobustModel E A Z N) (d : MarkovPolicy R.toDecisionModel)
    (γ : MarkovNature R) (n : ℕ) (x : E) (j : ℕ) : Measure (Hist E A (0 + j)) :=
  pathLaw R 0 n (fun j h => d.act (n + j) (histState (0 + j) h))
    (fun j w => γ.act (n + j) (histState (0 + j) w.1, w.2)) x j

/-- The value `J_{nπγ}(x)` of Markov policies (Bäuerle & Glauner, arXiv:2007.13103v1, p.10): the value
(2.5), a function of the state alone, with `J_{Nπγ} = c_N`.

**Formalization Note.** It is the expectation under the law of motion started from `x` at time `n`,
not the recursion, which the paper derives from Proposition 3.5. -/
noncomputable def markovValue (R : RobustModel E A Z N) (d : MarkovPolicy R.toDecisionModel)
    (γ : MarkovNature R) (n : ℕ) (x : E) : ℝ :=
  ∫ h', totalCost R 0 n (N - n) h' ∂(markovLaw R d γ n x (N - n))

/-- The robust value `J_{nπ}(x) = sup_{γ∈Γ^M} J_{nπγ}(x)` of a Markov policy (Bäuerle & Glauner,
arXiv:2007.13103v1, p.10). -/
noncomputable def markovRobustValue (R : RobustModel E A Z N)
    (d : MarkovPolicy R.toDecisionModel) (n : ℕ) (x : E) : ℝ :=
  ⨆ γ : MarkovNature R, markovValue R d γ n x

/-- The Markovian value function `J_n(x) = inf_{π∈Π^M} sup_{γ∈Γ^M} J_{nπγ}(x)` (Bäuerle & Glauner,
arXiv:2007.13103v1, p.10). -/
noncomputable def markovOptimalValue (R : RobustModel E A Z N) (n : ℕ) (x : E) : ℝ :=
  ⨅ d : MarkovPolicy R.toDecisionModel, markovRobustValue R d n x

end BorelRobustMDP


