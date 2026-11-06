-- Prove2me | Definitions.Def_FirstOrderFG_Alg2_condExp
-- name    : FirstOrderFG_Alg2_condExp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:54:58.89694+00:00
-- url     : https://prove2.me/theorems/2bd82835-2411-461f-bbc1-60d864f028b8
-- title:
--   Expectation $\mathbb E_\tau$ over an instance of Algorithm 2 started at round $\tau$
-- statement:
--   For an instance started in a given state before round $\tau$, $\mathbb E_\tau[\Phi]$ is the expectation of a functional $\Phi$ of the instance's arms in rounds $\tau,\dots,T$, the arm of each round drawn from the instance's $\pi_t$, conditional on the history before $\tau$.
-- source:
--   Zhang–Zhang–Luo–Mineiro, Near-Optimal First-Order Regret for Bandits with Feedback Graphs, arXiv:2610.40861, Lemma B.1, p.22

import Mathlib
import Definitions.Def_FirstOrderFG_Alg2_runFrom
import Definitions.Def_FirstOrderFG_piDist
import Definitions.Def_FirstOrderFG_treeExp

namespace FirstOrderFG

/-- **`E_τ`, the expectation over an instance of Algorithm 2 started at round `τ`.** Zhang–Zhang–Luo–Mineiro, *Near-Optimal First-Order Regret for Bandits with Feedback Graphs*, arXiv:2610.40861,
Lemma B.1, p.22 ("Denote by `E_τ` the expectation conditional on the history before `τ`").

The instance starts in state `st₀` before global round `τ` and plays rounds `τ, …, T`, drawing
`I_t ∼ π_t`; `Φ` is evaluated on the instance's history (the list of arms played from round `τ`).

**Formalization Note.** The rounds after the interval of interest are drawn from the instance's
own `π_t`; functionals `Φ` that read only the rounds of the interval (`Alg2.sumOn`, `Alg2.maxOn`)
do not depend on that choice, so this is the conditional expectation given the history before
`τ`. -/
noncomputable def Alg2.condExp {K : ℕ} (E : Fin K → Fin K → Prop) [DecidableRel E] (T : ℕ) (ℓ : ℕ → Fin K → ℝ)
    (q₀ : (Fin K → ℝ) → ℝ → Fin K → ℝ) (τ : ℕ) (st₀ : Alg2.State K)
    (Φ : List (Fin K) → ℝ) : ℝ :=
  treeExp (fun hist => piDist E (Alg2.runFrom E T ℓ q₀ τ st₀ hist).x
      (Alg2.qOf E T q₀ (Alg2.runFrom E T ℓ q₀ τ st₀ hist)))
    (T + 1 - τ) [] Φ

end FirstOrderFG


