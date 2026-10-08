-- Prove2me | Definitions.Def_YoungConventions_RiskDominance_IsStochasticallyStable
-- name    : YoungConventions_RiskDominance_IsStochasticallyStable
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T18:01:34.039862+00:00
-- url     : https://prove2.me/theorems/5c7fa802-147a-4488-ac33-4edecec97a02
-- title:
--   Stochastically stable state
-- statement:
--   A state $h\in H$ is **stochastically stable** relative to the process $P^\varepsilon$ if
--   $$\lim_{\varepsilon\to0}\mu^\varepsilon_h>0,$$
--   where $\mu^\varepsilon$ is the stationary distribution of $P^\varepsilon$. Precisely: there is $L>0$ such that, for every family $(\mu^\varepsilon)$ with $\mu^\varepsilon$ a stationary distribution of $P^\varepsilon$ for every admissible $\varepsilon$ ($0<\varepsilon$, $\varepsilon\lambda_i\le1$ for all $i$), $\mu^\varepsilon_h\to L$ as $\varepsilon\to0^+$.
--
--   The stochastically stable states are those observed with positive probability in the long run when the noise is small but nonvanishing.
--
--   **Formalization Note** The existence of the limit is part of the claim. For admissible $\varepsilon$ the stationary distribution exists and is unique (milestone on irreducibility and aperiodicity), so the quantifier over families is not vacuous. The limit is one-sided ($\varepsilon\to0^+$). The definition uses only the process $P^\varepsilon$; it does not mention resistances.
-- source:
--   Young (1993), The Evolution of Conventions, Econometrica 61:57–84, §6, p. 68, displayed definition (Stochastic Stability)

import Mathlib
import Definitions.Def_YoungConventions_AdaptivePlay_History
import Definitions.Def_YoungConventions_RiskDominance_perturbed
import Definitions.Def_YoungConventions_RiskDominance_IsStationaryDistribution

namespace YoungConventions.RiskDominance

/-- **Stochastic stability.** Young (1993), The Evolution of Conventions, Econometrica 61:57–84, §6, p. 68 (PDF p. 13), displayed definition: "A state `h ∈ H`
is stochastically stable relative to the process `P^ε` if `lim_{ε→0} μ^ε_h > 0`."

`h` is stochastically stable iff there is `L > 0` such that, for every family `(μ^ε)` with `μ^ε` a
stationary distribution of `P^ε` for every admissible `ε` (that is, `0 < ε` and `ελᵢ ≤ 1` for all
`i`), `μ^ε_h → L` as `ε → 0⁺`.

**Formalization Note.** The existence of the limit is part of the claim. For admissible `ε`, `P^ε` has
exactly one stationary distribution (milestone `perturbed_irreducible_aperiodic`, p. 68), so such a
family exists and is unique there, and the universal quantifier over families is not vacuous.
`ε → 0` is the one-sided limit `𝓝[>] 0`. The definition is about the actual process `P^ε`: it does
not mention resistances or stochastic potential. -/
def IsStochasticallyStable {ι : Type*} [Fintype ι] [DecidableEq ι] {S : ι → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)] {m : ℕ} [NeZero m]
    (p q : (i : ι) → YoungConventions.AdaptivePlay.History S m → S i → ℝ) (lam : ι → ℝ) (h : YoungConventions.AdaptivePlay.History S m) : Prop :=
  ∃ L : ℝ, 0 < L ∧ ∀ μ : ℝ → YoungConventions.AdaptivePlay.History S m → ℝ,
    (∀ ε : ℝ, 0 < ε → (∀ i, ε * lam i ≤ 1) →
      IsStationaryDistribution (μ ε) (perturbed p q lam ε)) →
    Filter.Tendsto (fun ε => μ ε h) (nhdsWithin 0 (Set.Ioi 0)) (nhds L)

end YoungConventions.RiskDominance


