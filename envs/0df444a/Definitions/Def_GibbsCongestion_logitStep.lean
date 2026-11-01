-- Prove2me | Definitions.Def_GibbsCongestion_logitStep
-- name    : GibbsCongestion_logitStep
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T12:02:20.077999+00:00
-- url     : https://prove2.me/theorems/3b175fd1-ec5a-4c41-b3c6-48e59805bb7a
-- title:
--   Transition matrix of the logit dynamics
-- statement:
--   The **logit dynamics** at temperature $T$, from the current profile $s$:
--
--   1. select a player $i\in N$ uniformly at random;
--   2. move to $(r,s_{-i})$, $r\in\mathcal P$, with probability $e^{-T\Phi(r,s_{-i})}/Z'_i$, where $Z'_i=\sum_{r'\in\mathcal P}e^{-T\Phi(r',s_{-i})}$.
--
--   As a matrix,
--   $$\mathrm{Logit}(s,s')=\frac1n\sum_{i\in N}\sum_{r\in\mathcal P}[\,s'=(r,s_{-i})\,]\,\frac{e^{-T\Phi(s')}}{Z'_i(s)}.$$
--   The chain is reversible with respect to the Gibbs distribution.
--
--   **Formalization Note** The normalizer is the local $Z'_i(s)$, not the global partition function; $(r,s_{-i})$ is the profile $s$ with player $i$'s strategy replaced by $r$.
-- source:
--   Kleer, Sampling from the Gibbs Distribution in Congestion Games, arXiv:2105.12982v1, §2.1, p.8

import Mathlib
import Definitions.Def_GibbsCongestion_potential

namespace GibbsCongestion

/-- The transition matrix of the **logit dynamics** (Kleer, Sampling from the Gibbs Distribution in Congestion Games, arXiv:2105.12982v1, §2.1, p.8): select a player `i`
uniformly at random, then move to `(r, s₋ᵢ)` with probability `e^{-TΦ(r,s₋ᵢ)}/Z'ᵢ`, where
`Z'ᵢ = ∑_{r ∈ P} e^{-TΦ(r,s₋ᵢ)}`.

**Formalization Note** As a matrix,
`logit(s, s') = (1/n) ∑_i ∑_{r ∈ P} [s' = (r, s₋ᵢ)] · e^{-TΦ(s')}/Z'ᵢ(s)`. The normalizer is the
local `Z'ᵢ(s)`, not the global partition function. -/
noncomputable def logitStep {E : Type*} [Fintype E] [DecidableEq E] (P : Finset (Finset E))
    (n : ℕ) (c : E → ℕ → ℝ) (T : ℝ) : Matrix (Fin n → P) (Fin n → P) ℝ :=
  fun s s' => (1 / (n : ℝ)) * ∑ i : Fin n, ∑ r : P,
    if s' = Function.update s i r then
      Real.exp (-T * potential c s') /
        ∑ r' : P, Real.exp (-T * potential c (Function.update s i r'))
    else 0

end GibbsCongestion


