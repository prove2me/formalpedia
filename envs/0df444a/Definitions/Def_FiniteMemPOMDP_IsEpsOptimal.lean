-- Prove2me | Definitions.Def_FiniteMemPOMDP_IsEpsOptimal
-- name    : FiniteMemPOMDP_IsEpsOptimal
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:33:03.315442+00:00
-- url     : https://prove2.me/theorems/01108b2a-7a48-47af-af18-d26e17a33e80
-- title:
--   $\varepsilon$-optimal strategy
-- statement:
--   Let $p_1\in\Delta(\mathcal K)$ and $\varepsilon>0$. A strategy $\sigma$ is **$\varepsilon$-optimal** in $\Gamma(p_1)$ if
--
--   $$\gamma^{p_1}_\infty(\sigma)\ge v_\infty(p_1)-\varepsilon .$$
-- source:
--   Chatterjee, Saona & Ziliotto, Finite-memory strategies in POMDPs with Long-run Average Objectives, arXiv:1904.13360v2, Definition 2.4, p.3

import Mathlib
import Definitions.Def_FiniteMemPOMDP_vInf

namespace FiniteMemPOMDP

variable {K A S : Type} [Fintype K] [Fintype A] [Fintype S] [Nonempty A] [Nonempty S]

/-- **ε-optimal strategy.**
Chatterjee, Saona & Ziliotto, arXiv:1904.13360v2, Definition 2.4, p.3: "Let p1 ∈ ∆(K) and ε > 0.
A strategy σ ∈ Σ is ε-optimal in Γ(p1) if γ^{p1}_∞(σ) ≥ v∞(p1) − ε."

`IsEpsOptimal Γ p ε σ` says `gammaInf Γ p σ ≥ vInf Γ p − ε`. The positivity `ε > 0` is a
hypothesis of every statement that uses this predicate. -/
def IsEpsOptimal (Γ : POMDP K A S) (p : stdSimplex ℝ K) (ε : ℝ) (σ : List (A × S) → A) : Prop :=
  vInf Γ p - ε ≤ gammaInf Γ p σ

end FiniteMemPOMDP


