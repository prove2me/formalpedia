-- Prove2me | Definitions.Def_PersuadeFly_prefSet
-- name    : PersuadeFly_prefSet
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:28:49.395603+00:00
-- url     : https://prove2.me/theorems/102ea9d6-98b1-42f0-968a-8c8e4c6c959a
-- title:
--   The region $\mathcal P_a$ where action $a$ is optimal
-- statement:
--   For an action $a$, the set of beliefs under which $a$ is optimal for the receiver:
--   $$
--   \mathcal P_a=\{\mu\in\Delta(\Omega):\ \mathbf E_\mu[u(\omega,a)]\ge\mathbf E_\mu[u(\omega,a')]\ \text{for all }a'\in A\}.
--   $$
-- source:
--   Zu, Iyer, Xu, Learning to Persuade on the Fly: Robustness Against Ignorance, arXiv:2102.10156v2, §4, p.24

import Mathlib
import Definitions.Def_PersuadeFly_Instance

namespace PersuadeFly

/-- **The region `P_a` where `a` is optimal.** Zu, Iyer, Xu, *Learning to Persuade on the Fly: Robustness Against Ignorance*, arXiv:2102.10156v2, §4, p.24:
`P_a = {μ ∈ Δ(Ω) : E_μ[u(ω, a)] ≥ E_μ[u(ω, a')] for all a' ∈ A}`. -/
def prefSet {Ω A : Type} [Fintype Ω] (I : Instance Ω A) (a : A) : Set (Ω → ℝ) :=
  {μ | μ ∈ stdSimplex ℝ Ω ∧ ∀ a' : A, ∑ ω, μ ω * I.u ω a' ≤ ∑ ω, μ ω * I.u ω a}

end PersuadeFly


