-- Prove2me | Definitions.Def_MaxWeightInstab_IsInitial
-- name    : MaxWeightInstab_IsInitial
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:14:34.696902+00:00
-- url     : https://prove2.me/theorems/aa8d2663-8f6d-4293-a11e-8559db07a407
-- title:
--   Initial set $\mathcal I_M$ of display (13)
-- statement:
--   A queue-length vector $Q$ lies in $\mathcal I_M$ (for given $\varepsilon$ and $M$) when
--
--   1. $Q^\Sigma_{\mathcal B}=M$ (13a);
--   2. $Q^\Sigma_{\mathcal A}\le\varepsilon M/\nu$ (13b);
--   3. $|Q_{\mathcal B_0}-\nu Q_{\mathcal B_j}|\le\varepsilon M$ for $j=1,\dots,J$ (13c).
--
--   There are $M$ jobs at component $\mathcal B$, comparatively few at $\mathcal A$, and $\mathcal B$ is approximately balanced.
-- source:
--   Bramson, D'Auria, Walton, Stability and Instability of the MaxWeight Policy, arXiv:1909.10825v2, display (13), p.6; ℐ_M, p.7

import Mathlib
import Definitions.Def_MaxWeightInstab_totalA
import Definitions.Def_MaxWeightInstab_totalB

namespace MaxWeightInstab

/-- The set `ℐ_M` of initial queue lengths satisfying (13) (Bramson, D'Auria & Walton, *Stability and Instability of the MaxWeight Policy*, arXiv:1909.10825v2, p.6):
`Q^Σ_ℬ(0) = M` (13a), `Q^Σ_𝒜(0) ≤ εM/ν` (13b), and `|Q_{ℬ₀}(0) − ν Q_{ℬ_j}(0)| ≤ εM` for
`j = 1, …, J` (13c). -/
def IsInitial {J : ℕ} (ν : ℕ) (ε M : ℝ) (x : State J) : Prop :=
  (totalB x : ℝ) = M ∧ (totalA x : ℝ) ≤ ε * M / ν ∧
    ∀ j : Fin J, |(x (Sum.inr 0) : ℝ) - ν * (x (Sum.inr j.succ) : ℝ)| ≤ ε * M

end MaxWeightInstab


