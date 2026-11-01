-- Prove2me | Definitions.Def_MaxWeightInstab_extCount
-- name    : MaxWeightInstab_extCount
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:12:30.473521+00:00
-- url     : https://prove2.me/theorems/2d2495fc-8af9-4b59-9ae5-d444a7494c03
-- title:
--   Cumulative external arrivals
-- statement:
--   For an arrival path $e$, the cumulative number of external arrivals at the externally fed queue $j$ by time $t$ is the number of time units $1,\dots,t$ in which $j$ receives an arrival. For $j\in\{\mathcal A_1,\dots,\mathcal B_J\}$ this is the process $A_j(t)$ of Lemma 1 and (15).
-- source:
--   Bramson, D'Auria, Walton, Stability and Instability of the MaxWeight Policy, arXiv:1909.10825v2, (7b), p.5; Lemma 1, p.6

import Mathlib
import Definitions.Def_MaxWeightInstab_ExtArrivals

namespace MaxWeightInstab

/-- The cumulative number of external arrivals at the external queue `k` by time `t`
(Bramson, D'Auria & Walton, *Stability and Instability of the MaxWeight Policy*, arXiv:1909.10825v2, `E_j(t)` in (7b), p.5; `A_j(t)` for `j ∈ {𝒜₁, …, ℬ_J}` in Lemma 1, p.6): the arrivals of
time units `1, …, t` of the arrival path `e`. `k = Sum.inl j` is `𝒜_{j+1}`, `Sum.inr j` is `ℬ_{j+1}`. -/
def extCount {J : ℕ} (e : ℕ → ExtArrivals J) (k : Fin J ⊕ Fin J) (t : ℕ) : ℕ :=
  ∑ τ ∈ Finset.range t, if e (τ + 1) k then 1 else 0

end MaxWeightInstab


