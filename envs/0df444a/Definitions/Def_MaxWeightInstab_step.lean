-- Prove2me | Definitions.Def_MaxWeightInstab_step
-- name    : MaxWeightInstab_step
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:14:17.369735+00:00
-- url     : https://prove2.me/theorems/737d8f49-ed3d-45db-8b05-2c80603b540a
-- title:
--   One time unit of the network of Figure 1
-- statement:
--   One time unit maps queue lengths $Q$, a schedule $\sigma$ and an arrival pattern $e$ to new queue lengths. First the jobs present are served, $d_j=\sigma_j\wedge Q_j$ at each queue; then jobs arrive at their new queues:
--
--   $$
--   Q'_{\mathcal A_0}=Q_{\mathcal A_0}-d_{\mathcal A_0}+\sum_{j=1}^J d_{\mathcal B_j},\qquad
--   Q'_{\mathcal B_0}=Q_{\mathcal B_0}-d_{\mathcal B_0}+\sum_{j=1}^J d_{\mathcal A_j},
--   $$
--
--   $$
--   Q'_{\mathcal A_j}=Q_{\mathcal A_j}-d_{\mathcal A_j}+e_{\mathcal A_j},\qquad
--   Q'_{\mathcal B_j}=Q_{\mathcal B_j}-d_{\mathcal B_j}+e_{\mathcal B_j}\quad(j=1,\dots,J).
--   $$
--
--   Jobs served at $\mathcal A_0$ and $\mathcal B_0$ leave the network. "We assume that jobs initially present are first served, after which jobs arrive at their new queues" (p.5).
-- source:
--   Bramson, D'Auria, Walton, Stability and Instability of the MaxWeight Policy, arXiv:1909.10825v2, Figure 1, p.3; queueing equations (7)–(8) and the ordering convention, p.5

import Mathlib
import Definitions.Def_MaxWeightInstab_departure
import Definitions.Def_MaxWeightInstab_ExtArrivals

namespace MaxWeightInstab

/-- One time unit of the network of Figure 1 (Bramson, D'Auria & Walton, *Stability and Instability of the MaxWeight Policy*, arXiv:1909.10825v2, p.3 and p.5): the jobs present are served
first, `departure x σ q = min(σ_q, x_q)` at each queue, then jobs arrive at their new queues. Jobs
served at `𝒜_j` (`j ≥ 1`) move to `ℬ₀`, jobs served at `ℬ_j` (`j ≥ 1`) move to `𝒜₀`, jobs served at
`𝒜₀` and `ℬ₀` leave the network, and the external arrivals `e` join `𝒜₁, …, 𝒜_J, ℬ₁, …, ℬ_J`.

**Formalization Note.** "we assume that jobs initially present are first served, after which jobs
arrive at their new queues. The allocation of service at time t is governed by Q(t − 1)" (p.5). The
subtraction is exact: `min(σ_q, x_q) ≤ x_q`. -/
def step {J : ℕ} (x σ : State J) (e : ExtArrivals J) : State J
  | Sum.inl i => Fin.cases (motive := fun _ => ℕ)
      (x (Sum.inl 0) - departure x σ (Sum.inl 0) +
        ∑ j : Fin J, departure x σ (Sum.inr j.succ))
      (fun j => x (Sum.inl j.succ) - departure x σ (Sum.inl j.succ) +
        if e (Sum.inl j) then 1 else 0) i
  | Sum.inr i => Fin.cases (motive := fun _ => ℕ)
      (x (Sum.inr 0) - departure x σ (Sum.inr 0) +
        ∑ j : Fin J, departure x σ (Sum.inl j.succ))
      (fun j => x (Sum.inr j.succ) - departure x σ (Sum.inr j.succ) +
        if e (Sum.inr j) then 1 else 0) i

end MaxWeightInstab


