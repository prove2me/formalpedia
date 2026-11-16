-- Prove2me | Definitions.Def_MetricMatchingDistortion_Supplement_RSD
-- name    : MetricMatchingDistortion_Supplement_RSD
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:02:07.258234+00:00
-- url     : https://prove2.me/theorems/88d4dc14-2687-4ca9-b1b0-4f939d7229ef
-- title:
--   Serial dictatorship with a processing order, and the expected cost of Random Serial Dictatorship
-- statement:
--   Let $\tau$ be a processing order, i.e. a bijection from positions $0,\dots,n-1$ to agents. **Serial dictatorship** $\mathrm{SD}(\tau)$ lets the agent $\tau(0)$ take her favorite item, then $\tau(1)$ take her favorite item among those still available, and so on; $\mathrm{SD}(\tau)(a)$ denotes the item agent $a$ receives.
--
--   **Random Serial Dictatorship (RSD)** processes the agents in a uniformly random order. Its expected cost under a distance function $d$ is
--   $$\mathbb E_{M\sim\mathrm{RSD}(\sigma)}[\mathrm{cost}(M,d)]=\frac1{n!}\sum_{\tau}\sum_{a}d\big(a,\mathrm{SD}(\tau)(a)\big).$$
--
--   RSD is the mechanism of the paper's Theorem 1.
--
--   **Formalization Note** "Favorite item of a set" is the published `rankPick` of the PS definition. Rankings are strict, so the choice has no ties.
-- source:
--   Charikar, Haqi, Hastings, Huang, Ramakrishnan, Sublinear Metric Distortion for Matching, arXiv:2611.05777 (held version, sha256 fdf3452b105082d6ff680c8a762ec950298417efdebeb216b721705a9802e0da), p.1 (PDF p.3) and §3.3, p.16 (PDF p.18)

import Mathlib
import Definitions.Def_MetricMatchingDistortion_Ranking
import Definitions.Def_MetricMatchingDistortion_psAlloc

namespace MetricMatchingDistortion.Supplement

open MetricMatchingDistortion Finset

variable {n : ℕ}

/-- One turn of a serial dictatorship: the state is the set of items already taken and the current
assignment `agent ↦ item`; agent `a` takes her favorite item among those not yet taken
(`rankPick`, the base mission's "favorite item of a nonempty set"). If no item is left, nothing
changes (this never happens while fewer than `n` agents have chosen). -/
def sdStep (rk : Ranking n) (s : Finset (Fin n) × (Fin n → Fin n)) (a : Fin n) :
    Finset (Fin n) × (Fin n → Fin n) :=
  if h : (univ \ s.1).Nonempty then
    (insert (rankPick rk a (univ \ s.1) h) s.1,
      Function.update s.2 a (rankPick rk a (univ \ s.1) h))
  else s

/-- **Serial dictatorship with processing order `τ`.** Charikar et al., *Sublinear Metric
Distortion for Matching*, arXiv:2611.05777 (held version, sha256 fdf3452b…), p.1 (PDF p.3) and
§3.3, p.16 (PDF p.18): RSD "processes the agents in a uniformly random order, and greedily matches
each to her favorite available item"; "Random serial dictatorship (RSD) processes agents in a
uniformly random order and assigns each agent her favorite available item."

`τ i` is the agent processed at position `i` (positions `0, 1, …, n − 1`). `sdAssign rk τ a` is the
item agent `a` receives: the agents choose in the order `τ 0, τ 1, …`, each taking her favorite item
among those not taken by earlier agents.

**Formalization Note.** Rankings are strict, so the choice has no ties. The initial assignment
`id` is overwritten for every agent, since at each of the `n` turns some item is still free. -/
def sdAssign (rk : Ranking n) (τ : Equiv.Perm (Fin n)) : Fin n → Fin n :=
  (((List.finRange n).map τ).foldl (sdStep rk) (∅, id)).2

/-- **Expected cost of RSD**, `E_{M∼RSD(σ)}[cost(M, d)]` (§2, p.10, and p.1): the processing order
is uniform over the `n!` orders, so the expected cost is
`(1/n!) ∑_τ ∑_a d(a, SD(τ)(a))`. -/
noncomputable def rsdExpectedCost (rk : Ranking n) (d : Fin n ⊕ Fin n → Fin n ⊕ Fin n → ℝ) : ℝ :=
  ((Nat.factorial n : ℝ))⁻¹ *
    ∑ τ : Equiv.Perm (Fin n), ∑ a, d (Sum.inl a) (Sum.inr (sdAssign rk τ a))

end MetricMatchingDistortion.Supplement


