-- Prove2me | Definitions.Def_KMeansTaper_cost2
-- name    : KMeansTaper_cost2
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T17:04:25.134194+00:00
-- url     : https://prove2.me/theorems/bb4f59f3-877a-423d-819e-d0086d4df3f3
-- title:
--   Squared cost $\mathrm{cost}_2(S)$, restricted optimum $\mathrm{opt}_{I'}$, optimum $\mathrm{OPT}_k$ and indicator lists
-- statement:
--   An **instance** $I=(J,F,d,k)$ is the published `OAI.MetricKMedian.Instance`: finitely many points $0,\dots,n-1$ with a rational metric $d$ (nonnegative, zero exactly on the diagonal, symmetric, triangle inequality), a set $J$ of clients, a set $F$ of candidate facilities (they may overlap, and other points may exist) and an integer $k$ with $1\le k\le |F|$.
--
--   For a set $S$ of points, $d(j,S)=\min_{i\in S}d(j,i)$, and the **squared cost** is
--
--   $$\mathrm{cost}_2(S)=\sum_{j\in J} d(j,S)^2 .$$
--
--   For a set $F'\subseteq F$ of facilities, $\mathrm{opt}_{I'}$ is the minimum of $\mathrm{cost}_2(S)$ over nonempty $S\subseteq F'$ with $|S|\le k$: the optimum of the **restricted instance** $I'$ with the same clients, distances and $k$ (Appendix F). The **optimum** is
--
--   $$\mathrm{OPT}_k=\min_{\emptyset\ne S\subseteq F,\ |S|\le k}\mathrm{cost}_2(S).$$
--
--   An algorithm returns a set $S$ as its **indicator list**: the list of $n$ bits whose $i$-th bit says whether $i\in S$.
--
--   These are the objective and the benchmark of metric k-means with candidate centers, used by every statement of the mission.
--
--   **Formalization Note** The published `nearest I j S` is $d(j,S)$ and is $0$ for $S=\emptyset$, where the paper's value is $+\infty$; therefore the optimum ranges over nonempty sets (for $F'=F$ these are `OAI.MetricKMedian.feasibleSets`) and every statement asks for a nonempty output. `optimumOn` is $0$ when $F'=\emptyset$.
-- source:
--   Zhu, A tight approximation for metric k-means via squared tapered rounding, STOC 2027 submission (manuscript sha256 8b6610229e43dc2441325b120437136afe762dbd6e873f73919fcb6b043fc5a3), Section 2 ("Problem"), p.3 (PDF p.6); Appendix F, Notation, p.42 (PDF p.45)

import Mathlib
import Definitions.Def_MetricKMedian

namespace KMeansTaper

open OAI.MetricKMedian (Instance nearest)

/-- **Squared cost** `cost₂(S) = ∑_{j ∈ J} d(j, S)²`, Section 2 ("Problem"), p.3 (PDF p.6).

Zhu, *A tight approximation for metric k-means via squared tapered rounding*, STOC 2027
submission (manuscript sha256 8b661022…fc5a3).

**Formalization Note.** The instance is the published `OAI.MetricKMedian.Instance`: points
`Fin n` with a finite rational metric, client set `J`, candidate facility set `F` and
`1 ≤ k ≤ |F|`. `nearest I j S` is the real distance `d(j, S) = min_{i ∈ S} d(j, i)`; it is `0`
when `S = ∅` (the paper's value is `+∞`), so every statement that uses `cost2` asks for a nonempty
`S`. -/
noncomputable def cost2 (I : Instance) (S : Finset (Fin I.n)) : ℝ :=
  ∑ j ∈ I.clients, (nearest I j S) ^ 2

/-- **Feasible sets of a restricted instance**: nonempty `S ⊆ F'` with `|S| ≤ k` (for `F' = F`
this is `OAI.MetricKMedian.feasibleSets I`). -/
def feasibleOn (I : Instance) (F' : Finset (Fin I.n)) : Finset (Finset (Fin I.n)) :=
  F'.powerset.filter (fun S => S.Nonempty ∧ S.card ≤ I.k)

/-- **Optimum over a facility subset** `opt_{I'}`: the minimum of `cost₂(S)` over nonempty
`S ⊆ F'` with `|S| ≤ k`; this is the optimum of the restricted instance `I'` of Appendix F, p.42
(PDF p.45), which keeps the clients, distances and `k`.

**Formalization Note.** The value is `0` when no such `S` exists (only for `F' = ∅`). -/
noncomputable def optimumOn (I : Instance) (F' : Finset (Fin I.n)) : ℝ :=
  if h : (feasibleOn I F').Nonempty then
    ((feasibleOn I F').image (cost2 I)).min' (h.image _)
  else 0

/-- **The optimum** `OPT_k = min_{|S| ≤ k} cost₂(S)`, Section 2, p.3 (PDF p.6): the optimum over
the whole candidate facility set.

**Formalization Note.** The minimum is over nonempty `S ⊆ F` with `|S| ≤ k` (the set
`OAI.MetricKMedian.feasibleSets I`); the empty set is excluded because its paper cost is `+∞`
(and `0` under `nearest`). The minimum exists because `1 ≤ k ≤ |F|`. -/
noncomputable def optimum2 (I : Instance) : ℝ := optimumOn I I.facilities

/-- **Indicator bit-list** of a set `S ⊆ Fin n`: bit `i` is `true` iff `i ∈ S`. This is how an
algorithm "returns S" (the convention of the published `OAI.MetricKMedian.Correct`). -/
def mask (I : Instance) (S : Finset (Fin I.n)) : List Bool :=
  List.ofFn (fun i : Fin I.n => decide (i ∈ S))

end KMeansTaper


