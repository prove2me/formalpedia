-- Prove2me | Definitions.Def_SplitPMSGame_pmsCost
-- name    : SplitPMSGame_pmsCost
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:12:16.008497+00:00
-- url     : https://prove2.me/theorems/3b0a38d0-fad5-454d-a54b-5bc29bd21d32
-- title:
--   The PMS game $(N,P)$ of equation (1)
-- statement:
--   Let $N$ be a finite set of players, each player $i$ owning machines of total speed $v(\{i\})\in\mathbb Q_{>0}$, and let $J(N)$ be a finite set of jobs; job $j$ has processing requirement $p_j\ge0$ and belongs to its **father** $f(j)\in N$. For a coalition $S\subseteq N$ write $J(S)=\{j : f(j)\in S\}$, $\psi(S)=|J(S)|$, $v(S)=\sum_{i\in S}v(\{i\})$, and $p^S_1\le\dots\le p^S_{\psi(S)}$ for the requirements of $J(S)$ in nondecreasing order. The **PMS game** has characteristic function
--   $$
--   P(S)=\frac{1}{v(S)}\sum_{k=1}^{\psi(S)}(\psi(S)-k+1)\,p^S_k .
--   $$
--   The module also defines $J(S)$, the number $\psi(\{i\})$ of jobs of player $i$, and $v(S)$.
--
--   $P(S)$ is the minimum total completion time of the jobs of $S$ on the pooled machines of $S$ when jobs may be split ($Q|split|\sum C_j$); it is the game whose total balancedness the mission proves.
--
--   **Formalization Note** Jobs are `Fin ψ`, the father map is `f : Fin ψ → N`, speeds are `v : N → ℚ` (only the total speed of a player's machines matters). The requirements are sorted inside (1), so the jobs need not be indexed in nondecreasing order. $P(\emptyset)=0$.
-- source:
--   Alon, Anily, The Basic Core of a Parallel Machines Scheduling Game, MSOM 25(6) (2023), doi:10.1287/msom.2021.0337, §4.1–§4.2, pp.2237–2239 (PDF pp.6–8), eq. (1)

import Mathlib
import Definitions.Def_SplitPMSGame_sptCost

namespace SplitPMSGame

/-- The jobs `J(S)` of a coalition `S` (Alon, Anily, *The Basic Core of a Parallel Machines
Scheduling Game*, MSOM 25(6) (2023), §4.1, p.2238): the jobs whose father `f(j)` is in `S`.

**Formalization Note** The jobs of `J(N)` are the indices `Fin ψ` (paper index `j` is `j − 1`);
`f : Fin ψ → N` is the father map. -/
def jobsOf {N : Type*} [DecidableEq N] {ψ : ℕ} (f : Fin ψ → N) (S : Finset N) : Finset (Fin ψ) :=
  Finset.univ.filter (fun j => f j ∈ S)

/-- The number `ψ({i})` of jobs of player `i` (MSOM 2023, §4.1, p.2237). -/
def jobCount {N : Type*} [DecidableEq N] {ψ : ℕ} (f : Fin ψ → N) (i : N) : ℕ :=
  (jobsOf f {i}).card

/-- The total speed `v(S) = ∑_{i∈S} v({i})` of the machines of a coalition (MSOM 2023, §4.1,
p.2238), with each player's total speed `v({i}) ∈ ℚ` cast to `ℝ`. -/
def speed {N : Type*} (v : N → ℚ) (S : Finset N) : ℝ :=
  ∑ i ∈ S, (v i : ℝ)

/-- **The PMS game** `(N, P)` (MSOM 2023, §4.2, eq. (1), p.2239):
`P(S) = (1/v(S)) ∑_{k=1}^{ψ(S)} (ψ(S) − k + 1) p^S_k`, where `p^S_1 ≤ ⋯ ≤ p^S_{ψ(S)}` are the
processing requirements of the jobs of `J(S)` in nondecreasing order and `v(S)` is the total
speed of the coalition. It is the cost of `Q|split|∑Cⱼ` for the pooled machines of `S`.

**Formalization Note** Players `N`; jobs `Fin ψ` with requirements `p : Fin ψ → ℝ` and father
map `f : Fin ψ → N`; per-player total speeds `v : N → ℚ` (the paper notes that "the number of
machines in M({i}) is immaterial", p.2238). `P` is defined by equation (1), as the paper takes
it. The requirements are sorted inside `sptCost`, so `p` need not be indexed in nondecreasing
order. `P(∅) = 0`. -/
noncomputable def pmsCost {N : Type*} [DecidableEq N] {ψ : ℕ} (p : Fin ψ → ℝ) (f : Fin ψ → N)
    (v : N → ℚ) (S : Finset N) : ℝ :=
  sptCost ((jobsOf f S).val.map p) (speed v S)

end SplitPMSGame


