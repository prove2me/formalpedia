-- Prove2me | Definitions.Def_NestedLogitAssort_General_K
-- name    : NestedLogitAssort_General_K
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:48:05.913428+00:00
-- url     : https://prove2.me/theorems/12ec3de3-d6fa-428d-b9ae-31b9300900f3
-- title:
--   0–1 knapsack value $K_i(\epsilon_i)$
-- statement:
--   For a nest $i$ and a capacity $\epsilon\ge0$,
--
--   $$
--   K_i(\epsilon)=\max\Bigl\{\sum_{j\in N}r_{ij}v_{ij}z_j:\ \sum_{j\in N}v_{ij}z_j\le\epsilon,\ z\in\{0,1\}^n\Bigr\},
--   $$
--
--   the best total of $r_{ij}v_{ij}$ over assortments whose total preference weight is at most $\epsilon$ (problem (9)).
--
--   **Formalization Note** The maximum is a `sSup` over the finite, nonempty set of values of subsets $S$ with $\sum_{j\in S}v_{ij}\le\epsilon$; for $\epsilon\ge0$ it contains $0$ (from $S=\emptyset$), so it is the maximum. Negative $\epsilon$ is never used.
-- source:
--   Davis, Gallego & Topaloglu, Assortment Optimization under Variants of the Nested Logit Model, revised manuscript of June 18, 2013, eq. (9), p. 22

import Mathlib
import Definitions.Def_NestedLogitAssort_General_Instance

namespace NestedLogitAssort.General

/-- **The 0–1 knapsack value `K_i(ϵ_i)`.**
Davis, Gallego & Topaloglu, *Assortment Optimization under Variants of the Nested Logit Model*,
revised manuscript of June 18, 2013, eq. (9), p. 22:
`K_i(ϵ_i) = max { ∑_{j ∈ N} r_{ij} v_{ij} z_{ij} : ∑_{j ∈ N} v_{ij} z_{ij} ≤ ϵ_i, z_i ∈ {0,1}^n }`.

A vector `z_i ∈ {0,1}^n` is the indicator of the set `S = {j : z_{ij} = 1}`.

**Formalization Note.** For `ϵ ≥ 0` the set is finite and contains `0` (from `S = ∅`), so `sSup`
is its maximum. For `ϵ < 0` (outside the paper's range, and never used) the value is a junk
value. -/
noncomputable def K {M : Type*} {n : ℕ} (I : Instance M n) (i : M) (ε : ℝ) : ℝ :=
  sSup {s : ℝ | ∃ S : Finset (Fin n), ∑ j ∈ S, I.v i j ≤ ε ∧ s = ∑ j ∈ S, I.r i j * I.v i j}

end NestedLogitAssort.General


