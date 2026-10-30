-- Prove2me | Definitions.Def_NestedLogitAssort_PartialCapture_K
-- name    : NestedLogitAssort_PartialCapture_K
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:44:53.954634+00:00
-- url     : https://prove2.me/theorems/dbf0c25f-bf8f-424a-b31a-182e3e2652f6
-- title:
--   0–1 knapsack value $K_i(\epsilon_i)$
-- statement:
--   For a nest $i$ and a capacity $\epsilon$,
--
--   $$
--   K_i(\epsilon)=\max\Bigl\{\sum_{j\in N}r_{ij}v_{ij}z_{j}\ :\ \sum_{j\in N}v_{ij}z_{j}\le\epsilon,\ z\in\{0,1\}^n\Bigr\}.
--   $$
--
--   A 0–1 vector $z$ is identified with the set of products $j$ with $z_j=1$.
--
--   **Formalization Note** The maximum is a supremum of a finite set; for $\epsilon\ge 0$ the set contains the value $0$ of the empty set, so the supremum is attained. Capacities $\epsilon<0$ are never used.
-- source:
--   Davis, Gallego & Topaloglu, Assortment Optimization under Variants of the Nested Logit Model, revised manuscript of June 18, 2013, eq. (9), p. 22

import Mathlib
import Definitions.Def_NestedLogitAssort_PartialCapture_Instance

namespace NestedLogitAssort.PartialCapture

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

end NestedLogitAssort.PartialCapture


