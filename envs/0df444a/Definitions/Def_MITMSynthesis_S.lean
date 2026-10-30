-- Prove2me | Definitions.Def_MITMSynthesis_S
-- name    : MITMSynthesis_S
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:02:38.431823+00:00
-- url     : https://prove2.me/theorems/abe4c1b0-03e4-4a90-b754-3240a5b95869
-- title:
--   Depth-$m$ products $S_m$ and minimal depth
-- statement:
--   Let $M$ be a monoid and $V \subseteq M$. For $m \in \mathbb N$, $S_m$ is the set of products of exactly $m$ elements of $V$:
--
--   $$
--   S_m = \{\, U_1 U_2 \cdots U_m \;:\; U_1, \dots, U_m \in V \,\}, \qquad S_0 = \{I\}.
--   $$
--
--   Equivalently $S_0 = \{I\}$ and $S_i = V S_{i-1}$. With $V = V_{n,\mathcal G}$, $S_m$ is the set of unitaries implementable in depth $m$ over $\mathcal G$, the paper's $S_i$ (Lemma 1 and MITM-factor).
--
--   A number $k$ is the **minimal depth** of $U$ over $V$ if $U \in S_k$ and $k \le m$ for every $m$ with $U \in S_m$.
--
--   **Formalization Note** `S V m` is the set of `L.prod` over lists `L` of length `m` with entries in `V`; `List.prod [U₁, …, U_m] = U₁ * ⋯ * U_m` is the paper's operator-composition order. `IsMinDepth V U k` is a predicate, so no default value arises when $U$ is not implementable.
-- source:
--   Amy, Maslov, Mosca, Roetteler, A meet-in-the-middle algorithm for fast synthesis of depth-optimal quantum circuits, arXiv:1206.0758v3, §2, p. 4 (depth of a circuit as a product U_1U_2···U_m of elements of V_{n,G}); Lemma 1, p. 5 (S_i); MITM-factor, p. 6 (S_0 := {I}, S_i := V_{n,G}S_{i−1})

import Mathlib

namespace MITMSynthesis

/-- **`S_m`**: the elements that are products `U₁ U₂ ⋯ U_m` of exactly `m` elements of `V`
(arXiv:1206.0758v3, p. 4 and Lemma 1, p. 5; `S₀ = {I}`, `S_i = V S_{i-1}` on p. 6). With
`V = V_{n,G}` this is the set of unitaries implementable in depth `m` over `G`. -/
def S {M : Type*} [Monoid M] (V : Set M) (m : ℕ) : Set M :=
  {U | ∃ L : List M, L.length = m ∧ (∀ x ∈ L, x ∈ V) ∧ L.prod = U}

/-- `k` is the minimal depth of `U` over `V`: `U ∈ S V k`, and `k ≤ m` whenever `U ∈ S V m`. -/
def IsMinDepth {M : Type*} [Monoid M] (V : Set M) (U : M) (k : ℕ) : Prop :=
  U ∈ S V k ∧ ∀ m, U ∈ S V m → k ≤ m

end MITMSynthesis


