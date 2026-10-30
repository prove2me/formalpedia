-- Prove2me | Definitions.Def_ConsiderThenChoose_phi
-- name    : ConsiderThenChoose_phi
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:33:26.951417+00:00
-- url     : https://prove2.me/theorems/9c4b8ff9-b036-4c5d-bab2-47366eb26bca
-- title:
--   The projection $\Phi(S,T) = [\min(S)] \cap \bigcup_{u\in T} C_u$
-- statement:
--   For a subproblem $(S,T)$ let
--
--   $$
--   \Phi(S,T) = [\min(S)] \cap \Big( \bigcup_{u \in T} C_u \Big),
--   $$
--
--   where $[X] = \{1, \dots, X\}$. In words, $\Phi(S,T)$ is the set of products at least as preferred as $\min(S)$ that some type of $T$ considers. The paper's Lemma 2 shows that $\Phi$ is injective on the state space $\mathcal S$, which reduces counting states to counting the sets $\Phi(S,T)$.
--
--   **Formalization Note** The condition $p \le \min(S)$ is written "$p \le q$ for every $q \in S$", which agrees with it whenever $S$ is nonempty (as at every state) and avoids a junk value of $\min \emptyset$. $\Phi$ is defined on all pairs; the paper's $\Phi$ is its restriction to $\mathcal S$.
-- source:
--   Aouad, Farias and Levi, Assortment Optimization Under Consider-then-Choose Choice Models, Management Science 67(6) (2021), doi:10.1287/mnsc.2020.3681, §3 "State space mapping", p. 14

import Mathlib

namespace ConsiderThenChoose

/-- **The projection `Φ(S,T) = [min(S)] ∩ ⋃_{u∈T} C_u`.** Aouad, Farias and Levi, Management
Science 67(6) (2021), doi:10.1287/mnsc.2020.3681, §3 "State space mapping", unnumbered, p. 14:
"Φ : S → P([N]), (S,T) ↦ [min(S)] ∩ (⋃_{u∈T} C_u)", "each subproblem (S,T) is mapped to the
set of products exactly covered by the consideration sets T in the interval [min(S)]".

`phi C (S, T)` is the set of products `p` that are at least as preferred as every product of
`S` (that is, `p ≤ min(S)`) and lie in the consideration set of some type of `T`.

**Formalization Note** `[X] = {1, …, X}` in the paper, so `[min(S)]` is the set of products
`p ≤ min(S)`. The condition `∀ q ∈ S, p ≤ q` equals `p ≤ min(S)` whenever `S` is nonempty (as
it is at every state) and avoids a junk value for `min ∅`. Φ is defined on all pairs; the
paper's Φ is its restriction to the state space 𝒮, used through `Set.InjOn` and images. -/
def phi {N K : ℕ} (C : Fin K → Finset (Fin N)) (x : Finset (Fin N) × Finset (Fin K)) :
    Finset (Fin N) :=
  Finset.univ.filter fun p => (∀ q ∈ x.1, p ≤ q) ∧ ∃ u ∈ x.2, p ∈ C u

end ConsiderThenChoose


