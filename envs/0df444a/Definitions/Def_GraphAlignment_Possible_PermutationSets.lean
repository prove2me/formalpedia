-- Prove2me | Definitions.Def_GraphAlignment_Possible_PermutationSets
-- name    : GraphAlignment_Possible_PermutationSets
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T02:30:08.542052+00:00
-- url     : https://prove2.me/theorems/5ca9b575-ac92-4006-b561-9505e9ab64b0
-- title:
--   §4.1.2, pp. 14–15 — fixed points of a permutation p and the sets S¹₂ (ordered) and S̄²₂ (unordered pairs)
-- statement:
--   Sets of vertex pairs attached to a permutation $p$ of $\{1,\dots,n\}$ (§4.1.2).
--
--   1. $m$ is the number of fixed points of $p$, so that $\epsilon = m/n$ is the fraction of fixed points.
--   2. $S^1_2$ is the set of ordered pairs $(i,j)$ with $i \ne j$, $p(i) \ne i$ and $(p(i), p(j)) = (j, i)$, i.e. the pairs of $S_2 = \{(i,j) : i \ne j,\ i \ne p(i)\}$ that $p$ swaps.
--   3. $\bar S^2_2$ is the set of unordered pairs $\{i,j\}$, $i \ne j$, with $\{p(i), p(j)\} \ne \{i, j\}$.
--
--   These sets appear in the proof of Proposition 4.4, where the sum $\sum_{(i,j)\in S_2} A_{ij}B'_{p(i)p(j)}$ is split according to whether $p$ swaps the pair, fixes it as an unordered pair, or moves it.
--
--   **Formalization Note** The sets are defined for an arbitrary permutation $p$; in the paper $p$ is the permutation relating a candidate $\pi$ to the planted $\pi^*$, whose fixed points are the vertices where $\pi$ and $\pi^*$ agree. The condition $p(i) \ne i$ in $S^1_2$ is implied by the others and is kept to mirror $S^1_2 \subseteq S_2$.
-- source:
--   Hall, Massoulié, Partial Recovery in the Graph Alignment Problem, arXiv:2007.00533v5, pp. 14–15, §4.1.2, Definition 1 (9) and the definitions of S^1_2 and S̄^2_2

import Mathlib

namespace GraphAlignment.Possible

/-- The number `m` of fixed points of a permutation `p` of `{1, …, n}` (so `ε = m / n` is the
fraction of fixed points, §4.1.2, p. 14). -/
def numFixed {n : ℕ} (p : Equiv.Perm (Fin n)) : ℕ :=
  (Finset.univ.filter fun i => p i = i).card

/-- The set `S^1_2 = {(i, j) ∈ S_2 | (p(i), p(j)) = (j, i)}` of ordered pairs (§4.1.2, p. 15),
where `S_2` is the set of ordered pairs `(i, j)`, `i ≠ j`, with `i` not a fixed point of `p`. -/
def S12 {n : ℕ} (p : Equiv.Perm (Fin n)) : Finset (Fin n × Fin n) :=
  Finset.univ.filter fun x => x.1 ≠ x.2 ∧ p x.1 ≠ x.1 ∧ p x.1 = x.2 ∧ p x.2 = x.1

/-- The set `S̄^2_2 = {{i, j} | i ≠ j, {i, j} ≠ {p(i), p(j)}}` of unordered pairs (§4.1.2, p. 15). -/
def Sbar22 {n : ℕ} (p : Equiv.Perm (Fin n)) : Finset (Sym2 (Fin n)) :=
  Finset.univ.filter fun e => ¬ e.IsDiag ∧ e.map p ≠ e

end GraphAlignment.Possible


