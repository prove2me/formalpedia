-- Prove2me | Definitions.Def_HypClass1_IsPseudorandom3
-- name    : HypClass1_IsPseudorandom3
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:25:08.547701+00:00
-- url     : https://prove2.me/theorems/98792cd8-43d0-4b4f-ac92-bc56e5ab431a
-- title:
--   $(\varepsilon,p,n)$-pseudorandom 3-graph
-- statement:
--   For a 3-graph $H$ on a vertex set $V$ and a matching $M \subseteq V^{(2)}$ of pairs and $Z \subseteq V$, let $E_H(M, Z) = \{\{x,y,z\} \in H : \{x,y\} \in M, z \in Z\}$ and $e_H(M,Z) = |E_H(M,Z)|$.
--
--   Let $\varepsilon, p \in [0,1]$ and let $H$ be a 3-graph on $n$ vertices. $H$ is **$(\varepsilon, p, n)$-pseudorandom** if:
--   1. (B1) for all distinct $x, y \in V$, $\deg_H(x,y) = (1 \pm \varepsilon)pn$;
--   2. (B2) for every matching $M \subseteq V^{(2)}$ and $Z \subseteq V$ with $|M|, |Z| \ge \varepsilon n$, $e_H(M,Z) = (1\pm\varepsilon)p|M||Z|$;
--   3. (B3) if $|M| < \varepsilon n$ and $|Z| = 2|M|$, then $e_H(M,Z) \le 4\varepsilon p n |M|$;
--   4. (B4) if $|Z| < \varepsilon n$ and $|M| = 2|Z|$, then $e_H(M,Z) \le 4\varepsilon p n |Z|$.
--
--   Here $x = (1\pm\varepsilon)y$ means $(1-\varepsilon)y \le x \le (1+\varepsilon)y$. This is the 3-graph analogue of Definition 4.1, chosen so that bipartite projections of pseudorandom 3-graphs are pseudorandom (Lemma 5.2).
--
--   **Formalization Note** The vertex set is a finite set $W$ of an ambient type with $n = |W|$, so the definition applies to induced subgraphs $H[U]$; the first clause says $H \subseteq W^{(3)}$. The module also defines $e_H(M,Z)$.
-- source:
--   Chatterjee, Ferber, Sales, Shurman, Almost Every 3-Uniform Hypergraph is Class 1, manuscript (STOC 2027 submission, version of 2026-11-03, sha256 ce3bba9d…), Definition 4.4 and the display before it, p.10

import Mathlib
import Definitions.Def_HypClass1_codeg
import Definitions.Def_HypClass1_IsMatching

namespace HypClass1

/-- `e_H(M, Z) = |E_H(M, Z)|`, `E_H(M, Z) = {{x, y, z} ∈ H : {x, y} ∈ M, z ∈ Z}`. Chatterjee, Ferber, Sales, Shurman, *Almost Every 3-Uniform Hypergraph is Class 1*, manuscript
(STOC 2027 submission, version of 2026-11-03, sha256 ce3bba9d…), §4 p.10.

**Formalization Note.** An edge `{x, y, z}` is `insert z m` with `m = {x, y} ∈ M`, `z ∈ Z`, `z ∉ m`. When
`M` is a matching, at most one pair of `M` lies inside a given edge, so counting edges is the paper's
cardinality of the set `E_H(M, Z)`. -/
def eHMZ {V : Type*} [DecidableEq V] (H M : Finset (Finset V)) (Z : Finset V) : ℕ :=
  (H.filter (fun e => ∃ m ∈ M, ∃ z ∈ Z, z ∉ m ∧ e = insert z m)).card

/-- **(ε, p, n)-pseudorandom 3-graph**, Definition 4.4. Chatterjee, Ferber, Sales, Shurman, *Almost Every 3-Uniform Hypergraph is Class 1*, manuscript
(STOC 2027 submission, version of 2026-11-03, sha256 ce3bba9d…), p.10:
"Let ε, p ∈ [0, 1] and let H be a 3-graph on n vertices. We say that H is (ε, p, n)-pseudorandom if
the following hold:
(B1) For every x, y ∈ V, we have deg_H(x, y) = (1 ± ε)pn;
(B2) For every matching M ⊆ V^{(2)} and set of vertices Z ⊆ V such that |M|, |Z| ≥ εn, it holds
e_H(M, Z) = (1 ± ε)p|M||Z|;
(B3) For every matching M ⊆ V^{(2)} and set of vertices Z ⊆ V such that |M| < εn and |Z| = 2|M|,
it holds e_H(M, Z) ≤ 4εpn|M|;
(B4) For every matching M ⊆ V^{(2)} and set of vertices Z ⊆ V such that |Z| < εn and |M| = 2|Z|,
it holds e_H(M, Z) ≤ 4εpn|Z|."

**Formalization Note.** The vertex set is a finite set `W` of an ambient type `V` and `n = |W|`, so the
same definition applies to induced subgraphs `H[U]` (Proposition 4.8); for a 3-graph on `[n]` take
`W = univ` in `Fin n`. The first clause says `H` is a 3-graph on `W`. `x = (1 ± ε)y` means
`(1 − ε)y ≤ x ≤ (1 + ε)y` (p.9). (B1) is over distinct `x ≠ y` (a codegree). A matching
`M ⊆ W^{(2)}` is a set of pairwise disjoint two-element subsets of `W`. -/
def IsPseudorandom3 {V : Type*} [DecidableEq V] (ε p : ℝ) (W : Finset V)
    (H : Finset (Finset V)) : Prop :=
  H ⊆ W.powersetCard 3 ∧
  (∀ x ∈ W, ∀ y ∈ W, x ≠ y →
      (1 - ε) * p * W.card ≤ codeg H x y ∧ (codeg H x y : ℝ) ≤ (1 + ε) * p * W.card) ∧
  (∀ M : Finset (Finset V), M ⊆ W.powersetCard 2 → IsMatching M → ∀ Z ⊆ W,
      ε * W.card ≤ M.card → ε * W.card ≤ Z.card →
      (1 - ε) * p * M.card * Z.card ≤ eHMZ H M Z ∧
        (eHMZ H M Z : ℝ) ≤ (1 + ε) * p * M.card * Z.card) ∧
  (∀ M : Finset (Finset V), M ⊆ W.powersetCard 2 → IsMatching M → ∀ Z ⊆ W,
      (M.card : ℝ) < ε * W.card → Z.card = 2 * M.card →
      (eHMZ H M Z : ℝ) ≤ 4 * ε * p * W.card * M.card) ∧
  (∀ M : Finset (Finset V), M ⊆ W.powersetCard 2 → IsMatching M → ∀ Z ⊆ W,
      (Z.card : ℝ) < ε * W.card → M.card = 2 * Z.card →
      (eHMZ H M Z : ℝ) ≤ 4 * ε * p * W.card * Z.card)

end HypClass1


