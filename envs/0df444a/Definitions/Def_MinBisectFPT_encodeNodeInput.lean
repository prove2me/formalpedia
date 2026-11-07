-- Prove2me | Definitions.Def_MinBisectFPT_encodeNodeInput
-- name    : MinBisectFPT_encodeNodeInput
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:56:42.609197+00:00
-- url     : https://prove2.me/theorems/60da8adf-6e47-49c7-bbb6-bcae7bf6042b
-- title:
--   Bit encoding of the input and output of Algorithm 1
-- statement:
--   The output word of Lemma 4.6 is the table of $t$: the exact integers $C_t(T,\ell,j)$ in binary, for $T\subseteq\sigma(t)$ by bitmask over $\sigma(t)$ in increasing order, $0\le\ell\le|\alpha(t)|$ and $0\le j\le k$.
--
--   The input word holds the input of the goal, then $\beta(t)$, $\sigma(t)$, $\gamma(t)$, the number of children, and for each child in increasing order $\sigma(c)$, $\alpha(c)$ and its table. That is the printed input of Algorithm 1, "a node t of the decomposition, and the tables $C_c$ of its children".
--
--   **Formalization Note** Only the data of the node is included, not the whole decomposition. (D1)–(D3) alone do not bound the number of nodes, and a machine must read its whole input, so a word holding the whole decomposition would make a bound in $n$ and $k$ false.
-- source:
--   Anand, Kipouridis, Węgrzycki, Counting over Unbreakable Decompositions, STOC 2027 submission (manuscript sha256 8db80a52…), Lemma 4.6, p.14; Algorithm 1, p.15

import Mathlib
import Definitions.Def_MinBisectFPT_encodeCounts
import Definitions.Def_MinBisectFPT_NodeCtx

open scoped Classical

namespace MinBisectFPT

open ExponomialAssortment.FPTAS (encodeNat)

/-- The subset of `S` picked by the bits of `m`, with the elements of `S` in increasing order. -/
noncomputable def maskSubset {n : ℕ} (S : Finset (Fin n)) (m : ℕ) : Finset (Fin n) :=
  S.filter fun v => m.testBit (((List.finRange n).filter (· ∈ S)).idxOf v)

/-- **The table of `t` as a word**: the exact integers `C_t(T, ℓ, j)` in binary, for `T ⊆ σ(t)` by
bitmask, `0 ≤ ℓ ≤ |α(t)|`, `0 ≤ j ≤ k`, in that order. Anand, Kipouridis, Węgrzycki, *Counting over
Unbreakable Decompositions*, STOC 2027 submission (manuscript sha256 8db80a52…), p.11. -/
noncomputable def encodeTable {n : ℕ} (G : SimpleGraph (Fin n)) (D : RootedTD n) (k : ℕ)
    (t : Fin D.N) : List Bool :=
  (List.range (2 ^ (D.adhesion t).card)).flatMap fun m =>
    (List.range ((D.component t).card + 1)).flatMap fun l =>
      (List.range (k + 1)).flatMap fun j =>
        encodeNat (tableCount G D t (maskSubset (D.adhesion t) m) l j)

/-- **The input of Algorithm 1** (p.15): "a node t of the decomposition, and the tables C_c of its
children". The graph and `k`; `β(t)`, `σ(t)`, `γ(t)`; the number of children; and for each child in
increasing order its `σ(c)`, `α(c)` and table.

**Formalization Note** Only the data of the node, not the whole decomposition, so the input length does
not depend on the number of nodes (properties (D1)–(D3) alone do not bound it). -/
noncomputable def encodeNodeInput {n : ℕ} (G : SimpleGraph (Fin n)) (D : RootedTD n) (k : ℕ)
    (t : Fin D.N) : List Bool :=
  encodeInput G k ++ encodeSet (D.bag t) ++ encodeSet (D.adhesion t) ++ encodeSet (D.cone t) ++
    encodeNat (D.children t).card ++
      ((List.finRange D.N).filter (· ∈ D.children t)).flatMap fun c =>
        encodeSet (D.adhesion c) ++ encodeSet (D.component c) ++ encodeTable G D k c

end MinBisectFPT


