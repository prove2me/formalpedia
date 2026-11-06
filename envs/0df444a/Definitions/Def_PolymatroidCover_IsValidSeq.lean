-- Prove2me | Definitions.Def_PolymatroidCover_IsValidSeq
-- name    : PolymatroidCover_IsValidSeq
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:20:09.812221+00:00
-- url     : https://prove2.me/theorems/8d3478ab-7fff-4f3b-93be-025e1e259263
-- title:
--   Definition 3.2: valid search sequence
-- statement:
--   Let $S = S_1 \sqcup \dots \sqcup S_k$ be a valid $k$-coloring and $h$ the element being inserted. A search sequence $T = (T^1, \dots, T^L)$ is **valid** with respect to this coloring if every layer $T^i = (a, j, R)$, $i \in [L]$, satisfies
--
--   1. (V1, adding) $a \in B(T^{<i}) \cup \{h\}$ and $f(a \mid A_j^{<i} \cup B_j^{<i}) = f(a)$;
--   2. (V2, blocking) $R$ is the minimal minimizer of $\min_{X \subseteq S_j \setminus B_j^{<i}} \tilde f(X \mid \{a\} \cup A_j^{<i} \cup B_j^{<i})$ and $R \ne \emptyset$.
--
--   Validity depends on the coloring through the domain of (V2). The algorithm maintains a valid coloring and a valid search sequence.
--
--   **Formalization Note** Layers are indexed from $0$ (`T[t]` is $T^{t+1}$, `T.take t` is $T^{<t+1}$). The validity of the coloring is a separate hypothesis wherever it is assumed.
-- source:
--   Bérczi, Chandrasekaran, Chekuri, Liu, Ravi, Approximate Covering and Packing in Polymatroids, STOC 2027 submission (manuscript sha256 47f38a6f…), §3.1, Definition 3.2, p.13 (PDF p.15)

import Mathlib
import Definitions.Def_PolymatroidCover_IsAddingPair
import Definitions.Def_PolymatroidCover_IsBlockingSet

namespace PolymatroidCover

/-- Definition 3.2 (Bérczi–Chandrasekaran–Chekuri–Liu–Ravi, *Approximate Covering and Packing in Polymatroids*, STOC 2027 submission (manuscript sha256 47f38a6f…), printed p.13 = PDF p.15): the search sequence `T = (T^1, …, T^L)`
is valid with respect to the coloring `S_1 ⊔ ⋯ ⊔ S_k` (and the element `h` being inserted) if
every layer `T^i = (a, j, R)` satisfies
* (V1) (Adding) `a ∈ B(T^{<i}) ∪ {h}` and `f(a | A_j^{<i} ∪ B_j^{<i}) = f(a)`;
* (V2) (Blocking) `R` is the minimal minimizer of
  `min_{X ⊆ S_j \ B_j^{<i}} f̃(X | {a} ∪ A_j^{<i} ∪ B_j^{<i})` and `R ≠ ∅`.

**Formalization Note** Layers are 0-based: `T[t]` is the paper's `T^{t+1}` and `T.take t` is
`T^{<t+1}`. (V1) is `IsAddingPair` for the prefix and (V2) is `IsBlockingSet` for the prefix
plus nonemptiness. The validity of the coloring itself is a separate hypothesis
(`IsValidColoring`) wherever the paper assumes it. -/
def IsValidSeq {n k : ℕ} (f : Finset (Fin n) → ℕ) (h : Fin n) (col : Fin k → Finset (Fin n))
    (T : List (Layer n k)) : Prop :=
  ∀ (t : ℕ) (ht : t < T.length),
    IsAddingPair f h (T.take t) (T[t]'ht).add (T[t]'ht).color ∧
      IsBlockingSet f col (T.take t) (T[t]'ht).add (T[t]'ht).color (T[t]'ht).block ∧
      (T[t]'ht).block.Nonempty

end PolymatroidCover


