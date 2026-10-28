-- Prove2me | Definitions.Def_SyncPrefix_Huffman_DisjointCopies
-- name    : SyncPrefix_Huffman_DisjointCopies
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-10-27T07:30:00.303034+00:00
-- url     : https://prove2.me/theorems/c1f9c558-be27-42d8-811a-8abe55a12eaa
-- title:
--   Disjoint-copies Set Cover construction ($n$ disjoint copies of $I$)
-- statement:
--   Given a Set Cover instance $I = ([n], \mathcal{S})$ with universe $[n] = \{0, \dots, n-1\}$ and family of subsets $\mathcal{S} = (S_1, \dots, S_m)$, we define the $n$-fold disjoint-copies Set Cover instance $I' = \mathrm{scDisjointCopies}(I)$ as follows.
--
--   1. For each copy index $r \in [n]$ and point $x \in [n]$, the point embedding $\mathrm{scCopyPoint}(n, r, x) \in [n^2]$ maps $(r, x)$ to $r n + x$.
--   2. For each copy index $r \in [n]$ and subset $S \subseteq [n]$, the lifted subset is
--   $$
--   \mathrm{scCopySet}(n, r, S) = \{ r n + x : x \in S \} \subseteq [n^2].
--   $$
--   3. The duplicated Set Cover instance $\mathrm{scDisjointCopies}(I)$ has universe size $n^2$ and consists of the $n m$ subsets $\mathrm{scCopySet}(n, r, S_i)$ for $r \in [n]$ and $i \in [m]$.
--
--   This construction is used in the padding reduction before Corollary 8 to boost the minimum set cover size of $I$ by an exact factor of $n$ while squaring the universe size.
--
--   **Formalization Note** Points are represented in `Fin (I.n ^ 2)` and the family of sets is built via `(List.finRange I.n).flatMap (fun r => I.sets.map (scCopySet I.n r))`.
-- source:
--   Ryzhikov & Szykuła, Finding Short Synchronizing Words for Prefix Codes, arXiv:1806.06299v1, p. 8, proof of Corollary 8 (Set Cover padding)

import Mathlib.Data.List.FinRange
import Definitions.Def_SetCoverThreshold_SetCover_Instance

namespace SyncPrefix.Huffman

open SetCoverThreshold.SetCover

/-- Embedding of the `r`-th copy of point `x : Fin n` into `Fin (n ^ 2)` via `r * n + x`. -/
def scCopyPoint (n : ℕ) (r x : Fin n) : Fin (n ^ 2) :=
  ⟨r.val * n + x.val, by
    have hr := r.isLt
    have hx := x.isLt
    nlinarith⟩

/-- The copy of a subset `S ⊆ Fin n` in the `r`-th disjoint copy of the universe `Fin (n ^ 2)`. -/
def scCopySet (n : ℕ) (r : Fin n) (S : Finset (Fin n)) : Finset (Fin (n ^ 2)) :=
  S.image (scCopyPoint n r)

/-- The Set Cover instance formed by taking `I.n` disjoint copies of `I` (p. 9, proof of the
padding lemma before Corollary 8): `I.n ^ 2` points and `I.n * I.sets.length` sets. -/
def scDisjointCopies (I : SCInstance) : SCInstance where
  n := I.n ^ 2
  sets := (List.finRange I.n).flatMap fun r => I.sets.map (scCopySet I.n r)

end SyncPrefix.Huffman


