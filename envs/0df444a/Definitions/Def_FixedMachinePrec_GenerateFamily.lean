-- Prove2me | Definitions.Def_FixedMachinePrec_GenerateFamily
-- name    : FixedMachinePrec_GenerateFamily
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:06:48.628823+00:00
-- url     : https://prove2.me/theorems/b15daa23-14f3-433e-9c81-88443d75e166
-- title:
--   Algorithm 1, GenerateFamily$(J,m,K)$: the layers $F_1,\dots,F_K$
-- statement:
--   **Algorithm 1** builds the family $\mathcal F_K$ layer by layer, as lists of distinct sets.
--
--   1. The atomic list is $J,\emptyset,R_1,\dots,R_{N+1}$, followed by $A,P_A,D_A,\hat P_A,\hat D_A$ for each $m$-set $A$ in lexicographic identifier order.
--   2. Layer $F_1$: for each atom $X$ in the atomic list, insert $X$ and then $J\setminus X$; a set is appended exactly when it is not yet stored.
--   3. For $k=2,\dots,K$: layer $F_k$ starts as a copy of $F_{k-1}$; then for $i=1,\dots,k-1$, for each $X\in F_i$ and each $Y\in F_{k-i}$ in their stored order, insert $X\cup Y$ and then $X\cap Y$ with the same duplicate test.
--
--   The procedure returns $F_K$ together with the intermediate layers; the algorithm uses $F_{4m+5}$ and retains $F_{m+3}$.
--
--   **Formalization Note** The binary trie of the paper is the RAM's dictionary; here a layer is the list of its distinct sets in insertion order, which is the order the trie-based procedure stores them in.
-- source:
--   K. Jansen, Precedence Constraint Scheduling on a Fixed Number of Machines, manuscript dated 1 November 2026 (sha256 08cdf3e1…), §2.3, Algorithm 1, p.5

import Mathlib
import Definitions.Def_FixedMachinePrec_Formula
import Definitions.Def_FixedMachinePrec_FixedOrders

namespace FixedMachinePrec

/-- Insert a set at the end of a list unless an identical set is already stored (the binary trie's
exact duplicate test, Jansen §2.3, p.5). -/
def insertNew {N : ℕ} (l : List (Finset (Fin N))) (X : Finset (Fin N)) : List (Finset (Fin N)) :=
  if X ∈ l then l else l ++ [X]

/-- The atomic list of Algorithm 1, Step 1: `J, ∅, R_1, …, R_{N+1}`, followed by
`A, P_A, D_A, P̂_A, D̂_A` for each `m`-set `A` in lexicographic identifier order. -/
def atomList {N : ℕ} (prec : Fin N → Fin N → Prop) [DecidableRel prec] (rank : Fin N → ℕ)
    (m : ℕ) : List (Finset (Fin N)) :=
  [Finset.univ, ∅] ++ (List.range (N + 1)).map (fun i => Atom.rankSuffixSet rank (i + 1)) ++
    (mSubsetsLex N m).flatMap fun A =>
      [A, predCone prec A, succCone prec A, weakPredCone prec A, weakSuccCone prec A]

/-- Layer `F_1` (Algorithm 1, Step 2): for each atom `A` in the atomic list, insert `A` and then
`J \ A`, appending a vector exactly when it is new. -/
def layerOne {N : ℕ} (prec : Fin N → Fin N → Prop) [DecidableRel prec] (rank : Fin N → ℕ)
    (m : ℕ) : List (Finset (Fin N)) :=
  (atomList prec rank m).foldl (fun l A => insertNew (insertNew l A) (Finset.univ \ A)) []

/-- One round of Algorithm 1, Step 3, from the stored layers `[F_1, …, F_k]` (`k ≥ 1`) to layer
`F_{k+1}`: start from a copy of `F_k`; then for `i = 1, …, k`, for each `X ∈ F_i` and each
`Y ∈ F_{k+1−i}` in their stored order, insert `X ∪ Y` and then `X ∩ Y`. -/
def nextLayer {N : ℕ} (Ls : List (List (Finset (Fin N)))) : List (Finset (Fin N)) :=
  let k := Ls.length
  (List.range k).foldl
    (fun acc i =>
      (Ls.getD i []).foldl
        (fun acc X =>
          (Ls.getD (k - 1 - i) []).foldl (fun acc Y => insertNew (insertNew acc (X ∪ Y)) (X ∩ Y))
            acc)
        acc)
    (Ls.getD (k - 1) [])

/-- **Algorithm 1, GenerateFamily(J, m, K)** (Jansen, *Precedence Constraint Scheduling on a Fixed
Number of Machines*, manuscript, sha256 08cdf3e1…, Algorithm 1, p.5): `genLayers … K` is the list
of stored layers `[F_1, …, F_K]` (empty for `K = 0`).

**Formalization Note** The binary trie is an implementation detail of the RAM; here a layer is the
list of its distinct vectors in insertion order, which is the order the trie-based procedure
stores them in. The source lists in Step 3(b) all have index smaller than the new layer and stay
fixed, as in the paper. -/
def genLayers {N : ℕ} (prec : Fin N → Fin N → Prop) [DecidableRel prec] (rank : Fin N → ℕ)
    (m : ℕ) : ℕ → List (List (Finset (Fin N)))
  | 0 => []
  | k + 1 =>
    match k with
    | 0 => [layerOne prec rank m]
    | _ + 1 =>
      let Ls := genLayers prec rank m k
      Ls ++ [nextLayer Ls]

/-- The stored list `F_K` returned by Algorithm 1 (layer `K`, `K ≥ 1`). -/
def generateFamily {N : ℕ} (prec : Fin N → Fin N → Prop) [DecidableRel prec] (rank : Fin N → ℕ)
    (m K : ℕ) : List (Finset (Fin N)) :=
  (genLayers prec rank m K).getD (K - 1) []

end FixedMachinePrec


