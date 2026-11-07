-- Prove2me | Definitions.Def_MatroidSensOracle_MatroidOracle
-- name    : MatroidSensOracle_MatroidOracle
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:49:25.077889+00:00
-- url     : https://prove2.me/theorems/9e55c4a1-ae80-46ca-82b2-50c298c959e5
-- title:
--   Matroid sensitivity oracles on the algebraic RAM: the general ($k$-sparse) and subset settings
-- statement:
--   These are the instance formats, queries and correctness conditions of the matroid sensitivity oracles of Theorems 3.5 and 3.7, on the algebraic RAM over a finite field $\mathbb F$.
--
--   1. **General setting.** The instance is a ground set of $m$ elements, each with its columns in the two representations (all $c$-sparse, where $c$ is the sparsity of the theorem) and a weight in $[-W,W]$, together with $N,k,f,W$; columns are given as lists of their nonzero entries. A query deletes a set of elements and inserts a list of new elements (sparse columns, weights in $[-W,W]$), at most $f$ updates in all.
--   2. **Subset setting.** The instance lists all $m=|E\cup E^\star|$ elements with dense columns, the active set $E$ and the susceptible set $E^\star$ ($m^\star=|E^\star|\ge1$). A query deletes $F\subseteq E\cap E^\star$ and inserts $I\subseteq E^\star\setminus E$, $|F|+|I|\le f$; the updated ground set is $(E\setminus F)\cup I$.
--   3. **Answer.** Word cell $0$ of the query's final memory is $1$ exactly when the objective (a common basis, or a $k$-intersection-packing) exists in the updated matroids; for a weighted objective, word cell $1$ then holds its minimum weight.
--
--   An oracle *solves* a row of a table with bounds $T_P$, $S$, $T_Q$ and error $\varepsilon$ when, for every instance with all size parameters at least $1$ and every word width $w\ge b(\lfloor\log_2(N+m+k+f+W+2)\rfloor+1)$, the preprocessing halts within $T_P$ steps with space at most $S$ on all coins, and every valid query halts within $T_Q$ steps on all coins and is answered wrongly with probability at most $\varepsilon$.
-- source:
--   Choudhary, Kumar, Saggi, Sensitivity Oracles for Matroid Packing, Matroid Covering, and Matching Problems with Applications, arXiv:2609.01283 (held version, sha256 0de50841…), §3.2, pp.17–19 (PDF pp.20–22); Tables 8, 9

import Mathlib
import Definitions.Def_MatroidSensOracle_AlgRAM
import Definitions.Def_MatroidSensOracle_LinearMatroid

set_option autoImplicit false

namespace MatroidSensOracle

/-!
# Matroid sensitivity oracles on the algebraic RAM: general and subset settings

Choudhary, Kumar, Saggi, arXiv:2609.01283 (held version, sha256 0de50841…), §3.2, p.17
(PDF p.20): "Given a query (F, I) (with |F|+|I| ⩽ f), the goal is to decide whether the updated
matroids have a common independent set of size N (i.e. a 1-intersection-packing exists). In the
weighted version, each element has an integer weight w(e) ∈ [−W, W], and the oracle returns the
minimum weight of a common basis of size N, or reports that none exists. In the general sensitivity
setting, we assume that the original and inserted columns of both representations are k-sparse. In
the subset setting, the columns of all susceptible elements are known during preprocessing, and no
sparsity assumption is needed." p.18 (PDF p.21): "In the subset sensitivity setting, all updates are
confined to a set E★ of m★ elements." Table 8: "Here m = |E| in the general setting and
m = |E ∪ E★| in the subset setting."

**Formalization Note.**
* **General setting.** The instance is a list `L` of `m` elements (columns in both representations,
  weight in `[−W, W]`) with every column `spar k`-sparse, together with `N, k, f, W`. Input words:
  `N, m, k, f, W`, then per element its weight, the number and the row indices of the nonzero entries
  of its first column, the same for its second column; input field elements: the nonzero values in
  the same order. A query deletes a set of positions and inserts a list of new elements (sparse
  columns, weight in `[−W, W]`), at most `f` updates in all; its words are the number and the
  positions of the deletions (increasing) and the number and the sparse encodings of the insertions,
  its field elements the values of the inserted columns.
* **Subset setting.** The instance lists every element of `E ∪ E★` (`m` elements), with the active
  set `E` and the susceptible set `E★` (`m★ = |E★| ≥ 1`), columns dense. Input words:
  `N, m, m★, k, f, W`, then per element its weight and two flags (in `E`, in `E★`); field elements:
  the `N` entries of the first column, then of the second, element by element. A query deletes a set
  `F ⊆ E ∩ E★` and inserts a set `I ⊆ E★ \ E` of positions, `|F| + |I| ≤ f`; its words are the
  numbers and the increasing positions. The updated ground set is `(E \ F) ∪ I`.
* **Answer.** Word cell `0` of the final query memory is `1` exactly when the objective is
  feasible; for a weighted objective, when it is feasible, word cell `1` (read signed) is the
  minimum weight.
* All size parameters are at least `1`, so that the printed `O(·)` bounds are positive. The
  programs work for every word width `w ≥ b (⌊log₂(N + m + k + f + W + 2)⌋ + 1)`.
-/

variable {F : Type} [Field F] [DecidableEq F]

/-- The rows of the nonzero entries of `v`, increasing. -/
def sparseRows {N : ℕ} (v : Fin N → F) : List (Fin N) := (List.finRange N).filter fun r => v r ≠ 0

/-- The words of one element in the sparse encoding. -/
def sparseWords {N : ℕ} (x : Elem F N) : List ℤ :=
  [x.wt, ((sparseRows x.a).length : ℤ)] ++ (sparseRows x.a).map (fun r => ((r : ℕ) : ℤ)) ++
    [((sparseRows x.b).length : ℤ)] ++ (sparseRows x.b).map (fun r => ((r : ℕ) : ℤ))

/-- The field elements of one element in the sparse encoding. -/
def sparseFields {N : ℕ} (x : Elem F N) : List F :=
  (sparseRows x.a).map x.a ++ (sparseRows x.b).map x.b

/-- The increasing list of the members of a set of positions. -/
def posList {m : ℕ} (S : Finset (Fin m)) : List ℤ :=
  ((List.finRange m).filter fun e => e ∈ S).map fun e => ((e : ℕ) : ℤ)

/-- General setting, input words. -/
def generalWords {N : ℕ} (k f W : ℕ) (L : List (Elem F N)) : List ℤ :=
  [(N : ℤ), L.length, k, f, W] ++ L.flatMap sparseWords

/-- General setting, input field elements. -/
def generalFields {N : ℕ} (L : List (Elem F N)) : List F := L.flatMap sparseFields

/-- General setting, query words: deletions, then sparse insertions. -/
def generalQueryWords {N : ℕ} {m : ℕ} (del : Finset (Fin m)) (ins : List (Elem F N)) : List ℤ :=
  [(del.card : ℤ)] ++ posList del ++ [(ins.length : ℤ)] ++ ins.flatMap sparseWords

/-- General setting, query field elements. -/
def generalQueryFields {N : ℕ} (ins : List (Elem F N)) : List F := ins.flatMap sparseFields

/-- Subset setting, input words. -/
def subsetWords {N : ℕ} (k f W : ℕ) (L : List (Elem F N)) (Eact Es : Finset (Fin L.length)) :
    List ℤ :=
  [(N : ℤ), L.length, Es.card, k, f, W] ++
    (List.finRange L.length).flatMap fun e =>
      [(L.get e).wt, if e ∈ Eact then 1 else 0, if e ∈ Es then 1 else 0]

/-- Subset setting, input field elements (dense columns). -/
def subsetFields {N : ℕ} (L : List (Elem F N)) : List F :=
  L.flatMap fun x => List.ofFn x.a ++ List.ofFn x.b

/-- Subset setting, query words: deleted positions, then inserted positions. -/
def subsetQueryWords {m : ℕ} (del ins : Finset (Fin m)) : List ℤ :=
  [(del.card : ℤ)] ++ posList del ++ [(ins.card : ℤ)] ++ posList ins

/-- The final query word memory answers the objective: cell `0` is `1` iff it is feasible, and for a
weighted objective cell `1` holds the minimum weight when it is feasible. -/
def Answers {w : ℕ} (feasible : Prop) (minW : WithTop ℤ) (weighted : Bool) (wm : ℤ → BitVec w) :
    Prop :=
  ((wm 0).toNat = 1 ↔ feasible) ∧ (weighted = true → feasible → ((wm 1).toInt : WithTop ℤ) = minW)

variable [Fintype F]

/-- `O` is a sensitivity oracle in the general setting for the objective `prob` (feasibility and
minimum weight of the problem on a ground set, given `N` and the parameter `k`), with columns
`spar k`-sparse, preprocessing time `TP`, space `S` (cells), query time `TQ` and error `err` per fixed
query, all functions of `(N, m, k, f, W)`. -/
def AOracle.SolvesGeneral (O : AOracle) (b : ℕ) (spar : ℕ → ℕ)
    (prob : (N k : ℕ) → List (Elem F N) → Prop × WithTop ℤ) (weighted : Bool)
    (TP S TQ err : ℕ → ℕ → ℕ → ℕ → ℕ → ℝ) : Prop :=
  ∀ (N k f W : ℕ) (L : List (Elem F N)), 1 ≤ N → 1 ≤ L.length → 1 ≤ k → 1 ≤ f → 1 ≤ W →
    (∀ x ∈ L, Sparse (spar k) x.a ∧ Sparse (spar k) x.b ∧ |x.wt| ≤ W) →
    ∀ w : ℕ, b * (Nat.log 2 (N + L.length + k + f + W + 2) + 1) ≤ w →
      O.PrepWithin w (generalWords k f W L) (generalFields L)
          ⌊TP N L.length k f W⌋₊ (S N L.length k f W) ∧
      ∀ (del : Finset (Fin L.length)) (ins : List (Elem F N)), del.card + ins.length ≤ f →
        (∀ x ∈ ins, Sparse (spar k) x.a ∧ Sparse (spar k) x.b ∧ |x.wt| ≤ W) →
        O.QueryWithin w (generalWords k f W L) (generalFields L) (generalQueryWords del ins)
            (generalQueryFields ins) ⌊TP N L.length k f W⌋₊ ⌊TQ N L.length k f W⌋₊ ∧
        O.ErrorAtMost w (generalWords k f W L) (generalFields L) (generalQueryWords del ins)
            (generalQueryFields ins) ⌊TP N L.length k f W⌋₊ ⌊TQ N L.length k f W⌋₊
            (Answers (prob N k (updateList L del ins)).1 (prob N k (updateList L del ins)).2 weighted)
            (err N L.length k f W)

/-- `O` is a sensitivity oracle in the subset setting for the objective `prob`, with preprocessing
time `TP`, space `S` (cells), query time `TQ` and error `err` per fixed query, all functions of
`(N, m, m★, k, f, W)`. -/
def AOracle.SolvesSubset (O : AOracle) (b : ℕ)
    (prob : (N k : ℕ) → List (Elem F N) → Prop × WithTop ℤ) (weighted : Bool)
    (TP S TQ err : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℝ) : Prop :=
  ∀ (N k f W : ℕ) (L : List (Elem F N)) (Eact Es : Finset (Fin L.length)),
    1 ≤ N → 1 ≤ Es.card → 1 ≤ k → 1 ≤ f → 1 ≤ W → Eact ∪ Es = Finset.univ →
    (∀ x ∈ L, |x.wt| ≤ W) →
    ∀ w : ℕ, b * (Nat.log 2 (N + L.length + k + f + W + 2) + 1) ≤ w →
      O.PrepWithin w (subsetWords k f W L Eact Es) (subsetFields L)
          ⌊TP N L.length Es.card k f W⌋₊ (S N L.length Es.card k f W) ∧
      ∀ del ins : Finset (Fin L.length), del ⊆ Eact ∩ Es → ins ⊆ Es \ Eact →
        del.card + ins.card ≤ f →
        O.QueryWithin w (subsetWords k f W L Eact Es) (subsetFields L) (subsetQueryWords del ins) []
            ⌊TP N L.length Es.card k f W⌋₊ ⌊TQ N L.length Es.card k f W⌋₊ ∧
        O.ErrorAtMost w (subsetWords k f W L Eact Es) (subsetFields L) (subsetQueryWords del ins) []
            ⌊TP N L.length Es.card k f W⌋₊ ⌊TQ N L.length Es.card k f W⌋₊
            (Answers (prob N k (subList L ((Eact \ del) ∪ ins))).1
              (prob N k (subList L ((Eact \ del) ∪ ins))).2 weighted)
            (err N L.length Es.card k f W)

end MatroidSensOracle


