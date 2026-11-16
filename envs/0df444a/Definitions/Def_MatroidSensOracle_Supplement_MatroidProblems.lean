-- Prove2me | Definitions.Def_MatroidSensOracle_Supplement_MatroidProblems
-- name    : MatroidSensOracle_Supplement_MatroidProblems
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:04:55.225086+00:00
-- url     : https://prove2.me/theorems/b95d5ed9-6351-4023-ae3d-1c2d89718d8c
-- title:
--   Single-matroid bases, $k$-packings, $k$-coverings, parity bases and oracles with instance restrictions
-- statement:
--   For a ground set given as a list of the base mission's elements (two columns in $\mathbb F^N$ and an integer weight):
--
--   1. A *single* matroid uses only the first column; such an element has second column $0$ and weight $0$.
--   2. The first columns *contain a basis* if some $N$ of them are linearly independent (rank $N$).
--   3. A *$k$-packing* is a set of elements that splits into $k$ pairwise disjoint bases (p.21).
--   4. The ground set is *$k$-coverable* if it splits into $k$ independent sets (p.22).
--   5. For **pairs** (§7, p.36), the two columns of an element are the pair's columns. A *parity basis* is a set of $N/2$ pairs whose $N$ columns are linearly independent. A *$k$-parity basis* is a set of $kN/2$ pairs whose $kN$ columns split into $k$ bases; the two columns of a pair may go to different bases (p.38). Minimum weights lie in $\mathbb Z\cup\{+\infty\}$.
--
--   The oracle predicates *SolvesGeneralOn* and *SolvesSubsetOn* are the base mission's general and subset matroid-oracle semantics on the algebraic RAM. They add an admissibility condition on instances (for standing hypotheses such as "rank $N$" or "$m\le kN$"), a condition on inserted elements, and a deletions-only flag; with the base conditions they coincide with the base predicates.
-- source:
--   Choudhary, Kumar, Saggi, Sensitivity Oracles for Matroid Packing, Matroid Covering, and Matching Problems with Applications, arXiv:2609.01283 (held version, sha256 0de50841…), §3.1 p.14, §3.3 pp.21–22, §7 pp.36–38 (PDF pp.17, 24–25, 39–41)

import Mathlib
import Definitions.Def_MatroidSensOracle_MatroidOracle

set_option autoImplicit false

namespace MatroidSensOracle.Supplement

/-!
# Single-matroid bases, `k`-packings, `k`-coverings, parity bases, and oracles with instance restrictions

Choudhary, Kumar, Saggi, *Sensitivity Oracles for Matroid Packing, Matroid Covering, and Matching
Problems with Applications*, arXiv:2609.01283 (held version, sha256 0de50841…).
* §3.1, p.14 (PDF p.17): "Let M = (E, ℐ) be a rank-N linear matroid on m elements, represented by a
  matrix A ∈ F^{N×m}. Given an update query (F, I) […] the basis sensitivity oracle (a.k.a. 1-packing
  problem) asks whether the updated column set contains a basis of rank N. […] we allow the original
  columns of A to have arbitrary density and assume that each inserted column is k-sparse."
* p.1 and §3.3, p.21 (PDF p.24): a `k`-packing is a set of `kN` elements partitioned into `k` bases of
  `M`. p.22 (PDF p.25): "The k-covering problem asks whether the entire ground set E can be covered by
  (partitioned into) k independent sets of M."
* §7.1, p.36 (PDF p.39): "Let M be a linear matroid of even rank N over F. Its ground elements are
  partitioned into m pairs indexed by E, with representation columns a_e, b_e ∈ F^N for each e ∈ E. A
  parity basis consists of N/2 pairs whose N columns form a basis of M. […] For integer pair weights
  wt(e) ∈ [−W, W], the weighted oracle returns the minimum total weight of a parity basis."
* §7.2, p.38 (PDF p.41): "For k-parity, we seek kN/2 pairs whose kN elements can be partitioned into
  k bases of M. The two elements of a selected pair may belong to different bases."

**Formalization Note.**
* A ground set is a list of the base mission's elements `Elem F N` (repetitions are distinct
  elements). For a **single** matroid only the first column `a` is used; such an instance is encoded
  with second column `0` and weight `0` (`IsSingle`), so that the base encodings `generalWords`,
  `subsetWords` apply unchanged. For **pairs** (§7), an element is a pair: its two columns are `a`
  and `b`, its weight is `wt`.
* A basis of a rank-`N` matroid on `N` rows is a set of `N` linearly independent columns; "rank `N`"
  of a column family is the existence of `N` linearly independent columns (`HasBasisA`,
  `PairRankFull`).
* Partitions into `k` parts allow empty parts (the empty set is independent), as in the base.
* `AOracle.SolvesGeneralOn` / `AOracle.SolvesSubsetOn` are the base `SolvesGeneral` / `SolvesSubset`
  with three additions: an instance restriction `adm` (which carries the sparsity of the original
  columns and the theorem's standing hypotheses such as "rank `N`", "`m ⩽ kN`", "`kN` even"), a
  restriction `insOK` on inserted elements, and a flag `delOnly` for the deletions-only setting.
  With `adm` = "columns `spar k`-sparse, weights in `[−W, W]`", `insOK` the same and
  `delOnly = false`, `SolvesGeneralOn` is exactly the base `SolvesGeneral`.
-/

variable {F : Type} [Field F]

section Problems

variable {N : ℕ}

/-- The element is a single-matroid column: second column `0`, weight `0`. -/
def IsSingle (x : Elem F N) : Prop := x.b = 0 ∧ x.wt = 0

/-- The first columns of `L` contain a basis: `N` linearly independent columns (rank `N`). -/
def HasBasisA (L : List (Elem F N)) : Prop :=
  ∃ S : Finset (Fin L.length), S.card = N ∧ IndepA L S

/-- The single matroid of the first columns of `L` has a `k`-packing: a set of elements that splits
into `k` pairwise disjoint bases (each `N` independent columns). -/
def HasKPackingA (L : List (Elem F N)) (k : ℕ) : Prop :=
  ∃ S : Finset (Fin L.length), SplitsInto (fun X => X.card = N ∧ IndepA L X) k S

/-- The whole ground set `L` splits into `k` independent sets of the matroid of first columns. -/
def KCoverable (L : List (Elem F N)) (k : ℕ) : Prop :=
  SplitsInto (IndepA L) k Finset.univ

/-- The column of the element `(e, false)` (first column) or `(e, true)` (second column) of a pair. -/
def pairCol (L : List (Elem F N)) (p : Fin L.length × Bool) : Fin N → F :=
  if p.2 then (L.get p.1).b else (L.get p.1).a

/-- The `2m` columns of the pairs of `L` have rank `N`: some `N` of them are linearly independent. -/
def PairRankFull (L : List (Elem F N)) : Prop :=
  ∃ X : Finset (Fin L.length × Bool), X.card = N ∧ LinearIndependent F fun x : X => pairCol L x.1

/-- `S` is a parity basis: `|S| = N/2` pairs whose `N` columns are linearly independent. -/
def IsParityBasis (L : List (Elem F N)) (S : Finset (Fin L.length)) : Prop :=
  2 * S.card = N ∧
    LinearIndependent F fun x : (S ×ˢ (Finset.univ : Finset Bool) : Finset (Fin L.length × Bool)) =>
      pairCol L x.1

open Classical in
/-- The minimum weight of a parity basis (`⊤` if there is none). -/
noncomputable def minParityWeight (L : List (Elem F N)) : WithTop ℤ :=
  (Finset.univ.filter fun S => IsParityBasis L S).inf fun S => ((weight L S : ℤ) : WithTop ℤ)

/-- `S` is a `k`-parity basis: `|S| = kN/2` pairs whose `kN` elements split into `k` bases (`N`
independent columns each); the two elements of a pair may go to different bases. -/
def IsKParityBasis (L : List (Elem F N)) (k : ℕ) (S : Finset (Fin L.length)) : Prop :=
  2 * S.card = k * N ∧
    SplitsInto (fun X : Finset (Fin L.length × Bool) =>
        X.card = N ∧ LinearIndependent F fun x : X => pairCol L x.1) k
      (S ×ˢ (Finset.univ : Finset Bool))

open Classical in
/-- The minimum weight of a `k`-parity basis (`⊤` if there is none). -/
noncomputable def minKParityWeight (L : List (Elem F N)) (k : ℕ) : WithTop ℤ :=
  (Finset.univ.filter fun S => IsKParityBasis L k S).inf fun S => ((weight L S : ℤ) : WithTop ℤ)

end Problems

variable [DecidableEq F] [Fintype F]

/-- `O` is a sensitivity oracle in the general setting (base `SolvesGeneral` encodings) for the
objective `prob`, on the instances satisfying `adm N k W L`, for queries of at most `f` updates
whose inserted elements satisfy `insOK N k W`, with no insertions if `delOnly`. Preprocessing time
`TP`, space `S` (cells), query time `TQ` and error `err` per fixed query are functions of
`(N, m, k, f, W)`. -/
def _root_.MatroidSensOracle.AOracle.SolvesGeneralOn (O : AOracle) (b : ℕ)
    (adm : (N k W : ℕ) → List (Elem F N) → Prop) (insOK : (N k W : ℕ) → Elem F N → Prop)
    (delOnly : Bool)
    (prob : (N k : ℕ) → List (Elem F N) → Prop × WithTop ℤ) (weighted : Bool)
    (TP S TQ err : ℕ → ℕ → ℕ → ℕ → ℕ → ℝ) : Prop :=
  ∀ (N k f W : ℕ) (L : List (Elem F N)), 1 ≤ N → 1 ≤ L.length → 1 ≤ k → 1 ≤ f → 1 ≤ W →
    adm N k W L →
    ∀ w : ℕ, b * (Nat.log 2 (N + L.length + k + f + W + 2) + 1) ≤ w →
      O.PrepWithin w (generalWords k f W L) (generalFields L)
          ⌊TP N L.length k f W⌋₊ (S N L.length k f W) ∧
      ∀ (del : Finset (Fin L.length)) (ins : List (Elem F N)), del.card + ins.length ≤ f →
        (delOnly = true → ins = []) → (∀ x ∈ ins, insOK N k W x) →
        O.QueryWithin w (generalWords k f W L) (generalFields L) (generalQueryWords del ins)
            (generalQueryFields ins) ⌊TP N L.length k f W⌋₊ ⌊TQ N L.length k f W⌋₊ ∧
        O.ErrorAtMost w (generalWords k f W L) (generalFields L) (generalQueryWords del ins)
            (generalQueryFields ins) ⌊TP N L.length k f W⌋₊ ⌊TQ N L.length k f W⌋₊
            (Answers (prob N k (updateList L del ins)).1 (prob N k (updateList L del ins)).2 weighted)
            (err N L.length k f W)

/-- `O` is a sensitivity oracle in the subset setting (base `SolvesSubset` encodings: ground set
`E ∪ E★` listed in `L`, active set `Eact`, susceptible set `Es`) for the objective `prob`, on the
instances satisfying `adm N k W L Eact Es`. Resources are functions of `(N, m, m★, k, f, W)`. -/
def _root_.MatroidSensOracle.AOracle.SolvesSubsetOn (O : AOracle) (b : ℕ)
    (adm : (N k W : ℕ) → (L : List (Elem F N)) → Finset (Fin L.length) → Finset (Fin L.length) → Prop)
    (prob : (N k : ℕ) → List (Elem F N) → Prop × WithTop ℤ) (weighted : Bool)
    (TP S TQ err : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℝ) : Prop :=
  ∀ (N k f W : ℕ) (L : List (Elem F N)) (Eact Es : Finset (Fin L.length)),
    1 ≤ N → 1 ≤ Es.card → 1 ≤ k → 1 ≤ f → 1 ≤ W → Eact ∪ Es = Finset.univ →
    (∀ x ∈ L, |x.wt| ≤ W) → adm N k W L Eact Es →
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

end MatroidSensOracle.Supplement


