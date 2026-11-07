-- Prove2me | Definitions.Def_MatroidSensOracle_LinearMatroid
-- name    : MatroidSensOracle_LinearMatroid
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:48:27.6719+00:00
-- url     : https://prove2.me/theorems/9e091acc-47a4-406e-903c-8576f3b396b9
-- title:
--   Linear matroids from columns, sparse columns, common bases, $k$-intersection-packings, $k$-fold unions and strongly base-orderable matroids
-- statement:
--   Let $\mathbb F$ be a field and $A\in\mathbb F^{N\times m}$. A set $S$ of columns is **independent** when the columns $A_{\cdot,e}$, $e\in S$, are linearly independent (Definition 2.9); $A_S$ denotes the $|S|\times|S|$ submatrix of the columns of $S$. A column is **$c$-sparse** if it has at most $c$ nonzero entries (Definition 2.10).
--
--   For two rank-$N$ matroids represented by $A$ and $B$, a **common basis** is an $N$-set independent in both. A ground set is modelled as a list of elements, each with its column in each representation and an integer weight.
--   1. The two matroids have a common basis of size $N$, and its minimum weight $\sum_{e\in S}w(e)$ is taken over all common bases.
--   2. A **$k$-intersection-packing** is a set $S$ that splits into $k$ disjoint $N$-sets independent in the first representation and also, possibly differently, into $k$ such sets for the second (p.20). Its minimum weight is defined likewise.
--   3. The **$k$-fold union** $M^{\vee k}$ has as independent sets the $S$ that split into $k$ disjoint independent sets, and $A^{\vee k}=(AD_1;\dots;AD_k)$ for diagonal matrices $D_i$.
--
--   A matroid is **strongly base-orderable** (Definition 2.11) if for any two bases $B_1,B_2$ there is a bijection $\pi:B_1\to B_2$ such that for every $X\subseteq B_1$ both $(B_1\setminus X)\cup\pi(X)$ and $(B_2\setminus\pi(X))\cup X$ are bases.
--
--   **Formalization Note** Partitions into $k$ parts allow empty parts. Updated ground sets delete positions and append inserted elements.
-- source:
--   Choudhary, Kumar, Saggi, Sensitivity Oracles for Matroid Packing, Matroid Covering, and Matching Problems with Applications, arXiv:2609.01283 (held version, sha256 0de50841…), §2, pp.13–14 (PDF pp.16–17), Definitions 2.9–2.11; §3.2–3.3, pp.17–20 (PDF pp.20–23)

import Mathlib

set_option autoImplicit false

namespace MatroidSensOracle

/-!
# Linear matroids from columns, common bases, `k`-intersection-packings, `k`-fold unions, SBO

Choudhary, Kumar, Saggi, arXiv:2609.01283 (held version, sha256 0de50841…), §2, pp.12–14
(PDF pp.15–17) and §3.2–3.3, pp.17–21 (PDF pp.20–24).
* Definition 2.9 (p.13): "A matroid M = (E, ℐ) on a ground set E of size m is said to be linear if
  there exists a d × m matrix A over F such that S ⊆ E is independent iff the sub-matrix A_S (columns
  of A indexed by S) has full column rank in F."
* Definition 2.10 (p.13): "c-sparse […] every column of A contains at most c non-zero entries."
* Definition 2.11 (p.14): "A matroid M on E is strongly base-orderable (SBO) if, for any two bases B1
  and B2 of M, there exists a bijection π : B1 → B2 such that for every X ⊆ B1, both (B1 \ X) ∪ π(X)
  and (B2 \ π(X)) ∪ X are bases of M."
* p.20: "the k-fold union of M, denoted by M^{∨k} = (E, ℐ^{∨k}), is the matroid whose independent sets
  are all subsets S ⊆ E that admit a partition S = S1 ⊎ · · · ⊎ Sk such that Si ∈ ℐ for each i ∈ [k]";
  "a k-intersection-packing is a set of kN elements that can be partitioned into k bases of M1 and
  also into k bases of M2, where, the two partitions may differ."

**Formalization Note.**
* A set `S` of columns of `A ∈ F^{N×m}` is independent when the columns `A_{·,e}`, `e ∈ S`, are
  linearly independent (full column rank).
* For two rank-`N` matroids a common basis is an `N`-set independent in both; `IsCommonBasisM` says
  exactly this, so it equals `ℬ(M1) ∩ ℬ(M2)` in the paper's setting (rank `N`).
* An element of a pair of matroids (`Elem`) carries its column in each representation and its integer
  weight; a ground set is a list of elements (repetitions are distinct elements). Its common bases
  are the `N`-sets of positions independent in both representations; a `k`-intersection-packing is a
  set `S` of positions that splits into `k` disjoint `N`-sets independent in the first representation
  and also (possibly differently) into `k` such sets for the second. A set of `N` independent columns
  of a rank-`N` matroid is a basis, so these are the paper's notions.
* Partitions into `k` parts allow empty parts (the empty set is independent).
-/

/-- The `r × r` submatrix `A_S` of the columns in `S` (`|S| = r`), in increasing order. -/
def colSub {R : Type*} {r m : ℕ} (A : Matrix (Fin r) (Fin m) R) (S : Finset (Fin m))
    (h : S.card = r) : Matrix (Fin r) (Fin r) R :=
  A.submatrix id fun i => S.orderEmbOfFin h i

/-- The columns of `A` indexed by `S` are linearly independent (`A_S` has full column rank); the rows
may be indexed by any type. -/
def ColIndep {F ι : Type*} [Field F] {m : ℕ} (A : Matrix ι (Fin m) F) (S : Finset (Fin m)) :
    Prop :=
  LinearIndependent F fun e : S => fun r => A r e

/-- `S` is a common basis of the rank-`N` linear matroids represented by `A` and `B`. -/
def IsCommonBasisM {F : Type*} [Field F] {N m : ℕ} (A B : Matrix (Fin N) (Fin m) F)
    (S : Finset (Fin m)) : Prop :=
  S.card = N ∧ ColIndep A S ∧ ColIndep B S

open Classical in
/-- The minimum weight `∑_{e ∈ S} wt(e)` of a common basis (`⊤` if there is none). -/
noncomputable def minCommonBasisWeightM {F : Type*} [Field F] {N m : ℕ}
    (A B : Matrix (Fin N) (Fin m) F) (wt : Fin m → ℤ) : WithTop ℤ :=
  (Finset.univ.filter fun S => IsCommonBasisM A B S).inf fun S => ((∑ e ∈ S, wt e : ℤ) : WithTop ℤ)

open Classical in
/-- The vector `v` has at most `c` nonzero entries. -/
def Sparse {F : Type*} [Field F] {N : ℕ} (c : ℕ) (v : Fin N → F) : Prop :=
  (Finset.univ.filter fun r => v r ≠ 0).card ≤ c

/-- A ground-set element of two linear matroids of rank `N`: its columns `a`, `b` and its weight. -/
structure Elem (F : Type*) (N : ℕ) where
  a : Fin N → F
  b : Fin N → F
  wt : ℤ

/-- `S` splits into `k` pairwise disjoint parts, each satisfying `P`. -/
def SplitsInto {α : Type*} [DecidableEq α] (P : Finset α → Prop) (k : ℕ) (S : Finset α) : Prop :=
  ∃ Q : Fin k → Finset α, (∀ i, P (Q i)) ∧ (∀ i j, i ≠ j → Disjoint (Q i) (Q j)) ∧
    Finset.univ.biUnion Q = S

section Elem

variable {F : Type*} [Field F] {N : ℕ}

/-- The positions `S` of `L` have linearly independent first columns. -/
def IndepA (L : List (Elem F N)) (S : Finset (Fin L.length)) : Prop :=
  LinearIndependent F fun e : S => (L.get e).a

/-- The positions `S` of `L` have linearly independent second columns. -/
def IndepB (L : List (Elem F N)) (S : Finset (Fin L.length)) : Prop :=
  LinearIndependent F fun e : S => (L.get e).b

/-- The weight of a set of positions. -/
def weight (L : List (Elem F N)) (S : Finset (Fin L.length)) : ℤ := ∑ e ∈ S, (L.get e).wt

/-- `S` is a common basis (of size `N`) of the two matroids on the ground set `L`. -/
def IsCommonBasis (L : List (Elem F N)) (S : Finset (Fin L.length)) : Prop :=
  S.card = N ∧ IndepA L S ∧ IndepB L S

/-- The two matroids on `L` have a common basis of size `N`. -/
def HasCommonBasis (L : List (Elem F N)) : Prop := ∃ S, IsCommonBasis L S

open Classical in
/-- The minimum weight of a common basis of size `N` (`⊤` if there is none). -/
noncomputable def minCommonBasisWeight (L : List (Elem F N)) : WithTop ℤ :=
  (Finset.univ.filter fun S => IsCommonBasis L S).inf fun S => ((weight L S : ℤ) : WithTop ℤ)

/-- `S` is a `k`-intersection-packing of the two matroids on `L`: it splits into `k` bases of the
first matroid and, possibly differently, into `k` bases of the second (bases have `N` elements). -/
def IsKPacking (L : List (Elem F N)) (k : ℕ) (S : Finset (Fin L.length)) : Prop :=
  SplitsInto (fun X => X.card = N ∧ IndepA L X) k S ∧ SplitsInto (fun X => X.card = N ∧ IndepB L X) k S

/-- The two matroids on `L` have a `k`-intersection-packing. -/
def HasKPacking (L : List (Elem F N)) (k : ℕ) : Prop := ∃ S, IsKPacking L k S

open Classical in
/-- The minimum weight of a `k`-intersection-packing (`⊤` if there is none). -/
noncomputable def minKPackingWeight (L : List (Elem F N)) (k : ℕ) : WithTop ℤ :=
  (Finset.univ.filter fun S => IsKPacking L k S).inf fun S => ((weight L S : ℤ) : WithTop ℤ)

/-- The ground set after deleting the positions `del` of `L` and inserting the elements `ins`:
the remaining elements in order, then `ins`. -/
def updateList (L : List (Elem F N)) (del : Finset (Fin L.length)) (ins : List (Elem F N)) :
    List (Elem F N) :=
  (((List.finRange L.length).filter fun e => e ∉ del).map L.get) ++ ins

/-- The sub-ground-set of the positions in `S`, in order. -/
def subList (L : List (Elem F N)) (S : Finset (Fin L.length)) : List (Elem F N) :=
  ((List.finRange L.length).filter fun e => e ∈ S).map L.get

end Elem

/-- `S` is independent in the `k`-fold union of the linear matroid of `A`: it splits into `k`
disjoint sets of linearly independent columns. -/
def UnionIndep {F : Type*} [Field F] {N m : ℕ} (A : Matrix (Fin N) (Fin m) F) (k : ℕ)
    (S : Finset (Fin m)) : Prop :=
  SplitsInto (ColIndep A) k S

/-- The block matrix `A^{∨k} = (A D₁; …; A D_k)`, rows indexed by `(i, r)` (block `i`, row `r`), for
the diagonals `D i` of the matrices `D_i`. -/
def unionRep {F : Type*} [Field F] {N m k : ℕ} (A : Matrix (Fin N) (Fin m) F) (D : Fin k → Fin m → F) :
    Matrix (Fin k × Fin N) (Fin m) F :=
  fun p e => A p.2 e * D p.1 e

/-- The matroid `M` is strongly base-orderable (Definition 2.11). -/
def IsSBO {α : Type*} (M : Matroid α) : Prop :=
  ∀ B₁ B₂ : Set α, M.IsBase B₁ → M.IsBase B₂ → ∃ π : α → α, Set.BijOn π B₁ B₂ ∧
    ∀ X ⊆ B₁, M.IsBase ((B₁ \ X) ∪ π '' X) ∧ M.IsBase ((B₂ \ π '' X) ∪ X)

/-- `S` can be partitioned into `k` (possibly empty) pairwise disjoint sets, each satisfying `P`. -/
def SetPartitionsInto {α : Type*} (P : Set α → Prop) (k : ℕ) (S : Set α) : Prop :=
  ∃ Q : Fin k → Set α, (∀ i, P (Q i)) ∧ (∀ i j, i ≠ j → Disjoint (Q i) (Q j)) ∧ (⋃ i, Q i) = S

end MatroidSensOracle


