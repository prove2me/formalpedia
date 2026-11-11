-- Prove2me | Definitions.Def_FOMCMonDep_treeCode
-- name    : FOMCMonDep_treeCode
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:24:08.894363+00:00
-- url     : https://prove2.me/theorems/b58a0380-c5e9-4cbe-9d12-cc5dac007fba
-- title:
--   Horizon functions $\rho^\pm$, atomic $(k,q)$-types and type trees $\mathrm{tree}^G_{k,q}(\bar a)$
-- statement:
--   Fix the **horizon functions** $\rho^-(k,q)=9^{(k+q+1)q}$ and $\rho^+(k,q)=9^{(k+q)(q+1)}$. Let $G$ be a partial graph, $k,q\in\mathbb N$ and $\bar a=(a_1,\dots,a_\ell)$ a tuple of vertices.
--
--   1. **dist-FO atoms of distance rank $(k,q)$**: equalities, $E$, $N$ and color atoms applied to variables, binary distance atoms $\mathrm{dist}(x_i,x_j)\le r$ with $r\le\rho^-(k,q)$, and unary distance atoms $\mathrm{dist}(x_i,Y)<r$ with $r\le\rho^+(k,q)$.
--   2. The **atomic $(k,q)$-type** $\mathrm{atp}_{k,q}(\bar a)$ is the set of such atoms with free variables among $x_1,\dots,x_\ell$ true of $\bar a$; it is finite.
--   3. The **type tree** is $\mathrm{tree}_{k,q}(\bar a)=(\mathrm{atp}_{k,q}(\bar a),E_{k,q}(\bar a))$ with $E_{k,0}(\bar a)=\emptyset$ and, for $q\ge1$,
--   $$E_{k,q}(\bar a)=\{(i,\mathrm{tree}_{k+1,q-1}(\bar a b)): i\in[\ell],\ b\in V(G),\ \mathrm{dist}(a_i,b)\le\rho^+(k+1,q-1)\}.$$
--   4. Type trees are represented in a **canonical form** (sorted, duplicate-free), and $\|\tau\|$ is the size of the representation, including $k$, $q$ and $\ell$. A family $(\mathrm{tree}^G_{k,q}(a):a\in V(G))$ is input as the codes of the trees in vertex order, each preceded by its length.
--
--   Type trees represent local types compactly: their size is governed by the types realized nearby (Lemma 13.1), and the model checking algorithm maintains them along a construction sequence (Lemmas 12.1, 12.2).
--
--   **Formalization Note** A type tree is identified with its canonical code: $[k,q,\ell]$, the sorted duplicate-free list of atom codes, and the sorted duplicate-free list of extension codes $i::\mathrm{code}(\mu)$, with every list length-prefixed. The code determines the tree, and two tuples have the same type tree iff their codes agree. Variable indices and guards are $0$-based.
-- source:
--   Dreier, Mählmann, Toruńczyk, First-Order Model Checking on Monadically Dependent Graph Classes, STOC 2027 submission (held manuscript, sha256 98040ab52fa9eeb6577af7e100d83ff2a156142fed0a0178723cec8569510454), §10.1–10.2, pp.39–40 (PDF 41–42)

import Mathlib
import Definitions.Def_FOMCMonDep_PartialGraph

set_option autoImplicit false

namespace FOMCMonDep

/-- **Horizon functions (10).** Dreier, Mählmann, Toruńczyk, *First-Order Model Checking on Monadically Dependent Graph Classes*, STOC 2027 submission (held manuscript, sha256 98040ab5…), §10.1, p.39 (PDF 41): "ρ⁻(k, q) := 9^{(k+q+1)q}". -/
def rhoMinus (k q : ℕ) : ℕ := 9 ^ ((k + q + 1) * q)

/-- **Horizon functions (10).** Dreier, Mählmann, Toruńczyk, *First-Order Model Checking on Monadically Dependent Graph Classes*, STOC 2027 submission (held manuscript, sha256 98040ab5…), §10.1, p.39 (PDF 41): "ρ⁺(k, q) := 9^{(k+q)(q+1)}". -/
def rhoPlus (k q : ℕ) : ℕ := 9 ^ ((k + q) * (q + 1))

/-- The canonical form of a finite set of codes (§10.2, p.40: "a canonical (say, sorted, duplicate-free) form"):
duplicates removed, then sorted lexicographically. Two lists with the same elements have the same canonical form. -/
def canon (L : List (List ℤ)) : List (List ℤ) := L.dedup.mergeSort fun x y => decide (x ≤ y)

/-- A list of codes as one word list: the number of codes, then each code preceded by its length (a prefix code). -/
def flat (L : List (List ℤ)) : List ℤ := (L.length : ℤ) :: L.flatMap fun x => (x.length : ℤ) :: x

open Classical in
/-- **The atomic `(k, q)`-type `atp_{k,q}(ā)`, as a list of atom codes.** Dreier, Mählmann, Toruńczyk, *First-Order Model Checking on Monadically Dependent Graph Classes*, STOC 2027 submission (held manuscript, sha256 98040ab5…), §10.1–10.2,
pp.39–40 (PDF 41–42). dist-FO adds "for each radius r ∈ N […] a binary distance atom dist(x, y) ⩽ r" and "for each
radius r ∈ N and color Y, […] a unary distance atom dist(x, Y) < r […] equivalent to ∃y Y(y) ∧ dist(x, y) < r". "A
dist-FO formula has distance rank (k, q) if it is a Boolean combination of • first-order atoms: relational symbols in
the signature or equality, applied to variables, • binary distance atoms with radius r ⩽ ρ⁻(k, q), • unary distance
atoms with radius r ⩽ ρ⁺(k, q), […]". "The atomic (k, q)-type, denoted atp_{k,q}(ā), is the set of all atomic
formulas φ of distance rank (k, q) with free variables among x1, . . . , xℓ, such that G |= φ(ā). Note that this set
is finite, as an atom mentioning a color that does not occur in G is not satisfiable in G."

**Formalization Note.** Variables are `x_i` for `0 ≤ i < ℓ` (the paper's `x_{i+1}`). The atoms and their codes are
`x_i = x_j` ↦ `[0, i, j]`, `E(x_i, x_j)` ↦ `[1, i, j]`, `N(x_i, x_j)` ↦ `[2, i, j]`, `Y(x_i)` ↦ `[3, i, Y]`,
`dist(x_i, x_j) ⩽ r` ↦ `[4, i, j, r]` (`r ≤ ρ⁻(k, q)`), `dist(x_i, Y) < r` ↦ `[5, i, Y, r]` (`r ≤ ρ⁺(k, q)`). The list
contains exactly the codes of the true atoms; colors range over the colors that occur in `G`, since an atom with
any other color is false. Distances are in the graph of resolved pairs. -/
noncomputable def atpCodes {n : ℕ} (G : PartialGraph n) (k q : ℕ) (a : List (Fin n)) : List (List ℤ) :=
  let I := List.finRange a.length
  let cols := ((List.finRange n).map G.color).dedup
  (I.flatMap fun i => I.flatMap fun j =>
      (if a.get i = a.get j then [[0, (i : ℤ), (j : ℤ)]] else []) ++
      (if G.E.Adj (a.get i) (a.get j) then [[1, (i : ℤ), (j : ℤ)]] else []) ++
      (if G.N.Adj (a.get i) (a.get j) then [[2, (i : ℤ), (j : ℤ)]] else []) ++
      ((List.range (rhoMinus k q + 1)).flatMap fun r : ℕ =>
        if G.dist (a.get i) (a.get j) ≤ (r : ℕ∞) then [[4, (i : ℤ), (j : ℤ), (r : ℤ)]] else [])) ++
  (I.flatMap fun i => cols.flatMap fun Y =>
      (if G.color (a.get i) = Y then [[3, (i : ℤ), (Y : ℤ)]] else []) ++
      ((List.range (rhoPlus k q + 1)).flatMap fun r : ℕ =>
        if ∃ y, G.color y = Y ∧ G.dist (a.get i) y < (r : ℕ∞) then [[5, (i : ℤ), (Y : ℤ), (r : ℤ)]] else []))

open Classical in
/-- **Type trees `tree^G_{k,q}(ā)`, in their canonical representation.** Dreier, Mählmann, Toruńczyk, *First-Order Model Checking on Monadically Dependent Graph Classes*, STOC 2027 submission (held manuscript, sha256 98040ab5…), §10.2, p.40
(PDF 42): "let G be a partial graph, k, q ∈ N, and ā ∈ V(G)^{⩽k}, and put ℓ := |ā|. […] Define the (k, q)-type tree of
ā as tree_{k,q}(ā) := (atp_{k,q}(ā), E_{k,q}(ā)) where E_{k,q}(ā) = ∅ if q = 0, and otherwise E_{k,q}(ā) :=
{(i, tree_{k+1,q−1}(āb)) : i ∈ [ℓ], b ∈ V(G), dist(a_i, b) ⩽ ρ⁺(k + 1, q − 1)}." "Representation. Type trees are
represented in the standard RAM model in a canonical (say, sorted, duplicate-free) form, so that equality of two type
trees τ1, τ2 can be tested in time O(∥τ1∥ + ∥τ2∥). By ∥τ∥ we denote the size of this representation (which includes
k, q, and ℓ)."

**Formalization Note.** The type tree is identified with its canonical code: `[k, q, ℓ]`, then the root label (the
canonical list of atom codes), then the canonical list of the extensions `(i, μ)`, each coded `i :: code(μ)`. Lists
of codes are written with `flat` (count, then length-prefixed codes), so the code is prefix-free and determines the
tree; two tuples have the same type tree iff they have the same code, which is how the type trees are compared and
counted. The guard `i` is `0`-based (the paper's `i + 1`). The argument order is `q`, then `k`. -/
noncomputable def treeCode {n : ℕ} (G : PartialGraph n) : (q k : ℕ) → List (Fin n) → List ℤ
  | 0, k, a => [(k : ℤ), 0, (a.length : ℤ)] ++ flat (canon (atpCodes G k 0 a)) ++ flat []
  | q + 1, k, a => [(k : ℤ), ((q + 1 : ℕ) : ℤ), (a.length : ℤ)] ++ flat (canon (atpCodes G k (q + 1) a)) ++
      flat (canon ((List.finRange a.length).flatMap fun i => (List.finRange n).flatMap fun b =>
        if G.dist (a.get i) b ≤ (rhoPlus (k + 1) q : ℕ∞) then [((i : ℕ) : ℤ) :: treeCode G q (k + 1) (a ++ [b])]
        else []))

/-- **The size `∥τ∥`** of a type tree: the length of its canonical representation (which includes `k`, `q`, `ℓ`). -/
noncomputable def treeSize {n : ℕ} (G : PartialGraph n) (k q : ℕ) (a : List (Fin n)) : ℕ :=
  (treeCode G q k a).length

/-- **The family `(tree^G_{k,q}(a) : a ∈ V(G))` as an input or output**: for `a = 0, 1, …, n − 1` in order, the length
of the code of `tree^G_{k,q}(a)` followed by the code. -/
noncomputable def treesCode {n : ℕ} (G : PartialGraph n) (k q : ℕ) : List ℤ :=
  (List.finRange n).flatMap fun a => ((treeCode G q k [a]).length : ℤ) :: treeCode G q k [a]

end FOMCMonDep


