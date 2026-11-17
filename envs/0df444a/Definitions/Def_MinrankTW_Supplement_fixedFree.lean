-- Prove2me | Definitions.Def_MinrankTW_Supplement_fixedFree
-- name    : MinrankTW_Supplement_fixedFree
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T13:03:42.937632+00:00
-- url     : https://prove2.me/theorems/ffd305dc-7a71-4d5c-af7d-497e13afbdff
-- title:
--   Fixed/free matrices
-- statement:
--   A **fixed/free matrix** over a finite field $\mathbb F$ is an $m\times n$ array whose every entry is either *fixed* to a prescribed value $a\in\mathbb F$ (possibly $0$) or *free* (unrestricted). As independent entry constraints it is the family
--   $$
--   S_{ij}=\begin{cases}\{a\}&\text{if entry }(i,j)\text{ is fixed to }a,\\ \mathbb F&\text{if entry }(i,j)\text{ is free,}\end{cases}
--   $$
--   so a completion assigns an arbitrary value to every free entry and keeps the fixed ones. Its bipartite support graph has an edge $r_ic_j$ for every free entry and every fixed nonzero entry.
--
--   Fixed/free matrices are the instances of the circuit encoding (Theorem 5) and of the conditional lower bound (Theorem 6).
--
--   **Formalization Note** The table is `Fin m → Fin n → Option F` (`some a` fixed, `none` free); `fixedFree` turns it into allowed sets for the published `IsCompletion` and `supportGraph`. A RAM writes an entry as the code $e(a)$ when fixed and $q=|\mathbb F|$ when free.
-- source:
--   Perles–Weinstein, Efficient Algorithms for Minrank and Index Coding for Low-Treewidth Graphs, STOC 2027 submission (manuscript sha256 32a91384…), §B, pp.17–20 (fixed/free matrices), Theorems 5 and 6

import Mathlib

namespace MinrankTW.Supplement

/-- The entry constraints of a **fixed/free matrix** (Perles–Weinstein, *Efficient Algorithms for
Minrank and Index Coding for Low-Treewidth Graphs*, STOC 2027 submission manuscript (sha256
32a91384…c57991), §B, pp. 17–20: "a square fixed/free matrix", "an n × n matrix whose entries are
each fixed or unrestricted"). The table `A i j` is `some a` for an entry fixed to the value `a`
(possibly `0`) and `none` for a free (unrestricted) entry; the allowed set is `{a}` or all of `F`.

**Formalization Note** The allowed sets are in the format of the published `MinrankTW.IsCompletion`
and `MinrankTW.supportGraph`. `ffCode e` is the numeric code of an entry of the table written by a
RAM: `e(a)` for a fixed entry `a` and `q = |F|` for a free one. -/
def fixedFree {F : Type*} [Fintype F] {m n : ℕ} (A : Fin m → Fin n → Option F) :
    Fin m → Fin n → Finset F :=
  fun i j => match A i j with
    | some a => {a}
    | none => Finset.univ

/-- The RAM code of an entry of a fixed/free table: `e(a)` for a fixed entry `a`, `q = |F|` for a
free entry. -/
def ffCode {F : Type*} [Fintype F] (e : F ≃ Fin (Fintype.card F)) : Option F → ℕ
  | some a => (e a : ℕ)
  | none => Fintype.card F

end MinrankTW.Supplement


