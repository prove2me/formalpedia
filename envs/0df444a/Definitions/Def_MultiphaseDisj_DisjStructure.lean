-- Prove2me | Definitions.Def_MultiphaseDisj_DisjStructure
-- name    : MultiphaseDisj_DisjStructure
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:28:19.457059+00:00
-- url     : https://prove2.me/theorems/f068caa1-53ed-4855-93f1-a1a35497cab4
-- title:
--   Randomized cell-probe data structure for insert-only multiphase Disjointness
-- statement:
--   **Insert-only multiphase Disjointness** (Problem 1) has three phases over the universe $[n]$:
--
--   1. Phase I: query sets $S_1,\dots,S_m\subseteq[n]$ arrive and are preprocessed arbitrarily, without charge;
--   2. Phase II: elements are inserted one at a time into a set $X\subseteq[n]$, initially empty;
--   3. Phase III: an index $q\in[m]$ arrives and the structure reports whether $S_q\cap X=\emptyset$, without writing.
--
--   A **randomized structure** with $w$-bit cells and a random tape $\omega$ consists of a preprocessing map $\omega,\vec S\mapsto M_0$ (an arbitrary memory), an insertion program $\mathrm{upd}(\omega,x)$ for every element $x$, and a read-only query program $\mathrm{qry}(\omega,q)$ for every index $q$. The memory after Phase I and the insertions $x_1,\dots,x_k$ is obtained by running $\mathrm{upd}(\omega,x_1),\dots,\mathrm{upd}(\omega,x_k)$ in order starting from $M_0$.
--
--   The tape is drawn once, independently of the input, and shared by all operations.
--
--   **Formalization Note** Only the preprocessing sees the query sets: an insertion sees only the tape, its element and the memory, and a query only the tape, its index and the memory, so all input-dependent information retained between operations resides in memory (§2.1). $[n]$ and $[m]$ are `Fin n`, `Fin m` (0-based); a query's answer `true` means "disjoint".
-- source:
--   Ko, Unconditional Boolean Dynamic Lower Bounds from Disjointness, arXiv:2610.10904 (held version, sha256 ba26649b…), Problem 1, p.5; §2.1 Cell-probe conventions, p.11

import Mathlib
import Definitions.Def_MultiphaseDisj_CellProbe

set_option autoImplicit false

namespace MultiphaseDisj

/-- A randomized cell-probe data structure for **insert-only multiphase Disjointness**
(Ko, *Unconditional Boolean Dynamic Lower Bounds from Disjointness*, arXiv:2610.10904,
held version sha256 ba26649b…, Problem 1, p.5, and §2.1, p.11), with universe `[n]`, `m` query
sets, word size `w`, and random tape `ω : Ω`:

* Phase I: `pre ω S` is the memory built from the query sets `S : Fin m → Finset (Fin n)`
  (arbitrary, uncharged preprocessing);
* Phase II: inserting the element `x` runs the program `upd ω x` on the current memory;
* Phase III: query `q` runs the read-only program `qry ω q`, whose answer is `true` for
  "`S q ∩ X = ∅`".

**Formalization Note** Only `pre` sees the query sets. An insertion sees only the tape, its
element and the memory, and a query only the tape, its index and the memory: all
input-dependent information retained between operations resides in memory (§2.1). The tape is
drawn once and shared by all operations. `[n]` and `[m]` are `Fin n`, `Fin m` (0-based). -/
structure DisjStructure (n m w : ℕ) (Ω : Type*) where
  pre : Ω → (Fin m → Finset (Fin n)) → Mem w
  upd : Ω → Fin n → Prog w Unit
  qry : Ω → Fin m → QProg w Bool

namespace DisjStructure

variable {n m w : ℕ} {Ω : Type*}

/-- The memory after Phase I on the query sets `S` and the insertions of the list `L`, in order,
with tape `ω`. -/
def memAfter (D : DisjStructure n m w Ω) (ω : Ω) (S : Fin m → Finset (Fin n))
    (L : List (Fin n)) : Mem w :=
  L.foldl (fun M x => ((D.upd ω x).run M).2) (D.pre ω S)

end DisjStructure

end MultiphaseDisj


