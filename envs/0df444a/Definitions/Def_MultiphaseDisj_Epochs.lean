-- Prove2me | Definitions.Def_MultiphaseDisj_Epochs
-- name    : MultiphaseDisj_Epochs
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:30:28.538114+00:00
-- url     : https://prove2.me/theorems/8a3087b0-8d91-4397-b014-04d690ac7a7b
-- title:
--   Epoch bookkeeping: $M_{>i}$, the cells $C_j$ last written in epoch $j$, $T(q)$, $t_j(q)$, $\tau_j$ and Merlin's message $U$
-- statement:
--   Let $\mathcal D$ be a deterministic structure (the random tape fixed) run on query sets $\vec S$ and on the insertions of the hard distribution, epoch $\ell$ first and epoch $1$ last.
--
--   1. $M_{>i}$ is the memory after Phase I and epochs $\ell,\dots,i+1$; $M_{>0}$ is the final memory, after Phase II.
--   2. $C_j$ is the set of cells **last written in epoch $j$**: written during epoch $j$ and in none of the later epochs $1,\dots,j-1$. The sets $C_1,\dots,C_\ell$ are pairwise disjoint, and $C_{<j}=\bigcup_{j'<j}C_{j'}$ is the set of cells written after epoch $j$.
--   3. $T(q)$ is the number of cells read by query $q$ on the final memory, $t_j(q)$ the number of distinct cells of $C_j$ that it reads, and
--   $$
--   \tau_j=\mathbb E_{\mathcal D,Q}\big[t_j(Q)\big].
--   $$
--   4. **Merlin's message** $U$ for epoch $i$ consists of two lists: the cells of $C_i$ and the cells of $C_{<i}$, each with its final content.
--
--   **Formalization Note** A deterministic structure is a structure whose tape type has one element. Each of Merlin's lists is the finite set of (address, final content) pairs; the order of a list carries no information.
-- source:
--   Ko, Unconditional Boolean Dynamic Lower Bounds from Disjointness, arXiv:2610.10904 (held version, sha256 ba26649b…), §3.1 Setup and Epochs, p.16; §3.2, p.17 (U)

import Mathlib
import Definitions.Def_MultiphaseDisj_ZeroError
import Definitions.Def_MultiphaseDisj_HardDist

set_option autoImplicit false

noncomputable section

open Classical

namespace MultiphaseDisj

namespace DisjStructure

variable {n m w : ℕ} {Ω : Type*}

/-- The set of cells written while the insertions of `L` are run, in order, from memory `M`
with tape `ω`. -/
def seqWrites (D : DisjStructure n m w Ω) (ω : Ω) : List (Fin n) → Mem w → Finset (Word w)
  | [], _ => ∅
  | x :: L, M => (D.upd ω x).writes M ∪ D.seqWrites ω L ((D.upd ω x).run M).2

end DisjStructure

/-! ### Epoch bookkeeping of §3.1 (Setup and Epochs, p.16)

Throughout, `D : DisjStructure n n w Unit` is a **deterministic** structure (the random tape has
been fixed, p.16: "Fix the random tape by averaging over the hard distribution"), `t = tu · w`
fixes the hard distribution, `S` are the query sets and `X` the inserted set; insertions follow
`insertList n t X` (epoch `ℓ` first, epoch `1` last). -/

namespace Epochs

variable {n w : ℕ}

/-- `M_{>k}`: the memory after Phase I and epochs `ℓ, …, k + 1` (Ko, *Unconditional Boolean
Dynamic Lower Bounds from Disjointness*, arXiv:2610.10904, held version sha256 ba26649b…, p.16).
`memAbove … 0` is the final memory, after Phase II. -/
def memAbove (D : DisjStructure n n w Unit) (t : ℕ) (S : Fin n → Finset (Fin n))
    (X : Finset (Fin n)) (k : ℕ) : Mem w :=
  D.memAfter () S (epochsAbove n t X k)

/-- The final memory, after Phase II. -/
def finalMem (D : DisjStructure n n w Unit) (t : ℕ) (S : Fin n → Finset (Fin n))
    (X : Finset (Fin n)) : Mem w :=
  memAbove D t S X 0

/-- The cells written during epoch `j`. -/
def written (D : DisjStructure n n w Unit) (t : ℕ) (S : Fin n → Finset (Fin n))
    (X : Finset (Fin n)) (j : ℕ) : Finset (Word w) :=
  D.seqWrites () (epochList n t X j) (memAbove D t S X j)

/-- `C_j`: the cells **last written** in epoch `j` (p.16), i.e. written in epoch `j` and in none of
the later epochs `j' < j`. -/
def lastWritten (D : DisjStructure n n w Unit) (t : ℕ) (S : Fin n → Finset (Fin n))
    (X : Finset (Fin n)) (j : ℕ) : Finset (Word w) :=
  written D t S X j \ (Finset.Ico 1 j).biUnion (written D t S X)

/-- `C_{<j} := ⋃_{j' < j} C_{j'}`, the cells written after epoch `j` (p.16). -/
def lastWrittenBelow (D : DisjStructure n n w Unit) (t : ℕ) (S : Fin n → Finset (Fin n))
    (X : Finset (Fin n)) (j : ℕ) : Finset (Word w) :=
  (Finset.Ico 1 j).biUnion (lastWritten D t S X)

/-- `T(q)`: the number of cells read by query `q` on the final memory (p.16). -/
def queryCost (D : DisjStructure n n w Unit) (t : ℕ) (S : Fin n → Finset (Fin n))
    (X : Finset (Fin n)) (q : Fin n) : ℕ :=
  (D.qry () q).probes (finalMem D t S X)

/-- `t_j(q)`: the number of distinct cells of `C_j` read by query `q` (p.16). -/
def epochReads (D : DisjStructure n n w Unit) (t : ℕ) (S : Fin n → Finset (Fin n))
    (X : Finset (Fin n)) (j : ℕ) (q : Fin n) : ℕ :=
  (((D.qry () q).probed (finalMem D t S X)).toFinset ∩ lastWritten D t S X j).card

/-- `τ_j := E_{D,Q}[t_j(Q)]` (p.16). -/
def tau (D : DisjStructure n n w Unit) (t j : ℕ) : ℝ :=
  expect (dqLaw n t) (fun ω => (epochReads D t ω.1.1 ω.1.2 j ω.2 : ℝ))

/-- Merlin's message `U` for epoch `i` (§3.2, p.17): the two lists of the cells of `C_i` and of
`C_{<i}`, each cell with its final content.

**Formalization Note** Each list is a finite set of (address, final content) pairs; the order of
a list carries no information. -/
def merlinMsg (D : DisjStructure n n w Unit) (t i : ℕ) (S : Fin n → Finset (Fin n))
    (X : Finset (Fin n)) : Finset (Word w × Word w) × Finset (Word w × Word w) :=
  ((lastWritten D t S X i).image (fun a => (a, finalMem D t S X a)),
    (lastWrittenBelow D t S X i).image (fun a => (a, finalMem D t S X a)))

end Epochs

end MultiphaseDisj


