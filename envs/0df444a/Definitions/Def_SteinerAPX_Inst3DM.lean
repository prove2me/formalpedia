-- Prove2me | Definitions.Def_SteinerAPX_Inst3DM
-- name    : SteinerAPX_Inst3DM
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:33:20.837762+00:00
-- url     : https://prove2.me/theorems/4cbbb374-b727-45e4-be98-46a67ff21805
-- title:
--   Three-dimensional matching, 3DM-3, and the maximum matching size $\nu(H)$
-- statement:
--   A **three-dimensional matching instance** $H=(U,E)$ has an element set $U$ partitioned into three parts of size $r\ge1$, and a set $E$ of triples each containing one element from each part. Here $U=\{0,1,2\}\times\{0,\dots,r-1\}$, so $|U|=3r$, and a triple $(a,b,c)$ contains the elements $(0,a),(1,b),(2,c)$.
--
--   1. A **matching** is a set of pairwise disjoint triples of $E$; it is perfect if it has size $r$.
--   2. $H$ is an instance of **3DM-3** if every element occurs in at most three triples (so $|E|\le 3r$).
--   3. $\nu(H)$ is the maximum size of a matching, and $m=|U|+|E|$ is the instance size.
--
--   A **raw 3DM code** $(r,\text{list of triples})$ is valid if $r\ge1$, every coordinate is $<r$ and no triple repeats; it describes the instance with those triples.
--
--   This is the source problem of the reduction: the gap version of Lemma 4 asks to distinguish $\nu(H)=r$ from $\nu(H)\le(1-\delta)r$.
--
--   **Formalization Note** $r\ge 1$ is built in: for $r=0$ the two cases of the gap problem coincide. The occurrence bound is the separate predicate `IsThreeDM3`. Raw codes are encoded with the published `natBits`, `listBits`, `pairBits`.
-- source:
--   S. Bartlmae, Inapproximability of Euclidean Steiner Tree, STOC 2027 submission (manuscript sha256 6f78a9ea…), §2, p.4 (PDF p.6)

import Mathlib
import Definitions.Def_BinPackingGap

namespace SteinerAPX

/-- **Three-dimensional matching, 3DM-3, and the maximum matching size `ν(H)`.** S. Bartlmae,
*Inapproximability of Euclidean Steiner Tree*, STOC 2027 submission (manuscript sha256
6f78a9ea…), §2, p.4 (PDF p.6): "In a three-dimensional matching instance H = (U, E), the element
set U is partitioned into three parts of size r, and each triple in E contains one element from
each part. A matching consists of pairwise disjoint triples and is perfect if it has size r. We
consider 3DM-3, where each element occurs in at most three triples, implying |E| ≤ 3r. Write
m = |U| + |E| for the instance size and ν(H) for the maximum size of a matching."

An instance has parts of size `r ≥ 1`; the element set is `U = {0,1,2} × {0,…,r−1}` (part, index),
so `|U| = 3r`, and a triple `(a, b, c)` contains the elements `(0,a)`, `(1,b)`, `(2,c)`.

**Formalization Note** `1 ≤ r` is a field: for `r = 0` the two cases of the gap problem
(`ν = r` and `ν ≤ (1−δ)r`) coincide, so the empty instance is excluded. The occurrence bound of
3DM-3 is the separate predicate `IsThreeDM3`. `ν(H)` is the largest cardinality of a matching
(a finite maximum; the empty matching makes it well defined). `Raw3DM` is the code a machine
reads and writes: `(r, list of triples)`, encoded by `Raw3DM.bits` (the published `natBits`,
`listBits`, `pairBits`), valid when `1 ≤ r`, every coordinate is `< r`, and no
triple is repeated. -/
structure Inst3DM where
  r : ℕ
  one_le_r : 1 ≤ r
  triples : Finset (Fin r × Fin r × Fin r)

namespace Inst3DM

/-- The elements: `(part, index)`. -/
abbrev Element (H : Inst3DM) := Fin 3 × Fin H.r

/-- The three elements of a triple. -/
def elems (H : Inst3DM) (t : Fin H.r × Fin H.r × Fin H.r) : Finset H.Element :=
  {(0, t.1), (1, t.2.1), (2, t.2.2)}

/-- The number of triples of `E` containing the element `u`. -/
def occurrences (H : Inst3DM) (u : H.Element) : ℕ :=
  (H.triples.filter fun t => u ∈ H.elems t).card

/-- 3DM-3: every element occurs in at most three triples. -/
def IsThreeDM3 (H : Inst3DM) : Prop := ∀ u : H.Element, H.occurrences u ≤ 3

/-- A matching: a set of triples of `E` that are pairwise disjoint. -/
def IsMatching (H : Inst3DM) (M : Finset (Fin H.r × Fin H.r × Fin H.r)) : Prop :=
  M ⊆ H.triples ∧ ∀ t ∈ M, ∀ t' ∈ M, t ≠ t' → Disjoint (H.elems t) (H.elems t')

/-- `ν(H)`: the maximum size of a matching. -/
noncomputable def nu (H : Inst3DM) : ℕ := by
  classical
  exact (H.triples.powerset.filter fun M => H.IsMatching M).sup Finset.card

/-- The instance size `m = |U| + |E| = 3r + |E|`. -/
def size (H : Inst3DM) : ℕ := 3 * H.r + H.triples.card

end Inst3DM

/-- Raw code of a three-dimensional matching instance: `r` and a list of triples. -/
abbrev Raw3DM := ℕ × List (ℕ × ℕ × ℕ)

namespace Raw3DM

/-- Well-formedness: `1 ≤ r`, every coordinate below `r`, no repeated triple. -/
def Valid (R : Raw3DM) : Prop :=
  1 ≤ R.1 ∧ (∀ t ∈ R.2, t.1 < R.1 ∧ t.2.1 < R.1 ∧ t.2.2 < R.1) ∧ R.2.Nodup

/-- The instance described by a valid raw code. -/
def toInst (R : Raw3DM) (h : R.Valid) : Inst3DM where
  r := R.1
  one_le_r := h.1
  triples := (R.2.filterMap fun t =>
    if h' : t.1 < R.1 ∧ t.2.1 < R.1 ∧ t.2.2 < R.1 then
      some (⟨t.1, h'.1⟩, ⟨t.2.1, h'.2.1⟩, ⟨t.2.2, h'.2.2⟩)
    else none).toFinset

/-- Binary code of a raw instance, from the published `natBits`, `listBits`, `pairBits`. -/
def bits : Raw3DM → List Bool :=
  OAI.BinPackingGap.BinaryEncoding.pairBits OAI.BinPackingGap.BinaryEncoding.natBits
    (OAI.BinPackingGap.BinaryEncoding.listBits
      (OAI.BinPackingGap.BinaryEncoding.pairBits OAI.BinPackingGap.BinaryEncoding.natBits
        (OAI.BinPackingGap.BinaryEncoding.pairBits OAI.BinPackingGap.BinaryEncoding.natBits
          OAI.BinPackingGap.BinaryEncoding.natBits)))

end Raw3DM

end SteinerAPX


