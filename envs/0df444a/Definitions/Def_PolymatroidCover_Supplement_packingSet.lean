-- Prove2me | Definitions.Def_PolymatroidCover_Supplement_packingSet
-- name    : PolymatroidCover_Supplement_packingSet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:50:45.081808+00:00
-- url     : https://prove2.me/theorems/7a3da773-7f53-4570-a143-3c0d6125697b
-- title:
--   Output decoder for a packing of generators on the oracle RAM
-- statement:
--   This fixes how a program of the mission's value-oracle RAM reports a family of pairwise disjoint sets. When the machine halts with output pointer $p$, the integer cell $p$ holds a number $q$, and the integer cell $p + 1 + e$ holds a label $\ell(e)$ of the element $e \in E = \{0,\dots,n-1\}$. For $0 \le i < q$ the $i$-th set of the family is
--
--   $$
--   G_i := \{ e \in E : \ell(e) = i \}.
--   $$
--
--   An element whose label lies outside $\{0,\dots,q-1\}$ belongs to no set. The sets $G_0,\dots,G_{q-1}$ are pairwise disjoint by construction and need not cover $E$. This is the output format of the algorithmic clause of Theorem 1.3.
--
--   **Formalization Note** The input layout is the published `coverInput n` of Theorem 1.1 (only $n$, in integer cell $0$). The module defines `packingCount` (the number $q$), `packingLabel` (the label of $e$) and `packingSet` (the set $G_i$).
-- source:
--   Bérczi, Chandrasekaran, Chekuri, Liu, Ravi, Approximate Covering and Packing in Polymatroids, STOC 2027 submission (manuscript sha256 47f38a6f…), Theorem 1.3, p.4 (PDF p.6) and p.26 (PDF p.28)

import Mathlib
import Definitions.Def_LSWNewArcAudit_NewArc_OracleRAM

namespace PolymatroidCover.Supplement

/-- Output decoder for the algorithmic clause of Theorem 1.3 (Bérczi–Chandrasekaran–Chekuri–Liu–Ravi, *Approximate Covering and Packing in Polymatroids*, STOC 2027 submission (manuscript sha256 47f38a6f…), printed p.4 = PDF p.6 and
p.26 = PDF p.28) on the published oracle RAM `LSWNewArcAudit.NewArc`. A machine state `s` that
halted with pointer `p` outputs a family of `q := integerMemory p` sets: the label of the element
`e` is stored in integer cell `p + 1 + e`, and for `0 ≤ i < q` the `i`-th set of the family is
`{e : label e = i}` (`packingSet`). An element whose label lies outside `[0, q)` is in no set.

**Formalization Note** The sets of the decoded family are pairwise disjoint by construction (each
element has one label); they need not cover the ground set. The input layout is the published
`PolymatroidCover.coverInput n` (only `n`). -/
def packingCount {n : ℕ} (s : LSWNewArcAudit.NewArc.OracleState n) (p : ℤ) : ℤ :=
  s.integerMemory p

/-- The label of the element `e` in the output of a halted state with pointer `p`. -/
def packingLabel {n : ℕ} (s : LSWNewArcAudit.NewArc.OracleState n) (p : ℤ) (e : Fin n) : ℤ :=
  s.integerMemory (p + 1 + (e : ℤ))

/-- The `i`-th set of the decoded family: the elements labelled `i`. -/
def packingSet {n : ℕ} (s : LSWNewArcAudit.NewArc.OracleState n) (p : ℤ) (i : ℤ) :
    Finset (Fin n) :=
  Finset.univ.filter (fun e => packingLabel s p e = i)

end PolymatroidCover.Supplement


