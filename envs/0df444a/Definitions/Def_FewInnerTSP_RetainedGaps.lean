-- Prove2me | Definitions.Def_FewInnerTSP_RetainedGaps
-- name    : FewInnerTSP_RetainedGaps
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:25:12.245544+00:00
-- url     : https://prove2.me/theorems/f697c99d-bfa5-4adb-9cc2-42c1071af4eb
-- title:
--   Gap weights, gap lists and the retained gap set of App. A
-- statement:
--   Fix an instance and a counterclockwise hull order $h_0,\dots,h_{h-1}$. For interior indices $p,q$ (possibly equal) and a gap $j$, the **attachment weight** is
--   $$w_j(p,q)=|h_jp|+|qh_{j+1}|-|h_jh_{j+1}|,$$
--   the extra length of inserting a chain from $p$ to $q$ into gap $j$.
--
--   The **list** of $(p,q)$ consists of the $\min\{k,h\}$ cheapest gaps, ties broken by index: gap $j$ is listed when fewer than $\min\{k,h\}$ gaps $i$ satisfy $w_i<w_j$, or $w_i=w_j$ and $i<j$. The **retained gaps** $R$ are the union of the lists over all ordered pairs $(p,q)\in I^2$, including $p=q$. The **retained hull positions** $H_0$ are both endpoints $j$ and $j+1$ of every retained gap.
--
--   These are the objects selected by Lemma 3.1 and kept by the reduction of §3.
--
--   **Formalization Note** For $k=0$ the set $R$ is empty; the reduction is used only for $k>0$.
-- source:
--   Li, Ma, Gong, Exact Euclidean TSP with Few Interior Points: A Square-Root Exponent, STOC 2027 submission (manuscript sha256 6541f631…), Lemma 3.1 and App. A, pp.4, 16 (PDF pp.6, 18)

import Mathlib
import Definitions.Def_FewInnerTSP_Instance

namespace FewInnerTSP

/-- The attachment weight `w_j(p, q) = |h_j p| + |q h_{j+1}| − |h_j h_{j+1}|` of gap `j` (between `h_j`
and `h_{j+1}`, cyclic indices) for a chain with endpoints `p, q`.
Source: Li, Ma, Gong, STOC 2027 submission (manuscript sha256 6541f631…), App. A, p.16 (PDF p.18). -/
noncomputable def gapWeight {n h : ℕ} (P : Fin n → Pt) (hull : Fin h → Fin n) (p q : Fin n)
    (j : Fin h) : ℝ :=
  dist (P (hull j)) (P p) + dist (P q) (P (hull (finRotate h j))) -
    dist (P (hull j)) (P (hull (finRotate h j)))

open Classical in
/-- The list of the pair `(p, q)`: the `min{k, h}` cheapest distinct gaps, ties broken by the index.
A gap `j` is on the list when fewer than `min{k, h}` gaps come strictly before it in the
lexicographic order of `(w_j(p, q), j)`.
Source: Li, Ma, Gong, App. A, p.16 (PDF p.18). -/
noncomputable def gapList {n h : ℕ} (P : Fin n → Pt) (hull : Fin h → Fin n) (p q : Fin n) :
    Finset (Fin h) :=
  Finset.univ.filter fun j =>
    (Finset.univ.filter fun i =>
      gapWeight P hull p q i < gapWeight P hull p q j ∨
        (gapWeight P hull p q i = gapWeight P hull p q j ∧ i < j)).card
      < min (interiorCount P) h

/-- **The retained gaps** `R`: the union of the lists of all ordered pairs `(p, q) ∈ I²`, including
`p = q`. Source: Li, Ma, Gong, App. A, p.16 (PDF p.18).

**Formalization Note** At `k = 0` this is empty; the reduction is defined only for `k > 0`. -/
noncomputable def retainedGaps {n h : ℕ} (P : Fin n → Pt) (hull : Fin h → Fin n) : Finset (Fin h) :=
  (interiorIdx P).biUnion fun p => (interiorIdx P).biUnion fun q => gapList P hull p q

/-- The hull positions of the retained vertices `H₀`: both endpoints of every retained gap.
Source: Li, Ma, Gong, §3, p.4 (PDF p.6). -/
noncomputable def retainedPos {n h : ℕ} (P : Fin n → Pt) (hull : Fin h → Fin n) : Finset (Fin h) :=
  retainedGaps P hull ∪ (retainedGaps P hull).image (finRotate h)

end FewInnerTSP


