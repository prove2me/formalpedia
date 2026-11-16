-- Prove2me | Definitions.Def_HiddenPartition_Supplement_HasDrawingWithin
-- name    : HiddenPartition_Supplement_HasDrawingWithin
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T19:02:55.833749+00:00
-- url     : https://prove2.me/theorems/8162bf67-047f-4da7-a3c8-3f18bff3b528
-- title:
--   Plane drawings with at most $L$ crossings
-- statement:
--   A **plane drawing** of a graph $H$ places its vertices at distinct points of $\mathbb R^2$ and draws each edge $\{u,v\}$ as a simple arc — a continuous injective map $[0,1]\to\mathbb R^2$ — joining the points of $u$ and $v$ and passing through no vertex point in its interior. Its **number of crossings** is
--
--   $$
--   \sum_{\{e,e'\}} \big|\,\mathrm{int}(e)\cap\mathrm{int}(e')\,\big|,
--   $$
--
--   the sum over unordered pairs of distinct edges of the number of points common to their arc interiors (each required finite). $H$ has a drawing with at most $L$ crossings if some plane drawing has at most $L$ crossings.
--
--   This is the feasibility condition of Maximum Bounded-Crossing Subgraph (Definition 4.3).
--
--   **Formalization Note** The paper takes the problem from [CDGT23] and does not spell drawings out; this is the standard crossing-number convention. The sum over unordered pairs is written as the sum over ordered pairs, bounded by $2L$; the arc interior is the image of the open interval $(0,1)$.
-- source:
--   H. Agrawal, P. Eua-anant, B. Haeupler, B. Laekhanukit, P. Mihov, L. Milenković, R. Santos, Z. Zhang, From One Hidden Subgraph to Dense Graph Partitions with Applications to Hardness of Clustering, STOC 2027 submission (manuscript sha256 17239d0bf911912040cb82c45ae979b179c419fb0b9e69d6d1413bf70068b601), Definition 4.3, p.24 (pdf p.26) (drawings: the standard crossing-number convention of [CDGT23])

import Mathlib

set_option autoImplicit false

open Classical

namespace HiddenPartition.Supplement

/-- **A plane drawing with at most `L` crossings** (for Definition 4.3, Maximum Bounded-Crossing
Subgraph, Agrawal et al., STOC 2027 submission, manuscript sha256 17239d0b…, p.24 (pdf p.26)).

A drawing of the graph `H` places the vertices at distinct points `pos v` of `ℝ²` and draws each
edge `{u, v}` as a simple arc `arc {u, v} : [0, 1] → ℝ²` (continuous and injective) from `pos u`
to `pos v` (in either direction) that passes through no vertex point in its interior. The number
of crossings is the sum, over unordered pairs of distinct edges, of the number of points common to
their arc interiors; each such number must be finite. `HasDrawingWithin H L` says some drawing has
at most `L` crossings.

**Formalization Note.** The paper takes the problem from [CDGT23] and does not define drawings;
this is the standard crossing-number convention. The sum over unordered pairs of distinct edges is
written as the sum over ordered pairs, bounded by `2L`. The arc interior is the image of
`(0, 1)`. -/
def HasDrawingWithin {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) (L : ℕ) :
    Prop :=
  ∃ (pos : V → EuclideanSpace ℝ (Fin 2)) (arc : Sym2 V → unitInterval → EuclideanSpace ℝ (Fin 2)),
    Function.Injective pos ∧
    (∀ u v, H.Adj u v →
      Continuous (arc s(u, v)) ∧ Function.Injective (arc s(u, v)) ∧
      s(arc s(u, v) 0, arc s(u, v) 1) = s(pos u, pos v) ∧
      ∀ t : unitInterval, t ≠ 0 → t ≠ 1 → ∀ w : V, arc s(u, v) t ≠ pos w) ∧
    (∀ e ∈ H.edgeSet, ∀ e' ∈ H.edgeSet, e ≠ e' →
      (arc e '' {t | t ≠ 0 ∧ t ≠ 1} ∩ arc e' '' {t | t ≠ 0 ∧ t ≠ 1}).Finite) ∧
    (∑ e ∈ Finset.univ.filter (fun e : Sym2 V => e ∈ H.edgeSet),
      ∑ e' ∈ Finset.univ.filter (fun e' : Sym2 V => e' ∈ H.edgeSet ∧ e' ≠ e),
        (arc e '' {t | t ≠ 0 ∧ t ≠ 1} ∩ arc e' '' {t | t ≠ 0 ∧ t ≠ 1}).ncard) ≤ 2 * L

end HiddenPartition.Supplement


