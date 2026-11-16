-- Prove2me | Definitions.Def_SNPTreedepth_Supplement_HasStackLayout
-- name    : SNPTreedepth_Supplement_HasStackLayout
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:53:11.709233+00:00
-- url     : https://prove2.me/theorems/c11f1de2-e8d8-4494-a06d-99358e1e8780
-- title:
--   Stack layouts and stack number $\mathrm{sn}(G)\le k$
-- statement:
--   Let $G=(V,E)$ be a graph. A **$k$-page linear layout** $(<,E_1,\dots,E_k)$ consists of a total order $<$ on $V$ and a partition of $E$ into $k$ pages $E_1,\dots,E_k$ (pages may be empty, $k\ge0$). Two edges $ab,cd$ with $a<b$, $c<d$ and, by symmetry, $a<c$ **cross** if $c<b<d$. The layout is a **$k$-page stack layout** if no two edges on the same page cross. The **stack number** $\mathrm{sn}(G)$ is the least $k$ for which $G$ admits a $k$-page stack layout; since pages may be empty, $\mathrm{sn}(G)\le k$ holds exactly when $G$ has a $k$-page stack layout.
--
--   Stack layouts (book embeddings) are one of the two classical linear layouts; Theorem 42 expresses $\mathrm{sn}(G)\le k$ by an SNP sentence.
--
--   **Formalization Note** The order is an injective map $V\to\mathbb N$ and the pages are the fibres of an assignment of the edges to $\{0,\dots,k-1\}$; this mirrors the published queue-layout definition `PlanarQueue.Planar.HasQueueLayout`, which is used for the queue number.
-- source:
--   Depian, Ganian, Greilhuber, Gründel, Wietheger, A Uniform Algorithm for Strict NP on Bounded-Treedepth Structures, STOC 2027 submission (manuscript sha256 98e4e1a9…), Definitions 40 and 41, p.41 (PDF p.42)

import Mathlib

set_option autoImplicit false

namespace SNPTreedepth.Supplement

/-- Two edges **cross** in the vertex order `ord` (Depian et al., *A Uniform Algorithm for Strict NP
on Bounded-Treedepth Structures*, STOC 2027 submission (manuscript sha256 98e4e1a9…),
Definition 40, p.41): for edges `ab`, `cd` with `a < b`, `c < d` and (by symmetry) `a < c`, they
cross if `c < b < d`. Equivalently there are vertices `a < b < c < d` such that the two edges are
`{a, c}` and `{b, d}`.

**Formalization Note** The order is an injective `ord : V → ℕ` (`x < y` iff `ord x < ord y`); the
inequalities are strict, as in Definition 40. -/
def Crosses {V : Type} (ord : V → ℕ) (e f : Sym2 V) : Prop :=
  ∃ a b c d : V,
    ((e = s(a, c) ∧ f = s(b, d)) ∨ (e = s(b, d) ∧ f = s(a, c))) ∧
      ord a < ord b ∧ ord b < ord c ∧ ord c < ord d

/-- A **`k`-page stack layout** `(<, E₁, …, E_k)` of `G` (Depian et al., Definition 40, p.41): a
total order `<` on `V` (the injective `ord`) and a partition of `E` into `k` pages (the assignment
`page : E → Fin k`) such that no two edges on the same page cross. -/
def IsStackLayout {V : Type} (G : SimpleGraph V) (k : ℕ) (ord : V → ℕ)
    (page : G.edgeSet → Fin k) : Prop :=
  Function.Injective ord ∧ ∀ e f : G.edgeSet, page e = page f → ¬ Crosses ord e f

/-- `G` **has a `k`-page stack layout**, that is, `sn(G) ≤ k` (Depian et al., Definition 41,
p.41: "the stack number sn(G) of G is the least k such that G admits a k-page stack layout").

**Formalization Note** Pages are the fibres of an assignment `E → Fin k` and may be empty
(Definition 40 allows any `k ≥ 0`), so a layout with fewer pages is one with `k` pages; hence the
existence of a `k`-page layout is exactly `sn(G) ≤ k`. This is the stack analogue of the published
`PlanarQueue.Planar.HasQueueLayout`, with the same order and page conventions. -/
def HasStackLayout {V : Type} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ (ord : V → ℕ) (page : G.edgeSet → Fin k), IsStackLayout G k ord page

end SNPTreedepth.Supplement


