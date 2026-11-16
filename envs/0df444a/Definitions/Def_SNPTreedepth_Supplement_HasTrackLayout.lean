-- Prove2me | Definitions.Def_SNPTreedepth_Supplement_HasTrackLayout
-- name    : SNPTreedepth_Supplement_HasTrackLayout
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:53:27.979479+00:00
-- url     : https://prove2.me/theorems/8c10b45e-06a4-45d3-9bc4-82181d3bec66
-- title:
--   Track layouts and track number $\mathrm{tn}(G)\le t$
-- statement:
--   Let $t\ge1$. A **$t$-track layout** of a graph $G=(V,E)$ is a partition $V=T_1\cup\dots\cup T_t$ of the vertex set into independent sets, the **tracks**, together with a strict linear order $<_i$ on each track $T_i$, such that no two edges form an **X-crossing**: there are no $i\ne j$ and edges $uv,xy$ with $u,x\in T_i$, $v,y\in T_j$, $u<_ix$ and $y<_jv$. The **track number** $\mathrm{tn}(G)$ is the least $t$ such that $G$ has a $t$-track layout; tracks may be empty, so $\mathrm{tn}(G)\le t$ holds exactly when $G$ has a $t$-track layout.
--
--   Theorem 45 expresses $\mathrm{tn}(G)\le t$ by an SNP sentence.
--
--   **Formalization Note** The tracks are the fibres of a map $V\to\{0,\dots,t-1\}$, and the orders are given by a ranking $V\to\mathbb N$ that is injective on each track; every family of strict linear orders on the finite tracks arises this way.
-- source:
--   Depian, Ganian, Greilhuber, Gründel, Wietheger, A Uniform Algorithm for Strict NP on Bounded-Treedepth Structures, STOC 2027 submission (manuscript sha256 98e4e1a9…), Definition 44, p.43 (PDF p.44)

import Mathlib

set_option autoImplicit false

namespace SNPTreedepth.Supplement

/-- A **`t`-track layout** of `G` (Depian et al., *A Uniform Algorithm for Strict NP on
Bounded-Treedepth Structures*, STOC 2027 submission (manuscript sha256 98e4e1a9…), Definition 44,
p.43): a partition `V = T₁ ∪ ⋯ ∪ T_t` into independent sets (the tracks; `T_i` is the fibre of
`track` over `i`) with a strict linear order `<_i` on each track (`u <_i x` iff `ord u < ord x` for
`u, x ∈ T_i`), such that no two edges form an **X-crossing**: there are no `i ≠ j` and edges
`uv`, `xy` with `u, x ∈ T_i`, `v, y ∈ T_j`, `u <_i x` and `y <_j v`.

**Formalization Note** The order on each track is given by a ranking `ord : V → ℕ` that is
injective on every track; restricted to a track it is a strict linear order, and every family of
strict linear orders on the (finite) tracks arises this way. Comparisons of `ord` between
different tracks are never used. -/
def IsTrackLayout {V : Type} (G : SimpleGraph V) (t : ℕ) (track : V → Fin t) (ord : V → ℕ) :
    Prop :=
  (∀ u v, G.Adj u v → track u ≠ track v) ∧
  (∀ u v, track u = track v → ord u = ord v → u = v) ∧
  ¬ ∃ u v x y : V, track u = track x ∧ track v = track y ∧ track u ≠ track v ∧
      G.Adj u v ∧ G.Adj x y ∧ ord u < ord x ∧ ord y < ord v

/-- `G` **has a `t`-track layout**, that is, `tn(G) ≤ t` (Depian et al., Definition 44, p.43:
"the track number tn(G) is the least t such that G has a t-track layout").

**Formalization Note** Tracks are the fibres of `track : V → Fin t` and may be empty, so the
existence of a layout with `t` tracks is the monotone statement `tn(G) ≤ t`. -/
def HasTrackLayout {V : Type} (G : SimpleGraph V) (t : ℕ) : Prop :=
  ∃ (track : V → Fin t) (ord : V → ℕ), IsTrackLayout G t track ord

end SNPTreedepth.Supplement


