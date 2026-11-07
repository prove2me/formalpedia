-- Prove2me | Definitions.Def_SteinerAPX_cleanNetwork
-- name    : SteinerAPX_cleanNetwork
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:36:02.788051+00:00
-- url     : https://prove2.me/theorems/befe77a9-8278-4cad-9ece-2a6a125907a4
-- title:
--   Clean networks (Definition 10) and the four-port Steiner tree of a square
-- statement:
--   Let a cable layout of $H=(U,E)$ be given and let $M$ be a set of triples. The **clean network** of $M$ consists of
--
--   1. all cable segments;
--   2. at the square of every triple of $M$, the **four-port Steiner tree** on the corners $z\pm b_1$, $z\pm b_2$: Steiner points $s_\pm=z\pm c(b_1+b_2)$ with $c=\frac12\bigl(1-\frac1{\sqrt3}\bigr)$, segments $[s_+,z+b_1]$, $[s_+,z+b_2]$, $[s_-,z-b_1]$, $[s_-,z-b_2]$ and $[s_+,s_-]$, of total length $\sqrt2+\sqrt6=4-\Delta$;
--   3. at the fallback of every element $u$ contained in no triple of $M$, the **fallback segment** $[p_{s,0},p_{s,u}]$ of length $\frac43$.
--
--   When $M$ is a matching using $q$ squares, the clean network joins every element cable to the backbone and has length $L+\frac43(|U|-3q)+(4-\Delta)q=L+\frac43|U|-\Delta q$.
--
--   Clean networks realize the upper bound of the cable reduction, and the cleaning lemma compares every short tree on $P_\rho$ with one of them.
--
--   **Formalization Note** The Steiner tree is the explicit one above; any shortest network on the four corners has the same length. The clean networks of the paper are those of matchings, which is a hypothesis wherever they are used.
-- source:
--   S. Bartlmae, Inapproximability of Euclidean Steiner Tree, STOC 2027 submission (manuscript sha256 6f78a9ea…), Definition 10, §4.1, p.14 (PDF p.16); four-port tree from §4.1, p.13 (PDF p.15), Figure 3

import Mathlib
import Definitions.Def_SteinerAPX_CableLayout

namespace SteinerAPX

open Inst3DM CableLayout

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- **The four-port Steiner tree of a square.** For the square with corners `z ± b₁`, `z ± b₂`
(`b₁, b₂` orthonormal), the two Steiner points are `s± = z ± c(b₁ + b₂)` with
`c = (1 − 1/√3)/2`; `s₊` is joined to `z + b₁` and `z + b₂`, `s₋` to `z − b₁` and `z − b₂`, and
`s₊` to `s₋`. The four corner edges have length `√(2/3)` and the middle edge `√2 − √6/3`, in total
`√2 + √6 = 4 − ∆` (S. Bartlmae, *Inapproximability of Euclidean Steiner Tree*, STOC 2027
submission, manuscript sha256 6f78a9ea…, §4.1, p.13, Figure 3). -/
noncomputable def squareSteinerTree (z b₁ b₂ : V) : Network V := by
  classical
  exact
    let c : ℝ := (1 - 1 / Real.sqrt 3) / 2
    let sp := z + c • (b₁ + b₂)
    let sm := z - c • (b₁ + b₂)
    {(sp, z + b₁), (sp, z + b₂), (sm, z - b₁), (sm, z - b₂), (sp, sm)}

/-- **Clean networks (Definition 10).** S. Bartlmae, *Inapproximability of Euclidean Steiner
Tree*, STOC 2027 submission (manuscript sha256 6f78a9ea…), Definition 10, §4.1, p.14 (PDF p.16):
"A network is clean if it consists of the cables, the four-port Steiner trees at squares whose
triples form a matching, and the fallback segments for all elements outside these triples."

For a set `M` of triples, `cleanNetwork L M` consists of all cable segments, the four-port
Steiner tree `squareSteinerTree z_s b₁ b₂` at the square `s` of every triple of `M` that lies in
`E`, and the fallback segment `[p_{s,0}, p_{s,u}]` at the fallback `s` of every element `u`
contained in no triple of `M`. The clean networks of the paper are those with `M` a matching
(`IsMatching`, a hypothesis of each statement).

**Formalization Note** The Steiner tree at a square is the explicit one above; any other shortest
network on the four ports has the same length `4 − ∆`. The network is a `Finset`, so a segment
listed twice counts once; in a separated layout the three parts share no segment. -/
noncomputable def cleanNetwork {H : Inst3DM} (L : CableLayout H V)
    (M : Finset (Fin H.r × Fin H.r × Fin H.r)) : Network V := by
  classical
  exact (Finset.univ.biUnion fun i : Label H => L.cable i) ∪
    (Finset.univ.biUnion fun t : H.triples =>
      if t.1 ∈ M then squareSteinerTree (L.z (.inl t)) L.b₁ L.b₂ else ∅) ∪
    ((Finset.univ.filter fun u : H.Element => ∀ t ∈ M, u ∉ H.elems t).image fun u =>
      (L.port (.inr u) none, L.port (.inr u) (some u)))

end SteinerAPX


