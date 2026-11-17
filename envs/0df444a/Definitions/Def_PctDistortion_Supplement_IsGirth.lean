-- Prove2me | Definitions.Def_PctDistortion_Supplement_IsGirth
-- name    : PctDistortion_Supplement_IsGirth
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:27:27.830459+00:00
-- url     : https://prove2.me/theorems/08fc0c1e-125a-46d7-b3cd-87c20d74b262
-- title:
--   Girth $g(G)$ and minimum in-degree $\delta^-(G)$ of a digraph
-- statement:
--   Let $G=(V,E)$ be a digraph. A **directed cycle of length** $\ell\ge 1$ consists of $\ell$ distinct nodes $u_1,\dots,u_\ell$ with arcs $u_i\to u_{i+1}$ for $i<\ell$ and $u_\ell\to u_1$. The **girth** $g(G)$ is the length of a shortest directed cycle; $G$ has **finite girth** $g$ when it has a directed cycle of length $g$ and none of any length $\ell$ with $1\le \ell<g$.
--
--   For a finite node set, the **minimum in-degree** is
--   $$\delta^-(G)=\min_{j\in V}\deg^-(j),$$
--   where $\deg^-(j)$ is the number of in-neighbours of $j$.
--
--   These are the graph quantities of the Caccetta–Häggkvist conjecture and of Theorems 4 and 5.
--
--   **Formalization Note** Directed cycles are the published `Digraph.HasCycleOfLength`. Since a "cycle of length $0$" holds vacuously, cycle lengths range over $\ell\ge 1$; a cycle of length $1$ is a loop and one of length $2$ a 2-cycle, so an oriented digraph has girth at least $3$. The minimum in-degree is a natural number (an infimum over the node type, $0$ on the empty type).
-- source:
--   Kizilkaya, Kalayci, Kempe, Micha, The Caccetta-Häggkvist Conjecture and Percentile Distortion: An Equivalence via Asymmetric Maximal Lotteries, STOC 2027 submission (held version, sha256 fd779dd0…), §2.2, p.9 (minimum in-degree, girth); §6, pp.18–19 (finite girth g = g(G))

import Mathlib
import Definitions.Def_TenChallenges_CaccettaHaggkvist
import Definitions.Def_PctDistortion_inDeg

set_option autoImplicit false

namespace PctDistortion.Supplement

/-- `g` is the **girth** `g(G)` of the digraph `G`: the length of a shortest directed cycle.
So `G` has a directed cycle of length `g ≥ 1` and none of any length `ℓ` with `1 ≤ ℓ < g`;
`G` has finite girth exactly when some such `g` exists.

Kizilkaya, Kalayci, Kempe, Micha, *The Caccetta-Häggkvist Conjecture and Percentile Distortion: An Equivalence via Asymmetric Maximal Lotteries*, STOC 2027 submission (held version, sha256 fd779dd0…), §2.2, p.9 and §6, pp.18–19 ("finite girth g = g(G)").

**Formalization Note.** A directed cycle of length `ℓ` is the published
`Digraph.HasCycleOfLength ℓ` (`ℓ` distinct nodes, each joined by an arc to the next,
cyclically). `HasCycleOfLength 0` holds vacuously, so cycle lengths range over `ℓ ≥ 1`; a cycle
of length `1` is a loop and one of length `2` is a 2-cycle, so in an oriented digraph the girth
is at least `3`. -/
def IsGirth {W : Type} (G : Digraph W) (g : ℕ) : Prop :=
  1 ≤ g ∧ G.HasCycleOfLength g ∧ ∀ ℓ : ℕ, 1 ≤ ℓ → ℓ < g → ¬ G.HasCycleOfLength ℓ

/-- The **minimum in-degree** `δ⁻(G) = min_{j ∈ V} deg⁻(j)` of a digraph on a finite node type,
a natural number.

Kizilkaya, Kalayci, Kempe, Micha, *The Caccetta-Häggkvist Conjecture and Percentile Distortion: An Equivalence via Asymmetric Maximal Lotteries*, STOC 2027 submission (held version, sha256 fd779dd0…), §2.2, p.9: "we write δ−(G) = min_{j∈V} deg−(j) for the minimum in-degree".

**Formalization Note.** The minimum is `⨅` over the node type in `ℕ`; on a nonempty finite type
it is attained, and on the empty type it is `0`. -/
noncomputable def minInDeg {W : Type} [Fintype W] (G : Digraph W) : ℕ :=
  ⨅ w, PctDistortion.inDeg G w

end PctDistortion.Supplement


