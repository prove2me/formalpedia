-- Prove2me | Definitions.Def_SparseDisc_IsCGood
-- name    : SparseDisc_IsCGood
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:54:36.868606+00:00
-- url     : https://prove2.me/theorems/0aecd100-e79e-494b-be96-d3dd893aada1
-- title:
--   $c$-good graph
-- statement:
--   A **2-sparse constraint system** on a finite item set consists of supports $(U_v)_{v \in V}$, every item lying in at most two of them, and symmetric sets $Z_v \subseteq \{\pm1\}^{U_v}$; a solution is an $x$ with $x|_{U_v} \in Z_v$ for all $v$. A simple graph $G$ on $V$ is **$c$-good** if every 2-sparse constraint system with vertex set $V$, with graph $H$ a subgraph of $G$, and with $c$-coarse constraints $Z_v$, has a solution.
--
--   **Formalization Note** The definition quantifies over every finite item type, as the paper quantifies over every item set $[m]$; symmetry of $Z_v$ is part of $c$-coarseness.
-- source:
--   Zeng–Cao–Dai–Wang–Liao, Sparse Discrepancy Beyond Additive Functions: Acyclic, Bounded-Degree and Degenerate Sparsity Patterns, STOC 2027 submission (manuscript sha256 0f09ec60…25b81), Definition 8.4, p.30

import Mathlib
import Definitions.Def_SparseDisc_IsCoarse
import Definitions.Def_SparseDisc_IsTwoSparseSupp
import Definitions.Def_SparseDisc_instGraph
import Definitions.Def_SparseDisc_restrictTo

namespace SparseDisc

/-- `IsCGood G c`: the simple graph `G` on `V` is **`c`-good** — every 2-sparse constraint system
with vertex set `V`, with graph `H` a subgraph of `G`, and with `c`-coarse constraints, has a
solution (Zeng–Cao–Dai–Wang–Liao, *Sparse Discrepancy Beyond Additive Functions*, STOC 2027
submission manuscript (sha256 0f09ec60…25b81), Definition 8.4, p.30).

**Formalization Note** A constraint system on a finite item type `ι` is a family of supports
`U_v ⊆ ι` and sets `Z_v ⊆ {±1}^{U_v}`; a solution is `x ∈ {±1}^ι` with `x|_{U_v} ∈ Z_v` for all
`v`. Symmetry of `Z_v` is part of `c`-coarseness. The definition quantifies over every finite
item type, as the paper quantifies over every item set `[m]`. -/
def IsCGood {V : Type} [Fintype V] (G : SimpleGraph V) (c : ℝ) : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (U : V → Finset ι) (Z : (v : V) → Set (Cube (U v))),
    IsTwoSparseSupp U → instGraph U ≤ G → (∀ v, IsCoarse c (Z v)) →
      ∃ x : Cube ι, ∀ v, restrictTo (U v) x ∈ Z v

end SparseDisc


