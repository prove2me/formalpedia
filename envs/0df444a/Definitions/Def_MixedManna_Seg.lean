-- Prove2me | Definitions.Def_MixedManna_Seg
-- name    : MixedManna_Seg
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:12:41.275014+00:00
-- url     : https://prove2.me/theorems/81c63c51-6f46-4d15-a8b6-f3921b456c84
-- title:
--   Segments carrying LCP variables
-- statement:
--   The LCP variables $f_{ijk}$ and $s_{ijk}$ are indexed by the **segments** $(i,j,k)$, $k\le|u_{ij}|$, of every agent on a bad and of the agents with $U_{ij1}>0$ on a good. For a good $j$ and an agent with $U_{ij1}\le 0$ the paper sets $f_{ijk}:=0$ and introduces no variables. The module also names the agent, item, index and slope of a segment, and whether it is the final segment $k=|u_{ij}|$.
--
--   **Formalization Note** A segment is a dependent triple with a 0-based index below $|u_{ij}|$; the type is finite.
-- source:
--   Chaudhury, Garg, McGlaughlin, Mehta, Competitive Allocation of a Mixed Manna, arXiv:2008.02753v1, §4.1, p.17 (variables not introduced for U_ij1 ≤ 0 on a good)

import Mathlib
import Definitions.Def_MixedManna_Instance

namespace MixedManna

variable {N M : Type*} [Fintype N] [Fintype M]

/-- Agent `i` carries LCP variables for item `j` unless `j` is a good and `U_ij1 ≤ 0` (p.17: "For
every `U_ij1 ≤ 0` for a good `j`, then we set `f_ijk := 0` at the beginning itself, and we do not
introduce the corresponding variables"). -/
def HasVar (I : Instance N M) (i : N) (j : M) : Prop := IsGood I j → 0 < I.U i j 0

/-- **The segments that carry LCP variables** (Chaudhury, Garg, McGlaughlin, Mehta, *Competitive
Allocation of a Mixed Manna*, arXiv:2008.02753v1, p.17): triples `(i, j, k)` with `k < |u_ij|`,
for every agent on a bad and for the agents with `U_ij1 > 0` on a good. The variables `f_ijk`,
`s_ijk` of LCP (14) are indexed by this finite type.

**Formalization Note** An element is `⟨⟨(i, j), k⟩, h⟩` with `k : Fin (K i j)` 0-based. -/
abbrev Seg (I : Instance N M) : Type _ :=
  {σ : (ij : N × M) × Fin (I.K ij.1 ij.2) // HasVar I σ.1.1 σ.1.2}

noncomputable instance (I : Instance N M) : Fintype (Seg I) := Fintype.ofFinite _

/-- The agent `i` of a segment `(i, j, k)`. -/
def segAgent {I : Instance N M} (σ : Seg I) : N := σ.1.1.1

/-- The item `j` of a segment `(i, j, k)`. -/
def segItem {I : Instance N M} (σ : Seg I) : M := σ.1.1.2

/-- The (0-based) index `k` of a segment `(i, j, k)`. -/
def segIdx {I : Instance N M} (σ : Seg I) : ℕ := σ.1.2.val

/-- The slope `U_ijk` of a segment. -/
def segSlope {I : Instance N M} (σ : Seg I) : ℝ := I.U (segAgent σ) (segItem σ) (segIdx σ)

/-- A segment is the final one, `k = |u_ij|`. -/
def IsLastSeg {I : Instance N M} (σ : Seg I) : Prop :=
  segIdx σ + 1 = I.K (segAgent σ) (segItem σ)

end MixedManna


