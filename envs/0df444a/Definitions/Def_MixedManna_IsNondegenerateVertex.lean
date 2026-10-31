-- Prove2me | Definitions.Def_MixedManna_IsNondegenerateVertex
-- name    : MixedManna_IsNondegenerateVertex
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:15:05.213155+00:00
-- url     : https://prove2.me/theorems/c1fc510e-0096-400b-b17a-4d793307b8ea
-- title:
--   Nondegenerate vertex of $\mathcal P$ and the nondegeneracy hypothesis of Theorem 14
-- statement:
--   $\mathcal P$ lives in $k=|M|+2|\mathrm{Seg}|+|N|+1$ variables. A vertex (extreme point) of $\mathcal P$ is **nondegenerate** when exactly $k$ of the inequalities of $\mathcal P$ hold with equality there, counting the sign constraints of all variables and the constraints (14a)–(14f). This is the $d=0$ case of the paper's definition: at a $d$-dimensional face exactly $k-d$ inequalities are tight.
--
--   The module also defines the hypothesis used by Theorem 14: every vertex of $\mathcal P$ with $z>0$, $p_j<P$ for all $j$ and $r_i<R$ for all $i$ is nondegenerate. This is the conclusion of the paper's Theorem 11.
--
--   **Formalization Note** Each inequality is counted once, even when two inequalities coincide.
-- source:
--   Chaudhury, Garg, McGlaughlin, Mehta, Competitive Allocation of a Mixed Manna, arXiv:2008.02753v1, §4.2.2, p.21 (nondegeneracy of 𝒫; Theorem 11)

import Mathlib
import Definitions.Def_MixedManna_lcpPolyhedron

namespace MixedManna

variable {N M : Type*} [Fintype N] [Fintype M]

open Classical

/-- The number of inequalities of `𝒫` that hold with equality at `x`: the sign constraints of
`p`, `f`, `r`, `s`, `z` and the constraints `(14a)`–`(14f)`, each counted once. -/
noncomputable def tightCount (I : Instance N M) (P R : ℝ) (δ : M → ℝ) (ε : ℝ) (x : LCPVar I) :
    ℕ :=
  (Finset.univ.filter fun j => pv x j = 0).card +
  (Finset.univ.filter fun σ => fv x σ = 0).card +
  (Finset.univ.filter fun i => rv x i = 0).card +
  (Finset.univ.filter fun σ => sv x σ = 0).card +
  (if zv x = 0 then 1 else 0) +
  (Finset.univ.filter fun i => agentSlack I P x i = 0).card +
  (Finset.univ.filter fun j => priceSlack I P δ x j = 0).card +
  (Finset.univ.filter fun σ => spendSlack I P R x σ = 0).card +
  (Finset.univ.filter fun σ => segSlack I P ε x σ = 0).card

/-- The number `k = |M| + 2|Seg| + |N| + 1` of variables of `𝒫`. -/
noncomputable def numVars (I : Instance N M) : ℕ :=
  Fintype.card M + 2 * Fintype.card (Seg I) + Fintype.card N + 1

/-- **Nondegenerate vertex** (Chaudhury, Garg, McGlaughlin, Mehta, *Competitive Allocation of a
Mixed Manna*, arXiv:2008.02753v1, p.21: "if `𝒫` is defined on `k` variables, then at any `d`
dimensional face of `𝒫` exactly `(k − d)` inequalities hold with equality"). For a vertex
(`d = 0`): `x` is an extreme point of `𝒫` and exactly `k` of the inequalities of `𝒫` are tight.

**Formalization Note** The count runs over all inequalities of `𝒫`, sign constraints included
(`tightCount`). -/
def IsNondegenerateVertex (I : Instance N M) (P R : ℝ) (δ : M → ℝ) (ε : ℝ) (x : LCPVar I) :
    Prop :=
  x ∈ Set.extremePoints ℝ (lcpPolyhedron I P R δ ε) ∧ tightCount I P R δ ε x = numVars I

/-- **The nondegeneracy hypothesis of Theorem 14** (the conclusion of Theorem 11, p.21): every
vertex of `𝒫` with `z > 0`, `p_j < P` for all `j ∈ M` and `r_i < R` for all `i ∈ N` is
nondegenerate. -/
def NondegenerateInRegion (I : Instance N M) (P R : ℝ) (δ : M → ℝ) (ε : ℝ) : Prop :=
  ∀ x ∈ Set.extremePoints ℝ (lcpPolyhedron I P R δ ε), 0 < zv x → (∀ j, pv x j < P) →
    (∀ i, rv x i < R) → IsNondegenerateVertex I P R δ ε x

end MixedManna


