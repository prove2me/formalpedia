-- Prove2me | Definitions.Def_MixedManna_lcpSolutions
-- name    : MixedManna_lcpSolutions
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:15:15.290771+00:00
-- url     : https://prove2.me/theorems/499d1f4e-d32e-423c-9b1d-b4b04a45a0a3
-- title:
--   Solutions of the augmented LCP (14)
-- statement:
--   A **solution** of LCP (14) is a point of $\mathcal P$ at which every complementarity condition holds: each variable times the slack of its paired constraint vanishes, with the pairing $r_i\perp(14a)$, $p_j\perp(14b)$ or $(14c)$, $f_{ijk}\perp(14d)$ or $(14e)$, $s_{ijk}\perp(14f)$. The variable $z$ has no partner. A solution of LCP (13) is a solution with $z=0$.
--
--   The solution set is the object Lemke's scheme walks on: under nondegeneracy it is a union of vertices and edges of $\mathcal P$.
-- source:
--   Chaudhury, Garg, McGlaughlin, Mehta, Competitive Allocation of a Mixed Manna, arXiv:2008.02753v1, §2.2 p.6 (⊥ notation, the set S) and (14a′)–(14f′), p.21

import Mathlib
import Definitions.Def_MixedManna_lcpPolyhedron

namespace MixedManna

variable {N M : Type*} [Fintype N] [Fintype M]

/-- **Solutions of the augmented LCP (14)** (Chaudhury, Garg, McGlaughlin, Mehta, *Competitive
Allocation of a Mixed Manna*, arXiv:2008.02753v1, pp.6, 21): the points of `𝒫` at which every
complementarity condition holds, i.e. each variable times the slack of its paired constraint is
zero: `r_i ⊥ (14a)`, `p_j ⊥ (14b)/(14c)`, `f_ijk ⊥ (14d)/(14e)`, `s_ijk ⊥ (14f)`. The variable `z`
has no partner. This is the set `S` of p.6; a "solution to LCP (14)" is a point of it, and a
"solution to LCP (13)" is a point of it with `z = 0`.

**Formalization Note** "`⊥`" means: the inequality, the variable `≥ 0`, and
(variable)·(slack) = 0 (p.6 and p.17). -/
def lcpSolutions (I : Instance N M) (P R : ℝ) (δ : M → ℝ) (ε : ℝ) : Set (LCPVar I) :=
  {x | x ∈ lcpPolyhedron I P R δ ε ∧ (∀ i, rv x i * agentSlack I P x i = 0) ∧
    (∀ j, pv x j * priceSlack I P δ x j = 0) ∧ (∀ σ, fv x σ * spendSlack I P R x σ = 0) ∧
    (∀ σ, sv x σ * segSlack I P ε x σ = 0)}

end MixedManna


