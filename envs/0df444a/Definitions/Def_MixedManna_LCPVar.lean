-- Prove2me | Definitions.Def_MixedManna_LCPVar
-- name    : MixedManna_LCPVar
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:13:32.449271+00:00
-- url     : https://prove2.me/theorems/c3d1df5c-3025-434a-bfab-8a8aba3268af
-- title:
--   Variables $(p,f,r,s,z)$ of LCP (14)
-- statement:
--   A point of LCP (14) is $(p,f,r,s,z)$ with prices $p\in\mathbb R^M$, spendings $f\in\mathbb R^{\mathrm{Seg}}$, agent variables $r\in\mathbb R^N$, supplementary prices $s\in\mathbb R^{\mathrm{Seg}}$, and Lemke's scalar $z$. Writing $y=(p,f,r,s)$, the paper's points are $(y,z)$.
--
--   **Formalization Note** The point lives in the real vector space $\mathbb R^M\times\mathbb R^{\mathrm{Seg}}\times\mathbb R^N\times\mathbb R^{\mathrm{Seg}}\times\mathbb R$, so segments and extreme points are Mathlib's.
-- source:
--   Chaudhury, Garg, McGlaughlin, Mehta, Competitive Allocation of a Mixed Manna, arXiv:2008.02753v1, §4.2.2 pp.20–21 and §5 p.22 (y = (p, f, r, s))

import Mathlib
import Definitions.Def_MixedManna_Seg

namespace MixedManna

variable {N M : Type*} [Fintype N] [Fintype M]

/-- **The variables of LCP (14)** (Chaudhury, Garg, McGlaughlin, Mehta, *Competitive Allocation of
a Mixed Manna*, arXiv:2008.02753v1, pp.20–21): a point is `(p, f, r, s, z)` with prices
`p ∈ ℝ^M`, spendings `f ∈ ℝ^Seg`, agent multipliers `r ∈ ℝ^N`, supplementary prices `s ∈ ℝ^Seg`
and the scalar `z` of Lemke's augmentation.

**Formalization Note** The point is the real vector space
`(M → ℝ) × (Seg I → ℝ) × (N → ℝ) × (Seg I → ℝ) × ℝ`, so that `segment`, `openSegment` and
`Set.extremePoints` apply; the projections are `pv`, `fv`, `rv`, `sv`, `zv`. -/
abbrev LCPVar (I : Instance N M) : Type _ :=
  (M → ℝ) × (Seg I → ℝ) × (N → ℝ) × (Seg I → ℝ) × ℝ

/-- The prices `p`. -/
def pv {I : Instance N M} (x : LCPVar I) : M → ℝ := x.1
/-- The spendings `f`. -/
def fv {I : Instance N M} (x : LCPVar I) : Seg I → ℝ := x.2.1
/-- The agent variables `r`. -/
def rv {I : Instance N M} (x : LCPVar I) : N → ℝ := x.2.2.1
/-- The supplementary prices `s`. -/
def sv {I : Instance N M} (x : LCPVar I) : Seg I → ℝ := x.2.2.2.1
/-- The augmentation variable `z`. -/
def zv {I : Instance N M} (x : LCPVar I) : ℝ := x.2.2.2.2

end MixedManna


