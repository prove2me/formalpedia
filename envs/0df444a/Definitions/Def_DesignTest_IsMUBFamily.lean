-- Prove2me | Definitions.Def_DesignTest_IsMUBFamily
-- name    : DesignTest_IsMUBFamily
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T04:10:06.570412+00:00
-- url     : https://prove2.me/theorems/a72f40dd-2107-4453-abef-6dbdbcef6aa3
-- title:
--   A family of pairwise mutually unbiased orthonormal bases of $\mathbb C^d$
-- statement:
--   A family $(B_r)_{r}$ of orthonormal bases $B_r=(b_{r,0},\dots,b_{r,d-1})$ of $\mathbb C^d$ is **pairwise mutually unbiased** if vectors from two different bases always have the same overlap,
--   $$|\langle b_{r,i}|b_{s,j}\rangle|^2=\frac1d\qquad(r\ne s,\ \text{all }i,j).$$
--   A **complete set** of mutually unbiased bases is such a family of $d+1$ bases.
--
--   The uniform measure on the $d(d+1)$ vectors of a complete set is an exact state $2$-design, which gives the inverse-square sample lower bound for $t=2$.
--
--   **Formalization Note** Bases are indexed families of unit vectors (`Fin d → PureVec d`) that are orthonormal as vectors of $\mathbb C^d$.
-- source:
--   Kawachi–Nakata–Takeuchi, Testing State and Unitary Designs, STOC 2027 submission (sha256 e2f0a429…), proof of Corollary 4.17, p.44 ([WF89])

import Mathlib
import Definitions.Def_DesignTest_haarState

set_option autoImplicit false

namespace DesignTest

/-- **A family of pairwise mutually unbiased orthonormal bases** of `ℂ^d` (STOC 2027 submission
(sha256 e2f0a429…), proof of Corollary 4.17, p.44; [WF89]): every `B r` is an orthonormal basis
`(B r 0, …, B r (d−1))` of `ℂ^d`, and vectors from two different bases satisfy
`|⟨B r i | B s j⟩|² = 1/d`. A complete set is a family of `d + 1` such bases (index type `Fin (d + 1)`). -/
def IsMUBFamily {d : ℕ} {ι : Type} (B : ι → Fin d → PureVec d) : Prop :=
  (∀ r, Orthonormal ℂ fun i => ((B r i : PureVec d) : EuclideanSpace ℂ (Fin d))) ∧
    ∀ r s, r ≠ s → ∀ i j,
      ‖inner ℂ ((B r i : PureVec d) : EuclideanSpace ℂ (Fin d))
          ((B s j : PureVec d) : EuclideanSpace ℂ (Fin d))‖ ^ 2 = 1 / (d : ℝ)

end DesignTest


