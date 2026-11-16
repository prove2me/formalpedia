-- Prove2me | Definitions.Def_GeomDRSub_Supplement_OResp
-- name    : GeomDRSub_Supplement_OResp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T18:37:39.740246+00:00
-- url     : https://prove2.me/theorems/a16de089-bfcc-46c1-8904-859297beb046
-- title:
--   Oracle responses: value–gradient pair or projected point
-- statement:
--   A response to an oracle call is either the exact pair $(f(y),\nabla f(y))\in\mathbb R\times\mathbb R^d$ returned by an objective query, or a point of $\mathbb R^d$ returned by a projection call. An emission receives the uninformative response $0\in\mathbb R^d$.
-- source:
--   Aggarwal–Lu, Geometry-Dependent Online and Offline Approximation for Non-Monotone DR-Submodular Maximization, arXiv:2610.00545, Definition 6.1, p.33

import Mathlib

namespace GeomDRSub.Supplement

/-- **Oracle responses.** Aggarwal–Lu, *Geometry-Dependent Online and Offline Approximation for Non-Monotone
DR-Submodular Maximization*, arXiv:2610.00545, Definition 6.1 (p.33): "An objective query at
`y ∈ [0,1]^d` returns the exact pair `(f(y), ∇f(y))`, and exact Euclidean projection onto `K` is
supplied separately."

`OResp d = (ℝ × ℝ^d) ⊕ ℝ^d`: `Sum.inl (f(y), ∇f(y))` answers an objective query and `Sum.inr q`
answers a projection call (`q = Π_K(z)`). Emissions receive the uninformative response
`Sum.inr 0`. -/
abbrev OResp (d : ℕ) : Type :=
  (ℝ × EuclideanSpace ℝ (Fin d)) ⊕ EuclideanSpace ℝ (Fin d)

end GeomDRSub.Supplement


