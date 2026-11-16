-- Prove2me | Definitions.Def_GeomDRSub_Supplement_OCall
-- name    : GeomDRSub_Supplement_OCall
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T18:37:20.022086+00:00
-- url     : https://prove2.me/theorems/9ce212b6-89ec-4951-9807-cf2ab74ccc89
-- title:
--   Oracle calls: objective query, projection call, or emitted point
-- statement:
--   An oracle algorithm in dimension $d$ makes calls of three kinds:
--
--   1. an **objective query** at a point $y\in[0,1]^d$;
--   2. a **projection call** on a vector $z\in\mathbb R^d$, asking for the exact Euclidean projection $\Pi_K(z)$ onto the feasible set;
--   3. the **emission** of a point $p\in\mathbb R^d$: the returned point of an offline algorithm, or the action $p_t$ that an online learner commits for its next round.
--
--   This type lists the calls; the answers are given by `offlineAns` and `onlineAns`.
--
--   **Formalization Note** The type is $[0,1]^d\sqcup(\mathbb R^d\sqcup\mathbb R^d)$, so an objective query can only be made at a point of the cube. A sum type carries the standard measurable structure.
-- source:
--   Aggarwal–Lu, Geometry-Dependent Online and Offline Approximation for Non-Monotone DR-Submodular Maximization, arXiv:2610.00545, Definition 6.1, p.33, and Section 7.2, p.52

import Mathlib
import Definitions.Def_GeomDRSub_cube

namespace GeomDRSub.Supplement

/-- **Oracle calls.** Aggarwal–Lu, *Geometry-Dependent Online and Offline Approximation for Non-Monotone
DR-Submodular Maximization*, arXiv:2610.00545, Definition 6.1 (p.33) and Section 7.2 (p.52): an algorithm
either makes an objective query at a point `y ∈ [0,1]^d`, or asks for the exact Euclidean projection
`Π_K(z)` of a vector `z ∈ ℝ^d`, or emits a point of `ℝ^d` (the offline output `p`, or the online
action `p_t` committed for the next round).

`OCall d = cube d ⊕ (ℝ^d ⊕ ℝ^d)`: `Sum.inl y` is an objective query at `y`, `Sum.inr (Sum.inl z)`
a projection call on `z`, and `Sum.inr (Sum.inr p)` the emission of the point `p` (a *mark*).

**Formalization Note.** Query points have type `cube d`, so an algorithm cannot query outside
`[0,1]^d` (the page only defines queries at `y ∈ [0,1]^d`). A sum type is used, rather than an
inductive type, so that the measurable-space structure is the standard one on `Sum`/`Subtype`. -/
abbrev OCall (d : ℕ) : Type :=
  ↥(cube d) ⊕ (EuclideanSpace ℝ (Fin d) ⊕ EuclideanSpace ℝ (Fin d))

end GeomDRSub.Supplement


