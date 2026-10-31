-- Prove2me | Definitions.Def_MinVolEllipsoid_liftCone
-- name    : MinVolEllipsoid_liftCone
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:44:40.846639+00:00
-- url     : https://prove2.me/theorems/d8ff30d9-4260-43c2-b8fb-82804de6b4d0
-- title:
--   The cone $\mathcal K=\mathrm{cone}(\{[x;1]:x\in\mathcal P\})$, display (2)
-- statement:
--   Let $\mathcal P\subseteq\mathbb R^K$. The cone of display (2) is the **conic hull** of the lifted set,
--
--   $$
--   \mathcal K=\mathrm{cone}\bigl(\{[x;1]:x\in\mathcal P\}\bigr)=\Bigl\{\textstyle\sum_{s=1}^{m}\lambda_s[x_s;1]\;:\;m\in\mathbb N,\ \lambda_s\ge0,\ x_s\in\mathcal P\Bigr\}\subseteq\mathbb R^{K+1}.
--   $$
--
--   The empty combination ($m=0$) gives $0\in\mathcal K$; no closure is taken. For a convex $\mathcal P$, the points of $\mathcal P$ are exactly the $x$ with $[x;1]\in\mathcal K$, which is how the paper rewrites optimization over $\mathcal P$ as optimization over the cone $\mathcal K$.
--
--   **Formalization Note** The dimension is written $n$ (the paper's $K$ clashes with the cone $\mathcal K$). $\mathbb R^{K+1}$ is the function type `Fin n ⊕ Unit → ℝ`, the paper's last coordinate being the `Unit` coordinate. The conic hull is written out as finite nonnegative combinations, the form used in the proof of Lemma 1 (p.6).
-- source:
--   Mittal & Hanasusanto, Finding Minimum Volume Circumscribing Ellipsoids Using Generalized Copositive Programming, arXiv:1807.07507v4, Theorem 1, display (2), p.6; cone(S) as conic hull, notation, p.5

import Mathlib
import Definitions.Def_MinVolEllipsoid_lift

namespace MinVolEllipsoid

/-- **The cone `𝒦 = cone({[x; 1] : x ∈ 𝒫})`** (Mittal & Hanasusanto, arXiv:1807.07507v4,
Theorem 1, display (2), p.6; `cone(S)` is the conic hull of `S`, notation, p.5).

`liftCone P` is the conic hull of the lifted set `{[x; 1] : x ∈ P} ⊆ ℝᴷ⁺¹`: the set of all finite
nonnegative combinations `∑ₛ λₛ [xₛ; 1]` with `λₛ ≥ 0` and `xₛ ∈ P`. The empty combination
(`m = 0`) gives `0`, so `0 ∈ liftCone P`; no closure is taken.

**Formalization Note** `ℝᴷ⁺¹` is `Fin n ⊕ Unit → ℝ` with the paper's last coordinate as the
`Unit` coordinate (see `MinVolEllipsoid.lift`). The conic hull is written out as finite nonnegative
combinations, the form used in the proof of Lemma 1 (p.6). -/
def liftCone {n : ℕ} (P : Set (Fin n → ℝ)) : Set (Fin n ⊕ Unit → ℝ) :=
  {v | ∃ (m : ℕ) (c : Fin m → ℝ) (x : Fin m → Fin n → ℝ),
    (∀ s, 0 ≤ c s) ∧ (∀ s, x s ∈ P) ∧ v = ∑ s, c s • lift (x s)}

end MinVolEllipsoid


