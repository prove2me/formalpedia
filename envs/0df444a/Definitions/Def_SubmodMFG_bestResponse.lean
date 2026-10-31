-- Prove2me | Definitions.Def_SubmodMFG_bestResponse
-- name    : SubmodMFG_bestResponse
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:16:08.246306+00:00
-- url     : https://prove2.me/theorems/f288ab7f-e2a6-48db-a052-eef7a81d471e
-- title:
--   The best-response set $R(\mu)$
-- statement:
--   For $\mu\in L$, the **set of best responses** $R(\mu)\subseteq L$ is the image under the projection $p:E\to L$ of the optimal strategies:
--   $$
--   R(\mu):=p\Big(\arg\min_{\nu\in E}J(\nu,\mu)\Big).
--   $$
--
--   $R$ is the best-response map of the abstract mean field game; equilibria are its fixed points.
-- source:
--   Dianetti, Ferrari, Fischer, Nendel, A Unifying Framework for Submodular Mean Field Games, arXiv:2201.07850v1, §2.1, p.6 (display before Definition 2.2)

import Mathlib
import Definitions.Def_SubmodMFG_argminSet

namespace SubmodMFG

/-- **The set of best responses `R(µ)`.**
Dianetti, Ferrari, Fischer, Nendel, *A Unifying Framework for Submodular Mean Field Games*,
arXiv:2201.07850v1, §2.1, p.6: "For µ ∈ L, we define the set of best responses R(µ) ⊂ L by
R(µ) := p(arg min_{ν∈E} J(ν, µ))."

`R(µ)` is the image under the projection `p : E → L` of the set of minimizers of `J(·, µ)`.

**Formalization Note.** `J` is curried (`J ν µ = J(ν, µ)`); the image is `Set.image`. -/
def bestResponse {E L : Type*} (p : E → L) (J : E → L → ℝ) (μ : L) : Set L :=
  p '' argminSet J μ

end SubmodMFG


