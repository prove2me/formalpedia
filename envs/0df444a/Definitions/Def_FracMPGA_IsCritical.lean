-- Prove2me | Definitions.Def_FracMPGA_IsCritical
-- name    : FracMPGA_IsCritical
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:40:41.24982+00:00
-- url     : https://prove2.me/theorems/df06ff30-739e-46d1-a16b-b6911de3c303
-- title:
--   Definition 2: critical point of $F$
-- statement:
--   Let $F$ be the extended objective (8). A point $x^\star\in\operatorname{dom}F$ is a **critical point** of $F$ if
--   $$
--   0\in\hat\partial f(x^\star)+\nabla h(x^\star)-F(x^\star)\,\partial g(x^\star),
--   $$
--   where $\hat\partial f$ is the Fréchet subdifferential and $\partial g$ the subdifferential of the convex function $g$.
--
--   This is the stationarity notion to which the paper's algorithms converge.
--
--   **Formalization Note** The Fréchet subdifferential is the published `NonconvexSplitting.Shared.IsRegularSubgrad`; $x^\star\in\operatorname{dom}F$ is part of the definition, so $F(x^\star)$ is a real number.
-- source:
--   Zhou, Zhang, Li, An equivalent reformulation and multi-proximity gradient algorithms for a class of nonsmooth fractional programming, arXiv:2311.00957v2, §3, p.10, Definition 2

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_FracMPGA_Problem
import Definitions.Def_ProxAlg_FixedPoint_Basic

open NonconvexSplitting.Shared

namespace FracMPGA

/-- **Definition 2 (critical points of `F`)** of Zhou, Zhang, Li, arXiv:2311.00957v2, p.10:
`x⋆ ∈ dom(F)` is a critical point of `F` if `0 ∈ ∂̂f(x⋆) + ∇h(x⋆) − F(x⋆) ∂g(x⋆)`, where `∂̂f` is
the Fréchet subdifferential (p.5) and `∂g` the subdifferential of the convex function `g`.

**Formalization Note** `∂̂f` is `NonconvexSplitting.Shared.IsRegularSubgrad` (the ε-form of the
liminf definition of p.5), `∂g(x)` is `ProxAlg.FixedPoint.subdifferential (fun z => (g z : EReal)) x`, `∇h` is Mathlib's
`gradient`, and `F(x⋆)` is the real number `(F x⋆).toReal`, which is `F(x⋆)` because
`x⋆ ∈ dom(F)` is part of the definition. -/
def IsCritical {n N : ℕ} (P : Problem n N) (x : Vec n) : Prop :=
  P.F x ≠ ⊤ ∧ ∃ u v : Vec n, IsRegularSubgrad P.f x u ∧
    v ∈ ProxAlg.FixedPoint.subdifferential (fun z => (P.g z : EReal)) x ∧
    u + gradient P.h x - (P.F x).toReal • v = 0

end FracMPGA


