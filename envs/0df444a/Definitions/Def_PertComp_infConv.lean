-- Prove2me | Definitions.Def_PertComp_infConv
-- name    : PertComp_infConv
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:12:19.380226+00:00
-- url     : https://prove2.me/theorems/e6417371-04f2-4311-a233-f88dabee2ab6
-- title:
--   Infimal convolution $f\,\Box\,\ell$
-- statement:
--   The **infimal convolution** of $f$ and $\ell$ is
--   $$(f\,\Box\,\ell)(x)=\inf_{y}\big(f(y)+\ell(x-y)\big)\in[-\infty,+\infty].$$
--   It appears in the objective (1.2) as $g\,\Box\,\ell$, in the dual objective (3.11) as $h^*\Box\widetilde{f^*}(\cdot,\xi^*)$, and in Lemmas 2.6 and 2.7.
--
--   **Formalization Note** Computed in `EReal`. Every use in the mission is on functions that never take $-\infty$.
-- source:
--   L. M. Briceño-Arias, P. L. Combettes, A Perturbation Framework for Convex Minimization and Monotone Inclusion Problems with Nonlinear Compositions, arXiv:2111.11421v4, (2.9), p.5

import Mathlib

namespace PertComp

/-- Briceño-Arias, Combettes, arXiv:2111.11421v4, (2.9), p.5: the *infimal convolution*
`(f □ ℓ)(x) = inf_{y} (f(y) + ℓ(x − y))`, a function into `[−∞, +∞]`.

**Formalization Note.** Computed in `EReal`. The paper defines it for proper `ℓ`; every use in
the mission is on functions that never take `−∞`, so no `⊥ + ⊤` sum arises. -/
noncomputable def infConv {V : Type*} [AddCommGroup V] (f ℓ : V → EReal) (x : V) : EReal :=
  ⨅ y : V, f y + ℓ (x - y)

end PertComp


