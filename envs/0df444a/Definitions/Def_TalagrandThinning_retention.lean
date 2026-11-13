-- Prove2me | Definitions.Def_TalagrandThinning_retention
-- name    : TalagrandThinning_retention
-- status  : Definition
-- author  : @iris
-- created : 2026-11-12T06:41:42.201821+00:00
-- url     : https://prove2.me/theorems/1d4ae427-22a0-4f5a-8911-76c7dcaea7df
-- title:
--   The retention law $T_t\nu$ (independent thinning)
-- statement:
--   For $t\in(0,1)$ and a law $\nu$ on the cube, the **retention law** is
--
--   $$T_t\nu=\mathcal L(J\cap X_t),\qquad J\sim\nu,\ X_t\sim\mu_t \text{ independent of } J.$$
--
--   Each element of the random set $J$ is kept independently with probability $t$.
--
--   **Formalization Note** Independence is the product measure $\nu\otimes\mu_t$ on pairs $(J,X_t)$, and $T_t\nu$ is its image under $(J,x)\mapsto J\cap x$. The map is measurable because every subset of the finite cube is measurable.
-- source:
--   Fang & Wang, A Note on a Result of Chen Li: the Thinning Problem via the Kernel Method, arXiv:2609.18458 (held version dated Sep 12, 2026, sha256 68a0f38d…), Definition 1.1, p.2

import Mathlib
import Definitions.Def_TalagrandThinning_prodLaw

set_option autoImplicit false

open MeasureTheory

namespace TalagrandThinning

/-- The retention law `T_t ν = L(J ∩ X_t)`, where `J ∼ ν` and `X_t ∼ µ_t` is independent of `J`
(arXiv:2609.18458, held version dated Sep 12, 2026, sha256 68a0f38d…, Definition 1.1, p.2).

**Formalization Note** Independence is encoded by the product measure `ν ⊗ µ_t` on pairs
`(J, X_t)`; the law of `J ∩ X_t` is its push-forward under `(J, x) ↦ J ⊓ x`. The map is measurable
because every subset of the finite cube is measurable. The paper takes `t ∈ (0,1)`; the theorems
that use `retention` assume it. -/
noncomputable def retention {N : ℕ} (t : ℝ) (ν : Measure (Cube N)) : Measure (Cube N) :=
  (ν.prod (prodLaw N t)).map (fun z : Cube N × Cube N => z.1 ⊓ z.2)

end TalagrandThinning


