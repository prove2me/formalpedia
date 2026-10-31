-- Prove2me | Definitions.Def_MixedManna_primaryStart
-- name    : MixedManna_primaryStart
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:14:21.431986+00:00
-- url     : https://prove2.me/theorems/fb3b6481-097a-4b3b-a097-7db7a50b16da
-- title:
--   The start $S_0$ of the primary ray
-- statement:
--   The primary ray starts at
--   $$
--   S_0=\big(y=0,\ z=z_0\big),\qquad z_0=\max_{j\in M^+,i,k}U_{ijk}R-P ,
--   $$
--   the maximum taken over the segments of goods that carry variables. The primary ray is $\{(0,z):z\ge z_0\}$; its direction is the $z$-unit vector, which the module also names.
--
--   Algorithm 1 starts here; every path considered in the mission begins at $S_0$.
--
--   **Formalization Note** The maximum is a real supremum over a finite type; that type is nonempty under the standing assumptions, so the supremum is the maximum.
-- source:
--   Chaudhury, Garg, McGlaughlin, Mehta, Competitive Allocation of a Mixed Manna, arXiv:2008.02753v1, §5, p.22 (S₀ = {y₀ = 0, z = max U_ijk R − P, v₀ = q + cz})

import Mathlib
import Definitions.Def_MixedManna_LCPVar

namespace MixedManna

variable {N M : Type*} [Fintype N] [Fintype M]

/-- The starting height `z₀ = max_{j∈M⁺, i, k} U_ijk R − P` of the primary ray (p.22), the maximum
over the segments of goods that carry variables. -/
noncomputable def z0 (I : Instance N M) (P R : ℝ) : ℝ :=
  ⨆ σ : {σ : Seg I // IsGood I (segItem σ)}, segSlope σ.1 * R - P

/-- **The start `S₀` of the primary ray** (Chaudhury, Garg, McGlaughlin, Mehta, *Competitive
Allocation of a Mixed Manna*, arXiv:2008.02753v1, p.22): "`S₀ = {y₀ = 0, z = max_{j∈M⁺,i,k}
U_ijk R − P, v₀ = q + cz}`", i.e. the point `y = (p, f, r, s) = 0`, `z = z₀`. The primary ray is
`{(0, z) : z ≥ z₀}`.

**Formalization Note** The maximum is a real `⨆` over the finite type of good segments; under
the standing assumptions that type is nonempty (some agent has `U_ij1 > 0` on a good, and goods
exist by Condition 1), so `⨆` is the maximum. -/
noncomputable def primaryStart (I : Instance N M) (P R : ℝ) : LCPVar I :=
  (0, 0, 0, 0, z0 I P R)

/-- The direction `(y, z) = (0, 1)` of the primary ray. -/
def zUnit (I : Instance N M) : LCPVar I := (0, 0, 0, 0, 1)

end MixedManna


