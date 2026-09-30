-- Prove2me | Definitions.Def_Smooth4AlgebraHomology
-- name    : Smooth4AlgebraHomology
-- status  : Definition
-- author  : @ryanshin
-- created : 2026-09-05T19:27:18.01001+00:00
-- url     : https://prove2.me/theorems/03345c44-ac25-4419-bd93-b6273df594a5
-- title:
--   Cycles modulo boundaries for a finite linear complex
-- statement:
--   Let $d:V\to V$ be a linear map over a field. Its cycle space is $\ker d$. The subspace called boundaries in cycles is $\ker d\cap\operatorname{im}d$, represented inside $\ker d$; the homology space is its quotient. When $d^2=0$, all boundaries are cycles, so this is precisely the usual homology $\ker d/\operatorname{im}d$.
--
--   Every theorem using this construction as square-zero homology explicitly assumes $d^2=0$. The definition itself works for an arbitrary linear map.
-- source:
--   Newly authored from cycle21_corner_budget_independent.md, §1 (joint kernel/projection argument), SHA-256 89aa667aee6440fe989e7664eec02f5a7a60010d1d86a77dd094bdf95ba8bdba

import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions

set_option autoImplicit false

namespace Smooth4Algebra

/-- Boundaries viewed inside the cycle space.  When `d ∘ d = 0`, these
are exactly the boundaries of the square-zero complex. -/
def boundariesInCycles {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (d : V →ₗ[K] V) : Submodule K (LinearMap.ker d) :=
  (LinearMap.range d).comap (LinearMap.ker d).subtype

/-- Actual vector-space homology, represented as cycles modulo boundaries.
Every theorem using it as homology explicitly assumes square-zero. -/
abbrev Homology {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (d : V →ₗ[K] V) :=
  (LinearMap.ker d) ⧸ boundariesInCycles d

end Smooth4Algebra


