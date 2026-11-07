-- Prove2me | Definitions.Def_BeatingGV42_FunctionFieldOver
-- name    : BeatingGV42_FunctionFieldOver
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:32:06.257732+00:00
-- url     : https://prove2.me/theorems/a5ea2809-4dee-4d38-81d1-3a788be219bc
-- title:
--   Function field of one variable over $\mathbb F_Q$ (bundled)
-- statement:
--   An **algebraic function field of one variable $F/\mathbb F_Q$ with full constant field $\mathbb F_Q$**, packaged as a single object so that sequences $(F_i/\mathbb F_Q)_{i\ge 1}$ of such fields can be formed (§4.3).
--
--   **Formalization Note** A structure with a carrier field `F` (in the universe of `k`), a `k`-algebra structure, the platform's `AlgebraicCurve.IsCurveOver k F` (principal divisors of degree $0$, finite residue fields, $\Omega_{F/k}$ free of rank $1$), `Algebra.EssFiniteType k F`, and `AlgebraicCurve.ConstantsAreBase k F` ($\mathcal L(0)=k$: $k$ is the full constant field). These are the hypotheses of the platform's `AlgebraicCurve.exists_LPolynomial_of_finite`; every function field of one variable over a finite field with full constant field satisfies them.
-- source:
--   Cohen, Manket, Beating the Gilbert–Varshamov Bound at Alphabet Size 42, manuscript of October 24, 2026 (STOC 2027 submission; held version sha256 da05fc8e…eb595), §3, p.10 (PDF p.12), and §4.3, p.17 (PDF p.19)

import Mathlib
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_IsCurveOver

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

namespace BeatingGV42

/-- **An algebraic function field of one variable `F/F_Q` with full constant field `F_Q`**, bundled
so that sequences `(F_i/F_Q)_i` can be formed (Cohen, Manket, *Beating the Gilbert–Varshamov Bound at Alphabet Size 42*, manuscript of October 24, 2026 (held version sha256 da05fc8e…), §3, p.10 (PDF p.12): "F/F_Q is an algebraic
function field of one variable with full constant field F_Q"; §4.3, p.17 (PDF p.19)).

**Formalization Note** The carrier is a field `F` with a `k`-algebra structure satisfying the
platform's `AlgebraicCurve.IsCurveOver k F` (principal divisors of degree `0`, finite residue fields,
`Ω_{F/k}` free of rank one) and `Algebra.EssFiniteType k F`, together with
`AlgebraicCurve.ConstantsAreBase k F` (`L(0) = k`, i.e. `k` is the full constant field). These are
exactly the hypotheses of the platform's `AlgebraicCurve.exists_LPolynomial_of_finite`, and every
function field of one variable over a finite (hence perfect) field with full constant field satisfies
them. The carrier lives in the universe of `k`. -/
structure FunctionFieldOver (k : Type u) [Field k] where
  /-- The function field `F`. -/
  carrier : Type u
  [instField : Field carrier]
  [instAlgebra : Algebra k carrier]
  [instCurve : AlgebraicCurve.IsCurveOver k carrier]
  [instEFT : Algebra.EssFiniteType k carrier]
  /-- `F_Q` is the full constant field of `F`. -/
  constantsAreBase : AlgebraicCurve.ConstantsAreBase k carrier

attribute [instance] FunctionFieldOver.instField FunctionFieldOver.instAlgebra
  FunctionFieldOver.instCurve FunctionFieldOver.instEFT

end BeatingGV42


