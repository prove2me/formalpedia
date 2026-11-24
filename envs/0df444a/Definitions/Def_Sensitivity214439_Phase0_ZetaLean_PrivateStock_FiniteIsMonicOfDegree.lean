-- Prove2me | Definitions.Def_Sensitivity214439_Phase0_ZetaLean_PrivateStock_FiniteIsMonicOfDegree
-- name    : Sensitivity214439_Phase0_ZetaLean_PrivateStock_FiniteIsMonicOfDegree
-- status  : Definition
-- author  : @yousofy
-- created : 2026-11-24T12:49:23.348799+00:00
-- url     : https://prove2.me/theorems/c7d6434c-d485-4a54-872e-c85135996b3b
-- title:
--   Finiteness of monic polynomials of a fixed degree
-- statement:
--   Over a finite field F, the type of monic polynomials of any prescribed natural degree n is finite. The bundled proof transports finiteness from the finite coefficient-vector type Fin n → F through the monic-polynomial equivalence.
-- source:
--   Upstream https://github.com/teal-sea/zeta-lab/tree/main/lean/ZetaLean/PrivateStock (Apache-2.0); checked task source research/hec-lean433/ZetaLean/PrivateStock/FiniteIsMonicOfDegree.lean lines 21–24; SHA256 e5e9b3e00b40f0d5d4d655c83ea723e2d8056571b3c98134afab987c0b3b8cb3.

import Definitions.Def_Sensitivity214439_Phase0_ZetaLean_PrivateStock_CardIsMonicOfDegree
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.SetTheory.Cardinal.Finite

namespace Polynomial
end Polynomial



@[expose] public section

/-!
# Finiteness of the set of monic polynomials of a given degree

Over a finite field `F`, the monic polynomials of degree `n` are parametrised by their `n`
lower-order coefficients (`Polynomial.isMonicOfDegreeEquivFun`), so there are only finitely many
of them. This is the finiteness underlying the count `Polynomial.card_isMonicOfDegree`.
-/

set_option autoImplicit false

open scoped Polynomial

namespace Polynomial

/-- Over a finite field there are only finitely many monic polynomials of a given degree. -/
theorem finite_isMonicOfDegree {F : Type*} [Field F] [Finite F] (n : ℕ) :
    Finite {f : F[X] // Polynomial.IsMonicOfDegree f n} :=
  Finite.of_equiv _ (isMonicOfDegreeEquivFun F n).symm

end Polynomial

end


