-- Prove2me | Definitions.Def_Sensitivity214439_Phase0_ZetaLean_PrivateStock_CardIsMonicOfDegree
-- name    : Sensitivity214439_Phase0_ZetaLean_PrivateStock_CardIsMonicOfDegree
-- status  : Definition
-- author  : @yousofy
-- created : 2026-11-24T12:36:19.298802+00:00
-- url     : https://prove2.me/theorems/ad0675d1-fb9b-49b8-a9b0-b55e1fa212fd
-- title:
--   Monic degree-n polynomials as coefficient vectors
-- statement:
--   For a field F and natural number n, define an equivalence between monic polynomials of degree n and functions from Fin n to F. A polynomial is represented by its n coefficients below the leading term; its leading coefficient is fixed to be 1. The equivalence passes through the space of polynomials of degree less than n.
-- source:
--   Upstream https://github.com/teal-sea/zeta-lab/tree/main/lean/ZetaLean/PrivateStock (Apache-2.0); checked task source research/hec-lean433/ZetaLean/PrivateStock/CardIsMonicOfDegree.lean lines 27–33; SHA256 f98bbcf7924f2fbdb22875fdffa14387f63c48a48541ecb21153480aef83d8b8.

import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.SetTheory.Cardinal.Finite

namespace Polynomial
end Polynomial



@[expose] public section

/-!
# The number of monic polynomials of a given degree over a finite field

A monic polynomial of degree `n` over `F` is `X ^ n` plus an arbitrary polynomial of degree
less than `n`, and the latter are parametrised by their `n` coefficients. Hence there are
exactly `|F| ^ n` of them.

This is the count that makes `|f| = |F| ^ deg(f)` the right notion of norm on `F[T]`, and it is
the total against which the counts of monic *irreducible* polynomials
(`Polynomial.numMonicIrreducibleOfDegree`) are compared.
-/

set_option autoImplicit false

open scoped Polynomial

namespace Polynomial

/-- Monic polynomials of degree `n` over `F` correspond to polynomials of degree `< n`, hence
to their `n` coefficients. -/
noncomputable def isMonicOfDegreeEquivFun (F : Type*) [Field F] (n : ℕ) :
    {f : F[X] // IsMonicOfDegree f n} ≃ (Fin n → F) :=
  (Equiv.subtypeEquivRight fun f ↦
      (isMonicOfDegree_iff' f n).trans and_comm).trans <|
    (monicEquivDegreeLT n).trans (degreeLTEquiv F n).toEquiv



end Polynomial

end


