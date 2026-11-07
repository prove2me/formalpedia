-- Prove2me | Definitions.Def_QSDMixing_GU_densityIn
-- name    : QSDMixing_GU_densityIn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:50:17.870357+00:00
-- url     : https://prove2.me/theorems/d523f709-8ae5-4075-9c82-8f9e081850ab
-- title:
--   The density matrices $\mathcal D(\mathcal A)$ of a matrix algebra
-- statement:
--   For a unital $*$-subalgebra $\mathcal A$ of $M_n(\mathbb C)$,
--
--   $$
--   \mathcal D(\mathcal A)=\{\rho\in\mathcal A:\ \rho\succeq0,\ \mathrm{tr}\,\rho=1\}.
--   $$
--
--   All the contraction coefficients and mixing times below range over this set.
-- source:
--   Zhou, Leditzky, A mixing time method for estimating the sample complexity of quantum state discrimination, arXiv:2609.40182 (held version, sha256 62fb68dd…), §2.3.2, p.15

import Mathlib

set_option autoImplicit false
open scoped ComplexOrder

namespace QSDMixing.GU

/-- The density matrices `D(A)` of a unital `*`-subalgebra `A` of `M_n(ℂ)`: the positive semidefinite
elements of `A` with trace `1`.

Zhou, Leditzky, *A mixing time method for estimating the sample complexity of quantum state discrimination*, arXiv:2609.40182 (held version, sha256 62fb68dd…), §2.3.2, p.15. -/
def densityIn {n : Type} [Fintype n] [DecidableEq n] (A : StarSubalgebra ℂ (Matrix n n ℂ)) :
    Set (Matrix n n ℂ) :=
  {ρ | ρ ∈ A ∧ ρ.PosSemidef ∧ ρ.trace = 1}

end QSDMixing.GU


