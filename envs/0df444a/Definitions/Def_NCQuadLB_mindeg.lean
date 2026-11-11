-- Prove2me | Definitions.Def_NCQuadLB_mindeg
-- name    : NCQuadLB_mindeg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T20:27:41.636142+00:00
-- url     : https://prove2.me/theorems/7aad3a8e-e82a-47a4-bae8-76a4a0523a13
-- title:
--   Minimum degree $\mathrm{mindeg}(f)$ of a noncommutative polynomial
-- statement:
--   For a nonzero polynomial $f$ in the free algebra $\mathbb F\langle V\rangle$, $\mathrm{mindeg}(f)$ is the minimum degree of a monomial appearing in $f$ (with nonzero coefficient).
--
--   It measures how many non-constant factors a product must have before its low-degree part vanishes, which is what makes the degree-$d$ projection count only short products.
--
--   **Formalization Note** Coefficients of words are the published `NCFactorClosure607.Circuits.coeffs`. The value is the infimum of the lengths of the words with nonzero coefficient; at $f=0$ it is $0$, a case the source excludes.
-- source:
--   Shastri, Willumsgaard, A Quadratic Lower Bound for Noncommutative Circuits, arXiv:2604.20575 (version of November 2, 2026, sha256 34159453…), §2, p.5

import Mathlib
import Definitions.Def_NCFactorClosure607_Circuits_Polynomials

namespace NCQuadLB

/-- **Minimum degree** (Shastri, Willumsgaard, *A Quadratic Lower Bound for Noncommutative Circuits*,
arXiv:2604.20575, version of November 2, 2026, sha256 34159453…, §2, p.5): for a nonzero
`f ∈ F⟨V⟩`, `mindeg f` is the minimum degree (word length) of a monomial appearing in `f`.

**Formalization Note** Coefficients of words are the published
`NCFactorClosure607.Circuits.coeffs` (through `FreeAlgebra.equivMonoidAlgebraFreeMonoid`). The value
is the infimum in `ℕ` of the lengths of the words with nonzero coefficient; for `f = 0` this set is
empty and the value is `0`, a case the source excludes ("for any nonzero polynomial"). -/
noncomputable def mindeg {F : Type*} [Field F] {V : Type*} (f : FreeAlgebra F V) : ℕ :=
  sInf ((fun w : FreeMonoid V => w.length) '' ↑(NCFactorClosure607.Circuits.coeffs f).support)

end NCQuadLB


