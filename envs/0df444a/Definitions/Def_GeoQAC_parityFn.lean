-- Prove2me | Definitions.Def_GeoQAC_parityFn
-- name    : GeoQAC_parityFn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:29:14.229293+00:00
-- url     : https://prove2.me/theorems/7f46ac03-09c6-495f-95c1-6b2e43580d54
-- title:
--   The parity function $\mathrm{PARITY}_n$
-- statement:
--   The parity function is
--   $$
--   \mathrm{PARITY}_n(x)=\bigoplus_{j=1}^n x_j ,
--   $$
--   which is $1$ exactly when $x$ has an odd number of ones.
--
--   **Formalization Note** $\mathrm{PARITY}_0$ is the constant $0$.
-- source:
--   Dong, Ou, Yao, On the Computational Power of Geometrically Local QAC circuits, arXiv:2604.07178 (version of 2026-11-03), §2.4, p.12

import Mathlib

namespace GeoQAC

/-- The parity function `PARITY_n(x) = ⊕_{j=1}^n x_j` (arXiv:2604.07178, version of 2026-11-03,
§2.4, p.12).

**Formalization Note.** Written as "the number of ones of `x` is odd"; `PARITY_0` is the constant
`false`. -/
def parityFn (n : ℕ) (x : Fin n → Bool) : Bool :=
  decide (Odd (Finset.univ.filter fun j => x j = true).card)

end GeoQAC


