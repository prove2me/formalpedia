-- Prove2me | Definitions.Def_IntADSat_Supplement_castVec
-- name    : IntADSat_Supplement_castVec
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:40:18.250132+00:00
-- url     : https://prove2.me/theorems/08ad6aee-b900-4f2a-8051-a25794de085e
-- title:
--   Inclusion $\mathbb Z^n\hookrightarrow\mathbb Q^n$
-- statement:
--   The coordinatewise inclusion $\iota_n:\mathbb Z^n\hookrightarrow\mathbb Q^n$, a $\mathbb Z$-linear map. It is used to form the saturation $\mathrm{Sat}(\Lambda_G)=M_{\mathbb Q}(G)\cap\mathbb Z^n$ of the word lattice and to view the word lattice $\Lambda_G$ inside the rational space $V=\mathbb Q^{V(G)}$ of Section S5.
--
--   **Formalization Note** `Int.castAddHom` applied coordinatewise (`LinearMap.compLeft`).
-- source:
--   Z. Lu, Integral saturation of adjacency-degree lattices, arXiv:2611.01838 (held version, sha256 d1acbc32826e81e9ed42d927759ebc2d62786404cb2c44cedc931020e3631145), §A, p.11 (PDF 12) (Sat(Λ_G)); §S5, p.40 (PDF 41)

import Mathlib

set_option autoImplicit false

namespace IntADSat.Supplement

/-- The inclusion `ℤⁿ ↪ ℚⁿ` of integer vectors into rational vectors, coordinatewise
(Z. Lu, *Integral saturation of adjacency-degree lattices*, arXiv:2611.01838 (held version, sha256 d1acbc32…3631145), §A, p.11 (PDF 12): `Sat(Λ_G) = M_ℚ(G) ∩ ℤⁿ`; §S5, p.40 (PDF 41): lattices in `V = ℚ^{V(G)}`).

**Formalization Note** A `ℤ`-linear map, so that `ℤ`-submodules of `ℤⁿ` can be pushed into `ℚⁿ` and
`ℚ`-subspaces of `ℚⁿ` pulled back to `ℤⁿ`. -/
def castVec (n : ℕ) : (Fin n → ℤ) →ₗ[ℤ] (Fin n → ℚ) :=
  (Int.castAddHom ℚ).toIntLinearMap.compLeft (Fin n)

end IntADSat.Supplement


