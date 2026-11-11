-- Prove2me | Definitions.Def_UnitaryQIPPSPACE_unitaryPSPACE
-- name    : UnitaryQIPPSPACE_unitaryPSPACE
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:35:12.408778+00:00
-- url     : https://prove2.me/theorems/718a8561-1116-4e9d-98ae-78d443e1068b
-- title:
--   The class $\mathsf{unitaryPSPACE}$
-- statement:
--   $$\mathsf{unitaryPSPACE}:=\bigcap_{p(n)\in\mathrm{poly}(n)}\mathsf{unitaryPSPACE}_{1/p},$$
--   the intersection ranging over all polynomials: the unitary families synthesizable in polynomial space with arbitrarily small inverse-polynomial error.
--
--   **Formalization Note** The intersection is over all polynomials $p$ with natural-number coefficients at error $1/(p(n)+1)$; since the class is monotone in its error and the two families of inverse polynomials are mutually cofinal, this is the intersection over all real polynomials $p\ge1$.
-- source:
--   He, Ou, Zhao, unitaryQIP = unitaryPSPACE, arXiv:2611.02819 (held version, sha256 9e357a00…ead793), §1.1, p.3 (PDF p.5)

import Mathlib
import Definitions.Def_UnitaryQIPPSPACE_unitaryPSPACEd

namespace UnitaryQIPPSPACE

/-- **The subscript-free class `unitaryPSPACE`** (He, Ou, Zhao, *unitaryQIP = unitaryPSPACE*,
arXiv:2611.02819, held version sha256 9e357a00…, §1.1, p. 3 (PDF p. 5)): "we define the following
subscript-free classes by requiring arbitrarily inverse-polynomial synthesis error …
`unitaryPSPACE := ⋂_{p(n) ∈ poly(n)} unitaryPSPACE_{1/p}`, where both intersections range over all
polynomials."

**Formalization Note** The intersection is over every polynomial `p` with natural-number
coefficients, at error `1/(p(n) + 1)`. This is the same set as the intersection over all (real)
polynomials `p ≥ 1`: the class is monotone in its error and the two families of inverse
polynomials are mutually cofinal. -/
def unitaryPSPACE : Set UFam :=
  ⋂ p : Polynomial ℕ, unitaryPSPACEd (fun n => 1 / (((p.eval n : ℕ) : ℝ) + 1))

end UnitaryQIPPSPACE


