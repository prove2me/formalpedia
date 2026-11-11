-- Prove2me | Definitions.Def_UnitaryQIPPSPACE_unitaryQIP
-- name    : UnitaryQIPPSPACE_unitaryQIP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:37:00.456204+00:00
-- url     : https://prove2.me/theorems/bfb934d0-1004-4a8f-b538-646c5edb0352
-- title:
--   The class $\mathsf{unitaryQIP}$
-- statement:
--   $$\mathsf{unitaryQIP}:=\bigcap_{p(n)\in\mathrm{poly}(n)}\mathsf{unitaryQIP}_{0,\frac12,\frac1p},$$
--   the intersection ranging over all polynomials: perfect completeness, soundness threshold $1/2$ and arbitrarily small inverse-polynomial synthesis error.
--
--   **Formalization Note** The intersection is over all polynomials $p$ with natural-number coefficients at error $1/(p(n)+1)$, which equals the intersection over all real polynomials $p\ge1$.
-- source:
--   He, Ou, Zhao, unitaryQIP = unitaryPSPACE, arXiv:2611.02819 (held version, sha256 9e357a00…ead793), §1.1, p.3 (PDF p.5)

import Mathlib
import Definitions.Def_UnitaryQIPPSPACE_unitaryQIPc

namespace UnitaryQIPPSPACE

/-- **The subscript-free class `unitaryQIP`** (He, Ou, Zhao, *unitaryQIP = unitaryPSPACE*,
arXiv:2611.02819, held version sha256 9e357a00…, §1.1, p. 3 (PDF p. 5)): "we define the following
subscript-free classes by requiring arbitrarily inverse-polynomial synthesis error, perfect
completeness and soundness threshold 1/2: `unitaryQIP := ⋂_{p(n) ∈ poly(n)} unitaryQIP_{0, 1/2, 1/p}`,
where both intersections range over all polynomials."

**Formalization Note** The intersection is over every polynomial `p` with natural-number
coefficients, at synthesis error `1/(p(n) + 1)`; as for `unitaryPSPACE` this is the intersection
over all (real) polynomials `p ≥ 1`. -/
def unitaryQIP : Set UFam :=
  ⋂ p : Polynomial ℕ, unitaryQIPc (fun _ => 0) (fun _ => 1 / 2) (fun n => 1 / (((p.eval n : ℕ) : ℝ) + 1))

end UnitaryQIPPSPACE


