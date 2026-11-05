-- Prove2me | Definitions.Def_DotySW_Deranged_corner
-- name    : DotySW_Deranged_corner
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:34:44.167601+00:00
-- url     : https://prove2.me/theorems/8c01c49b-fc0b-4020-81e1-835457259223
-- title:
--   The deranged algebra $e\mathcal B^{(n)}_{r,r}e$
-- statement:
--   The set of all elements $exe$ with $x\in\mathcal B^{(n)}_{r,r}$, where $e$ is the idempotent of the mission. It is the algebra whose dimension is the derangement number $N(2r)$ and is therefore called the deranged algebra.
--
--   **Formalization Note** It is a subspace of the walled Brauer algebra, with the product of that algebra and unit $e$. It is not replaced by a subalgebra of $\mathrm{End}_{\mathrm{GL}_n}(V^{r,r})$.
-- source:
--   Doty, New versions of Schur-Weyl duality, arXiv:0704.1877v1, §4.2, Eq. (17) and unnumbered, p. 11

import Mathlib
import Definitions.Def_DotySW_Deranged_eIdem

namespace DotySW.Deranged

/-- **The deranged algebra `e B^{(n)}_{r,r} e`.**
Doty, *New versions of Schur-Weyl duality*, arXiv:0704.1877v1, §4.2, Eq. (17), and unnumbered, p. 11.

The set of all `e x e` with `x` in the walled Brauer algebra, as a subspace of it.

**Formalization Note** The corner lives inside `WalledBrauerAlgebra`, not inside
`End_{GL_n}(V^{r,r})`. Its multiplication is that of the algebra and its unit is `e`. -/
noncomputable def corner (n r : ℕ) : Submodule ℂ (WB n r r) :=
  LinearMap.range
    ((LinearMap.mulLeft ℂ (eIdem n r)).comp (LinearMap.mulRight ℂ (eIdem n r)))

end DotySW.Deranged


