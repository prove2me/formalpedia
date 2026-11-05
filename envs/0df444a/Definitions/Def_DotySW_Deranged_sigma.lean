-- Prove2me | Definitions.Def_DotySW_Deranged_sigma
-- name    : DotySW_Deranged_sigma
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:35:28.457101+00:00
-- url     : https://prove2.me/theorems/45d99f99-42f6-49c6-a96d-f21f72a56a17
-- title:
--   The action $\sigma$ of $\mathcal B^{(n)}_{r,s}$ on $V^{r,s}$
-- statement:
--   The linear map $\sigma:\mathcal B^{(n)}_{r,s}\to\mathrm{End}(V^{r,s})$ with $\sigma(D)$ the operator of the diagram $D$, the right arrow of the diagram (13):
--
--   $$
--   \sigma(x)=\sum_{D}\mathrm{coord}(x,D)\,\mathrm{diagOp}(D).
--   $$
--
--   **Formalization Note** That $\sigma$ is multiplicative is the milestone `sigma_mul`, not part of the definition.
-- source:
--   Doty, New versions of Schur-Weyl duality, arXiv:0704.1877v1, §3.4, unnumbered and Eq. (13), p. 9

import Mathlib
import Definitions.Def_DotySW_Deranged_coord
import Definitions.Def_DotySW_Deranged_diagOp

namespace DotySW.Deranged

open WalledBrauer.Blocks

/-- **The action `σ` of `B^{(n)}_{r,s}` on `V^{r,s}`.**
Doty, *New versions of Schur-Weyl duality*, arXiv:0704.1877v1, §3.4, unnumbered and Eq. (13), p. 9.

The linear extension to the walled Brauer algebra of `D ↦ diagOp n D`.

**Formalization Note** Defined as a linear map through `coord`, so that no multiplicativity proof
sits in the definition; that `σ` is an algebra representation is the milestone `sigma_mul`. -/
noncomputable def sigma (n r s : ℕ) : WB n r s →ₗ[ℂ] Op n (r + s) where
  toFun x := ∑ D : WalledDiagram r s, coord x D • diagOp n D
  map_add' x y := by
    have h : ∀ D, coord (x + y) D = coord x D + coord y D := fun _ => rfl
    simp only [h, add_smul, Finset.sum_add_distrib]
  map_smul' c x := by
    have h : ∀ D, coord (c • x) D = c * coord x D := fun _ => rfl
    simp only [h, mul_smul, RingHom.id_apply, Finset.smul_sum]

end DotySW.Deranged


