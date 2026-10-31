-- Prove2me | Definitions.Def_RainsSep_Distill_krausChoi
-- name    : RainsSep_Distill_krausChoi
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T15:57:17.997996+00:00
-- url     : https://prove2.me/theorems/768f85da-0b08-45fc-9d5b-23625c201d7a
-- title:
--   $\rho_i=|A\rangle\langle A|$, the rank-one operator of a Kraus operator
-- statement:
--   For a linear map $A:V\to W$, $\rho_A=|A\rangle\langle A|$ is the positive rank-one operator on $V\otimes W$ built from the vector $|A\rangle$ of Eq. (7), with entries $A_{wv}\overline{A_{w'v'}}$ at $((v,w),(v',w'))$. For a product Kraus representation it gives $\rho_i^{(1)}=|P_i^{(1)}\rangle\langle P_i^{(1)}|$ and $\rho_i^{(2)}$.
--
--   **Formalization Note** The complex conjugate $\overline{\rho_i^{(1)}}$ used in Eqs. (16), (17), (23), (26) is written as the entrywise conjugate of this matrix where it is needed.
-- source:
--   Rains, Entanglement purification via separable superoperators, arXiv:quant-ph/9707002v3, Eq. (18), p. 2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_RainsSep_Distill_opVec

namespace RainsSep.Distill

/-- **`ρ_i = |A⟩⟨A|`, the rank-one operator of a Kraus operator.**
Rains, *Entanglement purification via separable superoperators*, arXiv:quant-ph/9707002v3, Eq. (18), p. 2: "ρ_i(1) = |P_i(1)⟩⟨P_i(1)|, (18) and similarly for ρ_i(2)."

For `A : V → W`, the operator `|A⟩⟨A|` on `V ⊗ W`, with entries
`A_{w v} \overline{A_{w' v'}}` at `((v,w),(v',w'))`.

**Formalization Note.** The paper's overline `\overline{ρ_i(1)}` (complex conjugate, Eqs. (16),
(17), (23), (26)) is written `(krausChoi A).map star` where it is used. -/
noncomputable def krausChoi {V W : Type*} (A : Matrix W V ℂ) : Matrix (V × W) (V × W) ℂ :=
  QAlgorithms.pureDensity (opVec A)

end RainsSep.Distill


