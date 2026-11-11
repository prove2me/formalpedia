-- Prove2me | Definitions.Def_FlexRigidity_RoundJ
-- name    : FlexRigidity_RoundJ
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:20:28.144872+00:00
-- url     : https://prove2.me/theorems/0e9ef2ad-e1a7-4a59-9abd-7c4418a0f34a
-- title:
--   The register $J_i$
-- statement:
--   $J_i$ is $Y_iQ^{\mathrm A}_iQ^{\mathrm B}_i$ on generation rounds and $Y_iB_iM^{\mathrm A}_{i+1}M^{\mathrm B}_{i+1}$ on test rounds, the two spaces embedded as orthogonal summands of a common register.
-- source:
--   Arqand, Kundu, Tan, Flexible rigidity: Compiling generic trusted-preparation protocols into sequential device-independent protocols, arXiv:2610.00444 (artifact sha256 8c67699d…), p. 45

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P35

set_option autoImplicit false

open scoped Matrix ComplexOrder ENNReal
open Filter Topology
open QAlgorithms (Superop IsChannel krausApply idTensorSuperop piSuperop)
open QAlgorithms.Papers.Independent.Dependency50.P35 (tr Density Dominates divergence rawTrace spectralPower maxRelative POVM leftMarginal rightMarginal)

noncomputable section

namespace FlexRigidity

/-- **The register `J_i`** of §5.3.1 (Arqand–Kundu–Tan, *Flexible rigidity*, arXiv:2610.00444,
artifact sha256 8c67699d…, p. 45): `Y_i Q^A_i Q^B_i` on generation rounds and
`Y_i B_i M^A_{i+1} M^B_{i+1}` on test rounds, embedded as orthogonal summands of a common register
(`Sum`). -/
abbrev RoundJ (Y B : Type) (qA qB dA' dB' : ℕ) : Type :=
  (Option Y × (Fin qA × Fin qB)) ⊕ (Option Y × Option B × (Fin dA' × Fin dB'))

end FlexRigidity


