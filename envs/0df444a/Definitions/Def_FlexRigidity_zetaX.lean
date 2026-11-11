-- Prove2me | Definitions.Def_FlexRigidity_zetaX
-- name    : FlexRigidity_zetaX
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:29:31.945121+00:00
-- url     : https://prove2.me/theorems/df08d8e6-f11b-41cf-bdc7-97c97a9fa5d6
-- title:
--   The coherent extracted vector $|\zeta^x\rangle$, eq. (54)
-- statement:
--   $|\zeta^x\rangle_{S_iRQ^{\mathrm A}_iQ^{\mathrm B}_i}=\sum_a|a\rangle_{A_i}(I_R\otimes V^{\mathrm A}_i\otimes V^{\mathrm B}_i)H^x_{i,a}\big(|\rho\rangle_{RM^{\mathrm A}_iM^{\mathrm B}_i}\otimes|00\rangle_{M'^{\mathrm A}_iM'^{\mathrm B}_i}\big)$, the coherent version of the real state after the extraction isometries.
-- source:
--   Arqand, Kundu, Tan, Flexible rigidity: Compiling generic trusted-preparation protocols into sequential device-independent protocols, arXiv:2610.00444 (artifact sha256 8c67699d…), eq. (54), p. 48

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P35
import Definitions.Def_FlexRigidity_Extraction
import Definitions.Def_FlexRigidity_withAnc
set_option autoImplicit false

open scoped Matrix ComplexOrder ENNReal
open Filter Topology
open QAlgorithms (Superop IsChannel krausApply idTensorSuperop piSuperop)
open QAlgorithms.Papers.Independent.Dependency50.P35 (tr Density Dominates divergence rawTrace spectralPower maxRelative POVM leftMarginal rightMarginal)

noncomputable section

namespace FlexRigidity

/-- **The coherent extracted vector `|ζ^x⟩_{S_i R Q^A_i Q^B_i}`, eq. (54)** (Arqand–Kundu–Tan,
*Flexible rigidity*, arXiv:2610.00444, artifact sha256 8c67699d…, p. 48):
`|ζ^x⟩ = Σ_a |a⟩_{A_i} (I_R ⊗ V^A_i ⊗ V^B_i) H^x_{i,a} (|ρ⟩_{R M^A_i M^B_i} ⊗ |00⟩_{M′^A_i M′^B_i})`.

**Formalization Note** The vector is indexed by `S_i × Q` with `S_i = A_i S^A_i S^B_i` and
`Q = R Q^A_i Q^B_i` (fixed reordering of tensor factors). -/
def zetaX {X Y A B SA SB R : Type} [Fintype R] {I : StoredImpl X Y A B}
    (Ex : Extraction X Y A B SA SB I) (i : ℕ) (ρ : R × (Fin (I.dA i) × Fin (I.dB i)) → ℂ) (x : X) :
    (A × SA × SB) × (R × (Fin (Ex.qA i) × Fin (Ex.qB i))) → ℂ :=
  fun p => ∑ ma : Fin (I.dA i) × Fin (I.kA i + 1), ∑ mb : Fin (I.dB i) × Fin (I.kB i + 1),
    Ex.VA i (p.1.2.1, p.2.2.1) ma * Ex.VB i (p.1.2.2, p.2.2.2) mb *
      ∑ ma' : Fin (I.dA i) × Fin (I.kA i + 1), I.H i x p.1.1 ma ma' * withAnc I i ρ (p.2.1, (ma', mb))

end FlexRigidity


