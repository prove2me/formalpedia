-- Prove2me | Definitions.Def_FlexRigidity_zetaCQ
-- name    : FlexRigidity_zetaCQ
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:31:25.08021+00:00
-- url     : https://prove2.me/theorems/df99ea36-2a31-432b-bd96-e5346d76e595
-- title:
--   The CQ state $\zeta_{X_iS_iRQ^{\mathrm A}_iQ^{\mathrm B}_i}$, eq. (57)
-- statement:
--   $\zeta=\sum_xP_X(x)|x\rangle\langle x|_{X_i}\otimes|\zeta^x\rangle\langle\zeta^x|$.
-- source:
--   Arqand, Kundu, Tan, Flexible rigidity: Compiling generic trusted-preparation protocols into sequential device-independent protocols, arXiv:2610.00444 (artifact sha256 8c67699d…), eq. (57), p. 49

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P35
import Definitions.Def_FlexRigidity_zetaX
import Definitions.Def_ObliviousRSP_pureState
set_option autoImplicit false

open scoped Matrix ComplexOrder ENNReal
open Filter Topology
open QAlgorithms (Superop IsChannel krausApply idTensorSuperop piSuperop)
open QAlgorithms.Papers.Independent.Dependency50.P35 (tr Density Dominates divergence rawTrace spectralPower maxRelative POVM leftMarginal rightMarginal)

noncomputable section

namespace FlexRigidity

/-- **The CQ state `ζ_{X_i S_i R Q^A_i Q^B_i}`, eq. (57)** (Arqand–Kundu–Tan, *Flexible rigidity*,
arXiv:2610.00444, artifact sha256 8c67699d…, p. 49): `ζ = Σ_x P_X(x) |x⟩⟨x|_{X_i} ⊗ |ζ^x⟩⟨ζ^x|`. -/
def zetaCQ {X Y A B SA SB R : Type} [Fintype R] [DecidableEq X]
    (Rz : Realization X Y A B SA SB) {I : StoredImpl X Y A B} (Ex : Extraction X Y A B SA SB I)
    (i : ℕ) (ρ : R × (Fin (I.dA i) × Fin (I.dB i)) → ℂ) :
    Matrix (X × ((A × SA × SB) × (R × (Fin (Ex.qA i) × Fin (Ex.qB i)))))
      (X × ((A × SA × SB) × (R × (Fin (Ex.qA i) × Fin (Ex.qB i))))) ℂ :=
  Matrix.of fun p q => if p.1 = q.1 then (Rz.PX p.1 : ℂ) * ObliviousRSP.pureState (zetaX Ex i ρ p.1) p.2 q.2 else 0

end FlexRigidity


