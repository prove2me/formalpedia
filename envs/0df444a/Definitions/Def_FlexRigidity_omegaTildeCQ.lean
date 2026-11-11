-- Prove2me | Definitions.Def_FlexRigidity_omegaTildeCQ
-- name    : FlexRigidity_omegaTildeCQ
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:31:38.820887+00:00
-- url     : https://prove2.me/theorems/b075872b-e22e-4b76-843e-bc35d1e6a09b
-- title:
--   The comparison state $\tilde\omega^\mu_{X_iS_iRQ^{\mathrm A}_iQ^{\mathrm B}_i}$, eqs. (56)–(57)
-- statement:
--   $\tilde\omega^{\mu,x}_{S_i}=(1-\mu)|\phi^x\rangle\langle\phi^x|+\mu I/|S_i|$ and $\tilde\omega^\mu=\sum_xP_X(x)|x\rangle\langle x|\otimes\tilde\omega^{\mu,x}_{S_i}\otimes\zeta^x_{RQ^{\mathrm A}_iQ^{\mathrm B}_i}$, with $\zeta^x_{RQ^{\mathrm A}Q^{\mathrm B}}$ the marginal of $|\zeta^x\rangle\langle\zeta^x|$.
-- source:
--   Arqand, Kundu, Tan, Flexible rigidity: Compiling generic trusted-preparation protocols into sequential device-independent protocols, arXiv:2610.00444 (artifact sha256 8c67699d…), eqs. (56)–(57), p. 49

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P35
import Definitions.Def_FlexRigidity_zetaX
import Definitions.Def_FlexRigidity_phiX
import Definitions.Def_ObliviousRSP_pureState
import Definitions.Def_FlexRigidity_depol
set_option autoImplicit false

open scoped Matrix ComplexOrder ENNReal
open Filter Topology
open QAlgorithms (Superop IsChannel krausApply idTensorSuperop piSuperop)
open QAlgorithms.Papers.Independent.Dependency50.P35 (tr Density Dominates divergence rawTrace spectralPower maxRelative POVM leftMarginal rightMarginal)

noncomputable section

namespace FlexRigidity

/-- **The depolarized comparison state `ω̃^µ_{X_i S_i R Q^A_i Q^B_i}`, eqs. (56)–(57)**
(Arqand–Kundu–Tan, *Flexible rigidity*, arXiv:2610.00444, artifact sha256 8c67699d…, p. 49):
`ω̃^{µ,x}_{S_i} = (1−µ)|ϕ^x⟩⟨ϕ^x| + µ I_{S_i}/|S_i|` and
`ω̃^µ = Σ_x P_X(x) |x⟩⟨x| ⊗ ω̃^{µ,x}_{S_i} ⊗ ζ^x_{R Q^A_i Q^B_i}`, with `ζ^x_{RQ^AQ^B}` the marginal of
`|ζ^x⟩⟨ζ^x|` on `R Q^A_i Q^B_i`. -/
def omegaTildeCQ {X Y A B SA SB R : Type} [Fintype A] [Fintype SA] [Fintype SB] [Fintype R]
    [DecidableEq X] [DecidableEq A] [DecidableEq SA] [DecidableEq SB]
    (Rz : Realization X Y A B SA SB) {I : StoredImpl X Y A B} (Ex : Extraction X Y A B SA SB I)
    (i : ℕ) (ρ : R × (Fin (I.dA i) × Fin (I.dB i)) → ℂ) (μ : ℝ) :
    Matrix (X × ((A × SA × SB) × (R × (Fin (Ex.qA i) × Fin (Ex.qB i)))))
      (X × ((A × SA × SB) × (R × (Fin (Ex.qA i) × Fin (Ex.qB i))))) ℂ :=
  Matrix.of fun p q =>
    if p.1 = q.1 then
      (Rz.PX p.1 : ℂ) * Matrix.kronecker (depol μ (ObliviousRSP.pureState (phiX Rz p.1)))
        (rightMarginal (ObliviousRSP.pureState (zetaX Ex i ρ p.1))) p.2 q.2
    else 0

end FlexRigidity


