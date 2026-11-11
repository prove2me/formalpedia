-- Prove2me | Definitions.Def_FlexRigidity_etaX
-- name    : FlexRigidity_etaX
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:31:23.471723+00:00
-- url     : https://prove2.me/theorems/6930b53d-f245-4563-9965-83ca53ec90ff
-- title:
--   The overlap error $\eta_x$, eq. (55)
-- statement:
--   $\eta_x=1-\langle\phi^x|\zeta^x_{S_i}|\phi^x\rangle$, where $\zeta^x_{S_i}$ is the marginal of $|\zeta^x\rangle\langle\zeta^x|$ on $S_i$.
-- source:
--   Arqand, Kundu, Tan, Flexible rigidity: Compiling generic trusted-preparation protocols into sequential device-independent protocols, arXiv:2610.00444 (artifact sha256 8c67699d…), eq. (55), p. 48

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P35
import Definitions.Def_FlexRigidity_phiX
import Definitions.Def_FlexRigidity_zetaX
set_option autoImplicit false

open scoped Matrix ComplexOrder ENNReal
open Filter Topology
open QAlgorithms (Superop IsChannel krausApply idTensorSuperop piSuperop)
open QAlgorithms.Papers.Independent.Dependency50.P35 (tr Density Dominates divergence rawTrace spectralPower maxRelative POVM leftMarginal rightMarginal)

noncomputable section

namespace FlexRigidity

/-- **The overlap error `η_x = 1 − ⟨ϕ^x|ζ^x_{S_i}|ϕ^x⟩`, eq. (55)** (Arqand–Kundu–Tan, *Flexible
rigidity*, arXiv:2610.00444, artifact sha256 8c67699d…, p. 48), where `ζ^x_{S_i}` is the marginal
of `|ζ^x⟩⟨ζ^x|` on `S_i`: `⟨ϕ^x|ζ^x_{S_i}|ϕ^x⟩ = Σ_q |Σ_s conj(ϕ^x_s) ζ^x_{s,q}|²`. -/
def etaX {X Y A B SA SB R : Type} [Fintype A] [Fintype SA] [Fintype SB] [Fintype R]
    (Rz : Realization X Y A B SA SB) {I : StoredImpl X Y A B} (Ex : Extraction X Y A B SA SB I)
    (i : ℕ) (ρ : R × (Fin (I.dA i) × Fin (I.dB i)) → ℂ) (x : X) : ℝ :=
  1 - ∑ q : R × (Fin (Ex.qA i) × Fin (Ex.qB i)),
    ‖∑ s : A × SA × SB, star (phiX Rz x s) * zetaX Ex i ρ x (s, q)‖ ^ 2

end FlexRigidity


