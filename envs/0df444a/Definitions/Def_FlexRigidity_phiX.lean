-- Prove2me | Definitions.Def_FlexRigidity_phiX
-- name    : FlexRigidity_phiX
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:24:54.721932+00:00
-- url     : https://prove2.me/theorems/e159386d-9940-4015-b1ab-fac7ae4357e5
-- title:
--   The coherent ideal vector $|\phi^x\rangle_{S_i}$, eq. (54)
-- statement:
--   $|\phi^x\rangle_{S_i}=\sum_a|a\rangle_{A_i}(T^x_a\otimes I)|\phi\rangle_{S^{\mathrm A}_iS^{\mathrm B}_i}$, the coherent version of $\omega^x_{S_i}$.
-- source:
--   Arqand, Kundu, Tan, Flexible rigidity: Compiling generic trusted-preparation protocols into sequential device-independent protocols, arXiv:2610.00444 (artifact sha256 8c67699d…), eq. (54), p. 48

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P35
import Definitions.Def_FlexRigidity_Realization
set_option autoImplicit false

open scoped Matrix ComplexOrder ENNReal
open Filter Topology
open QAlgorithms (Superop IsChannel krausApply idTensorSuperop piSuperop)
open QAlgorithms.Papers.Independent.Dependency50.P35 (tr Density Dominates divergence rawTrace spectralPower maxRelative POVM leftMarginal rightMarginal)

noncomputable section

namespace FlexRigidity

/-- **The coherent ideal vector `|ϕ^x⟩_{S_i}`, eq. (54)** (Arqand–Kundu–Tan, *Flexible rigidity*,
arXiv:2610.00444, artifact sha256 8c67699d…, p. 48): `|ϕ^x⟩ = Σ_a |a⟩_{A_i} (T^x_a ⊗ I)|ϕ⟩_{S^A_i S^B_i}`. -/
def phiX {X Y A B SA SB : Type} [Fintype SA] (Rz : Realization X Y A B SA SB) (x : X) :
    A × SA × SB → ℂ :=
  fun s => ∑ sa' : SA, Rz.T x s.1 s.2.1 sa' * Rz.ϕ (sa', s.2.2)

end FlexRigidity


