-- Prove2me | Definitions.Def_FlexRigidity_omegaX
-- name    : FlexRigidity_omegaX
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:24:32.160027+00:00
-- url     : https://prove2.me/theorems/0ca12fd6-5c49-458f-bb95-ffbf7fb43371
-- title:
--   The ideal state $\omega^x_{S_i}$, eq. (50)
-- statement:
--   $\omega^x_{S_i}=\sum_a|a\rangle\langle a|_{A_i}\otimes(T^x_a\otimes I)|\phi\rangle\langle\phi|(T^x_a\otimes I)$ on $S_i=A_iS^{\mathrm A}_iS^{\mathrm B}_i$; normalized and classical on $A_i$.
-- source:
--   Arqand, Kundu, Tan, Flexible rigidity: Compiling generic trusted-preparation protocols into sequential device-independent protocols, arXiv:2610.00444 (artifact sha256 8c67699d…), eq. (50), p. 46

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

/-- **The ideal state `ω^x_{S_i}`, eq. (50)** (Arqand–Kundu–Tan, *Flexible rigidity*,
arXiv:2610.00444, artifact sha256 8c67699d…, p. 46):
`ω^x_{S_i} = Σ_a |a⟩⟨a|_{A_i} ⊗ (T^x_a ⊗ I)|ϕ⟩⟨ϕ|_{S^A_i S^B_i}(T^x_a ⊗ I)`, on `S_i = A_i S^A_i S^B_i`. -/
def omegaX {X Y A B SA SB : Type} [Fintype SA] [DecidableEq A]
    (Rz : Realization X Y A B SA SB) (x : X) : Matrix (A × SA × SB) (A × SA × SB) ℂ :=
  Matrix.of fun i j =>
    if i.1 = j.1 then
      (∑ sa' : SA, Rz.T x i.1 i.2.1 sa' * Rz.ϕ (sa', i.2.2)) *
        star (∑ sa' : SA, Rz.T x j.1 j.2.1 sa' * Rz.ϕ (sa', j.2.2))
    else 0

end FlexRigidity


