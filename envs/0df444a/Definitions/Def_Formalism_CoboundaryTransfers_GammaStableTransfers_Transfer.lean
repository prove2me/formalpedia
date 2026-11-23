-- Prove2me | Definitions.Def_Formalism_CoboundaryTransfers_GammaStableTransfers_Transfer
-- name    : Formalism_CoboundaryTransfers_GammaStableTransfers_Transfer
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:41:30.796966+00:00
-- url     : https://prove2.me/theorems/c7c2cf00-3c77-4d43-87e5-7ccce22627c5
-- title:
--   Transfer
-- statement:
--   Definitions and structural lemmas for Transfer, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CoboundaryTransfers/GammaStableTransfers/Transfer.lean

import Definitions.Def_Formalism_LagrangeIdealLifts_LiftLagrangeIdealInt
import Definitions.Def_Formalism_CoboundaryTransfers_StatementBridge
import Definitions.Def_Formalism_CoboundaryTransfers_StatementTransfer
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.CoboundaryTransfers
open Formalism
section Maps
variable {ℓ : ℕ} [Fact ℓ.Prime] {A : Type} [CommRing A] [Algebra ℤ_[ℓ] A]
  {B : Base ℤ_[ℓ] A} {M : ℕ}
def homToLIFT {D D' : Type} [AddCommGroup D] [Module A D] [Module ℤ_[ℓ] D]
    [IsScalarTower ℤ_[ℓ] A D] [AddCommGroup D'] [Module A D'] [Module ℤ_[ℓ] D']
    [IsScalarTower ℤ_[ℓ] A D'] {W : WachMod B M D} {W' : WachMod B M D'} (F : Hom W W')
    (u : ℤ_[ℓ]ˣ) (hφ : B.φ B.X = B.X * B.Q) (hγX : B.GammaX (u : ℤ_[ℓ])) (hγQ : B.GammaQ) :
    LIFT.Hom (W.toLIFT u hφ hγX hγQ) (W'.toLIFT u hφ hγX hγQ) where
  f := F.f
  φ_comm := F.φ_comm
  γ_comm := F.γ_comm
  N_le := F.N_le
def sesToLIFT {D₀ D₁ D₂ : Type}
    [AddCommGroup D₀] [Module A D₀] [Module ℤ_[ℓ] D₀] [IsScalarTower ℤ_[ℓ] A D₀]
    [AddCommGroup D₁] [Module A D₁] [Module ℤ_[ℓ] D₁] [IsScalarTower ℤ_[ℓ] A D₁]
    [AddCommGroup D₂] [Module A D₂] [Module ℤ_[ℓ] D₂] [IsScalarTower ℤ_[ℓ] A D₂]
    {W₀ : WachMod B M D₀} {W₁ : WachMod B M D₁} {W₂ : WachMod B M D₂} (S : SES W₀ W₁ W₂)
    (u : ℤ_[ℓ]ˣ) (hφ : B.φ B.X = B.X * B.Q) (hγX : B.GammaX (u : ℤ_[ℓ])) (hγQ : B.GammaQ) :
    LIFT.SES (W₀.toLIFT u hφ hγX hγQ) (W₁.toLIFT u hφ hγX hγQ) (W₂.toLIFT u hφ hγX hγQ) where
  ι := homToLIFT S.ι u hφ hγX hγQ
  π := homToLIFT S.π u hφ hγX hγQ
  ι_inj := S.ι_inj
  exact := S.exact
  sat := S.sat
end Maps
end Formalism.CoboundaryTransfers


