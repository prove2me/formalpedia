-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_IsUnitDetOfProductMapNeZero
-- name    : Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_IsUnitDetOfProductMapNeZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T13:00:06.889945+00:00
-- url     : https://prove2.me/theorems/cf0153b8-3265-4ca4-892d-04569abd4eb2
-- title:
--   Is Unit Det Of Product Map Ne Zero
-- statement:
--   Definitions and structural lemmas for Is Unit Det Of Product Map Ne Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/IsUnitDetOfProductMapNeZero.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_CoeffEqZeroOfMemSpanPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_DiscrMulDetEqNormOfAnnihilator
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory.DiscrJacobian
open scoped TensorProduct
section Diagonal
variable {R S B : Type} [CommRing R] [CommRing S] [CommRing B] [Algebra R S] [Algebra S B]
  [Algebra R B] [IsScalarTower R S B]
variable (R S B) in

noncomputable def mu : S ⊗[R] B →ₐ[S] B :=
  Algebra.TensorProduct.lift (Algebra.ofId S B) (AlgHom.id R B) fun _ _ => Commute.all _ _
noncomputable def der (D : Derivation R S S) : S ⊗[R] B →ₗ[R] B :=
  ((mu R S B).toLinearMap.restrictScalars R) ∘ₗ D.toLinearMap.rTensor B
end Diagonal
section Socle
variable {R B C : Type} [CommRing R] [CommRing B] [CommRing C] [Algebra R B] [Algebra R C]
noncomputable def pairing (ρ : B →ₐ[R] C) (ψ : B →ₗ[R] C) : B ⊗[R] B →ₗ[R] C :=
  LinearMap.mul' R C ∘ₗ TensorProduct.map ρ.toLinearMap ψ
end Socle
section Series
open MvPowerSeries IsLocalRing
end Series
end GlobalTheory.DiscrJacobian
namespace GlobalTheory
end GlobalTheory


