-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardResidueFieldAdjoinUnitaryProd
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardResidueFieldAdjoinUnitaryProd
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-24T14:53:07.185044+00:00
-- url     : https://prove2.me/theorems/0e3485ed-ba60-4e52-90b5-dce6c4198037
-- title:
--   Card Residue Field Adjoin Unitary Prod
-- statement:
--   Definitions and structural lemmas for Card Residue Field Adjoin Unitary Prod, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CardResidueFieldAdjoinUnitaryProd.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OverExtAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocalRingOfIdem
import Theorems.Thm_GlobalTheory_UnitLemma_Orbit_adjoin_stable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.UnitLemma.ResDeg
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Orbit Polynomial IsLocalRing
end GlobalTheory.UnitLemma.ResDeg
namespace GlobalTheory.UnitLemma.ResDeg
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Orbit Polynomial IsLocalRing
variable {K : UQ}
def sigmaAdj (B : InvAlg K) (hu : B.g * B.σ B.g = 1) (hi : IsIntegral K.O B.g) :
    Algebra.adjoin K.O ({B.g} : Set B.A) ≃+* Algebra.adjoin K.O ({B.g} : Set B.A) where
  toFun y := ⟨B.σ (y : B.A), adjoin_stable B hu hi y.2⟩
  invFun y := ⟨B.σ (y : B.A), adjoin_stable B hu hi y.2⟩
  left_inv y := Subtype.ext (B.σ_σ (y : B.A))
  right_inv y := Subtype.ext (B.σ_σ (y : B.A))
  map_mul' x y := Subtype.ext (map_mul B.σ (x : B.A) (y : B.A))
  map_add' x y := Subtype.ext (map_add B.σ (x : B.A) (y : B.A))
end GlobalTheory.UnitLemma.ResDeg


