-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ThetaLiftGeometry_AgreementAtAlmostAllSplitPrimes
-- name    : Development_AbelianVarietyTheory_BlockTheory_ThetaLiftGeometry_AgreementAtAlmostAllSplitPrimes
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T18:32:47.507391+00:00
-- url     : https://prove2.me/theorems/52bf2e62-249c-40ad-a923-d2b2658d8228
-- title:
--   Agreement At Almost All Split Primes
-- statement:
--   Definitions and structural lemmas for Agreement At Almost All Split Primes, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/ThetaLiftGeometry/AgreementAtAlmostAllSplitPrimes.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataN
import Definitions.Def_Formalism_LocalRingCardinality_DataRows
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_GaloisCohomology_scalRep_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.GaloisCohomology.scalRep_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv


set_option autoImplicit false
open Formalism.BasicNotions Formalism.MainNotions.N
namespace GlobalTheory.IndefiniteRowSideFullHecke.AgreementAtAlmostAllSplitPrimes
def AgreeAtAlmostAllSplit {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂}
    (A : NAut N) (χ χ' : A.CG 1) : Prop :=
  {w : PlE H | IsSplitPl H w ∧ A.locG χ w ≠ A.locG χ' w}.Finite
def HeckeCharEqOfSplit {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂)
    (A : NAut N) : Prop :=
  ∀ χ χ' : A.CG 1, AgreeAtAlmostAllSplit A χ χ' → χ = χ'
example {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂}
    (A : NAut N) (χ : A.CG 1) : AgreeAtAlmostAllSplit A χ χ := by
  simp [AgreeAtAlmostAllSplit]
end GlobalTheory.IndefiniteRowSideFullHecke.AgreementAtAlmostAllSplitPrimes


