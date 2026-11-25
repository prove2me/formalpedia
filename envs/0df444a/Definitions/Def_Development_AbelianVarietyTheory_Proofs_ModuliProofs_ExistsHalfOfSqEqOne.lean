-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsHalfOfSqEqOne
-- name    : Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsHalfOfSqEqOne
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T16:57:08.5726+00:00
-- url     : https://prove2.me/theorems/61243613-8ef9-5317-a420-ffbc0957e68d
-- title:
--   Exists Half Of Sq Eq One
-- statement:
--   Definitions and structural lemmas for Exists Half Of Sq Eq One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsHalfOfSqEqOne.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsUnitOfLagrangian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_MulVecOfRealVecAddMemSpanPeriodLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_MemPeriodLatticeOfThetaTranslateEqUnitMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_HasSumPolyDerivMulProdAddMatrix
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex Matrix Filter Topology ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Real
namespace GlobalTheory.ThetaPoint
open CanTh
variable {g : ℕ}
def lawSubgroup {Λ V : Type*} [AddCommGroup Λ] [AddCommGroup V] (ι : Λ →+ V) (J : Λ → V → ℂ)
    (hJ : ∀ l z, J l z ≠ 0) (hc : ∀ l m z, J (l + m) z = J l (z + ι m) * J m z) (θ : V → ℂ) :
    AddSubgroup Λ where
  carrier := {l | ∀ z, θ (z + ι l) = J l z * θ z}
  zero_mem' := fun z => by
    have h := hc 0 0 z
    rw [add_zero, map_zero, add_zero] at h
    rw [map_zero, add_zero, (mul_eq_left₀ (hJ 0 z)).1 h.symm, one_mul]
  add_mem' := fun {l m} hl hm z => by
    rw [map_add, add_comm (ι l), ← add_assoc, hl, hm, hc, mul_assoc]
  neg_mem' := fun {l} hl z => by
    have h0 := hc 0 0 z
    rw [add_zero, map_zero, add_zero] at h0
    have h1 := hc l (-l) z
    rw [add_neg_cancel, (mul_eq_left₀ (hJ 0 z)).1 h0.symm] at h1
    have h2 := hl (z + ι (-l))
    rw [add_assoc, ← map_add, neg_add_cancel, map_zero, add_zero] at h2
    rw [h2, ← mul_assoc, mul_comm (J (-l) z), ← h1, one_mul]
end GlobalTheory.ThetaPoint


