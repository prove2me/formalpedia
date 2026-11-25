-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_MemPadicAlgClValuationSubringIffNormLeOne
-- name    : Development_AbelianVarietyTheory_Proofs_DegenerationProofs_MemPadicAlgClValuationSubringIffNormLeOne
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T14:32:18.706808+00:00
-- url     : https://prove2.me/theorems/b7a42766-02f1-4332-873e-380ebb5544cc
-- title:
--   Mem Padic Alg Cl Valuation Subring Iff Norm Le One
-- statement:
--   Definitions and structural lemmas for Mem Padic Alg Cl Valuation Subring Iff Norm Le One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/MemPadicAlgClValuationSubringIffNormLeOne.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosurePadicInt
import Theorems.Thm_GlobalTheory_mem_integralClosure_padicInt_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
local notation "OO" p:max => (Valuation.valuationSubring (Valued.v : Valuation (PadicAlgCl p) NNReal))
local notation "cPt" p:max => (IsLocalRing.closedPoint (OO p) : Sp (OO p))
local notation "gPt" p:max => spMap (ValuationSubring.subtype (OO p))
namespace GlobalTheory
section
variable {p : ℕ} [Fact p.Prime]
theorem mem_padicAlgCl_valuationSubring_iff_norm_le_one (x : PadicAlgCl p) :
    x ∈ OO p ↔ ‖x‖ ≤ 1 := by
  rw [Valuation.mem_valuationSubring_iff, ← NNReal.coe_le_coe]
  rfl
noncomputable def integralClosureToPadicAlgClIntegers
    (K : IntermediateField ℚ_[p] (PadicAlgCl p)) : integralClosure ℤ_[p] K →+* OO p :=
  (K.val.toRingHom.comp (integralClosure ℤ_[p] K).val.toRingHom).codRestrict (OO p) fun x =>
    (mem_padicAlgCl_valuationSubring_iff_norm_le_one _).mpr
      ((mem_integralClosure_padicInt_iff K _).mp x.2)
end
end GlobalTheory


