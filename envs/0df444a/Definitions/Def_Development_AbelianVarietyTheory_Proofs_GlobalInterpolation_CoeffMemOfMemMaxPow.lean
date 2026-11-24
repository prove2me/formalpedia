-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_CoeffMemOfMemMaxPow
-- name    : Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_CoeffMemOfMemMaxPow
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T20:35:59.677806+00:00
-- url     : https://prove2.me/theorems/9ec2d5a5-caef-4f3e-910f-793661d6ae60
-- title:
--   Coeff Mem Of Mem Max Pow
-- statement:
--   Definitions and structural lemmas for Coeff Mem Of Mem Max Pow, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/CoeffMemOfMemMaxPow.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_ValuationFrobeniusEpsilon_LiftInvariantsFinrankEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_CoeffXMulPart
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_MonomialOneMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_MaximalIdealLeFiltOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_FiltLePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_NoethLocalHausdorff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_Imports
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ImportsAlt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_EqXMulShiftAdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_MemPowOfCoeffMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ImportsBis
import Theorems.Thm_GlobalTheory_FiltrationMultiplicative_main
import Theorems.Thm_GlobalTheory_FiltrationMultiplicative_mem_max_iff
import Theorems.Thm_GlobalTheory_LocalRingBasicFacts_main
import Theorems.Thm_GlobalTheory_LocalRingFurtherFacts_main
import Theorems.Thm_GlobalTheory_MaximalIdealFiltration_main
import Theorems.Thm_GlobalTheory_MaximalIdealMembership_mem_maximalIdeal_iff
import Theorems.Thm_GlobalTheory_NoetherianLocalHausdorff_noeth_local_hausdorff
import Theorems.Thm_GlobalTheory_PowerSeriesCoeffSum_main
import Theorems.Thm_GlobalTheory_PowerSeriesIdealPowers_main
import Theorems.Thm_GlobalTheory_PowerSeriesIdealPowers_mem_max_iff
import Theorems.Thm_GlobalTheory_PowerSeriesMaximalBound_main
import Theorems.Thm_GlobalTheory_PowerSeriesShift_main

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPowerSeries IsLocalRing Formalism.BasicNotions.V1
namespace GlobalTheory.PsCNL
section Division
variable {σ : Type} {O : Type} [CommRing O]
def divX (i : σ) (f : MvPowerSeries σ O) : MvPowerSeries σ O := fun m => coeff (Finsupp.single i 1 + m) f
def remX (i : σ) (f : MvPowerSeries σ O) : MvPowerSeries σ O := fun m => if m i = 0 then coeff m f else 0
end Division
section
variable {O : Type} [CommRing O] [IsLocalRing O] {a : ℕ}
theorem mem_max_iff (f : MvPowerSeries (Fin a) O) :
    f ∈ maximalIdeal (MvPowerSeries (Fin a) O) ↔ constantCoeff f ∈ maximalIdeal O :=
  _root_.GlobalTheory.MaximalIdealMembership.mem_maximalIdeal_iff f
theorem ps_isPrecomplete [IsPrecomplete (maximalIdeal O) O] (a : ℕ) :
    IsPrecomplete (maximalIdeal (MvPowerSeries (Fin a) O)) (MvPowerSeries (Fin a) O) :=
  _root_.GlobalTheory.PowerSeriesIdealPowers.main a
end
theorem haus_of_noeth (B : Type) [CommRing B] [IsLocalRing B] [IsNoetherianRing B] :
    IsHausdorff (maximalIdeal B) B :=
  _root_.GlobalTheory.NoetherianLocalHausdorff.noeth_local_hausdorff B
theorem psCNL : ∀ (O : Type) [CommRing O] [IsLocalRing O] (C : TR O) (n : ℕ),
    ∃ (_ : IsLocalRing (MvPowerSeries (Fin n) C.C)), IsCNL O (MvPowerSeries (Fin n) C.C) ∧
      ∀ x : MvPowerSeries (Fin n) C.C, x ∈ maximalIdeal (MvPowerSeries (Fin n) C.C) ↔
        MvPowerSeries.constantCoeff x ∈ maximalIdeal C.C := by
  intro O _ _ A n
  refine ⟨inferInstance, ?_, fun x => mem_max_iff x⟩
  exact
    { noeth := inferInstance
      complete :=
        { toIsHausdorff := haus_of_noeth _
          toIsPrecomplete := ps_isPrecomplete n }
      localHom := ⟨fun a ha => by
        rw [MvPowerSeries.algebraMap_apply, isUnit_iff_constantCoeff, constantCoeff_C] at ha
        exact isUnit_of_map_unit _ _ ha⟩
      resSurj := by
        intro y
        obtain ⟨f, rfl⟩ := residue_surjective y
        obtain ⟨a, ha⟩ := IsCNL.resSurj (O := O) (A := A.C) (residue A.C (constantCoeff f))
        have ha' : residue A.C (algebraMap O A.C a) = residue A.C (constantCoeff f) := ha
        refine ⟨a, ?_⟩
        show residue _ (algebraMap O (MvPowerSeries (Fin n) A.C) a) = residue _ f
        rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff, mem_maximalIdeal, mem_nonunits_iff,
          isUnit_iff_constantCoeff, map_sub, MvPowerSeries.algebraMap_apply, constantCoeff_C]
        show algebraMap O A.C a - constantCoeff f ∈ maximalIdeal A.C
        rw [← residue_eq_zero_iff, map_sub, ha', sub_self] }
end GlobalTheory.PsCNL
open Formalism.BasicNotions.V1 IsLocalRing in
example : ∀ (O : Type) [CommRing O] [IsLocalRing O] (C : TR O) (n : ℕ), ∃ (_ : IsLocalRing (MvPowerSeries (Fin n) C.C)), IsCNL O (MvPowerSeries (Fin n) C.C) ∧ ∀ x : MvPowerSeries (Fin n) C.C, x ∈ maximalIdeal (MvPowerSeries (Fin n) C.C) ↔ MvPowerSeries.constantCoeff x ∈ maximalIdeal C.C := GlobalTheory.PsCNL.psCNL


