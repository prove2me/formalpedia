-- Prove2me | Definitions.Def_OAIQ244Duke032
-- name    : OAIQ244Duke032
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-13T06:28:46.058569+00:00
-- url     : https://prove2.me/theorems/7a29a586-e5dd-4325-b713-610574b86063
-- title:
--   Definitions bundle OAIQ244Duke032 of the split of OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1 declaration of OpenAI's Lean: 1 theorem.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `LocalField_NonarchimedeanLocalField_UnitTopology`.
--
--   **Imports.** It imports the bundle `OAIQ244Duke020` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ244Duke041`.
-- source:
--   OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 15; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Equidistribution-of-Prime-Degree-Torus-Packets-with-Arbitrary-Local-Type-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory at commit 7ef5c0c

import Mathlib
import Mathlib.NumberTheory.LocalField.Basic
import Definitions.Def_OAIQ244Duke020

section
-- module Solutions.OAIQ244_DUKE.LocalField_NonarchimedeanLocalField_UnitTopology
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isLocalRing _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.infinitePlace_mult_smul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
open OAI

set_option autoImplicit false

/-!
# The unit subgroup of a nonarchimedean local field

This module identifies the image of valuation-ring units in the field unit
group with the valuation-one sphere and records that this subgroup is open in
the native topology of a nonarchimedean local field.
-/

noncomputable section

universe u

namespace LocalFieldTheory

open scoped ValuativeRel
open _root_.LocalFieldTheory.IsNonarchimedeanLocalField

/-- A field unit lies in the image of valuation-ring units exactly when its
valuation is one. -/
theorem mem_localBaseUnitSubgroup_iff_valuation_eq_one
    (K : Type u) [Field K] [ValuativeRel K] (x : Kˣ) :
    x ∈ localBaseUnitSubgroup K ↔ ValuativeRel.valuation K (x : K) = 1 := by
  constructor
  · rintro ⟨a, rfl⟩
    simpa [integerUnitsToFieldUnits] using
      (Valuation.Integers.valuation_unit
        (Valuation.integer.integers (ValuativeRel.valuation K)) a)
  · intro hx
    let a : 𝒪[K]ˣ :=
      { val := ⟨(x : K), by
          rw [Valuation.mem_integer_iff]
          exact hx.le⟩
        inv := ⟨(x⁻¹ : K), by
          rw [Valuation.mem_integer_iff]
          simp [hx]⟩
        val_inv := by ext; simp
        inv_val := by ext; simp }
    exact ⟨a, by ext; rfl⟩

end LocalFieldTheory
end
end


