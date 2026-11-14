-- Prove2me | Definitions.Def_OAIQ244Duke041
-- name    : OAIQ244Duke041
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-13T06:32:14.810182+00:00
-- url     : https://prove2.me/theorems/6f3c9d20-4721-4441-abf2-fea6cad09509
-- title:
--   Definitions bundle OAIQ244Duke041 of the split of OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1 declaration of OpenAI's Lean: 1 theorem.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `LocalField_NonarchimedeanLocalField_UnitTopology`.
--
--   **Imports.** It imports the bundle `OAIQ244Duke032` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ244Duke069`.
-- source:
--   OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 15; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Equidistribution-of-Prime-Degree-Torus-Packets-with-Arbitrary-Local-Type-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory at commit 7ef5c0c

import Mathlib
import Mathlib.NumberTheory.LocalField.Basic
import Definitions.Def_OAIQ244Duke032

section
-- module Solutions.OAIQ244_DUKE.LocalField_NonarchimedeanLocalField_UnitTopology
attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.PrimeDegreePackets.instNonemptyLeafTestSpace _root_.OAI.PrimeDegreePackets.integralClosure_padicInt_dvr _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace
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

/-- The image of valuation-ring units is open in the native topology of a
nonarchimedean local field. -/
theorem localBaseUnitSubgroup_isOpen
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    IsOpen (localBaseUnitSubgroup K : Set Kˣ) := by
  have hsphere : IsOpen {x : K | ValuativeRel.valuation K x = 1} :=
    by
      simpa only [Valuation.restrict_eq_one_iff] using
        (ValuativeRel.valuation K).isOpen_sphere one_ne_zero
  have hpre := hsphere.preimage (Units.continuous_val :
    Continuous (fun x : Kˣ => (x : K)))
  rw [show (localBaseUnitSubgroup K : Set Kˣ) =
      {x : Kˣ | ValuativeRel.valuation K (x : K) = 1} by
    ext x
    exact mem_localBaseUnitSubgroup_iff_valuation_eq_one K x]
  exact hpre

end LocalFieldTheory
end
end


