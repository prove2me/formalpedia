-- Prove2me | Definitions.Def_PricingWithTips3DM_39b9c4b37fbdd91ca7a2f747
-- name    : PricingWithTips3DM_39b9c4b37fbdd91ca7a2f747
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-23T00:13:06.848931+00:00
-- url     : https://prove2.me/theorems/c8cf7942-efee-4780-8faa-986287f2a505
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorAcceptingBoundaryCanonical
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_10dccb0778a8c660a6c31b4a
import Definitions.Def_PricingWithTips3DM_df16da8834b8c21bdee3aa31
import Mathlib.Tactic
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# Builder-free canonical accepting frames

This module removes the proof-carrying builder coordinates from the positive
accepting branch.  The old semantic equality family is identified with the
explicit public-slot order, the independently generated input-boundary end,
and the polynomial first wire of the last tableau row.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Canonical accepting equality frame attached to one public row slot. -/
def verifierAcceptingSlotFrame
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (hmember : verifierAcceptingSymbol W ∈
      reachableAlphabet W.machine.tm W.machine.tm.k₁)
    (input : List Γ)
    (slot : CfgSlot W.machine.tm ((verifierHeight W).eval input.length)) :
    AffineEqFinPairFrame :=
  let coordinate :=
    (cfgSlotEquivFin W.machine.tm
      ((verifierHeight W).eval input.length) slot).val
  let previous := verifierInputBoundaryEnd W input + 6 * coordinate
  { eqStart := previous + 1
    left := (verifierLastRowStartPolynomial W).eval input.length + coordinate
    right := verifierAcceptingTargetWires W input
      (verifierAcceptingOutputFitsOfSymbol W input hmember) slot
    matched := previous + 5
    previous := previous }

/-- The semantic positive-branch canonical family is exactly the explicit
public-slot map with no remaining builder-derived start or row wire. -/
theorem verifierAcceptingCanonicalFrames_eq_slotFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (hmember : verifierAcceptingSymbol W ∈
      reachableAlphabet W.machine.tm W.machine.tm.k₁)
    (input : List Γ) :
    affineEqFinCanonicalFrames
        (verifierInputBoundary W input).builder.gates.length
        (cfgBitCount W.machine.tm
          ((verifierHeight W).eval input.length))
        (fun i =>
          (verifierRows W input).rows
            (Fin.last ((verifierHorizon W).eval input.length))
            ((cfgSlotEquivFin W.machine.tm
              ((verifierHeight W).eval input.length)).symm i))
        (fun i => verifierAcceptingTargetWires W input
          (verifierAcceptingOutputFitsOfSymbol W input hmember)
          ((cfgSlotEquivFin W.machine.tm
            ((verifierHeight W).eval input.length)).symm i)) =
      (transitionEqPublicSlots W.machine.tm
        ((verifierHeight W).eval input.length)).map
          (verifierAcceptingSlotFrame W hmember input) := by
  rw [affineEqFinCanonicalFrames_eq_ofFn]
  rw [transitionEqPublicSlots_eq_canonical, List.map_ofFn]
  apply List.ofFn_inj.mpr
  funext coordinate
  unfold verifierAcceptingSlotFrame
  rw [verifierInputBoundary_gates_length_eq_end]
  rw [verifierRowWire_eq]
  simp only [verifierLastRowStartPolynomial_eval]
  simp
  omega

/-- The actual optional accepting operand selects precisely the explicit
slot-map family in the static positive case. -/
theorem compileVerifierAcceptingBoundaryFrames_eq_some_slotFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (hmember : verifierAcceptingSymbol W ∈
      reachableAlphabet W.machine.tm W.machine.tm.k₁)
    (input : List Γ) :
    compileVerifierAcceptingBoundaryFrames W input =
      some ((transitionEqPublicSlots W.machine.tm
        ((verifierHeight W).eval input.length)).map
          (verifierAcceptingSlotFrame W hmember input)) := by
  rw [compileVerifierAcceptingBoundaryFrames_eq_some W hmember input]
  rw [verifierAcceptingCanonicalFrames_eq_slotFrames W hmember input]

end CLRS.Chapter34.Turing.CookLevin


