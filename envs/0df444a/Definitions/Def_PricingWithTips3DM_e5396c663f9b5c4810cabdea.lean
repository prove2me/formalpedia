-- Prove2me | Definitions.Def_PricingWithTips3DM_e5396c663f9b5c4810cabdea
-- name    : PricingWithTips3DM_e5396c663f9b5c4810cabdea
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T23:42:16.41656+00:00
-- url     : https://prove2.me/theorems/bdef959a-45d9-4cf0-acd7-fb6cc3e913c7
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionEqCanonicalAlignment
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_8a431b2515253bbdce9fce33
import Mathlib.Tactic
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# Canonical transition equality alignment

This module closes the generated equality frame stream against the existing
seed-derived canonical transition script, first for one row and then for the
complete verifier transition family.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

private theorem transitionEqZipWith3_ofFn {alpha beta gamma delta : Type}
    (combine : alpha → beta → gamma → delta) (count : Nat)
    (first : Fin count → alpha) (second : Fin count → beta)
    (third : Fin count → gamma) :
    List.zipWith3 combine (List.ofFn first) (List.ofFn second)
        (List.ofFn third) =
      List.ofFn fun index => combine (first index) (second index) (third index) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [List.ofFn_succ, List.ofFn_succ, List.ofFn_succ, List.ofFn_succ]
      simp only [List.zipWith3]
      congr 1
      exact ih (fun index => first index.succ)
        (fun index => second index.succ) (fun index => third index.succ)

/-- For one transition row, the fixed-TM2-generated equality frames are
literally the canonical seed-derived script's equality frames. -/
theorem transitionEqGeneratedFrames_eq_script
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (hwork : 0 < workHeight tm seed.height) :
    transitionEqGeneratedFrames tm seed =
      (transitionScriptFromSeed tm seed
        (seed.rowBase + cfgBitCount tm seed.height)).eqFrames := by
  rw [transitionEqGeneratedFrames_eq_slotFrames tm seed hwork]
  rw [transitionEqPublicSlots_eq_canonical, List.map_ofFn]
  unfold transitionScriptFromSeed transitionScriptOfDecomposition
    transitionScriptDecompositionFromSeed transitionTailLayoutAt
    transitionDispatchOperandLayoutFromSeed transitionDispatchOperandLayout
    transitionEqRightOperandsAt
  rw [transitionEqZipWith3_ofFn]
  apply List.ofFn_inj.mpr
  funext coordinate
  simp only [Function.comp_apply]
  unfold transitionEqSlotFrame transitionEqSlotSeed
    transitionEqCoordinateFrame
  rw [(cfgSlotEquivFin tm seed.height).apply_symm_apply]
  congr 1 <;> ring

/-- The raw-input equality compiler emits the exact canonical equality input
for every verifier transition row, byte for byte. -/
theorem verifierTransitionEqInvocationInput_eq_scripts
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionEqInvocationInput W input =
      encodeAffineEqFinFrames
        ((verifierTransitionRowSeeds W input).flatMap fun seed =>
          (transitionScriptFromSeed W.machine.tm seed
            (seed.rowBase +
              cfgBitCount W.machine.tm seed.height)).eqFrames) := by
  rw [verifierTransitionEqInvocationInput_eq_generatedFrames]
  apply congrArg encodeAffineEqFinFrames
  apply List.flatMap_congr
  intro seed hseed
  apply transitionEqGeneratedFrames_eq_script
  rw [verifierTransitionRowSeeds_height_eq W input seed hseed]
  exact Nat.add_pos_left
    (verifierHeight_eval_pos W input.length)
    (maxPushesPerStep W.machine.tm)

end CLRS.Chapter34.Turing.CookLevin


