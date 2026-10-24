-- Prove2me | Definitions.Def_PricingWithTips3DM_1a41b0d96127a74376e13dc5
-- name    : PricingWithTips3DM_1a41b0d96127a74376e13dc5
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T23:37:50.819597+00:00
-- url     : https://prove2.me/theorems/6ab345e1-31a5-4c88-acbe-59e9295ace11
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionAffineStmtScriptTotal
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_8982bf3acd71bf536ecf93fb
import Definitions.Def_PricingWithTips3DM_3799fd79c9b0b4d68c438353
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# Total fixed affine statement-script compiler

The fixed-delimiter source requires a nonempty verifier-fixed column table.
This wrapper handles the only missing case with the verified bounded-loop
eraser, giving one unconditional compiler interface for every fixed symbolic
statement script, including `[]`.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Row-major semantics of a fixed symbolic script, including the empty
script. -/
def verifierTransitionAffineStmtScriptTarget
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (script : List TransitionAffineStmtPhaseForm)
    (input : List Γ) : List UnaryFrameSym :=
  (verifierTransitionRowSeeds W input).flatMap fun seed =>
    encodeAffineStmtControllerScript (script.map fun phase =>
      phase.eval (transitionTailAffineSeed seed))

/-- The conditional fixed-delimiter source has exactly the total target when
the symbolic script is nonempty. -/
theorem verifierTransitionAffineStmtScript_eq_target
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (script : List TransitionAffineStmtPhaseForm) (hnonempty : script ≠ [])
    (input : List Γ) :
    verifierTransitionAffineStmtScript W script hnonempty input =
      verifierTransitionAffineStmtScriptTarget W script input := by
  exact verifierTransitionAffineStmtScript_eq_rows W script hnonempty input

/-- Symbol-local eraser for an empty fixed script. -/
def transitionAffineStmtScriptEraseBody (Γ : Type) :
    LoopBody Γ UnaryFrameSym where
  emit _ := []
  cost _ := 0
  emit_length_le_cost _ := le_rfl

private noncomputable def
    transitionAffineStmtScriptEmpty_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (fun _ : List Γ => ([] : List UnaryFrameSym)) := by
  letI : Fintype Γ := W.alphabetFintype
  let base := boundedLoop_computableInPolyTime
    (transitionAffineStmtScriptEraseBody Γ)
  exact
    { tm := base.tm
      inputAlphabet := base.inputAlphabet
      outputAlphabet := base.outputAlphabet
      time := base.time
      outputsFun := fun input => by
        have run := base.outputsFun input
        have hempty : input.flatMap
            (transitionAffineStmtScriptEraseBody Γ).emit = [] := by
          simp [transitionAffineStmtScriptEraseBody]
        rw [hempty] at run
        simpa only [id_eq, List.map_nil] using run }

/-- One fixed polynomial-time TM2 emits any fixed affine statement script,
with no nonempty side condition. -/
noncomputable def
    verifierTransitionAffineStmtScriptTarget_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (script : List TransitionAffineStmtPhaseForm) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionAffineStmtScriptTarget W script) := by
  by_cases hscript : script = []
  · let base := transitionAffineStmtScriptEmpty_computableInPolyTime W
    exact
      { tm := base.tm
        inputAlphabet := base.inputAlphabet
        outputAlphabet := base.outputAlphabet
        time := base.time
        outputsFun := fun input => by
          have run := base.outputsFun input
          subst script
          have htarget :
              verifierTransitionAffineStmtScriptTarget W [] input = [] := by
            unfold verifierTransitionAffineStmtScriptTarget
            rw [List.flatMap_eq_nil_iff]
            simp [encodeAffineStmtControllerScript]
          rw [htarget]
          simpa only [id_eq, List.map_nil] using run }
  · let base := verifierTransitionAffineStmtScript_computableInPolyTime W
      script hscript
    exact
      { tm := base.tm
        inputAlphabet := base.inputAlphabet
        outputAlphabet := base.outputAlphabet
        time := base.time
        outputsFun := fun input => by
          have run := base.outputsFun input
          rw [verifierTransitionAffineStmtScript_eq_target W script hscript
            input] at run
          simpa only [id_eq] using run }

end CLRS.Chapter34.Turing.CookLevin


