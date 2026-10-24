-- Prove2me | Definitions.Def_PricingWithTips3DM_6bf3e19aca9b962b1545960f
-- name    : PricingWithTips3DM_6bf3e19aca9b962b1545960f
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T20:53:45.082678+00:00
-- url     : https://prove2.me/theorems/a7bf053e-b9fe-413f-880c-79b85ab510df
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.Canonicalizer.Run
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_0d134ee636ce936d7bb92521
import Mathlib.Tactic
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# Raw-input canonicalizer: complete run
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.GeneralCliqueVerifier.Canonicalizer

open PolyBuilder

/-- Exact branch-sensitive cost of one complete canonicalization. -/
def steps (kind : Kind) (input : List CliqueSym) : Nat :=
  if accepts kind (scanSymbols (initialMode kind) input) then
    4 * input.length + 3
  else
    match kind with
    | .certificate => 3 * input.length + 4
    | .instance => 3 * input.length + 6

/-- The fixed controller halts on every raw string with its total canonical
representative. -/
def run (kind : Kind) (input : List CliqueSym) :
    EvalsToInTime (step (program kind))
      (initialCfg (program kind) input)
      (some (haltCfg (program kind) (canonicalStream kind input)))
      (steps kind input) := by
  rcases scan_run kind (initialMode kind) input [] [] none none false with
    ⟨finalBuffer, scanned⟩
  have scanned' : EvalsToInTime (step (program kind))
      (initialCfg (program kind) input)
      (some (cfg kind
        (.scan (scanSymbols (initialMode kind) input)) finalBuffer none false
        [] [] input.reverse []))
      (2 * input.length) := by
    simpa [initialCfg, cfg, program] using scanned
  by_cases haccepts :
      accepts kind (scanSymbols (initialMode kind) input) = true
  · have finish : EvalsToInTime (step (program kind))
        (cfg kind (.scan (scanSymbols (initialMode kind) input))
          finalBuffer none false [] [] input.reverse [])
        (some (cfg kind .restore none none false [] [] input.reverse [])) 1 :=
      ⟨⟨1, by simp [flip, step, program, cfg, stepOp, haccepts]⟩, le_rfl⟩
    have restored := restore_run kind input.reverse [] none none false
    have restored' : EvalsToInTime (step (program kind))
        (cfg kind .restore none none false [] [] input.reverse [])
        (some (haltCfg (program kind) input))
        (2 * input.length + 2) := by
      simpa using restored
    let first := EvalsToInTime.trans (step (program kind))
      (2 * input.length) 1 _ _ _ scanned' finish
    let full := EvalsToInTime.trans (step (program kind))
      _ (2 * input.length + 2) _ _ _ first restored'
    convert full using 1
    all_goals simp [steps, canonicalStream, haccepts, Nat.add_comm,
      Nat.add_left_comm]
    omega
  · have hacceptsFalse :
        accepts kind (scanSymbols (initialMode kind) input) = false := by
      exact Bool.eq_false_of_not_eq_true haccepts
    have finish : EvalsToInTime (step (program kind))
        (cfg kind (.scan (scanSymbols (initialMode kind) input))
          finalBuffer none false [] [] input.reverse [])
        (some (cfg kind .clear none none false [] [] input.reverse [])) 1 :=
      ⟨⟨1, by simp [flip, step, program, cfg, stepOp,
        hacceptsFalse]⟩, le_rfl⟩
    have cleared := clear_run kind input.reverse [] none none false
    let first := EvalsToInTime.trans (step (program kind))
      (2 * input.length) 1 _ _ _ scanned' finish
    let second := EvalsToInTime.trans (step (program kind))
      _ (input.length + 1) _ _ _ first (by simpa using cleared)
    rcases kind with _ | _
    ·
        have fallbackRun := certificate_fallback_run [] none none false
        let full := EvalsToInTime.trans (step (program .certificate))
          _ 2 _ _ _ second fallbackRun
        convert full using 1
        all_goals simp [steps, canonicalStream, hacceptsFalse, fallback,
          Nat.add_assoc, Nat.add_left_comm]
        omega
    ·
        have fallbackRun := instance_fallback_run [] none none false
        let full := EvalsToInTime.trans (step (program .instance))
          _ 4 _ _ _ second fallbackRun
        convert full using 1
        all_goals simp [steps, canonicalStream, hacceptsFalse, fallback,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        omega

end CLRS.Chapter34.Turing.GeneralCliqueVerifier.Canonicalizer


