-- Prove2me | Definitions.Def_PricingWithTips3DM_8a89fbe04430356adb3f42c0
-- name    : PricingWithTips3DM_8a89fbe04430356adb3f42c0
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T20:58:13.035057+00:00
-- url     : https://prove2.me/theorems/e470964a-bd75-40d0-966e-b788c18b5389
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.Canonicalizer.Runtime
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_f1062b85fcc07826ef0bc683
import Mathlib.Tactic
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# Raw-input canonicalizer: polynomial runtime
-/

noncomputable section

open Computability StateTransition

namespace CLRS.Chapter34.Turing.GeneralCliqueVerifier.Canonicalizer

open PolyBuilder
open _root_.Turing

/-- Every branch of the canonicalizer is bounded by one linear expression. -/
theorem steps_le (kind : Kind) (input : List CliqueSym) :
    steps kind input ≤ 4 * input.length + 6 := by
  unfold steps
  split
  · omega
  · cases kind <;> simp <;> omega

/-- Compiled output theorem shared by the certificate and instance wrappers. -/
def outputs_in_time (kind : Kind) (input : List CliqueSym) :
    TM2OutputsInTime (compile (program kind)) input
      (some (canonicalStream kind input))
      ((4 * Polynomial.X + 6).eval input.length) := by
  have builderRun := run kind input
  have compiledRun := compile_evalsToInTime (program kind) builderRun
  have htime : steps kind input ≤
      (4 * Polynomial.X + 6).eval input.length := by
    simpa [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X] using
      steps_le kind input
  change EvalsToInTime (compile (program kind)).step
    (initList (compile (program kind)) input)
    (some (haltList (compile (program kind)) (canonicalStream kind input)))
    ((4 * Polynomial.X + 6).eval input.length)
  refine ⟨⟨compiledRun.steps, ?_⟩,
    compiledRun.steps_le_m.trans htime⟩
  convert compiledRun.evals_in_steps using 1
  all_goals simp only [encodeCfg_initialCfg, encodeCfg_haltCfg]

/-- A fixed linear-time TM2 decodes or defaults any raw certificate string. -/
noncomputable def certificateComputableInPolyTime :
    TM2ComputableInPolyTime id encodeCliqueCertificate certificateValue where
  tm := compile (program .certificate)
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 4 * Polynomial.X + 6
  outputsFun := fun input => by
    have output := outputs_in_time .certificate input
    rw [canonicalStream_certificate_eq] at output
    convert output using 1 <;> simp
    all_goals
      change List.map id _ = _
      exact List.map_id _

/-- A fixed linear-time TM2 decodes or defaults any raw graph-instance string. -/
noncomputable def instanceComputableInPolyTime :
    TM2ComputableInPolyTime id encodeCliqueInstance instanceValue where
  tm := compile (program .instance)
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 4 * Polynomial.X + 6
  outputsFun := fun input => by
    have output := outputs_in_time .instance input
    rw [canonicalStream_instance_eq] at output
    convert output using 1 <;> simp
    all_goals
      change List.map id _ = _
      exact List.map_id _

end CLRS.Chapter34.Turing.GeneralCliqueVerifier.Canonicalizer


