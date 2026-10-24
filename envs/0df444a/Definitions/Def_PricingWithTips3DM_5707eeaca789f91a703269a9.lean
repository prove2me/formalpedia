-- Prove2me | Definitions.Def_PricingWithTips3DM_5707eeaca789f91a703269a9
-- name    : PricingWithTips3DM_5707eeaca789f91a703269a9
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T20:35:40.126845+00:00
-- url     : https://prove2.me/theorems/51bdc0e9-d890-4110-9f9b-100e30e75c4d
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.BatchEdgeLookup.HeadProjection
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_d8886977e67d59ff4f35de9d
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# Batch edge lookup: aggregate projection

The enriched batch controller exposes one Boolean per query.  This fixed
streaming projection retains the leading aggregate bit, preserving the older
singleton-output interface used by the CLIQUE verifier pipeline.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.GeneralCliqueVerifier.BatchEdgeLookup.HeadProjection

open PolyBuilder

/-- Pure stream contract of the leading-bit projection. -/
def stream : List Bool → List Bool
  | [] => []
  | bit :: _ => [bit]

/-- `false` means that the first input symbol has not yet been seen. -/
def spec : StatefulFlatMapSpec Bool Bool Bool where
  initial := false
  action seen bit := if seen then ([], true) else ([bit], true)
  finish _ := []

private theorem rewrite_from_seen (input : List Bool) :
    rewriteStatefulFlatMapFrom spec true input = [] := by
  induction input with
  | nil => rfl
  | cons bit tail ih =>
      rw [rewriteStatefulFlatMapFrom]
      change [] ++ rewriteStatefulFlatMapFrom spec true tail = []
      simpa using ih

theorem rewrite_eq_stream (input : List Bool) :
    rewriteStatefulFlatMap spec input = stream input := by
  cases input with
  | nil => rfl
  | cons bit tail =>
      rw [rewriteStatefulFlatMap, rewriteStatefulFlatMapFrom]
      change [bit] ++ rewriteStatefulFlatMapFrom spec true tail = [bit]
      rw [rewrite_from_seen]
      rfl

/-- A fixed linear-time TM2 retains only the leading Boolean. -/
noncomputable def computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime id id stream := by
  let machine := statefulFlatMap_computableInPolyTime spec
  exact
    { tm := machine.tm
      inputAlphabet := machine.inputAlphabet
      outputAlphabet := machine.outputAlphabet
      time := machine.time
      outputsFun := fun input => by
        have output := machine.outputsFun input
        simpa only [rewrite_eq_stream] using output }

end CLRS.Chapter34.Turing.GeneralCliqueVerifier.BatchEdgeLookup.HeadProjection


