-- Prove2me | Definitions.Def_PricingWithTips3DM_b6bd7fccce8d7d3f1596c77e
-- name    : PricingWithTips3DM_b6bd7fccce8d7d3f1596c77e
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T20:35:40.226316+00:00
-- url     : https://prove2.me/theorems/a6f9ed17-d335-448c-b54d-cef5e8a3a116
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.DropHead
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_d8886977e67d59ff4f35de9d
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# Fixed streaming head deletion

A reusable finite-state transducer drops exactly the first input symbol and
copies the remaining stream.  It is used when a controller returns a summary
symbol before a pointwise answer stream.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.PolyBuilder.DropHead

open PolyBuilder

def stream {Γ : Type} : List Γ → List Γ
  | [] => []
  | _ :: tail => tail

def spec (Γ : Type) : StatefulFlatMapSpec Bool Γ Γ where
  initial := false
  action seen symbol := if seen then ([symbol], true) else ([], true)
  finish _ := []

private theorem rewrite_from_seen {Γ : Type} (input : List Γ) :
    rewriteStatefulFlatMapFrom (spec Γ) true input = input := by
  induction input with
  | nil => rfl
  | cons symbol tail ih =>
      rw [rewriteStatefulFlatMapFrom]
      change [symbol] ++
        rewriteStatefulFlatMapFrom (spec Γ) true tail = symbol :: tail
      rw [ih]
      rfl

theorem rewrite_eq_stream {Γ : Type} (input : List Γ) :
    rewriteStatefulFlatMap (spec Γ) input = stream input := by
  cases input with
  | nil => rfl
  | cons symbol tail =>
      rw [rewriteStatefulFlatMap, rewriteStatefulFlatMapFrom]
      change [] ++ rewriteStatefulFlatMapFrom (spec Γ) true tail = tail
      exact rewrite_from_seen tail

noncomputable def computableInPolyTime (Γ : Type) [Fintype Γ] :
    _root_.Turing.TM2ComputableInPolyTime id id (@stream Γ) := by
  let machine := statefulFlatMap_computableInPolyTime (spec Γ)
  exact
    { tm := machine.tm
      inputAlphabet := machine.inputAlphabet
      outputAlphabet := machine.outputAlphabet
      time := machine.time
      outputsFun := fun input => by
        have output := machine.outputsFun input
        simpa only [rewrite_eq_stream] using output }

end CLRS.Chapter34.Turing.PolyBuilder.DropHead


