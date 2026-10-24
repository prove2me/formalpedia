-- Prove2me | Definitions.Def_PricingWithTips3DM_3a628384b5ec96abe91265ca
-- name    : PricingWithTips3DM_3a628384b5ec96abe91265ca
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T20:35:44.948988+00:00
-- url     : https://prove2.me/theorems/f3ea065b-7acb-40b5-a98f-beab3e19d29a
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.PairFirstProjection.Runtime
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_9b700618b7ca1003b94b6a7b
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# First pair projection: polynomial runtime
-/

noncomputable section

open Computability StateTransition

namespace CLRS.Chapter34.Turing.PolyBuilder.PairFirstProjection

open _root_.Turing

/-- The fixed controller computes the first projection in linear time. -/
noncomputable def computableInPolyTime (Γ : Type) [Fintype Γ] :
    TM2ComputableInPolyTime
      (fun pr : List Γ × List Γ => pairEncoding pr.1 pr.2)
      id Prod.fst where
  tm := compile (program Γ)
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 4 * Polynomial.X + 4
  outputsFun := fun pr => by
    rcases pr with ⟨left, right⟩
    have builderRun := run left right
    have compiledRun := compile_evalsToInTime (program Γ) builderRun
    have htime : 4 * left.length + right.length + 4 ≤
        (4 * Polynomial.X + 4).eval (pairEncoding left right).length := by
      simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
        pairEncoding]
      omega
    have bounded : EvalsToInTime (compile (program Γ)).step
        (initList (compile (program Γ)) (pairEncoding left right))
        (some (haltList (compile (program Γ)) left))
        ((4 * Polynomial.X + 4).eval (pairEncoding left right).length) := by
      refine ⟨⟨compiledRun.steps, ?_⟩,
        compiledRun.steps_le_m.trans htime⟩
      convert compiledRun.evals_in_steps using 1
      all_goals simp only [encodeCfg_initialCfg, encodeCfg_haltCfg]
    simp only [TM2OutputsInTime]
    convert bounded using 1
    · congr 1
      change List.map id _ = _
      exact List.map_id _
    · simp only [id_eq, Option.map_some]
      congr 2
      change List.map id _ = _
      exact List.map_id _

end CLRS.Chapter34.Turing.PolyBuilder.PairFirstProjection


