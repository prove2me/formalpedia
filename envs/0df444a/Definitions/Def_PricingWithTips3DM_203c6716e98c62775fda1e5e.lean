-- Prove2me | Definitions.Def_PricingWithTips3DM_203c6716e98c62775fda1e5e
-- name    : PricingWithTips3DM_203c6716e98c62775fda1e5e
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T21:16:33.393767+00:00
-- url     : https://prove2.me/theorems/4b58a9ae-fd26-44d0-86f9-d705fd5568d8
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralCircuit.ToSAT.Machine.Emitter.Computable
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_b273d9a0a98624995a8d7aae
import Definitions.Def_PricingWithTips3DM_b8c03f33e84411dcd1343113
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-! # General-circuit formula emitter: forward polynomial-time interface -/

namespace CLRS.Chapter34.Turing.GeneralCircuitToSAT.Emitter

/-- Composing the direct emitter with the verified generic reversal machine
returns the forward exact formula stream. -/
noncomputable def computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime encodeGuardedCircuit id
      guardedCircuitFormulaList := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      reverseComputableInPolyTime
      (PolyBuilder.reverse_computableInPolyTime (Γ := FormulaSym))
  simpa [Function.comp_def] using Classical.choice composed

end CLRS.Chapter34.Turing.GeneralCircuitToSAT.Emitter


