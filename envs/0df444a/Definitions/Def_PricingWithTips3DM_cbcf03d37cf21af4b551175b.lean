-- Prove2me | Definitions.Def_PricingWithTips3DM_cbcf03d37cf21af4b551175b
-- name    : PricingWithTips3DM_cbcf03d37cf21af4b551175b
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T21:00:03.554038+00:00
-- url     : https://prove2.me/theorems/7c59587b-ed58-43d9-b23e-02c81c86e1d3
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralCircuit.ToSAT.Machine.Normalizer.GateConstant
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_8c5300f3efe3ecfc7b6be671
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# Guarded circuit normalizer: constant gates
-/

namespace CLRS.Chapter34.Turing.GeneralCircuitToSAT.Normalizer

open Computability StateTransition

private abbrev transition := flip Option.bind step

def constantKind : Bool → GateKind
  | false => .constFalse
  | true => .constTrue

/-- Constants need only the shared chronological-index pass; their finite tag
phase closes the row and advances the gate counter. -/
theorem constantGate_phase (state : State) (value : Bool) (gateIndex : Nat)
    (input : List CircuitSym) (output rows : List NormalizedCircuitSym)
    (inputCount : Nat) :
    ∃ finalState,
      transition^[2 * gateIndex + 3]
        (some (cfg (some .gates) state
          (encodeCircuitGate (.const value) ++ input) output rows
          inputCount gateIndex 0 0 0)) =
        some (cfg (some .gates) finalState input output
          ((encodeNormalizedGateRow gateIndex (.const value)).reverse ++ rows)
          inputCount (gateIndex + 1) 0 0 0) := by
  have h₁ : transition^[1]
      (some (cfg (some .gates) state
        (encodeCircuitGate (.const value) ++ input) output rows
        inputCount gateIndex 0 0 0)) =
      some (cfg (some (.rowIndexCopy (constantKind value)))
        { state with inputBuffer := some (rawGateTag (constantKind value)) }
        input output (.gateRowMark :: rows) inputCount gateIndex 0 0 0) := by
    change step (cfg (some .gates) state
      (encodeCircuitGate (.const value) ++ input) output rows
      inputCount gateIndex 0 0 0) = _
    have htag := gates_tag_step state (constantKind value) input output rows
      inputCount gateIndex 0 0 0
    cases value <;>
      simpa [encodeCircuitGate, constantKind, rawGateTag] using htag
  rcases rowPrefix_phase
      { state with inputBuffer := some (rawGateTag (constantKind value)) }
      (constantKind value) gateIndex input output (.gateRowMark :: rows)
      inputCount 0 0 with ⟨s₂, h₂⟩
  have hfull := step_comp _ _ h₁ h₂
  refine ⟨s₂, ?_⟩
  have hsteps : 1 + (2 * gateIndex + 2) = 2 * gateIndex + 3 := by omega
  rw [← hsteps]
  cases value <;>
    simpa [encodeNormalizedGateRow, encodeNormalizedNat, encodeNormalizedGate,
      constantKind, rawGateTag, normalizedGateTag, afterRowPrefixLabel,
      afterRowPrefixRows, afterRowPrefixGateCount, List.reverse_append,
      List.append_assoc, List.reverse_replicate] using hfull

end CLRS.Chapter34.Turing.GeneralCircuitToSAT.Normalizer


