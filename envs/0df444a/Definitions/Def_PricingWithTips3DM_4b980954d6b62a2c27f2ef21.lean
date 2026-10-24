-- Prove2me | Definitions.Def_PricingWithTips3DM_4b980954d6b62a2c27f2ef21
-- name    : PricingWithTips3DM_4b980954d6b62a2c27f2ef21
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T20:47:50.81158+00:00
-- url     : https://prove2.me/theorems/b038ae69-4f57-4964-bb70-5ae2e2220c7f
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralCircuit.ToSAT.Machine.InternalEncoding.RoundTrip
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_988b27bbcd4d2ab75ab2bc8b
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# Guarded circuit work-record round trips

Every encoder preserves an arbitrary following suffix until the top-level
codec, where complete consumption is enforced.
-/

namespace CLRS.Chapter34

/-- Unary normalized fields decode while preserving their exact suffix. -/
theorem decodeNormalizedNat_encodeNormalizedNat (n : Nat)
    (rest : List NormalizedCircuitSym) :
    decodeNormalizedNat (encodeNormalizedNat n ++ rest) = some (n, rest) := by
  induction n generalizing rest with
  | zero => simp [encodeNormalizedNat, decodeNormalizedNat]
  | succ n ih =>
      rw [show encodeNormalizedNat (n + 1) ++ rest =
          .tick :: (encodeNormalizedNat n ++ rest) by
        simp [encodeNormalizedNat, List.replicate_succ, List.append_assoc]]
      simp [decodeNormalizedNat, ih]

/-- A normalized gate body decodes while preserving its exact suffix. -/
theorem decodeNormalizedGate_encodeNormalizedGate (gate : CircuitGate)
    (rest : List NormalizedCircuitSym) :
    decodeNormalizedGate (encodeNormalizedGate gate ++ rest) =
      some (gate, rest) := by
  cases gate with
  | input inputIndex =>
      simp [encodeNormalizedGate, decodeNormalizedGate,
        decodeNormalizedNat_encodeNormalizedNat]
  | const value =>
      cases value <;> simp [encodeNormalizedGate, decodeNormalizedGate]
  | not source =>
      simp [encodeNormalizedGate, decodeNormalizedGate,
        decodeNormalizedNat_encodeNormalizedNat]
  | and left right =>
      simp [encodeNormalizedGate, decodeNormalizedGate,
        decodeNormalizedNat_encodeNormalizedNat, List.append_assoc]
  | or left right =>
      simp [encodeNormalizedGate, decodeNormalizedGate,
        decodeNormalizedNat_encodeNormalizedNat, List.append_assoc]

/-- A normalized gate row checks and recovers its chronological index. -/
theorem decodeNormalizedGateRow_encodeNormalizedGateRow
    (gateIndex : Nat) (gate : CircuitGate)
    (rest : List NormalizedCircuitSym) :
    decodeNormalizedGateRow gateIndex
        (encodeNormalizedGateRow gateIndex gate ++ rest) =
      some (gate, rest) := by
  simp [encodeNormalizedGateRow, decodeNormalizedGateRow,
    decodeNormalizedNat_encodeNormalizedNat,
    decodeNormalizedGate_encodeNormalizedGate, List.append_assoc]

/-- A chronological normalized row family decodes with its suffix intact. -/
theorem decodeNormalizedGateRowsFrom_encodeNormalizedGateRowsFrom
    (gateIndex : Nat) (gates : List CircuitGate)
    (rest : List NormalizedCircuitSym) :
    decodeNormalizedGateRowsFrom gateIndex gates.length
        (encodeNormalizedGateRowsFrom gateIndex gates ++ rest) =
      some (gates, rest) := by
  induction gates generalizing gateIndex with
  | nil => simp [encodeNormalizedGateRowsFrom, decodeNormalizedGateRowsFrom]
  | cons gate gates ih =>
      simp only [List.length_cons, encodeNormalizedGateRowsFrom,
        List.append_assoc]
      rw [show gates.length + 1 = Nat.succ gates.length by omega]
      simp only [decodeNormalizedGateRowsFrom]
      rw [decodeNormalizedGateRow_encodeNormalizedGateRow]
      simp only [Option.bind_eq_bind, Option.bind_some]
      rw [ih]
      rfl

/-- Encoding and then decoding an indexed guarded record recovers the circuit. -/
theorem decode_encodeNormalizedCircuit (c : Circuit) :
    decodeNormalizedCircuit (encodeNormalizedCircuit c) = some c := by
  have hrows :=
    decodeNormalizedGateRowsFrom_encodeNormalizedGateRowsFrom
      0 c.gates ([] : List NormalizedCircuitSym)
  simp only [List.append_nil] at hrows
  unfold encodeNormalizedCircuit
  simp only [List.cons_append, List.nil_append]
  simp [decodeNormalizedCircuit,
    decodeNormalizedNat_encodeNormalizedNat, hrows]

/-- Guarded normalization returns the invalid sentinel exactly when no
successfully decoded circuit is well formed. -/
theorem normalizeGeneralCircuit_eq_invalid_iff (input : List CircuitSym) :
    normalizeGeneralCircuit input = [.invalidMark] ↔
      ∀ c, decodeCircuit input = some c → ¬ c.WellFormed := by
  cases hdecode : decodeCircuit input with
  | none => simp [normalizeGeneralCircuit, hdecode]
  | some c =>
      by_cases hwellFormed : c.WellFormed
      · simp [normalizeGeneralCircuit, hdecode, hwellFormed,
          encodeNormalizedCircuit]
      · simp [normalizeGeneralCircuit, hdecode, hwellFormed]

/-- Guarded normalization returns a canonical valid record exactly when the
raw input decodes to a well-formed circuit. -/
theorem normalizeGeneralCircuit_eq_valid_iff (input : List CircuitSym) :
    (∃ c, normalizeGeneralCircuit input = encodeNormalizedCircuit c) ↔
      ∃ c, decodeCircuit input = some c ∧ c.WellFormed := by
  cases hdecode : decodeCircuit input with
  | none =>
      simp [normalizeGeneralCircuit, hdecode, encodeNormalizedCircuit]
  | some c =>
      by_cases hwellFormed : c.WellFormed
      · simp [normalizeGeneralCircuit, hdecode, hwellFormed]
      · simp [normalizeGeneralCircuit, hdecode, hwellFormed,
          encodeNormalizedCircuit]

end CLRS.Chapter34


