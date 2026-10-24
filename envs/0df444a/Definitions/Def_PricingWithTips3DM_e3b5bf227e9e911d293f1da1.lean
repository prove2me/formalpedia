-- Prove2me | Definitions.Def_PricingWithTips3DM_e3b5bf227e9e911d293f1da1
-- name    : PricingWithTips3DM_e3b5bf227e9e911d293f1da1
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T20:23:08.209633+00:00
-- url     : https://prove2.me/theorems/4da950f8-44db-41cb-a7ad-117fda3dbd12
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Tableau.ValidityBounds
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_7a3546642b0e4bed8fb9baa4
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# CLRS Section 34.4 - Canonical row-validity gate bounds

This module separates the exact row-validity cost from the polynomial-size
argument.  For a fixed machine, one height-independent coefficient controls
the emitted gate count at every public row height.
-/

namespace CLRS.Chapter34.Turing.CookLevin

noncomputable section

/-- A height-independent coefficient controlling canonical row-validity gates
for one fixed machine. -/
def validCfgGateCoefficient (tm : _root_.Turing.FinTM2) : Nat := by
  letI := tm.kFin
  exact 3 * labelCount tm + 3 * stateCount tm + 20 +
    ∑ k : tm.K, (3 * (reachableAlphabet tm k).card + 28)

/-- The exact canonical-validity cost is at most a fixed-machine coefficient
times the affine height expression {lit}`H + 1`. -/
theorem validCfgGateCost_le (tm : _root_.Turing.FinTM2) (H : Nat) :
    validCfgGateCost tm H ≤ validCfgGateCoefficient tm * (H + 1) := by
  letI := tm.kFin
  let fixedCost := 3 * labelCount tm + 3 * stateCount tm + 20
  have hfixed : fixedCost ≤ fixedCost * (H + 1) :=
    Nat.le_mul_of_pos_right fixedCost (by omega)
  have hstack :
      (∑ k : tm.K,
          (H * (3 * (reachableAlphabet tm k).card + 19) + 9)) ≤
        ∑ k : tm.K,
          ((3 * (reachableAlphabet tm k).card + 28) * (H + 1)) := by
    apply Finset.sum_le_sum
    intro k _
    calc
      H * (3 * (reachableAlphabet tm k).card + 19) + 9 ≤
          H * (3 * (reachableAlphabet tm k).card + 19) +
            (3 * (reachableAlphabet tm k).card + 19) + 9 * H + 9 := by
        omega
      _ = (3 * (reachableAlphabet tm k).card + 28) * (H + 1) := by
        ring
  change fixedCost +
      (∑ k : tm.K,
        (H * (3 * (reachableAlphabet tm k).card + 19) + 9)) ≤ _
  change _ ≤ (fixedCost +
      ∑ k : tm.K, (3 * (reachableAlphabet tm k).card + 28)) * (H + 1)
  rw [Nat.add_mul, Finset.sum_mul]
  exact Nat.add_le_add hfixed hstack

/-- Canonical row validation emits at most the advertised fixed-machine
coefficient times {lit}`H + 1` gates beyond the input builder. -/
theorem validCfgCircuit_gate_count_le
    {tm : _root_.Turing.FinTM2} {H : Nat}
    (base : CircuitBuilder) (wires : CfgWires tm H)
    (hvalid : wires.ValidIn base) :
    (validCfgCircuit base wires hvalid).builder.gates.length ≤
      base.gates.length + validCfgGateCoefficient tm * (H + 1) := by
  rw [validCfgCircuit_gate_delta]
  exact Nat.add_le_add_left (validCfgGateCost_le tm H) _

end

end CLRS.Chapter34.Turing.CookLevin


