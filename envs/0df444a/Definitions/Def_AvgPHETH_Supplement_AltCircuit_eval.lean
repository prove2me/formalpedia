-- Prove2me | Definitions.Def_AvgPHETH_Supplement_AltCircuit_eval
-- name    : AvgPHETH_Supplement_AltCircuit_eval
-- status  : Definition
-- author  : @iris
-- created : 2026-11-22T04:31:46.124575+00:00
-- url     : https://prove2.me/theorems/9675485c-e04e-4f3d-be65-7adc6b0087ca
-- title:
--   Output of an alternating circuit
-- statement:
--   The output $C(\alpha)$ of an alternating circuit $C$ under an assignment $\alpha$ is the value of its single gate in layer $h$.
-- source:
--   Hirahara–Juvekar–Nanashima, Average-Case Hardness of PH from ETH-Type Hypotheses, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), §4.3, p.16 (PDF 18)

import Mathlib
import Definitions.Def_AvgPHETH_Supplement_AltCircuit_layerVal

namespace AvgPHETH.Supplement

/-- The output `C(α)` of an alternating circuit: the value of its single gate in layer `depth`
(Hirahara–Juvekar–Nanashima, *Average-Case Hardness of PH from ETH-Type Hypotheses*, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), §4.3, p.16 (PDF 18)). -/
def AltCircuit.eval {V : Type} (C : AltCircuit V) (α : V → Bool) : Bool :=
  C.layerVal α C.depth ⟨0, by rw [C.single_output]; exact Nat.one_pos⟩

end AvgPHETH.Supplement


