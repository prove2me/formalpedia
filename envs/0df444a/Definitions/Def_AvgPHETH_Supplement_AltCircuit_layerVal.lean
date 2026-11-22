-- Prove2me | Definitions.Def_AvgPHETH_Supplement_AltCircuit_layerVal
-- name    : AvgPHETH_Supplement_AltCircuit_layerVal
-- status  : Definition
-- author  : @iris
-- created : 2026-11-22T04:31:15.506353+00:00
-- url     : https://prove2.me/theorems/f0850c18-db54-4b54-b2ff-bb334aad73e0
-- title:
--   Values of the vertices of an alternating circuit
-- statement:
--   Under an assignment $\alpha$, an input vertex takes the value of its label. A gate in layer $j$ is an AND gate if it has the type of the output gate and $h-j$ is even, or the opposite type and $h-j$ is odd. Otherwise it is an OR gate. It takes the AND, respectively the OR, of the values of its inputs in layer $j-1$.
-- source:
--   Hirahara–Juvekar–Nanashima, Average-Case Hardness of PH from ETH-Type Hypotheses, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), §4.3, p.16 (PDF 18)

import Mathlib
import Definitions.Def_AvgPHETH_Supplement_AltCircuit
import Definitions.Def_AvgPHETH_Supplement_Lit_eval

namespace AvgPHETH.Supplement

/-- The value of every vertex of layer `j` of an alternating circuit under an assignment `α`
(Hirahara–Juvekar–Nanashima, *Average-Case Hardness of PH from ETH-Type Hypotheses*, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), §4.3, p.16 (PDF 18)): input vertices take the value of their label; a gate of layer `j + 1`
is the AND (if `depth - (j + 1)` is even and the output is AND, or it is odd and the output is OR) or
else the OR of its inputs. -/
def AltCircuit.layerVal {V : Type} (C : AltCircuit V) (α : V → Bool) :
    (j : ℕ) → Fin (C.size j) → Bool
  | 0, i => (C.input i).eval α
  | j + 1, g =>
      if (if Even (C.depth - (j + 1)) then C.outAnd else !C.outAnd) then
        decide (∀ u ∈ C.wires j g, C.layerVal α j u = true)
      else
        decide (∃ u ∈ C.wires j g, C.layerVal α j u = true)

end AvgPHETH.Supplement


