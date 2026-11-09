-- Prove2me | Definitions.Def_AgnosticTNS_bitsSplit
-- name    : AgnosticTNS_bitsSplit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:33:39.087971+00:00
-- url     : https://prove2.me/theorems/29bedde4-9660-475d-a579-3a9ebd37b151
-- title:
--   Data qubits and ancillas
-- statement:
--   A register of $a+b$ qubits is split into its first $a$ qubits (the encoded copies) and its last $b$ qubits (the ancillas).
-- source:
--   Caro–McHugh–Strelchuk, Efficient Agnostic Learning of Tensor Network States, STOC 2027 submission (manuscript sha256 d69077bb…abec0), Proposition 3.10, p.26

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Complexity

namespace AgnosticTNS

/-- **Splitting `a + b` qubits into the first `a` and the last `b`** (data wires, then ancillas),
for the learner model of Theorem 3.6 / Proposition 3.10, pp.23, 26 (Caro–McHugh–Strelchuk, *Efficient Agnostic Learning of Tensor Network States*, STOC 2027 submission manuscript (sha256 d69077bb…abec0)). -/
def bitsSplit (a b : ℕ) :
    QAlgorithms.Complexity.Bits (a + b) ≃ QAlgorithms.Complexity.Bits a × QAlgorithms.Complexity.Bits b :=
  (Equiv.arrowCongr finSumFinEquiv.symm (Equiv.refl Bool)).trans (Equiv.sumArrowEquivProdArrow _ _ _)

end AgnosticTNS


