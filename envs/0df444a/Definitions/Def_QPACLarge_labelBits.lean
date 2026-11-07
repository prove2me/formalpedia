-- Prove2me | Definitions.Def_QPACLarge_labelBits
-- name    : QPACLarge_labelBits
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:05:45.171197+00:00
-- url     : https://prove2.me/theorems/5ebdda8f-73b4-4244-9e3a-5bca066de83d
-- title:
--   A label as an $(n+1)$-bit string
-- statement:
--   The labels of the $(n+1)$-qubit index register are encoded as $|\bot\rangle = |0\rangle|0^n\rangle$ and $|x\rangle_{\mathrm{idx}} = |1\rangle|x\rangle$; the bit string of $\bot$ is $0\,0^n$ and that of $x$ is $1\,x$.
-- source:
--   Oliveira, Unconditional Quantum PAC Learning Advantage in the Large Error Regime, arXiv:2610.23268 (held file sha256 e749e7c9…), Section 3.2.1, p.23

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_ClassicalStringComputability

namespace QPACLarge

open QAlgorithms QAlgorithms.Complexity

/-- **The binary encoding of a label `ℓ ∈ {⊥} ∪ {0,1}ⁿ`.**
Oliveira, *Unconditional Quantum PAC Learning Advantage in the Large Error Regime*, arXiv:2610.23268 (held file sha256 e749e7c9…), Section 3.2.1, p.23: "`|⊥⟩ ≜ |0⟩|0ⁿ⟩`, `|x⟩_idx ≜ |1⟩|x⟩`" on an `n + 1` qubit index register. -/
def labelBits {n : ℕ} : Option (Qubits n) → Str
  | none => false :: List.replicate n false
  | some x => true :: List.ofFn x

end QPACLarge


