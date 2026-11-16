-- Prove2me | Definitions.Def_QiOPoQ_Supplement_InCBQPO
-- name    : QiOPoQ_Supplement_InCBQPO
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:59:00.224895+00:00
-- url     : https://prove2.me/theorems/fcc28684-fe71-4bff-a2c8-976526364f7e
-- title:
--   The class $\mathcal C^O_{\mathsf{BQP}}$ of oracle BQP circuits
-- statement:
--   "For an oracle $O$, write $\mathcal C^O_{\mathsf{BQP}}$ for circuits with $O$-query gates whose channels relative to $O$ satisfy the condition defining $\mathcal C_{\mathsf{BQP}}$." A family of oracle circuits is in the class if it has polynomial size, one input and one output qubit, and for one negligible $\mu$ every member satisfies $\|C^O_\lambda-X^{b}(\cdot)\|_\diamond\le\mu(\lambda)$ for some bit $b$.
-- source:
--   Gheorghiu, Gupte, Havlíček, Liu, Verifiable Quantum Advantage and Computation via Quantum Circuit Obfuscation, arXiv:2609.40289 (sha256 fe2f9210…), §5.2, p.25

import Mathlib
import Definitions.Def_QAdvFew_PoQOracle_Negligible
import Definitions.Def_QiOPoQ_diamond
import Definitions.Def_QiOPoQ_bitFlip
import Definitions.Def_QiOPoQ_Supplement_ochan

set_option autoImplicit false

namespace QiOPoQ.Supplement

open QAdvFew.PoQOracle QAlgorithms.Complexity

variable {G : GateSet}

/-- **The class `C^O_BQP`.** Gheorghiu, Gupte, Havlíček, Liu, *Verifiable Quantum Advantage and
Computation via Quantum Circuit Obfuscation*, arXiv:2609.40289 (sha256 fe2f9210…), p.25: "For an
oracle O, write C^O_BQP for circuits with O-query gates whose channels relative to O satisfy the
condition defining C_BQP."

A family of oracle circuits is in `C^O_BQP` if it is polynomial-size, each member has one input and
one output qubit, and for one negligible `μ` each channel relative to `O` is within `μ(λ)` of
`X^b(·)` for some bit `b`: the published `QiOPoQ.InCBQP` with `ochanAs O` in place of `chanAs`. -/
def InCBQPO (O : Str → Bool) (Cf : ℕ → OCirc G) : Prop :=
  OPolySize Cf ∧ (∀ n, (Cf n).nin = 1) ∧ (∀ n, (Cf n).out.length = 1) ∧
    ∃ μ : ℕ → ℝ, Negligible μ ∧ ∀ n, ∃ b : Bool, diamond (ochanAs O (Cf n) 1 1) (bitFlip b) ≤ μ n

end QiOPoQ.Supplement


