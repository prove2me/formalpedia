-- Prove2me | Definitions.Def_QiOPoQ_Supplement_IsRowsCols
-- name    : QiOPoQ_Supplement_IsRowsCols
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:50:09.443867+00:00
-- url     : https://prove2.me/theorems/5a171615-18f3-4d10-b9c2-e169dfafe556
-- title:
--   Notation 5.1: admissible numbers of rows and columns
-- statement:
--   Functions $\mathrm{rows},\mathrm{cols}$ of $\lambda$ are admissible if both are computable from $1^\lambda$ in polynomial time and, for a polynomial $p$,
--
--   $$\lambda\le\mathrm{rows}(\lambda)\le p(\lambda),\qquad 2\le\mathrm{cols}(\lambda)\le p(\lambda).$$
--
--   They are the dimensions of the grid of obfuscated circuits in Figure 7.
-- source:
--   Gheorghiu, Gupte, Havlíček, Liu, Verifiable Quantum Advantage and Computation via Quantum Circuit Obfuscation, arXiv:2609.40289 (sha256 fe2f9210…), Notation 5.1, p.22

import Mathlib
import Definitions.Def_QAlgorithms_ClassicalStringComputability
import Definitions.Def_QAlgorithms_ClassicalUnaryInput

set_option autoImplicit false

namespace QiOPoQ.Supplement

open QAlgorithms.Complexity

/-- **Notation 5.1, first bullet.** Gheorghiu, Gupte, Havlíček, Liu, *Verifiable Quantum Advantage
and Computation via Quantum Circuit Obfuscation*, arXiv:2609.40289 (sha256 fe2f9210…),
Notation 5.1, p.22: "Let rows, cols ∈ N be efficiently computable from λ, with
λ ≤ rows ≤ poly(λ) and 2 ≤ cols ≤ poly(λ)."

**Formalization Note.** "Efficiently computable from λ" is polynomial-time computability from
`1^λ` (as for the published `QiOPoQ.IsAdmissibleRounds`); one polynomial bounds both. -/
def IsRowsCols (rows cols : ℕ → ℕ) : Prop :=
  PolyTimeComputable (fun w => unary (rows w.length)) ∧
    PolyTimeComputable (fun w => unary (cols w.length)) ∧
    ∃ p : Polynomial ℕ, ∀ n, n ≤ rows n ∧ rows n ≤ p.eval n ∧ 2 ≤ cols n ∧ cols n ≤ p.eval n

end QiOPoQ.Supplement


