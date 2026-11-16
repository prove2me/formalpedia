-- Prove2me | Definitions.Def_QStateSearch_Supplement_testBlock
-- name    : QStateSearch_Supplement_testBlock
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:22:15.359425+00:00
-- url     : https://prove2.me/theorems/d6dfa0d5-e1f8-463b-a726-62fe87d4c90e
-- title:
--   Testing block $W_n$ of the random-subset oracle
-- statement:
--   For label sets $L_n\subseteq\{0,1\}^n$ and $n$-qubit vectors $\psi_x$, the testing block $W_n$ on $2n+1$ qubits (a control qubit, an $n$-bit label register, an $n$-qubit state register) acts by
--   $$W_n|c,x\rangle|\phi\rangle=|c,x\rangle\,R_{\psi_x}^{\,c\cdot 1[x\in L_n]}|\phi\rangle\qquad\text{(Eq. (4))}:$$
--   a controlled query at $x\in L_n$ applies the reflection about $|\psi_x\rangle$, a query at $x\notin L_n$ the identity.
-- source:
--   Barhoush, Quantum State Search with Classical Interactive Advice, arXiv:2610.25657 (held version, sha256 2a16939a…3408), Eq. (4), p.17

import Mathlib
import Definitions.Def_QStateSearch_refl
import Definitions.Def_QStateSearch_Supplement_qIdx
import Definitions.Def_QStateSearch_Supplement_blockAt

set_option autoImplicit false

namespace QStateSearch.Supplement

open Classical in
/-- The **testing block** `W_n` of Section 6 on `k = 2n + 1` qubits: wire `0` is a control
qubit `c`, wires `1, …, n` the label `x`, wires `n + 1, …, 2n` an `n`-qubit state register, and
`W_n|c, x⟩|ϕ⟩ = |c, x⟩ R_{ψ_x}^{c·1[x ∈ L_n]} |ϕ⟩` (`R_ψ` the base mission's
`QStateSearch.refl`, reindexed to `{0,1}^n` by `qIdx`).

Barhoush, *Quantum State Search with Classical Interactive Advice*, arXiv:2610.25657
(held version, sha256 2a16939a…3408), Eq. (4), p.17: "The testing component W_n has a control qubit, an n-bit label register, and
an n-qubit state register. On computational-basis control and label registers, it acts as
W_n|c, x⟩|ϕ⟩ = |c, x⟩ R^{c 1[x∈L_n]}_{ψ_x} |ϕ⟩."

**Formalization Note.** The matrix is written for any `k` (entries vanish unless the two basis
states agree outside the state register); the oracle uses it only for `k = 2n + 1`. -/
noncomputable def testBlock (L : (n : ℕ) → Finset (Fin n → Bool))
    (ψ : (n : ℕ) → (Fin n → Bool) → EuclideanSpace ℂ (Fin (2 ^ n))) (n k : ℕ) :
    Matrix (Fin k → Bool) (Fin k → Bool) ℂ :=
  Matrix.of fun z z' =>
    if ∀ i : Fin k, (i.val < n + 1 ∨ 2 * n + 1 ≤ i.val) → z i = z' i then
      (if bitAt z 0 = true ∧ blockAt z 1 n ∈ L n then
        QStateSearch.refl (ψ n (blockAt z 1 n)) (qIdx n (blockAt z (n + 1) n))
          (qIdx n (blockAt z' (n + 1) n))
      else if blockAt z (n + 1) n = blockAt z' (n + 1) n then 1 else 0)
    else 0

end QStateSearch.Supplement


