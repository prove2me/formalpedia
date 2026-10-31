-- Prove2me | Definitions.Def_RainsSep_Distill_pairPower
-- name    : RainsSep_Distill_pairPower
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T15:56:16.211116+00:00
-- url     : https://prove2.me/theorems/ffa67037-0d5a-4960-9997-49dc318e190f
-- title:
--   The $n$-pair tensor power $\rho^{\otimes n}$ of a bipartite state
-- statement:
--   Let $\rho$ be an operator on $A\otimes A$ (Alice $\otimes$ Bob). Its **$n$-pair tensor power** $\rho^{\otimes n}$ is the operator on $A^{\otimes n}\otimes A^{\otimes n}$ describing $n$ independent copies of $\rho$, where Alice holds the first halves of all copies and Bob the second halves. For basis strings $a=(a_1,\dots,a_n)$, $b,c,d$,
--
--   $$
--   \big(\rho^{\otimes n}\big)_{(a,b),(c,d)}=\prod_{k=1}^n \rho_{(a_k,b_k),(c_k,d_k)} .
--   $$
--
--   This is the input of a distillation protocol acting on $n$ shared pairs.
--
--   **Formalization Note** Alice's $k$-th subsystem is paired with Bob's $k$-th subsystem. For $A=\mathbb C^2$ both registers are $n$-qubit registers. For $n=0$ it is the $1\times 1$ identity.
-- source:
--   Rains, Entanglement purification via separable superoperators, arXiv:quant-ph/9707002v3, p. 1 (Eqs. (3)–(4), states on V^{⊗n_i}) and Eq. (21), p. 2

import Mathlib

namespace RainsSep.Distill

/-- **The `n`-pair tensor power `ρ^{⊗n}` of a bipartite state.**
Rains, *Entanglement purification via separable superoperators*, arXiv:quant-ph/9707002v3, p. 1 (Eqs. (3)–(4): "P_i mapping states on V^{⊗n_i}") and Eq. (21), p. 2
(`F_P(Δ(ε)^{⊗n})`).

For an operator `ρ` on `α ⊗ α` (Alice ⊗ Bob), `pairPower ρ n` is the operator on
`αⁿ ⊗ αⁿ` whose matrix entries are
`(ρ^{⊗n})_{(a,b),(c,d)} = Π_k ρ_{(a_k,b_k),(c_k,d_k)}`: `n` copies of `ρ`, Alice holding the
first register `a = (a_1, …, a_n)` and Bob the second.

**Formalization Note.** Alice's `k`-th subsystem is paired with Bob's `k`-th subsystem; for
`α = Bool` both registers are `n`-qubit registers `Fin n → Bool`. For `n = 0` this is the
`1 × 1` identity. -/
def pairPower {α : Type*} (ρ : Matrix (α × α) (α × α) ℂ) (n : ℕ) :
    Matrix ((Fin n → α) × (Fin n → α)) ((Fin n → α) × (Fin n → α)) ℂ :=
  Matrix.of fun p q => ∏ k, ρ (p.1 k, p.2 k) (q.1 k, q.2 k)

end RainsSep.Distill


