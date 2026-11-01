-- Prove2me | Definitions.Def_WildeQIT_EntManip_tensorPowVec
-- name    : WildeQIT_EntManip_tensorPowVec
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T18:36:12.367838+00:00
-- url     : https://prove2.me/theorems/d06ef16b-b030-4df7-8ac9-94c33e2709d3
-- title:
--   Tensor power $|\psi\rangle_{AB}^{\otimes n}$ across the cut $A^n:B^n$
-- statement:
--   Let $|\psi\rangle_{AB}\in\mathcal H_A\otimes\mathcal H_B$ with amplitudes $\psi(x,y)$ in product bases. Its $n$-th tensor power, regarded as a bipartite vector of Alice's systems $A^n=A_1\cdots A_n$ and Bob's systems $B^n=B_1\cdots B_n$, is
--
--   $$
--   |\psi\rangle_{AB}^{\otimes n}\in\mathcal H_A^{\otimes n}\otimes\mathcal H_B^{\otimes n},\qquad \psi^{\otimes n}(x^n,y^n)=\prod_{i=1}^n\psi(x_i,y_i).
--   $$
--
--   For $n=0$ it is the number $1$, the state of the trivial system.
--
--   **Formalization Note** $A^n$ is indexed by `Fin n → a` and $B^n$ by `Fin n → b`, so the result is a vector on `(Fin n → a) × (Fin n → b)`.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, §19.3, p. 540

import Mathlib

namespace WildeQIT.EntManip

/-- **Tensor power of a bipartite pure state across the `Aⁿ : Bⁿ` cut** (Wilde, *From Classical
to Quantum Shannon Theory*, arXiv:1106.1445v8, §19.3, p. 540): for `|ψ⟩_{AB} ∈ H_A ⊗ H_B`,
`(|ψ⟩_{AB})^{⊗n} ∈ H_A^{⊗n} ⊗ H_B^{⊗n} = H_{Aⁿ} ⊗ H_{Bⁿ}`, with amplitudes
`ψ^{⊗n}(xⁿ, yⁿ) = ∏_{i=1}^n ψ(x_i, y_i)`.

**Formalization Note** The `n` copies of `A` (Alice's systems) are grouped into the index type
`Fin n → a` and the `n` copies of `B` into `Fin n → b`, so that the result is a bipartite vector
on `(Fin n → a) × (Fin n → b)` across Alice's and Bob's laboratories. For `n = 0` both index
types have one element and the vector is the number `1`, the state of the trivial system. -/
def tensorPowVec {a b : Type} (ψ : a × b → ℂ) (n : ℕ) : (Fin n → a) × (Fin n → b) → ℂ :=
  fun z => ∏ i, ψ (z.1 i, z.2 i)

end WildeQIT.EntManip


