-- Prove2me | Definitions.Def_WildeQIT_Schumacher_tensorPow
-- name    : WildeQIT_Schumacher_tensorPow
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T18:35:51.881686+00:00
-- url     : https://prove2.me/theorems/713805d2-a0ec-4f6d-b7f3-13b0aefc4145
-- title:
--   $n$-fold tensor power $M^{\otimes n}$ of a matrix
-- statement:
--   Let $M$ be a complex matrix with rows indexed by a finite set $a$ and columns by $b$ (an operator from $\mathbb C^b$ to $\mathbb C^a$). Its $n$-fold tensor power $M^{\otimes n}$ is the operator on $(\mathbb C^{b})^{\otimes n}$, whose standard basis is indexed by sequences $y^n = (y_1,\dots,y_n)$, with entries
--
--   $$
--   (M^{\otimes n})_{x^n,\,y^n} = \prod_{i=1}^n M_{x_i,\,y_i}.
--   $$
--
--   For a density operator $\rho_A$ this is the state $\rho_{A^n} = \rho_{A_1}\otimes\cdots\otimes\rho_{A_n} = (\rho_A)^{\otimes n}$ of $n$ independent copies of a quantum information source (eq. (15.5)).
--
--   **Formalization Note** Copy $i$ is the $i$-th coordinate of the sequence (`Fin n → a`). At $n = 0$ the power is the $1\times 1$ identity on the one-point index type.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, eq. (15.5), p. 463

import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Fin

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, §15.1, eq. (15.5), p. 463:
the state of `n` copies of a quantum information source is `ρ_{Aⁿ} ≡ ρ_{A₁} ⊗ ⋯ ⊗ ρ_{Aₙ} = (ρ_A)^{⊗n}`.
-/

namespace WildeQIT.Schumacher

/-- **`n`-fold tensor power** `M^{⊗n}` (Wilde, arXiv:1106.1445v8, eq. (15.5), p. 463). For a
matrix `M : Matrix a b ℂ` (an operator from `ℋ_b` to `ℋ_a`), `M^{⊗n}` acts on
`ℋ^{⊗n}`, whose standard basis is indexed by sequences `xⁿ : Fin n → a`, and has entries
`(M^{⊗n})_{xⁿ, yⁿ} = ∏ᵢ M_{xᵢ, yᵢ}`.

**Formalization Note.** Copy `i` of the system is the `i`-th coordinate of the sequence; at
`n = 0` the power is the `1 × 1` identity on the one-point index type. -/
def tensorPow {a b : Type} (n : ℕ) (M : Matrix a b ℂ) : Matrix (Fin n → a) (Fin n → b) ℂ :=
  Matrix.of fun x y => ∏ i, M (x i) (y i)

end WildeQIT.Schumacher


