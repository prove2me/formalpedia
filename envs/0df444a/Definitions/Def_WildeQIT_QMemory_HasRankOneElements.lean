-- Prove2me | Definitions.Def_WildeQIT_QMemory_HasRankOneElements
-- name    : WildeQIT_QMemory_HasRankOneElements
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T17:56:15.838787+00:00
-- url     : https://prove2.me/theorems/31780468-e7b8-433a-a515-6b3afe482811
-- title:
--   Rank-one elements $\Lambda_y=|\varphi_y\rangle\langle\varphi_y|$
-- statement:
--   A family of operators $\{\Lambda_y\}$ on $\mathcal H_A$ **has rank-one elements** if every element is of the form
--
--   $$
--   \Lambda_y=|\varphi_y\rangle\langle\varphi_y|
--   $$
--
--   for some vector $|\varphi_y\rangle\in\mathcal H_A$. A POVM with this property is what the book calls a **rank-one POVM**: "those with $\Lambda_y=|\varphi_y\rangle\langle\varphi_y|$ for some vectors $|\varphi_y\rangle$ such that $\mathrm{Tr}\{|\varphi_y\rangle\langle\varphi_y|\}\le 1$ and $\sum_y|\varphi_y\rangle\langle\varphi_y|=I$".
--
--   **Formalization Note** $|\varphi\rangle\langle\varphi|$ is `Matrix.vecMulVec φ (star φ)`. As in the book's parenthetical definition the vectors need not be nonzero; a zero element is an outcome of probability zero. The bound $\mathrm{Tr}\{|\varphi_y\rangle\langle\varphi_y|\}\le 1$ follows from $\sum_y|\varphi_y\rangle\langle\varphi_y|=I$ and is not repeated.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Theorem 11.1.1, p. 323 (parenthetical definition of rank-one POVMs)

import Mathlib

namespace WildeQIT.QMemory

/-- **Rank-one elements** (Wilde, *From Classical to Quantum Shannon Theory*,
arXiv:1106.1445v8, Theorem 11.1.1, p. 323): a family of operators whose every element has the
form `Λ_y = |φ_y⟩⟨φ_y|` for some vector `|φ_y⟩`. A POVM with this property is what the book
calls a rank-one POVM ("those with `Λ_y = |φ_y⟩⟨φ_y|` for some vectors `|φ_y⟩` such that
`Tr{|φ_y⟩⟨φ_y|} ≤ 1` and `∑_y |φ_y⟩⟨φ_y| = I`").

**Formalization Note** `|φ⟩⟨φ|` is `Matrix.vecMulVec φ (star φ)`. As in the book's parenthetical
definition, the vectors are not required to be nonzero; a zero element is an outcome of
probability zero. The book's `Tr{|φ_y⟩⟨φ_y|} ≤ 1` follows from `∑_y |φ_y⟩⟨φ_y| = I` and is not
repeated. -/
def HasRankOneElements {a x : Type} (Λ : x → Matrix a a ℂ) : Prop :=
  ∀ i, ∃ φ : a → ℂ, Λ i = Matrix.vecMulVec φ (star φ)

end WildeQIT.QMemory


