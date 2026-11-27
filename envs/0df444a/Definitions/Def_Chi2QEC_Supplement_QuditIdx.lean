-- Prove2me | Definitions.Def_Chi2QEC_Supplement_QuditIdx
-- name    : Chi2QEC_Supplement_QuditIdx
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T03:06:21.700968+00:00
-- url     : https://prove2.me/theorems/ed736bb3-58f3-5db4-bd2f-efdc1e67fcbc
-- title:
--   Computational-basis index of $n$ qudits of dimension $q$
-- statement:
--   A physical qudit of dimension $q$ has the computational basis $|0\rangle,\dots,|q-1\rangle$. A computational-basis state of $n$ such qudits assigns to each qudit $\ell\in\{1,\dots,n\}$ a basis label $x_\ell\in\{0,\dots,q-1\}$.
--
--   The $n$-qudit Hilbert space $(\mathbb C^q)^{\otimes n}$ is spanned by these basis states, so its dimension is $q^n$, "the subspace dimensionality for $n$ physical qudits of dimension $q$" against which the qudit-rotation Hamming bound counts errors.
--
--   **Formalization Note** The index type is `Fin n → Fin q` and the Hilbert space is `EuclideanSpace ℂ (Fin n → Fin q)`. Section V A of the paper works with generic qudits, not with the three-mode Fock space of the $\chi^{(2)}$ codes.
-- source:
--   Niu–Chuang–Shapiro, Hardware-Efficient Bosonic QEC Codes Based on Symmetry Operators, arXiv:1709.05302v1, Sec. I, p.3; Theorem 1 and its proof, p.15

import Mathlib

namespace Chi2QEC.Supplement

/-- Niu–Chuang–Shapiro, *Hardware-Efficient Bosonic QEC Codes Based on Symmetry Operators*,
arXiv:1709.05302v1, Sec. V A, Theorem 1 and its proof, p.15 ("the subspace dimensionality for
n physical qudits of dimension q"), and Sec. I, p.3: the computational-basis index of `n`
physical qudits of dimension `q`; `x ℓ` is the basis state `|x ℓ⟩ ∈ {|0⟩, …, |q - 1⟩}` of qudit
`ℓ`. The `n`-qudit Hilbert space `(ℂ^q)^{⊗n}` is `EuclideanSpace ℂ (QuditIdx n q)`, of dimension
`qⁿ`.

**Formalization Note.** Sec. V A works with generic qudits, not with the three-mode Fock space
`FockIdx` of the χ(2) codes. -/
abbrev QuditIdx (n q : ℕ) := Fin n → Fin q

end Chi2QEC.Supplement


