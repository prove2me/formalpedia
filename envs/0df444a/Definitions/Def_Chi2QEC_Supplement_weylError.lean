-- Prove2me | Definitions.Def_Chi2QEC_Supplement_weylError
-- name    : Chi2QEC_Supplement_weylError
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T03:06:41.26323+00:00
-- url     : https://prove2.me/theorems/880c6e53-7303-509b-aa4b-a1f16577c2fd
-- title:
--   Generalized Pauli (qudit-rotation) error $\bigotimes_\ell X^{a_\ell}Z^{b_\ell}$
-- statement:
--   On one qudit of dimension $q$ let $X|j\rangle=|j+1 \bmod q\rangle$ be the shift and $Z|j\rangle=\omega^j|j\rangle$ the clock operator, where $\omega=e^{2\pi i/q}$. For exponents $e=((a_1,b_1),\dots,(a_n,b_n))$ with $a_\ell,b_\ell\in\{0,\dots,q-1\}$, the generalized Pauli operator on $n$ qudits is
--   $$
--   W_e=\bigotimes_{\ell=1}^{n}X^{a_\ell}Z^{b_\ell},\qquad W_e|y\rangle=\prod_{\ell}\omega^{b_\ell y_\ell}\,|y+a\rangle .
--   $$
--
--   The $q^2$ operators $X^aZ^b$ of one qudit form a basis of all $q\times q$ matrices; the $q^2-1$ of them with $(a,b)\neq(0,0)$ are the paper's "$(q^2-1)$ independent error operators" per affected qudit, and $W_e$ with $e=0$ is the identity.
--
--   **Formalization Note** The matrix entry at row $x$, column $y$ is $\prod_\ell[x_\ell=y_\ell+a_\ell \bmod q]\,\omega^{b_\ell y_\ell}$; the addition is that of `Fin q`, i.e. modulo $q$.
-- source:
--   Niu–Chuang–Shapiro, Hardware-Efficient Bosonic QEC Codes Based on Symmetry Operators, arXiv:1709.05302v1, proof of Theorem 1, p.15

import Mathlib
import Definitions.Def_Chi2QEC_Supplement_QuditIdx

namespace Chi2QEC.Supplement

/-- Niu–Chuang–Shapiro, *Hardware-Efficient Bosonic QEC Codes Based on Symmetry Operators*,
arXiv:1709.05302v1, Sec. V A, proof of Theorem 1, p.15 (a weight-`j` error's "decomposition into
(q² − 1)ʲ independent error operators"): the generalized Pauli (Weyl) operator
`⊗_ℓ X^{a_ℓ} Z^{b_ℓ}` with `(a_ℓ, b_ℓ) = e ℓ`, where `X|j⟩ = |j + 1 mod q⟩` and
`Z|j⟩ = ω^j |j⟩`, `ω = exp(2πi/q)`.

**Formalization Note.** The matrix entry at row `x`, column `y` is
`∏_ℓ [x ℓ = y ℓ + a_ℓ mod q] · ω^{b_ℓ · y ℓ}`, i.e. `X^a Z^b |y⟩ = ω^{b y} |y + a⟩` on each qudit
(`Fin` addition is addition mod `q`). The `q²` operators `X^a Z^b` of one qudit form a basis of the
`q × q` matrices; the `q² − 1` with `(a, b) ≠ (0, 0)` are the paper's independent nontrivial
qudit-rotation errors. -/
noncomputable def weylError (n q : ℕ) (e : Fin n → Fin q × Fin q) :
    Matrix (QuditIdx n q) (QuditIdx n q) ℂ :=
  fun x y => ∏ ℓ, if x ℓ = y ℓ + (e ℓ).1 then
      Complex.exp (2 * Real.pi * Complex.I * (((e ℓ).2 : ℕ) * (y ℓ : ℕ) : ℕ) / (q : ℂ))
    else 0

end Chi2QEC.Supplement


