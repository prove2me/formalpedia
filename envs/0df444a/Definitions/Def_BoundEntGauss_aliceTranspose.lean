-- Prove2me | Definitions.Def_BoundEntGauss_aliceTranspose
-- name    : BoundEntGauss_aliceTranspose
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:47:49.944205+00:00
-- url     : https://prove2.me/theorems/613bba80-fb47-439e-b483-d99c533273e8
-- title:
--   Partial transpose on Alice's tensor factor
-- statement:
--   Let $\mathcal H_A\otimes\mathcal H_B$ be a bipartite Hilbert space with orthonormal product basis $|i\rangle\otimes|j\rangle$, $i\in I$, $j\in J$; Alice holds the first factor. For an operator $X$ with matrix elements $X_{(i,j),(k,l)}$, the **partial transpose with respect to Alice** is the operator $X^{T_A}$ with
--
--   $$
--   \bigl(X^{T_A}\bigr)_{(i,j),(k,l)} = X_{(k,j),(i,l)} ,
--   $$
--
--   that is, Alice's indices are exchanged and Bob's are kept.
--
--   On the oscillator Fock space the basis is the number basis. In it position operators have real and momentum operators imaginary matrix elements, so the partial transpose reverses Alice's momenta and keeps her positions, which is how the paper describes it.
--
--   **Formalization Note** Stated for arbitrary index types $I$, $J$; the mission uses the full occupation-number labels of $n$ and $m$ modes, without cutoff.
-- source:
--   Werner, Wolf, Bound entangled Gaussian states, arXiv:quant-ph/0009118v1, Section II, p. 3 (paragraph before Proposition 2)

import Mathlib

namespace BoundEntGauss

/-- **Partial transpose on Alice's factor, in the product basis.**
Werner, Wolf, *Bound entangled Gaussian states*, arXiv:quant-ph/0009118v1, Section II, p. 3 (unnumbered paragraph before Proposition 2).

For a kernel `X` on a product index `I × J` (Alice is the first factor), the partial transpose
with respect to Alice is `(Xᵀᴬ) (i, j) (k, l) = X (k, j) (i, l)`: Alice's indices are swapped and
Bob's are kept.

**Formalization Note.** On the multimode Fock space, `I = Occupation (Fin n)` and
`J = Occupation (Fin m)` are the full occupation labels, so this is the transpose in the Fock
(number) basis of Alice. In that basis position operators are real and momentum operators are
imaginary, so the transpose reverses Alice's momenta and keeps her positions, which is the
characterization the paper uses on p. 3. The definition is stated for arbitrary index types. -/
def aliceTranspose {I J : Type} (X : Matrix (I × J) (I × J) ℂ) : Matrix (I × J) (I × J) ℂ :=
  fun u v => X (v.1, u.2) (u.1, v.2)

end BoundEntGauss


