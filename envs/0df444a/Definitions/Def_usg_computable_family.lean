-- Prove2me | Definitions.Def_usg_computable_family
-- name    : usg_computable_family
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-14T12:16:34.642436+00:00
-- url     : https://prove2.me/theorems/b2745244-ec05-436c-be1e-17a815e005b9
-- title:
--   Uniformly computable family of complex matrices
-- statement:
--   A family of complex matrices $A(0), A(1), A(2), \dots$ of a fixed size, indexed by the natural numbers, is called **uniformly computable** when its entries are computable complex numbers, uniformly in the index and in the matrix position: there are computable functions
--
--   $$
--   \mathrm{re},\ \mathrm{im} : \mathbb N \times \mathbb N \times I \times I \to \mathbb Q
--   $$
--
--   on the index set $I$ of the matrices such that for every index $n$, every precision $k$ and every position $(i,j)$,
--
--   $$
--   \Big| A(n)_{ij} - \big(\mathrm{re}(n,k,i,j) + \mathrm i\,\mathrm{im}(n,k,i,j)\big) \Big| \le 2^{-k}.
--   $$
--
--   This is the standard notion of a uniformly computable sequence of complex numbers, arranged for matrix families. Its role in the undecidability results for the spectral gap is to express the requirement that the interactions of a Hamiltonian be computable functions of the input: only that requirement prevents a family from consulting the halting behaviour of the machine it is meant to simulate. Requiring instead that each matrix entry be algebraic constrains every matrix separately and says nothing about the dependence of the family on the index, so it does not capture the same content.
-- source:
--   Cubitt, Perez-Garcia & Wolf, Undecidability of the Spectral Gap, Forum of Mathematics Pi 10:e14 (2022), doi:10.1017/fmp.2021.15, Section 6.1, pp. 93-94 (the interactions of Proposition 53 and Corollary 54 are computable functions of the input).

import Definitions.Def_usg_spectral_notions

set_option autoImplicit false

namespace UndecidableSpectralGap

/-- A family `A : ℕ → Matrix m m ℂ` of complex matrices is **uniformly computable** if its
entries are computable complex numbers, uniformly in the index `n` and in the matrix
position: there are computable functions `re, im` producing, for every index `n`, every
precision `k` and every matrix position `(i, j)`, rational numbers approximating the real
and the imaginary part of the entry `A n i j` to within `2 ^ (-k)`.

This is the formal counterpart of the requirement, in the constructions of Cubitt,
Perez-Garcia and Wolf, that the interactions of the Hamiltonian be *computable functions of
the input* — the property that makes the halting information genuinely inaccessible to the
model. Requiring only that each individual entry be algebraic does not express it, since
that constrains every matrix separately and says nothing about how the family depends
on `n`. -/
def ComputableMatrixFamily {m : Type} [Fintype m] [DecidableEq m] [Primcodable m]
    (A : ℕ → Matrix m m ℂ) : Prop :=
  ∃ re im : ℕ × ℕ × m × m → ℚ, Computable re ∧ Computable im ∧
    ∀ (n k : ℕ) (i j : m),
      ‖A n i j - ((re (n, k, i, j) : ℂ) + (im (n, k, i, j) : ℂ) * Complex.I)‖
        ≤ 1 / 2 ^ k

end UndecidableSpectralGap


