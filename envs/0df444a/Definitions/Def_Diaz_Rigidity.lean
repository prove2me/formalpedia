-- Prove2me | Definitions.Def_Diaz_Rigidity
-- name    : Diaz_Rigidity
-- status  : Definition
-- author  : @carlok
-- created : 2026-09-07T08:20:24.270419+00:00
-- url     : https://prove2.me/theorems/26cf7c4e-3390-4a00-9d7e-cfa989b22309
-- title:
--   The rank-one matrix $H(u,r) = \begin{pmatrix} u & r \\ r & \bar u\end{pmatrix}$
-- statement:
--   For complex numbers $u$ and $r$, define the $2 \times 2$ complex matrix
--
--   $$H(u,r) = \begin{pmatrix} u & r \\ r & \bar u \end{pmatrix},$$
--
--   where $\bar u$ is the complex conjugate of $u$.
--
--   The intended input is a hypothetical counterexample $u$ to Diaz's modulus conjecture together with $r = \sqrt{\rho}$, where $\rho = u\bar u = |u|^{2}$. In that case $\det H = u\bar u - r^{2} = 0$, so the two rows are linearly dependent **over $\mathbb{C}$**  yet no coefficient $w^{\mathsf{T}} H v$ vanishes for non-zero vectors $w, v$ with entries in the base field. Dependent over $\mathbb{C}$, independent over $K$ — that gap is the four exponentials problem in miniature, and it places $H$ exactly at the boundary of the Matrix Coefficient Conjecture.
--
--   Only the definition is given here  the two properties just described are separate theorems.
-- source:
--   https://github.com/carlok/diaz-modulus-lean/blob/801802b8ac052dff50baf17ac4a7ceac3e994ca9/Diaz/Rigidity.lean#L29-L31

/-
# The rank-one matrix attached to a candidate

The rank-one matrix attached to a candidate: the concrete object at the
boundary of the Matrix Coefficient Conjecture.

For a candidate `u` with `ρ = u * conj u` and `r = √ρ`, the matrix

    H = ( u  r )
        ( r  ū )

has vanishing determinant — its rows are dependent over `ℂ` — and yet no
coefficient `wᵀ H v` vanishes for non-zero `w, v` over the base field.
Dependent over `ℂ`, independent over `K`. That gap is the four
exponentials problem in miniature, and it is why `H` sits exactly at the
boundary of the Matrix Coefficient Conjecture.

Note what is *not* needed: transcendence of `u`. Only `u ∉ K` is used.
-/
import Mathlib

open ComplexConjugate

namespace Diaz

variable {K : Subfield ℂ} {u r : ℂ}

/-- The matrix `H` attached to a candidate. -/
noncomputable def Hmat (u r : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![u, r; r, conj u]

/-! ## Linking the coefficient to the matrix

The statement above writes the coefficient out by hand.  This says it is
`wᵀ H v`, so that `det_Hmat` and `no_vanishing_coeff` are about the same
object. -/

/-! ## End to end

The one statement that starts from the arithmetic hypothesis rather than
from transcendence.  This is the only place where being a Diaz candidate,
rather than merely being outside the base field, is what is assumed. -/

end Diaz


