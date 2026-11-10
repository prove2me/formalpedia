-- Prove2me | Definitions.Def_BorderDiffEq_AffineForm
-- name    : BorderDiffEq_AffineForm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:25:15.414251+00:00
-- url     : https://prove2.me/theorems/06a194a8-2474-4c8f-ad01-57eaa1c82032
-- title:
--   Affine linear polynomials $\ell(x)=c+\sum_l a_l x_l$
-- statement:
--   An **affine linear polynomial** over a commutative ring $K$ in variables $x=(x_l)_{l\in\sigma}$ ($\sigma$ finite) is
--   $$
--   \ell(x)=c+\sum_{l\in\sigma}a_l\,x_l ,\qquad c,a_l\in K .
--   $$
--   It is stored by its constant $c$ and its coefficient vector $a$; $\mathrm{supp}(\ell)=\{l : a_l\neq0\}$ is the set of variables it uses, and $|\mathrm{supp}(\ell)|$ enters the size of a depth-3 circuit.
--
--   Affine forms are the bottom gates of depth-3 circuits, the bases of the powers in $\Sigma\wedge\Sigma$ circuits, and the edge labels of algebraic branching programs.
--
--   **Formalization Note** `toPoly` is the polynomial $c+\sum_l a_lx_l$ in `MvPolynomial σ K`; `supportCard` is $|\mathrm{supp}(\ell)|$.
-- source:
--   Bhat–Dutta–Kaplan–Shpilka–Shringi, Demystifying Border of Structured Algebraic Circuits via Differential Equations, manuscript (STOC 2027 submission; preprint basis, sha256 583bcc89e7078b50ae14babedf540a37b37e36912abda1931e4aaeb64bc57db8), §2.1, p.5, display (2); Definition 4.8, p.27

import Mathlib

namespace BorderDiffEq

/-- **Affine linear polynomials** (Bhat–Dutta–Kaplan–Shpilka–Shringi, *Demystifying Border of
Structured Algebraic Circuits via Differential Equations*, manuscript (STOC 2027 submission),
§2.1, p.5, display (2), and Definition 4.8, p.27): an affine linear polynomial
`ℓ(x) = c + ∑ₗ aₗ xₗ` over a commutative ring `K` in the variables indexed by `σ`.

**Formalization Note.** An affine form is stored by its constant `c` and its coefficient vector
`a`, so that circuit sizes can count the variables it actually uses (`supportCard`). The variables
are indexed by a finite type `σ` (in this mission `Fin n`). -/
structure AffineForm (K : Type) (σ : Type) where
  /-- the constant term -/
  c : K
  /-- the coefficient of each variable -/
  a : σ → K

namespace AffineForm

variable {K σ : Type}

/-- The polynomial `c + ∑ₗ aₗ xₗ` of an affine form. -/
noncomputable def toPoly [CommRing K] [Fintype σ] (ℓ : AffineForm K σ) : MvPolynomial σ K :=
  MvPolynomial.C ℓ.c + ∑ l, MvPolynomial.C (ℓ.a l) * MvPolynomial.X l

/-- The number of variables with a nonzero coefficient. -/
noncomputable def supportCard [Zero K] [Fintype σ] (ℓ : AffineForm K σ) : ℕ := by
  classical
  exact (Finset.univ.filter fun l => ℓ.a l ≠ 0).card

end AffineForm

end BorderDiffEq


