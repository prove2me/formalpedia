-- Prove2me | Definitions.Def_polynomialDerivativeFrame
-- name    : polynomialDerivativeFrame
-- status  : Definition
-- author  : @shivm
-- created : 2026-09-12T17:32:31.497142+00:00
-- url     : https://prove2.me/theorems/2f81bad6-7005-47e0-9172-e96ca9715c6c
-- title:
--   Polynomial coordinates for derivatives with determinant regular at a point
-- statement:
--   Let $F\in\mathbb C[[X]]$, $\xi\in\mathbb C$, and $n\ge0$. A polynomial derivative frame consists of a polynomial $d$, a family $g_0,\ldots,g_{n-1}$ linearly independent over $\mathbb C[X]$, a polynomial matrix $A$ of size $n$, and a polynomial row $b$, satisfying
--
--   $$dF^{(i)}=\sum_j A_{ij}g_j\quad(0\le i<n),\qquad dF^{(n)}=\sum_j b_jg_j,$$
--
--   with $d(\xi)\ne0$ and $(\det A)(\xi)\ne0$.
--
--   The predicate records finite coordinate data for extracting a scalar differential equation ordinary at $\xi$. It makes no assertion that a frame exists and does not contain a minimal-equation hypothesis.
-- source:
--   Auxiliary formalization of Beukers, A refined version of the Siegel–Shidlovskii theorem, Theorem 3.2, printed pp. 6–7 (prescribed derivative rows and determinant equation), https://webspace.science.uu.nl/~beuke106/siegelshidlovskii.pdf. These explicit polynomial-numerator and module-coordinate interfaces are derived from the proof, not quoted named lemmas.

import Definitions.Def_beukersLiftingData

noncomputable section
open scoped BigOperators
namespace ArithmeticE

/-- Coordinates for the first `n+1` derivatives in a polynomially independent
family, after multiplication by one denominator regular at `ξ`.
The first `n` coordinate rows are invertible at `ξ`. -/
def PolynomialDerivativeFrame (F : PowerSeries ℂ) (ξ : ℂ) (n : ℕ) : Prop :=
  ∃ (d : Polynomial ℂ) (g : Fin n → PowerSeries ℂ)
    (A : Matrix (Fin n) (Fin n) (Polynomial ℂ)) (b : Fin n → Polynomial ℂ),
    d.eval ξ ≠ 0 ∧
    (∀ c : Fin n → Polynomial ℂ,
      (∑ j, (c j : PowerSeries ℂ) * g j) = 0 → ∀ j, c j = 0) ∧
    (∀ i : Fin n, (d : PowerSeries ℂ) * (PowerSeries.derivative ℂ)^[i.val] F =
      ∑ j, (A i j : PowerSeries ℂ) * g j) ∧
    (d : PowerSeries ℂ) * (PowerSeries.derivative ℂ)^[n] F =
      (∑ j, (b j : PowerSeries ℂ) * g j) ∧
    A.det.eval ξ ≠ 0

end ArithmeticE


