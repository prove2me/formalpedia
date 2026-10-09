-- Prove2me | Definitions.Def_IntroMatrixConc_GaussianSeries_Models
-- name    : IntroMatrixConc_GaussianSeries_Models
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T02:40:53.18354+00:00
-- url     : https://prove2.me/theorems/1a82e1e6-95e0-4697-8b2a-7558249cca3e
-- title:
--   Gaussian Wigner, rectangular, signed-entry, and Toeplitz coefficient matrices
-- statement:
--   For a positive dimension $d$, the Wigner coefficient for $i<j$ has ones at $(i,j)$ and $(j,i)$ and zeros elsewhere. A rectangular coefficient has a single unit entry. Given a fixed matrix $B$, a signed-entry coefficient places $b_{ij}$ at $(i,j)$. A Toeplitz coefficient selects all entries on one diagonal $j-i=k$, where $-(d-1)\le k\le d-1$. The row and column energies of $B$ are the largest sums of squared entry magnitudes in a row or column.
--
--   These deterministic coefficient matrices specify the four random series in §§4.2–4.4. The Toeplitz index runs from the lower-left diagonal to the upper-right diagonal. The energy maxima are over the actual finite row and column sets.
-- source:
--   Tropp, An Introduction to Matrix Concentration Inequalities, arXiv:1501.01571v1, §§4.2.1–4.4, pp. 45–49

import Mathlib
import Definitions.Def_TroppMatrixConcentration_ch4_scalar_laws

open MeasureTheory ProbabilityTheory TroppMatrixConcentration
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace IntroMatrixConc.GaussianSeries

/-- The Hermitian coefficient of an upper triangular Gaussian Wigner entry. -/
def wignerCoeff {d : ℕ} (p : {p : Fin d × Fin d // p.1 < p.2}) :
    Matrix (Fin d) (Fin d) ℂ :=
  fun i j => if (i = p.1.1 ∧ j = p.1.2) ∨ (i = p.1.2 ∧ j = p.1.1) then 1 else 0

/-- The standard rectangular matrix unit. -/
def rectCoeff {d₁ d₂ : ℕ} (p : Fin d₁ × Fin d₂) :
    Matrix (Fin d₁) (Fin d₂) ℂ :=
  fun i j => if i = p.1 ∧ j = p.2 then 1 else 0

/-- A matrix unit weighted by its fixed complex entry. -/
def signedCoeff {d₁ d₂ : ℕ} (B : Matrix (Fin d₁) (Fin d₂) ℂ)
    (p : Fin d₁ × Fin d₂) : Matrix (Fin d₁) (Fin d₂) ℂ :=
  fun i j => if i = p.1 ∧ j = p.2 then B p.1 p.2 else 0

/-- A diagonal indicator in a Toeplitz matrix, indexed from `-(d-1)` to `d-1`. -/
def toeplitzCoeff {d : ℕ} (k : Fin (2 * d - 1)) :
    Matrix (Fin d) (Fin d) ℂ :=
  fun i j => if (j : ℤ) - (i : ℤ) = (k : ℤ) - ((d : ℤ) - 1) then 1 else 0

/-- Largest squared Euclidean norm of a row. -/
def rowEnergy {d₁ d₂ : ℕ} (B : Matrix (Fin d₁) (Fin d₂) ℂ) : ℝ :=
  sSup (Set.range (fun i : Fin d₁ => ∑ j : Fin d₂, ‖B i j‖ ^ 2))

/-- Largest squared Euclidean norm of a column. -/
def colEnergy {d₁ d₂ : ℕ} (B : Matrix (Fin d₁) (Fin d₂) ℂ) : ℝ :=
  sSup (Set.range (fun j : Fin d₂ => ∑ i : Fin d₁, ‖B i j‖ ^ 2))

end IntroMatrixConc.GaussianSeries


