-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P01_Model
-- name    : QAlgorithms_Papers_Independent_Independent1_P01_Model
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:00:02.701472+00:00
-- url     : https://prove2.me/theorems/9a463791-1088-46a9-9d0f-4f0359ff7b20
-- title:
--   Separability Criterion for Density Matrices: supporting definitions
-- statement:
--   Reviewed paper-local supporting definitions and conventions. The attached text aggregates the existing blind readbacks of every definition; it makes no theorem proof claim.
-- source:
--   Separability Criterion for Density Matrices, arXiv:quant-ph/9604005v2. PDF SHA-256: 6574d1af38e331a5ed4f7c58673855e1e580eb96d79fa52338f18cdc22d43998. Exact locators remain in declaration docstrings.

import Definitions.Def_QAlgorithms_Defs_BipartiteSeparability
import Definitions.Def_QAlgorithms_Defs_Hamiltonian
/-!
# Peres: Separability Criterion for Density Matrices

Source: arXiv:quant-ph/9604005v2, PDF pp.2–5. The first subsystem alone
is transposed, without complex conjugation. Equation (5), which has a
conjugating-factor defect, is deferred; its valid spectral conclusion is stated.
-/

noncomputable section

open scoped Matrix ComplexOrder

namespace QAlgorithms.Papers.Independent.Independent1.P01

open QAlgorithms.Entanglement

/-- The singlet density matrix of Eq. (8), Peres PDF p.3; `false` labels 0. -/
def singletDensity : Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  (2⁻¹ : ℂ) • pureDensity (ket (false, true) - ket (true, false))

/-- The white-noise mixture of Eq. (7), Peres PDF p.3, including singlets in the noise. -/
def wernerDensity (x : ℝ) : Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  (x : ℂ) • singletDensity + (((1 - x) / 4 : ℝ) : ℂ) • 1

/-- The mixture in Eqs. (9)–(12), Peres PDF p.4, with pure component `a|01> + b|10>`. -/
def gisinDensity (x : ℝ) (a b : ℂ) : Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  (x : ℂ) • pureDensity (a • ket (false, true) + b • ket (true, false)) +
    (((1 - x) / 2 : ℝ) : ℂ) •
      (pureDensity (ket (false, false)) + pureDensity (ket (true, true)))

/-- The singlet/polarized mixture of Eq. (15), Peres PDF p.4. -/
def polarizedSingletDensity (x : ℝ) : Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  (x : ℂ) • singletDensity + ((1 - x : ℝ) : ℂ) • pureDensity (ket (false, false))

/-- Identical copies grouped by observer, Peres PDF p.5: all first-subsystem
coordinates precede all second-subsystem coordinates. The empty product is 1. -/
def observerTensorPower {I J : Type*} (rho : Matrix (I × J) (I × J) ℂ) (k : ℕ) :
    Matrix ((Fin k → I) × (Fin k → J)) ((Fin k → I) × (Fin k → J)) ℂ :=
  Matrix.of fun p q => ∏ t : Fin k, rho (p.1 t, p.2 t) (q.1 t, q.2 t)

example : singletDensity (false, true) (false, true) = 1 / 2 ∧
    singletDensity (false, true) (true, false) = -(1 / 2) ∧
    singletDensity (false, false) (false, false) = 0 := by
  norm_num [singletDensity, pureDensity, ket, EuclideanSpace.single_apply]

example : wernerDensity 0 = (4⁻¹ : ℂ) • 1 := by
  norm_num [wernerDensity]

example : gisinDensity 1 1 0 = pureDensity (ket (false, true)) := by
  simp [gisinDensity]

example : polarizedSingletDensity 0 = pureDensity (ket (false, false)) := by
  simp [polarizedSingletDensity]

example {I J : Type*} (rho : Matrix (I × J) (I × J) ℂ)
    (p q : (Fin 1 → I) × (Fin 1 → J)) :
    observerTensorPower rho 1 p q = rho (p.1 0, p.2 0) (q.1 0, q.2 0) := by
  simp [observerTensorPower]

example {I J : Type*} (rho : Matrix (I × J) (I × J) ℂ)
    (p q : (Fin 0 → I) × (Fin 0 → J)) : observerTensorPower rho 0 p q = 1 := by
  simp [observerTensorPower]








end QAlgorithms.Papers.Independent.Independent1.P01


