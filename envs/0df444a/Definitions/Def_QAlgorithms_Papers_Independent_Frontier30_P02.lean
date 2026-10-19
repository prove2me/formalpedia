-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P02
-- name    : QAlgorithms_Papers_Independent_Frontier30_P02
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-19T09:09:39.947136+00:00
-- url     : https://prove2.me/theorems/fb906996-8f48-4cce-a907-eeb98c97df0f
-- title:
--   Definitions for The Symmetry Group of Gaussian States in $L^2 (\mathbb{R}^n)$
-- statement:
--   The objects the formalized statements of *The Symmetry Group of Gaussian States in $L^2 (\mathbb{R}^n)$* (arXiv:1101.5041) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `PhaseMatrix`: Real 2n-by-2n matrices, with the block order of (1.2), PDF p.2.
--   - `canonicalJ`: The paper's skew form J = [0,-I;I,0], PDF p.2, (1.2).
--   - `uncertaintyMatrix`: The full complex uncertainty matrix 2S - iJ, PDF p.2, (1.1).
--   - `covarianceSet`: K_n, in the ambient space of all real matrices, PDF p.2, (1.3). PosSemidef is Hermitian positivity, not entrywise order.
--   - `IsSymplectic`: Symplecticity with precisely the source's sign and transpose, PDF p.2, (1.4).
--   - `williamsonDiagonal`: The repeated Williamson diagonal [D,0;0,D], PDF pp.8–9, (3.4)–(3.5).
--   - `WilliamsonData`: Ordered Williamson data with d_j >= 1/2; no data are assumed to exist. PDF pp.8–9, Theorem 2.
-- source:
--   The Symmetry Group of Gaussian States in L²(ℝⁿ), arXiv:1101.5041v1, https://arxiv.org/abs/1101.5041v1

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P10

/-!
# Covariance geometry of Gaussian states

Source: K. R. Parthasarathy, arXiv:1101.5041v1, PDF pp.2,8–12.
The coordinate type and entrywise complexification reuse pinned accepted
library declarations; the remaining definitions are local to this paper.
The phase-space coordinates are
(p_1,...,p_n,-q_1,...,-q_n), with J = [0,-I;I,0].
The operator results and the incorrect printed periodicity claim are deferred
explicitly in the unit's HARD.md and GAPS.json. No finite-dimensional operator
model is used as a replacement for the source's infinite-dimensional system.
Compilation is pending the authorized batch handoff.
-/

noncomputable section

open scoped ComplexOrder

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase complexify)

namespace QAlgorithms.Papers.Independent.Frontier30.P02

/-- Real 2n-by-2n matrices, with the block order of (1.2), PDF p.2. -/
abbrev PhaseMatrix (n : ℕ) := Matrix (Phase n) (Phase n) ℝ

/-- The paper's skew form J = [0,-I;I,0], PDF p.2, (1.2). -/
def canonicalJ (n : ℕ) : PhaseMatrix n :=
  Matrix.fromBlocks 0 (-1) 1 0

/-- The full complex uncertainty matrix 2S - iJ, PDF p.2, (1.1). -/
def uncertaintyMatrix {n : ℕ} (S : PhaseMatrix n) : Matrix (Phase n) (Phase n) ℂ :=
  (2 : ℂ) • complexify S - Complex.I • complexify (canonicalJ n)

/-- K_n, in the ambient space of all real matrices, PDF p.2, (1.3).
PosSemidef is Hermitian positivity, not entrywise order. -/
def covarianceSet (n : ℕ) : Set (PhaseMatrix n) :=
  {S | S.transpose = S ∧ (uncertaintyMatrix S).PosSemidef}

/-- Symplecticity with precisely the source's sign and transpose, PDF p.2, (1.4). -/
def IsSymplectic {n : ℕ} (M : PhaseMatrix n) : Prop :=
  M.transpose * canonicalJ n * M = canonicalJ n

/-- The repeated Williamson diagonal [D,0;0,D], PDF pp.8–9, (3.4)–(3.5). -/
def williamsonDiagonal {n : ℕ} (d : Fin n → ℝ) : PhaseMatrix n :=
  Matrix.fromBlocks (Matrix.diagonal d) 0 0 (Matrix.diagonal d)

/-- Ordered Williamson data with d_j >= 1/2; no data are assumed to exist.
PDF pp.8–9, Theorem 2. -/
def WilliamsonData {n : ℕ} (S : PhaseMatrix n) (d : Fin n → ℝ)
    (M : PhaseMatrix n) : Prop :=
  Antitone d ∧ (∀ j, (1 / 2 : ℝ) ≤ d j) ∧ IsSymplectic M ∧
    S = M.transpose * williamsonDiagonal d * M

example : canonicalJ 1 (Sum.inl 0) (Sum.inr 0) = -1 := by
  simp [canonicalJ]

example : canonicalJ 1 (Sum.inr 0) (Sum.inl 0) = 1 := by
  simp [canonicalJ]

example {n : ℕ} (S : PhaseMatrix n) (i j : Phase n) :
    complexify S i j = (S i j : ℂ) := by
  rfl

example (n : ℕ) : IsSymplectic (1 : PhaseMatrix n) := by
  simp [IsSymplectic]

example {n : ℕ} (d : Fin n → ℝ) (j : Fin n) :
    williamsonDiagonal d (Sum.inr j) (Sum.inr j) = d j := by
  simp [williamsonDiagonal]

end QAlgorithms.Papers.Independent.Frontier30.P02


