-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaussianDetSquareIntegral
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaussianDetSquareIntegral
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:56:28.169835+00:00
-- url     : https://prove2.me/theorems/4e610075-9bee-43c2-bc0e-f1f3cebe3682
-- title:
--   Gaussian Det Square Integral
-- statement:
--   Definitions and structural lemmas for Gaussian Det Square Integral, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/GaussianDetSquareIntegral.lean

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_JoinCol
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PAreaMultiplicityWeight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ReciprocityTheory.L2DbarEstimates GlobalTheory.CompanionTheory.FSCrofton
open scoped ENNReal ComplexConjugate
noncomputable section
namespace GlobalTheory.CompanionTheory.FSCrofton.GaussDet
def hf (p q : Prop) [Decidable p] [Decidable q] (z : ℂ) : ℂ :=
  (if p then z else 1) * (if q then conj z else 1) * (Real.exp (-‖z‖ ^ 2) : ℂ)
variable {β : Type} [Fintype β] [DecidableEq β]
def eR (r : β → ℂ) : ℂ := (Real.exp (-∑ k, ‖r k‖ ^ 2) : ℂ)
variable {d : ℕ}
def rowF (G : Matrix β (Fin d) ℂ) (a c : Fin d) (r : β → ℂ) : ℂ :=
  (∑ i, r i * G i a) * conj (∑ j, r j * G j c) * eR r
def fR (G : Matrix β (Fin d) ℂ) (C : Fin d → β → ℂ) : ℝ :=
  Real.exp (-∑ k, ∑ j, ‖C k j‖ ^ 2) * ‖(Matrix.of C * G).det‖ ^ 2
end GlobalTheory.CompanionTheory.FSCrofton.GaussDet


