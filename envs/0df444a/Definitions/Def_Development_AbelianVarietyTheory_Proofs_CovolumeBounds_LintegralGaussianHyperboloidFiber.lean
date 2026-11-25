-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LintegralGaussianHyperboloidFiber
-- name    : Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LintegralGaussianHyperboloidFiber
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T03:03:56.609173+00:00
-- url     : https://prove2.me/theorems/09096d9d-15aa-5642-87b7-0c830189bf22
-- title:
--   Lintegral Gaussian Hyperboloid Fiber
-- statement:
--   Definitions and structural lemmas for Lintegral Gaussian Hyperboloid Fiber, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/LintegralGaussianHyperboloidFiber.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsKMeas
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LintegralHyperboloidFibrationStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 GlobalTheory.HCXi
open scoped ENNReal ComplexOrder
namespace GlobalTheory.HCXi.ConeSlice
noncomputable abbrev sgnMat (k : ℕ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ :=
  Matrix.diagonal (fun i : Fin (k + 1) => if i = Fin.last k then (-1 : ℂ) else 1)
noncomputable abbrev pt {k : ℕ} (τ : ℝ) (p : (Fin k → ℂ) × ℝ) : Fin (k + 1) → ℂ :=
  Fin.snoc (α := fun _ => ℂ) p.1 (((Real.sqrt (sqLen p.1 + τ) : ℝ) : ℂ) * Complex.exp (Complex.I * p.2))
noncomputable def slice {k : ℕ} (g : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (τ : ℝ) : ℝ≥0∞ :=
  ∫⁻ p : (Fin k → ℂ) × ℝ in Set.univ ×ˢ Set.Ioc 0 (2 * Real.pi),
    ENNReal.ofReal (Real.exp (-sqLen (g *ᵥ pt τ p)))
end GlobalTheory.HCXi.ConeSlice


