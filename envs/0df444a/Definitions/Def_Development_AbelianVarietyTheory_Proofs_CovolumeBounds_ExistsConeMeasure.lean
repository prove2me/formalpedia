-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsConeMeasure
-- name    : Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsConeMeasure
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T03:52:26.687801+00:00
-- url     : https://prove2.me/theorems/0733d7a1-e122-4049-b5e4-22b4808dbd81
-- title:
--   Exists Cone Measure
-- statement:
--   Definitions and structural lemmas for Exists Cone Measure, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsConeMeasure.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsKMeas
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LintegralGaussianHyperboloidFiberStatement
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
noncomputable section
namespace GlobalTheory.HCXi.ConeZero
def param (n : ℕ) (p : (Fin n → ℂ) × ℝ) : Fin (n + 1) → ℂ :=
  Fin.snoc (α := fun _ => ℂ) p.1
    (((Real.sqrt (sqLen p.1 + 0) : ℝ) : ℂ) * Complex.exp (Complex.I * p.2))
def coneMeasure (n : ℕ) : Measure (Fin (n + 1) → ℂ) :=
  Measure.map (param n) (volume.restrict (Set.univ ×ˢ Set.Ioc 0 (2 * Real.pi)))
end GlobalTheory.HCXi.ConeZero


