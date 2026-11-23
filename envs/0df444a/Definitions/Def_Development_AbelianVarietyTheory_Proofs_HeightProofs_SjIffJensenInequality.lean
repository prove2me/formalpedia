-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_SjIffJensenInequality
-- name    : Development_AbelianVarietyTheory_Proofs_HeightProofs_SjIffJensenInequality
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:58:01.803801+00:00
-- url     : https://prove2.me/theorems/87f35fbe-d684-4c84-92ef-48d46ce4d3b8
-- title:
--   Sj Iff Jensen Inequality
-- statement:
--   Definitions and structural lemmas for Sj Iff Jensen Inequality, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/SjIffJensenInequality.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereLogIntegrableStatement
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_HeightDefect_SphereBlockLogMean
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory NumberField MvPolynomial
noncomputable section
namespace GlobalTheory.HeightZeroCompare
open ReciprocityTheory.MultiplicativeHeights GlobalTheory.IndefiniteRowSideFullHecke.UnitSphereMeasure
def JensenInequality : Prop :=
  ∀ (N a : ℕ) (f : MvPolynomial (Fin (N + 1)) ℂ) (u : EuclideanSpace ℂ (Fin (N + 1))),
    f.IsHomogeneous a → ‖u‖ = 1 → eval (fun j => u j) f ≠ 0 →
    Integrable (sphereLogAbs f) (sphereMeasure N) ∧
      Real.log ‖eval (fun j => u j) f‖ - (a : ℝ) / 2 * (harmonic N : ℝ) ≤ sphereLogMean f
def conjVec {n : ℕ} (u : EuclideanSpace ℂ (Fin n)) : EuclideanSpace ℂ (Fin n) :=
  WithLp.toLp 2 fun j => starRingEnd ℂ (u j)
def BlockIntegrable : Prop :=
  ∀ (B N : ℕ) (a : Fin B → ℕ) (P : MvPolynomial (Fin B × Fin (N + 1)) ℂ), P ≠ 0 →
    IsBlockHomogeneous P a → Integrable (blockLogAbs P) (blockSphereMeasure B N)
end GlobalTheory.HeightZeroCompare


