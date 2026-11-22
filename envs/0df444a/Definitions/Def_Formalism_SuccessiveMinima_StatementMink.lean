-- Prove2me | Definitions.Def_Formalism_SuccessiveMinima_StatementMink
-- name    : Formalism_SuccessiveMinima_StatementMink
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T16:46:17.351698+00:00
-- url     : https://prove2.me/theorems/b7b4c924-f552-4b78-9bfa-b0d223ecdc7d
-- title:
--   Statement Mink
-- statement:
--   Definitions and structural lemmas for Statement Mink, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SuccessiveMinima/StatementMink.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Module Metric Set
open scoped Pointwise
noncomputable section
namespace Formalism.FN
def succMin {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : Submodule ℤ E) (K : Set E) (i : ℕ) : ℝ :=
  sInf {t : ℝ | 0 ≤ t ∧ i ≤ finrank ℝ (Submodule.span ℝ ((L : Set E) ∩ t • K))}
def succMinBall {r : ℕ} (R : Submodule ℤ (EuclideanSpace ℝ (Fin r))) (i : ℕ) : ℝ :=
  sInf {t : ℝ | 0 ≤ t ∧
    i ≤ Module.finrank ℝ (Submodule.span ℝ ((R : Set (EuclideanSpace ℝ (Fin r))) ∩ Metric.closedBall 0 t))}
def MinkowskiIIUpper : Prop :=
  ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] (K : Set E),
    IsCompact K → Convex ℝ K → (∀ x ∈ K, -x ∈ K) → (0 : E) ∈ interior K →
      μ.real K * ∏ i : Fin (finrank ℝ E), succMin L K ((i : ℕ) + 1)
        ≤ 2 ^ finrank ℝ E * ZLattice.covolume L μ
def MinkowskiIILower : Prop :=
  ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] (K : Set E),
    IsCompact K → Convex ℝ K → (∀ x ∈ K, -x ∈ K) → (0 : E) ∈ interior K →
      (2 : ℝ) ^ finrank ℝ E / (Nat.factorial (finrank ℝ E) : ℝ) * ZLattice.covolume L μ
        ≤ μ.real K * ∏ i : Fin (finrank ℝ E), succMin L K ((i : ℕ) + 1)
def MinkowskiIIBall : Prop :=
  ∀ (r : ℕ) (R : Submodule ℤ (EuclideanSpace ℝ (Fin r))) [DiscreteTopology R] [IsZLattice ℝ R],
    (MeasureTheory.volume (Metric.ball (0 : EuclideanSpace ℝ (Fin r)) 1)).toReal *
        ∏ i : Fin r, succMinBall R ((i : ℕ) + 1)
      ≤ 2 ^ r * ZLattice.covolume R
end Formalism.FN


