-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeakApproximationDVR_BigExists
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeakApproximationDVR_BigExists
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:12:42.71705+00:00
-- url     : https://prove2.me/theorems/59e71c3d-fa66-46bd-a498-ad33f7d00dd5
-- title:
--   Big Exists
-- statement:
--   Definitions and structural lemmas for Big Exists, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeakApproximationDVR/BigExists.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_WeakApproxDVR
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeakApproximationDVR_SmOneOfNotIsUnit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.WA
open PI.WADVR
def BigExists : Prop :=
  ∀ (E : Type) [Field E] (ι : Type) [Fintype ι] (W Q : ι → Type) [∀ i, CommRing (W i)]
    [∀ i, IsDomain (W i)] [∀ i, IsDiscreteValuationRing (W i)] [∀ i, Field (Q i)]
    [∀ i, Algebra (W i) (Q i)] [∀ i, IsFractionRing (W i) (Q i)] (iw : ∀ i, E →+* Q i) (p : ℕ),
    (∀ i, (p : Q i) ≠ 0) → (∀ i, ¬ IsUnit (p : W i)) →
    (∀ i (x : Q i) (N : ℕ), ∃ a : E, ∃ c : W i, iw i a = x + (p : Q i) ^ N * algebraMap (W i) (Q i) c) →
    (∀ i j, i ≠ j → ∃ a : E, iw i a ∈ Set.range (algebraMap (W i) (Q i)) ∧
      iw j a ∉ Set.range (algebraMap (W j) (Q j))) →
    ∀ (ϖ : ∀ i, W i), (∀ i, Irreducible (ϖ i)) →
    ∀ i, ∃ z : E, z ≠ 0 ∧ Sm (Q i) (ϖ i) 1 (iw i z)⁻¹ ∧ ∀ j, j ≠ i → Sm (Q j) (ϖ j) 1 (iw j z)
def Assembly : Prop :=
  ∀ (E : Type) [Field E] (ι : Type) [Fintype ι] (W Q : ι → Type) [∀ i, CommRing (W i)]
    [∀ i, IsDomain (W i)] [∀ i, IsDiscreteValuationRing (W i)] [∀ i, Field (Q i)]
    [∀ i, Algebra (W i) (Q i)] [∀ i, IsFractionRing (W i) (Q i)] (iw : ∀ i, E →+* Q i) (p : ℕ),
    (∀ i, (p : Q i) ≠ 0) → (∀ i, ¬ IsUnit (p : W i)) →
    (∀ i (x : Q i) (N : ℕ), ∃ a : E, ∃ c : W i, iw i a = x + (p : Q i) ^ N * algebraMap (W i) (Q i) c) →
    ∀ (ϖ : ∀ i, W i), (∀ i, Irreducible (ϖ i)) →
    (∀ i, ∃ z : E, z ≠ 0 ∧ Sm (Q i) (ϖ i) 1 (iw i z)⁻¹ ∧ ∀ j, j ≠ i → Sm (Q j) (ϖ j) 1 (iw j z)) →
    ∀ (x : ∀ i, Q i) (N : ℕ), ∃ a : E, ∀ i, ∃ c : W i,
      iw i a = x i + (p : Q i) ^ N * algebraMap (W i) (Q i) c
end PI.WA


