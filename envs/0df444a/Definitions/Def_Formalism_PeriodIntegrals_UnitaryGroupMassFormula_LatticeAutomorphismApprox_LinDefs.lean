-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_LinDefs
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_LinDefs
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:57:22.095373+00:00
-- url     : https://prove2.me/theorems/977574bb-f97b-4406-a322-e9dbce784edb
-- title:
--   Lin Defs
-- statement:
--   Definitions and structural lemmas for Lin Defs, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeAutomorphismApprox/LinDefs.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.UnitaryGroupMassFormula.ScXuExists
open Matrix
def pr {K : Type} [Field K] {n : ℕ} (P : Matrix (Fin n) (Fin n) K) (β x : Fin n → K) : K :=
  β ⬝ᵥ (P *ᵥ x)
def LocLin : Prop :=
  ∀ (K : Type) [Field K] (O : ValuationSubring K) (n r : ℕ) (P : Matrix (Fin n) (Fin n) K) (g : K)
    (Λ1 Λ2 : Submodule O (Fin n → K)) (a a' α α' : Fin r → Fin n → K) (u φ u0 φ0 : Fin n → K) (t : K),
    g ∈ O → g⁻¹ ∉ O →
    (∀ β ∈ Λ2, ∀ x ∈ Λ1, pr P β x ∈ O) →
    (∀ i, a i ∈ Λ1 ∧ a' i ∈ Λ1 ∧ α i ∈ Λ2 ∧ α' i ∈ Λ2) →
    (∀ i j, pr P (α i) (a j) = 0 ∧ pr P (α' i) (a' j) = 0 ∧
      pr P (α i) (a' j) = (if i = j then 1 else 0) ∧ pr P (α' i) (a j) = (if i = j then 1 else 0)) →
    u ∈ Λ1 → φ ∈ Λ2 → u0 ∈ Λ1 → φ0 ∈ Λ2 →
    (∀ i, pr P (α i) u = 0 ∧ pr P (α' i) u = 0 ∧ pr P φ (a i) = 0 ∧ pr P φ (a' i) = 0) →
    t ∈ O → (∃ s ∈ O, t - 1 = g * s) → pr P φ u = -t →
    (∀ i, (∃ s ∈ O, pr P (α i) u0 = g * s) ∧ (∃ s ∈ O, pr P (α' i) u0 = g * s) ∧
      (∃ s ∈ O, pr P φ0 (a i) = g * s) ∧ (∃ s ∈ O, pr P φ0 (a' i) = g * s)) →
    (∃ s ∈ O, pr P φ0 u0 + 1 = g * s) →
    ∃ T : GL (Fin n) K,
      (∀ x ∈ Λ1, (T : Matrix (Fin n) (Fin n) K) *ᵥ x ∈ Λ1 ∧
        ((T⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x ∈ Λ1) ∧
      (∀ β ∈ Λ2, (∃ β' ∈ Λ2, β' ᵥ* P = (β ᵥ* P) ᵥ* (T : Matrix (Fin n) (Fin n) K)) ∧
        (∃ β' ∈ Λ2, β' ᵥ* P = (β ᵥ* P) ᵥ* ((T⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))) ∧
      (∀ i, (T : Matrix (Fin n) (Fin n) K) *ᵥ a i = a i ∧ (T : Matrix (Fin n) (Fin n) K) *ᵥ a' i = a' i ∧
        (α i ᵥ* P) ᵥ* (T : Matrix (Fin n) (Fin n) K) = α i ᵥ* P ∧
        (α' i ᵥ* P) ᵥ* (T : Matrix (Fin n) (Fin n) K) = α' i ᵥ* P) ∧
      (∃ w ∈ Λ1, ((T⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ u - u0 = g • w) ∧
      (∃ β ∈ Λ2, (φ ᵥ* P) ᵥ* (T : Matrix (Fin n) (Fin n) K) - φ0 ᵥ* P = g • (β ᵥ* P))
end PI.UnitaryGroupMassFormula.ScXuExists


