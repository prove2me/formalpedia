-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_SsetGroup
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_SsetGroup
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:10:22.475822+00:00
-- url     : https://prove2.me/theorems/5131affb-649e-4030-a2b4-985e786e7993
-- title:
--   Sset Group
-- statement:
--   Definitions and structural lemmas for Sset Group, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryQuotientCompactness/SsetGroup.lean

import Definitions.Def_Formalism_PeriodIntegrals_QuotSetU
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
noncomputable section
namespace PI.QuotSetU.UnitaryGroupMassFormula
open PI PI.QuotSetU
def ModProps {m : ℕ} (G : Set (Matrix (Fin m) (Fin m) ℂ)) (D : Matrix (Fin m) (Fin m) ℂ → ℝ) : Prop :=
  (∀ g ∈ G, 0 < D g) ∧ (∀ a ∈ G, ∀ b ∈ G, D (a * b) = D a * D b) ∧
  (∀ c : Matrix (Fin m) (Fin m) ℂ, IsUnit c → (∀ g, c * g * c⁻¹ ∈ G ↔ g ∈ G) →
      ∀ g ∈ G, D (c * g * c⁻¹) = D g) ∧
  (∀ V ⊆ G, IsCompact V → ∃ M : ℝ, ∀ v ∈ V, D v ≤ M)
def ModExists : Prop :=
  ∀ (m : ℕ) (G : Set (Matrix (Fin m) (Fin m) ℂ)), IsMatGroup G →
    ∃ D : Matrix (Fin m) (Fin m) ℂ → ℝ, ModProps G D ∧
      ((∀ g ∈ G, D g = 1) → ∀ μ : Measure (MtM m), IsHaarOnM G μ → IsRightInvM G μ)
def UHGroup : Prop := ∀ k r : ℕ, IsMatGroup (UH (Hpk k r))
def SsetSub : Prop := ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), Sset k r z ⊆ UH (Hpk k r)
def SsetGroup : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), inWb k r z → 0 < Tz k r z → IsMatGroup (Sset k r z)
def TrivG : Prop :=
  ∀ (k r : ℕ) (D : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → ℝ),
    ModProps (UH (Hpk k r)) D → ∀ g ∈ UH (Hpk k r), D g = 1
def TrivS : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), inWb k r z → 0 < Tz k r z →
    ∀ D : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → ℝ,
      ModProps (Sset k r z) D → ∀ g ∈ Sset k r z, D g = 1
def PolarUH : Prop :=
  ∀ (k r : ℕ), ∀ g ∈ UH (Hpk k r), ∃ u p : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ,
    u ∈ UH (Hpk k r) ∧ uᴴ * u = 1 ∧ p ∈ UH (Hpk k r) ∧ pᴴ = p ∧ g = u * p
def KCompact : Prop := ∀ k r : ℕ, IsCompact {u | u ∈ UH (Hpk k r) ∧ uᴴ * u = 1}
def UWCompact : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), inWb k r z → 0 < Tz k r z → IsCompact (UWset k r z)
def NGroup : Prop :=
  ∀ k r : ℕ, (1 ∈ Nset k r) ∧ (∀ a ∈ Nset k r, ∀ b ∈ Nset k r, a * b ∈ Nset k r) ∧
    ∀ a ∈ Nset k r, a⁻¹ ∈ Nset k r
def NContract : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), inWb k r z → ∀ n ∈ Nset k r, ∀ ε : ℝ, 0 < ε →
    ∃ c : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ, IsUnit c ∧
      (∀ g, c * g * c⁻¹ ∈ Sset k r z ↔ g ∈ Sset k r z) ∧ ∀ i j, ‖(c * n * c⁻¹ - 1) i j‖ ≤ ε
end PI.QuotSetU.UnitaryGroupMassFormula
end


