-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_SideNormalisedGap
-- name    : Development_AbelianVarietyTheory_BlockTheory_JetGauges_SideNormalisedGap
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T02:39:23.834384+00:00
-- url     : https://prove2.me/theorems/81b568c2-960c-412a-8429-158894306e66
-- title:
--   Side Normalised Gap
-- statement:
--   Definitions and structural lemmas for Side Normalised Gap, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/JetGauges/SideNormalisedGap.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UpqRep
import Definitions.Def_Formalism_PeriodIntegrals_IsLowUnitH
import Definitions.Def_Formalism_FormalDegreeBessel_StatementG
import Definitions.Def_Formalism_FormalDegreeBessel_StatementDS
import Definitions.Def_Formalism_PeriodIntegrals_BesselPeriodGGP
import Definitions.Def_Formalism_PeriodIntegrals_BesselMapUniq
import Definitions.Def_Formalism_PeriodIntegrals_KFinSmooth
import Definitions.Def_Formalism_HermitianCurvature_StatementB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.SideNormalisedGap
open MeasureTheory Matrix
open scoped InnerProductSpace
open PI.UpqRep (IsDSHpk IsLowUnitH IsHCTypeW IsKFinHpk IsCayleyU IsOrthProjOnto InLieHpk lowKSub smoothVecs dsigW)
open Formalism.QuantumDeterminants (Mt UH Hpk Nset UWset inWb Tz IsHCParam GapAtLeast)
open Formalism.FourierDecayAlt.B (gN)
abbrev Mat (k r : ℕ) := Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ
def dimV (k r : ℕ) : ℝ := 2 * (r : ℝ) + k + 1
def decExp (r : ℕ) (h : ℝ) : ℝ := h / (8 * Real.sqrt (2 * ((r : ℝ) + 1)))
def decConst (r : ℕ) (h : ℝ) : ℝ := Real.exp (h / (16 * ((r : ℝ) + 1)))
def dimN (k r : ℕ) : ℝ := (r : ℝ) * ((r : ℝ) - 1) + 2 * (r : ℝ) * ((k : ℝ) + 1) + (r : ℝ) ^ 2
def thrG (k r : ℕ) : ℝ := 4 * ((k : ℝ) + r) * ((r : ℝ) + 1)
def thrS (k r : ℕ) : ℝ := (dimV k r - 1) * dimN k r
def propExp (r : ℕ) : ℝ := 2 * ((r : ℝ) ^ 2 + r + 1)
def thrSS (k r : ℕ) : ℝ := 2 * propExp r * thrS k r + 1
def DecGap (k r : ℕ) (h : ℝ) : Prop := 120 * dimV k r * ((r : ℝ) + 1) ^ ((3 : ℝ) / 2) ≤ h
def Size (k r : ℕ) (h : ℝ) : Prop :=
  DecGap k r h ∧ 16 * dimV k r ^ 5 * Real.sqrt (2 * ((r : ℝ) + 1)) ≤ h
def Thresholds (k r : ℕ) (a : ℝ) : Prop :=
  thrG k r < a / 2 ∧ thrS k r < a / 2 ∧ thrSS k r + thrG k r + 1 ≤ a ∧ thrS k r < a - 1
def mulP {k r : ℕ} (p : Mt k r × Mt k r) : Mt k r := fun i j => (Matrix.of p.1 * Matrix.of p.2) i j
def muS {k r : ℕ} (μW μN : Measure (Mt k r)) : Measure (Mt k r) := (μW.prod μN).map mulP
section Side
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {Vp : Type} [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp]
def IsSide (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ) (h : ℝ)
    (σ : Mat k r → (H →L[ℂ] H)) (w₀ : H) (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (u : Fin k → ℝ)
    (π : Mat k r → (Vp →L[ℂ] Vp)) (μW μN μG ν : Measure (Mt k r)) : Prop :=
  1 ≤ k ∧
  (IsHCParam lam ∧ IsDSHpk k r ε lam σ ∧ GapAtLeast ε lam h) ∧
  IsLowUnitH k r ε lam σ w₀ ∧
  (inWb k r z ∧ 0 < Tz k r z) ∧
  c ≠ 0 ∧
  (IsHCParam u ∧ IsHCTypeW k r z u π) ∧
  (PI.BesselPeriodGGP.IsHaarOn (UWset k r z) μW ∧ PI.BesselPeriodGGP.IsHaarOn (Nset k r) μN ∧
    PI.BesselPeriodGGP.IsHaarOn (UH (Hpk k r)) μG) ∧
  (SigmaFinite ν ∧ PI.BesselPeriodGGP.IsQuotMeas μG (muS μW μN) ν)
def IsSideNormalised (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ) (h : ℝ)
    (σ : Mat k r → (H →L[ℂ] H)) (w₀ : H) (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (u : Fin k → ℝ)
    (π : Mat k r → (Vp →L[ℂ] Vp)) (μW μN μG ν : Measure (Mt k r)) : Prop :=
  IsSide k r ε lam h σ w₀ z c u π μW μN μG ν ∧ μW Set.univ = 1
def KFinDecay (k r : ℕ) (σ : Mat k r → (H →L[ℂ] H)) (a : ℝ) : Prop :=
  ∀ v v' : H, IsKFinHpk (k := k) (r := r) σ v → IsKFinHpk (k := k) (r := r) σ v' →
    ∃ C : ℝ, ∀ x ∈ UH (Hpk k r), ‖⟪v', σ x v⟫_ℂ‖ ≤ C * gN x ^ (-a)
def wordSeminorm {k r : ℕ} (σ : Mat k r → (H →L[ℂ] H)) (Ws : List (List (Mat k r))) (w : H) : ℝ :=
  (Ws.map fun D => ‖dsigW (k := k) (r := r) σ D w‖).sum
end Side
def DecProj : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ) (h : ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Mat k r → (H →L[ℂ] H)),
    1 ≤ k → IsHCParam lam → IsDSHpk k r ε lam σ → GapAtLeast ε lam h → DecGap k r h →
    ∀ (P : Mat k r) (E : H →L[ℂ] H), IsCayleyU k r ε P →
      IsOrthProjOnto E (lowKSub ε lam fun g => σ (P⁻¹ * g * P)) →
      ∀ κ X : Mat k r, κ ∈ UH (Hpk k r) → κ ∈ Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ →
        InLieHpk k r X → Xᴴ = X →
        ‖E ∘L σ (κ * NormedSpace.exp X) ∘L E‖ ≤
          Real.exp (-(h / 8) * min (gN X ^ 2) (gN X / Real.sqrt (2 * ((r : ℝ) + 1))))
def DecLow : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ) (h : ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Mat k r → (H →L[ℂ] H)),
    1 ≤ k → IsHCParam lam → IsDSHpk k r ε lam σ → GapAtLeast ε lam h → DecGap k r h →
    ∀ w₁ w₂ : H, IsLowUnitH k r ε lam σ w₁ → IsLowUnitH k r ε lam σ w₂ →
      ∀ x ∈ UH (Hpk k r),
        ‖⟪w₂, σ x w₁⟫_ℂ‖ ≤ decConst r h * dimV k r ^ (decExp r h / 2) * gN x ^ (-decExp r h)
def DecKFin : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ) (h : ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Mat k r → (H →L[ℂ] H)),
    1 ≤ k → IsHCParam lam → IsDSHpk k r ε lam σ → GapAtLeast ε lam h → DecGap k r h →
    KFinDecay k r σ (decExp r h)
def DecSmooth : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Mat k r → (H →L[ℂ] H)) (a : ℝ),
    IsHCParam lam → IsDSHpk k r ε lam σ → KFinDecay k r σ a →
    ∀ v₀ : H, IsKFinHpk (k := k) (r := r) σ v₀ →
      ∃ (C : ℝ) (Ws : List (List (Mat k r))), (∀ D ∈ Ws, ∀ X ∈ D, InLieHpk k r X) ∧
        ∀ w ∈ smoothVecs (k := k) (r := r) σ, ∀ x ∈ UH (Hpk k r),
          ‖⟪v₀, σ x w⟫_ℂ‖ ≤ C * wordSeminorm σ Ws w * gN x ^ (1 - a)
example : decExp 1 16 = 1 := by
  unfold decExp
  rw [show (2 * (((1 : ℕ) : ℝ) + 1)) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  norm_num
example : dimN 1 1 = 5 ∧ thrG 1 1 = 16 ∧ thrS 1 1 = 15 ∧ thrSS 1 1 = 181 := by
  simp only [thrSS, thrS, thrG, dimN, dimV, propExp]; norm_num
example (k r : ℕ) : ∃ h, Size k r h :=
  ⟨max _ _, le_max_left _ _, le_max_right _ _⟩
end GlobalTheory.IndefiniteRowSideFullHecke.SideNormalisedGap


