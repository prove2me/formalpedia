-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_ActionCoordinates
-- name    : Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_ActionCoordinates
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:37:21.002598+00:00
-- url     : https://prove2.me/theorems/de4356ac-228b-4a40-9543-b98b03eec982
-- title:
--   Action Coordinates
-- statement:
--   Definitions and structural lemmas for Action Coordinates, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/GlobalSignature/ActionCoordinates.lean

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataCD
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.ActionCoordinates
open MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped ENNReal
abbrev Wsp (P Q : ℕ) : Type := Fin P ⊕ Fin Q → ℂ
def sgn {P Q : ℕ} : Fin P ⊕ Fin Q → ℂ := Sum.elim (fun _ => 1) (fun _ => -1)
def herm {P Q : ℕ} (x y : Wsp P Q) : ℂ := ∑ j, sgn j * x j * (starRingEnd ℂ) (y j)
def qf {P Q : ℕ} (x : Wsp P Q) : ℝ := (herm x x).re
def bil {P Q : ℕ} (x y : Wsp P Q) : ℝ := Algebra.trace ℝ ℂ (herm x y)
def fourierT {V : Type} [MeasurableSpace V] (e : ℝ) (β : V → V → ℝ) (μ : Measure V)
    (Φ : V → ℂ) (y : V) : ℂ :=
  ∫ x, Φ x * Complex.exp (2 * Real.pi * Complex.I * ((e * β x y : ℝ) : ℂ)) ∂μ
def IsSelfDualFor {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [MeasurableSpace V]
    (e : ℝ) (β : V → V → ℝ) (μ : Measure V) : Prop :=
  ∀ Φ : SchwartzMap V ℂ, Integrable (⇑Φ) μ ∧ Integrable (fourierT e β μ Φ) μ ∧
    ∀ x, fourierT e β μ (fourierT e β μ Φ) x = Φ (-x)
def dx (P Q : ℕ) : Measure (Wsp P Q) := (2 : ℝ≥0∞) ^ (P + Q) • volume
def cM (M : ℕ) : ℝ≥0∞ := ENNReal.ofReal ((2 * Real.pi) ^ M / (Nat.factorial (M - 1) : ℝ))
def IsDxDq {P Q : ℕ} (β : ℝ) (fib : ℝ → Measure (Wsp P Q)) : Prop :=
  ∃ (U : Set (Wsp P Q)) (B : Set ℝ), {x | x ≠ 0} ⊆ U ∧ IsOpen B ∧ β ∈ B ∧
    IsFibreFamily (dx P Q) qf id U (volume : Measure ℝ) B fib
def act {P Q : ℕ} (g : UpqT P Q) (x : Wsp P Q) : Wsp P Q := (UpqT.mat g).mulVec x
def IsPerpFrame {P Q P' Q' : ℕ} (x₀ : Wsp P Q) (j : Wsp P' Q' →ₗ[ℂ] Wsp P Q)
    (ι : UpqT P' Q' → UpqT P Q) : Prop :=
  (∀ v w, herm (j v) (j w) = herm v w) ∧
  (∀ y, herm y x₀ = 0 ↔ ∃ v, j v = y) ∧
  (∀ g', act (ι g') x₀ = x₀ ∧ ∀ v, act (ι g') (j v) = j (act g' v))
def SelfDualMeasures : Prop :=
  ∀ e : ℝ, (e = 1 ∨ e = -1) →
    (∀ (P Q : ℕ) (μ : Measure (Wsp P Q)), μ.IsAddHaarMeasure →
      (IsSelfDualFor e bil μ ↔ μ = dx P Q)) ∧
    (∀ ν : Measure ℝ, ν.IsAddHaarMeasure →
      (IsSelfDualFor e (fun t s : ℝ => t * s) ν ↔ ν = volume))
def SphereVolume : Prop :=
  ∀ M : ℕ, 1 ≤ M → ∀ fib : ℝ → Measure (Wsp M 0), IsDxDq 1 fib →
    fib 1 {x | qf x = 1} = cM M
def QuotientMeasure : Prop :=
  ∀ (P Q : ℕ) (β : ℝ), (β = 1 ∨ β = -1) → ∀ x₀ : Wsp P Q, qf x₀ = β →
    (∀ y : Wsp P Q, qf y = β → ∃ g : UpqT P Q, act g⁻¹ x₀ = y) ∧
    (∃ (P' Q' : ℕ) (j : Wsp P' Q' →ₗ[ℂ] Wsp P Q) (ι : UpqT P' Q' → UpqT P Q),
      (β = 1 → P' + 1 = P ∧ Q' = Q) ∧ (β = -1 → P' = P ∧ Q' + 1 = Q) ∧ IsPerpFrame x₀ j ι) ∧
    ∀ (P' Q' : ℕ) (j : Wsp P' Q' →ₗ[ℂ] Wsp P Q) (ι : UpqT P' Q' → UpqT P Q),
      IsPerpFrame x₀ j ι →
        Set.range ι = {g | act g x₀ = x₀} ∧
        ∀ (c : CDHaar) (fib : ℝ → Measure (Wsp P Q)), IsDxDq β fib →
          ∀ s : Wsp P Q → UpqT P Q, (∀ y, qf y = β → act (s y)⁻¹ x₀ = y) →
            ∀ f : UpqT P Q → ℝ≥0∞, Measurable f →
              ∫⁻ g, f g ∂(c.cd P Q) =
                (cM (P + Q))⁻¹ *
                  ∫⁻ y in {y | qf y = β}, (∫⁻ g', f (ι g' * s y) ∂(c.cd P' Q')) ∂(fib β)
def RealPlaceMeasures : Prop := SelfDualMeasures ∧ SphereVolume ∧ QuotientMeasure
example : cM 1 = ENNReal.ofReal (2 * Real.pi) := by simp [cM]
example : qf (Pi.single (Sum.inl 0) 1 : Wsp 1 1) = 1 ∧
    qf (Pi.single (Sum.inr 0) 1 : Wsp 1 1) = -1 := by
  constructor <;> simp [qf, herm, sgn, Pi.single_apply]
example : IsPerpFrame (P := 1) (Q := 0) (P' := 0) (Q' := 0) (fun _ => 1) 0 (fun _ => 1) := by
  have h1 : UpqT.mat (1 : UpqT 1 0) = 1 := rfl
  refine ⟨fun v w => by simp [herm], fun y => ?_, fun g' => by simp [act, h1]⟩
  simp only [herm, sgn, Fintype.sum_sum_type, Finset.univ_unique, Finset.sum_singleton]
  constructor
  · intro h
    refine ⟨0, ?_⟩
    funext i
    rcases i with i | i
    · have : i = default := Subsingleton.elim _ _
      subst this
      simpa [eq_comm] using h
    · exact i.elim0
  · rintro ⟨v, rfl⟩
    simp
end GlobalTheory.IndefiniteRowSideFullHecke.ActionCoordinates


