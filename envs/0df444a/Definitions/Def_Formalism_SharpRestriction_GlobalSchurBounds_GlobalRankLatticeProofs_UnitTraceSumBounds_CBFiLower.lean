-- Prove2me | Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GlobalRankLatticeProofs_UnitTraceSumBounds_CBFiLower
-- name    : Formalism_SharpRestriction_GlobalSchurBounds_GlobalRankLatticeProofs_UnitTraceSumBounds_CBFiLower
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:45:50.342912+00:00
-- url     : https://prove2.me/theorems/f4358721-9073-4d7e-9a9d-6c5770674165
-- title:
--   CBFi Lower
-- statement:
--   Definitions and structural lemmas for CBFi Lower, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GlobalSchurBounds/GlobalRankLatticeProofs/UnitTraceSumBounds/CBFiLower.lean

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
open Finset MeasureTheory
namespace Formalism.MainNotions.Ext.CutB
abbrev cBNC {N : ℕ} (ε : Fin N → Bool) : Type := {ab : Fin N × Fin N // ab.1 < ab.2 ∧ ε ab.1 ≠ ε ab.2}
def cBpp {N : ℕ} (ε : Fin N → Bool) (z : cBNC ε → ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  fun a b => if h : a < b ∧ ε a ≠ ε b then z ⟨(a, b), h⟩
    else if h' : b < a ∧ ε b ≠ ε a then star (z ⟨(b, a), h'⟩) else 0
theorem cBpp_herm {N : ℕ} (ε : Fin N → Bool) (z : cBNC ε → ℂ) : (cBpp ε z).IsHermitian := by
  ext a b
  simp only [Matrix.conjTranspose_apply, cBpp]
  by_cases h1 : a < b ∧ ε a ≠ ε b
  · have h2 : ¬ (b < a ∧ ε b ≠ ε a) := fun h => absurd h1.1 (not_lt.2 h.1.le)
    rw [dif_neg h2, dif_pos h1, dif_pos h1, star_star]
  · by_cases h3 : b < a ∧ ε b ≠ ε a
    · rw [dif_pos h3, dif_neg h1, dif_pos h3]
    · simp [h1, h3]
def cBp {N : ℕ} (ε : Fin N → Bool) : ℕ := (univ.filter (fun a => ε a = true)).card
def cBq {N : ℕ} (ε : Fin N → Bool) : ℕ := (univ.filter (fun a => ε a = false)).card
def cBhs {N : ℕ} (X : Matrix (Fin N) (Fin N) ℂ) : ℝ := ∑ a, ∑ b, ‖X a b‖ ^ 2
def cBlead {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) (i : ℕ) (hi : i ≤ N) : Matrix (Fin i) (Fin i) ℂ :=
  A.submatrix (Fin.castLE hi) (Fin.castLE hi)
def cBF {N : ℕ} (X : Matrix (Fin N) (Fin N) ℂ) (i : ℕ) (hi : i ≤ N) : ℝ :=
  Real.log ((cBlead (NormedSpace.exp X) i hi).det).re
def cBV {N : ℕ} (X : Matrix (Fin N) (Fin N) ℂ) (i : ℕ) : ℝ :=
  cBhs ((1 - Matrix.diagonal (fun a : Fin N => if a.val < i then (1 : ℂ) else 0)) * X *
    Matrix.diagonal (fun a : Fin N => if a.val < i then (1 : ℂ) else 0))
def cBPh {N : ℕ} (lam : Fin N → ℝ) (X : Matrix (Fin N) (Fin N) ℂ) : ℝ :=
  ∑ i : Fin N, if h : i.val + 1 < N then (lam i - lam ⟨i.val + 1, h⟩ + 1) * cBF X (i.val + 1) h.le else 0
def cBsh (u : ℝ) : ℝ := if u = 0 then 1 else Real.sinh u / u
def cBJ {N : ℕ} (ε : Fin N → Bool) (z : cBNC ε → ℂ) : ℝ :=
  ∏ a, ∏ b ∈ univ.filter (fun b : Fin N => a < b),
    cBsh ((cBpp_herm ε z).eigenvalues a - (cBpp_herm ε z).eigenvalues b)
def cBQ {N : ℕ} (ε : Fin N → Bool) (lam : Fin N → ℝ) (z : cBNC ε → ℂ) : ℝ :=
  ∑ pr : cBNC ε, (lam pr.1.1 - lam pr.1.2 + ((pr.1.2.val : ℝ) - pr.1.1.val)) * ‖z pr‖ ^ 2
def cBPi {N : ℕ} (ε : Fin N → Bool) (lam : Fin N → ℝ) : ℝ :=
  ∏ a, ∏ b ∈ univ.filter (fun b : Fin N => a < b ∧ ε a ≠ ε b), Real.pi / (lam a - lam b + ((b.val : ℝ) - a.val))
def cBFiLower : Prop :=
  ∀ (N : ℕ) (ε : Fin N → Bool) (X : Matrix (Fin N) (Fin N) ℂ), X.IsHermitian →
    (∀ a b, ε a = ε b → X a b = 0) → ∀ ep : ℝ, ep ≤ 1 →
    Real.sqrt (2 * (min (cBp ε) (cBq ε) : ℕ)) * Real.sqrt (cBhs X) ≤ ep →
    ∀ (i : ℕ) (hi : i ≤ N), (1 - ep) / 2 * cBV X i ≤ cBF X i hi
def cBFiUpper : Prop :=
  ∀ (N : ℕ) (ε : Fin N → Bool) (X : Matrix (Fin N) (Fin N) ℂ), X.IsHermitian →
    (∀ a b, ε a = ε b → X a b = 0) →
    Real.sqrt (2 * (min (cBp ε) (cBq ε) : ℕ)) * Real.sqrt (cBhs X) ≤ 1 →
    ∀ (i : ℕ) (hi : i ≤ N), cBF X i hi ≤ cBV X i
def cBFiScale : Prop :=
  ∀ (N : ℕ) (X : Matrix (Fin N) (Fin N) ℂ), X.IsHermitian → (∀ a, X a a = 0) →
    ∀ (i : ℕ) (hi : i ≤ N), 0 ≤ cBF X i hi ∧ ∀ t : ℝ, 1 ≤ t → t * cBF X i hi ≤ cBF ((t : ℂ) • X) i hi
def cBInner : Prop :=
  ∀ (N : ℕ) (ε : Fin N → Bool) (lam : Fin N → ℝ) (ε₀ h₀ : ℝ),
    1 ≤ cBp ε → 1 ≤ cBq ε → StrictAnti lam → (∀ a b, ε a ≠ ε b → h₀ ≤ |lam a - lam b|) →
    Real.exp (-(N : ℝ)) ≤ ε₀ → ε₀ < 1 / 2 →
    8192 * ((min (cBp ε) (cBq ε) : ℕ) : ℝ) * ((cBp ε : ℝ) * cBq ε) ^ 3 * Real.log N / ε₀ ^ 2 ≤ h₀ →
    ∀ z : cBNC ε → ℂ,
      2 * ((min (cBp ε) (cBq ε) : ℕ) : ℝ) * cBhs (cBpp ε z) ≤ (ε₀ / (8 * ((cBp ε : ℝ) * cBq ε))) ^ 2 →
      (1 - 2 * (ε₀ / (8 * ((cBp ε : ℝ) * cBq ε)))) * cBQ ε lam z ≤
        2 * cBPh lam (cBpp ε z) - Real.log (cBJ ε z)
def cBTail : Prop :=
  ∀ (ι : Type) [Fintype ι] (w : ι → ℝ) (G : (ι → ℂ) → ℝ) (R δ : ℝ), (∀ j, 0 < w j) → 0 < R → 0 ≤ δ →
    (∀ z, 0 ≤ G z) → Measurable G →
    (∀ Y : ι → ℂ, ∑ j, ‖Y j‖ ^ 2 = R ^ 2 → ∃ κ : ℝ, 2 * (Fintype.card ι : ℝ) ≤ κ ∧
      (∀ s : ℝ, 1 ≤ s → G ((s : ℂ) • Y) ≤ Real.exp (-(κ * s))) ∧
      Real.exp (-κ) ≤ δ * (Real.Gamma (Fintype.card ι) / (2 * (∑ j, w j * ‖Y j‖ ^ 2) ^ Fintype.card ι))) →
    IntegrableOn G {z : ι → ℂ | R ^ 2 < ∑ j, ‖z j‖ ^ 2} ∧
      ∫ z in {z : ι → ℂ | R ^ 2 < ∑ j, ‖z j‖ ^ 2}, G z ≤ δ * ∫ z : ι → ℂ, Real.exp (-∑ j, w j * ‖z j‖ ^ 2)
def cBBall : Prop :=
  ∀ (ι : Type) [Fintype ι] (t : ℝ), 0 ≤ t →
    (volume {z : ι → ℂ | ∑ j, ‖z j‖ ^ 2 ≤ t}).toReal =
      Real.pi ^ Fintype.card ι * t ^ Fintype.card ι / ((Fintype.card ι).factorial : ℝ)
def cBIntLow : Prop :=
  ∀ (N : ℕ) (ε : Fin N → Bool) (lam : Fin N → ℝ) (ε₀ h₀ : ℝ),
    StrictAnti lam → (∀ a b, ε a ≠ ε b → h₀ ≤ |lam a - lam b|) →
    Real.exp (-(N : ℝ)) ≤ ε₀ → ε₀ < 1 / 2 →
    8192 * ((min (cBp ε) (cBq ε) : ℕ) : ℝ) * ((cBp ε : ℝ) * cBq ε) ^ 3 * Real.log N / ε₀ ^ 2 ≤ h₀ →
    Integrable (fun z : cBNC ε → ℂ => Real.exp (-(2 * cBPh lam (cBpp ε z))) * cBJ ε z) ∧
    0 < ∫ z : cBNC ε → ℂ, Real.exp (-(2 * cBPh lam (cBpp ε z))) * cBJ ε z ∧
    ∫ z : cBNC ε → ℂ, Real.exp (-(2 * cBPh lam (cBpp ε z))) * cBJ ε z ≤ (1 + 0.58 * ε₀) * cBPi ε lam
def cBPhBall : Prop :=
  ∀ (N : ℕ) (ε : Fin N → Bool) (lam : Fin N → ℝ) (Λ : ℝ) (z : cBNC ε → ℂ),
    (∀ a b : Fin N, a < b → ((b.val : ℝ) - a.val) ≤ lam a - lam b) → (∀ a b, lam a - lam b ≤ Λ) →
    2 * ((min (cBp ε) (cBq ε) : ℕ) : ℝ) * cBhs (cBpp ε z) ≤ 1 →
    cBPh lam (cBpp ε z) ≤ Λ * cBhs (cBpp ε z)
end Formalism.MainNotions.Ext.CutB


