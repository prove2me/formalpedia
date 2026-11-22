-- Prove2me | Definitions.Def_Formalism_RealPlaceAnalysis_Complexify
-- name    : Formalism_RealPlaceAnalysis_Complexify
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T16:45:49.73573+00:00
-- url     : https://prove2.me/theorems/8317ced1-fc81-41e5-a6fb-cfba2ca4937d
-- title:
--   Complexify
-- statement:
--   Definitions and structural lemmas for Complexify, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/Complexify.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
namespace Formalism.REAL
def Jm {n : ℕ} (ε : Fin n → Bool) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal fun a => if ε a then 1 else -1
def inUJ {n : ℕ} (ε : Fin n → Bool) (g : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  gᴴ * Jm ε * g = Jm ε
def inG {n : ℕ} (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  Xᴴ * Jm ε + Jm ε * X = 0
def inK {n : ℕ} (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  inG ε X ∧ X * Jm ε = Jm ε * X
def inP {n : ℕ} (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  inG ε X ∧ X * Jm ε = -(Jm ε * X)
def Kset {n : ℕ} (ε : Fin n → Bool) : Set (Matrix (Fin n) (Fin n) ℂ) :=
  {g | g ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ g * Jm ε = Jm ε * g}
def hs {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) : ℝ := ∑ i, ∑ j, ‖g i j‖ ^ 2
def UJ {n : ℕ} (ε : Fin n → Bool) : Subgroup (Matrix (Fin n) (Fin n) ℂ)ˣ where
  carrier := {g | inUJ ε (g : Matrix (Fin n) (Fin n) ℂ)}
  mul_mem' := by
    intro g h hg hh
    simp only [Set.mem_ofPred_eq, inUJ, Units.val_mul, Matrix.conjTranspose_mul] at *
    calc (h : Matrix (Fin n) (Fin n) ℂ)ᴴ * (g : Matrix (Fin n) (Fin n) ℂ)ᴴ * Jm ε *
          ((g : Matrix (Fin n) (Fin n) ℂ) * h)
        = (h : Matrix (Fin n) (Fin n) ℂ)ᴴ * ((g : Matrix (Fin n) (Fin n) ℂ)ᴴ * Jm ε * g) * h := by
          simp only [Matrix.mul_assoc]
      _ = Jm ε := by rw [hg, hh]
  one_mem' := by
    simp only [Set.mem_ofPred_eq, inUJ, Units.val_one, Matrix.conjTranspose_one, Matrix.one_mul,
      Matrix.mul_one]
  inv_mem' := by
    intro g hg
    simp only [Set.mem_ofPred_eq, inUJ] at *
    have h1 : ((g⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)ᴴ *
        (g : Matrix (Fin n) (Fin n) ℂ)ᴴ = 1 := by
      rw [← Matrix.conjTranspose_mul, Units.mul_inv, Matrix.conjTranspose_one]
    have h2 : (g : Matrix (Fin n) (Fin n) ℂ) * ((g⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) :
        Matrix (Fin n) (Fin n) ℂ) = 1 := Units.mul_inv g
    calc ((g⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)ᴴ * Jm ε *
          ((g⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)
        = ((g⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)ᴴ *
          ((g : Matrix (Fin n) (Fin n) ℂ)ᴴ * Jm ε * g) *
          ((g⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) := by rw [hg]
      _ = Jm ε := by
          rw [show ∀ A B C D E : Matrix (Fin n) (Fin n) ℂ, A * (B * C * D) * E = (A * B) * C * (D * E)
            from fun A B C D E => by simp only [Matrix.mul_assoc], h1, h2, Matrix.one_mul, Matrix.mul_one]
def UJClosed : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool), IsClosed {g : Matrix (Fin n) (Fin n) ℂ | inUJ ε g}
def ExpUJ : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ), inG ε X →
    ∀ t : ℝ, inUJ ε (NormedSpace.exp ((t : ℂ) • X))
def KFacts : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool),
    (∀ g ∈ Kset ε, inUJ ε g) ∧ IsCompact (Kset ε) ∧ Jm ε ∈ Kset ε ∧
    (∀ X, inK ε X → NormedSpace.exp X ∈ Kset ε) ∧
    (∀ g, g ∈ Kset ε ↔ (inUJ ε g ∧ g ∈ Matrix.unitaryGroup (Fin n) ℂ))
def PChar : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ),
    (inP ε X ↔ (Xᴴ = X ∧ X * Jm ε = -(Jm ε * X))) ∧
    (inP ε X → Jm ε * X * Jm ε = -X)
def Brackets : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (X Y : Matrix (Fin n) (Fin n) ℂ),
    (inK ε X → inK ε Y → inK ε (X * Y - Y * X)) ∧
    (inK ε X → inP ε Y → inP ε (X * Y - Y * X)) ∧
    (inP ε X → inP ε Y → inK ε (X * Y - Y * X)) ∧
    (inG ε X → ∃ A B, inK ε A ∧ inP ε B ∧ X = A + B) ∧
    (inK ε X → inP ε X → X = 0)
def Polar : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool),
    (∀ g, inUJ ε g → ∃ k X, k ∈ Kset ε ∧ inP ε X ∧ g = k * NormedSpace.exp X) ∧
    (∀ k k' X X', k ∈ Kset ε → k' ∈ Kset ε → inP ε X → inP ε X' →
      k * NormedSpace.exp X = k' * NormedSpace.exp X' → k = k' ∧ X = X') ∧
    (∃ L : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ,
      ContinuousOn L {g | inUJ ε g} ∧
      ∀ g, inUJ ε g → inP ε (L g) ∧ g * NormedSpace.exp (-L g) ∈ Kset ε)
def Complexify : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ),
    ∃! p : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ,
      inG ε p.1 ∧ inG ε p.2 ∧ Z = p.1 + Complex.I • p.2
def HSBall : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool),
    (∀ R : ℝ, IsCompact {g : Matrix (Fin n) (Fin n) ℂ | inUJ ε g ∧ hs g ≤ R}) ∧
    (∀ g k, k ∈ Kset ε → hs (g * k) = hs g ∧ hs (k * g) = hs g)
def UJInv : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (g : Matrix (Fin n) (Fin n) ℂ), inUJ ε g →
    g * (Jm ε * gᴴ * Jm ε) = 1 ∧ (Jm ε * gᴴ * Jm ε) * g = 1
def OneParam : Prop :=
  ∀ (n : ℕ) (X : Matrix (Fin n) (Fin n) ℂ) (s t : ℝ),
    NormedSpace.exp (((s + t : ℝ) : ℂ) • X) =
      NormedSpace.exp ((s : ℂ) • X) * NormedSpace.exp ((t : ℂ) • X)
def BallOpen : Prop :=
  ∀ (n : ℕ) (R : ℝ), (n : ℝ) < R →
    ∃ U : Set (Matrix (Fin n) (Fin n) ℂ), IsOpen U ∧ (1 : Matrix (Fin n) (Fin n) ℂ) ∈ U ∧
      ∀ g ∈ U, hs g < R
end Formalism.REAL


