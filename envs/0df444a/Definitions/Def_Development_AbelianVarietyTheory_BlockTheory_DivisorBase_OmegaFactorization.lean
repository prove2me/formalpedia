-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
-- name    : Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:51:39.210802+00:00
-- url     : https://prove2.me/theorems/0ea661f3-e6b8-4ea5-b3ff-3d1e6175a151
-- title:
--   Omega Factorization
-- statement:
--   Definitions and structural lemmas for Omega Factorization, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/OmegaFactorization.lean

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
open NumberField Complex
open scoped nonZeroDivisors ContDiff
namespace GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization
variable (F : Type) [Field F] [NumberField F]
abbrev Emb : Type := F →+* ℝ
abbrev Frac : Type := (FractionalIdeal (𝓞 F)⁰ F)ˣ
def upperHalf : Set (Emb F → ℂ) := {z | ∀ τ, 0 < (z τ).im}
def dF : ℝ := |(discr F : ℝ)|
variable {F}
def latM (𝔞 : Frac F) : FractionalIdeal (𝓞 F)⁰ F :=
  ((differentIdeal ℤ (𝓞 F) : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F)⁻¹ * (↑𝔞⁻¹ : FractionalIdeal (𝓞 F)⁰ F)
def nrm (𝔞 : Frac F) : ℝ := (FractionalIdeal.absNorm (𝔞 : FractionalIdeal (𝓞 F)⁰ F) : ℝ)
open NumberField Complex in
open scoped nonZeroDivisors ContDiff in
variable (F : Type) [Field F] [NumberField F] in
variable {F} in

theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.unit_inv_mul (ε : (𝓞 F)ˣ) :
    (((ε⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F) * ((ε : 𝓞 F) : F) = 1 := by
  norm_cast; simp
def latPt (z : Emb F → ℂ) (p : F × F) : Emb F → ℂ :=
  fun τ => 2 * (Real.pi : ℂ) * I * ((τ p.1 : ℂ) + (τ p.2 : ℂ) * z τ)
def LatPair (𝔞 𝔟 : Frac F) : Type :=
  {p : F × F // p.1 ∈ latM 𝔞 ∧ p.2 ∈ (𝔟 : FractionalIdeal (𝓞 F)⁰ F) ∧ p ≠ 0}
def latRel (𝔞 𝔟 : Frac F) : Setoid (LatPair 𝔞 𝔟) where
  r p q := ∃ ε : (𝓞 F)ˣ, q.1.1 = ((ε : 𝓞 F) : F) * p.1.1 ∧ q.1.2 = ((ε : 𝓞 F) : F) * p.1.2
  iseqv :=
    { refl := fun _ => ⟨1, by simp, by simp⟩
      symm := fun {p q} ⟨ε, h1, h2⟩ => ⟨ε⁻¹, by
          rw [h1, ← mul_assoc, unit_inv_mul, one_mul], by
          rw [h2, ← mul_assoc, unit_inv_mul, one_mul]⟩
      trans := fun {p q r} ⟨ε, h1, h2⟩ ⟨ε', h1', h2'⟩ => ⟨ε' * ε, by
          rw [h1', h1, ← mul_assoc]; simp, by
          rw [h2', h2, ← mul_assoc]; simp⟩ }
def eisTerm (k : ℕ) (σ : ℂ) (z : Emb F → ℂ) (p : F × F) : ℂ :=
  (∏ τ, latPt z p τ)⁻¹ ^ k * ((‖∏ τ, latPt z p τ‖ : ℝ) : ℂ) ^ (-2 * σ)
def eisClass (𝔞 𝔟 : Frac F) (k : ℕ) (σ : ℂ) (z : Emb F → ℂ) (c : Quotient (latRel 𝔞 𝔟)) : ℂ :=
  eisTerm k σ z c.out.1
def eisSum (𝔞 𝔟 : Frac F) (k : ℕ) (σ : ℂ) (z : Emb F → ℂ) : ℂ := ∑' c, eisClass 𝔞 𝔟 k σ z c
def QPair (𝔞 𝔟 : Frac F) : Type :=
  {p : F × F // p.1 ∈ (𝔞 : FractionalIdeal (𝓞 F)⁰ F) ∧ p.2 ∈ (𝔟 : FractionalIdeal (𝓞 F)⁰ F) ∧
    ∀ τ : Emb F, 0 < τ (p.1 * p.2)}
def qRel (𝔞 𝔟 : Frac F) : Setoid (QPair 𝔞 𝔟) where
  r p q := ∃ ε : (𝓞 F)ˣ, q.1.1 = (((ε⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F) * p.1.1 ∧ q.1.2 = ((ε : 𝓞 F) : F) * p.1.2
  iseqv :=
    { refl := fun _ => ⟨1, by simp, by simp⟩
      symm := fun {p q} ⟨ε, h1, h2⟩ => ⟨ε⁻¹, by
          rw [h1, inv_inv, ← mul_assoc, mul_comm ((ε : 𝓞 F) : F), unit_inv_mul, one_mul], by
          rw [h2, ← mul_assoc, unit_inv_mul, one_mul]⟩
      trans := fun {p q r} ⟨ε, h1, h2⟩ ⟨ε', h1', h2'⟩ => ⟨ε' * ε, by
          rw [h1', h1, ← mul_assoc, mul_inv]; simp, by
          rw [h2', h2, ← mul_assoc]; simp⟩ }
def qPow (ξ : F) (z : Emb F → ℂ) : ℂ := Complex.exp (2 * (Real.pi : ℂ) * I * ∑ τ, (τ ξ : ℂ) * z τ)
def qTerm (𝔞 : Frac F) (k : ℕ) (z : Emb F → ℂ) (p : F × F) : ℂ :=
  (((|(Algebra.norm ℚ p.1 : ℝ)| / nrm 𝔞) ^ (k - 1) : ℝ) : ℂ) * qPow (p.1 * p.2) z
def qClass (𝔞 𝔟 : Frac F) (k : ℕ) (z : Emb F → ℂ) (c : Quotient (qRel 𝔞 𝔟)) : ℂ := qTerm 𝔞 k z c.out.1
def IsPartialZeta (C : ClassGroup (𝓞 F)) (Z : ℂ → ℂ) : Prop :=
  DifferentiableOn ℂ Z {1}ᶜ ∧ ∀ s : ℂ, 1 < s.re →
    HasSum (fun J : {J : (Ideal (𝓞 F))⁰ // ClassGroup.mk0 J = C} =>
      ((Ideal.absNorm (J.1 : Ideal (𝓞 F)) : ℕ) : ℂ) ^ (-s)) (Z s)
def cK (F : Type) [Field F] [NumberField F] (k : ℕ) : ℝ :=
  ((k - 1).factorial : ℝ) ^ Module.finrank ℚ F * dF F ^ (((k : ℝ) - 1) / 2)
def omegaFactor (𝔞 : Frac F) : ℝ := dF F ^ ((1 : ℝ) / 2) * nrm 𝔞
def HasExpansion (𝔞 𝔟 : Frac F) (k : ℕ) (g : (Emb F → ℂ) → ℂ) : Prop :=
  ∃ Z : ℂ → ℂ, IsPartialZeta (ClassGroup.mk F 𝔞)⁻¹ Z ∧ ∀ z ∈ upperHalf F,
    Summable (qClass 𝔞 𝔟 k z) ∧
      (cK F k : ℂ) * g z / (omegaFactor 𝔞 : ℂ) ^ k =
        (2 : ℂ)⁻¹ ^ Module.finrank ℚ F * Z (1 - (k : ℂ)) + ∑' c, qClass 𝔞 𝔟 k z c
open Classical in

def wirt {Φ : Type} [Fintype Φ] (τ : Φ) (bar : Bool) (g : (Φ → ℂ) → ℂ) : (Φ → ℂ) → ℂ := fun z =>
  (fderiv ℝ g z (Pi.single τ 1) + (if bar then I else -I) * fderiv ℝ g z (Pi.single τ I)) / 2
def wirtWord {Φ : Type} [Fintype Φ] (ws : List (Φ × Bool)) (g : (Φ → ℂ) → ℂ) : (Φ → ℂ) → ℂ :=
  ws.foldr (fun w h => wirt w.1 w.2 h) g
def halfPlane : Set ℂ := {σ | -1 / 2 < σ.re}
def IsContinuation (𝔞 𝔟 : Frac F) (G : ℂ → (Emb F → ℂ) → ℂ) : Prop :=
  (∀ σ : ℂ, 0 < σ.re → ∀ z ∈ upperHalf F, Summable (eisClass 𝔞 𝔟 2 σ z) ∧ G σ z = eisSum 𝔞 𝔟 2 σ z) ∧
  (∀ σ ∈ halfPlane, ContDiffOn ℝ ∞ (G σ) (upperHalf F)) ∧
  (∀ w : List (Emb F × Bool), ∀ z ∈ upperHalf F, DifferentiableOn ℂ (fun σ => wirtWord w (G σ) z) halfPlane)
def HeckeWeightTwo : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], 2 ≤ Module.finrank ℚ F → ∀ 𝔞 𝔟 : Frac F,
    ∃ G : ℂ → (Emb F → ℂ) → ℂ, IsContinuation 𝔞 𝔟 G ∧
      DifferentiableOn ℂ (G 0) (upperHalf F) ∧ HasExpansion 𝔞 𝔟 2 (G 0)
example (z : Unit → ℂ) : wirt () false (fun w => w ()) z = 1 ∧ wirt () true (fun w => w ()) z = 0 := by
  have h : fderiv ℝ (fun w : Unit → ℂ => w ()) z = ContinuousLinearMap.proj () :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Unit => ℂ) ()).fderiv
  constructor <;> simp [wirt, h]
end GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization


