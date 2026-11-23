-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:45:08.576979+00:00
-- url     : https://prove2.me/theorems/6d5a7774-59ad-4368-9812-beaed2ae7da1
-- title:
--   KFac Differentiable
-- statement:
--   Definitions and structural lemmas for KFac Differentiable, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/KFacDifferentiable.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Complex MeasureTheory
open scoped nonZeroDivisors ContDiff
namespace GlobalTheory.HeckeTwo
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization
variable {F : Type} [Field F] [NumberField F]
def NZ (I : FractionalIdeal (𝓞 F)⁰ F) : Type := {b : F // b ∈ I ∧ b ≠ 0}
def unitRel (I : FractionalIdeal (𝓞 F)⁰ F) : Setoid (NZ I) where
  r p q := ∃ ε : (𝓞 F)ˣ, q.1 = ((ε : 𝓞 F) : F) * p.1
  iseqv :=
    { refl := fun _ => ⟨1, by simp⟩
      symm := fun {p q} ⟨ε, h⟩ => ⟨ε⁻¹, by rw [h, ← mul_assoc, unit_inv_mul, one_mul]⟩
      trans := fun {p q r} ⟨ε, h⟩ ⟨ε', h'⟩ => ⟨ε' * ε, by rw [h', h, ← mul_assoc]; simp⟩ }
def phi (σ w : ℂ) : ℂ := w⁻¹ ^ 2 * ((‖w‖ : ℝ) : ℂ) ^ (-2 * σ)
def hTrans (σ : ℂ) (ν y : ℝ) : ℂ :=
  ∫ t : ℝ, phi σ ((t : ℂ) + (y : ℂ) * I) * Complex.exp (-(2 * (Real.pi : ℂ) * I * (ν : ℂ) * (t : ℂ)))
def cConst (σ : ℂ) : ℂ := hTrans σ 0 1
variable (F) in

def kFac (σ : ℂ) : ℂ :=
  ∏ _τ : Emb F, ((2 * (Real.pi : ℂ) * I)⁻¹ ^ 2 * ((2 * Real.pi : ℝ) : ℂ) ^ (-2 * σ))
def fTerm (σ : ℂ) (z : Emb F → ℂ) (b ν : F) : ℂ :=
  ∏ τ : Emb F, (Complex.exp (2 * (Real.pi : ℂ) * I * ((τ ν * τ b * (z τ).re : ℝ) : ℂ)) *
    hTrans σ (τ ν) (τ b * (z τ).im))
def aPart (𝔞 : Frac F) (σ : ℂ) : ℂ :=
  ∑' c : Quotient (unitRel (latM 𝔞)), eisTerm 2 σ 0 (c.out.1, 0)
def bOne (𝔞 𝔟 : Frac F) (σ : ℂ) (z : Emb F → ℂ) : ℂ :=
  ∑' c : Quotient (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F)),
    ∑' ν : NZ (𝔞 : FractionalIdeal (𝓞 F)⁰ F), fTerm σ z c.out.1 ν.1
def bZero (Zb : ℂ → ℂ) (𝔞 𝔟 : Frac F) (σ : ℂ) (z : Emb F → ℂ) : ℂ :=
  if σ = 0 then 0 else
    kFac F σ * (omegaFactor 𝔞 : ℂ) * ((nrm 𝔟 : ℝ) : ℂ) ^ (-1 - 2 * σ) * Zb (1 + 2 * σ) *
      ∏ τ : Emb F, (cConst σ * (((z τ).im : ℝ) : ℂ) ^ (-1 - 2 * σ))
def gFun (Zb : ℂ → ℂ) (𝔞 𝔟 : Frac F) (σ : ℂ) (z : Emb F → ℂ) : ℂ :=
  aPart 𝔞 σ + bZero Zb 𝔞 𝔟 σ z + kFac F σ * (omegaFactor 𝔞 : ℂ) * bOne 𝔞 𝔟 σ z
def IsGood (P : ℂ → (Emb F → ℂ) → ℂ) : Prop :=
  (∀ σ ∈ halfPlane, ContDiffOn ℝ ∞ (P σ) (upperHalf F)) ∧
  (∀ w : List (Emb F × Bool), ∀ z ∈ upperHalf F, DifferentiableOn ℂ (fun σ => wirtWord w (P σ) z) halfPlane)
example (𝔞 : Frac F) (σ : ℂ) (z : Emb F → ℂ) (a : F) : eisTerm 2 σ z (a, 0) = eisTerm 2 σ 0 (a, 0) := by
  simp [eisTerm, latPt]
end GlobalTheory.HeckeTwo


