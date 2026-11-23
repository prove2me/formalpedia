-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_PointHeight
-- name    : Development_AbelianVarietyTheory_Definitions_Divisors_PointHeight
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T09:59:27.297654+00:00
-- url     : https://prove2.me/theorems/697fe60b-89c7-41c2-8739-ed562bd3b379
-- title:
--   Point Height
-- statement:
--   Definitions and structural lemmas for Point Height, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/PointHeight.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereLogIntegrableStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPolynomial NumberField
namespace GlobalTheory.ChowHt
structure IsChowForm {k : Type} [Field k] {N : ℕ} (I : Ideal (MvPolynomial (Fin N) k)) (D δ : ℕ)
    (f : MvPolynomial (Fin (D + 1) × Fin N) k) : Prop where

  homog : ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous (fun _ => δ) f

  irred : Irreducible (MvPolynomial.map (algebraMap k (AlgebraicClosure k)) f)

  zero_iff : ∀ u : Fin (D + 1) × Fin N → AlgebraicClosure k, MvPolynomial.aeval u f = 0 ↔
    ∃ y : Fin N → AlgebraicClosure k, y ≠ 0 ∧ (∀ g ∈ I, MvPolynomial.aeval y g = 0) ∧
      ∀ i, ∑ j, u (i, j) * y j = 0
def linSubst {R : Type} [CommRing R] {B N n : ℕ} (M : Matrix (Fin N) (Fin n) R)
    (f : MvPolynomial (Fin B × Fin N) R) : MvPolynomial (Fin B × Fin n) R :=
  MvPolynomial.aeval (fun p : Fin B × Fin N => ∑ k, C (M p.2 k) * X (p.1, k)) f
def frameNorm {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) (x : Fin N → ℂ) : ℝ :=
  Real.sqrt (∑ i, ‖(A⁻¹.mulVec x) i‖ ^ 2)
def formHeight {F : Type} [Field F] [NumberField F] {B N n : ℕ} (δ : ℕ)
    (w : Matrix (Fin N) (Fin n) F) (A : (F →+* ℂ) → Matrix (Fin N) (Fin N) ℂ)
    (f : MvPolynomial (Fin B × Fin N) F) : ℝ :=
  ((∑ᶠ v : FinitePlace F, Real.log (ReciprocityTheory.MultiplicativeHeights.gaussAbs v (linSubst w f))) +
    ∑ σ : F →+* ℂ, (ReciprocityTheory.MultiplicativeHeights.blockSphereMean B N (linSubst (A σ) (MvPolynomial.map σ f)) +
      (B : ℝ) * δ * (harmonic (N - 1) : ℝ) / 2)) / (Module.finrank ℚ F : ℝ)
def pointHeight {F : Type} [Field F] [NumberField F] {N n : ℕ}
    (w : Matrix (Fin N) (Fin n) F) (A : (F →+* ℂ) → Matrix (Fin N) (Fin N) ℂ)
    {K : Type} [Field K] [NumberField K] [Algebra F K] (y : Fin N → K) : ℝ :=
  ((∑ᶠ v : FinitePlace K, Real.log (⨆ k, v (∑ j, algebraMap F K (w j k) * y j))) +
    ∑ τ : K →+* ℂ, Real.log (Real.sqrt
      (∑ i, ‖∑ j, A (τ.comp (algebraMap F K)) j i * τ (y j)‖ ^ 2))) / (Module.finrank ℚ K : ℝ)
def ConjCompat {F : Type} [Field F] {N : ℕ} (A : (F →+* ℂ) → Matrix (Fin N) (Fin N) ℂ) : Prop :=
  ∀ (σ : F →+* ℂ) (x : Fin N → ℂ),
    frameNorm (A ((starRingEnd ℂ).comp σ)) (fun j => (starRingEnd ℂ) (x j)) = frameNorm (A σ) x
end GlobalTheory.ChowHt


