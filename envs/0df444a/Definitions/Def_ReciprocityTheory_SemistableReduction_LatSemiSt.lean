-- Prove2me | Definitions.Def_ReciprocityTheory_SemistableReduction_LatSemiSt
-- name    : ReciprocityTheory_SemistableReduction_LatSemiSt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:12:29.085979+00:00
-- url     : https://prove2.me/theorems/33a94e5f-6648-4330-996f-840f5be9a01f
-- title:
--   Lat Semi St
-- statement:
--   Definitions and structural lemmas for Lat Semi St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/LatSemiSt.lean

import Definitions.Def_ReciprocityTheory_SemistableReduction_TorsionNonvanishStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.MultiplicativeHeights
open Matrix NumberField ComplexConjugate
open scoped ComplexOrder
def UnipotentStatement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (r g : ℕ) (γ : Matrix (Fin r) (Fin r) K)
    (Q : (K →+* ℂ) → Matrix (Fin r) (Fin r) ℂ),
    (∀ n : ℕ, 1 ≤ n → n ≤ r → ∃ z : 𝓞 K, (γ ^ n).trace - r = (g : K) * z) →
    (Real.exp (1 / 3) + 1) * r < g → (∀ σ, (Q σ).det ≠ 0) →
    (∀ σ (u : Fin r → ℂ), normSq ((Q σ * γ.map σ * (Q σ)⁻¹) *ᵥ u) ≤
      Real.exp (2 / (3 * (r : ℝ))) * normSq u) →
    (γ - 1) ^ r = 0 ∧ ∀ σ, ∑ a, ∑ b, ‖(Q σ * (γ.map σ - 1) * (Q σ)⁻¹) a b‖ ^ 2 < 1
def hq {r : ℕ} (H : Matrix (Fin r) (Fin r) ℂ) (u : Fin r → ℂ) : ℝ := (star u ⬝ᵥ (H *ᵥ u)).re
structure Majorant {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r) where

  H : (K →+* ℂ) → Matrix (Fin r) (Fin r) ℂ
  posDef : ∀ σ, (H σ).PosDef
  major : ∀ σ, H σ * (S.G.map σ)⁻¹ * H σ = S.G.map σ
  conj_compat : ∀ σ, H ((starRingEnd ℂ).comp σ) = (H σ).map (starRingEnd ℂ)
def gramC {K : Type} [Field K] [NumberField K] {r : ℕ} {k : ℕ} (H : Matrix (Fin r) (Fin r) ℂ) (σ : K →+* ℂ) (b : Fin k → Fin r → K) :
    Matrix (Fin k) (Fin k) ℂ :=
  Matrix.of fun i j => star (embVec σ (b i)) ⬝ᵥ (H *ᵥ embVec σ (b j))
def IsKBasisIn {K : Type} [Field K] [NumberField K] {r : ℕ} {k : ℕ} (B : Submodule (𝓞 K) (Fin r → K)) (b : Fin k → Fin r → K) : Prop :=
  (∀ i, b i ∈ B) ∧ LinearIndependent K b ∧ ∀ x ∈ B, x ∈ Submodule.span K (Set.range b)
def latDeg {K : Type} [Field K] [NumberField K] {r : ℕ} {k : ℕ} (H : (K →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (B : Submodule (𝓞 K) (Fin r → K))
    (b : Fin k → Fin r → K) : ℝ :=
  Real.log ((Submodule.span (𝓞 K) (Set.range b)).toAddSubgroup.relIndex B.toAddSubgroup : ℝ) -
    (1 / 2) * ∑ σ : K →+* ℂ, Real.log (gramC (H σ) σ b).det.re
def IsSemistableZero {K : Type} [Field K] [NumberField K] {r : ℕ} (H : (K →+* ℂ) → Matrix (Fin r) (Fin r) ℂ)
    (L : Submodule (𝓞 K) (Fin r → K)) : Prop :=
  (∀ (k : ℕ) (b : Fin k → Fin r → K), IsKBasisIn L b → latDeg H L b = 0) ∧
  ∀ B : Submodule (𝓞 K) (Fin r → K), B ≤ L →
    ∀ (k : ℕ) (b : Fin k → Fin r → K), IsKBasisIn B b → latDeg H B b ≤ 0
def gramX {K : Type} [Field K] [NumberField K] {r k m : ℕ} (H : Matrix (Fin r) (Fin r) ℂ)
    (σ : K →+* ℂ) (b : Fin k → Fin r → K) (c : Fin m → Fin r → K) : Matrix (Fin k) (Fin m) ℂ :=
  Matrix.of fun i j => star (embVec σ (b i)) ⬝ᵥ (H *ᵥ embVec σ (c j))
def quotGramC {K : Type} [Field K] [NumberField K] {r k m : ℕ} (H : Matrix (Fin r) (Fin r) ℂ)
    (σ : K →+* ℂ) (b : Fin k → Fin r → K) (c : Fin m → Fin r → K) : Matrix (Fin m) (Fin m) ℂ :=
  gramC H σ c - gramX H σ c b * (gramC H σ b)⁻¹ * gramX H σ b c
def satSub {K : Type} [Field K] [NumberField K] {r k : ℕ} (L : Submodule (𝓞 K) (Fin r → K))
    (b : Fin k → Fin r → K) : Submodule (𝓞 K) (Fin r → K) :=
  L ⊓ (Submodule.span K (Set.range b)).restrictScalars (𝓞 K)
def quotDeg {K : Type} [Field K] [NumberField K] {r k m : ℕ}
    (H : (K →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (L : Submodule (𝓞 K) (Fin r → K))
    (b : Fin k → Fin r → K) (c : Fin m → Fin r → K) : ℝ :=
  Real.log ((satSub L b ⊔ Submodule.span (𝓞 K) (Set.range c)).toAddSubgroup.relIndex
      L.toAddSubgroup : ℝ) -
    (1 / 2) * ∑ σ : K →+* ℂ, Real.log (quotGramC (H σ) σ b c).det.re
def DegAddStatement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (r k m : ℕ) (H : (K →+* ℂ) → Matrix (Fin r) (Fin r) ℂ)
    (L : Submodule (𝓞 K) (Fin r → K)) (b : Fin k → Fin r → K) (c : Fin m → Fin r → K),
    (∀ σ, (H σ).PosDef) → L.FG → (∀ i, b i ∈ L) → (∀ j, c j ∈ L) →
    LinearIndependent K (Fin.append b c) →
    (∀ x ∈ L, x ∈ Submodule.span K (Set.range (Fin.append b c))) →
    latDeg H L (Fin.append b c) = latDeg H (satSub L b) b + quotDeg H L b c
def SemiPointStatement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (r : ℕ) (S : HermForm K r)
    (L : Submodule (𝓞 K) (Fin r → K)),
    IsLattice L → IsSelfDual S L → ∃ M : Majorant S, IsSemistableZero M.H L
def SemistableStatement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (r : ℕ) (S : HermForm K r)
    (L : Submodule (𝓞 K) (Fin r → K)),
    IsLattice L → IsSelfDual S L → ∃ M : Majorant S, IsSemistableZero M.H L ∧
      ∀ N : Matrix (Fin r) (Fin r) K, (∀ x ∈ L, N *ᵥ x ∈ L) →
        (∀ σ (u : Fin r → ℂ), u ≠ 0 → hq (M.H σ) (N.map σ *ᵥ u) < hq (M.H σ) u) → N = 0
end ReciprocityTheory.MultiplicativeHeights


