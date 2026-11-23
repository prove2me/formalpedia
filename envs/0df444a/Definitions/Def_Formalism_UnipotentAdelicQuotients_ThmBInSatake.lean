-- Prove2me | Definitions.Def_Formalism_UnipotentAdelicQuotients_ThmBInSatake
-- name    : Formalism_UnipotentAdelicQuotients_ThmBInSatake
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:08:15.071801+00:00
-- url     : https://prove2.me/theorems/b0177e57-1924-4eb4-8494-20e95859837e
-- title:
--   Thm BIn Satake
-- statement:
--   Definitions and structural lemmas for Thm BIn Satake, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/UnipotentAdelicQuotients/ThmBInSatake.lean

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
open NumberField IsDedekindDomain
namespace HeckeCharacterZeroLocus.ThmBIn
variable {K : Type} [Field K] [NumberField K]
def Kmax (w : HeightOneSpectrum (𝓞 K)) (n : ℕ) : Set (GL (Fin n) (w.adicCompletion K)) :=
  {g | ∀ i j, (g : Matrix (Fin n) (Fin n) (w.adicCompletion K)) i j ∈ w.adicCompletionIntegers K ∧
    ((g⁻¹ : GL (Fin n) (w.adicCompletion K)) : Matrix (Fin n) (Fin n) (w.adicCompletion K)) i j ∈
      w.adicCompletionIntegers K}
def IsDiagAt (w : HeightOneSpectrum (𝓞 K)) {n : ℕ} (ϖ : 𝓞 K) (d : List ℤ) (α : GL (Fin n) (w.adicCompletion K)) :
    Prop :=
  (α : Matrix (Fin n) (Fin n) (w.adicCompletion K)) =
    Matrix.diagonal (fun i => (algebraMap K (w.adicCompletion K) (ϖ : K)) ^ (d.getD i.1 0))
def IsCosetRep {G : Type} [Group G] (Kset : Set G) (α : G) (R : Finset G) : Prop :=
  (∀ γ ∈ R, ∃ k₁ ∈ Kset, ∃ k₂ ∈ Kset, γ = k₁ * α * k₂) ∧
    ∀ x : G, (∃ k₁ ∈ Kset, ∃ k₂ ∈ Kset, x = k₁ * α * k₂) → ∃! γ, γ ∈ R ∧ γ⁻¹ * x ∈ Kset
def IsSphPD (w : HeightOneSpectrum (𝓞 K)) {n : ℕ} (ϖ : 𝓞 K) (ω : GL (Fin n) (w.adicCompletion K) → ℂ) : Prop :=
  ω 1 = 1 ∧
  (∀ g, ∀ k ∈ Kmax w n, ω (g * k) = ω g ∧ ω (k * g) = ω g) ∧
  (∀ (m : ℕ) (g : Fin m → GL (Fin n) (w.adicCompletion K)) (z : Fin m → ℂ),
    (∑ i, ∑ j, star (z i) * z j * ω ((g i)⁻¹ * g j)).im = 0 ∧
      0 ≤ (∑ i, ∑ j, star (z i) * z j * ω ((g i)⁻¹ * g j)).re) ∧
  ∀ (d : List ℤ) (α : GL (Fin n) (w.adicCompletion K)), IsDiagAt w ϖ d α →
    ∀ R, IsCosetRep (Kmax w n) α R → ∀ x, ∑ γ ∈ R, ω (x * γ) = (∑ γ ∈ R, ω γ) * ω x
def splitLab (n k : ℕ) : List ℤ := List.replicate (n - k) 0 ++ List.replicate k (-1)
def satPolyL (c : List ℤ → ℂ) (q : ℕ) (r : ℕ) : Polynomial ℂ :=
  ∑ k ∈ Finset.range (r + 1), Polynomial.monomial (r - k)
    ((-1 : ℂ) ^ k * ((q : ℝ) ^ (-((k * (r - k) : ℕ) : ℝ) / 2) : ℝ) * c (splitLab r k))
def SatakeBoundLocal : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) (ϖ : 𝓞 K), ϖ ∈ w.asIdeal →
    ϖ ∉ w.asIdeal ^ 2 → ∀ (n : ℕ) (ω : GL (Fin n) (w.adicCompletion K) → ℂ), IsSphPD w ϖ ω →
    ∀ c : List ℤ → ℂ, (∀ k ≤ n, ∀ α R, IsDiagAt w ϖ (splitLab n k) α → IsCosetRep (Kmax w n) α R →
      c (splitLab n k) = ∑ γ ∈ R, ω γ) →
    ∀ a : ℂ, (satPolyL c (Ideal.absNorm w.asIdeal) n).IsRoot a →
      (Ideal.absNorm w.asIdeal : ℝ) ^ (-((n : ℝ) - 1) / 2) ≤ ‖a‖ ∧
        ‖a‖ ≤ (Ideal.absNorm w.asIdeal : ℝ) ^ (((n : ℝ) - 1) / 2)
end HeckeCharacterZeroLocus.ThmBIn
end


