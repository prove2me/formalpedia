-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_SigmaCount
-- name    : Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_SigmaCount
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:41:06.317916+00:00
-- url     : https://prove2.me/theorems/2bb73bc4-282c-485a-92ef-a18d8d13898e
-- title:
--   Sigma Count
-- statement:
--   Definitions and structural lemmas for Sigma Count, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/SigmaCount.lean

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityRatio
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FiniteRepSetOfOrtho
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
namespace Formalism.HermitianLattices.Ext.L3
section Defs
variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
def eA (h : V →ₗ⋆[K] V →ₗ[K] K) (A : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F)) : ℕ :=
  sInf {e : ℕ | ∀ x : V, (∀ y ∈ A, h y x ∈ locF 𝔭 (1 : Submodule (𝓞 K) K)) →
    ∀ t ∈ 𝔭 ^ e, algebraMap (𝓞 F) (𝓞 K) t • x ∈ A}
def sigmaCount (h : V →ₗ⋆[K] V →ₗ[K] K) (A : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F)) (j : ℕ) : ℕ :=
  Nat.card {Y : Module.End (𝓞 K) (↥A ⧸ ((extP K 𝔭) ^ j • ⊤ : Submodule (𝓞 K) ↥A)) //
    ∀ x y x' y' : ↥A, Submodule.Quotient.mk x' = Y (Submodule.Quotient.mk x) →
      Submodule.Quotient.mk y' = Y (Submodule.Quotient.mk y) →
      CongrP 𝔭 j (h (x' : V) (y : V) + h (x : V) (y' : V)) 0}
def redCount (h : V →ₗ⋆[K] V →ₗ[K] K) (A : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F)) (j : ℕ) : ℕ :=
  Nat.card {X : Module.End (𝓞 K) (↥A ⧸ ((extP K 𝔭) ^ j • ⊤ : Submodule (𝓞 K) ↥A)) //
    ∃ g ∈ autSub h A, ∀ x : ↥A, ∃ y : ↥A, (y : V) = g x ∧
      X (Submodule.Quotient.mk x) = Submodule.Quotient.mk y}
def repRatio (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F)) (n : 𝓞 F) : ℝ :=
  (Ideal.absNorm 𝔭 : ℝ) ^ ((finrank K V - 1) * vd h L 𝔭) * alphaN h L 𝔭 n / alphaL h L 𝔭
end Defs
def LIRatio : Prop :=
  ∀ (K F : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K],
    Formalism.HermitianLatticesTheory.IsCMUnram K → IsFixF K F →
    ∀ (V V' : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
      [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
      [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V'] (h : V →ₗ⋆[K] V →ₗ[K] K)
      (h' : V' →ₗ⋆[K] V' →ₗ[K] K) (S : VecSplit h h') (L L₀ : Submodule (𝓞 K) V)
      (𝔭 : Ideal (𝓞 F)) (n : 𝓞 F),
      h.IsSymm → IsTotPosDef h → 𝔭.IsMaximal → n ≠ 0 → h S.x₀ S.x₀ = algebraMap F K (n : F) →
      Submodule.IsLattice K L → Formalism.HermitianLatticesTheory.IsIntegralLat h L →
      Submodule.IsLattice K L₀ → Formalism.HermitianLatticesTheory.IsIntegralLat h L₀ →
      psiP S L 𝔭 * repRatio h L₀ 𝔭 n = psiP S L₀ 𝔭 * repRatio h L 𝔭 n
def LIPin : Prop :=
  ∀ (K F : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K],
    Formalism.HermitianLatticesTheory.IsCMUnram K → IsFixF K F →
    ∀ (V V' : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
      [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
      [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V'] (h : V →ₗ⋆[K] V →ₗ[K] K)
      (h' : V' →ₗ⋆[K] V' →ₗ[K] K) (S : VecSplit h h') (𝔭 : Ideal (𝓞 F)) (n : 𝓞 F),
      h.IsSymm → IsTotPosDef h → 𝔭.IsMaximal → n ≠ 0 → h S.x₀ S.x₀ = algebraMap F K (n : F) →
      ∃ L₀ : Submodule (𝓞 K) V, Submodule.IsLattice K L₀ ∧ Formalism.HermitianLatticesTheory.IsIntegralLat h L₀ ∧
        repRatio h L₀ 𝔭 n ≠ 0 ∧
        psiP S L₀ 𝔭 = (Ideal.absNorm 𝔭 : ℝ) ^ ((finrank K V - 1) * vF 𝔭 n) *
          alphaStd K 𝔭 (finrank K V - 1) * repRatio h L₀ 𝔭 n
end Formalism.HermitianLattices.Ext.L3


