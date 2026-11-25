-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_JordanExists
-- name    : Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_JordanExists
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T10:07:46.065836+00:00
-- url     : https://prove2.me/theorems/69184aa2-3957-5b82-b20d-39b121a35919
-- title:
--   Jordan Exists
-- statement:
--   Definitions and structural lemmas for Jordan Exists, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/JordanExists.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_SameGenusFix
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
namespace Formalism.L2.SG.Pf.Cnt
open Formalism.HermitianLattices.Ext.L3
def NondegOn {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
    (h : V →ₗ⋆[K] V →ₗ[K] K) (X : Submodule K V) : Prop :=
  ∀ x ∈ X, (∀ y ∈ X, h x y = 0) → x = 0
def JordanExists : Prop :=
  ∀ (K F V : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V],
    Formalism.HermitianLatticesTheory.IsCMUnram K → IsFixF K F → ∀ h : V →ₗ⋆[K] V →ₗ[K] K, h.IsSymm →
    (∀ (X : Submodule K V) (L : Submodule (𝓞 K) V), NondegOn h X → IsLatIn X L →
      Formalism.HermitianLatticesTheory.IsIntegralLat h L → ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → ∃ b a, IsJordanIn h X L 𝔭 b a) ∧
    (∀ L : Submodule (𝓞 K) V, Submodule.IsLattice K L → ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal →
      ∀ b a, IsJordanIn h ⊤ L 𝔭 b a → vd h L 𝔭 = vJof 𝔭 a)
def JordanInv : Prop :=
  ∀ (K F V V' : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    [AddCommGroup V'] [Module K V'] [FiniteDimensional K V'] [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V'],
    Formalism.HermitianLatticesTheory.IsCMUnram K → IsFixF K F → ∀ (h : V →ₗ⋆[K] V →ₗ[K] K) (h' : V' →ₗ⋆[K] V' →ₗ[K] K),
    h.IsSymm → h'.IsSymm → ∀ (X : Submodule K V) (X' : Submodule K V') (L : Submodule (𝓞 K) V)
    (L' : Submodule (𝓞 K) V'), IsLatIn X L → IsLatIn X' L' → ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal →
    ∀ b a b' a', IsJordanIn h X L 𝔭 b a → IsJordanIn h' X' L' 𝔭 b' a' →
      Nonempty (DiscMod h X L 𝔭 ≃ₗ[𝓞 K] DiscMod h' X' L' 𝔭) →
      ∀ j : ℕ, ∑ i, min (vF 𝔭 (a i)) j = ∑ i, min (vF 𝔭 (a' i)) j
def JordanIsom : Prop :=
  ∀ (K F V : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V],
    Formalism.HermitianLatticesTheory.IsCMUnram K → IsFixF K F → ∀ h : V →ₗ⋆[K] V →ₗ[K] K, h.IsSymm → IsTotPosDef h → ∀ L L' : Submodule (𝓞 K) V, Submodule.IsLattice K L →
    Submodule.IsLattice K L' → ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → ∀ b a b' a',
      IsJordanIn h ⊤ L 𝔭 b a → IsJordanIn h ⊤ L' 𝔭 b' a' → (∀ i, vF 𝔭 (a i) = vF 𝔭 (a' i)) →
      ∃ g ∈ Formalism.HermitianLatticesTheory.isom h, Formalism.HermitianLatticesTheory.gmap g (locF 𝔭 L) = locF 𝔭 L'
def AlphaDisc : Prop :=
  ∀ (K F V : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V],
    Formalism.HermitianLatticesTheory.IsCMUnram K → IsFixF K F → ∀ h : V →ₗ⋆[K] V →ₗ[K] K, h.IsSymm → IsTotPosDef h → ∀ L : Submodule (𝓞 K) V, Submodule.IsLattice K L →
    Formalism.HermitianLatticesTheory.IsIntegralLat h L → ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → ∀ b a, IsJordanIn h ⊤ L 𝔭 b a →
      alphaL h L 𝔭 = (discAut h ⊤ L 𝔭 : ℝ) * alphaStd K 𝔭 (finrank K V - cJof 𝔭 a)
def GlueLoc : Prop :=
  ∀ (K F V : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V],
    Formalism.HermitianLatticesTheory.IsCMUnram K → IsFixF K F → ∀ h : V →ₗ⋆[K] V →ₗ[K] K, h.IsSymm → Nondeg h → ∀ U : Submodule K V, IsCompl U (orthK h U) →
    ∀ M T : Submodule (𝓞 K) V, IsLatIn U M → IsLatIn (orthK h U) T → ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal →
      (fibP h U 𝔭 M T ≠ 0 →
        Nonempty (DiscMod h U M 𝔭 ≃ₗ[𝓞 K] DiscMod h (orthK h U) T 𝔭) ∧
        fibP h U 𝔭 M T = discAut h (orthK h U) T 𝔭) ∧
      ∀ g ∈ isomFix h U, fibP h U 𝔭 M (Formalism.HermitianLatticesTheory.gmap g T) = fibP h U 𝔭 M T
def GlueExists : Prop :=
  ∀ (K F V : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V],
    Formalism.HermitianLatticesTheory.IsCMUnram K → IsFixF K F → ∀ h : V →ₗ⋆[K] V →ₗ[K] K, h.IsSymm → Nondeg h → ∀ U : Submodule K V, IsCompl U (orthK h U) → PosDefOn h (orthK h U) →
    (∃ Λ₀ : Submodule (𝓞 K) V, Submodule.IsLattice K Λ₀ ∧ Formalism.HermitianLatticesTheory.IsUnimodular h Λ₀) →
    ∀ M : Submodule (𝓞 K) V, IsLatIn U M → Formalism.HermitianLatticesTheory.IsIntegralLat h M →
    (∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → cJ h U M 𝔭 < finrank K (orthK h U)) →
      (GlueSet h U M).Nonempty
def GlueProd : Prop :=
  ∀ (K F V : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V],
    Formalism.HermitianLatticesTheory.IsCMUnram K → IsFixF K F → ∀ h : V →ₗ⋆[K] V →ₗ[K] K, h.IsSymm → Nondeg h → ∀ U : Submodule K V, IsCompl U (orthK h U) → PosDefOn h (orthK h U) →
    ∀ M : Submodule (𝓞 K) V, IsLatIn U M → ∀ Λ₀ ∈ GlueSet h U M,
    ∀ T : Submodule (𝓞 K) V, IsLatIn (orthK h U) T →
      ((∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → fibP h U 𝔭 M T ≠ 0) ↔
        SameGenusFix (F := F) h U (Λ₀ ⊓ (orthK h U).restrictScalars (𝓞 K)) T) ∧
      Nat.card {Λ : Submodule (𝓞 K) V // Λ ∈ GlueSet h U M ∧ Λ ⊓ (orthK h U).restrictScalars (𝓞 K) = T} =
        ∏' 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, fibP h U 𝔭.1 M T
def GlueMass : Prop :=
  ∀ (K F V : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V],
    Formalism.HermitianLatticesTheory.IsCMUnram K → IsFixF K F → ∀ h : V →ₗ⋆[K] V →ₗ[K] K, h.IsSymm → Nondeg h → ∀ U : Submodule K V, IsCompl U (orthK h U) → PosDefOn h (orthK h U) →
    ∀ M : Submodule (𝓞 K) V, IsLatIn U M → Formalism.HermitianLatticesTheory.IsIntegralLat h M → (GlueSet h U M).Nonempty →
    ∀ c : ℝ, MassConst K F (finrank K (orthK h U)) c →
      ∃ s : Finset (Submodule (𝓞 K) V), (∀ Λ ∈ s, Λ ∈ GlueSet h U M) ∧
        (∀ Λ ∈ GlueSet h U M, ∃! Λ₁, Λ₁ ∈ s ∧ ∃ g ∈ isomFix h U, Formalism.HermitianLatticesTheory.gmap g Λ₁ = Λ) ∧
        (∀ Λ ∈ s, (stabFix h U Λ).Finite) ∧
        ∑ Λ ∈ s, ((Nat.card (stabFix h U Λ) : ℕ) : ℝ)⁻¹ =
          c * nM F h U M ^ finrank K (orthK h U) *
            ∏' 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, alphaStd K 𝔭.1 (finrank K (orthK h U)) /
              alphaStd K 𝔭.1 (finrank K (orthK h U) - cJ h U M 𝔭.1)
end Formalism.L2.SG.Pf.Cnt


