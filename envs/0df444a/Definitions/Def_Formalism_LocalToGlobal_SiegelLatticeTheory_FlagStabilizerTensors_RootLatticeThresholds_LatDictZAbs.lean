-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_LatDictZAbs
-- name    : Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_LatDictZAbs
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T14:05:50.200177+00:00
-- url     : https://prove2.me/theorems/7d6e510e-fe96-48ab-ac68-986da300f80d
-- title:
--   Lat Dict ZAbs
-- statement:
--   Definitions and structural lemmas for Lat Dict ZAbs, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/LatDictZAbs.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_LatDictZSt
import Definitions.Def_Formalism_PeriodIntegrals_HermitianGenusExtension_SemilocalHermitianLattices_GmapLocEqOfFrame
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_WittExtensionTheorem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
namespace Formalism.L2.SG.Pf.LatDictZ.Z0
open ReciprocityTheory.ChartRestriction.L3.WA
def SemiGenusLoc : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (V : Type) [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (h : V →ₗ⋆[K] V →ₗ[K] K),
    Formalism.HermitianLatticesTheory.IsCMUnram K → h.IsSymm → (∀ x, (∀ y, h x y = 0) → x = 0) →
    ∀ p : Ideal (𝓞 K), p.IsMaximal →
    ∀ M₁ M₂ : AddSubgroup V, IsSelfDualMod (locRing p) h M₁ → IsSelfDualMod (locRing p) h M₂ →
      ∃ g ∈ Formalism.HermitianLatticesTheory.isom h, ∀ x, x ∈ M₁ ↔ g x ∈ M₂
def SemiGenusZLoc : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (V : Type) [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (h : V →ₗ⋆[K] V →ₗ[K] K),
    Formalism.HermitianLatticesTheory.IsCMUnram K → h.IsSymm → (∀ x, (∀ y, h x y = 0) → x = 0) →
    ∀ p : Ideal (𝓞 K), p.IsMaximal →
    ∀ {r : ℕ} (s : Fin r → V) (z : V) (M₁ M₂ : AddSubgroup V),
      IsSelfDualMod (locRing p) h M₁ → IsSelfDualMod (locRing p) h M₂ →
      (∀ a, h (s a) z = 0) →
      (∀ w ∈ Submodule.span K (Set.range s), w ∈ M₁ ↔ w ∈ M₂) →
      (∀ w ∈ M₁, ∃ w₁ ∈ M₁, w₁ ∈ Submodule.span K (Set.range s) ∧ ∀ a, h (s a) (w - w₁) = 0) →
      (∀ w ∈ M₂, ∃ w₁ ∈ M₂, w₁ ∈ Submodule.span K (Set.range s) ∧ ∀ a, h (s a) (w - w₁) = 0) →
      z ∈ M₁ → z ∈ M₂ →
      (∀ c : K, c • z ∈ M₁ → c ∈ locRing p) → (∀ c : K, c • z ∈ M₂ → c ∈ locRing p) →
      ∃ g ∈ Formalism.HermitianLatticesTheory.isom h, (∀ a, g (s a) = s a) ∧ g z = z ∧ ∀ x, x ∈ M₁ ↔ g x ∈ M₂
def PrimPlaneLoc : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (V : Type) [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (h : V →ₗ⋆[K] V →ₗ[K] K),
    Formalism.HermitianLatticesTheory.IsCMUnram K → h.IsSymm → (∀ x, (∀ y, h x y = 0) → x = 0) →
    ∀ p : Ideal (𝓞 K), p.IsMaximal →
    ∀ (N : AddSubgroup V) (z : V) (b : K), IsSelfDualMod (locRing p) h N → z ∈ N →
      (∀ c : K, c • z ∈ N → c ∈ locRing p) → ¬ IsUnitIn (locRing p) (h z z) →
      b ∈ locRing p → star b = b → (∃ w : V, h z w = 1 ∧ h w w = b) →
      ∃ y ∈ N, h z y = 1 ∧ h y y = b
end Formalism.L2.SG.Pf.LatDictZ.Z0


