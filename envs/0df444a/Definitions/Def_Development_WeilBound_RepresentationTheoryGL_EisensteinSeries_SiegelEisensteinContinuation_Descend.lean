-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_Descend
-- name    : Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_Descend
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:04:32.078607+00:00
-- url     : https://prove2.me/theorems/71b81e10-255b-4dbe-b03d-46c96fb26c2f
-- title:
--   Descend
-- statement:
--   Definitions and structural lemmas for Descend, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/EisensteinSeries/SiegelEisensteinContinuation/Descend.lean

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PositivityTheory.RgEis
def Twist : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    (Γ K S P P' : Subgroup G) (c c₀ : G → ℂ) (η η' β ξ : G → ℝ) (N : ℝ), IsCompact (K : Set G) → IsCh Γ ⊤ c₀ →
    IsPar Γ K S c → IsPar Γ K P c → IsPar Γ K P' c →
    ((AllRep K fun ρ => HasWall Γ K P P' c η η' β ρ) → AllRep K fun ρ => HasWall Γ K P P' (c * c₀) η η' β ρ) ∧
    ((AllRep K fun ρ => HasFirst Γ K S P P' c η η' β ρ) → AllRep K fun ρ => HasFirst Γ K S P P' (c * c₀) η η' β ρ) ∧
    ((AllRep K fun ρ => HasLast Γ K S P P' c η η' β ξ N ρ) → AllRep K fun ρ => HasLast Γ K S P P' (c * c₀) η η' β ξ N ρ)
def Scale : Prop := ForRep fun {G} _ _ {_W} _ _ K ρ => ∀ (Γ P P' : Subgroup G) (c : G → ℂ) (η η' β l : G → ℝ) (s : ℝ), 0 < s →
  IsHt Γ K ⊤ l → HasWall Γ K P P' c η η' β ρ →
  HasWall Γ K P P' c (fun g => s * (η g + l g)) (fun g => s * (η' g - l g)) β ρ
def Descend : Prop := ForRep fun {G} _ _ {_W} _ _ K ρ => ∀ (G₁ : Type) [Group G₁] [TopologicalSpace G₁]
  [IsTopologicalGroup G₁] [T2Space G₁] [LocallyCompactSpace G₁] (j : G₁ →* G) (Γ P : Subgroup G) (Γ₁ K₁ : Subgroup G₁)
  (c : G → ℂ) (η η' β : G → ℝ) (s : P → G₁), Continuous j → IsCompact (K₁ : Set G₁) → K₁.map j = K → Γ₁.map j = Γ →
  Continuous s → (∀ p, j (s p) = p) → IsPar Γ K P c → IsHt Γ K P η → IsHt Γ K P η' → IsHt Γ K P β →
  (AllRep K₁ fun ρ₁ => HasWall Γ₁ K₁ (P.comap j) (P.comap j) (c ∘ j) (η ∘ j) (η' ∘ j) (β ∘ j) ρ₁) →
  HasWall Γ K P P c η η' β ρ
end PositivityTheory.RgEis


