-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_LocallyConstantTwoCochain
-- name    : Development_AbelianVarietyTheory_Definitions_Foundations_LocallyConstantTwoCochain
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:15:00.3008+00:00
-- url     : https://prove2.me/theorems/d809eed6-015a-4354-9015-3c86985575fc
-- title:
--   Locally Constant Two Cochain
-- statement:
--   Definitions and structural lemmas for Locally Constant Two Cochain, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/LocallyConstantTwoCochain.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_NotCoboundaryConstantOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.K5
variable {p : ℕ} [Fact p.Prime] {Ω : Type*} [Field Ω] [Algebra (O0 p) Ω]
def IsCyc (T : Tower p Ω) (k : ℕ) (χ : Gal p Ω → ZMod (p ^ k)) : Prop :=
  ∀ g : Gal p Ω, g (T.ζ k) = T.ζ k ^ (χ g).val
def LocallyConstantTwoCochain (k : ℕ) (ξ : Gal p Ω → Gal p Ω → Ω) : Prop :=
  (∀ g h, IsInt p (ξ g h)) ∧ ∀ g h, ∃ S : Finset Ω, ∀ g' h' : Gal p Ω,
    (∀ x ∈ S, g' x = g x ∧ h' x = h x) → Cong p k (ξ g' h') (ξ g h)
def IsTwistedTwoCocycleModPow (k : ℕ) (H : Subgroup (Gal p Ω)) (χ : Gal p Ω → ZMod (p ^ k)) (ξ : Gal p Ω → Gal p Ω → Ω) : Prop :=
  ∀ g ∈ H, ∀ h ∈ H, ∀ t ∈ H,
    Cong p k (((χ g).val : Ω) * g (ξ h t) + ξ g (h * t)) (ξ (g * h) t + ξ g h)
def IsTwistedTwoCoboundaryModPow (k : ℕ) (H : Subgroup (Gal p Ω)) (χ : Gal p Ω → ZMod (p ^ k)) (ξ : Gal p Ω → Gal p Ω → Ω) : Prop :=
  ∃ w : Gal p Ω → Ω, LocallyConstantOneCochain k w ∧ ∀ g ∈ H, ∀ h ∈ H,
    Cong p k (ξ g h) (((χ g).val : Ω) * g (w h) - w (g * h) + w g)
end GlobalTheory.K5


