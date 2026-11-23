-- Prove2me | Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisCohomology__BrauerDegreeZero_fefd58e19a2fa426
-- name    : P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisCohomology__BrauerDegreeZero_fefd58e19a2fa426
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:43:39.575472+00:00
-- url     : https://prove2.me/theorems/728aa8b3-3b61-410c-8ec3-50c127cff083
-- title:
--   Brauer Degree Zero
-- statement:
--   Definitions and structural lemmas for Brauer Degree Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/GaloisCohomology₂/BrauerDegreeZero.lean

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
namespace GlobalTheory.Published
open Classical in

def indFun {G : Type} [Group G] [Fintype G] (H : Subgroup G) (f : H → ℂ) (g : G) : ℂ :=
  (Nat.card H : ℂ)⁻¹ * ∑ x : G, if hx : x⁻¹ * g * x ∈ H then f ⟨x⁻¹ * g * x, hx⟩ else 0
def BrauerDegreeZero : Prop :=
  ∀ (G : Type) [Group G] [Fintype G] (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V),
    ∃ (r : ℕ) (H : Fin r → Subgroup G) (χ : ∀ i, H i →* ℂˣ) (c : Fin r → ℤ), ∀ g : G,
      LinearMap.trace ℂ V (ρ g) - (Module.finrank ℂ V : ℂ) =
        ∑ i, (c i : ℂ) * (indFun (H i) (fun x => (χ i x : ℂ)) g - indFun (H i) (fun _ => 1) g)
end GlobalTheory.Published
end


