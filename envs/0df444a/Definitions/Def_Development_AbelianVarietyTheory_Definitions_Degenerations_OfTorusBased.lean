-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfTorusBased
-- name    : Development_AbelianVarietyTheory_Definitions_Degenerations_OfTorusBased
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T16:24:52.809803+00:00
-- url     : https://prove2.me/theorems/c5a5e276-ffdd-4c54-8b5b-cc8839f14165
-- title:
--   Of Torus Based
-- statement:
--   Definitions and structural lemmas for Of Torus Based, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Degenerations/OfTorusBased.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_IsNormalSchemeSp
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_IsAffineSplitTorusLeft
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
namespace GlobalTheory.ZJ
variable {S : Scheme.{0}} {H : Over S} [GrpObj H]
def Charts.InK (C : Charts H.left) (a : {i // C.wt i = C.c₀}) {Y : Over S} (k : Y ⟶ H) : Prop :=
  ∃ (h : ⊤ ≤ k.left ⁻¹ᵁ C.W a) (h₁ : ⊤ ≤ (1 : Y ⟶ H).left ⁻¹ᵁ C.W a), ∀ j, C.wt j = C.c₀ →
    (k.left.appLE _ ⊤ h).hom (C.r a j) = ((1 : Y ⟶ H).left.appLE _ ⊤ h₁).hom (C.r a j)
def Charts.Based (C : Charts H.left) {d : ℕ} (c : Fin d → C.Cl) (a : {i // C.wt i = C.c₀}) (j : Fin d → C.I) : Prop :=
  ⊤ ≤ eSec H ⁻¹ᵁ C.W a ∧ ∀ n, C.wt (j n) = c n ∧ ⊤ ≤ eSec H ⁻¹ᵁ H.left.basicOpen (C.r a (j n))
def Charts.KerIs (C : Charts H.left) {d : ℕ} (a : {i // C.wt i = C.c₀}) (j : Fin d → C.I)
    (i : splitTorus S (Fin d → ℤ) ⟶ H) : Prop :=
  Mono i ∧ (∀ (Y : Over S) (k : Y ⟶ H), C.InK a k ↔ ∃ t, k = t ≫ i) ∧
    ∀ (Y : Over S) (t : Y ⟶ splitTorus S (Fin d → ℤ)) (n : Fin d) (h : ⊤ ≤ (t ≫ i).left ⁻¹ᵁ C.W a)
      (h₁ : ⊤ ≤ (1 : Y ⟶ H).left ⁻¹ᵁ C.W a), ((t ≫ i).left.appLE _ ⊤ h).hom (C.r a (j n)) =
        t.left.appTop.hom (charUnit S (Fin d → ℤ) (Pi.single n 1)).val * ((1 : Y ⟶ H).left.appLE _ ⊤ h₁).hom (C.r a (j n))
end GlobalTheory.ZJ
end


