-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_HermFormPullEqOfLbIsoPow
-- name    : Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_HermFormPullEqOfLbIsoPow
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:15:26.835027+00:00
-- url     : https://prove2.me/theorems/3073527a-9a14-4b89-b928-6626f1c9aba2
-- title:
--   Herm Form Pull Eq Of Lb Iso Pow
-- statement:
--   Definitions and structural lemmas for Herm Form Pull Eq Of Lb Iso Pow, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/HermFormPullEqOfLbIsoPow.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_AppellHumbertTrivialOfNowhereVanishing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
namespace GlobalTheory
namespace PullHermitian
section Values
variable {X : Scheme.{0}} (x : Sp ℂ ⟶ X)
def unitVal {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) : Γ(X, U)ˣ →* ℂˣ :=
  Units.map ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom.comp (x.appLE U ⊤ h).hom).toMonoidHom
lemma inf_of {U V : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) (h' : ⊤ ≤ x ⁻¹ᵁ V) : ⊤ ≤ x ⁻¹ᵁ (U ⊓ V) :=
  fun _ hp => ⟨h hp, h' hp⟩
abbrev idx {Y : Scheme.{0}} {L : LB X} {L' : LB Y} (f : X ⟶ Y) (m n : ℕ) (i : L.ι) (j : L'.ι) :
    (LB.div (lbPow L n) (lbPow (L'.pull f) m)).ι := (fun _ => i, fun _ _ => j)
end Values
end PullHermitian
end GlobalTheory


