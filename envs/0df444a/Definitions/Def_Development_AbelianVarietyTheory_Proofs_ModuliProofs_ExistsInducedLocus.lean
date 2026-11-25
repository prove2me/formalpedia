-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsInducedLocus
-- name    : Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsInducedLocus
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T15:03:57.271803+00:00
-- url     : https://prove2.me/theorems/fe19f866-a869-580b-bb82-8f17ff49fde5
-- title:
--   Exists Induced Locus
-- statement:
--   Definitions and structural lemmas for Exists Induced Locus, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsInducedLocus.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SpMapComp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
namespace GlobalTheory.LevCover
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {S : Scheme.{0}}
variable {l : Level H}
structure LevStr {B : Type} [CommRing B] {b : Base l B} {s : S ⟶ Sp B} (o : Obj D l b s) {l₂ : Level H}
    (b₂ : Base l₂ B) (T : Over S) (χ θ : D.La → (T ⟶ o.t.G)) : Prop where
  add : ∀ a c, χ (a + c) = χ a * χ c
  ker : ∀ a ∈ l₂.Mb • (⊤ : Submodule (𝓞 E) D.La), χ a = 1
  addA : ∀ a c, θ (a + c) = θ a * θ c
  kerA : ∀ a, θ (l₂.A • a) = 1
  low : ∀ a, χ a ^ (l₂.M / l.M) = toUnit T ≫ o.eta a
  lowA : ∀ a, θ a ^ (l₂.A / l.A) = toUnit T ≫ o.etaA a
  geom : ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (β : B →+* k), x ≫ s = spMap β →
    ∀ y : Over.mk x ⟶ T, ∃ I : TateAt D o.t x, (I.ζ l₂.A : k) = β b₂.ζ ∧ (∀ a, y ≫ θ a = I.ev l₂.A a) ∧
      ∀ a ∈ Mc l₂ • (⊤ : Submodule (𝓞 E) D.La), y ≫ χ a = I.ev l₂.M a
end GlobalTheory.LevCover


