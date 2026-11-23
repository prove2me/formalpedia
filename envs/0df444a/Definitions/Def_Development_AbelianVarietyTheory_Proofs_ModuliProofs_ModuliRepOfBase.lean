-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ModuliRepOfBase
-- name    : Development_AbelianVarietyTheory_Proofs_ModuliProofs_ModuliRepOfBase
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:58:36.985686+00:00
-- url     : https://prove2.me/theorems/3e82ea4c-53b2-4f63-b190-0a9f3ad17261
-- title:
--   Moduli Rep Of Base
-- statement:
--   Definitions and structural lemmas for Moduli Rep Of Base, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ModuliRepOfBase.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
noncomputable section
namespace GlobalTheory
def objRestrictBase {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
    {B : Type} [CommRing B] {b : Base l B} (j : KA l →+* B) {S : Scheme.{0}} {s : S ⟶ Sp B} (o : Obj D l b s)
    (hρ : j (baseKA l).ρ = b.ρ) (hζ : j (baseKA l).ζ = b.ζ) : Obj D l (baseKA l) (s ≫ spMap j) where
  t := o.t
  proper := o.proper
  ample := o.ample
  ktriv := o.ktriv
  eta := o.eta
  eta_add := o.eta_add
  eta_ker := o.eta_ker
  etaA := o.etaA
  etaA_add := o.etaA_add
  etaA_ker := o.etaA_ker
  geom := by
    intro k _ _ x β hx
    have h1 : x ≫ s = spMap (Spec.preimage (x ≫ s)).hom := by
      simp [spMap]
    have h2 : β = (Spec.preimage (x ≫ s)).hom.comp j := by
      have h3 : spMap β = spMap ((Spec.preimage (x ≫ s)).hom.comp j) := by
        rw [← hx, ← Category.assoc]
        conv_lhs => rw [h1]
        simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]
      exact congrArg CommRingCat.Hom.hom (Spec.map_injective h3)
    have h := o.geom k x _ h1
    rw [← hρ, ← hζ] at h
    subst h2
    exact h
end GlobalTheory


