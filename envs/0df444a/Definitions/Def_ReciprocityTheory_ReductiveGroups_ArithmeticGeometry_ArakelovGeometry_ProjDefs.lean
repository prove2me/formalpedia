-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ProjDefs
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ProjDefs
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:19:03.409811+00:00
-- url     : https://prove2.me/theorems/a36e1910-44b4-4638-a086-8093a35a5075
-- title:
--   Proj Defs
-- statement:
--   Definitions and structural lemmas for Proj Defs, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/ProjDefs.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsSemipositiveOn
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo Polynomial
variable {Ω : Type*} [Field Ω] [CharZero Ω] {κ : Type*} {D : ℕ}
structure IsProjFrame (x : κ → Ω) (e : Fin (D + 1) → κ) : Prop where
  inj : Function.Injective e
  free : coordIdeal ℤ (x ∘ e) = ⊥
  integral : ∀ i, IsIntegral (coneRing ℤ (x ∘ e)) (C (x i) * X : Polynomial Ω)
structure IsRatProjFrame (x : κ → Ω) (e : Fin (D + 1) → κ) : Prop where
  inj : Function.Injective e
  free : coordIdeal ℤ (x ∘ e) = ⊥
  integral : ∀ i, IsIntegral (coneRing ℚ (x ∘ e)) (C (x i) * X : Polynomial Ω)
def fnField (x : κ → Ω) : IntermediateField ℚ Ω :=
  IntermediateField.adjoin ℚ {t | ∃ i j, t = x i / x j}
def projDeg (x : κ → Ω) (e : Fin (D + 1) → κ) : ℕ :=
  IntermediateField.relfinrank (fnField (x ∘ e)) (fnField x)
open Classical in

def scaleOff (e : Fin (D + 1) → κ) (m : ℕ) (x : κ → Ω) : κ → Ω :=
  fun i => if i ∈ Set.range e then x i else (m : Ω) * x i
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry


