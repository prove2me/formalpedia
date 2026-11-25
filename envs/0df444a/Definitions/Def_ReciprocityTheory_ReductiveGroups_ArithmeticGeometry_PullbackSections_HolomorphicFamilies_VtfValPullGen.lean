-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_VtfValPullGen
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_VtfValPullGen
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T15:17:38.187676+00:00
-- url     : https://prove2.me/theorems/02e9b210-e2da-5312-999c-5dcd6e3301a2
-- title:
--   Vtf Val Pull Gen
-- statement:
--   Definitions and structural lemmas for Vtf Val Pull Gen, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/VtfValPullGen.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_VtFrRdA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Opposite
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.TB.ValAt Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
section LC
variable {X Y Z : Scheme.{0}} (L : LB X) {K K' : Type} [Fintype K] [Fintype K']
end LC
section Liou
variable {g : ℕ}
end Liou
structure VtFr {S : Scheme.{0}} (A : Over S) [GrpObj A] (L : RigLB A) (x0 : Sp ℂ ⟶ S) (g : ℕ) where
  e : (Fin g → ℂ) → (Over.mk x0 ⟶ A)
  lat : AddSubgroup (Fin g → ℂ)
  span : Submodule.span ℝ (lat : Set (Fin g → ℂ)) = ⊤
  e_add : ∀ z w, e (z + w) = e z * e w
  e_ker : ∀ z, e z = 1 ↔ z ∈ lat
  hol : IsHolFam (fun z => (e z).left)
  Hm : Matrix (Fin g) (Fin g) ℂ
  χ : (Fin g → ℂ) → ℂ
  fr : L.L.ι → (Fin g → ℂ) → ℂ
  fr_hol : ∀ j, DifferentiableOn ℂ (fr j) {z | ⊤ ≤ (e z).left ⁻¹ᵁ L.L.U j}
  fr_ne : ∀ j z, ⊤ ≤ (e z).left ⁻¹ᵁ L.L.U j → fr j z ≠ 0
  fr_g : ∀ j j' z, ⊤ ≤ (e z).left ⁻¹ᵁ (L.L.U j ⊓ L.L.U j') →
    fr j z = valAt' (e z).left _ (L.L.g j j').val * fr j' z
  fr_0 : ∀ j, ⊤ ≤ (e 0).left ⁻¹ᵁ L.L.U j →
    fr j 0 = valAt' x0 ((L.L.pull (eSec A)).U (fun _ => j)) (L.rig.s (fun _ => j)).val
  χ_norm : ∀ a ∈ lat, ‖χ a‖ = 1
  fr_per : ∀ a ∈ lat, ∀ j z, ⊤ ≤ (e z).left ⁻¹ᵁ L.L.U j →
    fr j z = χ a * Complex.exp (Real.pi * hermForm Hm z a + Real.pi / 2 * hermForm Hm a a) * fr j (z + a)
end ReciprocityTheory.ChartRestriction.G.PullbackSections


