-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsSemiAbelianOfCharts
-- name    : Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsSemiAbelianOfCharts
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:08:52.918808+00:00
-- url     : https://prove2.me/theorems/e1c4fb02-eb96-4d51-b0e0-013db5cb7e84
-- title:
--   Is Semi Abelian Of Charts
-- statement:
--   Definitions and structural lemmas for Is Semi Abelian Of Charts, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/IsSemiAbelianOfCharts.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SABBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
noncomputable section
namespace GlobalTheory.GroupGlue
variable {X : Scheme.{0}} (𝒰 : X.OpenCover.{0})
variable {𝒰} {G : Over X} {H : ∀ i, Over (𝒰.X i)} {ψ : ∀ i, (H i).left ⟶ G.left}
def res {Y S S' : Scheme.{0}} (k : S' ⟶ S) (u : S ⟶ Y) : Over.mk (k ≫ u) ⟶ Over.mk u := Over.homMk k rfl
variable [∀ i, GrpObj (H i)]
def MulCompat (ψ : ∀ i, (H i).left ⟶ G.left) : Prop :=
  ∀ (i j : 𝒰.I₀) (S : Scheme.{0}) (u : S ⟶ 𝒰.X i) (v : S ⟶ 𝒰.X j) (a a' : Over.mk u ⟶ H i)
    (b b' : Over.mk v ⟶ H j), a.left ≫ ψ i = b.left ≫ ψ j → a'.left ≫ ψ i = b'.left ≫ ψ j →
      (a * a').left ≫ ψ i = (b * b').left ≫ ψ j
variable [GrpObj G]
end GlobalTheory.GroupGlue


