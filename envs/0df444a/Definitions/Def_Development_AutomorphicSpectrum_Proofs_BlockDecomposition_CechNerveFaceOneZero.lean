-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CechNerveFaceOneZero
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CechNerveFaceOneZero
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T03:08:56.833997+00:00
-- url     : https://prove2.me/theorems/7f9f6f87-5b4b-4616-95c3-b38f1ac6155d
-- title:
--   Cech Nerve Face One Zero
-- statement:
--   Definitions and structural lemmas for Cech Nerve Face One Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CechNerveFaceOneZero.lean

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
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
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
open CategoryTheory.ComposableArrows
namespace GlobalTheory.CompanionTheory.Dict
variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)
def L0 : Cn F 0 →ₗ[R] C0 F where
  toFun f T := f (mk₀ T)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
def L1 : Cn F 1 →ₗ[R] C1 F where
  toFun f _ _ φ := f (mk₁ φ)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
def L2 : Cn F 2 →ₗ[R] C2 F where
  toFun f _ _ _ φ ψ := f (mk₂ φ ψ)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
def L3 : Cn F 3 →ₗ[R] C3 F where
  toFun f _ _ _ _ φ ψ χ := f (mk₃ φ ψ χ)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
section Faces
variable {T T' T'' T''' : C} (φ : T ⟶ T') (ψ : T' ⟶ T'') (χ : T'' ⟶ T''')
end Faces
end GlobalTheory.CompanionTheory.Dict


