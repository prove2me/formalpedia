-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsUniqueScaledBaseChangeFibreSection
-- name    : Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsUniqueScaledBaseChangeFibreSection
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:30:36.557688+00:00
-- url     : https://prove2.me/theorems/6ab7b1ae-93a6-4d42-90f0-30e63709fbe8
-- title:
--   Exists Unique Scaled Base Change Fibre Section
-- statement:
--   Definitions and structural lemmas for Exists Unique Scaled Base Change Fibre Section, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsUniqueScaledBaseChangeFibreSection.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_UnivFrame
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_AppCompatGeneric
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.Frames.SecPull
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l}
theorem res_res_top {X : Scheme.{0}} {U V : X.Opens} (h : V ≤ U) (g : Γ(X, ⊤)) :
    (X.presheaf.map (homOfLE h).op).hom ((X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom g) =
      (X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom g := by
  rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, ← Functor.map_comp]
  rfl
theorem scal_res {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) (a : S) (i j : (PPx x).ι) :
    ((Gx x).presheaf.map (homOfLE (inf_le_left : (PPx x).U i ⊓ (PPx x).U j ≤ (PPx x).U i)).op).hom (scal x a i) =
      ((Gx x).presheaf.map (homOfLE (inf_le_right : (PPx x).U i ⊓ (PPx x).U j ≤ (PPx x).U j)).op).hom
        (scal x a j) := by
  simp only [scal, ReciprocityTheory.ChartRestriction.G.Out.liftFun]
  rw [res_res_top, res_res_top]
def gxMap {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) (x : Sp S ⟶ Xo.X) (x' : Sp T ⟶ Xo.X)
    (h : spMap ψ ≫ x = x') : Gx x' ⟶ Gx x :=
  ((Over.homMk (spMap ψ) h : Over.mk x' ⟶ Over.mk x) ▷ Xo.univ.t.G).left
def scalSec {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) (a : S) (s : LB.Sec (PPx x)) : LB.Sec (PPx x) where
  f i := scal x a i * s.f i
  compat i j := by
    rw [map_mul, map_mul, s.compat i j, scal_res x a i j]
    ring
end GlobalTheory.Frames.SecPull


