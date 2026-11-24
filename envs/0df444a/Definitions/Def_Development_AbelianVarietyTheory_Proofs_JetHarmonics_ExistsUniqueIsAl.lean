-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsUniqueIsAl
-- name    : Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsUniqueIsAl
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T22:38:34.288439+00:00
-- url     : https://prove2.me/theorems/ed8a91b8-31ea-4085-80d3-6c47f4ea7590
-- title:
--   Exists Unique Is Al
-- statement:
--   Definitions and structural lemmas for Exists Unique Is Al, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ExistsUniqueIsAl.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_ThmASt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_RosatiAdj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_UnitOfBijectiveMulNatural
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_PowEqScaleAndExistsUniqueTorsion
import Theorems.Thm_GlobalTheory_TangentPow_pow_eq_scale_and_existsUnique_torsion
import Theorems.Thm_GlobalTheory_TangentPow_ptMap_comp_ptMap
import Theorems.Thm_GlobalTheory_restrictPoints_val
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.restrictPoints_val


set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace GlobalTheory.HodgeTateImage
open GlobalTheory.TangentPow GlobalTheory.GmPoints
variable {O : Type} [CommRing O] {G : Over (Spec (CommRingCat.of O))} [GrpObj G] {p : ℕ}
noncomputable def bc (R : Type) [CommRing R] [Algebra O R] (x : LieG G) :
    specO O (DualNumber R) ⟶ G :=
  ptMap (dualBC (Algebra.ofId O R)) ≫ x.1
theorem fst_bc (R : Type) [CommRing R] [Algebra O R] (x : LieG G) :
    ptMap (TrivSqZeroExt.fstHom O R R) ≫ bc R x = 1 := by
  have h : ptMap (TrivSqZeroExt.fstHom O R R) ≫ ptMap (dualBC (Algebra.ofId O R)) =
      ptMap (Algebra.ofId O R) ≫ ptMap (TrivSqZeroExt.fstHom O O O) := by
    rw [ptMap_comp_ptMap, ptMap_comp_ptMap]
    congr 1
    refine AlgHom.ext fun y => ?_
    simp [dualBC, TrivSqZeroExt.lift_def, TrivSqZeroExt.algebraMap_eq_inl']
  rw [bc, ← Category.assoc, h, Category.assoc, x.2]
  exact comp_one _
theorem existsUnique_lift {n : ℕ} {R : Type} [CommRing R] [Algebra O R] (hR : (p : R) ^ n = 0)
    (x : LieG G) : ∃! w : specO O (DualNumber R) ⟶ torsion G (p ^ n),
      w ≫ torsion.ι G (p ^ n) = bc R x :=
  (pow_eq_scale_and_existsUnique_torsion O G R (p ^ n) _ (fst_bc R x)).2 (by exact_mod_cast hR)
noncomputable def lift {n : ℕ} {R : Type} [CommRing R] [Algebra O R] (hR : (p : R) ^ n = 0)
    (x : LieG G) : specO O (DualNumber R) ⟶ torsion G (p ^ n) :=
  (existsUnique_lift hR x).choose
variable (χ : Tv G p)
noncomputable def unitAt {n : ℕ} {R : Type} [CommRing R] [Algebra O R] (hR : (p : R) ^ n = 0)
    (x : LieG G) : DualNumber R :=
  (unitOf (lift hR x ≫ χ.χ n) : DualNumber R)
end GlobalTheory.HodgeTateImage


