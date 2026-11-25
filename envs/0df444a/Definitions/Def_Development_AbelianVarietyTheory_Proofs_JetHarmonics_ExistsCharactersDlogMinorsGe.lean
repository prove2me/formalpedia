-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsCharactersDlogMinorsGe
-- name    : Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsCharactersDlogMinorsGe
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T14:08:53.754937+00:00
-- url     : https://prove2.me/theorems/00be639d-0af5-4c1d-be7d-ed95543cc08e
-- title:
--   Exists Characters Dlog Minors Ge
-- statement:
--   Definitions and structural lemmas for Exists Characters Dlog Minors Ge, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ExistsCharactersDlogMinorsGe.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_ThmASt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_RosatiAdj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsLeadingMinorsGeOfLeRank
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_UnitOfBijectiveMulNatural
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_EqOneOfPowEqOneOfCompEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Theorems.Thm_GlobalTheory_restrictPoints_val
import Theorems.Thm_P2M_GlobalTheory_KernelNoTorsion_torsion__pow_0f791edbd64c
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
namespace GlobalTheory
namespace HodgeTateStep
variable {O : Type} [CommRing O]
theorem ptMap_fst_dualScale (a : O) :
    ptMap (TrivSqZeroExt.fstHom O O O) ≫ ptMap (dualScale a) =
      ptMap (TrivSqZeroExt.fstHom O O O) := by
  apply Over.OverMorphism.ext
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  refine RingHom.ext fun x => ?_
  simp [dualScale]
variable {G : Over (Spec (CommRingCat.of O))} [GrpObj G]
noncomputable def scaleLie (a : O) (x : LieG G) : LieG G :=
  ⟨ptMap (dualScale a) ≫ x.1, by rw [← Category.assoc, ptMap_fst_dualScale]; exact x.2⟩
noncomputable def torsionEnd (a : G ⟶ G) [IsMonHom a] (N : ℕ) : torsion G N ⟶ torsion G N :=
  KernelNoTorsion.torsionLift (torsion.ι G N ≫ a) (by
    rw [← MonObj.pow_comp, KernelNoTorsion.torsionι_pow, MonObj.one_comp])
def HasDlog (p : ℕ) {L : Type} (e : L → LieG G)
    (κ : torsion G (p ^ 1) ⟶ Gm (Spec (CommRingCat.of O))) (y : L → O) : Prop :=
  IsCharTors G (p ^ 1) κ ∧ ∀ (l : L) (R : Type) [CommRing R] [Algebra O R], (p : R) = 0 →
    ∀ w : specO O (DualNumber R) ⟶ torsion G (p ^ 1),
      w ≫ torsion.ι G (p ^ 1) = ptMap (dualBC (Algebra.ofId O R)) ≫ (e l).1 →
      (unitOf (w ≫ κ) : DualNumber R) =
        TrivSqZeroExt.inl 1 + TrivSqZeroExt.inr (algebraMap O R (y l))
end HodgeTateStep
end GlobalTheory


