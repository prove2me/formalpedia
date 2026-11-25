-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_GroupRingHomConstOfLaurent
-- name    : Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_GroupRingHomConstOfLaurent
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T14:14:44.298547+00:00
-- url     : https://prove2.me/theorems/ab20018a-d786-5b0a-8b9f-adc97c312237
-- title:
--   Group Ring Hom Const Of Laurent
-- statement:
--   Definitions and structural lemmas for Group Ring Hom Const Of Laurent, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/GroupRingHomConstOfLaurent.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_AbelianSchemeQuotients_IsAbelianScheme
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_DimSplitPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GeometricallyIntegralIffGeometricallyConnectedOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HomBaseChangeBijectiveOfLeNilradical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_BijectiveRestrictPointsOfEtaleOfHenselian
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.GroupRingConst
noncomputable def pt {R F X : Type} [CommRing R] [CommRing F] [AddCommGroup X] (r : R →+* F)
    (c : Multiplicative X →* Fˣ) : AddMonoidAlgebra R X →+* F :=
  AddMonoidAlgebra.liftNCRingHom r ((Units.coeHom F).comp c) (fun _ _ ↦ Commute.all _ _)
def powChar {G X : Type} [CommGroup G] [AddCommGroup X] (l : X →+ ℤ) (u : G) :
    Multiplicative X →* G :=
  (zpowersHom G u).comp (AddMonoidHom.toMultiplicative l)
noncomputable def family {R F X : Type} [CommRing R] [CommRing F] [AddCommGroup X] (r : R →+* F)
    (c : Multiplicative X →* Fˣ) (l : X →+ ℤ) : AddMonoidAlgebra R X →+* AddMonoidAlgebra F ℤ :=
  AddMonoidAlgebra.liftNCRingHom ((algebraMap F (AddMonoidAlgebra F ℤ)).comp r)
    (((algebraMap F (AddMonoidAlgebra F ℤ)).toMonoidHom.comp ((Units.coeHom F).comp c)) *
      ((AddMonoidAlgebra.of F ℤ).comp (AddMonoidHom.toMultiplicative l)))
    (fun _ _ ↦ Commute.all _ _)
end GlobalTheory.GroupRingConst


