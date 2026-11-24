-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PProjDimSpread
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PProjDimSpread
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:07:23.674493+00:00
-- url     : https://prove2.me/theorems/41ff5c20-74fb-4dd1-b3cc-a095d4cb0494
-- title:
--   PProj Dim Spread
-- statement:
--   Definitions and structural lemmas for PProj Dim Spread, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PProjDimSpread.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StProjDimSpread
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open CategoryTheory
variable {R : Type} [CommRing R]
noncomputable def ProjDimSpread.localizedModuleEquiv (M : ModuleCat.{0} R) (S : Submonoid R) :
    M.localizedModule S ≃ₗ[Localization S] LocalizedModule S M :=
  LinearEquiv.extendScalarsOfIsLocalization S (Localization S)
    (IsLocalizedModule.linearEquiv S (M.localizedModuleMkLinearMap S)
      (LocalizedModule.mkLinearMap S M))
noncomputable def ProjDimSpread.quotientEquiv (I Q : Ideal R) [Q.IsPrime] :
    (ModuleCat.of R (R ⧸ I)).localizedModule Q.primeCompl ≃ₗ[Localization.AtPrime Q]
      (Localization.AtPrime Q ⧸ I.map (algebraMap R (Localization.AtPrime Q))) :=
  ((ProjDimSpread.localizedModuleEquiv (ModuleCat.of R (R ⧸ I)) Q.primeCompl).trans
    (LinearEquiv.extendScalarsOfIsLocalization Q.primeCompl (Localization.AtPrime Q)
      (IsLocalizedModule.linearEquiv Q.primeCompl (LocalizedModule.mkLinearMap Q.primeCompl (R ⧸ I))
        (I.toLocalizedQuotient' (Localization.AtPrime Q) Q.primeCompl
          (Algebra.linearMap R (Localization.AtPrime Q)))))).trans
    (Submodule.quotEquivOfEq _ _
      (Ideal.localized'_eq_map (Localization.AtPrime Q) Q.primeCompl I))
end GroundTheory.Heights₂.Heights


