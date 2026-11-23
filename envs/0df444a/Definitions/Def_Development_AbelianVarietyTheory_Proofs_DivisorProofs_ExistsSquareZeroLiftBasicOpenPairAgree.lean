-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSquareZeroLiftBasicOpenPairAgree
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSquareZeroLiftBasicOpenPairAgree
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:19:01.715202+00:00
-- url     : https://prove2.me/theorems/82362af1-36ff-48b9-ad95-2c0272d14a1c
-- title:
--   Exists Square Zero Lift Basic Open Pair Agree
-- statement:
--   Definitions and structural lemmas for Exists Square Zero Lift Basic Open Pair Agree, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSquareZeroLiftBasicOpenPairAgree.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsCombIn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsAffineCombinationInChartSpecMapComp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PreimageEqOfSquareZeroThickeningStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSqZeroExtendLocalizationAwayPowStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
namespace GlobalTheory.SecGlue.Pair
def strHom {R : Type} [CommRing R] (X : Over (Sp R)) (V : X.left.Opens) : R →+* Γ(X.left, V) :=
  ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ X.hom.appLE ⊤ V (le_top : V ≤ X.hom ⁻¹ᵁ ⊤)).hom
end GlobalTheory.SecGlue.Pair
namespace GlobalTheory.SecGlue.Pair
end GlobalTheory.SecGlue.Pair
namespace GlobalTheory.SecGlue.Pair
end GlobalTheory.SecGlue.Pair
namespace GlobalTheory.SecGlue.Pair
end GlobalTheory.SecGlue.Pair
namespace GlobalTheory.SecGlue
end GlobalTheory.SecGlue


