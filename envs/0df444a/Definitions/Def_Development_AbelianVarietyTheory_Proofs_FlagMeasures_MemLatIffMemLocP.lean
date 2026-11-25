-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemLatIffMemLocP
-- name    : Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemLatIffMemLocP
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T05:59:02.151348+00:00
-- url     : https://prove2.me/theorems/4aa5a66e-2aac-40f2-b752-910c295f932d
-- title:
--   Mem Lat Iff Mem Loc P
-- statement:
--   Definitions and structural lemmas for Mem Lat Iff Mem Loc P, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MemLatIffMemLocP.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Formalism_HermitianLattices_StatementLat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsIntegralOfQuad
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
namespace GlobalTheory.HL.LocDict
section Lin
variable {R K : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
end Lin
section Places
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E} (A : Places F E sig) {n : ℕ} (p : HeightOneSpectrum (𝓞 F))
end Places
end GlobalTheory.HL.LocDict


