-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardPrimitiveTuplesHermitianGramModUniformizer
-- name    : Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardPrimitiveTuplesHermitianGramModUniformizer
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T07:19:15.209969+00:00
-- url     : https://prove2.me/theorems/995bf11f-667d-4e14-87e2-5b4e6166daa3
-- title:
--   Card Primitive Tuples Hermitian Gram Mod Uniformizer
-- statement:
--   Definitions and structural lemmas for Card Primitive Tuples Hermitian Gram Mod Uniformizer, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/CardPrimitiveTuplesHermitianGramModUniformizer.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_PrimOfIsUnitDet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_PrimitiveTuplesWithGramMatrixHenselCountStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NcardPrimitiveTuplesGramModNilpotentStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardHermitianMatricesDvdSqStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NcardPrimitiveTuplesWithGramMatrixResidueRingStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
namespace GlobalTheory.GramCount
section Abstract
variable {O : Type} [CommRing O]
def quotInv (c : O →+* O) (p : O) (hp : c p = p) :
    O ⧸ Ideal.span {p} →+* O ⧸ Ideal.span {p} :=
  Ideal.quotientMap _ c (by
    rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, hp]
    exact Ideal.mem_span_singleton_self p)
end Abstract
end GlobalTheory.GramCount


