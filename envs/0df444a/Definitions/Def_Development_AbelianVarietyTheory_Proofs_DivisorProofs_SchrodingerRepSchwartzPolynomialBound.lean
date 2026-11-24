-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchrodingerRepSchwartzPolynomialBound
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchrodingerRepSchwartzPolynomialBound
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:23:33.436457+00:00
-- url     : https://prove2.me/theorems/877c21bc-74e1-43f8-abb5-a82a25e6a665
-- title:
--   Schrodinger Rep Schwartz Polynomial Bound
-- statement:
--   Definitions and structural lemmas for Schrodinger Rep Schwartz Polynomial Bound, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchrodingerRepSchwartzPolynomialBound.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RealMetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsSchwartzTranslate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzTranslationSeminormBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzCharacterSeminormBound
import Theorems.Thm_GlobalTheory_RealWeil_pPart_smul
import Theorems.Thm_GlobalTheory_RealWeil_qPart_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory GlobalTheory.RealWeil Filter Topology
open scoped SchwartzMap RealInnerProductSpace
noncomputable section
namespace GlobalTheory.RealWeil.SchrFamily
variable {l : Type} [Fintype l]
def pCLM (l : Type) [Fintype l] : (l ⊕ l → ℝ) →L[ℝ] EuclideanSpace ℝ l :=
  LinearMap.toContinuousLinearMap { toFun := pPart, map_add' := pPart_add, map_smul' := pPart_smul }
def qCLM (l : Type) [Fintype l] : (l ⊕ l → ℝ) →L[ℝ] EuclideanSpace ℝ l :=
  LinearMap.toContinuousLinearMap { toFun := qPart, map_add' := qPart_add, map_smul' := qPart_smul }
end GlobalTheory.RealWeil.SchrFamily


