-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianHeisenbergOperatorLaws
-- name    : Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianHeisenbergOperatorLaws
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T06:38:15.195346+00:00
-- url     : https://prove2.me/theorems/ba3ec594-df59-480b-8dfa-13f4e2d6e902
-- title:
--   Hermitian Heisenberg Operator Laws
-- statement:
--   Definitions and structural lemmas for Hermitian Heisenberg Operator Laws, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/HermitianHeisenbergOperatorLaws.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ThHEqThSDictionary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionUnitaryGroupTestFunctionsStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
namespace GlobalTheory.SW.HeisH
noncomputable section
section Cplx
variable {n N : ℕ}
end Cplx
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Finset (E →+* ℂ)} {n N : ℕ}
def pairT (b x : Matrix (Fin n) (Fin N) E) : ℚ := Algebra.trace ℚ E (∑ k, ∑ a, b k a * cc (x k a))
end
end GlobalTheory.SW.HeisH


