-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionCommPositiveUnitaryGroup
-- name    : Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionCommPositiveUnitaryGroup
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T06:38:32.773811+00:00
-- url     : https://prove2.me/theorems/08939a8e-0b4d-4c56-bfbf-954412696751
-- title:
--   Hermitian Weil Action Comm Positive Unitary Group
-- statement:
--   Definitions and structural lemmas for Hermitian Weil Action Comm Positive Unitary Group, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/HermitianWeilActionCommPositiveUnitaryGroup.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionUnitaryGroupTestFunctionsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SchwartzBruhatInvariantIntegralMatrixMulStatement
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
namespace GlobalTheory.SW.UnitaryLeft
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)) {n N : ℕ}
def mv (h : Matrix (Fin n) (Fin n) E) (z : CM Ψ n N) : CM Ψ n N :=
  fun τ => (h.map τ.1).map conj * z τ
def mv' (h : Matrix (Fin n) (Fin n) E) (z : CM Ψ n N) : CM Ψ n N :=
  fun τ => h.map τ.1 * z τ
end
end GlobalTheory.SW.UnitaryLeft


