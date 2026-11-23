-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_DerivDerivConstMulCexpBilinearAtZero
-- name    : Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_DerivDerivConstMulCexpBilinearAtZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:44:13.964082+00:00
-- url     : https://prove2.me/theorems/3ebe47f0-6c3e-429e-b66e-a0b281525a8e
-- title:
--   Deriv Deriv Const Mul Cexp Bilinear At Zero
-- statement:
--   Definitions and structural lemmas for Deriv Deriv Const Mul Cexp Bilinear At Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/DerivDerivConstMulCexpBilinearAtZero.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpace
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
namespace GlobalTheory.SW.HeatTerm
noncomputable section
def loc {n N : ℕ} (C D Z : Matrix (Fin N) (Fin N) ℂ) (z z' : Matrix (Fin n) (Fin N) ℂ) : ℂ :=
  ((C * Z + D).det ^ n * cexp (2 * Real.pi * I * ∑ k, z' k ⬝ᵥ ((C * Z + D)⁻¹ * C) *ᵥ z k))⁻¹
variable {E : Type} [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)) {n N : ℕ}
end
end GlobalTheory.SW.HeatTerm


