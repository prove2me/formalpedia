-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndices_CongSpanSingleIff
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndices_CongSpanSingleIff
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:53:50.307803+00:00
-- url     : https://prove2.me/theorems/3228b6de-48e4-4f0b-8536-31c964e06842
-- title:
--   Cong Span Single Iff
-- statement:
--   Definitions and structural lemmas for Cong Span Single Iff, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeIndices/CongSpanSingleIff.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace MassDataIdxFrA
variable {F k : Type} [Field F] [Field k] (O : ValuationSubring F) (π : O →+* k) (γ : O)
  {ι : Type} [Fintype ι] [DecidableEq ι]
def IntVec (v : ι → F) : Prop := ∀ i, v i ∈ O
def CongSpan (S : Set (ι → F)) (v : ι → F) : Prop :=
  ∃ w ∈ Submodule.span O S, ∃ z : ι → F, IntVec O z ∧ v = w + (γ : F) • z
section Mat
open Matrix
variable {F : Type} [Field F] (O : ValuationSubring F) (γ : O) {ι : Type} [Fintype ι] [DecidableEq ι]
end Mat
end MassDataIdxFrA


