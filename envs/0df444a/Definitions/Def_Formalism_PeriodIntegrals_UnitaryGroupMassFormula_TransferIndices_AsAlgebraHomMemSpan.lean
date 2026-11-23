-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_AsAlgebraHomMemSpan
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_AsAlgebraHomMemSpan
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:44:56.333605+00:00
-- url     : https://prove2.me/theorems/d96fdfcf-9b65-4a92-961d-f8e1157ffbc5
-- title:
--   As Algebra Hom Mem Span
-- statement:
--   Definitions and structural lemmas for As Algebra Hom Mem Span, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TransferIndices/AsAlgebraHomMemSpan.lean

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
namespace PI.Dv.TIW
section Span
variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G] {W : Type} [AddCommGroup W] [Module K W]
  [FiniteDimensional K W]
end Span
section Select
variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
end Select
end PI.Dv.TIW


