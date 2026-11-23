-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BlockEigenvalues_PhiUZero
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BlockEigenvalues_PhiUZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:58:26.540705+00:00
-- url     : https://prove2.me/theorems/4f8d1b7d-e078-42c5-a959-50e38f3cc77e
-- title:
--   Phi UZero
-- statement:
--   Definitions and structural lemmas for Phi UZero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BlockEigenvalues/PhiUZero.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DatumBlockEigen
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LemmaU
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BlockEigenvalues_IsIntInvOfUnit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
namespace PI.DatumBlockEigen.Main
open PI.DatumBlockEigen.Unit Formalism.DoubleCosetMeasures
section
variable {F : Type} [Field F] {a t : ℕ}
variable (O : Subring F) (ϖ : F) (J' : Subgroup (GL (Fin a) F))
abbrev Supp (x : Matrix (Fin a ⊕ Fin t) (Fin a) F) : Prop :=
  (∃ k : J', ((k : GL (Fin a) F) : Matrix (Fin a) (Fin a) F) = toRows₁ x) ∧
    toRows₂ x ∈ IIset O ϖ
variable {O ϖ J'}
end
end PI.DatumBlockEigen.Main


