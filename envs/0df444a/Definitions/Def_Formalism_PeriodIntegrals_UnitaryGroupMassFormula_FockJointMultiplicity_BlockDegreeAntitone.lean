-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_BlockDegreeAntitone
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_BlockDegreeAntitone
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T06:49:22.936911+00:00
-- url     : https://prove2.me/theorems/5e77b058-1163-4aef-898f-64b2def92bd3
-- title:
--   Block Degree Antitone
-- statement:
--   Definitions and structural lemmas for Block Degree Antitone, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/BlockDegreeAntitone.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_CauchyHW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_LoweringPartRightActionInlInr
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_EqZeroOfFockInnerSelfRe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial FockH1Action
namespace PI.FJMF
def BlockAntitone : Prop := ∀ (σ : Type) (m n : ℕ) (ι : Fin m × Fin n → σ), Function.Injective ι →
  ∀ (α : Fin m → ℕ) (P : MvPolynomial σ ℂ), P ≠ 0 → (∀ a b : Fin m, a < b → PI.FJM.bRow ι a b P = 0) →
    (∀ e ∈ P.support, ∀ i, ∑ k : Fin n, e (ι (i, k)) = α i) → Antitone α
section Block
variable {σ : Type} {m n : ℕ} (ι : Fin m × Fin n → σ)
end Block
section Inner
variable {σ : Type}
end Inner
end PI.FJMF


