-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockRaisingLowering_BlockDiagonalPreservesDegree
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockRaisingLowering_BlockDiagonalPreservesDegree
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:20:24.841872+00:00
-- url     : https://prove2.me/theorems/eee392f1-7130-43a0-be84-9cea6348a272
-- title:
--   Block Diagonal Preserves Degree
-- statement:
--   Definitions and structural lemmas for Block Diagonal Preserves Degree, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockRaisingLowering/BlockDiagonalPreservesDegree.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockRaisingLowering_SameSign
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
namespace FockRL
variable {p q r s : ℕ}
def Rop (M : Matrix (FockH1Action.Ln p q r s) (FockH1Action.Ln p q r s) ℂ) : Module.End ℂ (FockH1Action.Pol p q r s) :=
  ∑ l, ∑ l', if FockH1Action.linePos l = true ∧ FockH1Action.linePos l' = false then M l l' • FockH1Action.omE l l'
    else 0
def Lop (M : Matrix (FockH1Action.Ln p q r s) (FockH1Action.Ln p q r s) ℂ) : Module.End ℂ (FockH1Action.Pol p q r s) :=
  ∑ l, ∑ l', if FockH1Action.linePos l = false ∧ FockH1Action.linePos l' = true then M l l' • FockH1Action.omE l l'
    else 0
section Inner
variable {σ : Type}
end Inner
end FockRL


