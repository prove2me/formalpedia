-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_ArchPlace
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_ArchPlace
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T13:30:42.406425+00:00
-- url     : https://prove2.me/theorems/783432dc-8bfa-43ca-ac7c-c37e95c2ab31
-- title:
--   Arch Place
-- statement:
--   Definitions and structural lemmas for Arch Place, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeCountingBound/ArchPlace.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_SepDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeSizeContinuity_GramLowOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix
namespace PI.UnitaryGroupMassFormula.LCG
section LinAlg
variable {K : Type*} [Field K]
end LinAlg
section Place
variable (I : Formalism.MainNotions.S.AutInst)
def qM (z : I.GA) (v : InfinitePlace I.F) : Matrix (Fin I.n) (Fin I.n) ℂ :=
  Formalism.MainNotions.S.uMat (z.1 v)⁻¹ * (I.P v)⁻¹
def phv (v : InfinitePlace I.F) (w : Fin I.n → I.E) : Fin I.n → ℂ := fun i => I.φ v (w i)
def colM (z : I.GA) (v : InfinitePlace I.F) {k : ℕ} (b : Fin k → Fin I.n → I.E) : Matrix (Fin I.n) (Fin k) ℂ :=
  Matrix.of fun i c => PI.LatCountG.coordV I z v (b c) i
def hM {k : ℕ} (b' : Fin k → Fin I.n → I.E) : Matrix (Fin k) (Fin I.n) I.E :=
  Matrix.of (fun a i => star (b' a i)) * I.J
end Place
end PI.UnitaryGroupMassFormula.LCG
end


