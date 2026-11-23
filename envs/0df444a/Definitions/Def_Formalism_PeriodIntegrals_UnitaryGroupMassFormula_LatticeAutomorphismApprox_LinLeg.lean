-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_LinLeg
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_LinLeg
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:03:37.407322+00:00
-- url     : https://prove2.me/theorems/04225319-4cc2-494b-a991-9848d3362553
-- title:
--   Lin Leg
-- statement:
--   Definitions and structural lemmas for Lin Leg, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeAutomorphismApprox/LinLeg.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_LinBase
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.UnitaryGroupMassFormula.ScXuExists
open Matrix
section Leg
variable {K : Type} [Field K] (O : ValuationSubring K) {n r : ℕ} (P : Matrix (Fin n) (Fin n) K)
  (Λ1 Λ2 : Submodule O (Fin n → K)) (a a' α α' : Fin r → Fin n → K)
def Pair (u φ : Fin n → K) : Prop :=
  u ∈ Λ1 ∧ φ ∈ Λ2 ∧ (∀ i, pr P (α i) u = 0 ∧ pr P (α' i) u = 0) ∧
    (∀ i, pr P φ (a i) = 0 ∧ pr P φ (a' i) = 0)
end Leg
end PI.UnitaryGroupMassFormula.ScXuExists


