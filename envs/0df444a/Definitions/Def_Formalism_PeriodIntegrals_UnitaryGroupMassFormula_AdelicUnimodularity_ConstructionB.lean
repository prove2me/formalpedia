-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_ConstructionB
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_ConstructionB
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T12:54:14.217699+00:00
-- url     : https://prove2.me/theorems/a257fddb-ac2f-4f88-a6d6-a981514a97fa
-- title:
--   Construction B
-- statement:
--   Definitions and structural lemmas for Construction B, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicUnimodularity/ConstructionB.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_KCountable
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_ExistsNatVec
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.WAU.B
open Formalism.MainNotions.S MeasureTheory NumberField IsDedekindDomain Formalism.UG Matrix PI.WAU.B
open scoped TensorProduct
section
variable (I : AutInst) {k : ℕ} (m : Fin k → Fin I.n → I.E)
def PN (N : ℕ) (x : I.Gf) : Prop :=
  0 < N ∧ ∀ j, N • (I.fmat x *ᵥ ivec (F := I.F) (m j)) ∈ I.Lf ∧
    N • (I.fmat x⁻¹ *ᵥ ivec (F := I.F) (m j)) ∈ I.Lf
def fN (N : ℕ) (x : I.Gf) : Fin k → Fin k → Bad I.F (N * N) → I.F := by
  classical
  exact fun j => if h : N • (I.fmat x *ᵥ ivec (F := I.F) (m j)) ∈ Tset (F := I.F) m then
    fun i => cls (N * N) (h.choose i) else fun _ _ => 0
end
end PI.WAU.B
namespace PI.WAU
open PI.WAU.B
end PI.WAU


